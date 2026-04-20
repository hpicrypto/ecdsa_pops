//! CSchnorr RoK for reducing [RelECDSA] -> ([RelCSchnorr] x [RelPedersen])
//!
//! We use a single limb representation in circuit

use ark_std::{end_timer, start_timer};
use ff::{Field, PrimeField};
use halo2curves::{
    group::Curve,
    secp256r1::Secp256r1Affine,
    serde::{endian::EndianRepr, SerdeObject},
    CurveAffine,
};
use merlin::Transcript;
use r1csipa::{msm_function, TranscriptProtocol};
use rand_core::{CryptoRng, RngCore};
use rok::{Relation, RelationProduct, RoK};
use serde::{Deserialize, Serialize};

use crate::{
    errors::PopError,
    relations::{
        rcshnorr::{RelCSchnorr, RelCSchnorrParams, RelCSchnorrStatement, RelCSchnorrWitness},
        recdsa::{RelECDSA, RelECDSAWitness},
        rpedersen::{RelPedersen, RelPedersenParams, RelPedersenStatement, RelPedersenWitness},
    },
    utils::{ecdsa::ECDSA, fp_to_scalars, Fq},
};

#[derive(Debug, Serialize, Deserialize)]
/// CSchnorr RoK for reducing [RelECDSA] -> ([RelCSchnorr] x [RelPedersen])
pub struct CSchnorrRoKProof<C, const SEC_PARAM_BYTES: usize>
where
    C: CurveAffine,
    C::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    // Commitment to the first message R
    // Always given as a single compressed commitment
    C_R: C,
    // schnorr protocol response
    response: Fq,
}

#[derive(Serialize, Clone)]
/// L is the number of limbs to represent P256 as a C scalar
pub struct CSchnorrRoK<C, const SEC_PARAM_BYTES: usize, const L: usize>
where
    C: CurveAffine + SerdeObject,
    C::ScalarExt: PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>
        + EndianRepr,
{
    /// the generator(s) used to compute commitment to first message.
    pub(crate) G_R: Vec<C>,
    /// the generator(s) used to compute commitment to the public key.
    pub(crate) G_Q: Vec<C>,
    /// the generator used for hiding
    pub(crate) H: C,
}

impl<C, const SEC_PARAM_BYTES: usize, const L: usize> CSchnorrRoK<C, SEC_PARAM_BYTES, L>
where
    C: CurveAffine + SerdeObject,
    C::ScalarExt: PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>
        + EndianRepr,
{
    /// Computes the first message of Committed Schnorr consisting of a
    /// commitment to R=rK.
    fn compute_first_message<R>(
        &self,
        K: &Secp256r1Affine,
        rng: &mut R,
    ) -> Result<(C, Secp256r1Affine, Fq, C::ScalarExt), PopError>
    where
        R: RngCore + CryptoRng,
    {
        // 1. compute noraml Schnorr first message:
        // R = rK for random R
        let r = Fq::random(&mut *rng);
        let R = K * r;

        // 2. convert R.x to Vec<C::Scalar>
        let mut scalars = fp_to_scalars::<C, L>(&R.to_affine().x)?.to_vec();

        // 3. compute commitment to Rx_scalars
        // sample randomness
        let rhoR = C::ScalarExt::random(&mut *rng);
        scalars.push(rhoR);
        // compute the commitment
        let bases = [self.G_R.as_slice(), &[self.H]].concat();
        let C_R = msm_function(&scalars, &bases);

        Ok((C_R.into(), R.into(), r, rhoR))
    }

    /// Computes the verifier challenge
    pub(crate) fn get_challenge(transcript: &mut Transcript) -> Fq {
        let mut c_bytes_low = [0u8; SEC_PARAM_BYTES];
        transcript.challenge_bytes(b"Verifier challenge", &mut c_bytes_low);
        let mut c_bytes = [0u8; 32];
        (0..SEC_PARAM_BYTES).for_each(|i| c_bytes[i] = c_bytes_low[i]);
        <Fq as PrimeField>::from_repr(c_bytes.into()).unwrap()
    }

    /// Given the interaction, computes the CSchnorr statement/witness
    pub(crate) fn get_cschnorr_relation(
        &self,
        rs: &<Self as RoK>::RelationSource,
        proof: &<Self as RoK>::Proof,
        c: Fq,
        witness: Option<(RelECDSAWitness<C, L>, C::ScalarExt, Secp256r1Affine)>,
    ) -> RelCSchnorr<C, SEC_PARAM_BYTES, L> {
        // The underlying relation is knowledge of z s.t.
        // zK = Q + m K.x ^{-1} (<==> (z,K) valid on m under Q)
        //
        // The normal schnorr would run:
        // (R = rK, c, s = c * r + z)
        // We have
        // sK = crK + zK
        //    = cR + (Q + mK.x^{-1}P)
        // which is equivalent to
        // sK - mK.x^{-1}P = c R + Q
        //
        // setting T = sK - mK.x^{-1}P
        // we need to verify T = c R + Q

        // the commitment key consists of the concatenaation of the two keys
        let cschnorr_pp = RelCSchnorrParams {
            ck: [self.G_R.as_slice(), self.G_Q.as_slice(), &[self.H]].concat(),
        };
        // T = sK - cmK.x^{-1}P
        // C = \sum C_Qi + C_R
        let P = rs.params().ecdsa().pp;
        let Kx_inv = ECDSA::p256_to_scalar(rs.statement().k()).invert().unwrap();
        let T = rs.statement().k() * proof.response - P * (rs.statement().m() * Kx_inv);

        // compute compressed commitment to Q
        let C_Q = rs.statement().cx().iter().fold(C::identity().to_curve(), |acc, &com| acc + com);
        // compute compressed commitment to R
        let C = (C_Q + proof.C_R).into();
        let cschnorr_x = RelCSchnorrStatement::<C, SEC_PARAM_BYTES> { C, T: T.into(), c };

        let cschnorr_w = witness.map(|(w, rho_R, R)| {
            // the combined randomness for C_Q
            let rho_Q: C::ScalarExt = w.rhox().iter().sum();
            RelCSchnorrWitness::new(R, *w.q(), rho_Q + rho_R)
        });

        RelCSchnorr::new(cschnorr_pp, cschnorr_x, cschnorr_w)
    }

    /// Given the interaction, computes the Pedersen statement/witness
    pub(crate) fn get_pedersen_relation(
        &self,
        proof: &<Self as RoK>::Proof,
        witness: Option<(C::ScalarExt, Secp256r1Affine)>,
    ) -> RelPedersen<C> {
        let pedersen_pp = RelPedersenParams {
            ck: [self.G_R.as_slice(), &[self.H]].concat(),
        };
        let pedersen_x = RelPedersenStatement { C: proof.C_R };

        let pedersen_w = witness.map(|(rho_R, R)| {
            let mut m = fp_to_scalars::<C, L>(&R.x).unwrap().to_vec();
            m.push(rho_R);
            RelPedersenWitness { m }
        });
        RelPedersen::new(pedersen_pp, pedersen_x, pedersen_w)
    }
}

impl<C, const SEC_PARAM_BYTES: usize, const L: usize> RoK for CSchnorrRoK<C, SEC_PARAM_BYTES, L>
where
    C: CurveAffine + SerdeObject,
    C::ScalarExt: PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>
        + EndianRepr,
{
    type RelationSource = RelECDSA<C, L>;
    type RelationTarget =
        RelationProduct<RelCSchnorr<C, SEC_PARAM_BYTES, L>, RelPedersen<C>, PopError>;
    type Proof = CSchnorrRoKProof<C, SEC_PARAM_BYTES>;
    type Error = PopError;

    fn label() -> String {
        "Committed Schnorr proof".into()
    }

    fn hash_statement(&self, rs: &Self::RelationSource, transcript: &mut Transcript) {
        // hash the parameters
        self.G_R.iter().enumerate().for_each(|(i, g)| {
            transcript.append_u64(b"Append G_R generator:", i as u64);
            transcript.append_point(b"generator", g);
        });
        self.G_Q.iter().enumerate().for_each(|(i, g)| {
            transcript.append_u64(b"Append G_Q generator:", i as u64);
            transcript.append_point(b"generator", g);
        });
        transcript.append_point(b"Append H generator", &self.H);
        transcript.append_point(b"ECDSA generator", &rs.params().ecdsa().pp);

        // append statement C, K, m
        transcript.append_point(b"statement_C", &rs.statement().cx()[0]);
        transcript.append_point(b"statement_K", rs.statement().k());
        transcript.append_scalar(b"statement_m", rs.statement().m());
    }

    fn reduce<R>(
        &self,
        transcript: &mut Transcript,
        rs: &RelECDSA<C, L>,
        rng: &mut R,
    ) -> Result<(Self::RelationTarget, Self::Proof), Self::Error>
    where
        R: RngCore + CryptoRng,
    {
        let t = start_timer!(|| "Committed Schnorr RoK Prover");

        self.initialize(rs, transcript);

        // sample the first message
        let (C_R, R, r, rho_R) = self.compute_first_message(rs.statement().k(), rng)?;

        transcript.append_point(b"R Commitment", &C_R);

        // get challenge
        let c = CSchnorrRoK::<C, SEC_PARAM_BYTES, L>::get_challenge(transcript);

        // reply
        let witness = rs
            .witness()
            .as_ref()
            .ok_or_else(|| PopError::MissingWitness(RelECDSA::<C, L>::label()))?;
        let s = c * r + witness.z();

        // append s to the transcript to allow composition
        transcript.append_scalar(b"Prover response", &s);

        // compute the RoK proof
        let proof = CSchnorrRoKProof { C_R, response: s };

        let rcschnorr =
            self.get_cschnorr_relation(rs, &proof, c, Some((witness.clone(), rho_R, R)));
        let rpedersen = self.get_pedersen_relation(&proof, Some((rho_R, R)));

        let rt = RelationProduct::from_parts(rcschnorr, rpedersen);
        end_timer!(t);
        Ok((rt, proof))
    }

    fn reduce_statement(
        &self,
        transcript: &mut Transcript,
        rs: &Self::RelationSource,
        proof: &Self::Proof,
    ) -> Result<Self::RelationTarget, Self::Error> {
        let t = start_timer!(|| "Committed Schnorr RoK Verifier");

        self.initialize(rs, transcript);

        transcript.append_point(b"R Commitment", &proof.C_R);
        // get challenge
        let c = CSchnorrRoK::<C, SEC_PARAM_BYTES, L>::get_challenge(transcript);
        // append s to the transcript to allow composition
        transcript.append_scalar(b"Prover response", &proof.response);

        // construct the output statements
        let rcschnorr = self.get_cschnorr_relation(rs, proof, c, None);
        let rpedersen = self.get_pedersen_relation(proof, None);

        let rt = RelationProduct::from_parts(rcschnorr, rpedersen);

        end_timer!(t);

        Ok(rt)
    }
}

#[cfg(test)]
mod tests {

    use ff::PrimeField;
    use halo2curves::{
        bls12381::G1Affine,
        secp256r1::Secp256r1Affine,
        serde::{endian::EndianRepr, SerdeObject},
        t256::T256Affine,
        CurveAffine,
    };
    use merlin::Transcript;
    use rand_core::OsRng;
    use rok::{Relation, RoK};
    use serde::Serialize;

    use crate::{
        relations::tests::{pedersen_key, sample_random_ecdsa_instance_with_key},
        roks::cschnorr_rok::CSchnorrRoK,
    };

    fn test_cschnorr_rok_helper<C, const L: usize>()
    where
        C: CurveAffine + SerdeObject + Serialize,
        C::ScalarExt: PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>
            + SerdeObject
            + EndianRepr,
    {
        // sample a random key for committing to R, Q
        let G_R = pedersen_key::<C>(L, "test_cschnorr_rok_helper G_R");
        let G_Q = pedersen_key::<C>(L, "test_cschnorr_rok_helper G_Q");
        // common blinding element
        let H = pedersen_key::<C>(1, "test_cschnorr_rok_helper H")[0];

        // sample an ecdsa instance
        let recdsa =
            sample_random_ecdsa_instance_with_key::<C, L>(G_Q.clone().try_into().unwrap(), H);

        let rok = CSchnorrRoK::<C, 16, L> { G_R, G_Q, H };

        let mut transcript_prover = Transcript::new(b"CSchnorr RoK");
        let (rt_p, proof) = rok.reduce(&mut transcript_prover, &recdsa, &mut OsRng).unwrap();
        let result = rt_p.in_relation();
        assert!(result.is_ok(), "reduce failed: {:?}", result);

        let bytes = bincode::serialize(&proof).unwrap();
        println!("proof size: {} bytes", bytes.len());

        let mut transcript_verifier = Transcript::new(b"CSchnorr RoK");
        let result = rok.reduce_statement(&mut transcript_verifier, &recdsa, &proof);
        assert!(result.is_ok(), "reduce failed: {:?}", result);
    }

    #[test]
    fn test_cschnorr_rok() {
        // T256 -> 1 limb to represent P256 base
        test_cschnorr_rok_helper::<T256Affine, 1>();
        test_cschnorr_rok_helper::<T256Affine, 2>();
        test_cschnorr_rok_helper::<T256Affine, 4>();
        // BLS -> 2 limb to represent P256 base
        test_cschnorr_rok_helper::<G1Affine, 2>();
        test_cschnorr_rok_helper::<G1Affine, 4>();
    }
}
