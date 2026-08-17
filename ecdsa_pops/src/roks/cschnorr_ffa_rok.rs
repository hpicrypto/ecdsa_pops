//! CSchnorr RoK for reducing [RelCschnorr] -> [RelCSchnorrCompact] in bls curve

use ark_std::{end_timer, start_timer};
use ff::Field;
use merlin::Transcript;
use r1csipa::{msm_function, TranscriptProtocol};
use rand_core::{CryptoRng, RngCore};
use rok::{Nizk, Relation, RoK};
use serde::{Deserialize, Serialize};

use halo2curves::{
    bls12381::{Fr as BlsScalar, G1Affine},
    group::Curve,
};

use super::pederseneq_rok::PedersenEqRoKProof;
use crate::{
    errors::PopError,
    relations::{
        rcschnorr_compact::{
            RelCSchnorrCompact, RelCSchnorrCompactParams, RelCSchnorrCompactStatement,
            RelCSchnorrCompactWitness,
        },
        rcshnorr::RelCSchnorr,
        rpederseneq::{
            RelPedersenEq, RelPedersenEqParams, RelPedersenEqStatement, RelPedersenEqWitness,
        },
    },
    roks::pederseneq_rok::PedersenEqRoK,
    utils::fp_to_scalars,
};

#[derive(Clone, Debug, Serialize, Deserialize)]
/// CSchnorr RoK for reducing [RelCschnorr] -> [RelCSchnorrCompact] in bls curve
/// This simply uses the [PedersenEqRok] to transfer the commitments to compact
pub struct CSchnorrFFARoKProof {
    /// the compact commitment
    compact_commitment: G1Affine,
    /// the proof of equal openings of plain/compact Pedersen
    pederseneq_proof: PedersenEqRoKProof<G1Affine>,
}

#[derive(Clone)]
/// The RoK that composes with the ffa circuit
pub struct CSchnorrFFARoK {
    /// the generator used to compute the plain commitments.
    pub(crate) G_plain: G1Affine,
    /// the generator used as a blinding factor for the plain commitments.
    pub(crate) H_plain: G1Affine,
    /// the generator used for the compact commitments. We use two limbs for each point committed
    pub(crate) Gs_compact: [G1Affine; 4],
    /// the blinding factors used for the compact commitments. We use 8 in total
    pub(crate) Hs_compact: [G1Affine; 8],
}

impl RoK for CSchnorrFFARoK {
    type RelationSource = RelCSchnorr<G1Affine, 2>;
    type RelationTarget = RelCSchnorrCompact<G1Affine, 2, 8>;
    type Proof = CSchnorrFFARoKProof;
    type Error = PopError;

    fn label() -> String {
        "FFA Committed Schnorr proof".into()
    }

    fn hash_statement(&self, rs: &Self::RelationSource, transcript: &mut Transcript) {
        // append the parameters
        transcript.append_point(b"Append G_plain generator", &self.G_plain);
        transcript.append_point(b"Append H_plain generator", &self.H_plain);
        self.Gs_compact.iter().enumerate().for_each(|(i, g)| {
            transcript.append_u64(b"Append compact G generator:", i as u64);
            transcript.append_point(b"generator", g);
        });
        self.Hs_compact.iter().enumerate().for_each(|(i, h)| {
            transcript.append_u64(b"Append compact H generator:", i as u64);
            transcript.append_point(b"generator", h);
        });

        // append statement CQ, CR, T, c
        transcript.append_point(b"statement_CQ_limb0", &rs.statement().CQ[0]);
        transcript.append_point(b"statement_CQ_limb1", &rs.statement().CQ[1]);
        transcript.append_point(b"statement_CR_limb0", &rs.statement().CR[0]);
        transcript.append_point(b"statement_CR_limb1", &rs.statement().CR[1]);
        transcript.append_point(b"statement_T", &rs.statement().T);
        transcript.append_scalar(b"statement_c", &rs.statement().c);
    }

    fn reduce<R>(
        &self,
        transcript: &mut Transcript,
        rs: &RelCSchnorr<G1Affine, 2>,
        rng: &mut R,
    ) -> Result<(Self::RelationTarget, Self::Proof), Self::Error>
    where
        R: RngCore + CryptoRng,
    {
        let t = start_timer!(|| "FFA Committed Schnorr RoK Prover");

        // check relation params match rok params
        if rs.params().ck_Q != [self.G_plain; 2]
            || rs.params().ck_R != [self.G_plain; 2]
            || rs.params().h != self.H_plain
        {
            end_timer!(t);
            return Err(PopError::RoKError(
                Self::label() + ": invalid source relation parameters",
            ));
        }

        self.initialize(rs, transcript);

        let witness = rs
            .witness()
            .as_ref()
            .ok_or_else(|| PopError::MissingWitness(RelCSchnorr::<G1Affine, 2>::label()))?;

        // create the params for the the pok of same openings
        let pp = RelPedersenEqParams::<G1Affine, 4, 8> {
            G_plain: self.G_plain,
            H_plain: self.H_plain,
            Gs_compact: self.Gs_compact,
            Hs_compact: self.Hs_compact,
        };

        // sample blinding factors
        let r_compact: [_; 8] = std::array::from_fn(|_| BlsScalar::random(&mut *rng));

        // compute the compact commitment
        let mut scalars = fp_to_scalars::<G1Affine, 2>(&witness.Q.x)?.to_vec();
        scalars.extend_from_slice(fp_to_scalars::<G1Affine, 2>(&witness.R.x)?.as_slice());
        scalars.extend_from_slice(r_compact.as_slice());
        let mut bases = pp.Gs_compact.to_vec();
        bases.extend_from_slice(pp.Hs_compact.as_slice());
        let C_compact = msm_function(&scalars, &bases).to_affine();

        // put the commitment to the transcript
        transcript.append_point(b"compact commitment", &C_compact);

        // create the proof for Pedersen equality
        let x = RelPedersenEqStatement {
            C_plain: [
                rs.statement().CQ[0],
                rs.statement().CQ[1],
                rs.statement().CR[0],
                rs.statement().CR[1],
            ],
            C_compact,
        };

        let r_plain = [
            witness.rhoQ[0],
            witness.rhoQ[1],
            witness.rhoR[0],
            witness.rhoR[1],
        ];
        let w = RelPedersenEqWitness::<G1Affine, 4, 8> {
            m: scalars[0..4].to_vec().try_into().unwrap(),
            r_plain,
            r_compact,
        };

        let pederseneq_rok = PedersenEqRoK::<G1Affine, 4, 8> { pp: pp.clone() };
        let r_pederseneq = RelPedersenEq::new(pp.clone(), x, Some(w));

        // create the equality proof
        let pederseneq_proof = pederseneq_rok.prove(transcript, &r_pederseneq, rng)?;
        let proof = CSchnorrFFARoKProof {
            compact_commitment: C_compact,
            pederseneq_proof,
        };

        // create the target relation
        let rt_pp = RelCSchnorrCompactParams::<G1Affine, 2, 8> {
            ck_Q: pp.Gs_compact[0..2].try_into().unwrap(),
            ck_R: pp.Gs_compact[2..4].try_into().unwrap(),
            h: pp.Hs_compact,
        };
        let rt_x = RelCSchnorrCompactStatement::<G1Affine, 2> {
            C: C_compact,
            T: rs.statement().T,
            c: rs.statement().c,
        };
        let rt_w = RelCSchnorrCompactWitness::<G1Affine, 2, 8> {
            R: witness.R,
            Q: witness.Q,
            rho: r_compact,
        };
        let rt = RelCSchnorrCompact::new(rt_pp, rt_x, Some(rt_w));

        end_timer!(t);
        Ok((rt, proof))
    }

    fn reduce_statement(
        &self,
        transcript: &mut Transcript,
        rs: &Self::RelationSource,
        proof: &Self::Proof,
    ) -> Result<Self::RelationTarget, Self::Error> {
        let t = start_timer!(|| "FFA Committed Schnorr RoK Verifier");

        // check relation params match rok params
        if rs.params().ck_Q != [self.G_plain; 2]
            || rs.params().ck_R != [self.G_plain; 2]
            || rs.params().h != self.H_plain
        {
            end_timer!(t);
            return Err(PopError::RoKError(
                Self::label() + ": invalid source relation parameters",
            ));
        }

        self.initialize(rs, transcript);

        // create the pedersen statement to be verified
        let pp = RelPedersenEqParams::<G1Affine, 4, 8> {
            G_plain: self.G_plain,
            H_plain: self.H_plain,
            Gs_compact: self.Gs_compact,
            Hs_compact: self.Hs_compact,
        };

        // create the proof for Pedersen equality
        let x = RelPedersenEqStatement {
            C_plain: [
                rs.statement().CQ[0],
                rs.statement().CQ[1],
                rs.statement().CR[0],
                rs.statement().CR[1],
            ],
            C_compact: proof.compact_commitment,
        };

        transcript.append_point(b"compact commitment", &proof.compact_commitment);

        // verify the equality proof
        let r_pederseneq = RelPedersenEq::new(pp.clone(), x.clone(), None);
        let pederseneq_rok = PedersenEqRoK::<G1Affine, 4, 8> { pp: pp.clone() };
        pederseneq_rok.verify(transcript, &r_pederseneq, &proof.pederseneq_proof)?;

        // create the target relation
        let rt_pp = RelCSchnorrCompactParams::<G1Affine, 2, 8> {
            ck_Q: pp.clone().Gs_compact[0..2].try_into().unwrap(),
            ck_R: pp.clone().Gs_compact[2..4].try_into().unwrap(),
            h: pp.clone().Hs_compact,
        };
        let rt_x = RelCSchnorrCompactStatement::<G1Affine, 2> {
            C: x.C_compact,
            T: rs.statement().T,
            c: rs.statement().c,
        };
        let rt = RelCSchnorrCompact::new(rt_pp, rt_x, None);

        end_timer!(t);
        Ok(rt)
    }
}

#[cfg(test)]
mod tests {
    use ff::Field;
    use halo2curves::{bls12381::G1Affine, secp256r1::Secp256r1Affine, CurveAffine};
    use merlin::Transcript;
    use rand_core::OsRng;
    use rok::{Relation, RoK};

    use crate::{
        relations::{
            rcshnorr::{RelCSchnorr, RelCSchnorrParams, RelCSchnorrStatement, RelCSchnorrWitness},
            tests::pedersen_key,
        },
        roks::cschnorr_ffa_rok::CSchnorrFFARoK,
        utils::Fq,
    };

    #[test]
    fn test_cschnorr_ffa_rok() {
        let G_plain = pedersen_key::<G1Affine>(1, "test_cschnorr_ffa_rok G_plain")[0];
        let H_plain = pedersen_key::<G1Affine>(1, "test_cschnorr_ffa_rok H_plain")[0];
        let Gs_compact =
            pedersen_key::<G1Affine>(4, "test_cschnorr_ffa_rok Gs").try_into().unwrap();
        let Hs_compact =
            pedersen_key::<G1Affine>(8, "test_cschnorr_ffa_rok Hs").try_into().unwrap();

        // same commitment for the plain commitments
        let pp = RelCSchnorrParams::<G1Affine, 2> {
            ck_R: [G_plain; 2],
            ck_Q: [G_plain; 2],
            h: H_plain,
        };

        // sample a random statement
        let c = Fq::random(OsRng);
        let R = Secp256r1Affine::random(OsRng);
        let Q = Secp256r1Affine::random(OsRng);
        let rhoR = std::array::from_fn(|_| <G1Affine as CurveAffine>::ScalarExt::random(OsRng));
        let rhoQ = std::array::from_fn(|_| <G1Affine as CurveAffine>::ScalarExt::random(OsRng));
        let w = RelCSchnorrWitness::<G1Affine, 2>::new(R, Q, rhoR, rhoQ);
        let T = ((R * c) + Q).into();
        let CQ = RelCSchnorr::<G1Affine, 2>::create_commitments(&Q, &rhoQ, &pp.ck_Q, &pp.h);
        let CR = RelCSchnorr::<G1Affine, 2>::create_commitments(&R, &rhoR, &pp.ck_R, &pp.h);
        let x = RelCSchnorrStatement::<G1Affine, 2> { CQ, CR, T, c };
        let rs = RelCSchnorr::new(pp, x, Some(w));

        let rok = CSchnorrFFARoK {
            G_plain,
            H_plain,
            Gs_compact,
            Hs_compact,
        };

        // run the rok
        let mut transcript_prover = Transcript::new(b"FFA CSchnorr RoK");
        let (rt, proof) = rok.reduce(&mut transcript_prover, &rs, &mut OsRng).unwrap();
        let result = rt.in_relation();
        assert!(result.is_ok(), "target relation failed: {:?}", result);

        let rs_verifier = RelCSchnorr::new(rs.params().clone(), rs.statement().clone(), None);
        let mut transcript_verifier = Transcript::new(b"FFA CSchnorr RoK");
        let result = rok.reduce_statement(&mut transcript_verifier, &rs_verifier, &proof);
        assert!(result.is_ok(), "reduce failed: {:?}", result);
    }
}
