//! [RoK] (nizk) of discrete logrithm equality:  [RelDLEQ] --> [RelTrivial]

use ark_std::{end_timer, start_timer, One};
use ff::{Field, PrimeField};
use halo2curves::{
    secp256r1::Secp256r1Affine,
    serde::{endian::EndianRepr, SerdeObject},
    CurveAffine,
};
use merlin::Transcript;
use num_bigint::{BigUint, RandBigInt};
use r1csipa::{msm_function, TranscriptProtocol};
use rand_core::{CryptoRng, RngCore};
use rok::{RelTrivial, Relation, RoK};
use serde::{Deserialize, Serialize};

use crate::{
    circuit::utils::big_to_ff,
    errors::PopError,
    relations::rdleq::{RelDLEQ, RelDLEQParams, RelDLEQStatement, RelDLEQWitness},
};

/// A proof of equality produced by [DleqRoK].
///
/// NOTE: Assumes the scalar fields of C1, C2 are represented in *little endian*
#[derive(Serialize, Deserialize, Debug)]
pub(crate) struct DLEQRoKProof<C1, C2>
where
    C1: CurveAffine,
    C1::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
    C2: CurveAffine,
    C2::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    /// the verifier's challenge
    challenge: Vec<u8>,
    /// the response corresponding to m
    z: Vec<u8>,
    /// the response corresponding to C1 randomness
    s1: C1::Scalar,
    /// the response corresponding to C1 randomness
    s2: C2::Scalar,
}

#[derive(Clone)]
/// A [RoK] reducing [RelDLEQ] --> [RelTrivial].
///
/// TODO: Generics for the values b_x, b_f, b_c
pub(crate) struct DleqRoK<C1, C2>
where
    C1: CurveAffine,
    C1::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
    C2: CurveAffine,
    C2::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    /// parameter b_x
    pub(crate) b_x: u32,
    /// parameter b_c
    pub(crate) b_c: u32,
    /// parameter b_f
    pub(crate) b_f: u32,
    /// the commitment key used in C1
    pub(crate) ck1: Vec<C1>,
    /// the commitment key used in C2
    pub(crate) ck2: Vec<C2>,
}

impl<C1, C2> From<DleqRoK<C1, C2>> for RelDLEQParams<C1, C2>
where
    C1: CurveAffine,
    C1::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
    C2: CurveAffine,
    C2::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    fn from(rok_params: DleqRoK<C1, C2>) -> Self {
        assert!(
            rok_params.b_x + rok_params.b_c + rok_params.b_f
                < C1::ScalarExt::NUM_BITS.min(C2::ScalarExt::NUM_BITS)
        );
        RelDLEQParams {
            ck1: rok_params.ck1,
            ck2: rok_params.ck2,
        }
    }
}

impl<C1, C2> DleqRoK<C1, C2>
where
    C1: CurveAffine,
    C1::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
    C2: CurveAffine,
    C2::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    /// Samples a random statement/witness pair for this commitment key
    /// The statement is almost identical except the bound on the witness
    fn sample_random_pair<R>(
        &self,
        _pp: &RelDLEQParams<C1, C2>,
        rng: &mut R,
    ) -> (RelDLEQStatement<C1, C2>, RelDLEQWitness<C1, C2>)
    where
        R: RngCore + CryptoRng,
    {
        // sample k in [0..2^bx+bc+bf] and map it to the two curves
        let bound = self.b_x + self.b_c + self.b_f;
        let k = rng.gen_biguint(bound as u64);
        let (k1, k2) = (big_to_ff(&k), big_to_ff(&k));
        // sample randomness to commit to k
        let (t1, t2) = (
            C1::ScalarExt::random(&mut *rng),
            C2::ScalarExt::random(&mut *rng),
        );

        // compute the two commitments
        let (com1, com2) = (
            msm_function(&[k1, t1], &self.ck1).into(),
            msm_function(&[k2, t2], &self.ck2).into(),
        );

        let x = RelDLEQStatement::<C1, C2> { C1: com1, C2: com2 };
        let w = RelDLEQWitness {
            m: k,
            r1: t1,
            r2: t2,
        };

        (x, w)
    }

    /// Computes the verifier challenge and returns the corresponding field elements in both scalar
    /// fields.
    ///
    /// NOTE: Assumes the scalar fields of C1, C2 are represented in *little endian*
    pub(crate) fn get_challenge(&self, transcript: &mut Transcript) -> BigUint {
        if (self.b_c % 8) != 0 {
            unimplemented!()
        }
        let mut c_bytes = [0u8; 32];
        transcript.challenge_bytes(b"verifier's challenge", &mut c_bytes);
        ((self.b_c / 8)..32).for_each(|i| c_bytes[i as usize] = 0);
        BigUint::from_bytes_le(&c_bytes)
    }

    pub(crate) fn check_z_inrange(&self, z: &BigUint) -> bool {
        let lower = BigUint::one() << (self.b_x + self.b_c);
        let upper = BigUint::one() << (self.b_x + self.b_c + self.b_f);
        *z >= lower && *z < upper
    }
}

impl<C1, C2> RoK for DleqRoK<C1, C2>
where
    C1: CurveAffine + SerdeObject,
    C1::ScalarExt: PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>
        + EndianRepr,
    C2: CurveAffine + SerdeObject,
    C2::ScalarExt: PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>
        + EndianRepr,
{
    type RelationSource = RelDLEQ<C1, C2>;
    type RelationTarget = RelTrivial<PopError>;
    type Proof = DLEQRoKProof<C1, C2>;
    type Error = PopError;

    fn label() -> String {
        "Dlog equality RoK".into()
    }

    fn hash_statement(&self, rs: &Self::RelationSource, transcript: &mut Transcript) {
        // hash the parameters and the statement
        transcript.append_u64(b"b_x: ", self.b_x as u64);
        transcript.append_u64(b"b_c: ", self.b_c as u64);
        transcript.append_u64(b"b_f: ", self.b_f as u64);
        self.ck1.iter().enumerate().for_each(|(i, g)| {
            transcript.append_u64(b"Append generator:", i as u64);
            transcript.append_point(b"generator", g);
        });
        self.ck2.iter().enumerate().for_each(|(i, g)| {
            transcript.append_u64(b"Append generator:", i as u64);
            transcript.append_point(b"generator", g);
        });
        transcript.append_point(b"statement", &rs.statement().C1);
        transcript.append_point(b"statement", &rs.statement().C2);
    }

    fn reduce<R>(
        &self,
        transcript: &mut Transcript,
        rs: &RelDLEQ<C1, C2>,
        rng: &mut R,
    ) -> Result<(Self::RelationTarget, Self::Proof), Self::Error>
    where
        R: RngCore + CryptoRng,
    {
        let t = start_timer!(|| format!(
            "DLEQ RoK (b_x: {}, b_c: {}, b_f: {}) Prover",
            self.b_x, self.b_c, self.b_f,
        ));

        // keep a copy of the original transcript in case abort happens
        let mut base_transcript = transcript.clone();

        self.initialize(rs, &mut base_transcript);

        loop {
            let mut trial_transcript = base_transcript.clone();

            // sample a random statement
            let (x_r, w_r) = self.sample_random_pair(rs.params(), rng);

            // append first statement
            trial_transcript.append_point(b"first message K1", &x_r.C1);
            trial_transcript.append_point(b"first message K2", &x_r.C2);

            // get challenge
            let c = self.get_challenge(&mut trial_transcript);

            // compute response
            let w = rs
                .witness()
                .as_ref()
                .ok_or_else(|| PopError::MissingWitness(RelDLEQ::<C1, C2>::label()))?;
            let z: BigUint = w_r.m + c.clone() * w.m.clone();
            if self.check_z_inrange(&z) {
                // no abort
                *transcript = trial_transcript;
                let c1 = big_to_ff::<C1::ScalarExt>(&c);
                let c2 = big_to_ff::<C2::ScalarExt>(&c);
                let s1 = w_r.r1 + c1 * w.r1;
                let s2 = w_r.r2 + c2 * w.r2;

                // append values to the transcript to allow composition
                transcript.append_scalar(b"z in C1", &big_to_ff::<C1::ScalarExt>(&z));
                transcript.append_scalar(b"z in C2", &big_to_ff::<C2::ScalarExt>(&z));
                transcript.append_scalar(b"s1", &s1);
                transcript.append_scalar(b"s2", &s2);

                // add elements to the proof
                let proof = DLEQRoKProof::<C1, C2> {
                    challenge: c.to_bytes_le(),
                    z: z.to_bytes_le(),
                    s1,
                    s2,
                };
                end_timer!(t);
                return Ok((RelTrivial::default(), proof));
            }
        }
    }

    fn reduce_statement(
        &self,
        transcript: &mut Transcript,
        rs: &Self::RelationSource,
        proof: &Self::Proof,
    ) -> Result<Self::RelationTarget, Self::Error> {
        let t = start_timer!(|| format!(
            "DLEQ RoK (b_x: {}, b_c: {}, b_f: {}) Verifier",
            self.b_x, self.b_c, self.b_f,
        ));

        self.initialize(rs, transcript);

        if self.ck1 != rs.params().ck1 || self.ck2 != rs.params().ck2 {
            return Err(PopError::RoKError(
                Self::label() + ": invalid parameters in statement",
            ));
        }

        let z = BigUint::from_bytes_le(&proof.z);
        // check z bound
        if !self.check_z_inrange(&z) {
            return Err(PopError::RoKError(Self::label() + ": z not in range!"));
        }
        // map to the two fields
        let (z1, z2) = (big_to_ff(&z), big_to_ff(&z));

        // read c from proof and map to the two fields
        let c_big = BigUint::from_bytes_le(&proof.challenge);
        let (c1, c2) = (
            big_to_ff::<C1::ScalarExt>(&c_big),
            big_to_ff::<C2::ScalarExt>(&c_big),
        );

        // recompute K_1, K_2
        let scalars1 = [z1, proof.s1, -c1];
        let mut bases1 = self.ck1.clone();
        bases1.push(rs.statement().C1);
        let K1 = msm_function(&scalars1, &bases1);
        let scalars2 = [z2, proof.s2, -c2];
        let mut bases2 = self.ck2.clone();
        bases2.push(rs.statement().C2);
        let K2 = msm_function(&scalars2, &bases2);

        // append first statement
        transcript.append_point::<C1>(b"first message K1", &K1.into());
        transcript.append_point::<C2>(b"first message K2", &K2.into());

        let computed_c = self.get_challenge(transcript);

        // append values to the transcript to allow composition
        transcript.append_scalar(b"z in C1", &big_to_ff::<C1::ScalarExt>(&z));
        transcript.append_scalar(b"z in C2", &big_to_ff::<C2::ScalarExt>(&z));
        transcript.append_scalar(b"s1", &proof.s1);
        transcript.append_scalar(b"s2", &proof.s2);

        if computed_c.to_bytes_le() != proof.challenge {
            end_timer!(t);
            return Err(PopError::RoKError(Self::label() + ": computed c != c"));
        }
        end_timer!(t);
        Ok(RelTrivial::default())
    }
}

#[cfg(test)]
mod tests {

    use merlin::Transcript;
    use rand_core::OsRng;
    use rok::{rok_compose, Relation, RelationProduct, RoK};

    use crate::{
        errors::PopError, relations::tests::sample_random_dleq_instance, roks::dleq_rok::DleqRoK,
    };

    #[test]
    fn test_dleq_rok() {
        let rs1 = sample_random_dleq_instance();
        let rs2 = sample_random_dleq_instance();

        let dleq_rok_1 = DleqRoK {
            b_x: 64,
            b_f: 16,
            b_c: 128,
            ck1: rs1.params().ck1.clone(),
            ck2: rs2.params().ck2.clone(),
        };
        let dleq_rok_2 = DleqRoK {
            b_x: 64,
            b_f: 16,
            b_c: 128,
            ck1: rs1.params().ck1.clone(),
            ck2: rs2.params().ck2.clone(),
        };
        let rs = RelationProduct::<_, _, PopError>::from_parts(rs1, rs2);

        let rok = rok_compose!(
            PopError;
            ((dleq_rok_1) x (dleq_rok_2))
        );

        let mut transcript_prover = Transcript::new(b"dleq_rok test");
        let (_r_trivial, proof) = rok.reduce(&mut transcript_prover, &rs, &mut OsRng).unwrap();

        let bytes = bincode::serialize(&proof).unwrap();
        println!("proof size: {} bytes", bytes.len());

        let mut transcript_verifier = Transcript::new(b"dleq_rok test");
        let result = rok.reduce_statement(&mut transcript_verifier, &rs, &proof);
        assert!(result.is_ok(), "reduce failed: {:?}", result);
    }
}
