//! RoK  of equality of plain and compact Pedersen commitments
//!     - RPedersenEq -> Rtrivial

use ark_std::{end_timer, start_timer};
use ff::PrimeField;
use halo2curves::{
    ff::Field,
    group::Curve,
    secp256r1::Secp256r1Affine,
    serde::{endian::EndianRepr, SerdeObject},
    CurveAffine,
};
use merlin::Transcript;
use r1csipa::{msm_function, TranscriptProtocol};
use rand_core::{CryptoRng, RngCore};
use rok::{RelTrivial, Relation, RoK};
use serde::{Deserialize, Serialize};

use crate::{
    errors::PopError,
    relations::rpederseneq::{
        RelPedersenEq, RelPedersenEqParams, RelPedersenEqStatement, RelPedersenEqWitness,
    },
};

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PedersenEqRoKProof<C>
where
    C: CurveAffine,
    C::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    /// the verifier's challenge
    challenge: C::Scalar,
    /// the prover's response correpsonding to m
    response_m: Vec<C::ScalarExt>,
    /// the prover's response correpsonding to r_plain
    response_r_plain: Vec<C::ScalarExt>,
    /// the prover's response correpsonding to r_compact
    response_r_compact: Vec<C::ScalarExt>,
}

#[derive(Clone)]
/// The Pedersen [RoK] which reduces [RelPedersenEq] --> [RelTrivial]
/// L is the number of committed messages
/// B is the number of blinding factors used
pub struct PedersenEqRoK<C, const L: usize, const B: usize>
where
    C: CurveAffine,
    C::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    /// the parameters for RelPedersenEq
    pub(crate) pp: RelPedersenEqParams<C, L, B>,
}

impl<C, const L: usize, const B: usize> PedersenEqRoK<C, L, B>
where
    C: CurveAffine,
    C::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    /// helper function to samples a random statement/witness pair
    fn sample_random_statement<R>(
        &self,
        rng: &mut R,
    ) -> (RelPedersenEqStatement<C, L>, RelPedersenEqWitness<C, L, B>)
    where
        R: RngCore + CryptoRng,
    {
        let m = std::array::from_fn(|_| <C::ScalarExt as Field>::random(&mut *rng));
        let r_plain = std::array::from_fn(|_| <C::ScalarExt as Field>::random(&mut *rng));
        let r_compact = std::array::from_fn(|_| <C::ScalarExt as Field>::random(&mut *rng));

        let C_plain = std::array::from_fn(|i| {
            let bases = [self.pp.G_plain, self.pp.H_plain];
            let scalars = [m[i], r_plain[i]];
            msm_function(&scalars, &bases).to_affine()
        });

        let mut bases = self.pp.Gs_compact.to_vec();
        bases.extend(self.pp.Hs_compact.as_slice());
        let mut scalars = m.to_vec();
        scalars.extend(r_compact.as_slice());
        let C_compact = msm_function(&scalars, &bases).to_affine();

        let statement = RelPedersenEqStatement { C_plain, C_compact };
        let witness = RelPedersenEqWitness {
            m,
            r_plain,
            r_compact,
        };
        (statement, witness)
    }

    /// helper function to linearly combine witnesses based on a challenge
    /// In particular, it computes the new witness as w_new = w_1 + c w_2
    /// where c is a scalar
    fn lc_witness(
        w_1: &RelPedersenEqWitness<C, L, B>,
        w_2: &RelPedersenEqWitness<C, L, B>,
        c: C::ScalarExt,
    ) -> RelPedersenEqWitness<C, L, B> {
        let m = std::array::from_fn(|i| w_1.m[i] + c * w_2.m[i]);
        let r_plain = std::array::from_fn(|i| w_1.r_plain[i] + c * w_2.r_plain[i]);
        let r_compact = std::array::from_fn(|i| w_1.r_compact[i] + c * w_2.r_compact[i]);

        RelPedersenEqWitness {
            m,
            r_plain,
            r_compact,
        }
    }

    /// helper function to create statement from a witness
    fn compute_statement(&self, w: &RelPedersenEqWitness<C, L, B>) -> RelPedersenEqStatement<C, L> {
        // compute the plain commitments
        let C_plain = std::array::from_fn(|i| {
            let bases = [self.pp.G_plain, self.pp.H_plain];
            let scalars = [w.m[i], w.r_plain[i]];
            msm_function(&scalars, &bases).to_affine()
        });

        // compute the compact commitment
        let mut bases = self.pp.Gs_compact.to_vec();
        bases.extend(self.pp.Hs_compact.as_slice());
        let mut scalars = w.m.to_vec();
        scalars.extend(w.r_compact.as_slice());
        let C_compact = msm_function(&scalars, &bases).to_affine();

        RelPedersenEqStatement { C_plain, C_compact }
    }
}

impl<C, const L: usize, const B: usize> RoK for PedersenEqRoK<C, L, B>
where
    C: CurveAffine + SerdeObject,
    C::ScalarExt: PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>
        + EndianRepr,
{
    type RelationSource = RelPedersenEq<C, L, B>;
    type RelationTarget = RelTrivial<PopError>;
    type Proof = PedersenEqRoKProof<C>;
    type Error = PopError;

    fn label() -> String {
        "Plain and Compact Pedersen Equality RoK".into()
    }

    fn hash_statement(&self, rs: &Self::RelationSource, transcript: &mut Transcript) {
        // hash the parameters and the statement
        // hash G, H
        transcript.append_point(b"Plain G generator", &self.pp.G_plain);
        transcript.append_point(b"Plain G generator", &self.pp.H_plain);
        // hash compact pedersen generators
        self.pp.Gs_compact.iter().enumerate().for_each(|(i, g)| {
            transcript.append_u64(b"Append compact G generator:", i as u64);
            transcript.append_point(b"generator", g);
        });
        self.pp.Hs_compact.iter().enumerate().for_each(|(i, h)| {
            transcript.append_u64(b"Append compact H generator:", i as u64);
            transcript.append_point(b"generator", h);
        });
        // hash plain pedersen commitments
        rs.statement().C_plain.iter().enumerate().for_each(|(i, C)| {
            transcript.append_u64(b"Append commitment:", i as u64);
            transcript.append_point(b"commitment", C);
        });
        // hash compact pedersen commitment
        transcript.append_point(b"compact commitment", &rs.statement().C_compact);
    }

    fn reduce<R>(
        &self,
        transcript: &mut Transcript,
        rs: &RelPedersenEq<C, L, B>,
        rng: &mut R,
    ) -> Result<(Self::RelationTarget, Self::Proof), Self::Error>
    where
        R: RngCore + CryptoRng,
    {
        let t = start_timer!(|| "Plain/Compact Pedersen Equality RoK Prover");

        self.initialize(rs, transcript);

        // sample a random statement
        let (x_r, w_r) = self.sample_random_statement(rng);

        // append the random statement
        x_r.C_plain.iter().enumerate().for_each(|(i, C)| {
            transcript.append_u64(b"Append commitment:", i as u64);
            transcript.append_point(b"commitment", C);
        });
        // hash compact pedersen commitment
        transcript.append_point(b"compact commitment", &x_r.C_compact);

        // get challenge
        let c: C::ScalarExt = transcript.challenge_scalar(b"verifier's challenge");

        // compute response
        let w = rs
            .witness()
            .as_ref()
            .ok_or_else(|| PopError::MissingWitness(RelPedersenEq::<C, L, B>::label()))?;

        // response is w_r + c w
        let combined_witness = PedersenEqRoK::lc_witness(&w_r, w, c);
        end_timer!(t);

        let proof = PedersenEqRoKProof {
            challenge: c,
            response_m: combined_witness.m.to_vec(),
            response_r_plain: combined_witness.r_plain.to_vec(),
            response_r_compact: combined_witness.r_compact.to_vec(),
        };

        // append responses to the transcript to allow composition
        combined_witness
            .m
            .iter()
            .zip(combined_witness.r_plain.iter())
            .enumerate()
            .for_each(|(i, (m, r))| {
                transcript.append_u64(b"Append response m_i:", i as u64);
                transcript.append_scalar(b"commitment", m);
                transcript.append_u64(b"Append response r_i:", i as u64);
                transcript.append_scalar(b"commitment", r);
            });
        combined_witness.r_compact.iter().enumerate().for_each(|(i, r)| {
            transcript.append_u64(b"Append response r_i for compact:", i as u64);
            transcript.append_scalar(b"commitment", r);
        });
        Ok((RelTrivial::default(), proof))
    }

    fn reduce_statement(
        &self,
        transcript: &mut Transcript,
        rs: &Self::RelationSource,
        proof: &Self::Proof,
    ) -> Result<Self::RelationTarget, Self::Error> {
        let t = start_timer!(|| "Plain/Compact Pedersen Equality RoK verifier");
        if self.pp.G_plain != rs.params().G_plain
            || self.pp.H_plain != rs.params().H_plain
            || self.pp.Gs_compact != rs.params().Gs_compact
            || self.pp.Hs_compact != rs.params().Hs_compact
        {
            end_timer!(t);
            return Err(PopError::RoKError(
                Self::label() + ": invalid parameters in statement",
            ));
        }

        self.initialize(rs, transcript);
        // compute the combined statement from the proof
        let w_combined = RelPedersenEqWitness::<C, L, B> {
            m: proof.response_m.clone().try_into().unwrap(),
            r_plain: proof.response_r_plain.clone().try_into().unwrap(),
            r_compact: proof.response_r_compact.clone().try_into().unwrap(),
        };
        let x_combined = self.compute_statement(&w_combined);

        // compute the random statement implicit in the proof
        let x_r: RelPedersenEqStatement<C, L> = RelPedersenEqStatement {
            C_plain: std::array::from_fn(|i| {
                let scalars = [<C::ScalarExt as Field>::ONE, -proof.challenge];
                let bases = [x_combined.C_plain[i], rs.statement().C_plain[i]];
                msm_function(&scalars, &bases).to_affine()
            }),
            C_compact: {
                let scalars = [<C::ScalarExt as Field>::ONE, -proof.challenge];
                let bases = [x_combined.C_compact, rs.statement().C_compact];
                msm_function(&scalars, &bases).to_affine()
            },
        };

        // append the random statement
        x_r.C_plain.iter().enumerate().for_each(|(i, C)| {
            transcript.append_u64(b"Append commitment:", i as u64);
            transcript.append_point(b"commitment", C);
        });
        // hash compact pedersen commitment
        transcript.append_point(b"compact commitment", &x_r.C_compact);

        // get challenge
        let c: C::ScalarExt = transcript.challenge_scalar(b"verifier's challenge");

        if c != proof.challenge {
            end_timer!(t);
            return Err(PopError::RoKError(Self::label() + "computed c != c"));
        }

        // append responses to the transcript to allow composition
        w_combined
            .m
            .iter()
            .zip(w_combined.r_plain.iter())
            .enumerate()
            .for_each(|(i, (m, r))| {
                transcript.append_u64(b"Append response m_i:", i as u64);
                transcript.append_scalar(b"commitment", m);
                transcript.append_u64(b"Append response r_i:", i as u64);
                transcript.append_scalar(b"commitment", r);
            });
        w_combined.r_compact.iter().enumerate().for_each(|(i, r)| {
            transcript.append_u64(b"Append response r_i for compact:", i as u64);
            transcript.append_scalar(b"commitment", r);
        });

        end_timer!(t);
        Ok(RelTrivial::default())
    }
}

#[cfg(test)]
mod tests {
    use halo2curves::t256::T256Affine;
    use merlin::Transcript;
    use rand_core::OsRng;
    use rok::{Relation, RoK};

    use crate::{
        relations::rpederseneq::RelPedersenEq, relations::tests::sample_random_pederseneq_instance,
        roks::pederseneq_rok::PedersenEqRoK,
    };

    #[test]
    fn test_pederseneq_rok() {
        const L: usize = 4;
        const B: usize = 8;

        let r_prover = sample_random_pederseneq_instance::<T256Affine, L, B>();
        let r_verifier: RelPedersenEq<T256Affine, L, B> = Relation::new(
            r_prover.params().clone(),
            r_prover.statement().clone(),
            None,
        );

        let rok = PedersenEqRoK {
            pp: r_verifier.params().clone(),
        };

        let mut transcript_prover = Transcript::new(b"pederseneq_rok test");
        let (_r_trivial, proof) =
            rok.reduce(&mut transcript_prover, &r_prover, &mut OsRng).unwrap();

        let bytes = bincode::serialize(&proof).unwrap();
        println!("proof size: {} bytes", bytes.len());

        let mut transcript_verifier = Transcript::new(b"pederseneq_rok test");
        let result = rok.reduce_statement(&mut transcript_verifier, &r_verifier, &proof);
        assert!(result.is_ok(), "reduce failed: {:?}", result);
    }
}
