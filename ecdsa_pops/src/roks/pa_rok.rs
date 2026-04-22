//! PA RoK for reducing [RelPA] -> [RelTrivial])
//!
//! The implementation is based on a modified version of [Docknetwork
//! Crypto](github.com/docknetwork/crypto).
//!
//! TODO: Remove the docknetwork dependency. The implementation mixes
//! ark/halo2curves and the current transcript with docknetwork transcript which
//! is error prone.

use ark_secp256r1::Config as SecpConfig;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{end_timer, start_timer};
use dock_crypto_utils::{
    commitment::PedersenCommitmentKey,
    transcript::{new_merlin_transcript, Transcript as DockTranscript},
};
use equality_across_groups::{
    ec::{
        commitments::{PointCommitment, PointCommitmentWithOpening},
        sw_point_addition::{PointAdditionProof, PointAdditionProtocol},
    },
    tom256::{Affine as T256Ark, Config as TomConfig},
};
use halo2curves::t256::T256Affine;
use merlin::Transcript;
use r1csipa::TranscriptProtocol;
use rand_core::{CryptoRng, RngCore};
use rok::{RelTrivial, Relation, RoK};
use serde::{Deserialize, Deserializer, Serialize};

use crate::{
    errors::PopError,
    relations::rpa::RelPA,
    utils::{fr_to_arkfr, p256_to_arkp256, t256_to_arkt256},
};

/// PA RoK for reducing [RelPA] -> [RelTrivial])
pub struct PAProof {
    proof: PointAdditionProof<SecpConfig, TomConfig>,
}

impl Serialize for PAProof {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut bytes = Vec::new();
        self.proof.serialize_compressed(&mut bytes).map_err(serde::ser::Error::custom)?;
        serializer.serialize_bytes(&bytes)
    }
}

impl<'de> Deserialize<'de> for PAProof {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let bytes: Vec<u8> = Vec::<u8>::deserialize(deserializer)?;

        let proof = PointAdditionProof::<SecpConfig, TomConfig>::deserialize_compressed(&*bytes)
            .map_err(serde::de::Error::custom)?;

        Ok(PAProof { proof })
    }
}

#[derive(Clone)]
/// The PARoK
pub struct PARoK {
    /// Generators for committing to limbs
    G: T256Affine,
    /// Generator for blinding commitments (common for all)
    H: T256Affine,
}

impl PARoK {
    pub fn from_ck(ck: &[T256Affine; 2]) -> Self {
        Self { G: ck[0], H: ck[1] }
    }
}

impl RoK for PARoK {
    type RelationSource = RelPA;
    type RelationTarget = RelTrivial<PopError>;
    type Proof = PAProof;
    type Error = PopError;

    fn label() -> String {
        "PA RoK".into()
    }

    fn hash_statement(&self, rs: &Self::RelationSource, transcript: &mut Transcript) {
        // hash the parameters
        transcript.append_u64(b"Append generator:", 1);
        transcript.append_point(b"G generator", &self.G);
        transcript.append_u64(b"Append generator:", 2);
        transcript.append_point(b"H generator", &self.H);

        // hash the the statement
        (0..3usize).for_each(|i| {
            transcript.append_u64(b"Append Commitment:", i as u64);
            transcript.append_point(b"Commitment to Px", &rs.statement().c(i).unwrap().0);
            transcript.append_point(b"Commitment to Py", &rs.statement().c(i).unwrap().1);
        });
    }

    fn reduce<R>(
        &self,
        transcript: &mut Transcript,
        rs: &RelPA,
        rng: &mut R,
    ) -> Result<(Self::RelationTarget, Self::Proof), Self::Error>
    where
        R: RngCore + CryptoRng,
    {
        let t = start_timer!(|| "PA RoK Prover");

        self.initialize(rs, transcript);

        // convert halo2curve elements to ark elements
        let comm_key = PedersenCommitmentKey::<T256Ark> {
            g: t256_to_arkt256(&rs.params().g()),
            h: t256_to_arkt256(&rs.params().h()),
        };
        let w = rs.witness().clone();
        if w.is_none() {
            return Err(PopError::MissingWitness(RelPA::label()));
        };
        let w = w.unwrap();

        let rs = w.rhos().map(|r| {
            let rx = fr_to_arkfr(&r.0);
            let ry = fr_to_arkfr(&r.1);
            (rx, ry)
        });
        let ps = w.ps().map(|p| p256_to_arkp256(&p));

        let comm_a = PointCommitmentWithOpening::<TomConfig>::new_given_randomness(
            &ps[0], rs[0].0, rs[0].1, &comm_key,
        )?;
        let comm_b = PointCommitmentWithOpening::<TomConfig>::new_given_randomness(
            &ps[1], rs[1].0, rs[1].1, &comm_key,
        )?;
        let comm_t = PointCommitmentWithOpening::<TomConfig>::new_given_randomness(
            &ps[2], rs[2].0, rs[2].1, &comm_key,
        )?;

        // To connect the different types of transcripts we derive a challenge from
        // the current transcript and append it to the "inner" transcript
        let mut bytes = [0u8; 32];
        transcript.challenge_bytes(b"outer transcript digest", &mut bytes);
        let mut prover_transcript = new_merlin_transcript(b"DN transcript for pa");
        prover_transcript.append_message(b"outer transcript digest", &bytes);

        let protocol = PointAdditionProtocol::<SecpConfig, TomConfig>::init(
            rng,
            comm_a.clone(),
            comm_b.clone(),
            comm_t.clone(),
            ps[0],
            ps[1],
            ps[2],
            &comm_key,
        )?;
        protocol.challenge_contribution(&mut prover_transcript).unwrap();

        // sample the challenge
        let challenge_prover = prover_transcript.challenge_scalar(b"PA challenge");
        let proof = protocol.gen_proof(&challenge_prover);

        // compute the RoK proof
        let proof = PAProof { proof };

        end_timer!(t);
        let rt = RelTrivial::default();

        Ok((rt, proof))
    }

    fn reduce_statement(
        &self,
        transcript: &mut Transcript,
        rs: &Self::RelationSource,
        proof: &Self::Proof,
    ) -> Result<Self::RelationTarget, Self::Error> {
        // TODO We can use the randomized variant for faster verifier
        let t = start_timer!(|| "PA RoK verifier");

        if self.G != *rs.params().g() || self.H != *rs.params().h() {
            return Err(PopError::RoKError(
                Self::label() + ": invalid parameters in statement",
            ));
        }
        self.initialize(rs, transcript);

        // convert halo2curve elements to ark elements
        let comm_key = PedersenCommitmentKey::<T256Ark> {
            g: t256_to_arkt256(&rs.params().g()),
            h: t256_to_arkt256(&rs.params().h()),
        };
        let x = t256_to_arkt256(&rs.statement().c(0).unwrap().0);
        let y = t256_to_arkt256(&rs.statement().c(0).unwrap().1);
        let comm_a = PointCommitment::<TomConfig> { x, y };

        let x = t256_to_arkt256(&rs.statement().c(1).unwrap().0);
        let y = t256_to_arkt256(&rs.statement().c(1).unwrap().1);
        let comm_b = PointCommitment::<TomConfig> { x, y };

        let x = t256_to_arkt256(&rs.statement().c(2).unwrap().0);
        let y = t256_to_arkt256(&rs.statement().c(2).unwrap().1);
        let comm_t = PointCommitment::<TomConfig> { x, y };

        // To connect the different types of transcripts we derive a challenge from
        // the current transcript and append it to the "inner" transcript
        let mut bytes = [0u8; 32];
        transcript.challenge_bytes(b"outer transcript digest", &mut bytes);
        let mut verifier_transcript = new_merlin_transcript(b"DN transcript for pa");
        verifier_transcript.append_message(b"outer transcript digest", &bytes);

        proof.proof.challenge_contribution(&mut verifier_transcript).unwrap();

        let challenge_verifier = verifier_transcript.challenge_scalar(b"PA challenge");
        proof
            .proof
            .verify(&comm_a, &comm_b, &comm_t, &challenge_verifier, &comm_key)
            .unwrap();

        end_timer!(t);

        Ok(RelTrivial::default())
    }
}

#[cfg(test)]
mod tests {
    use ark_serialize::CanonicalSerialize;
    use ff::Field;
    use halo2curves::{secp256r1::Secp256r1Affine, t256::T256Affine};
    use merlin::Transcript;
    use r1csipa::msm_function;
    use rand_core::OsRng;
    use rok::{Relation, RoK};

    use crate::{
        relations::{
            rpa::{RelPA, RelPAParams, RelPAStatement, RelPAWitness},
            tests::pedersen_key,
        },
        roks::pa_rok::PARoK,
        utils::{fp_to_fr, Fq, Fr},
    };

    #[test]
    fn test_pa_rok() {
        // sample the commitment key
        let ck = pedersen_key::<T256Affine>(2, "sample_random_sm_instance");

        // sample the witness
        let P0 = Secp256r1Affine::random(OsRng);
        let P1 = Secp256r1Affine::random(OsRng);
        let P2: Secp256r1Affine = (P0 + P1).into();

        let rho0 = (Fr::random(OsRng), Fr::random(OsRng));
        let rho1 = (Fr::random(OsRng), Fr::random(OsRng));
        let rho2 = (Fr::random(OsRng), Fr::random(OsRng));

        // compute the commitments
        let Cs = [
            (
                msm_function(&[fp_to_fr(&P0.x), rho0.0], &ck).into(),
                msm_function(&[fp_to_fr(&P0.y), rho0.1], &ck).into(),
            ),
            (
                msm_function(&[fp_to_fr(&P1.x), rho1.0], &ck).into(),
                msm_function(&[fp_to_fr(&P1.y), rho1.1], &ck).into(),
            ),
            (
                msm_function(&[fp_to_fr(&P2.x), rho2.0], &ck).into(),
                msm_function(&[fp_to_fr(&P2.y), rho2.1], &ck).into(),
            ),
        ];
        let rhos = [(rho0.0, rho0.1), (rho1.0, rho1.1), (rho2.0, rho2.1)];

        let pp = RelPAParams::new(ck[0], ck[1]);
        let x = RelPAStatement::new(Cs);
        let w = RelPAWitness::new([P0, P1, P2], rhos);

        let rs = RelPA::new(pp, x, Some(w));
        assert!(rs.in_relation().is_ok());

        let rok = PARoK { G: ck[0], H: ck[1] };

        let mut transcript_prover = Transcript::new(b"PA RoK Test");
        let (rt, proof) = rok.reduce(&mut transcript_prover, &rs, &mut OsRng).unwrap();
        let result = rt.in_relation();
        assert!(result.is_ok(), "reduce failed: {:?}", result);

        let proof_size = proof.proof.compressed_size();
        println!("proof size: {} bytes", proof_size);

        let mut transcript_verifier = Transcript::new(b"PA RoK Test");
        let result = rok.reduce_statement(&mut transcript_verifier, &rs, &proof);
        assert!(result.is_ok(), "reduce failed: {:?}", result);
    }
}
