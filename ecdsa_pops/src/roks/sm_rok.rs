//! SM RoK for reducing [RelSM] -> [RelTrivial])
//!
//! The implementation is based on a modified version of [Docknetwork
//! Crypto](github.com/docknetwork/crypto).
//!
//! TODO: Remove the docknetwork dependency. The implementation mixes
//! ark/halo2curves and the current transcript with docknetwork transcript which
//! is error prone.

use ark_ec::CurveGroup;
use ark_secp256r1::Config as SecpConfig;
use ark_std::{end_timer, start_timer};
use dock_crypto_utils::{
    commitment::PedersenCommitmentKey,
    transcript::{new_merlin_transcript, Transcript as DockTranscript},
};
use equality_across_groups::{
    ec::{
        commitments::{PointCommitment, PointCommitmentWithOpening},
        sw_scalar_mult_without_commitment::{
            ScalarMultiplicationWCProof, ScalarMultiplicationWCProtocol,
        },
    },
    tom256::{Affine as T256Ark, Config as TomConfig},
};
use halo2curves::t256::T256Affine;
use merlin::Transcript;
use r1csipa::TranscriptProtocol;
use rand_core::{CryptoRng, RngCore};
use rok::{RelTrivial, Relation, RoK};

use crate::{
    errors::PopError,
    relations::rsm::RelSM,
    utils::{fq_to_arkfq, fr_to_arkfr, p256_to_arkp256, t256_to_arkt256, Fq},
};

/// SM RoK for reducing [RelSM] -> [RelTrivial])
pub(crate) struct SMProof {
    proof: ScalarMultiplicationWCProof<SecpConfig, TomConfig, 128>,
}

#[derive(Clone)]
/// The SMRoK
pub(crate) struct SMRoK {
    /// Generators for committing to limbs
    G: T256Affine,
    /// Generator for blinding commitments (common for all)
    H: T256Affine,
}

impl RoK for SMRoK {
    type RelationSource = RelSM;
    type RelationTarget = RelTrivial<PopError>;
    type Proof = SMProof;
    type Error = PopError;

    fn label() -> String {
        "SM RoK".into()
    }

    fn hash_statement(&self, rs: &Self::RelationSource, transcript: &mut Transcript) {
        // hash the parameters
        transcript.append_u64(b"Append generator:", 1);
        transcript.append_point(b"G generator", &self.G);
        transcript.append_u64(b"Append generator:", 2);
        transcript.append_point(b"H generator", &self.H);

        // hash the the statement
        transcript.append_point(b"Commitment to x", &rs.statement().c().0);
        transcript.append_point(b"Commitment to y", &rs.statement().c().1);
        transcript.append_point(b"Commitment to base point", rs.statement().g());
    }

    fn reduce<R>(
        &self,
        transcript: &mut Transcript,
        rs: &RelSM,
        rng: &mut R,
    ) -> Result<(Self::RelationTarget, Self::Proof), Self::Error>
    where
        R: RngCore + CryptoRng,
    {
        let t = start_timer!(|| "SM RoK Prover");

        self.initialize(rs, transcript);

        // convert halo2curve elements to ark elements
        let comm_key = PedersenCommitmentKey::<T256Ark> {
            g: t256_to_arkt256(&rs.params().g()),
            h: t256_to_arkt256(&rs.params().h()),
        };
        let w = rs.witness().clone();
        if w.is_none() {
            return Err(PopError::MissingWitness(RelSM::label()));
        };
        let w = w.unwrap();

        let base = p256_to_arkp256(&rs.statement().g());
        let scalar = fq_to_arkfq(&w.scalar());
        let result = (base * scalar).into_affine();

        let r_x = fr_to_arkfr(&w.rho().0);
        let r_y = fr_to_arkfr(&w.rho().1);
        let comm_result = PointCommitmentWithOpening::<TomConfig>::new_given_randomness(
            &result, r_x, r_y, &comm_key,
        )?;

        // To connect the different types of transcripts we derive a challenge from
        // the current transcript and append it to the "inner" transcript
        let mut bytes = [0u8; 32];
        transcript.challenge_bytes(b"outer transcript digest", &mut bytes);
        let mut prover_transcript = new_merlin_transcript(b"DN transcript for sm");
        prover_transcript.append_message(b"outer transcript digest", &bytes);

        let protocol = ScalarMultiplicationWCProtocol::<SecpConfig, TomConfig, 128>::init(
            rng,
            scalar,
            comm_result.clone(),
            result,
            base,
            &comm_key,
        )?;
        protocol.challenge_contribution(&mut prover_transcript).unwrap();

        // sample the challenge
        let mut challenge_prover = [0_u8; 128 / 8];
        prover_transcript.challenge_bytes(b"SM challenge", &mut challenge_prover);
        let proof = protocol.gen_proof(&challenge_prover);

        // compute the RoK proof
        let proof = SMProof { proof };

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
        let t = start_timer!(|| "SM RoK verifier");

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
        let base = p256_to_arkp256(&rs.statement().g());

        let x = t256_to_arkt256(&rs.statement().c().0);
        let y = t256_to_arkt256(&rs.statement().c().1);
        let comm = PointCommitment::<TomConfig> { x, y };

        // To connect the different types of transcripts we derive a challenge from
        // the current transcript and append it to the "inner" transcript
        let mut bytes = [0u8; 32];
        transcript.challenge_bytes(b"outer transcript digest", &mut bytes);
        let mut verifier_transcript = new_merlin_transcript(b"DN transcript for sm");
        verifier_transcript.append_message(b"outer transcript digest", &bytes);

        proof.proof.challenge_contribution(&mut verifier_transcript).unwrap();

        let mut challenge_verifier = [0_u8; 128 / 8];
        verifier_transcript.challenge_bytes(b"SM challenge", &mut challenge_verifier);

        proof.proof.verify(&comm, &base, &challenge_verifier, &comm_key)?;

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
            rsm::{RelSM, RelSMParams, RelSMStatement, RelSMWitness},
            tests::pedersen_key,
        },
        roks::sm_rok::SMRoK,
        utils::{fp_to_fr, Fq, Fr},
    };

    #[test]
    fn test_sm_rok() {
        // sample the commitment key
        let ck = pedersen_key::<T256Affine>(2, "sample_random_sm_instance");

        // sample the witness
        let G = Secp256r1Affine::random(OsRng);
        let z = Fq::random(OsRng);
        let P: Secp256r1Affine = (G * z).into();
        let rho = (Fr::random(OsRng), Fr::random(OsRng));

        // compute the commitment
        let C = (
            msm_function(&[fp_to_fr(&P.x), rho.0], &ck).into(),
            msm_function(&[fp_to_fr(&P.y), rho.1], &ck).into(),
        );
        let pp = RelSMParams::new(ck[0], ck[1]);
        let x = RelSMStatement::new(C, G);
        let w = RelSMWitness::new(P, rho, z);

        let rs = RelSM::new(pp, x, Some(w));
        assert!(rs.in_relation().is_ok());

        let rok = SMRoK { G: ck[0], H: ck[1] };

        let mut transcript_prover = Transcript::new(b"SM RoK Test");
        let (rt, proof) = rok.reduce(&mut transcript_prover, &rs, &mut OsRng).unwrap();
        let result = rt.in_relation();
        assert!(result.is_ok(), "reduce failed: {:?}", result);

        let proof_size = proof.proof.compressed_size();
        println!("proof size: {} bytes", proof_size);

        let mut transcript_verifier = Transcript::new(b"SM RoK Test");
        let result = rok.reduce_statement(&mut transcript_verifier, &rs, &proof);
        assert!(result.is_ok(), "reduce failed: {:?}", result);
    }
}
