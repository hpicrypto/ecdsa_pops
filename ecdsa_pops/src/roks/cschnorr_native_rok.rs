//! CSchnorr RoK for reducing [RelCschnorr] -> [RelCSchnorrCompact] in T256
//! curve

use ark_std::{end_timer, start_timer};
use halo2curves::{group::Curve, t256::T256Affine};
use merlin::Transcript;
use r1csipa::TranscriptProtocol;
use rand_core::{CryptoRng, RngCore};
use rok::{Nizk, Relation, RoK};
use serde::{Deserialize, Serialize};

use super::pedersen_rok::{PedersenRoK, PedersenRoKProof};
use crate::{
    errors::PopError,
    relations::{
        rcschnorr_compact::{
            RelCSchnorrCompact, RelCSchnorrCompactParams, RelCSchnorrCompactStatement,
            RelCSchnorrCompactWitness,
        },
        rcshnorr::RelCSchnorr,
        rpedersen::{RelPedersen, RelPedersenParams, RelPedersenStatement, RelPedersenWitness},
    },
    utils::fp_to_fr,
};

#[derive(Debug, Serialize, Deserialize)]
/// CSchnorr RoK for reducing [RelCschnorr] -> [RelCSchnorrCompact] in T256
/// curve
pub struct CSchnorrNativeRoKProof {
    pedersen_proof: PedersenRoKProof<T256Affine>,
}

#[derive(Clone)]
/// L is the number of limbs to represent P256 as a C scalar
pub struct CSchnorrNativeRoK {
    /// the generator used to compute commitment to first message R.
    pub(crate) G_R: T256Affine,
    /// the generator used to compute commitment to the public key.
    pub(crate) G_Q: T256Affine,
    /// the (common) generators used for hiding
    pub(crate) H: T256Affine,
}

impl RoK for CSchnorrNativeRoK {
    type RelationSource = RelCSchnorr<T256Affine, 1>;
    type RelationTarget = RelCSchnorrCompact<T256Affine, 1, 1>;
    type Proof = CSchnorrNativeRoKProof;
    type Error = PopError;

    fn label() -> String {
        "Native Committed Schnorr proof".into()
    }

    fn hash_statement(&self, rs: &Self::RelationSource, transcript: &mut Transcript) {
        transcript.append_point(b"Append G_R generator", &self.G_R);
        transcript.append_point(b"Append G_Q generator", &self.G_Q);
        transcript.append_point(b"Append H generator", &self.H);

        // append statement CQ, CR, T, c
        transcript.append_point(b"statement_CR", &rs.statement().CR[0]);
        transcript.append_point(b"statement_CQ", &rs.statement().CQ[0]);
        transcript.append_point(b"statement_T", &rs.statement().T);
        transcript.append_scalar(b"statement_c", &rs.statement().c);
    }

    fn reduce<R>(
        &self,
        transcript: &mut Transcript,
        rs: &RelCSchnorr<T256Affine, 1>,
        rng: &mut R,
    ) -> Result<(Self::RelationTarget, Self::Proof), Self::Error>
    where
        R: RngCore + CryptoRng,
    {
        let t = start_timer!(|| "Native Committed Schnorr RoK Prover");

        self.initialize(rs, transcript);

        let witness = rs
            .witness()
            .as_ref()
            .ok_or_else(|| PopError::MissingWitness(RelCSchnorr::<T256Affine, 1>::label()))?;

        // prove knowledge of opening of CR
        let pp = RelPedersenParams {
            ck: [self.G_R, self.H].to_vec(),
        };
        let x = RelPedersenStatement {
            C: rs.statement().CR[0],
        };
        let w = RelPedersenWitness::<T256Affine> {
            m: vec![fp_to_fr(&witness.R.x), witness.rhoR[0]],
        };
        let r_pedersen = RelPedersen::new(pp, x, Some(w));

        let pedersen_rok = PedersenRoK {
            ck: r_pedersen.params().ck.clone(),
        };
        let pedersen_proof = pedersen_rok.prove(transcript, &r_pedersen, rng)?;
        let proof = CSchnorrNativeRoKProof { pedersen_proof };

        // create the compact statment
        let pp = RelCSchnorrCompactParams {
            ck_R: [self.G_R],
            ck_Q: [self.G_Q],
            h: [self.H],
        };
        // sum the commitments C_R and C_Q to get the compact commitment
        let x = RelCSchnorrCompactStatement {
            C: (rs.statement().CR[0] + rs.statement().CQ[0]).to_affine(),
            T: rs.statement().T,
            c: rs.statement().c,
        };

        // sum the blinding factors
        let w = RelCSchnorrCompactWitness {
            R: witness.R,
            Q: witness.Q,
            rho: [witness.rhoR[0] + witness.rhoQ[0]],
        };

        let rt = RelCSchnorrCompact::new(pp, x, Some(w));

        end_timer!(t);
        Ok((rt, proof))
    }

    fn reduce_statement(
        &self,
        transcript: &mut Transcript,
        rs: &Self::RelationSource,
        proof: &Self::Proof,
    ) -> Result<Self::RelationTarget, Self::Error> {
        let t = start_timer!(|| "Native Committed Schnorr RoK Verifier");

        self.initialize(rs, transcript);

        // verify the pedersen proof
        let pp = RelPedersenParams {
            ck: [self.G_R, self.H].to_vec(),
        };
        let x = RelPedersenStatement {
            C: rs.statement().CR[0],
        };
        let r_pedersen = RelPedersen::new(pp, x, None);

        let pedersen_rok = PedersenRoK {
            ck: r_pedersen.params().ck.clone(),
        };

        pedersen_rok.verify(transcript, &r_pedersen, &proof.pedersen_proof)?;

        // create the compact statment
        let pp = RelCSchnorrCompactParams {
            ck_R: [self.G_R],
            ck_Q: [self.G_Q],
            h: [self.H],
        };
        // sum the commitments C_R and C_Q to get the compact commitment
        let x = RelCSchnorrCompactStatement {
            C: (rs.statement().CQ[0] + rs.statement().CR[0]).to_affine(),
            T: rs.statement().T,
            c: rs.statement().c,
        };

        let rt = RelCSchnorrCompact::new(pp, x, None);

        end_timer!(t);
        Ok(rt)
    }
}

#[cfg(test)]
mod tests {

    use halo2curves::t256::T256Affine;
    use merlin::Transcript;
    use rand_core::OsRng;
    use rok::{Relation, RoK};

    use crate::{
        relations::tests::{pedersen_key, sample_random_cschnorr_instance},
        roks::cschnorr_native_rok::CSchnorrNativeRoK,
    };

    #[test]
    fn test_native_cschnorr_rok() {
        let rs = sample_random_cschnorr_instance::<T256Affine, 16, 1>();

        let rok = CSchnorrNativeRoK {
            G_R: rs.params().ck_R[0],
            G_Q: rs.params().ck_Q[0],
            H: rs.params().h,
        };

        let mut transcript_prover = Transcript::new(b"Native CSchnorr RoK");
        let (rt, proof) = rok.reduce(&mut transcript_prover, &rs, &mut OsRng).unwrap();
        let result = rt.in_relation();
        assert!(result.is_ok(), "reduce failed: {:?}", result);

        let bytes = bincode::serialize(&proof).unwrap();
        println!("proof size: {} bytes", bytes.len());

        let mut transcript_verifier = Transcript::new(b"Native CSchnorr RoK");
        let result = rok.reduce_statement(&mut transcript_verifier, &rs, &proof);
        assert!(result.is_ok(), "reduce failed: {:?}", result);
    }
}
