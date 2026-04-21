//! Group RoK for reducing [RelECDSA] -> ([RelSM] x [RelPA])

use ark_std::{end_timer, start_timer};
use ff::Field;
use halo2curves::{secp256r1::Secp256r1Affine, t256::T256Affine};
use merlin::Transcript;
use r1csipa::{msm_function, TranscriptProtocol};
use rand_core::{CryptoRng, RngCore};
use rok::{Relation, RelationProduct, RoK};
use serde::{Deserialize, Serialize};

use crate::{
    errors::PopError,
    relations::{
        recdsa::RelECDSA,
        rpa::{RelPA, RelPAParams, RelPAStatement, RelPAWitness},
        rsm::{RelSM, RelSMParams, RelSMStatement, RelSMWitness},
    },
    utils::{ecdsa::ECDSA, fp_to_fr, Fr},
};

#[derive(Debug, Serialize, Deserialize)]
/// Group RoK for reducing [RelECDSA] (over T256) -> ([RelSM] x [RelPA]) in T256 curve
pub struct GroupRoKProof {
    // Pedersen commitment to the value Z=zK message R
    CZx: T256Affine,
    CZy: T256Affine,
}

#[derive(Serialize, Clone)]
pub struct GroupRoK {
    /// the G generator of the Pedersen commitment over T256
    pub(crate) G: T256Affine,
    /// the H generator of the Pedersen commitment over T256
    pub(crate) H: T256Affine,
}

impl GroupRoK {
    /// computes the Point \alpha G for ECDSA verification
    fn compute_alphaG(rs: &RelECDSA<T256Affine, 1>) -> Secp256r1Affine {
        // compute Kxinv^{-1} * m G_p and a commitment to it
        let Kxinv = ECDSA::p256_to_scalar(&rs.statement().k()).invert().unwrap();
        let alpha = rs.statement().m() * Kxinv;
        (rs.params().ecdsa().pp * alpha).into()
    }

    /// computes the two statements given the proof
    fn statements_from_proof(
        &self,
        rs: &RelECDSA<T256Affine, 1>,
        CZx: T256Affine,
        CZy: T256Affine,
    ) -> (RelSMStatement, RelPAStatement) {
        // the sm statement
        let x_sm = RelSMStatement::new((CZx, CZy), *rs.statement().k());

        let P1 = GroupRoK::compute_alphaG(rs);
        // the deterministic commitment to P1
        let C1 = (
            (self.G * fp_to_fr(&P1.x)).into(),
            (self.G * fp_to_fr(&P1.y)).into(),
        );
        // the pa statement
        let commitments = [
            (rs.statement().cx()[0], rs.statement().cy().unwrap()[0]),
            C1,
            (CZx, CZy),
        ];
        let x_pa = RelPAStatement::new(commitments);
        (x_sm, x_pa)
    }
}

impl RoK for GroupRoK {
    type RelationSource = RelECDSA<T256Affine, 1>;
    type RelationTarget = RelationProduct<RelSM, RelPA, PopError>;
    type Proof = GroupRoKProof;
    type Error = PopError;

    fn label() -> String {
        "Group RoK proof".into()
    }

    fn hash_statement(&self, rs: &Self::RelationSource, transcript: &mut Transcript) {
        // hash the parameters
        transcript.append_point(b"G generator", &self.G);
        transcript.append_point(b"H generator", &self.H);

        let st = rs.statement();

        // append statement Cx, Cy, K,  m
        transcript.append_point(b"Cx commitment", &rs.statement().cx()[0]);
        // should never panic
        transcript.append_point(b"Cy commitment", &rs.statement().cy().unwrap()[0]);
        transcript.append_point(b"K value", rs.statement().k());
        transcript.append_scalar(b"message", rs.statement().m());
    }

    fn reduce<R>(
        &self,
        transcript: &mut Transcript,
        rs: &RelECDSA<T256Affine, 1>,
        rng: &mut R,
    ) -> Result<(Self::RelationTarget, Self::Proof), Self::Error>
    where
        R: RngCore + CryptoRng,
    {
        let t = start_timer!(|| "Group RoK Prover");

        self.initialize(rs, transcript);

        // assert the witness and y-coordinate exist
        let witness = rs
            .witness()
            .as_ref()
            .ok_or_else(|| PopError::MissingWitness(RelECDSA::<T256Affine, 1>::label()))?;
        if witness.rhoy().is_none() {
            return Err(PopError::MissingWitness(RelECDSA::<T256Affine, 1>::label()));
        }
        // compute the value Z
        let Z: Secp256r1Affine = (rs.statement().k() * witness.z()).into();

        // compute the commitment to Z
        let rhox = Fr::random(&mut *rng);
        let rhoy = Fr::random(&mut *rng);
        let scalars_x = [fp_to_fr(&Z.x), rhox];
        let scalars_y = [fp_to_fr(&Z.y), rhoy];

        // compute the commitment
        let bases = [self.G, self.H];
        let CZx: T256Affine = msm_function(&scalars_x, &bases).into();
        let CZy: T256Affine = msm_function(&scalars_y, &bases).into();

        // add the commitments to the transcript to allow composition
        transcript.append_point(b"CZx Commitment", &CZx);
        transcript.append_point(b"CZy Commitment", &CZy);

        // construct the statement and the witness for SM
        let (pp_sm, pp_pa) = (
            RelSMParams::new(self.G, self.H),
            RelPAParams::new(self.G, self.H),
        );
        let (x_sm, x_pa) = self.statements_from_proof(rs, CZx, CZy);
        let w_sm = RelSMWitness::new(Z, (rhox, rhoy), *witness.z());

        let P1 = GroupRoK::compute_alphaG(rs);
        let w_pa = RelPAWitness::new(
            [*witness.q(), P1, Z],
            [
                (witness.rhox()[0], witness.rhoy().unwrap()[0]),
                (Fr::ZERO, Fr::ZERO),
                (rhox, rhoy),
            ],
        );

        let r_sm = RelSM::new(pp_sm, x_sm, Some(w_sm));
        let r_pa = RelPA::new(pp_pa, x_pa, Some(w_pa));

        // create the product relation
        let rt = RelationProduct::from_parts(r_sm, r_pa);
        let proof = GroupRoKProof { CZx, CZy };

        end_timer!(t);
        Ok((rt, proof))
    }

    fn reduce_statement(
        &self,
        transcript: &mut Transcript,
        rs: &Self::RelationSource,
        proof: &Self::Proof,
    ) -> Result<Self::RelationTarget, Self::Error> {
        let t = start_timer!(|| "Group RoK Verifier");

        self.initialize(rs, transcript);

        let (CZx, CZy) = (proof.CZx, proof.CZy);

        // add the commitments to the transcript to allow composition
        transcript.append_point(b"CZx Commitment", &CZx);
        transcript.append_point(b"CZy Commitment", &CZy);

        // construct the statement and the witness for SM
        let (pp_sm, pp_pa) = (
            RelSMParams::new(self.G, self.H),
            RelPAParams::new(self.G, self.H),
        );
        let (x_sm, x_pa) = self.statements_from_proof(rs, CZx, CZy);

        let r_sm = RelSM::new(pp_sm, x_sm, None);
        let r_pa = RelPA::new(pp_pa, x_pa, None);

        // create the product relation
        let rt = RelationProduct::from_parts(r_sm, r_pa);

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

    use crate::relations::tests::sample_random_ecdsa_instance_with_key;

    use super::GroupRoK;

    #[test]
    fn group_rok() {
        // sample a random key for committing to R, Q
        let G = T256Affine::random(OsRng);
        let H = T256Affine::random(OsRng);

        // sample an ecdsa instance
        let recdsa = sample_random_ecdsa_instance_with_key::<T256Affine, 1>([G], H);

        let rok = GroupRoK { G, H };

        let mut transcript_prover = Transcript::new(b"Group RoK");
        let (rt_p, proof) = rok.reduce(&mut transcript_prover, &recdsa, &mut OsRng).unwrap();
        let result = rt_p.in_relation();
        assert!(result.is_ok(), "reduce failed: {:?}", result);

        let bytes = bincode::serialize(&proof).unwrap();
        println!("proof size: {} bytes", bytes.len());

        let mut transcript_verifier = Transcript::new(b"Group RoK");
        let result = rok.reduce_statement(&mut transcript_verifier, &recdsa, &proof);
        assert!(result.is_ok(), "reduce failed: {:?}", result);
    }
}
