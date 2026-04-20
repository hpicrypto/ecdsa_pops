//! [RoK] nizk to change curve.
//! It is a [RoK]: [RelECDSA]<BLS,2> -> [RelECDSA]<T256,1>

use ark_std::{end_timer, start_timer, One};
use ff::Field;
use halo2curves::{bls12381::G1Affine, t256::T256Affine};
use merlin::Transcript;
use num_bigint::BigUint;
use r1csipa::{msm_function, TranscriptProtocol};
use rand_core::{CryptoRng, RngCore};
use rok::{Nizk, Relation, RoK};
use serde::{Deserialize, Serialize};

use crate::{
    circuit::utils::{big_to_ff, ff_to_big},
    errors::PopError,
    relations::{
        rdleq::{RelDLEQ, RelDLEQStatement, RelDLEQWitness},
        recdsa::{RelECDSA, RelECDSAParams, RelECDSAStatement, RelECDSAWitness},
    },
    roks::dleq_rok::{DLEQRoKProof, DleqRoK},
    utils::{fp_to_fr, fp_to_scalars, Fp, Fr},
};

#[derive(Clone)]
/// A [RoK] reducing [RelECDSA]<BLS,2> -> [RelECDSA]<T256,1>
pub struct BlsToTomRoK {
    /// the [RelDLEQ] for the low limb
    dleq_rok_low_limb: DleqRoK<G1Affine, T256Affine>,
    /// the [RelDLEQ] for the high limb
    dleq_rok_high_limb: DleqRoK<G1Affine, T256Affine>,
}

impl BlsToTomRoK {
    /// creates [BlsToTomRoK] parameters given the two commitment keys
    /// using fixed values:
    ///
    /// - b_f = 8
    /// - b_x = 128
    /// - b_c = 112
    pub fn from_params(g_bls: &[G1Affine; 3], g_t256: &[T256Affine; 2]) -> Self {
        let ck_bls_low = vec![g_bls[0], g_bls[2]];
        let ck_bls_high = vec![g_bls[1], g_bls[2]];
        let ck_t256 = g_t256.to_vec();
        let (b_f, b_x, b_c) = (8, 128, 112);
        let dleq_rok_low_limb = DleqRoK {
            b_f,
            b_x,
            b_c,
            ck1: ck_bls_low,
            ck2: ck_t256.clone(),
        };
        let dleq_rok_high_limb = DleqRoK {
            b_f,
            b_x,
            b_c,
            ck1: ck_bls_high,
            ck2: ck_t256.clone(),
        };
        Self {
            dleq_rok_low_limb,
            dleq_rok_high_limb,
        }
    }

    /// Creates the two [RelECDSAStatement]s from a
    /// [RelECDSAStatement]/[RelECDSAWitness] pair
    fn dleq_from_witness<R>(
        &self,
        x_ecdsa: &RelECDSAStatement<G1Affine, 2>,
        w_ecdsa: &RelECDSAWitness<G1Affine, 2>,
        rng: &mut R,
    ) -> [RelDLEQ<G1Affine, T256Affine>; 2]
    where
        R: RngCore + CryptoRng,
    {
        // Qx as bls and t256 limbs
        let Qx_as_limbs_bls = fp_to_scalars::<G1Affine, 2>(&w_ecdsa.q().x).unwrap();
        let Qx_as_limbs_t256 = fp_to_scalars::<T256Affine, 2>(&w_ecdsa.q().x).unwrap();

        // sample commitment randomness for the two fresh t256 commitments
        let rho_t256_low_limb = fp_to_fr(&Fp::random(&mut *rng));
        let rho_t256_high_limb = fp_to_fr(&Fp::random(&mut *rng));

        // fresh t256 commitments
        let C_t256_limb_low = msm_function(
            [Qx_as_limbs_t256[0], rho_t256_low_limb].as_slice(),
            self.dleq_rok_low_limb.ck2.as_slice(),
        );
        let C_t256_limb_high = msm_function(
            [Qx_as_limbs_t256[1], rho_t256_high_limb].as_slice(),
            self.dleq_rok_high_limb.ck2.as_slice(),
        );

        // create the two dleq statements
        let x_low = RelDLEQStatement::<G1Affine, T256Affine> {
            C1: x_ecdsa.cx()[0],
            C2: C_t256_limb_low.into(),
        };
        let x_high = RelDLEQStatement::<G1Affine, T256Affine> {
            C1: x_ecdsa.cx()[1],
            C2: C_t256_limb_high.into(),
        };
        let w_low = RelDLEQWitness::<G1Affine, T256Affine> {
            // low limb
            m: ff_to_big(&Qx_as_limbs_bls[0]),
            // randomness of bls commitment
            r1: w_ecdsa.rhox()[0],
            // randomness of t256 commitment
            r2: rho_t256_low_limb,
        };
        let w_high = RelDLEQWitness::<G1Affine, T256Affine> {
            // high limb
            m: ff_to_big(&Qx_as_limbs_bls[1]),
            // randomness of bls commitment
            r1: w_ecdsa.rhox()[1],
            // randomness of t256 commitment
            r2: rho_t256_high_limb,
        };
        let r_low = RelDLEQ::new(self.dleq_rok_low_limb.clone().into(), x_low, Some(w_low));
        let r_high = RelDLEQ::new(self.dleq_rok_high_limb.clone().into(), x_high, Some(w_high));
        [r_low, r_high]
    }

    /// Creates the two [RelDLEQStatement] from a
    /// [RelECDSAStatement]/[DLEQRoKProof] pair
    fn dleq_from_proof(
        &self,
        x_ecdsa: &RelECDSAStatement<G1Affine, 2>,
        proof: &BlsToTomRoKProof,
    ) -> [RelDLEQ<G1Affine, T256Affine>; 2] {
        let x_low = RelDLEQStatement::<G1Affine, T256Affine> {
            C1: x_ecdsa.cx()[0],
            C2: proof.C_t256_low,
        };
        let x_high = RelDLEQStatement::<G1Affine, T256Affine> {
            C1: x_ecdsa.cx()[1],
            C2: proof.C_t256_high,
        };
        let r_low = RelDLEQ::new(self.dleq_rok_low_limb.clone().into(), x_low, None);
        let r_high = RelDLEQ::new(self.dleq_rok_high_limb.clone().into(), x_high, None);
        [r_low, r_high]
    }

    /// helper function to assert the parameters are correct
    fn check_params(&self) -> Result<(), PopError> {
        let (b_f, b_x, b_c) = (8, 128, 112);
        if self.dleq_rok_low_limb.b_x != b_x
            || self.dleq_rok_low_limb.b_f != b_f
            || self.dleq_rok_low_limb.b_c != b_c
            || self.dleq_rok_high_limb.b_x != b_x
            || self.dleq_rok_high_limb.b_f != b_f
            || self.dleq_rok_high_limb.b_c != b_c
            || self.dleq_rok_low_limb.ck2 != self.dleq_rok_high_limb.ck2
        {
            return Err(PopError::RoKError(Self::label() + ": bad parameters"));
        }
        Ok(())
    }
}

/// the proof consists of two t256 commitments and the two [DLEQRoKProof]s
#[derive(Debug, Serialize, Deserialize)]
pub struct BlsToTomRoKProof {
    C_t256_low: T256Affine,
    dleq_proof_low: DLEQRoKProof<G1Affine, T256Affine>,
    C_t256_high: T256Affine,
    dleq_proof_high: DLEQRoKProof<G1Affine, T256Affine>,
}

impl RoK for BlsToTomRoK {
    type RelationSource = RelECDSA<G1Affine, 2>;
    type RelationTarget = RelECDSA<T256Affine, 1>;
    // the proof is two Nizks of dlog equality acroos the two groups
    type Proof = BlsToTomRoKProof;
    type Error = PopError;

    fn label() -> String {
        "ECDSA in BLS to ECDSA in T256".into()
    }

    fn hash_statement(&self, rs: &Self::RelationSource, transcript: &mut Transcript) {
        // the bx,bc,bf values are the same in the two proofs
        transcript.append_u64(b"b_x: ", self.dleq_rok_low_limb.b_x as u64);
        transcript.append_u64(b"b_c: ", self.dleq_rok_low_limb.b_c as u64);
        transcript.append_u64(b"b_f: ", self.dleq_rok_low_limb.b_f as u64);
        // append commitment keyscommitment keys
        // TODO: make this look nicer, add some helper function
        [&self.dleq_rok_low_limb, &self.dleq_rok_high_limb].iter().for_each(|&dleq| {
            dleq.ck1.iter().zip(self.dleq_rok_low_limb.ck2.iter()).enumerate().for_each(
                |(j, (g_bls, g_t256))| {
                    transcript.append_u64(b"Append bls generator:", j as u64);
                    transcript.append_point(b"generator", g_bls);
                    transcript.append_u64(b"Append t256 generator:", j as u64);
                    transcript.append_point(b"generator", g_t256);
                },
            );
        });
        // /// Commitment to Qx
        transcript.append_point(b"BLS commitment to low limb", &rs.statement().cx()[0]);
        transcript.append_point(b"BLS commitment to high limb", &rs.statement().cx()[1]);
        transcript.append_scalar(b"signed message", rs.statement().m());
        transcript.append_point(b"ECDSA K", rs.statement().k());
    }

    fn reduce<R>(
        &self,
        transcript: &mut Transcript,
        rs: &Self::RelationSource,
        rng: &mut R,
    ) -> Result<(Self::RelationTarget, Self::Proof), Self::Error>
    where
        R: RngCore + CryptoRng,
    {
        let t = start_timer!(|| "BLS to T256 RoK Prover");

        self.check_params()?;
        self.initialize(rs, transcript);

        let witness = rs
            .witness()
            .as_ref()
            .ok_or_else(|| PopError::MissingWitness(RelECDSA::<G1Affine, 2>::label()))?;

        // create the two dleq statements
        let [r_low, r_high] = self.dleq_from_witness(rs.statement(), witness, rng);

        let dleq_proof_low = self.dleq_rok_low_limb.prove(transcript, &r_low, rng)?;
        let dleq_proof_high = self.dleq_rok_high_limb.prove(transcript, &r_high, rng)?;

        // create target statement
        // C = C_low + 2^128 C_high
        let shift = BigUint::one() << 128;
        let C_t256 = r_low.statement().C2 + r_high.statement().C2 * big_to_ff::<Fr>(&shift);
        // rho = rho_low + 2^128 rho_high
        let rho = [r_low.witness().as_ref().unwrap().r2
            + r_high.witness().as_ref().unwrap().r2 * big_to_ff::<Fr>(&shift)];

        let G_t256 = self.dleq_rok_low_limb.ck2[0];
        let H_t256 = self.dleq_rok_low_limb.ck2[1];
        let pp = RelECDSAParams::new([G_t256], H_t256, *rs.params().ecdsa());
        let x = RelECDSAStatement::new(
            [C_t256.into()],
            None,
            *rs.statement().m(),
            *rs.statement().k(),
        );
        let w = RelECDSAWitness::new(*witness.q(), *witness.z(), rho, None);

        let rt = RelECDSA::new(pp, x, Some(w));
        let proof = BlsToTomRoKProof {
            C_t256_low: r_low.statement().C2,
            dleq_proof_low,
            C_t256_high: r_high.statement().C2,
            dleq_proof_high,
        };

        end_timer!(t);
        Ok((rt, proof))
    }

    fn reduce_statement(
        &self,
        transcript: &mut Transcript,
        rs: &Self::RelationSource,
        proof: &Self::Proof,
    ) -> Result<Self::RelationTarget, Self::Error> {
        let t = start_timer!(|| "BLS to T256 RoK Verifier");

        self.check_params()?;
        self.initialize(rs, transcript);

        // verify the two dleq proofs
        let [r_low, r_high] = self.dleq_from_proof(rs.statement(), proof);
        self.dleq_rok_low_limb.verify(transcript, &r_low, &proof.dleq_proof_low)?;
        self.dleq_rok_high_limb.verify(transcript, &r_high, &proof.dleq_proof_high)?;

        // create target statement
        let shift = BigUint::one() << 128;
        let C_t256 = r_low.statement().C2 + r_high.statement().C2 * big_to_ff::<Fr>(&shift);

        let G_t256 = self.dleq_rok_low_limb.ck2[0];
        let H_t256 = self.dleq_rok_low_limb.ck2[1];
        let pp = RelECDSAParams::new([G_t256], H_t256, *rs.params().ecdsa());
        let x = RelECDSAStatement::new(
            [C_t256.into()],
            None,
            *rs.statement().m(),
            *rs.statement().k(),
        );
        let rt = RelECDSA::new(pp, x, None);
        end_timer!(t);
        Ok(rt)
    }
}

#[cfg(test)]
mod tests {

    use halo2curves::{bls12381::G1Affine, t256::T256Affine};
    use merlin::Transcript;
    use rand_core::OsRng;
    use rok::{Relation, RoK};

    use crate::{
        relations::tests::{pedersen_key, sample_random_ecdsa_instance},
        roks::{bls_to_tom::BlsToTomRoK, dleq_rok::DleqRoK},
    };

    #[test]
    fn test_bls_to_tom_rok() {
        // sample t256 commitment keys
        let ck_t256 = pedersen_key::<T256Affine>(2, "test_bls_to_tom_rok");

        // sample a random ecdsa statement with two limbs
        let rs = sample_random_ecdsa_instance::<G1Affine, 2>();

        // the two bls keys
        let ck_bls_low = vec![rs.params().gs()[0], *rs.params().h()];
        let ck_bls_high = vec![rs.params().gs()[1], *rs.params().h()];

        // sample two dleq statements
        let dleq_rok_low_limb = DleqRoK {
            b_x: 128,
            b_c: 112,
            b_f: 8,
            ck1: ck_bls_low,
            ck2: ck_t256.clone(),
        };

        let dleq_rok_high_limb = DleqRoK {
            b_x: 128,
            b_c: 112,
            b_f: 8,
            ck1: ck_bls_high,
            ck2: ck_t256,
        };

        let rok = BlsToTomRoK {
            dleq_rok_low_limb,
            dleq_rok_high_limb,
        };

        let mut transcript_prover = Transcript::new(b"bls_to_tom_rok test");
        let (rt, proof) = rok.reduce(&mut transcript_prover, &rs, &mut OsRng).unwrap();
        assert!(rt.in_relation().is_ok());

        let bytes = bincode::serialize(&proof).unwrap();
        println!("proof size: {} bytes", bytes.len());

        let mut transcript_verifier = Transcript::new(b"bls_to_tom_rok test");
        let result = rok.reduce_statement(&mut transcript_verifier, &rs, &proof);
        assert!(result.is_ok(), "reduce failed: {:?}", result);
    }
}
