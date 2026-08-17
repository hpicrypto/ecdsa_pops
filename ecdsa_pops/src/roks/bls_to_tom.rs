//! [RoK] nizk to change curve.
//! It is a [RoK]: [RelECDSA]<BLS,2> -> [RelECDSA]<T256,1>

// TODO: It would be nice to refactor this and abstract parts/remove repetitive
// code

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
    circuit_native::utils::{big_to_ff, ff_to_big},
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
    /// the [DleqRoK] used
    dleq_rok: DleqRoK<G1Affine, T256Affine>,
}

// TODO: there is to much repetition. Refactor and make nicer.
impl BlsToTomRoK {
    /// creates [BlsToTomRoK] parameters given the two commitment keys
    /// using fixed values:
    ///
    /// - b_f = 8
    /// - b_x = 128
    /// - b_c = 112
    pub fn from_params(g_bls: &[G1Affine; 2], g_t256: &[T256Affine; 2]) -> Self {
        let ck_bls = vec![g_bls[0], g_bls[1]];
        let ck_t256 = g_t256.to_vec();
        let (b_f, b_x, b_c) = (8, 128, 112);
        let dleq_rok = DleqRoK {
            b_f,
            b_x,
            b_c,
            ck1: ck_bls,
            ck2: ck_t256.clone(),
        };
        Self { dleq_rok }
    }

    /// Creates the two [RelECDSAStatement]s from a
    /// [RelECDSAStatement]/[RelECDSAWitness] pair
    fn dleq_from_witness<R>(
        &self,
        x_ecdsa: &RelECDSAStatement<G1Affine, 2>,
        w_ecdsa: &RelECDSAWitness<G1Affine, 2>,
        rng: &mut R,
    ) -> (
        [RelDLEQ<G1Affine, T256Affine>; 2],
        [Option<RelDLEQ<G1Affine, T256Affine>>; 2],
    )
    where
        R: RngCore + CryptoRng,
    {
        // Q as bls and t256 limbs
        let Qx_as_limbs_bls = fp_to_scalars::<G1Affine, 2>(&w_ecdsa.q().x).unwrap();
        let Qx_as_limbs_t256 = fp_to_scalars::<T256Affine, 2>(&w_ecdsa.q().x).unwrap();
        let Qy_as_limbs_bls = fp_to_scalars::<G1Affine, 2>(&w_ecdsa.q().y).unwrap();
        let Qy_as_limbs_t256 = fp_to_scalars::<T256Affine, 2>(&w_ecdsa.q().y).unwrap();

        // sample commitment randomness for the fresh t256 commitments
        let rhox_t256_low_limb = fp_to_fr(&Fp::random(&mut *rng));
        let rhox_t256_high_limb = fp_to_fr(&Fp::random(&mut *rng));
        let rhoy_t256_low_limb = x_ecdsa.cy().map(|_| fp_to_fr(&Fp::random(&mut *rng)));
        let rhoy_t256_high_limb = x_ecdsa.cy().map(|_| fp_to_fr(&Fp::random(&mut *rng)));

        // fresh t256 commitments
        let Cx_t256_limb_low = msm_function(
            [Qx_as_limbs_t256[0], rhox_t256_low_limb].as_slice(),
            self.dleq_rok.ck2.as_slice(),
        );
        let Cx_t256_limb_high = msm_function(
            [Qx_as_limbs_t256[1], rhox_t256_high_limb].as_slice(),
            self.dleq_rok.ck2.as_slice(),
        );
        let Cy_t256_limb_low = rhoy_t256_low_limb.map(|rho| {
            msm_function(
                [Qy_as_limbs_t256[0], rho].as_slice(),
                self.dleq_rok.ck2.as_slice(),
            )
        });
        let Cy_t256_limb_high = rhoy_t256_high_limb.map(|rho| {
            msm_function(
                [Qy_as_limbs_t256[1], rho].as_slice(),
                self.dleq_rok.ck2.as_slice(),
            )
        });

        // create the two dleq statements for x
        let x_low = RelDLEQStatement::<G1Affine, T256Affine> {
            C1: x_ecdsa.cx()[0],
            C2: Cx_t256_limb_low.into(),
        };
        let x_high = RelDLEQStatement::<G1Affine, T256Affine> {
            C1: x_ecdsa.cx()[1],
            C2: Cx_t256_limb_high.into(),
        };
        let w_low = RelDLEQWitness::<G1Affine, T256Affine> {
            // low limb
            m: ff_to_big(&Qx_as_limbs_bls[0]),
            // randomness of bls commitment
            r1: w_ecdsa.rhox()[0],
            // randomness of t256 commitment
            r2: rhox_t256_low_limb,
        };
        let w_high = RelDLEQWitness::<G1Affine, T256Affine> {
            // high limb
            m: ff_to_big(&Qx_as_limbs_bls[1]),
            // randomness of bls commitment
            r1: w_ecdsa.rhox()[1],
            // randomness of t256 commitment
            r2: rhox_t256_high_limb,
        };
        let rx_low = RelDLEQ::new(self.dleq_rok.clone().into(), x_low, Some(w_low));
        let rx_high = RelDLEQ::new(self.dleq_rok.clone().into(), x_high, Some(w_high));

        // create the two dleq statements for y if they exist
        let (ry_low, ry_high) = match x_ecdsa.cy() {
            Some(y) => {
                let x_low = RelDLEQStatement::<G1Affine, T256Affine> {
                    C1: y[0],
                    C2: Cy_t256_limb_low.unwrap().into(),
                };
                let x_high = RelDLEQStatement::<G1Affine, T256Affine> {
                    C1: y[1],
                    C2: Cy_t256_limb_high.unwrap().into(),
                };
                let w_low = RelDLEQWitness::<G1Affine, T256Affine> {
                    // low limb
                    m: ff_to_big(&Qy_as_limbs_bls[0]),
                    // randomness of bls commitment
                    r1: w_ecdsa.rhoy().unwrap()[0],
                    // randomness of t256 commitment
                    r2: rhoy_t256_low_limb.unwrap(),
                };
                let w_high = RelDLEQWitness::<G1Affine, T256Affine> {
                    // high limb
                    m: ff_to_big(&Qy_as_limbs_bls[1]),
                    // randomness of bls commitment
                    r1: w_ecdsa.rhoy().unwrap()[1],
                    // randomness of t256 commitment
                    r2: rhoy_t256_high_limb.unwrap(),
                };
                let ry_low = RelDLEQ::new(self.dleq_rok.clone().into(), x_low, Some(w_low));
                let ry_high = RelDLEQ::new(self.dleq_rok.clone().into(), x_high, Some(w_high));
                (Some(ry_low), Some(ry_high))
            }
            None => (None, None),
        };
        ([rx_low, rx_high], [ry_low, ry_high])
    }

    /// Creates the two [RelDLEQStatement] from a
    /// [RelECDSAStatement]/[DLEQRoKProof] pair
    fn dleq_from_proof(
        &self,
        x_ecdsa: &RelECDSAStatement<G1Affine, 2>,
        proof: &BlsToTomRoKProof,
    ) -> (
        [RelDLEQ<G1Affine, T256Affine>; 2],
        [Option<RelDLEQ<G1Affine, T256Affine>>; 2],
    ) {
        let x_low = RelDLEQStatement::<G1Affine, T256Affine> {
            C1: x_ecdsa.cx()[0],
            C2: proof.Cx_t256_low,
        };
        let x_high = RelDLEQStatement::<G1Affine, T256Affine> {
            C1: x_ecdsa.cx()[1],
            C2: proof.Cx_t256_high,
        };
        let rx_low = RelDLEQ::new(self.dleq_rok.clone().into(), x_low, None);
        let rx_high = RelDLEQ::new(self.dleq_rok.clone().into(), x_high, None);
        let (ry_low, ry_high) = match x_ecdsa.cy() {
            Some(y) => {
                let y_low = RelDLEQStatement::<G1Affine, T256Affine> {
                    C1: y[0],
                    C2: proof.Cy_t256_low.unwrap(),
                };
                let y_high = RelDLEQStatement::<G1Affine, T256Affine> {
                    C1: y[1],
                    C2: proof.Cy_t256_high.unwrap(),
                };
                let ry_low = RelDLEQ::new(self.dleq_rok.clone().into(), y_low, None);
                let ry_high = RelDLEQ::new(self.dleq_rok.clone().into(), y_high, None);
                (Some(ry_low), Some(ry_high))
            }
            None => (None, None),
        };
        ([rx_low, rx_high], [ry_low, ry_high])
    }

    /// helper function to assert the parameters are correct
    fn check_params(&self) -> Result<(), PopError> {
        let (b_f, b_x, b_c) = (8, 128, 112);
        if self.dleq_rok.b_x != b_x || self.dleq_rok.b_f != b_f || self.dleq_rok.b_c != b_c {
            return Err(PopError::RoKError(Self::label() + ": bad parameters"));
        }
        Ok(())
    }
}

/// the proof consists of two t256 commitments and the two [DLEQRoKProof]s
#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct BlsToTomRoKProof {
    Cx_t256_low: T256Affine,
    dleq_proof_xlow: DLEQRoKProof<G1Affine, T256Affine>,
    Cx_t256_high: T256Affine,
    dleq_proof_xhigh: DLEQRoKProof<G1Affine, T256Affine>,
    Cy_t256_low: Option<T256Affine>,
    dleq_proof_ylow: Option<DLEQRoKProof<G1Affine, T256Affine>>,
    Cy_t256_high: Option<T256Affine>,
    dleq_proof_yhigh: Option<DLEQRoKProof<G1Affine, T256Affine>>,
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
        transcript.append_u64(b"b_x: ", self.dleq_rok.b_x as u64);
        transcript.append_u64(b"b_c: ", self.dleq_rok.b_c as u64);
        transcript.append_u64(b"b_f: ", self.dleq_rok.b_f as u64);
        // append commitment keyscommitment keys
        // TODO: make this look nicer, add some helper function
        self.dleq_rok.ck1.iter().zip(self.dleq_rok.ck2.iter()).enumerate().for_each(
            |(j, (g_bls, g_t256))| {
                transcript.append_u64(b"Append bls generator:", j as u64);
                transcript.append_point(b"generator", g_bls);
                transcript.append_u64(b"Append t256 generator:", j as u64);
                transcript.append_point(b"generator", g_t256);
            },
        );
        // Commitment to Qx
        transcript.append_point(b"BLS commitment to low limb", &rs.statement().cx()[0]);
        transcript.append_point(b"BLS commitment to high limb", &rs.statement().cx()[1]);
        // Commitment to Qy if it exists
        if rs.statement().cy().is_some() {
            transcript.append_point(
                b"BLS commitment to low limb",
                &rs.statement().cy().unwrap()[0],
            );
            transcript.append_point(
                b"BLS commitment to high limb",
                &rs.statement().cy().unwrap()[1],
            );
        }
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
        let ([rx_low, rx_high], [ry_low, ry_high]) =
            self.dleq_from_witness(rs.statement(), witness, rng);

        let dleq_proof_xlow = self.dleq_rok.prove(transcript, &rx_low, rng)?;
        let dleq_proof_xhigh = self.dleq_rok.prove(transcript, &rx_high, rng)?;
        let dleq_proof_ylow = ry_low
            .clone()
            .map(|ry_low| self.dleq_rok.prove(transcript, &ry_low, rng))
            .transpose()?;
        let dleq_proof_yhigh = ry_high
            .clone()
            .map(|ry_high| self.dleq_rok.prove(transcript, &ry_high, rng))
            .transpose()?;

        // create target statement
        // Cx = Cx_low + 2^128 Cx_high
        let shift = BigUint::one() << 128;
        let Cx_t256 = rx_low.statement().C2 + rx_high.statement().C2 * big_to_ff::<Fr>(&shift);
        // rho = rho_low + 2^128 rho_high
        let rhox = [rx_low.witness().as_ref().unwrap().r2
            + rx_high.witness().as_ref().unwrap().r2 * big_to_ff::<Fr>(&shift)];
        let (Cy_t256, rhoy) = match (&ry_low, &ry_high) {
            (Some(ry_low), Some(ry_high)) => {
                let Cy_t256: T256Affine = (ry_low.statement().C2
                    + ry_high.statement().C2 * big_to_ff::<Fr>(&shift))
                .into();
                // rho = rho_low + 2^128 rho_high
                let rhoy = [ry_low.witness().as_ref().unwrap().r2
                    + ry_high.witness().as_ref().unwrap().r2 * big_to_ff::<Fr>(&shift)];
                (Some([Cy_t256]), Some(rhoy))
            }
            _ => (None, None),
        };

        let G_t256 = self.dleq_rok.ck2[0];
        let H_t256 = self.dleq_rok.ck2[1];
        let pp = RelECDSAParams::new([G_t256], H_t256, *rs.params().ecdsa());
        let x = RelECDSAStatement::new(
            [Cx_t256.into()],
            Cy_t256,
            *rs.statement().m(),
            *rs.statement().k(),
        );
        let w = RelECDSAWitness::new(*witness.q(), *witness.z(), rhox, rhoy);

        let rt = RelECDSA::new(pp, x, Some(w));
        let proof = BlsToTomRoKProof {
            Cx_t256_low: rx_low.statement().C2,
            dleq_proof_xlow,
            Cx_t256_high: rx_high.statement().C2,
            dleq_proof_xhigh,
            Cy_t256_low: ry_low.map(|ry_low| ry_low.statement().C2),
            Cy_t256_high: ry_high.map(|ry_high| ry_high.statement().C2),
            dleq_proof_ylow,
            dleq_proof_yhigh,
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
        let ([rx_low, rx_high], [ry_low, ry_high]) = self.dleq_from_proof(rs.statement(), proof);
        self.dleq_rok.verify(transcript, &rx_low, &proof.dleq_proof_xlow)?;
        self.dleq_rok.verify(transcript, &rx_high, &proof.dleq_proof_xhigh)?;
        if rs.statement().cy().is_some() {
            let ry_low = ry_low.clone().ok_or(PopError::RoKError(
                Self::label() + ": missing dleq proofs for y",
            ))?;
            let ry_high = ry_high.clone().ok_or(PopError::RoKError(
                Self::label() + ": missing dleq proofs for y",
            ))?;
            let dleq_proof_ylow = proof.dleq_proof_ylow.clone().ok_or(PopError::RoKError(
                Self::label() + ": missing dleq proofs for y",
            ))?;
            let dleq_proof_yhigh = proof.dleq_proof_yhigh.clone().ok_or(PopError::RoKError(
                Self::label() + ": missing dleq proofs for y",
            ))?;
            self.dleq_rok.verify(transcript, &ry_low, &dleq_proof_ylow)?;
            self.dleq_rok.verify(transcript, &ry_high, &dleq_proof_yhigh)?;
        }

        // create target statement
        let shift = BigUint::one() << 128;
        let Cx_t256 = rx_low.statement().C2 + rx_high.statement().C2 * big_to_ff::<Fr>(&shift);
        let Cy_t256: Option<[T256Affine; 1]> = ry_low
            .zip(ry_high)
            .map(|(ry_low, ry_high)| {
                (ry_low.statement().C2 + ry_high.statement().C2 * big_to_ff::<Fr>(&shift)).into()
            })
            .map(|C| [C]);

        let G_t256 = self.dleq_rok.ck2[0];
        let H_t256 = self.dleq_rok.ck2[1];
        let pp = RelECDSAParams::new([G_t256], H_t256, *rs.params().ecdsa());
        let x = RelECDSAStatement::new(
            [Cx_t256.into()],
            Cy_t256,
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
        let mut rs = sample_random_ecdsa_instance::<G1Affine, 2>();

        // the two bls keys
        let ck_bls = vec![rs.params().gs()[0], *rs.params().h()];

        // sample two dleq statements
        let dleq_rok = DleqRoK {
            b_x: 128,
            b_c: 112,
            b_f: 8,
            ck1: ck_bls,
            ck2: ck_t256.clone(),
        };
        let rok = BlsToTomRoK { dleq_rok };

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
