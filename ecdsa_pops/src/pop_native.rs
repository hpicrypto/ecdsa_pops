use halo2curves::{
    bls12381::{G1Affine, G1},
    t256::{T256Affine, T256},
    CurveExt,
};
use r1csipa::R1CSProofParams;
use rok::{rok_compose, rok_compose_type, Nizk, RoK};

use crate::{
    circuit::CSchnorrCircuit,
    errors::PopError,
    roks::{
        bls_to_tom::BlsToTomRoK, circuit_rok::CircuitRoK, cschnorr_rok::CSchnorrRoK,
        pedersen_rok::PedersenRoK,
    },
    RelECDSA,
};

/// A proof of possesion of a P256 signature using native arithmetic
pub struct PoPNativeNizk {
    /// A Bls Generator for committing to the limbs of pk
    ck_bls: G1Affine,
    /// A Bls Generator for blinding
    ck_bls_blinding: G1Affine,
    /// A T256 generator for commiting to ECDSA pk Qx
    ck_t256_Qx: T256Affine,
    /// A T256 generator for commiting to CSChnorr commitment Rx
    ck_t256_Rx: T256Affine,
    /// A common T256 generator for blinding
    ck_t256_blinding: T256Affine,
    /// The universal parameters of the circuit
    circuit_params: R1CSProofParams<T256Affine>,
}

impl PoPNativeNizk {
    /// Returns the BLS commitment generator.
    pub fn ck_bls(&self) -> &G1Affine {
        &self.ck_bls
    }

    /// Returns the BLS blinding generator.
    pub fn ck_bls_blinding(&self) -> &G1Affine {
        &self.ck_bls_blinding
    }

    /// Returns the T256 generator for Qx.
    pub fn ck_t256_qx(&self) -> &T256Affine {
        &self.ck_t256_Qx
    }

    /// Returns the T256 generator for Rx.
    pub fn ck_t256_rx(&self) -> &T256Affine {
        &self.ck_t256_Rx
    }

    /// Returns the T256 blinding generator.
    pub fn ck_t256_blinding(&self) -> &T256Affine {
        &self.ck_t256_blinding
    }

    /// Returns the circuit proof parameters.
    pub fn circuit_params(&self) -> &R1CSProofParams<T256Affine> {
        &self.circuit_params
    }
}

type CSchnorrRoKT256128 = CSchnorrRoK<T256Affine, 16, 1>;
type CircuitRoK128 = CircuitRoK<T256Affine, 16>;
type PedersenRoKT256 = PedersenRoK<T256Affine>;

/// The type of the composed rok to prove proof-of-possession
///
/// We don't open the commitment used in the circuit since we can extract the
/// opening from the previous proofs
type PoPNativeComposedRoK = rok_compose_type!(
    PopError;
    // RelECDSA<BLS> ---> RelECDSA<T256> ---> (RelCSchnorr x RelPedersen) ---> (RelPedersen x Trivial)
    ((CircuitRoK128 x PedersenRoKT256) o CSchnorrRoKT256128) o BlsToTomRoK
);

impl PoPNativeNizk {
    /// Given a label, produces parameters for [PoPNativeNizk]
    pub fn new(label: &str) -> Self {
        let circuit_params = CSchnorrCircuit::<16>::universal_parameters(label);
        let label = [label, ": BLS committed input parameters"].concat();
        let hasher_bls = G1::hash_to_curve(&label);
        let ck_bls = hasher_bls(b"ck_bls").into();
        let ck_bls_blinding = hasher_bls(b"ck_bls_blinding").into();
        let hasher_t256 = T256::hash_to_curve(&label);
        let ck_t256_Qx = hasher_t256(b"ck_t256_Qx").into();
        let ck_t256_Rx = hasher_t256(b"ck_t256_Rx").into();
        let ck_t256_blinding = hasher_t256(b"ck_t256_blinding").into();

        Self {
            ck_bls,
            ck_bls_blinding,
            ck_t256_Qx,
            ck_t256_Rx,
            ck_t256_blinding,
            circuit_params,
        }
    }

    /// Given a statement, specializes parameters and creates the composed rok
    fn get_rok(&self) -> PoPNativeComposedRoK {
        // bls_to_tom_rok rok
        let ck_bls = [self.ck_bls, self.ck_bls_blinding];
        let ck_tom = [self.ck_t256_Qx, self.ck_t256_blinding];
        let bls_to_tom_rok = BlsToTomRoK::from_params(&ck_bls, &ck_tom);
        let cschnorr_rok = CSchnorrRoK::<T256Affine, 16, 1> {
            G_R: vec![self.ck_t256_Rx],
            G_Q: vec![self.ck_t256_Qx],
            H: self.ck_t256_blinding,
        };
        // the circuit replaces the generators for committed input with ck_ci
        let ck_ci = vec![self.ck_t256_Rx, self.ck_t256_Qx, self.ck_t256_blinding];
        let circuit_rok = CircuitRoK::<T256Affine, 16> {
            universal_params: self.circuit_params.clone(),
            ck_ci: ck_ci.clone(),
        };
        let pederen_rok = PedersenRoK::<T256Affine> {
            ck: vec![ck_ci[0], ck_ci[2]],
        };
        // return the composed RoK
        //
        // NOTE: We don't need to prove the last RelPedersen. In particular,
        // - the opening of the commitment  Qx is known by the application of bls_to_tom_rok
        // - the opening of the commitment  Rx is known by the pedersen rok
        // - these opening constitute an opening to the compact commitment used in the circuit
        rok_compose!(
            PopError;
            // RelECDSA<BLS> ---> RelECDSA<T256> ---> (RelCSchnorr x RelPedersen) ---> (RelPedersen x Trivial)
            ((circuit_rok x pederen_rok) o cschnorr_rok) o bls_to_tom_rok
        )
    }
}

impl Nizk for PoPNativeNizk {
    type Relation = RelECDSA<G1Affine, 2>;
    type Proof = <PoPNativeComposedRoK as RoK>::Proof;
    type Error = PopError;

    fn label() -> String {
        PoPNativeComposedRoK::label()
    }

    fn hash_statement(&self, r: &Self::Relation, transcript: &mut merlin::Transcript) {
        self.get_rok().hash_statement(r, transcript)
    }

    fn prove<R>(
        &self,
        transcript: &mut merlin::Transcript,
        r: &Self::Relation,
        rng: &mut R,
    ) -> Result<Self::Proof, Self::Error>
    where
        R: rand_core::RngCore + rand_core::CryptoRng,
    {
        self.get_rok().reduce(transcript, r, rng).map(|r| r.1)
    }

    fn verify(
        &self,
        transcript: &mut merlin::Transcript,
        r: &Self::Relation,
        proof: &Self::Proof,
    ) -> Result<(), Self::Error> {
        self.get_rok().reduce_statement(transcript, r, proof)?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {

    use halo2curves::bls12381::G1Affine;
    use merlin::Transcript;
    use rand_core::OsRng;
    use rok::{Nizk, Relation};

    use crate::{
        relations::{recdsa::RelECDSA, tests::sample_random_ecdsa_instance_with_key},
        PoPNativeNizk,
    };

    #[test]
    fn test_popnative_nizk() {
        let nizk = PoPNativeNizk::new("test popnative");

        // sample a random statement
        let mut r = sample_random_ecdsa_instance_with_key::<G1Affine, 2>(
            [nizk.ck_bls, nizk.ck_bls],
            nizk.ck_bls_blinding,
        );
        r.remove_cy();
        assert!(r.in_relation().is_ok());

        let mut transcript_prover = Transcript::new(b"pop native proof");
        let proof = nizk.prove(&mut transcript_prover, &r, &mut OsRng).unwrap();

        let bytes = bincode::serialize(&proof).unwrap();
        println!("proof size: {} bytes", bytes.len());

        let r_verifier = RelECDSA::new(r.params().clone(), r.statement().clone(), None);

        let mut transcript_verifier = Transcript::new(b"pop native proof");
        let result = nizk.verify(&mut transcript_verifier, &r_verifier, &proof);

        assert!(result.is_ok(), "nizk failed: {:?}", result);
    }
}
