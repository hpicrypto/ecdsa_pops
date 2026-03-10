//! [RoK] reducing [RelCSchnorr] -> [RelPedersen]
//!
//! The RoK Runs the circuit proofs and reduces to verifying the prover knows a valid opening
//! of the committed inputs

// TODO: Change how rng works in circuit and apply here
use ark_std::{end_timer, start_timer};
use ff::PrimeField;
use halo2curves::{secp256r1::Secp256r1Affine, t256::T256Affine, CurveAffine};
use r1csipa::{R1CSProof, R1CSProofParams, TranscriptProtocol};
use rok::{Relation, RoK};

use crate::{
    circuit::{CSchnorrCircuit, CschnorrCircuitPrivateInputs, CschnorrCircuitPublicInputs},
    errors::PopError,
    relations::{
        rcshnorr::RelCSchnorr,
        rpedersen::{RelPedersen, RelPedersenParams, RelPedersenStatement, RelPedersenWitness},
    },
    utils::fp_to_fr,
};

/// [RoK] for reducing [RelCSchnorr] -> [RelPedersen] using a circuit proof
#[derive(Clone)]
pub struct CircuitRoK<C, const SEC_PARAM_BYTES: usize>
where
    C: CurveAffine,
    C::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    /// universal parameters for the Circuit family
    pub(crate) universal_params: R1CSProofParams<C>,
    /// commitment key for committed input
    pub(crate) ck_ci: Vec<C>,
}

impl<const SEC_PARAM_BYTES: usize> CircuitRoK<T256Affine, SEC_PARAM_BYTES> {
    /// hash the circuit parameters
    pub(crate) fn hash_params(
        params: &R1CSProofParams<T256Affine>,
        ck_ci: &[T256Affine],
        transcript: &mut merlin::Transcript,
    ) {
        params
            .basesG
            .iter()
            .zip(params.basesH.iter())
            .enumerate()
            .for_each(|(i, (g, h))| {
                transcript.append_u64(b"Append G generator:", i as u64);
                transcript.append_point(b"generator", g);
                transcript.append_u64(b"Append H generator:", i as u64);
                transcript.append_point(b"generator", h);
            });
        transcript.append_point(b"Append U generator", &params.U);
        transcript.append_point(b"Append V generator", &params.V);
        ck_ci.iter().enumerate().for_each(|(i, g)| {
            transcript.append_u64(b"Append committed input generator:", i as u64);
            transcript.append_point(b"generator", g);
        });
    }
}

impl<const SEC_PARAM_BYTES: usize> RoK for CircuitRoK<T256Affine, SEC_PARAM_BYTES> {
    /// one field element is enough to encode P256 bases to T256 Scalar
    type RelationSource = RelCSchnorr<T256Affine, SEC_PARAM_BYTES, 1>;
    type RelationTarget = RelPedersen<T256Affine>;
    type Proof = R1CSProof<T256Affine>;
    type Error = PopError;

    fn hash_statement(&self, rs: &Self::RelationSource, transcript: &mut merlin::Transcript) {
        Self::hash_params(&self.universal_params, &self.ck_ci, transcript);
        transcript.append_point(b"C", &rs.statement().C);
        transcript.append_point(b"T", &rs.statement().T);
        transcript.append_scalar(b"c", &rs.statement().c);
    }

    fn label() -> String {
        "PoP: Circuit proof".into()
    }
    fn reduce<R>(
        &self,
        transcript: &mut merlin::Transcript,
        rs: &Self::RelationSource,
        _rng: &mut R,
    ) -> Result<(Self::RelationTarget, Self::Proof), Self::Error>
    where
        R: rand_core::RngCore + rand_core::CryptoRng,
    {
        let t = start_timer!(|| format!("Circuit RoK ({}) Prover", rs.params().ck.len()));

        self.initialize(rs, transcript);

        let witness = rs.witness().as_ref().ok_or_else(|| {
            PopError::MissingWitness(RelCSchnorr::<T256Affine, SEC_PARAM_BYTES, 1>::label())
        })?;

        // create the circuit and hash the parameters
        let private_inputs = CschnorrCircuitPrivateInputs::new(witness.R, witness.Q, witness.rho);
        let public_inputs =
            CschnorrCircuitPublicInputs::<SEC_PARAM_BYTES>::new(rs.statement().T, rs.statement().c);
        let circuit = CSchnorrCircuit::new(Some(private_inputs), public_inputs);
        let (mut params, shape) =
            CSchnorrCircuit::specialize_parameters(&circuit, &self.universal_params);

        // prove the circuit and get the committed inptus
        let proof = circuit.cshnorr_circuit_prove(&mut params, &shape, &self.ck_ci, transcript);

        // create the target statement
        let pp = RelPedersenParams {
            ck: rs.params().ck.clone(),
        };
        let x = RelPedersenStatement {
            C: rs.statement().C,
        };
        let w = RelPedersenWitness {
            m: vec![fp_to_fr(&witness.R.x), fp_to_fr(&witness.Q.x), witness.rho],
        };
        let rt = RelPedersen::new(pp, x, Some(w));

        end_timer!(t);

        Ok((rt, proof))
    }

    fn reduce_statement(
        &self,
        transcript: &mut merlin::Transcript,
        rs: &Self::RelationSource,
        proof: &Self::Proof,
    ) -> Result<Self::RelationTarget, Self::Error> {
        let t = start_timer!(|| format!("Circuit RoK ({}) Verifier", rs.params().ck.len()));

        self.initialize(rs, transcript);

        // create the circuit and hash the parameters
        let public_inputs =
            CschnorrCircuitPublicInputs::<SEC_PARAM_BYTES>::new(rs.statement().T, rs.statement().c);
        let circuit = CSchnorrCircuit::new(None, public_inputs);
        let (mut params, shape) =
            CSchnorrCircuit::specialize_parameters(&circuit, &self.universal_params);

        // verify the circuit using the rt committed inputs get the committed inptus
        circuit.cshnorr_circuit_verify(
            &mut params,
            &shape,
            &self.ck_ci,
            &rs.statement().C,
            proof,
            transcript,
        )?;

        // create the target statement of RelPedersen
        let pp = RelPedersenParams {
            ck: rs.params().ck.clone(),
        };
        let x = RelPedersenStatement {
            C: rs.statement().C,
        };
        let rt = RelPedersen::new(pp, x, None);

        end_timer!(t);

        Ok(rt)
    }
}

#[cfg(test)]
mod tests {

    use ff::Field;
    use halo2curves::group::Curve;
    use halo2curves::secp256r1::Secp256r1Affine;
    use halo2curves::t256::T256Affine;
    use merlin::Transcript;
    use num_bigint::BigUint;
    use r1csipa::msm_function;
    use rand_core::{OsRng, RngCore};
    use rok::rok_compose;
    use rok::Nizk;
    use rok::Relation;
    use rok::RoK;

    use crate::circuit::utils::biguint_to_scalar;

    use crate::circuit::CSchnorrCircuit;
    use crate::errors::PopError;
    use crate::relations::rcshnorr::{
        RelCSchnorr, RelCSchnorrParams, RelCSchnorrStatement, RelCSchnorrWitness,
    };
    use crate::relations::tests::pedersen_key;
    use crate::roks::circuit_rok::CircuitRoK;
    use crate::roks::pedersen_rok::PedersenRoK;
    use crate::utils::{fp_to_fr, Fp, Fq};

    // sample a field element from bytes
    fn c_from_bytes<const SEC_PARAM_BYTES: usize>(bytes: [u8; SEC_PARAM_BYTES]) -> Fq {
        let c_big = BigUint::from_bytes_be(&bytes);
        biguint_to_scalar::<Fq>(&c_big)
    }

    // sample a random instance
    fn sample_random_relation<const SEC_PARAM_BYTES: usize>(
        ck_ci: &[T256Affine],
    ) -> RelCSchnorr<T256Affine, SEC_PARAM_BYTES, 1> {
        // sample a random challenge of SEC_PARAM_BYTES  bytes
        let mut bytes = [0u8; SEC_PARAM_BYTES];
        OsRng.fill_bytes(&mut bytes);
        let c = c_from_bytes::<SEC_PARAM_BYTES>(bytes);

        // sample random group elements R, Q
        let R = Secp256r1Affine::random(OsRng);
        let Q = Secp256r1Affine::random(OsRng);

        let T = ((R * c) + Q).to_affine();

        // sample commitment randomness
        let rho = Fp::random(OsRng);

        let scalars = [R.x, Q.x, rho].map(|s| fp_to_fr(&s));
        let C = msm_function(&scalars, ck_ci).into();

        let pp = RelCSchnorrParams { ck: ck_ci.to_vec() };
        let x = RelCSchnorrStatement { C, c, T };
        let w = RelCSchnorrWitness {
            R,
            Q,
            rho: fp_to_fr(&rho),
        };
        RelCSchnorr::new(pp, x, Some(w))
    }

    #[test]
    fn test_circuit_rok() {
        let universal_params = CSchnorrCircuit::<16>::universal_parameters("test circuit rok");
        let ck_ci = pedersen_key::<T256Affine>(3, "ck_ci");
        let rs_prover = sample_random_relation::<16>(&ck_ci);
        let rs_verifier = RelCSchnorr::<T256Affine, 16, 1>::new(
            rs_prover.params().clone(),
            rs_prover.statement().clone(),
            None,
        );

        let circuit_rok = CircuitRoK {
            universal_params,
            ck_ci,
        };

        let mut transcript_prover = Transcript::new(b"circuit_rok test");
        let (_rt, proof) =
            circuit_rok.reduce(&mut transcript_prover, &rs_prover, &mut OsRng).unwrap();

        let proof_bytes = bincode::serialize(&proof).unwrap();
        println!("Circuit RoK + size:: {}b", proof_bytes.len());

        let mut transcript_verifier = Transcript::new(b"circuit_rok test");
        let result = circuit_rok.reduce_statement(&mut transcript_verifier, &rs_verifier, &proof);
        assert!(result.is_ok(), "reduce failed: {:?}", result);
    }

    #[test]
    fn test_circuit_rok_with_opening() {
        let universal_params =
            CSchnorrCircuit::<16>::universal_parameters("test circuit rok with opening");
        let ck_ci = pedersen_key::<T256Affine>(3, "ck_ci");
        let rs_prover = sample_random_relation::<16>(&ck_ci);
        let rs_verifier = RelCSchnorr::<T256Affine, 16, 1>::new(
            rs_prover.params().clone(),
            rs_prover.statement().clone(),
            None,
        );

        let circuit_rok = CircuitRoK::<T256Affine, 16> {
            universal_params,
            ck_ci,
        };
        let pedersen_rok = PedersenRoK::<T256Affine> {
            ck: rs_verifier.params().ck.clone(),
        };
        let circuit_nizk = rok_compose!(
            PopError;
            ((pedersen_rok) o (circuit_rok))
        );

        let mut transcript_prover = Transcript::new(b"circuit_nizk test");
        let proof = circuit_nizk.prove(&mut transcript_prover, &rs_prover, &mut OsRng).unwrap();

        let proof_bytes = bincode::serialize(&proof).unwrap();
        println!("Circuit RoK + opening proof size:: {}b", proof_bytes.len());

        let mut transcript_verifier = Transcript::new(b"circuit_nizk test");
        let result = circuit_nizk.verify(&mut transcript_verifier, &rs_verifier, &proof);
        assert!(result.is_ok(), "nizk failed: {:?}", result);
    }
}
