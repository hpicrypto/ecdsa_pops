//! A circuit to verify a curve equation of the form:
//! T = cR + Q where:
//!     - T (in T256), c (in scalar field of P256) are public
//!     - R, Q (in T256) are private values
//!     - Rx, Qx (in T256 Scalar) are committed public inputs using Pedersen over T256
//!     - rho, the randomness of the committments of Rx, Qx is private

#![allow(non_snake_case)]
use ark_std::{end_timer, start_timer};
use bellpepper_core::{num::AllocatedNum, Circuit, ConstraintSystem, SynthesisError};
use halo2curves::{secp256r1::Secp256r1Affine, t256::T256Affine};
use merlin::Transcript;
use r1csipa::{
    bellpepper::r1cs::R1CSShape,
    {R1CSInstance, R1CSProof, R1CSProofParams},
};

use crate::{
    circuit::ecc::AllocatedPoint,
    errors::PopError,
    utils::{fp_to_fr, fq_to_fr, Fq, Fr},
};

mod ecc;
pub(crate) mod utils;

#[derive(Clone, Debug)]
/// Private inputs of the CSchnorr circuit
pub struct CschnorrCircuitPrivateInputs {
    /// The first messge of a committed Schnorr execution
    R: Secp256r1Affine,
    /// The ECDSA public key
    Q: Secp256r1Affine,
    /// The commitment randomness
    rho: Fr,
}

impl CschnorrCircuitPrivateInputs {
    /// Create private inputs
    pub fn new(R: Secp256r1Affine, Q: Secp256r1Affine, rho: Fr) -> Self {
        CschnorrCircuitPrivateInputs { R, Q, rho }
    }
}

/// Public inputs of the CSchnorr circuit
#[derive(Clone, Debug)]
pub struct CschnorrCircuitPublicInputs<const SEC_PARAM_BYTES: usize> {
    /// The public element derived during the committed Schnorr execution
    pub(crate) T: Secp256r1Affine,
    /// The challenge of the committed Schnorr execution
    pub(crate) c: Fq,
}

impl<const SEC_PARAM_BYTES: usize> CschnorrCircuitPublicInputs<SEC_PARAM_BYTES> {
    /// Create public inputs
    pub fn new(T: Secp256r1Affine, c: Fq) -> Self {
        CschnorrCircuitPublicInputs { T, c }
    }
}

#[derive(Clone)]
/// The circuit that verifies the cschnorr equation equation
pub struct CSchnorrCircuit<const SEC_PARAM_BYTES: usize> {
    /// The private inputs
    pub private_inputs: Option<CschnorrCircuitPrivateInputs>,
    /// The public inputs
    pub public_inputs: CschnorrCircuitPublicInputs<SEC_PARAM_BYTES>,
}

impl<const SEC_PARAM_BYTES: usize> CSchnorrCircuit<SEC_PARAM_BYTES> {
    /// creates the R1CS circuit
    pub fn new(
        private_inputs: Option<CschnorrCircuitPrivateInputs>,
        public_inputs: CschnorrCircuitPublicInputs<SEC_PARAM_BYTES>,
    ) -> Self {
        Self {
            private_inputs,
            public_inputs: public_inputs.clone(),
        }
    }
}

impl<const SEC_PARAM_BYTES: usize> Circuit<Fr> for CSchnorrCircuit<SEC_PARAM_BYTES> {
    fn synthesize<CS: ConstraintSystem<Fr>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
        // allocate and inputize the public point of the equation
        let assignedT = AllocatedPoint::alloc(
            cs.namespace(|| "T"),
            Some((
                fp_to_fr(&self.public_inputs.T.x),
                fp_to_fr(&self.public_inputs.T.y),
                false,
            )),
        )?;
        assignedT.inputize(cs.namespace(|| "assign public input point T"))?;

        // allocate the private inputs
        let witness = if self.private_inputs.is_some() {
            let witness = self.private_inputs.clone().unwrap();
            (
                Some((fp_to_fr(&witness.R.x), fp_to_fr(&witness.R.y), false)),
                Some((fp_to_fr(&witness.Q.x), fp_to_fr(&witness.Q.y), false)),
                Some(witness.rho),
            )
        } else {
            (None, None, None)
        };

        // allocate the committed inputs
        let assignedR = AllocatedPoint::alloc(cs.namespace(|| "assign R"), witness.0)?;
        let assignedQ = AllocatedPoint::alloc(cs.namespace(|| "assign Q"), witness.1)?;

        let assigned_rho =
            AllocatedNum::alloc(cs.namespace(|| "committed input randomness"), || {
                Ok(witness.2.map_or(Fr::from(0), |rho| rho))
            })?;

        // inputize Rx, Qx, rho to use as committed input
        assignedR.x.inputize(cs.namespace(|| "inputize Rx"))?;
        assignedQ.x.inputize(cs.namespace(|| "inputize Qx"))?;
        assigned_rho.inputize(cs.namespace(|| "inputize rho"))?;

        // Enforce the points are on the curve.
        assignedQ.assert_on_curve(cs.namespace(|| "assert private input Q on curve"))?;
        assignedR.assert_on_curve(cs.namespace(|| "assert private input R on curve"))?;

        // compute c*R where c is public and part of the circuit description
        let scalar_mul_result = assignedR.scalar_mul_public_scalar(
            cs.namespace(|| "scalar_mul"),
            &fq_to_fr(&self.public_inputs.c),
        )?;

        // compute c*R + Q
        let rhs = scalar_mul_result.add(cs.namespace(|| "point addition"), &assignedQ)?;

        // assert it is equal to the lhs
        AllocatedPoint::enforce_equal(cs.namespace(|| "lhs = rhs"), &rhs, &assignedT)?;

        Ok(())
    }
}

impl<const SEC_PARAM_BYTES: usize> CSchnorrCircuit<SEC_PARAM_BYTES> {
    /// generate universal parameters for the circuit family
    pub fn universal_parameters(label: &str) -> R1CSProofParams<T256Affine> {
        let t = start_timer!(|| "Circuit: getting Universal Parameters");
        let label = [label, ": generate universal params"].concat();
        let params = R1CSProofParams::<T256Affine>::generate(&label, 1 << 12);
        end_timer!(t);
        params
    }

    /// Specialize parameters for the proven circuit. Uses an external pedersen key for committed input
    pub fn specialize_parameters(
        &self,
        universal: &R1CSProofParams<T256Affine>,
    ) -> (R1CSProofParams<T256Affine>, R1CSShape<Fr>) {
        let t = start_timer!(|| "Circuit: specialize parameters");

        let circuit_verifier = CSchnorrCircuit {
            public_inputs: self.public_inputs.clone(),
            private_inputs: None,
        };

        let mut cs = r1csipa::bellpepper::shape_cs::ShapeCS::<Fr>::new();
        let _ = circuit_verifier.clone().synthesize(&mut cs.namespace(|| "synthesize verifier"));
        let shape = cs.r1cs_shape_unpadded();
        let bound = 2 * cs.r1cs_shape().num_vars;
        // keep only the needed generators defined by the bound
        let basesG = universal.basesG[0..bound].to_vec();
        let basesH = universal.basesH[0..bound].to_vec();
        let r1cs_params = R1CSProofParams {
            basesG,
            basesH,
            U: universal.U,
            V: universal.V,
        };
        end_timer!(t);
        (r1cs_params, shape)
    }

    /// Create the snark proof
    pub fn cshnorr_circuit_prove(
        &self,
        r1cs_params: &mut R1CSProofParams<T256Affine>,
        r1cs_shape: &R1CSShape<Fr>,
        ck_ci: &[T256Affine],
        transcript: &mut Transcript,
    ) -> R1CSProof<T256Affine> {
        let t = start_timer!(|| "Circuit: prover");

        transcript.append_message(b"cschnorr circuit:", b"proof");

        // synthesize circuit
        let mut cs = r1csipa::bellpepper::solver::SatisfyingAssignment::<Fr>::new();
        let _ = self.clone().synthesize(&mut cs.namespace(|| "calculate witness"));

        // Create r1cs instance, witness and committed inputs for the circuit
        let (r, witness, committed_inputs) =
            R1CSInstance::new_from_shape_with_witness(&cs, r1cs_shape, 3);

        // Modify the parameters to use an externally chosen commitment key
        r.set_committed_inputs_ck(r1cs_params, ck_ci);

        // create the proof
        let proof = R1CSProof::create(&r, &witness, &committed_inputs[..], r1cs_params, transcript);
        end_timer!(t);

        #[cfg(feature = "print-trace")]
        {
            let bytes = bincode::serialize(&proof).unwrap();
            println!("R1CSIPA proof size: {} bytes", bytes.len());
        }

        proof
    }

    /// Verify the snark proof
    pub fn cshnorr_circuit_verify(
        &self,
        r1cs_params: &mut R1CSProofParams<T256Affine>,
        r1cs_shape: &R1CSShape<Fr>,
        ck_ci: &[T256Affine],
        committed_inputs: &T256Affine,
        proof: &R1CSProof<T256Affine>,
        transcript: &mut Transcript,
    ) -> Result<(), PopError> {
        let t = start_timer!(|| "R1CS verifier");

        let public_inputs = self.public_inputs.clone();

        transcript.append_message(b"cschnorr circuit:", b"proof");

        // Create R1CS instance for verification (without witness)
        let Tx = fp_to_fr(&public_inputs.T.x.clone());
        let Ty = fp_to_fr(&public_inputs.T.y.clone());
        // Tx, Ty, 0 is the point T, and the 3 last zeros correspond to the committed values
        let pi = vec![
            Fr::from(1),
            Tx,
            Ty,
            Fr::from(0),
            Fr::from(0),
            Fr::from(0),
            Fr::from(0),
        ];
        // create the r1cs instance
        let r1cs = R1CSInstance::new_from_shape(r1cs_shape, &pi, 3);

        // Modify the parameters to use an externally chosen commitment key
        r1cs.set_committed_inputs_ck(r1cs_params, ck_ci);

        R1CSProof::verify(&r1cs, r1cs_params, transcript, committed_inputs, proof)?;
        end_timer!(t);

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use bellpepper_core::{test_cs::TestConstraintSystem, Circuit};
    use ff::Field;
    use halo2curves::{group::Curve, secp256r1::Secp256r1Affine, t256::T256Affine};
    use merlin::Transcript;
    use num_bigint::BigUint;
    use r1csipa::{R1CSInstance, R1CSProof};
    use rand_core::{OsRng, RngCore};

    use crate::{
        circuit::{
            utils::biguint_to_scalar, CSchnorrCircuit, CschnorrCircuitPrivateInputs,
            CschnorrCircuitPublicInputs,
        },
        utils::{fp_to_fr, fq_to_fr, Fq, Fr},
    };

    // sample a field element from bytes
    fn c_from_bytes<const SEC_PARAM_BYTES: usize>(bytes: [u8; SEC_PARAM_BYTES]) -> Fq {
        let c_big = BigUint::from_bytes_be(&bytes);
        biguint_to_scalar::<Fq>(&c_big)
    }

    // create a circuit from artificial instance
    fn build_instance<const SEC_PARAM_BYTES: usize>(
        R: Secp256r1Affine,
        Q: Secp256r1Affine,
        rho: Fq,
        c: Fq,
    ) -> CSchnorrCircuit<SEC_PARAM_BYTES> {
        // choose the T that makes the equation verify
        let T = ((R * c) + Q).to_affine();

        let rho = fq_to_fr(&rho);
        CSchnorrCircuit {
            private_inputs: Some(CschnorrCircuitPrivateInputs { R, Q, rho }),
            public_inputs: CschnorrCircuitPublicInputs { T, c },
        }
    }

    // sample a random instance
    fn sample_random_instance<const SEC_PARAM_BYTES: usize>() -> CSchnorrCircuit<SEC_PARAM_BYTES> {
        // sample a random challenge of SEC_PARAM_BYTES  bytes
        let mut bytes = [0u8; SEC_PARAM_BYTES];
        OsRng.fill_bytes(&mut bytes);
        let c = c_from_bytes::<SEC_PARAM_BYTES>(bytes);
        let rho = <Fq as Field>::random(OsRng);

        // sample random group elements R, Q
        let R = Secp256r1Affine::random(OsRng);
        let Q = Secp256r1Affine::random(OsRng);

        build_instance::<SEC_PARAM_BYTES>(R, Q, rho, c)
    }

    // assert the constraint system is satisfied
    fn assert_cschnorr_cs_satisfied<const SEC_PARAM_BYTES: usize>(
        label: String,
        circuit: &CSchnorrCircuit<SEC_PARAM_BYTES>,
    ) {
        let mut cs = TestConstraintSystem::<Fr>::new();
        circuit.clone().synthesize(&mut cs).unwrap();

        println!("{label}: {} constraints", cs.num_constraints());

        assert!(
            cs.is_satisfied(),
            "unsatisfied: {:?}",
            cs.which_is_unsatisfied()
        );
    }

    // test helper for the three cases
    fn cschnorr_cs_helper<const SEC_PARAM_BYTES: usize>() {
        let circuit_random = sample_random_instance::<SEC_PARAM_BYTES>();

        assert_cschnorr_cs_satisfied(
            format!("cschnorr-random with {} bits seciruty", SEC_PARAM_BYTES),
            &circuit_random,
        );
    }

    // test helper for the snark in the three cases
    fn assert_cschnorr_snark_verifies<const SEC_PARAM_BYTES: usize>(
        label: String,
        circuit_prover: &CSchnorrCircuit<SEC_PARAM_BYTES>,
    ) {
        // sample commitment key for committed inputs
        let ck_ci = (0..3).map(|_| T256Affine::random(OsRng)).collect::<Vec<_>>();

        let circuit_prover = CSchnorrCircuit::<SEC_PARAM_BYTES> {
            private_inputs: circuit_prover.private_inputs.clone(),
            public_inputs: circuit_prover.public_inputs.clone(),
        };

        // verifier knows no private inputs
        let circuit_verifier = CSchnorrCircuit::<SEC_PARAM_BYTES> {
            private_inputs: None,
            public_inputs: circuit_prover.public_inputs.clone(),
        };

        let mut transcript = Transcript::new(b"test cschnorr circuit");

        // create universal parameters and specialize
        let universal_params =
            CSchnorrCircuit::<SEC_PARAM_BYTES>::universal_parameters("test cschnorr circuit");
        let (mut params, shape) =
            CSchnorrCircuit::specialize_parameters(&circuit_verifier, &universal_params);

        // create the proof from prover circuit
        let proof =
            circuit_prover.cshnorr_circuit_prove(&mut params, &shape, &ck_ci, &mut transcript);

        let r1cs = R1CSInstance::new_from_shape(&shape, &[Fr::from(0); 7], 3);

        // create committed_inputs
        let ci = [
            fp_to_fr(&circuit_prover.private_inputs.clone().unwrap().R.x),
            fp_to_fr(&circuit_prover.private_inputs.clone().unwrap().Q.x),
            circuit_prover.private_inputs.unwrap().rho,
        ];

        let committed_input =
            R1CSProof::commit_to_committed_public_inputs(&r1cs, &ci, &params).into();

        let mut transcript = Transcript::new(b"test cschnorr circuit");

        // verify the proof from verifier circuit
        let result = circuit_verifier.cshnorr_circuit_verify(
            &mut params,
            &shape,
            &ck_ci,
            &committed_input,
            &proof,
            &mut transcript,
        );

        assert!(result.is_ok(), "{label}: proof did not verify");
    }

    fn cschnorr_snark_helper<const SEC_PARAM_BYTES: usize>() {
        let circuit_random = sample_random_instance::<SEC_PARAM_BYTES>();

        // SNARK proof checks
        assert_cschnorr_snark_verifies(
            format!("cschnorr-random with {} bits seciruty", SEC_PARAM_BYTES),
            &circuit_random,
        );
    }

    #[test]
    fn test_cschnorr_snark_proof_16() {
        cschnorr_snark_helper::<16>();
    }

    #[test]
    fn test_cschnorr_snark_proof_32() {
        cschnorr_snark_helper::<32>();
    }

    #[test]
    fn test_cschnorr_cs_32() {
        cschnorr_cs_helper::<32>();
    }

    #[test]
    fn test_cschnorr_cs_16() {
        cschnorr_cs_helper::<16>();
    }
}
