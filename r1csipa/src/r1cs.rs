use std::iter::once;

use halo2curves::{
    ff::{Field, PrimeField},
    group::Curve,
    serde::{endian::EndianRepr, SerdeObject},
    CurveAffine,
};
use merlin::Transcript;
use rand_core::OsRng;
use serde::{Deserialize, Serialize};

use crate::{
    bellpepper::{r1cs::R1CSShape, solver::SatisfyingAssignment},
    errors::ProofError,
    ipa::{IPAParams, InnerProductArgZK},
    msm_function,
    transcript::TranscriptProtocol,
    utils::{inner_product, *},
};

// This file implements the R1CS to IPA transform given in ePrint 2025/327
// "Bulletproofs for R1CS: Bridging the Completeness-Soundness Gap and a ZK
// Extension" by Gil Segev with the optional values (x', y', z') all equal to
// zero.
//
// The IPA it compiles down to supports ZK as described by ePrint 2020/735:
// "Bulletproofs+: Shorter Proofs for Privacy-Enhanced Distributed Ledger"
//  Heewon Chung, Kyoohyung Han, Chanyang Ju, Myungsun Kim, and Jae Hong Seo

#[allow(type_alias_bounds)]
pub type R1CSMatrix<F: PrimeField> = Vec<(usize, usize, F)>;

#[allow(type_alias_bounds)]
pub type R1CSProofParams<C: CurveAffine> = IPAParams<C>;

#[derive(Serialize, Clone)]
/// A r1cs instance that allows for part of the public input to be committed.
/// By convention the public input is always of the form 1 || public_values ||
/// committed_values
pub struct R1CSInstance<F: PrimeField> {
    pub rows: usize, // rows in A, B, C, number of constraints
    pub cols: usize, /* cols in A, B, C, length of z = [witness, 1, inputs], 1 must be
                      * included in inputs */
    pub inputs_len: usize, // number of inputs, implies |witness| = cols - inputs_len
    pub com_inputs_len: usize, /* number of committed_inputs, implies |pub_inputs| = inputs_len -
                            * com_inputs_len */
    pub A: R1CSMatrix<F>,
    pub B: R1CSMatrix<F>,
    pub C: R1CSMatrix<F>,
    pub inputs: Vec<F>,
}
impl<F: PrimeField> R1CSInstance<F> {
    pub fn new_from_shape_with_witness(
        cs: &SatisfyingAssignment<F>,
        shape: &R1CSShape<F>,
        com_inputs_len: usize,
    ) -> (Self, Vec<F>, Vec<F>) {
        let (witness_F, inputs_F) = cs.r1cs_witness_and_inputs(shape);

        #[cfg(debug_assertions)]
        {
            // z is organized as [witness,1,public inputs, committed inputs]  The one is
            // already prepended to inputs
            let mut z = witness_F.clone();
            z.extend(inputs_F.clone());
            assert_eq!(z.len(), shape.num_vars + shape.num_io + 1);
            assert!(com_inputs_len <= shape.num_io);
            assert!(check_r1cs_instance(
                shape.num_cons,
                z.len(),
                &shape.A,
                &shape.B,
                &shape.C,
                &z
            ));
        }

        let r = Self::new_from_shape(shape, &inputs_F, com_inputs_len);

        let inputs_len = r.inputs_len;

        // get committed_inputs
        let committed_inputs = r.inputs[inputs_len - com_inputs_len..].to_vec();

        (r, witness_F, committed_inputs)
    }

    /// Function to replace committed inputs with zeros.
    pub fn remove_committed_inputs(&self) -> Self {
        let mut public_inputs = self.inputs[0..(self.inputs_len - self.com_inputs_len)].to_vec();
        public_inputs.extend(vec![F::ZERO; self.com_inputs_len]);

        let mut r1cs = self.clone();
        r1cs.inputs = public_inputs;
        r1cs
    }

    /// Used by the verifier
    pub fn new_from_shape(shape: &R1CSShape<F>, inputs: &[F], com_inputs_len: usize) -> Self {
        // We need to pad rows so that rows + cols is a power of two.  Since the
        // matrices are in sparse form, the extra rows are defined to be zero, as
        // required Padding is nicely explained here (page 8): https://eprint.iacr.org/2025/327
        let rows = shape.num_cons;
        let cols = shape.num_vars + shape.num_io + 1;

        #[cfg(feature = "print-trace")]
        {
            println!("Before padding:");
            println!("constraints: {}", shape.num_cons);
            println!("aux vars: {}", shape.num_vars);
            println!("num IO: {}", shape.num_io);
        }

        let rows = rows + (rows + cols).next_power_of_two() - (rows + cols);
        assert!((rows + cols).is_power_of_two());

        #[cfg(feature = "print-trace")]
        {
            println!("After padding:");
            println!("constraints: {}", rows);
            println!("rows + cols: {}", rows + cols);
        }

        R1CSInstance {
            rows,
            cols,
            inputs_len: inputs.len(),
            com_inputs_len,
            A: shape.A.clone(),
            B: shape.B.clone(),
            C: shape.C.clone(),
            inputs: inputs.to_owned(),
        }
    }

    /// Modify parameters to use an external pedersen key for committed inputs
    pub fn set_committed_inputs_ck<C: CurveAffine>(
        &self,
        params: &mut R1CSProofParams<C>,
        ck_ci: &[C],
    ) {
        // last com_inputs_len elements of z are the committed public inputs
        assert_eq!(ck_ci.len(), self.com_inputs_len);
        let lower = self.cols - self.com_inputs_len;
        ck_ci.iter().enumerate().for_each(|(i, G)| {
            params.basesG[lower + i] = *G;
        });
    }

    /// Given parameters, returns the commitment key corresponding to the
    /// committed inputs.
    pub fn commitment_key<C: CurveAffine>(&self, params: &R1CSProofParams<C>) -> Vec<C> {
        // compute I = <0||0||committed_inputs||0, G> + <0, H>
        let n = self.cols;

        // last com_inputs_len elements of z are the committed public inputs
        let lower = n - self.com_inputs_len;
        let upper = lower + self.com_inputs_len;
        params.basesG[lower..upper].to_owned()
    }

    pub fn witness_len(&self) -> usize {
        self.cols - self.inputs_len
    }

    pub fn check(&self, witness: &[F]) -> bool {
        let mut z = witness.to_owned();
        z.extend(self.inputs.clone());
        let a = multiply_vec(self.rows, self.cols, &self.A, &z);
        let b = multiply_vec(self.rows, self.cols, &self.B, &z);
        let c = multiply_vec(self.rows, self.cols, &self.C, &z);
        let ab = component_wise_mul(&a, &b);
        vec_compare(ab, c)
    }
}

// Internal helper struct to store values known only to the prover
struct ProverState<'a, C: CurveAffine> {
    witness: &'a Vec<C::Scalar>,
    Az: &'a Vec<C::Scalar>,
    Bz: &'a Vec<C::Scalar>,
    r: &'a C::Scalar,
    eta: &'a C::Scalar,
}

#[derive(Serialize, Deserialize)]
pub struct R1CSProof<C: CurveAffine + SerdeObject>
where
    <C as CurveAffine>::ScalarExt: Serialize + for<'a> Deserialize<'a> + EndianRepr,
{
    T: C,
    S0: C,
    ipa_proof: InnerProductArgZK<C>,
}

impl<C: CurveAffine + SerdeObject> R1CSProof<C>
where
    <C as CurveAffine>::ScalarExt: Serialize + for<'b> Deserialize<'b> + EndianRepr,
{
    fn commit_to_witness(
        params: &R1CSProofParams<C>,
        witness: &[C::Scalar],
    ) -> (C::Curve, C::Scalar) {
        // Commit to the witness as
        //      T = <witness||0, G> + <0, H> + eta S
        let eta = C::Scalar::random(OsRng);
        let n_plus_m = params.basesG.len();
        assert!(witness.len() <= n_plus_m);
        let mut w = witness.to_owned();
        w.extend(vec![C::Scalar::ZERO; n_plus_m - witness.len()]);
        w.extend_from_slice(&[eta]);

        let mut bases = params.basesG.clone();
        bases.extend_from_slice(&[params.V]);

        (msm_function(&w, &bases), eta)
    }

    /// creates the committement to the committed public inputs
    pub fn commit_to_committed_public_inputs(
        r1cs: &R1CSInstance<C::Scalar>,
        committed_inputs: &[C::Scalar],
        params: &R1CSProofParams<C>,
    ) -> C::Curve {
        let bases = r1cs.commitment_key(params);
        msm_function(committed_inputs, bases.as_slice())
    }

    /// Commits to public inputs and allows part of the commitment to come from
    /// the prover in the form of a commitment.
    ///
    /// By convention, this corresponds to the last inputs.
    ///
    /// The consistency of the commitment *must be checked outside the snark*,
    /// specifically:
    ///  - the commitment must only use the first com_input_len generators
    ///    corresponding to public inputs.
    ///  - An extra generator must also be manually used if this must be a
    ///    hiding commitment.
    fn commit_to_inputs(
        r1cs: &R1CSInstance<C::Scalar>,
        params: &R1CSProofParams<C>,
        committed_inputs: &C::Curve,
    ) -> C::Curve {
        let lower = r1cs.cols - r1cs.inputs_len;
        let upper = r1cs.cols - r1cs.com_inputs_len;
        let bases = &params.basesG[lower..upper];
        let scalars = &r1cs.inputs[..r1cs.inputs_len - r1cs.com_inputs_len];

        msm_function(scalars, bases) + committed_inputs
    }

    #[allow(clippy::type_complexity)]
    fn compute_S0(
        r1cs: &R1CSInstance<C::Scalar>,
        params: &R1CSProofParams<C>,
        witness: &[C::Scalar],
    ) -> (Vec<C::Scalar>, Vec<C::Scalar>, C::Curve, C::Scalar) {
        // Compute
        //      S0 = <0||Az, G> + <0||Bz, H> + r S
        // then the inputs commitment is computed separately by prover and verifier I =
        // <0||y, G> + <0, H> The value S = S0 + I is as in 2025/327, but we
        // separate I to allow inputs to be public.

        let _m = r1cs.rows;
        let n = r1cs.cols;

        let mut z = witness.to_owned();
        z.extend(r1cs.inputs.clone());
        let Az = multiply_vec(r1cs.rows, r1cs.cols, &r1cs.A, &z);
        let Bz = multiply_vec(r1cs.rows, r1cs.cols, &r1cs.B, &z);

        let mut g_scalars = vec![C::Scalar::ZERO; n];
        g_scalars.extend(Az.clone());

        let mut h_scalars = vec![C::Scalar::ZERO; n];
        h_scalars.extend(Bz.clone());

        let bases = params
            .basesG
            .clone()
            .into_iter()
            .chain(params.basesH.clone())
            .chain(once(params.V))
            .collect::<Vec<_>>();
        g_scalars.extend(h_scalars);

        let r = C::Scalar::random(OsRng);
        g_scalars.extend(once(r));

        (Az, Bz, msm_function(&g_scalars, &bases), r)
    }

    #[allow(clippy::type_complexity)]
    fn r1cs2ipa(
        r1cs: &R1CSInstance<C::Scalar>,
        params: &R1CSProofParams<C>,
        transcript: &mut Transcript,
        committed_input: &C,
        T: &C,
        S: &C,
        prover_state: Option<ProverState<C>>,
    ) -> (
        C::Curve,
        Vec<C::Scalar>,
        Option<Vec<C::Scalar>>,
        Option<Vec<C::Scalar>>,
        Option<C::Scalar>,
    )
    where
        <C as CurveAffine>::ScalarExt: Serialize + EndianRepr,
    {
        // 1. Hash instance (without committed inputs)
        transcript.append_message(
            b"r1cs_instance_digest",
            &bincode::serialize(&r1cs.remove_committed_inputs()).unwrap(),
        ); // TODO: (perf) maybe precompute an instance digest
           // Hash committed input length and committment
        transcript.append_message(
            b"committed input len",
            &bincode::serialize(&r1cs.com_inputs_len).unwrap(),
        );
        transcript.append_point(b"committed_inputs", committed_input);
        // 2. Hash T and S and derive challenges
        transcript.append_point(b"T", T);
        transcript.append_point(b"S'", S);
        let alpha: C::Scalar = transcript.challenge_scalar(b"alpha");
        let beta: C::Scalar = transcript.challenge_scalar(b"beta");
        let gamma: C::Scalar = transcript.challenge_scalar(b"gamma");
        let delta: C::Scalar = transcript.challenge_scalar(b"delta");

        // 3. Create IPA instance (u, v, w = <u, v>)  w will be public, based on the
        //    challenges

        let m = r1cs.rows;
        let n = r1cs.cols;
        let r_len = n - r1cs.inputs.len(); // Length of witness component x of z = [x,y] \in F^n

        let mu = alpha * gamma;
        let delta_vec_n = vec![delta; r_len]
            .into_iter()
            .chain(vec![C::Scalar::ONE; n - r_len])
            .collect::<Vec<_>>();
        let delta_inv = delta.invert().unwrap();

        let gamma_inv = gamma.invert().unwrap();
        let Gprime_factors: Vec<C::Scalar> = std::iter::repeat_n(C::Scalar::ONE, n)
            .chain(exp_iter(gamma_inv).take(m))
            .collect();

        let alpha_powers_n = exp_iter(alpha).take(n).collect::<Vec<C::Scalar>>();
        let beta_powers_m = exp_iter(beta).take(m).collect::<Vec<C::Scalar>>();
        let alpha_powers_m = exp_iter(alpha).take(m).collect::<Vec<C::Scalar>>(); // TOOD: perf; computing both alpha^n and alpha^m overlaps
        let mu_powers_m = exp_iter(mu).take(m).collect::<Vec<C::Scalar>>();
        let gamma_powers_m = exp_iter(gamma).take(m).collect::<Vec<C::Scalar>>();

        let mu_A = vec_multiply_mat(m, n, &r1cs.A, &mu_powers_m); // in F^n
        let beta_B = vec_multiply_mat(m, n, &r1cs.B, &beta_powers_m);
        let gamma_C = vec_multiply_mat(m, n, &r1cs.C, &gamma_powers_m);

        let c = sub_vec(&add_vec(&mu_A, &beta_B), &gamma_C); // c in F^n

        // w = <alpha^m, beta^m> + delta^2 cdot <alpha^n, c cdot delta_vec>
        let delta_sq = delta * delta;
        let w = inner_product(&alpha_powers_m, &beta_powers_m)
            + delta_sq * inner_product(&alpha_powers_n, &component_wise_mul(&c, &delta_vec_n));

        // Compute P as required by the IPA verifier.  Not explicitly required by the
        // prover      P = delta_inv*(T) + S + <(delta_sq *
        // alpha_powers||-beta_powers), Gprime> + <(c cdot detla_vec ||- alpha_powers),
        // H> (this is equal to  P = <u,G'> + <v,H> + <u,v> U + (randomness)*V)
        let P = if prover_state.is_none() {
            let mut g_scalars = vector_scalar_mul(&alpha_powers_n, &delta_sq);
            g_scalars.extend(vector_scalar_mul(&beta_powers_m, &(-C::Scalar::ONE)));
            for i in 0..g_scalars.len() {
                g_scalars[i] *= Gprime_factors[i];
            }

            let mut h_scalars = component_wise_mul(&c, &delta_vec_n);
            h_scalars.extend(vector_scalar_mul(&alpha_powers_m, &(-C::Scalar::ONE)));

            let mut bases = params.basesG.clone();
            bases.extend(params.basesH.clone());
            g_scalars.extend(h_scalars);

            bases.extend([*T]);
            g_scalars.extend([delta_inv]);

            *S + msm_function(&g_scalars, &bases).to_affine() + params.U * w
        } else {
            C::identity().into()
        };

        let (u, v, eta_prime) = if let Some(ps) = prover_state {
            // Prover additionally computes vectors (u, v) and eta_prime
            // u[1..n] : (0|y) + delta_inv_vec * (x|0) + delta_sq * alpha^n

            let mut pad_inputs = vec![C::Scalar::ZERO; ps.witness.len()];
            pad_inputs.extend(r1cs.inputs.clone());
            let mut pad_witness = ps.witness.clone();
            pad_witness.extend(vec![C::Scalar::ZERO; r1cs.inputs.len()]);
            let mut u = add_vec(
                &add_vec(&pad_inputs, &vector_scalar_mul(&pad_witness, &delta_inv)),
                &vector_scalar_mul(&alpha_powers_n, &delta_sq),
            );
            // u[n+1..n+m] : Az cdot gamma^m - beta^m
            u.extend(add_vec(
                &component_wise_mul(ps.Az, &gamma_powers_m),
                &vector_scalar_mul(&beta_powers_m, &(-C::Scalar::ONE)),
            ));

            // v[1..n] : c cdot delta_vec
            let mut v = component_wise_mul(&c, &delta_vec_n);
            // v[n+1..n+m]: Bz - alpha^m
            v.extend(add_vec(
                ps.Bz,
                &vector_scalar_mul(&alpha_powers_m, &(-C::Scalar::ONE)),
            ));

            debug_assert_eq!(
                w,
                inner_product(&u, &v),
                "Prover's self-check of <u,v>=w failed"
            );

            let eta_prime = *ps.r + delta_inv * ps.eta;

            (Some(u), Some(v), Some(eta_prime))
        } else {
            (None, None, None)
        };

        (P, Gprime_factors, u, v, eta_prime)
    }

    pub fn create(
        r1cs: &R1CSInstance<C::Scalar>,
        witness: &Vec<C::Scalar>,
        committed_inputs_opening: &[C::Scalar],
        params: &R1CSProofParams<C>,
        transcript: &mut Transcript,
    ) -> Self
    where
        <C as CurveAffine>::ScalarExt: Serialize + EndianRepr,
    {
        // Sanity check: committed_inputs must be less than public inputs
        debug_assert!(committed_inputs_opening.len() < r1cs.inputs_len);

        // Commit to instance
        let (T, eta) = Self::commit_to_witness(params, witness);
        // Commit to committed public inputs
        let committed_inputs =
            Self::commit_to_committed_public_inputs(r1cs, committed_inputs_opening, params);
        // commit to public inputs (without committed)
        let I = Self::commit_to_inputs(r1cs, params, &committed_inputs);

        // 1. Compute S = S0 + I
        let (Az, Bz, S0, r) = Self::compute_S0(r1cs, params, witness);
        let S = S0 + I;

        let (_P, Gprime_factors, u, v, eta_prime) = Self::r1cs2ipa(
            r1cs,
            params,
            transcript,
            &committed_inputs.into(),
            &T.into(),
            &S.into(),
            Some(ProverState {
                witness,
                Az: &Az,
                Bz: &Bz,
                r: &r,
                eta: &eta,
            }),
        );

        // Call IPA prover
        let H_factors: Vec<C::Scalar> =
            std::iter::repeat_n(C::Scalar::ONE, params.basesH.len()).collect();
        let proof = InnerProductArgZK::create(
            transcript,
            &params.U,
            &params.V,
            &Gprime_factors,
            &H_factors,
            params.basesG.clone(),
            params.basesH.clone(),
            u.unwrap(),
            v.unwrap(),
            eta_prime.unwrap(),
        );

        R1CSProof {
            T: T.into(),
            S0: S0.into(),
            ipa_proof: proof,
        }
    }

    pub fn verify(
        r1cs: &R1CSInstance<C::Scalar>,
        params: &R1CSProofParams<C>,
        transcript: &mut Transcript,
        committed_inputs: &C,
        proof: &R1CSProof<C>,
    ) -> Result<(), ProofError>
    where
        <C as CurveAffine>::ScalarExt: Serialize + EndianRepr,
    {
        // 1. Recompute S from prover value S0 and inputs
        let I = Self::commit_to_inputs(r1cs, params, &committed_inputs.to_curve());
        let S = proof.S0 + I.into();

        let (P, Gprime_factors, _, _, _) = Self::r1cs2ipa(
            r1cs,
            params,
            transcript,
            committed_inputs,
            &proof.T,
            &S.into(),
            None,
        );

        let H_factors: Vec<C::Scalar> =
            std::iter::repeat_n(C::Scalar::ONE, params.basesH.len()).collect();
        proof.ipa_proof.verify(
            transcript,
            Gprime_factors,
            &H_factors,
            &P.to_affine(),
            &params.U,
            &params.V,
            &params.basesG,
            &params.basesH,
        )
    }
}

#[cfg(test)]
mod tests {
    use bellpepper_core::{
        boolean::AllocatedBit, num::AllocatedNum, ConstraintSystem, LinearCombination,
        SynthesisError,
    };
    use halo2curves::{
        ff::{PrimeField, PrimeFieldBits},
        t256::{Fq as F, T256Affine as C},
    };
    use rand::random;

    use super::*;
    use crate::{
        bellpepper::{shape_cs::ShapeCS, solver::SatisfyingAssignment},
        utils::tests::test_helper_r1cs_proof,
    };

    // A sample gadget for testing
    /// Gets as input the little endian representation of a number and spits out
    /// the number
    fn le_bits_to_num<F, CS>(
        mut cs: CS,
        bits: &[AllocatedBit],
    ) -> Result<AllocatedNum<F>, SynthesisError>
    where
        F: PrimeField + PrimeFieldBits,
        CS: ConstraintSystem<F>,
    {
        // We loop over the input bits and construct the constraint
        // and the field element that corresponds to the result
        let mut lc = LinearCombination::zero();
        let mut coeff = F::ONE;
        let mut fe = Some(F::ZERO);
        for bit in bits.iter() {
            lc = lc + (coeff, bit.get_variable());
            fe = bit.get_value().map(|val| {
                if val {
                    fe.unwrap() + coeff
                } else {
                    fe.unwrap()
                }
            });
            coeff = coeff.double();
        }
        let num = AllocatedNum::alloc(cs.namespace(|| "Field element"), || {
            fe.ok_or(SynthesisError::AssignmentMissing)
        })?;
        lc = lc - num.get_variable();
        cs.enforce(|| "compute number from bits", |lc| lc, |lc| lc, |_| lc);
        Ok(num)
    }

    fn synthesize_bits_to_num<F: PrimeField + PrimeFieldBits, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        bits_le: &[bool],
    ) -> Result<Option<F>, SynthesisError> {
        let mut alloc_bits: Vec<AllocatedBit> = vec![];
        for (i, b) in bits_le.iter().enumerate() {
            alloc_bits.push(AllocatedBit::alloc(
                &mut cs.namespace(|| format!("alloc x[{}] = {}", i, b)),
                Some(*b),
            )?);
        }
        let alloc_num = le_bits_to_num(&mut cs.namespace(|| "let_bits_to_num(x)"), &alloc_bits)?;

        Ok(alloc_num.get_value())
    }

    #[test]
    fn test_r1cs_bits_to_num() {
        let x = random::<u64>();
        let x_bits_le: Vec<bool> = (0..64).map(|i| ((x >> i) & 1) != 0).collect();

        // First create the R1CS matrices
        let mut cs = ShapeCS::<F>::new();
        let _ = synthesize_bits_to_num(&mut cs, &x_bits_le);
        let shape = cs.r1cs_shape_unpadded();

        // Now compute the witness
        let mut cs: SatisfyingAssignment<F> = SatisfyingAssignment::new();
        let num = synthesize_bits_to_num(&mut cs, &x_bits_le);
        assert_eq!(num.unwrap().unwrap(), F::from(x));

        let (r, witness, committed) = R1CSInstance::new_from_shape_with_witness(&cs, &shape, 0);
        test_helper_r1cs_proof::<C>(&r, &witness, &committed);
    }

    fn synthesize_alloc_bits<F: PrimeField + PrimeFieldBits, CS: ConstraintSystem<F>>(
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        // get two bits as input and check that they are indeed bits
        let a = AllocatedNum::alloc(cs.namespace(|| "a"), || Ok(F::ONE))?;
        let _ = a.inputize(cs.namespace(|| "a is input"));
        cs.enforce(
            || "check a is 0 or 1",
            |lc| lc + CS::one() - a.get_variable(),
            |lc| lc + a.get_variable(),
            |lc| lc,
        );
        let b = AllocatedNum::alloc(cs.namespace(|| "b"), || Ok(F::ONE))?;
        let _ = b.inputize(cs.namespace(|| "b is input"));
        cs.enforce(
            || "check b is 0 or 1",
            |lc| lc + CS::one() - b.get_variable(),
            |lc| lc + b.get_variable(),
            |lc| lc,
        );
        // allocate 42 values to be committed public input
        (0..42).try_for_each(|i| {
            let forty_two =
                AllocatedNum::alloc(cs.namespace(|| format!("{}-th 42", i)), || Ok(F::from(42)))?;
            forty_two.inputize(cs.namespace(|| format!("inputize {}-th committed input", i)))
        })?;
        let c = a.mul(cs.namespace(|| "a*b"), &b)?;
        cs.enforce(
            || "check c is 0 or 1",
            |lc| lc + CS::one() - c.get_variable(),
            |lc| lc + c.get_variable(),
            |lc| lc,
        );

        Ok(())
    }

    #[test]
    fn test_r1cs_alloc_bit() {
        // First create the R1CS matrices
        let mut cs = ShapeCS::<F>::new();
        let _ = synthesize_alloc_bits(&mut cs);
        let shape = cs.r1cs_shape_unpadded();

        println!("Shape unpadded? constraints: {}", shape.num_cons);

        // Now compute the witness
        let mut cs: SatisfyingAssignment<F> = SatisfyingAssignment::new();
        let _ = synthesize_alloc_bits(&mut cs);
        // the two values are committed
        let (r, witness, committed) = R1CSInstance::new_from_shape_with_witness(&cs, &shape, 42);

        test_helper_r1cs_proof::<C>(&r, &witness, &committed);
    }
}
