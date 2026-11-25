//! Implements the optimised EC point-addition protocol Π'_PA .
//! It has: Optimisations 1 (Π_Sq for the squaring relation), 2 (sharing the
//! mask of C_τ across coordinate proofs), and 3 (dropping Π_PD(C_2) opening
//! proof, only valid when composed inside Π_SM).
//!
//! It also follows draft-cllz-cfrg-ecdsa-pop: the opening of C_f1 = C_3 - C_1
//! and the non-zero proof for it are merged into the single linear equation:
//!
//! ```text
//!   G = inv_f1 * C_f1 + aux_f1 * H
//! ```
//!
//! with witness inv_f1 = 1/(b_x - a_x), aux_f1 = -(r_3 - r_1)/(b_x - a_x).
//! A witness with inv_f1 = 0 would give G = aux_f1 * H, i.e. dlog_H(G); so
//! inv_f1 != 0 and C_f1 opens to f1 = 1/inv_f1 != 0. This replaces the CDLS
//! non-zero gadget (U_1, U_2, U_3, v_1, v_2, v_3) and the C_f1 opening
//! (z_f1, z_rf1), saving 3 points and 3 scalars per proof.
//!
//! The protocol implemented here is inlined.
//! DANGER: only use this inside the mul proof.

use ark_ec::{
    short_weierstrass::{self as sw},
    AffineRepr, CurveConfig, CurveGroup, VariableBaseMSM,
};
use ark_ff::fields::Field;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::UniformRand;
use merlin::Transcript;
use rand::{CryptoRng, RngCore};

use crate::{
    pedersen_config::{PedersenComm, PedersenConfig},
    transcript::OptECPointAdditionTranscript,
};

/// OptECPointAddProof. Optimised point-addition proof Π'_PA without the
/// C_2 opening sub-proof.
///
/// Statement: commitments (C_1, ..., C_6) to (a_x, a_y, b_x, b_y, t_x, t_y).
/// Witness: the six coordinate scalars and their commitment blindings.
#[derive(CanonicalSerialize, CanonicalDeserialize, Clone)]
pub struct OptECPointAddProof<P: PedersenConfig> {
    /// C_τ = τ*G + r_τ*H, commitment to the slope τ = (b_y - a_y)/(b_x - a_x).
    pub c_tau: sw::Affine<P>,

    /// First-round commitments T_1..T_6 (T_7 is dropped).
    pub t1: sw::Affine<P>,
    pub t2: sw::Affine<P>,
    pub t3: sw::Affine<P>,
    pub t4: sw::Affine<P>,
    pub t5: sw::Affine<P>,
    pub t6: sw::Affine<P>,

    /// Responses (z_2, z_r2 dropped).
    pub z_tau: <P as CurveConfig>::ScalarField,
    pub z_rtau: <P as CurveConfig>::ScalarField,
    pub z_inv_f1: <P as CurveConfig>::ScalarField,
    pub z_aux_f1: <P as CurveConfig>::ScalarField,
    pub z_e1: <P as CurveConfig>::ScalarField,
    pub z_e2: <P as CurveConfig>::ScalarField,
    pub z_f3: <P as CurveConfig>::ScalarField,
    pub z_rf3: <P as CurveConfig>::ScalarField,
    pub z_e3: <P as CurveConfig>::ScalarField,
}

/// OptECPointAddIntermediate. Prover state between message and response.
pub struct OptECPointAddIntermediate<P: PedersenConfig> {
    pub c_tau_comm: PedersenComm<P>,

    // Random scalars (a_2, a_r2 dropped).
    pub a_tau: <P as CurveConfig>::ScalarField,
    pub a_rtau: <P as CurveConfig>::ScalarField,
    pub a_inv_f1: <P as CurveConfig>::ScalarField,
    pub a_aux_f1: <P as CurveConfig>::ScalarField,
    pub a_e1: <P as CurveConfig>::ScalarField,
    pub a_e2: <P as CurveConfig>::ScalarField,
    pub a_f3: <P as CurveConfig>::ScalarField,
    pub a_rf3: <P as CurveConfig>::ScalarField,
    pub a_e3: <P as CurveConfig>::ScalarField,

    pub t1: sw::Affine<P>,
    pub t2: sw::Affine<P>,
    pub t3: sw::Affine<P>,
    pub t4: sw::Affine<P>,
    pub t5: sw::Affine<P>,
    pub t6: sw::Affine<P>,
}

impl<P: PedersenConfig> OptECPointAddProof<P> {
    /// Build the transcript: append C_1..C_6 (statement), C_τ, all T_i.
    #[allow(clippy::too_many_arguments)]
    pub fn make_transcript(
        transcript: &mut Transcript,
        c1: &sw::Affine<P>,
        c2: &sw::Affine<P>,
        c3: &sw::Affine<P>,
        c4: &sw::Affine<P>,
        c5: &sw::Affine<P>,
        c6: &sw::Affine<P>,
        c_tau: &sw::Affine<P>,
        t1: &sw::Affine<P>,
        t2: &sw::Affine<P>,
        t3: &sw::Affine<P>,
        t4: &sw::Affine<P>,
        t5: &sw::Affine<P>,
        t6: &sw::Affine<P>,
    ) {
        OptECPointAdditionTranscript::domain_sep(transcript);

        let mut buf = Vec::new();
        for (label, p) in [
            (&b"C1"[..], c1),
            (b"C2", c2),
            (b"C3", c3),
            (b"C4", c4),
            (b"C5", c5),
            (b"C6", c6),
            (b"Ct", c_tau),
            (b"T1", t1),
            (b"T2", t2),
            (b"T3", t3),
            (b"T4", t4),
            (b"T5", t5),
            (b"T6", t6),
        ] {
            p.serialize_compressed(&mut buf).unwrap();
            OptECPointAdditionTranscript::append_point(transcript, label, &buf[..]);
            buf.clear();
        }
    }

    /// Prover step 1: sample masks and build the first message.
    /// No transcript access, so many instances can run in parallel.
    #[allow(clippy::too_many_arguments)]
    pub fn first_message<T: RngCore + CryptoRng>(
        rng: &mut T,
        a: sw::Affine<<P as PedersenConfig>::OCurve>,
        b: sw::Affine<<P as PedersenConfig>::OCurve>,
        c1: &PedersenComm<P>,
        _c2: &PedersenComm<P>,
        c3: &PedersenComm<P>,
        _c4: &PedersenComm<P>,
        _c5: &PedersenComm<P>,
        _c6: &PedersenComm<P>,
    ) -> OptECPointAddIntermediate<P> {
        assert!(a.x != b.x); // P_1 != ±P_2 (no doubling, no inverse pair).

        // τ = (b_y - a_y)/(b_x - a_x), then C_τ.
        let tau = (b.y - a.y) * ((b.x - a.x).inverse().unwrap());
        let taua = <P as PedersenConfig>::from_ob_to_sf(tau);
        let c_tau_comm = PedersenComm::new(taua, rng);

        // Derived commitment C_f1 = C_3 - C_1 (verifier recomputes it).
        let c_f1_aff = (c3.comm.into_group() - c1.comm).into_affine();

        // Sample masks.
        let a_tau = <P as CurveConfig>::ScalarField::rand(rng);
        let a_rtau = <P as CurveConfig>::ScalarField::rand(rng);
        let a_inv_f1 = <P as CurveConfig>::ScalarField::rand(rng);
        let a_aux_f1 = <P as CurveConfig>::ScalarField::rand(rng);
        let a_e1 = <P as CurveConfig>::ScalarField::rand(rng);
        let a_e2 = <P as CurveConfig>::ScalarField::rand(rng);
        let a_f3 = <P as CurveConfig>::ScalarField::rand(rng);
        let a_rf3 = <P as CurveConfig>::ScalarField::rand(rng);
        let a_e3 = <P as CurveConfig>::ScalarField::rand(rng);

        // T_1 = a_τ*G + a_rτ*H
        let t1_p = P::msm_generators(&a_tau, &a_rtau);
        // T_2 = a_inv*C_f1 + a_aux*H   (for G = inv_f1*C_f1 + aux_f1*H)
        let t2_p = {
            let bases = [c_f1_aff, P::GENERATOR2];
            let scalars = [a_inv_f1, a_aux_f1];
            <sw::Projective<P> as VariableBaseMSM>::msm(&bases, &scalars).unwrap()
        };
        // T_3 = a_τ*C_f1 + a_e1*H
        let t3_p = {
            let bases = [c_f1_aff, P::GENERATOR2];
            let scalars = [a_tau, a_e1];
            <sw::Projective<P> as VariableBaseMSM>::msm(&bases, &scalars).unwrap()
        };
        // T_4 = a_τ*C_τ + a_e2*H
        let t4_p = {
            let bases = [c_tau_comm.comm, P::GENERATOR2];
            let scalars = [a_tau, a_e2];
            <sw::Projective<P> as VariableBaseMSM>::msm(&bases, &scalars).unwrap()
        };
        // T_5 = a_f3*G + a_rf3*H
        let t5_p = P::msm_generators(&a_f3, &a_rf3);
        // T_6 = a_f3*C_τ + a_e3*H
        let t6_p = {
            let bases = [c_tau_comm.comm, P::GENERATOR2];
            let scalars = [a_f3, a_e3];
            <sw::Projective<P> as VariableBaseMSM>::msm(&bases, &scalars).unwrap()
        };

        let pts = sw::Projective::<P>::normalize_batch(&[t1_p, t2_p, t3_p, t4_p, t5_p, t6_p]);
        let (t1, t2, t3, t4, t5, t6) = (pts[0], pts[1], pts[2], pts[3], pts[4], pts[5]);

        OptECPointAddIntermediate {
            c_tau_comm,
            a_tau,
            a_rtau,
            a_inv_f1,
            a_aux_f1,
            a_e1,
            a_e2,
            a_f3,
            a_rf3,
            a_e3,
            t1,
            t2,
            t3,
            t4,
            t5,
            t6,
        }
    }

    /// Append the statement and first message to the transcript.
    #[allow(clippy::too_many_arguments)]
    pub fn append_first_message(
        transcript: &mut Transcript,
        c1: &PedersenComm<P>,
        c2: &PedersenComm<P>,
        c3: &PedersenComm<P>,
        c4: &PedersenComm<P>,
        c5: &PedersenComm<P>,
        c6: &PedersenComm<P>,
        inter: &OptECPointAddIntermediate<P>,
    ) {
        Self::make_transcript(
            transcript,
            &c1.comm,
            &c2.comm,
            &c3.comm,
            &c4.comm,
            &c5.comm,
            &c6.comm,
            &inter.c_tau_comm.comm,
            &inter.t1,
            &inter.t2,
            &inter.t3,
            &inter.t4,
            &inter.t5,
            &inter.t6,
        );
    }

    /// Squeeze the challenge scalar.
    fn challenge(transcript: &mut Transcript) -> <P as CurveConfig>::ScalarField {
        let chal_buf = OptECPointAdditionTranscript::challenge_scalar(transcript, b"c");
        <P as PedersenConfig>::make_challenge_from_buffer(&chal_buf)
    }

    /// Prover step 2: absorb statement and first message, squeeze the challenge.
    #[allow(clippy::too_many_arguments)]
    pub fn append_and_challenge(
        transcript: &mut Transcript,
        c1: &PedersenComm<P>,
        c2: &PedersenComm<P>,
        c3: &PedersenComm<P>,
        c4: &PedersenComm<P>,
        c5: &PedersenComm<P>,
        c6: &PedersenComm<P>,
        inter: &OptECPointAddIntermediate<P>,
    ) -> <P as CurveConfig>::ScalarField {
        Self::append_first_message(transcript, c1, c2, c3, c4, c5, c6, inter);
        Self::challenge(transcript)
    }

    /// Sample masks, build the prover's first message, append it to the
    /// transcript.
    #[allow(clippy::too_many_arguments)]
    pub fn create_intermediates<T: RngCore + CryptoRng>(
        transcript: &mut Transcript,
        rng: &mut T,
        a: sw::Affine<<P as PedersenConfig>::OCurve>,
        b: sw::Affine<<P as PedersenConfig>::OCurve>,
        c1: &PedersenComm<P>,
        c2: &PedersenComm<P>,
        c3: &PedersenComm<P>,
        c4: &PedersenComm<P>,
        c5: &PedersenComm<P>,
        c6: &PedersenComm<P>,
    ) -> OptECPointAddIntermediate<P> {
        let inter = Self::first_message(rng, a, b, c1, c2, c3, c4, c5, c6);
        Self::append_first_message(transcript, c1, c2, c3, c4, c5, c6, &inter);
        inter
    }

    /// Prover step 3: build the full proof from intermediates and the challenge.
    #[allow(clippy::too_many_arguments)]
    pub fn create_proof_with_challenge(
        a: sw::Affine<<P as PedersenConfig>::OCurve>,
        b: sw::Affine<<P as PedersenConfig>::OCurve>,
        t: sw::Affine<<P as PedersenConfig>::OCurve>,
        inter: &OptECPointAddIntermediate<P>,
        c1: &PedersenComm<P>,
        c2: &PedersenComm<P>,
        c3: &PedersenComm<P>,
        c4: &PedersenComm<P>,
        c5: &PedersenComm<P>,
        c6: &PedersenComm<P>,
        chal: &<P as CurveConfig>::ScalarField,
    ) -> Self {
        // Recompute witness-side scalars.
        let tau_oc = (b.y - a.y) * ((b.x - a.x).inverse().unwrap());
        let tau = <P as PedersenConfig>::from_ob_to_sf(tau_oc);
        let bx_minus_ax = <P as PedersenConfig>::from_ob_to_sf(b.x - a.x);
        let ax_minus_tx = <P as PedersenConfig>::from_ob_to_sf(a.x - t.x);

        // inv_f1 = 1/(b_x - a_x) ; aux_f1 = -(r_3 - r_1)/(b_x - a_x)
        let inv_f1 = bx_minus_ax.inverse().unwrap();
        let aux_f1 = -(c3.r - c1.r) * inv_f1;

        let r_tau = inter.c_tau_comm.r;
        let c = *chal;

        // z_τ = a_τ + c*τ ; z_rτ = a_rτ + c*r_τ
        let z_tau = inter.a_tau + c * tau;
        let z_rtau = inter.a_rtau + c * r_tau;
        // z_inv = a_inv + c*inv_f1 ; z_aux = a_aux + c*aux_f1
        let z_inv_f1 = inter.a_inv_f1 + c * inv_f1;
        let z_aux_f1 = inter.a_aux_f1 + c * aux_f1;
        // z_e1 = a_e1 + c*((r_4 - r_2) - (r_3 - r_1)*τ)
        let z_e1 = inter.a_e1 + c * ((c4.r - c2.r) - (c3.r - c1.r) * tau);
        // z_e2 = a_e2 + c*((r_1 + r_3 + r_5) - r_τ*τ)
        let z_e2 = inter.a_e2 + c * ((c1.r + c3.r + c5.r) - r_tau * tau);
        // z_f3 = a_f3 + c*(a_x - t_x) ; z_rf3 = a_rf3 + c*(r_1 - r_5)
        let z_f3 = inter.a_f3 + c * ax_minus_tx;
        let z_rf3 = inter.a_rf3 + c * (c1.r - c5.r);
        // z_e3 = a_e3 + c*((r_2 + r_6) - r_τ*(a_x - t_x))
        let z_e3 = inter.a_e3 + c * ((c2.r + c6.r) - r_tau * ax_minus_tx);

        Self {
            c_tau: inter.c_tau_comm.comm,
            t1: inter.t1,
            t2: inter.t2,
            t3: inter.t3,
            t4: inter.t4,
            t5: inter.t5,
            t6: inter.t6,
            z_tau,
            z_rtau,
            z_inv_f1,
            z_aux_f1,
            z_e1,
            z_e2,
            z_f3,
            z_rf3,
            z_e3,
        }
    }

    /// Create.
    #[allow(clippy::too_many_arguments)]
    pub fn create<T: RngCore + CryptoRng>(
        transcript: &mut Transcript,
        rng: &mut T,
        a: sw::Affine<<P as PedersenConfig>::OCurve>,
        b: sw::Affine<<P as PedersenConfig>::OCurve>,
        t: sw::Affine<<P as PedersenConfig>::OCurve>,
        c1: &PedersenComm<P>,
        c2: &PedersenComm<P>,
        c3: &PedersenComm<P>,
        c4: &PedersenComm<P>,
        c5: &PedersenComm<P>,
        c6: &PedersenComm<P>,
    ) -> Self {
        let inter = Self::first_message(rng, a, b, c1, c2, c3, c4, c5, c6);
        let chal = Self::append_and_challenge(transcript, c1, c2, c3, c4, c5, c6, &inter);
        Self::create_proof_with_challenge(a, b, t, &inter, c1, c2, c3, c4, c5, c6, &chal)
    }

    /// Verify with externally-supplied challenge. Checks 6 equations
    /// (1..6); eq 7 is dropped per Optimisation 3.
    #[allow(clippy::too_many_arguments)]
    pub fn verify_with_challenge(
        &self,
        c1: &sw::Affine<P>,
        c2: &sw::Affine<P>,
        c3: &sw::Affine<P>,
        c4: &sw::Affine<P>,
        c5: &sw::Affine<P>,
        c6: &sw::Affine<P>,
        chal: &<P as CurveConfig>::ScalarField,
    ) -> bool {
        let c1p = c1.into_group();
        let c2p = c2.into_group();
        let c3p = c3.into_group();
        let c4p = c4.into_group();
        let c5p = c5.into_group();
        let c6p = c6.into_group();
        let c_tau_p = self.c_tau.into_group();

        let c_f1 = (c3p - c1p).into_affine();
        let c_p1_p = c4p - c2p;
        let c_p2_p = c1p + c3p + c5p;
        let c_f3_p = c1p - c5p;
        let c_p3_p = c2p + c6p;

        let c = *chal;

        // Eq (1): z_τ·G + z_rτ·H ?= T_1 + c·C_τ
        let lhs1 = P::msm_generators(&self.z_tau, &self.z_rtau);
        let rhs1 = self.t1.into_group() + c_tau_p * c;
        if lhs1 != rhs1 {
            return false;
        }

        // Eq (2): z_inv·C_f1 + z_aux·H ?= T_2 + c·G
        // (C_f1 opens to a non-zero value; replaces opening + non-zero proof.)
        let lhs2 = {
            let bases = [c_f1, P::GENERATOR2];
            let scalars = [self.z_inv_f1, self.z_aux_f1];
            <sw::Projective<P> as VariableBaseMSM>::msm(&bases, &scalars).unwrap()
        };
        let rhs2 = self.t2.into_group() + P::GENERATOR * c;
        if lhs2 != rhs2 {
            return false;
        }

        // Eq (3): z_τ·C_f1 + z_e1·H ?= T_3 + c·C_p1
        let lhs3 = {
            let bases = [c_f1, P::GENERATOR2];
            let scalars = [self.z_tau, self.z_e1];
            <sw::Projective<P> as VariableBaseMSM>::msm(&bases, &scalars).unwrap()
        };
        let rhs3 = self.t3.into_group() + c_p1_p * c;
        if lhs3 != rhs3 {
            return false;
        }

        // Eq (4): z_τ·C_τ + z_e2·H ?= T_4 + c·C_p2 (squaring check, Opt 1).
        let lhs4 = {
            let bases = [self.c_tau, P::GENERATOR2];
            let scalars = [self.z_tau, self.z_e2];
            <sw::Projective<P> as VariableBaseMSM>::msm(&bases, &scalars).unwrap()
        };
        let rhs4 = self.t4.into_group() + c_p2_p * c;
        if lhs4 != rhs4 {
            return false;
        }

        // Eq (5): z_f3·G + z_rf3·H ?= T_5 + c·C_f3
        let lhs5 = P::msm_generators(&self.z_f3, &self.z_rf3);
        let rhs5 = self.t5.into_group() + c_f3_p * c;
        if lhs5 != rhs5 {
            return false;
        }

        // Eq (6): z_f3·C_τ + z_e3·H ?= T_6 + c·C_p3
        let lhs6 = {
            let bases = [self.c_tau, P::GENERATOR2];
            let scalars = [self.z_f3, self.z_e3];
            <sw::Projective<P> as VariableBaseMSM>::msm(&bases, &scalars).unwrap()
        };
        let rhs6 = self.t6.into_group() + c_p3_p * c;
        lhs6 == rhs6
        // Eq (7) is dropped (Opt 3).
    }

    /// Verifier step 1: absorb statement + proof's first message, squeeze the
    /// challenge. Transcript only.
    #[allow(clippy::too_many_arguments)]
    pub fn absorb(
        &self,
        transcript: &mut Transcript,
        c1: &sw::Affine<P>,
        c2: &sw::Affine<P>,
        c3: &sw::Affine<P>,
        c4: &sw::Affine<P>,
        c5: &sw::Affine<P>,
        c6: &sw::Affine<P>,
    ) -> <P as CurveConfig>::ScalarField {
        Self::make_transcript(
            transcript,
            c1,
            c2,
            c3,
            c4,
            c5,
            c6,
            &self.c_tau,
            &self.t1,
            &self.t2,
            &self.t3,
            &self.t4,
            &self.t5,
            &self.t6,
        );
        Self::challenge(transcript)
    }

    /// Verify: re-derive challenge from transcript, then check.
    #[allow(clippy::too_many_arguments)]
    pub fn verify(
        &self,
        transcript: &mut Transcript,
        c1: &sw::Affine<P>,
        c2: &sw::Affine<P>,
        c3: &sw::Affine<P>,
        c4: &sw::Affine<P>,
        c5: &sw::Affine<P>,
        c6: &sw::Affine<P>,
    ) -> bool {
        let chal = self.absorb(transcript, c1, c2, c3, c4, c5, c6);
        self.verify_with_challenge(c1, c2, c3, c4, c5, c6, &chal)
    }

    /// serialized_size. Bytes needed once serialised.
    pub fn serialized_size(&self) -> usize {
        <Self as CanonicalSerialize>::serialized_size(self, ark_serialize::Compress::Yes)
    }
}
