//! Implements the standalone optimised point-addition Σ-protocol Π_PA
//!
//! Realises Optimisations 1 and 2 from Appendix G of the CDLS paper:
//!   * Opt 1: Π_Sq for the squaring relation (saves 1 point + 2 scalars).
//!   * Opt 2: shared mask for C_τ across coordinate proofs (saves 2 points + 4 scalars).
//!
//! Unlike [OptECPointAddProof] (which drops the C_2 opening sub-proof — Opt 3),
//! this version retains the opening proof and is therefore safe to use as a
//! standalone proof, not just inside Π_SM.
//!
//! Compared to the unoptimised [ECPointAddProof], saves:
//!   * Opt 1: 1 point + 2 scalars.
//!   * Opt 2: 2 points + 4 scalars.

use ark_ec::{
    short_weierstrass::{self as sw},
    AffineRepr, CurveConfig, CurveGroup, VariableBaseMSM,
};
use ark_ff::{fields::Field, Zero};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::UniformRand;
use merlin::Transcript;
use rand::{CryptoRng, RngCore};

use crate::{
    pedersen_config::{PedersenComm, PedersenConfig},
    transcript::SqECPointAdditionTranscript,
};

/// SqECPointAddProof. Standalone optimised point-addition proof Π_PA with the
/// C_2 opening sub-proof retained.
///
/// Statement: commitments (C_1, ..., C_6) to (a_x, a_y, b_x, b_y, t_x, t_y).
/// Witness: the six coordinate scalars and their commitment blindings.
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct SqECPointAddProof<P: PedersenConfig> {
    /// C_τ = τ·G + r_τ·H, commitment to the slope τ.
    pub c_tau: sw::Affine<P>,

    /// First-round commitments T_1..T_7 (T_7 is the C_2 opening commitment).
    pub t1: sw::Affine<P>,
    pub t2: sw::Affine<P>,
    pub t3: sw::Affine<P>,
    pub t4: sw::Affine<P>,
    pub t5: sw::Affine<P>,
    pub t6: sw::Affine<P>,
    pub t7: sw::Affine<P>,

    /// Non-zero subproof commitments.
    pub u1: sw::Affine<P>,
    pub u2: sw::Affine<P>,
    pub u3: sw::Affine<P>,

    /// Responses (z_2, z_r2 included for the C_2 opening).
    pub z_tau: <P as CurveConfig>::ScalarField,
    pub z_rtau: <P as CurveConfig>::ScalarField,
    pub z_f1: <P as CurveConfig>::ScalarField,
    pub z_rf1: <P as CurveConfig>::ScalarField,
    pub z_e1: <P as CurveConfig>::ScalarField,
    pub z_e2: <P as CurveConfig>::ScalarField,
    pub z_f3: <P as CurveConfig>::ScalarField,
    pub z_rf3: <P as CurveConfig>::ScalarField,
    pub z_e3: <P as CurveConfig>::ScalarField,
    pub z_2: <P as CurveConfig>::ScalarField,
    pub z_r2: <P as CurveConfig>::ScalarField,
    pub v1: <P as CurveConfig>::ScalarField,
    pub v2: <P as CurveConfig>::ScalarField,
    pub v3: <P as CurveConfig>::ScalarField,
}

/// SqECPointAddIntermediate. Prover state between message and response.
pub struct SqECPointAddIntermediate<P: PedersenConfig> {
    pub c_tau_comm: PedersenComm<P>,

    pub a_tau: <P as CurveConfig>::ScalarField,
    pub a_rtau: <P as CurveConfig>::ScalarField,
    pub a_f1: <P as CurveConfig>::ScalarField,
    pub a_rf1: <P as CurveConfig>::ScalarField,
    pub a_e1: <P as CurveConfig>::ScalarField,
    pub a_e2: <P as CurveConfig>::ScalarField,
    pub a_f3: <P as CurveConfig>::ScalarField,
    pub a_rf3: <P as CurveConfig>::ScalarField,
    pub a_e3: <P as CurveConfig>::ScalarField,
    pub a_2: <P as CurveConfig>::ScalarField,
    pub a_r2: <P as CurveConfig>::ScalarField,
    pub beta_1: <P as CurveConfig>::ScalarField,
    pub beta_2: <P as CurveConfig>::ScalarField,
    pub beta_3: <P as CurveConfig>::ScalarField,
    pub beta_4: <P as CurveConfig>::ScalarField,

    pub t1: sw::Affine<P>,
    pub t2: sw::Affine<P>,
    pub t3: sw::Affine<P>,
    pub t4: sw::Affine<P>,
    pub t5: sw::Affine<P>,
    pub t6: sw::Affine<P>,
    pub t7: sw::Affine<P>,
    pub u1: sw::Affine<P>,
    pub u2: sw::Affine<P>,
    pub u3: sw::Affine<P>,
}

impl<P: PedersenConfig> SqECPointAddProof<P> {
    /// Build the transcript: append C_1..C_6 (statement), C_τ, T_1..T_7, U_1..U_3.
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
        t7: &sw::Affine<P>,
        u1: &sw::Affine<P>,
        u2: &sw::Affine<P>,
        u3: &sw::Affine<P>,
    ) {
        SqECPointAdditionTranscript::domain_sep(transcript);

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
            (b"T7", t7),
            (b"U1", u1),
            (b"U2", u2),
            (b"U3", u3),
        ] {
            p.serialize_compressed(&mut buf).unwrap();
            SqECPointAdditionTranscript::append_point(transcript, label, &buf[..]);
            buf.clear();
        }
    }

    /// Sample masks, build the prover's first message.
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
    ) -> SqECPointAddIntermediate<P> {
        assert!(a != b); // No point-doubling.

        // τ = (b_y - a_y)/(b_x - a_x).
        let tau = (b.y - a.y) * ((b.x - a.x).inverse().unwrap());
        let taua = <P as PedersenConfig>::from_ob_to_sf(tau);
        let c_tau_comm = PedersenComm::new(taua, rng);

        // Derived commitment C_f1 (verifier recomputes).
        let c_f1 = c3.comm.into_group() - c1.comm;
        let c_f1_aff = c_f1.into_affine();

        // Sample masks.
        let a_tau = <P as CurveConfig>::ScalarField::rand(rng);
        let a_rtau = <P as CurveConfig>::ScalarField::rand(rng);
        let a_f1 = <P as CurveConfig>::ScalarField::rand(rng);
        let a_rf1 = <P as CurveConfig>::ScalarField::rand(rng);
        let a_e1 = <P as CurveConfig>::ScalarField::rand(rng);
        let a_e2 = <P as CurveConfig>::ScalarField::rand(rng);
        let a_f3 = <P as CurveConfig>::ScalarField::rand(rng);
        let a_rf3 = <P as CurveConfig>::ScalarField::rand(rng);
        let a_e3 = <P as CurveConfig>::ScalarField::rand(rng);
        // Masks for the C_2 opening proof (added back for standalone use).
        let a_2 = <P as CurveConfig>::ScalarField::rand(rng);
        let a_r2 = <P as CurveConfig>::ScalarField::rand(rng);

        // β_1 ∈ F*, β_2, β_3, β_4 ∈ F.
        let beta_1 = loop {
            let cand = <P as CurveConfig>::ScalarField::rand(rng);
            if !cand.is_zero() {
                break cand;
            }
        };
        let beta_2 = <P as CurveConfig>::ScalarField::rand(rng);
        let beta_3 = <P as CurveConfig>::ScalarField::rand(rng);
        let beta_4 = <P as CurveConfig>::ScalarField::rand(rng);

        // T_1..T_6 as in the optimised version.
        let t1_p = P::msm_generators(&a_tau, &a_rtau);
        let t2_p = P::msm_generators(&a_f1, &a_rf1);
        let t3_p = {
            let bases = [c_f1_aff, P::GENERATOR2];
            let scalars = [a_tau, a_e1];
            <sw::Projective<P> as VariableBaseMSM>::msm(&bases, &scalars).unwrap()
        };
        let t4_p = {
            let bases = [c_tau_comm.comm, P::GENERATOR2];
            let scalars = [a_tau, a_e2];
            <sw::Projective<P> as VariableBaseMSM>::msm(&bases, &scalars).unwrap()
        };
        let t5_p = P::msm_generators(&a_f3, &a_rf3);
        let t6_p = {
            let bases = [c_tau_comm.comm, P::GENERATOR2];
            let scalars = [a_f3, a_e3];
            <sw::Projective<P> as VariableBaseMSM>::msm(&bases, &scalars).unwrap()
        };
        // T_7 = a_2·G + a_r2·H — the C_2 opening commitment.
        let t7_p = P::msm_generators(&a_2, &a_r2);

        // Non-zero subproof commitments.
        let bx_minus_ax_sf = <P as PedersenConfig>::from_ob_to_sf(b.x - a.x);
        let u1_p = P::GENERATOR.into_group() * (beta_1 * bx_minus_ax_sf);
        let u2_p = {
            let bases = [c_f1_aff, P::GENERATOR2];
            let scalars = [beta_2, beta_3];
            <sw::Projective<P> as VariableBaseMSM>::msm(&bases, &scalars).unwrap()
        };
        let u3_p = P::GENERATOR.into_group() * beta_4;

        let pts = sw::Projective::<P>::normalize_batch(&[
            t1_p, t2_p, t3_p, t4_p, t5_p, t6_p, t7_p, u1_p, u2_p, u3_p,
        ]);
        let (t1, t2, t3, t4, t5, t6, t7, u1, u2, u3) = (
            pts[0], pts[1], pts[2], pts[3], pts[4], pts[5], pts[6], pts[7], pts[8], pts[9],
        );

        Self::make_transcript(
            transcript,
            &c1.comm,
            &c2.comm,
            &c3.comm,
            &c4.comm,
            &c5.comm,
            &c6.comm,
            &c_tau_comm.comm,
            &t1,
            &t2,
            &t3,
            &t4,
            &t5,
            &t6,
            &t7,
            &u1,
            &u2,
            &u3,
        );

        SqECPointAddIntermediate {
            c_tau_comm,
            a_tau,
            a_rtau,
            a_f1,
            a_rf1,
            a_e1,
            a_e2,
            a_f3,
            a_rf3,
            a_e3,
            a_2,
            a_r2,
            beta_1,
            beta_2,
            beta_3,
            beta_4,
            t1,
            t2,
            t3,
            t4,
            t5,
            t6,
            t7,
            u1,
            u2,
            u3,
        }
    }

    /// Build the full proof from intermediates and the challenge.
    #[allow(clippy::too_many_arguments)]
    pub fn create_proof_with_challenge(
        a: sw::Affine<<P as PedersenConfig>::OCurve>,
        b: sw::Affine<<P as PedersenConfig>::OCurve>,
        t: sw::Affine<<P as PedersenConfig>::OCurve>,
        inter: &SqECPointAddIntermediate<P>,
        c1: &PedersenComm<P>,
        c2: &PedersenComm<P>,
        c3: &PedersenComm<P>,
        c4: &PedersenComm<P>,
        c5: &PedersenComm<P>,
        c6: &PedersenComm<P>,
        chal: &<P as CurveConfig>::ScalarField,
    ) -> Self {
        let tau_oc = (b.y - a.y) * ((b.x - a.x).inverse().unwrap());
        let tau = <P as PedersenConfig>::from_ob_to_sf(tau_oc);
        let bx_minus_ax = <P as PedersenConfig>::from_ob_to_sf(b.x - a.x);
        let ax_minus_tx = <P as PedersenConfig>::from_ob_to_sf(a.x - t.x);
        let a_y_sf = <P as PedersenConfig>::from_ob_to_sf(a.y);

        let r_tau = inter.c_tau_comm.r;
        let c = *chal;

        // Coordinate-relation responses.
        let z_tau = inter.a_tau + c * tau;
        let z_rtau = inter.a_rtau + c * r_tau;
        let z_f1 = inter.a_f1 + c * bx_minus_ax;
        let z_rf1 = inter.a_rf1 + c * (c3.r - c1.r);
        let z_e1 = inter.a_e1 + c * ((c4.r - c2.r) - (c3.r - c1.r) * tau);
        let z_e2 = inter.a_e2 + c * ((c1.r + c3.r + c5.r) - r_tau * tau);
        let z_f3 = inter.a_f3 + c * ax_minus_tx;
        let z_rf3 = inter.a_rf3 + c * (c1.r - c5.r);
        let z_e3 = inter.a_e3 + c * ((c2.r + c6.r) - r_tau * ax_minus_tx);
        // C_2 opening responses: z_2 = a_2 + c·a_y, z_r2 = a_r2 + c·r_2.
        let z_2 = inter.a_2 + c * a_y_sf;
        let z_r2 = inter.a_r2 + c * c2.r;

        // Non-zero responses.
        let v1 = inter.beta_2 + c * inter.beta_1;
        let v2 = inter.beta_3 - c * inter.beta_1 * (c3.r - c1.r);
        let v3 = inter.beta_4 + c * inter.beta_1 * bx_minus_ax;

        Self {
            c_tau: inter.c_tau_comm.comm,
            t1: inter.t1,
            t2: inter.t2,
            t3: inter.t3,
            t4: inter.t4,
            t5: inter.t5,
            t6: inter.t6,
            t7: inter.t7,
            u1: inter.u1,
            u2: inter.u2,
            u3: inter.u3,
            z_tau,
            z_rtau,
            z_f1,
            z_rf1,
            z_e1,
            z_e2,
            z_f3,
            z_rf3,
            z_e3,
            z_2,
            z_r2,
            v1,
            v2,
            v3,
        }
    }

    /// Convenience: full create (derives challenge internally).
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
        let inter = Self::create_intermediates(transcript, rng, a, b, c1, c2, c3, c4, c5, c6);
        let chal_buf = SqECPointAdditionTranscript::challenge_scalar(transcript, b"c");
        let chal = <P as PedersenConfig>::make_challenge_from_buffer(&chal_buf);
        Self::create_proof_with_challenge(a, b, t, &inter, c1, c2, c3, c4, c5, c6, &chal)
    }

    /// Verify with externally-supplied challenge. Checks all 10 equations (1..7, 8, 9, 10).
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
        let u1_p = self.u1.into_group();

        let c_f1_p = c3p - c1p;
        let c_f1 = c_f1_p.into_affine();
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

        // Eq (2): z_f1·G + z_rf1·H ?= T_2 + c·C_f1
        let lhs2 = P::msm_generators(&self.z_f1, &self.z_rf1);
        let rhs2 = self.t2.into_group() + c_f1_p * c;
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
        if lhs6 != rhs6 {
            return false;
        }

        // Eq (7): z_2·G + z_r2·H ?= T_7 + c·C_2 (C_2 opening proof).
        let lhs7 = P::msm_generators(&self.z_2, &self.z_r2);
        let rhs7 = self.t7.into_group() + c2p * c;
        if lhs7 != rhs7 {
            return false;
        }

        // Eq (8): U_1 ?≠ O
        if u1_p.is_zero() {
            return false;
        }

        // Eqs (9) and (10) share c·U_1.
        let u1_c = u1_p * c;

        // Eq (9): c·U_1 + U_3 ?= v_3·G
        let lhs9 = u1_c + self.u3.into_group();
        let rhs9 = P::GENERATOR.into_group() * self.v3;
        if lhs9 != rhs9 {
            return false;
        }

        // Eq (10): c·U_1 + U_2 ?= v_1·C_f1 + v_2·H
        let lhs10 = u1_c + self.u2.into_group();
        let rhs10 = {
            let bases = [c_f1, P::GENERATOR2];
            let scalars = [self.v1, self.v2];
            <sw::Projective<P> as VariableBaseMSM>::msm(&bases, &scalars).unwrap()
        };
        lhs10 == rhs10
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
            &self.t7,
            &self.u1,
            &self.u2,
            &self.u3,
        );
        let chal_buf = SqECPointAdditionTranscript::challenge_scalar(transcript, b"c");
        let chal = <P as PedersenConfig>::make_challenge_from_buffer(&chal_buf);
        self.verify_with_challenge(c1, c2, c3, c4, c5, c6, &chal)
    }

    /// serialized_size. Bytes needed once serialised.
    pub fn serialized_size(&self) -> usize {
        <Self as CanonicalSerialize>::serialized_size(self, ark_serialize::Compress::Yes)
    }
}
