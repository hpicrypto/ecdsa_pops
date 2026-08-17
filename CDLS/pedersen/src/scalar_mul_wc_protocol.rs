//! Without-c1-commitment-to-scalar variant of EC scalar multiplication proof.
//!
//! Uses the optimised point-addition proof [OptECPointAddProof] internally
//! (Optimisations 1, 2, 3 from Appendix G)

use ark_ec::{
    short_weierstrass::{self as sw},
    AffineRepr, CurveConfig, CurveGroup,
};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::UniformRand;
use ark_std::Zero;
use merlin::Transcript;
use rand::{CryptoRng, RngCore};

use crate::{
    ec_point_add_protocol_opt::OptECPointAddProof,
    pedersen_config::{PedersenComm, PedersenConfig},
    transcript::ECScalarMulTranscript,
};

#[derive(CanonicalSerialize, CanonicalDeserialize)]
pub struct ECScalarMulWCProof<P: PedersenConfig> {
    /// c1_x, c1_y: commitments to Z' = αK.
    pub c1_x: sw::Affine<P>,
    pub c1_y: sw::Affine<P>,
    /// c2_x, c2_y: commitments to Z'' = (α-ω)K.
    pub c2_x: sw::Affine<P>,
    pub c2_y: sw::Affine<P>,

    /// alpha: response. If b=0, α = α (the random prover scalar) so αK = Z'.
    /// If b=1, α = α-ω so αK = Z''.
    pub alpha: <<P as PedersenConfig>::OCurve as CurveConfig>::ScalarField,
    pub tau_x: <P as CurveConfig>::ScalarField,
    pub tau_y: <P as CurveConfig>::ScalarField,

    /// Inner optimised point-addition proof: Z + Z'' = Z'.
    pub eap: OptECPointAddProof<P>,
}

pub struct ECScalarMulWCProofIntermediate<P: PedersenConfig> {
    _marker: core::marker::PhantomData<P>,
}

impl<P: PedersenConfig> ECScalarMulWCProof<P> {
    pub fn make_transcript(
        transcript: &mut Transcript,
        k: &sw::Affine<<P as PedersenConfig>::OCurve>,
        c_zx: &sw::Affine<P>,
        c_zy: &sw::Affine<P>,
        c1_x: &sw::Affine<P>,
        c1_y: &sw::Affine<P>,
        c2_x: &sw::Affine<P>,
        c2_y: &sw::Affine<P>,
    ) {
        ECScalarMulTranscript::domain_sep(transcript);

        let mut buf = Vec::new();
        k.serialize_compressed(&mut buf).unwrap();
        ECScalarMulTranscript::append_point(transcript, b"K", &buf[..]);
        buf.clear();

        for (label, pt) in [
            (b"C_Zx" as &[u8], c_zx),
            (b"C_Zy", c_zy),
            (b"C1_x", c1_x),
            (b"C1_y", c1_y),
            (b"C2_x", c2_x),
            (b"C2_y", c2_y),
        ] {
            pt.serialize_compressed(&mut buf).unwrap();
            ECScalarMulTranscript::append_point(transcript, label, &buf[..]);
            buf.clear();
        }
    }

    pub fn create<T: RngCore + CryptoRng>(
        transcript: &mut Transcript,
        rng: &mut T,
        z_pt: &sw::Affine<<P as PedersenConfig>::OCurve>, // S = ω*K
        z_scalar: &<<P as PedersenConfig>::OCurve as CurveConfig>::ScalarField, // ω (witness)
        k: &sw::Affine<<P as PedersenConfig>::OCurve>,    // K (base)
        c_z: (&PedersenComm<P>, &PedersenComm<P>),        // commitments to S.x, S.y
    ) -> Self {
        type ScalarOC<P> = <<P as PedersenConfig>::OCurve as CurveConfig>::ScalarField;
        type AffOC<P> = sw::Affine<<P as PedersenConfig>::OCurve>;
        type ProjOC<P> = sw::Projective<<P as PedersenConfig>::OCurve>;

        // Sample α ∈ F_q \ {0, ω, 2ω}.
        let alpha: ScalarOC<P> = loop {
            let cand = ScalarOC::<P>::rand(rng);
            if !cand.is_zero() && cand != *z_scalar && cand != (*z_scalar + *z_scalar) {
                break cand;
            }
        };

        let alpha_minus_omega = alpha - *z_scalar;

        // Z' = α*K, Z'' = (α-ω)*K.
        let k_proj = k.into_group();
        let z_prime_p = k_proj * alpha;
        let z_double_prime_p = k_proj * alpha_minus_omega;
        let z_pts: Vec<AffOC<P>> = ProjOC::<P>::normalize_batch(&[z_prime_p, z_double_prime_p]);
        let z_prime = z_pts[0];
        let z_double_prime = z_pts[1];

        // Commit to Z', Z'' coordinate-wise in P (T-curve).
        let z_prime_x_sf = <P as PedersenConfig>::from_ob_to_sf(*z_prime.x().unwrap());
        let z_prime_y_sf = <P as PedersenConfig>::from_ob_to_sf(*z_prime.y().unwrap());
        let z_dp_x_sf = <P as PedersenConfig>::from_ob_to_sf(*z_double_prime.x().unwrap());
        let z_dp_y_sf = <P as PedersenConfig>::from_ob_to_sf(*z_double_prime.y().unwrap());

        let c1_x_comm = PedersenComm::new(z_prime_x_sf, rng);
        let c1_y_comm = PedersenComm::new(z_prime_y_sf, rng);
        let c2_x_comm = PedersenComm::new(z_dp_x_sf, rng);
        let c2_y_comm = PedersenComm::new(z_dp_y_sf, rng);

        // Inner optimised PA proof: S + Z'' = Z'.
        // A = S  (commitments c_z.0, c_z.1)
        // B = Z'' (commitments c2_x_comm, c2_y_comm)
        // T = Z' (commitments c1_x_comm, c1_y_comm)
        // Verifies that ω*K + (α-ω)*K = α*K
        let eap = OptECPointAddProof::<P>::create(
            transcript,
            rng,
            *z_pt,          // A
            z_double_prime, // B
            z_prime,        // T
            c_z.0,
            c_z.1, // c1, c2 -> A
            &c2_x_comm,
            &c2_y_comm, // c3, c4 -> B
            &c1_x_comm,
            &c1_y_comm, // c5, c6 -> T
        );

        Self::make_transcript(
            transcript,
            k,
            &c_z.0.comm,
            &c_z.1.comm,
            &c1_x_comm.comm,
            &c1_y_comm.comm,
            &c2_x_comm.comm,
            &c2_y_comm.comm,
        );

        // Derive challenge bit b ∈ {0, 1}.
        let mut chal_buf = [0u8; 1];
        transcript.challenge_bytes(b"WC_SM_b", &mut chal_buf);
        let b = chal_buf[0] & 1 == 1;

        let (response_alpha, tau_x, tau_y) = if b {
            (alpha_minus_omega, c2_x_comm.r, c2_y_comm.r)
        } else {
            (alpha, c1_x_comm.r, c1_y_comm.r)
        };

        Self {
            c1_x: c1_x_comm.comm,
            c1_y: c1_y_comm.comm,
            c2_x: c2_x_comm.comm,
            c2_y: c2_y_comm.comm,
            alpha: response_alpha,
            tau_x,
            tau_y,
            eap,
        }
    }

    pub fn verify(
        &self,
        transcript: &mut Transcript,
        k: &sw::Affine<<P as PedersenConfig>::OCurve>,
        c_zx: &sw::Affine<P>,
        c_zy: &sw::Affine<P>,
    ) -> bool {
        let pa_ok = self.eap.verify(
            transcript, c_zx, c_zy, // c1, c2 -> A = S
            &self.c2_x, &self.c2_y, // c3, c4 -> B = Z''
            &self.c1_x, &self.c1_y, // c5, c6 -> T = Z'
        );
        if !pa_ok {
            return false;
        }

        Self::make_transcript(
            transcript, k, c_zx, c_zy, &self.c1_x, &self.c1_y, &self.c2_x, &self.c2_y,
        );

        let mut chal_buf = [0u8; 1];
        transcript.challenge_bytes(b"WC_SM_b", &mut chal_buf);
        let b = chal_buf[0] & 1 == 1;

        // αK = Z' (b=0) or Z'' (b=1). Verifier reconstructs from α and public K.
        let alpha_k = (k.into_group() * self.alpha).into_affine();
        let alpha_k_x_sf = <P as PedersenConfig>::from_ob_to_sf(*alpha_k.x().unwrap());
        let alpha_k_y_sf = <P as PedersenConfig>::from_ob_to_sf(*alpha_k.y().unwrap());

        let expected_x_p = P::msm_generators(&alpha_k_x_sf, &self.tau_x);
        let expected_y_p = P::msm_generators(&alpha_k_y_sf, &self.tau_y);
        let expected = sw::Projective::<P>::normalize_batch(&[expected_x_p, expected_y_p]);

        if b {
            expected[0] == self.c2_x && expected[1] == self.c2_y
        } else {
            expected[0] == self.c1_x && expected[1] == self.c1_y
        }
    }
}
