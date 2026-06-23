//! FS-wrapped WC variant of EC scalar multiplication proof.
//! Repeats the single-round WC protocol SECPARAM times for binary-challenge soundness.

use ark_ec::{
    short_weierstrass::{self as sw},
    CurveConfig,
};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use merlin::Transcript;
use rand::{CryptoRng, RngCore};

use crate::{
    pedersen_config::{PedersenComm, PedersenConfig},
    scalar_mul_wc_protocol::ECScalarMulWCProof,
    transcript::ECScalarMulTranscript,
};

#[derive(CanonicalSerialize, CanonicalDeserialize)]
pub struct FSECScalarMulWCProof<P: PedersenConfig> {
    proofs: Vec<ECScalarMulWCProof<P>>,
}

impl<P: PedersenConfig> FSECScalarMulWCProof<P> {
    /// Create. Runs the WC protocol SECPARAM times, each with independent randomness
    /// and an independent challenge bit derived from the transcript.
    pub fn create<T: RngCore + CryptoRng>(
        transcript: &mut Transcript,
        rng: &mut T,
        z_pt: &sw::Affine<<P as PedersenConfig>::OCurve>,
        z_scalar: &<<P as PedersenConfig>::OCurve as CurveConfig>::ScalarField,
        k: &sw::Affine<<P as PedersenConfig>::OCurve>,
        c_z: (&PedersenComm<P>, &PedersenComm<P>),
    ) -> Self {
        ECScalarMulTranscript::domain_sep(transcript);
        let mut proofs = Vec::with_capacity(P::SECPARAM);
        for _ in 0..P::SECPARAM {
            proofs.push(ECScalarMulWCProof::<P>::create(
                transcript, rng, z_pt, z_scalar, k, c_z,
            ));
        }
        Self { proofs }
    }

    /// Verify. Re-runs the transcript and checks every sub-proof.
    pub fn verify(
        &self,
        transcript: &mut Transcript,
        k: &sw::Affine<<P as PedersenConfig>::OCurve>,
        c_zx: &sw::Affine<P>,
        c_zy: &sw::Affine<P>,
    ) -> bool {
        ECScalarMulTranscript::domain_sep(transcript);
        if self.proofs.len() != P::SECPARAM {
            return false;
        }
        for proof in &self.proofs {
            if !proof.verify(transcript, k, c_zx, c_zy) {
                return false;
            }
        }
        true
    }
}
