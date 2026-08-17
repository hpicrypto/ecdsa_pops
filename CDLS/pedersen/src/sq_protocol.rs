//! Defines the Π_Sq protocol: a proof of knowledge for the squaring relation.
//! Given Pedersen commitments C_1 = m*G + ρ_1*H and C_2 = m^2*G + ρ_2*H, the
//! prover demonstrates knowledge of (m, ρ_1, ρ_2) without revealing them.
//! Implements Fig. 10.

use ark_ec::{
    short_weierstrass::{self as sw},
    AffineRepr, CurveConfig, CurveGroup, VariableBaseMSM,
};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{ops::Mul, UniformRand};
use merlin::Transcript;
use rand::{CryptoRng, RngCore};

use crate::{
    pedersen_config::{PedersenComm, PedersenConfig},
    transcript::SqTranscript,
};

/// SqProofTranscriptable.
pub trait SqProofTranscriptable {
    /// Affine: the type of curve point.
    type Affine;
    /// Add the proof contributions to the transcript, given the two public
    /// commitments c1 (to m) and c2 (to m^2).
    fn add_to_transcript(&self, transcript: &mut Transcript, c1: &Self::Affine, c2: &Self::Affine);
}

/// SqProof. Container for a Π_Sq proof.
/// (m, ρ_1, ρ_2) is the witness,
/// (C_1, C_2) the statement, (C'_1, C'_2) the prover's first message, and
/// (m'', ρ''_1, ρ''_2) the response after receiving challenge c.
#[derive(CanonicalSerialize, CanonicalDeserialize)]
pub struct SqProof<P: PedersenConfig> {
    /// C'_1 = m'*G + ρ'_1*H
    pub c1_prime: sw::Affine<P>,
    /// C'_2 = m'*C_1 + ρ'_2*H
    pub c2_prime: sw::Affine<P>,
    /// m'' = m' + c*m
    pub m_double_prime: <P as CurveConfig>::ScalarField,
    /// ρ''_1 = ρ'_1 + c*ρ_1
    pub rho_1_double_prime: <P as CurveConfig>::ScalarField,
    /// ρ''_2 = ρ'_2 + c*(ρ_2 − ρ_1*m)
    pub rho_2_double_prime: <P as CurveConfig>::ScalarField,
}

/// SqProofIntermediate.
pub struct SqProofIntermediate<P: PedersenConfig> {
    /// Random m'
    pub m_prime: <P as CurveConfig>::ScalarField,
    /// Random ρ'_1
    pub rho_1_prime: <P as CurveConfig>::ScalarField,
    /// Random ρ'_2
    pub rho_2_prime: <P as CurveConfig>::ScalarField,
    /// C'_1 = m'*G + ρ'_1*H
    pub c1_prime: sw::Affine<P>,
    /// C'_2 = m'*C_1 + ρ'_2*H
    pub c2_prime: sw::Affine<P>,
}

impl<P: PedersenConfig> Copy for SqProofIntermediate<P> {}
impl<P: PedersenConfig> Clone for SqProofIntermediate<P> {
    fn clone(&self) -> Self {
        *self
    }
}

/// SqProofIntermediateTranscript. The transcript-visible portion of the
/// intermediate state.
pub struct SqProofIntermediateTranscript<P: PedersenConfig> {
    /// C'_1
    pub c1_prime: sw::Affine<P>,
    /// C'_2
    pub c2_prime: sw::Affine<P>,
}

impl<P: PedersenConfig> SqProof<P> {
    pub fn make_intermediate_transcript(
        inter: SqProofIntermediate<P>,
    ) -> SqProofIntermediateTranscript<P> {
        SqProofIntermediateTranscript {
            c1_prime: inter.c1_prime,
            c2_prime: inter.c2_prime,
        }
    }

    /// make_transcript. Append all public points to the transcript.
    pub fn make_transcript(
        transcript: &mut Transcript,
        c1: &sw::Affine<P>,
        c2: &sw::Affine<P>,
        c1_prime: &sw::Affine<P>,
        c2_prime: &sw::Affine<P>,
    ) {
        transcript.domain_sep();

        let mut buf = Vec::new();
        c1.serialize_compressed(&mut buf).unwrap();
        transcript.append_point(b"C1", &buf[..]);
        buf.clear();

        c2.serialize_compressed(&mut buf).unwrap();
        transcript.append_point(b"C2", &buf[..]);
        buf.clear();

        c1_prime.serialize_compressed(&mut buf).unwrap();
        transcript.append_point(b"C1p", &buf[..]);
        buf.clear();

        c2_prime.serialize_compressed(&mut buf).unwrap();
        transcript.append_point(b"C2p", &buf[..]);
    }

    /// create. Full proof of knowledge for (m, ρ_1, ρ_2) satisfying the
    /// squaring relation.
    pub fn create<T: RngCore + CryptoRng>(
        transcript: &mut Transcript,
        rng: &mut T,
        m: &<P as CurveConfig>::ScalarField,
        c1: &PedersenComm<P>,
        c2: &PedersenComm<P>,
    ) -> Self {
        Self::create_proof(
            m,
            &Self::create_intermediates(transcript, rng, c1, c2),
            c1,
            c2,
            &transcript.challenge_scalar(b"c")[..],
        )
    }

    /// create_intermediates. Sample random (m', ρ'_1, ρ'_2), compute
    /// (C'_1, C'_2), add them to the transcript, and return the prover state.
    pub fn create_intermediates<T: RngCore + CryptoRng>(
        transcript: &mut Transcript,
        rng: &mut T,
        c1: &PedersenComm<P>,
        c2: &PedersenComm<P>,
    ) -> SqProofIntermediate<P> {
        let m_prime = <P as CurveConfig>::ScalarField::rand(rng);
        let rho_1_prime = <P as CurveConfig>::ScalarField::rand(rng);
        let rho_2_prime = <P as CurveConfig>::ScalarField::rand(rng);

        // C'_1 = m'*G + ρ'_1*H, where (G, H) = (P::GENERATOR, P::GENERATOR2).
        let c1_prime_p = P::msm_generators(&m_prime, &rho_1_prime);

        // C'_2 = m'*C_1 + ρ'_2*H, where C_1 is the existing commitment to m.
        let c2_prime_p = {
            let bases = [c1.comm, P::GENERATOR2];
            let scalars = [m_prime, rho_2_prime];
            <sw::Projective<P> as VariableBaseMSM>::msm(&bases, &scalars).unwrap()
        };

        let pts = sw::Projective::<P>::normalize_batch(&[c1_prime_p, c2_prime_p]);
        let (c1_prime, c2_prime) = (pts[0], pts[1]);

        // Append to transcript before returning.
        Self::make_transcript(transcript, &c1.comm, &c2.comm, &c1_prime, &c2_prime);

        SqProofIntermediate {
            m_prime,
            rho_1_prime,
            rho_2_prime,
            c1_prime,
            c2_prime,
        }
    }

    /// create_proof. Build the proof from intermediates and a pre-derived
    /// challenge buffer.
    pub fn create_proof(
        m: &<P as CurveConfig>::ScalarField,
        inter: &SqProofIntermediate<P>,
        c1: &PedersenComm<P>,
        c2: &PedersenComm<P>,
        chal_buf: &[u8],
    ) -> Self {
        let chal = <P as PedersenConfig>::make_challenge_from_buffer(chal_buf);
        Self::create_proof_with_challenge(m, inter, c1, c2, &chal)
    }

    /// create_proof_with_challenge. Same as `create_proof`, but the caller
    /// supplies the challenge scalar directly. Used when the challenge is
    /// shared across multiple sub-proofs (e.g., inside ECPointAddProof).
    pub fn create_proof_with_challenge(
        m: &<P as CurveConfig>::ScalarField,
        inter: &SqProofIntermediate<P>,
        c1: &PedersenComm<P>,
        c2: &PedersenComm<P>,
        chal: &<P as CurveConfig>::ScalarField,
    ) -> Self {
        let (m_double_prime, rho_1_double_prime, rho_2_double_prime) = if *chal == P::CM1 {
            (
                inter.m_prime - *m,
                inter.rho_1_prime - c1.r,
                inter.rho_2_prime - (c2.r - c1.r * *m),
            )
        } else if *chal == P::CP1 {
            (
                inter.m_prime + *m,
                inter.rho_1_prime + c1.r,
                inter.rho_2_prime + (c2.r - c1.r * *m),
            )
        } else {
            (
                inter.m_prime + *chal * *m,
                inter.rho_1_prime + *chal * c1.r,
                inter.rho_2_prime + *chal * (c2.r - c1.r * *m),
            )
        };

        Self {
            c1_prime: inter.c1_prime,
            c2_prime: inter.c2_prime,
            m_double_prime,
            rho_1_double_prime,
            rho_2_double_prime,
        }
    }

    /// verify. Re-derive the challenge from the transcript and verify.
    pub fn verify(
        &self,
        transcript: &mut Transcript,
        c1: &sw::Affine<P>,
        c2: &sw::Affine<P>,
    ) -> bool {
        Self::make_transcript(transcript, c1, c2, &self.c1_prime, &self.c2_prime);
        self.verify_proof(c1, c2, &transcript.challenge_scalar(b"c")[..])
    }

    /// verify_proof. Verify against a pre-derived challenge buffer.
    pub fn verify_proof(&self, c1: &sw::Affine<P>, c2: &sw::Affine<P>, chal_buf: &[u8]) -> bool {
        let chal = <P as PedersenConfig>::make_challenge_from_buffer(chal_buf);
        self.verify_with_challenge(c1, c2, &chal)
    }

    /// verify_with_challenge. Verify against an externally-supplied challenge.
    /// Checks the two equations from Fig. 10:
    /// m''*G + ρ''_1*H ?= C'_1 + c*C_1
    /// m''*C_1 + ρ''_2*H ?= C'_2 + c*C_2
    pub fn verify_with_challenge(
        &self,
        c1: &sw::Affine<P>,
        c2: &sw::Affine<P>,
        chal: &<P as CurveConfig>::ScalarField,
    ) -> bool {
        let lhs1 = P::msm_generators(&self.m_double_prime, &self.rho_1_double_prime);

        let lhs2 = {
            let bases = [*c1, P::GENERATOR2];
            let scalars = [self.m_double_prime, self.rho_2_double_prime];
            <sw::Projective<P> as VariableBaseMSM>::msm(&bases, &scalars).unwrap()
        };

        if *chal == P::CM1 {
            (self.c1_prime.into_group() - c1 == lhs1) && (self.c2_prime.into_group() - c2 == lhs2)
        } else if *chal == P::CP1 {
            (self.c1_prime.into_group() + c1 == lhs1) && (self.c2_prime.into_group() + c2 == lhs2)
        } else {
            (self.c1_prime + c1.mul(*chal) == lhs1) && (self.c2_prime + c2.mul(*chal) == lhs2)
        }
    }

    /// serialized_size. Bytes needed to represent this proof once serialised.
    pub fn serialized_size(&self) -> usize {
        self.c1_prime.compressed_size()
            + self.c2_prime.compressed_size()
            + self.m_double_prime.compressed_size()
            + self.rho_1_double_prime.compressed_size()
            + self.rho_2_double_prime.compressed_size()
    }
}

impl<P: PedersenConfig> SqProofTranscriptable for SqProof<P> {
    type Affine = sw::Affine<P>;
    fn add_to_transcript(&self, transcript: &mut Transcript, c1: &Self::Affine, c2: &Self::Affine) {
        SqProof::make_transcript(transcript, c1, c2, &self.c1_prime, &self.c2_prime);
    }
}

impl<P: PedersenConfig> SqProofTranscriptable for SqProofIntermediate<P> {
    type Affine = sw::Affine<P>;
    fn add_to_transcript(
        &self,
        transcript: &mut Transcript,
        c1: &sw::Affine<P>,
        c2: &sw::Affine<P>,
    ) {
        SqProof::make_transcript(transcript, c1, c2, &self.c1_prime, &self.c2_prime);
    }
}

impl<P: PedersenConfig> SqProofTranscriptable for SqProofIntermediateTranscript<P> {
    type Affine = sw::Affine<P>;
    fn add_to_transcript(
        &self,
        transcript: &mut Transcript,
        c1: &sw::Affine<P>,
        c2: &sw::Affine<P>,
    ) {
        SqProof::make_transcript(transcript, c1, c2, &self.c1_prime, &self.c2_prime);
    }
}

impl<P: PedersenConfig> SqProofIntermediateTranscript<P> {
    /// serialized_size. Bytes needed to represent this transcript intermediate.
    pub fn serialized_size(&self) -> usize {
        self.c1_prime.compressed_size() + self.c2_prime.compressed_size()
    }
}
