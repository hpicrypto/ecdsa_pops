//! Defines a protocol for a non-zero proof.
//! This protocol proves that x != 0 given C_1 as a Pedersen commitment to z = g^x * h^r (over F_p)

use ark_ec::{
    short_weierstrass::{self as sw},
    AffineRepr, CurveConfig, CurveGroup, VariableBaseMSM,
};
use merlin::Transcript;

use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{ops::Mul, UniformRand};
use rand::{CryptoRng, RngCore};

use crate::{
    pedersen_config::PedersenComm, pedersen_config::PedersenConfig, transcript::NonZeroTranscript,
};

use ark_ec::short_weierstrass::Affine;

/// NonZeroProofTranscriptable. This trait provides a notion of `Transcriptable`, which implies
/// that the particular struct can be, in some sense, added to the transcript for a non-zero proof.
pub trait NonZeroProofTranscriptable {
    /// Affine: the type of random point.
    type Affine;
    /// add_to_transcript. This function simply adds  the commitment various commitments to the `transcript`
    /// object.
    /// # Arguments
    /// * `self` - the proof object.
    /// * `c1` - the c1 commitment that is being added to the transcript.
    /// * `c2` - the c2 commitment that is being added to the transcript.
    /// * `c3` - the c3 commitment that is being added to the transcript.
    fn add_to_transcript(&self, transcript: &mut Transcript, c1: &Self::Affine);
}

/// NonZeroProof. This struct acts as a container for a NonZeroProof.
/// Essentially, a new proof object can be created by calling `create`, whereas
/// an existing proof can be verified by calling `verify`.
/// The challenge is `c` and the random values are `a1, ..., a4`.
/// We also have that C = xg + rh.
#[derive(CanonicalSerialize, CanonicalDeserialize)]
pub struct NonZeroProof<P: PedersenConfig> {
    /// t1: a random point produced by the prover during setup.
    pub t1: sw::Affine<P>,
    /// t2: a random point produced by the prover during setup.
    pub t2: sw::Affine<P>,
    /// t3: a random point produced by the prover during setup.
    pub t3: sw::Affine<P>,

    /// s1: the first part of the response. This is the same as a2 + c * a1.
    pub s1: <P as CurveConfig>::ScalarField,
    /// s2: the second part of the response. This is the same as a3 + c * a1 * r.
    pub s2: <P as CurveConfig>::ScalarField,
    /// s3: the third part of the response. This is the same as a4 + c * a1 * x.
    pub s3: <P as CurveConfig>::ScalarField,
}

/// NonZeroProofIntermediate. This struct provides a convenient wrapper
/// for building all of the random values _before_ the challenge is generated.
/// This struct should only be used if the transcript needs to modified in some way
/// before the proof is generated.
pub struct NonZeroProofIntermediate<P: PedersenConfig> {
    /// t1: a random point produced by the prover during setup.
    pub t1: sw::Affine<P>,
    /// t2: a random point produced by the prover during setup.
    pub t2: sw::Affine<P>,
    /// t3: a random point produced by the prover during setup.
    pub t3: sw::Affine<P>,

    /// a1: a random private value made during setup.
    pub a1: <P as CurveConfig>::ScalarField,
    /// a2: a random private value made during setup.
    pub a2: <P as CurveConfig>::ScalarField,
    /// a3: a random private value made during setup.
    pub a3: <P as CurveConfig>::ScalarField,
    /// a4: a random private value made during setup.
    pub a4: <P as CurveConfig>::ScalarField,
}

// We need to implement these manually for generic structs.
impl<P: PedersenConfig> Copy for NonZeroProofIntermediate<P> {}
impl<P: PedersenConfig> Clone for NonZeroProofIntermediate<P> {
    fn clone(&self) -> Self {
        *self
    }
}

/// NonZeroProofIntermediateTranscript. This struct provides a wrapper for every input
/// into the transcript i.e everything that's in `NonZeroProofIntermediate` except from
/// the randomness values.
pub struct NonZeroProofIntermediateTranscript<P: PedersenConfig> {
    /// t1: a random point produced by the prover during setup.
    pub t1: sw::Affine<P>,
    /// t2: a random point produced by the prover during setup.
    pub t2: sw::Affine<P>,
    /// t3: a random point produced by the prover during setup.
    pub t3: sw::Affine<P>,
}

impl<P: PedersenConfig> NonZeroProof<P> {
    /// make_intermediate_transcript. This function accepts a set of intermediate values (`inter`)
    /// and builds a new NonZeroProofIntermediateTranscript from `inter`.
    /// # Arguments
    /// * `inter` - the intermediate values to use.
    pub fn make_intermediate_transcript(
        inter: NonZeroProofIntermediate<P>,
    ) -> NonZeroProofIntermediateTranscript<P> {
        NonZeroProofIntermediateTranscript {
            t1: inter.t1,
            t2: inter.t2,
            t3: inter.t3,
        }
    }

    /// make_transcript. This function simply adds `c1`, and `t_*` to the `transcript` object.
    /// # Arguments
    /// * `transcript` - the transcript which is modified.
    /// * `c1` - the c1 commitment that is being added to the transcript.
    /// * `t1` - the t1 value that is being added to the transcript.
    /// * `t2` - the t2 value that is being added to the transcript.
    /// * `t3` - the t3 value that is being added to the transcript.
    pub fn make_transcript(
        transcript: &mut Transcript,
        c1: &sw::Affine<P>,
        t1: &sw::Affine<P>,
        t2: &sw::Affine<P>,
        t3: &sw::Affine<P>,
    ) {
        // This function just builds the transcript out of the various input values.
        // N.B Because of how we define the serialisation API to handle different numbers,
        // we use a temporary buffer here.
        transcript.domain_sep();
        let mut compressed_bytes = Vec::new();
        c1.serialize_compressed(&mut compressed_bytes).unwrap();
        transcript.append_point(b"C1", &compressed_bytes[..]);
        compressed_bytes.clear();

        t1.serialize_compressed(&mut compressed_bytes).unwrap();
        transcript.append_point(b"t1", &compressed_bytes[..]);
        compressed_bytes.clear();

        t2.serialize_compressed(&mut compressed_bytes).unwrap();
        transcript.append_point(b"t2", &compressed_bytes[..]);
        compressed_bytes.clear();

        t3.serialize_compressed(&mut compressed_bytes).unwrap();
        transcript.append_point(b"t3", &compressed_bytes[..]);
    }

    /// create. This function returns a new non-zero proof of the fact that x != 0 and c1 is a commitment
    /// to g^x * h^r.
    /// # Arguments
    /// * `transcript` - the transcript object that is modified.
    /// * `rng` - the RNG that is used to produce the random values. Must be cryptographically secure.
    /// * `x` - the non-zero value.
    /// * `c1` - the commitment to `x`.
    pub fn create<T: RngCore + CryptoRng>(
        transcript: &mut Transcript,
        rng: &mut T,
        x: &<P as CurveConfig>::ScalarField,
        c1: &PedersenComm<P>,
    ) -> Self {
        Self::create_proof(
            x,
            &Self::create_intermediates(transcript, rng, x, c1),
            c1,
            &transcript.challenge_scalar(b"c")[..],
        )
    }

    /// create_intermediates. This function returns a new set of intermediates
    /// for a non-zero proof. Namely, this function proves that `c1` is a commitment for
    /// `x`.
    /// # Arguments
    /// * `transcript` - the transcript object that is modified.
    /// * `x` - the non-zero value.
    /// * `c1` - the c1 commitment that is used. This is a commitment to `x`.
    pub fn create_intermediates<T: RngCore + CryptoRng>(
        transcript: &mut Transcript,
        rng: &mut T,
        x: &<P as CurveConfig>::ScalarField,
        c1: &PedersenComm<P>,
    ) -> NonZeroProofIntermediate<P> {
        // Generate the random values.
        let a1 = <P as CurveConfig>::ScalarField::rand(rng);
        let a2 = <P as CurveConfig>::ScalarField::rand(rng);
        let a3 = <P as CurveConfig>::ScalarField::rand(rng);
        let a4 = <P as CurveConfig>::ScalarField::rand(rng);

        let t1_p = (P::GENERATOR.mul(a1)).mul(x);
        let t2_p = {
            let b = [c1.comm, P::GENERATOR2];
            let s = [a2, a3];
            <sw::Projective<P> as VariableBaseMSM>::msm(&b, &s).unwrap()
        };
        let t3_p = P::GENERATOR.mul(a4);
        let normalized = sw::Projective::<P>::normalize_batch(&[t1_p, t2_p, t3_p]);
        let (t1, t2, t3) = (normalized[0], normalized[1], normalized[2]);

        // Add the values to the transcript.
        Self::make_transcript(transcript, &c1.comm, &t1, &t2, &t3);

        NonZeroProofIntermediate {
            t1,
            t2,
            t3,
            a1,
            a2,
            a3,
            a4,
        }
    }

    /// create_proof. This function returns a new non-zero proof
    /// usign the previously collected intermediates. Namely, this function proves that `c1` is a commitment for
    /// `x`, which is non-zero. Note that this function builds the challenge from the bytes supplied in `chal_buf`.
    ///
    /// # Arguments
    /// * `x` - the non-zero value.
    /// * `inter` - the intermediary values produced by a call to `create_intermediates`.
    /// * `c1` - the commitment to `x`.
    /// * `chal_buf` - the pre-determined challenge bytes.
    pub fn create_proof(
        x: &<P as CurveConfig>::ScalarField,
        inter: &NonZeroProofIntermediate<P>,
        c1: &PedersenComm<P>,
        chal_buf: &[u8],
    ) -> Self {
        // Make the challenge itself.
        let chal = <P as PedersenConfig>::make_challenge_from_buffer(chal_buf);
        Self::create_proof_with_challenge(x, inter, c1, &chal)
    }

    /// create_proof_with_challenge. This function creates a proof of non-zero
    /// using the pre-existing challenge `chal`. This function should only be used when the
    /// challenge is fixed across multiple, separate proofs.
    ///
    /// # Arguments
    /// * `x` - the non-zero value.
    /// * `inter` - the intermediary values produced by a call to `create_intermediates`.
    /// * `c1` - the commitment to `x`.
    /// * `chal` - the challenge.
    pub fn create_proof_with_challenge(
        x: &<P as CurveConfig>::ScalarField,
        inter: &NonZeroProofIntermediate<P>,
        c1: &PedersenComm<P>,
        chal: &<P as CurveConfig>::ScalarField,
    ) -> Self {
        let (s1, s2, s3) = if *chal == P::CM1 {
            (
                inter.a2 - inter.a1,
                inter.a3 + (inter.a1 * c1.r),
                inter.a4 - (inter.a1 * x),
            )
        } else if *chal == P::CP1 {
            (
                inter.a2 + inter.a1,
                inter.a3 - (inter.a1 * c1.r),
                inter.a4 + (inter.a1 * x),
            )
        } else {
            (
                inter.a2 + (*chal * inter.a1),
                inter.a3 - (*chal * (inter.a1 * c1.r)),
                inter.a4 + (*chal * (inter.a1 * x)),
            )
        };

        Self {
            t1: inter.t1,
            t2: inter.t2,
            t3: inter.t3,
            s1,
            s2,
            s3,
        }
    }

    /// verify. This function simply verifies that the proof held by `self` is a valid
    /// non-zero proof. Put differently, this function returns true if c1 is a valid
    /// commitment to `x` and `x` is non-zero, and false otherwise.
    /// # Arguments
    /// * `self` - the proof that is being verified.
    /// * `transcript` - the transcript object that's used.
    /// * `c1` - the c1 commitment. This acts as a commitment to `x`.
    pub fn verify(&self, transcript: &mut Transcript, c1: &sw::Affine<P>) -> bool {
        Self::make_transcript(transcript, c1, &self.t1, &self.t2, &self.t3);
        self.verify_proof(c1, &transcript.challenge_scalar(b"c")[..])
    }

    /// verify_proof. This function simply verifies that the proof held by `self` is a valid
    /// non-zero proof. Put differently, this function returns true if c1 is a valid
    /// commitment to `x` and `x` is non-zero, and false otherwise.
    /// Notably, this function uses the pre-existing challenge bytes supplied in `chal_buf`.
    /// # Arguments
    /// * `self` - the proof that is being verified.
    /// * `c1` - the c1 commitment. This acts as a commitment to `x`.
    pub fn verify_proof(&self, c1: &sw::Affine<P>, chal_buf: &[u8]) -> bool {
        let chal = <P as PedersenConfig>::make_challenge_from_buffer(chal_buf);
        self.verify_with_challenge(c1, &chal)
    }

    /// verify_with_challenge. This function simply verifies that the proof held by `self` is a valid
    /// non-zero proof. Put differently, this function returns true if c1 is a valid
    /// commitment to `x` and `x` is non-zero, and false otherwise.
    /// Notably, this function uses the pre-existing challenge supplied in `chal`.
    /// # Arguments
    /// * `self` - the proof that is being verified.
    /// * `c1` - the c1 commitment. This acts as a commitment to `x`.
    /// * `chal` - the challenge.
    pub fn verify_with_challenge(
        &self,
        c1: &sw::Affine<P>,
        chal: &<P as CurveConfig>::ScalarField,
    ) -> bool {
        // s1*C1 + s2*G2: same in every branch, so compute once.
        let rhs2 = {
            let bases = [*c1, P::GENERATOR2];
            let scalars = [self.s1, self.s2];
            <sw::Projective<P> as VariableBaseMSM>::msm(&bases, &scalars).unwrap()
        };

        let g_s3 = P::GENERATOR.mul(self.s3);

        if *chal == P::CM1 {
            (self.t1 != Affine::identity())
                && (self.t3 - self.t1 == P::GENERATOR.mul(self.s3))
                && (self.t2.into_group() - self.t1 == rhs2)
        } else if *chal == P::CP1 {
            (self.t1 != Affine::identity())
                && (self.t3 + self.t1 == P::GENERATOR.mul(self.s3))
                && (self.t2.into_group() + self.t1 == rhs2)
        } else {
            (self.t1 != Affine::identity())
                && (self.t3 + (self.t1.mul(*chal)) == P::GENERATOR.mul(self.s3))
                && (self.t2 + (self.t1.mul(*chal)) == rhs2)
        }
    }

    /// serialized_size. Returns the number of bytes needed to represent this proof object once serialised.
    pub fn serialized_size(&self) -> usize {
        <Self as CanonicalSerialize>::serialized_size(self, ark_serialize::Compress::Yes)
    }
}

impl<P: PedersenConfig> NonZeroProofTranscriptable for NonZeroProof<P> {
    type Affine = sw::Affine<P>;
    fn add_to_transcript(&self, transcript: &mut Transcript, c1: &Self::Affine) {
        NonZeroProof::make_transcript(transcript, c1, &self.t1, &self.t2, &self.t3);
    }
}

impl<P: PedersenConfig> NonZeroProofTranscriptable for NonZeroProofIntermediate<P> {
    type Affine = sw::Affine<P>;
    fn add_to_transcript(&self, transcript: &mut Transcript, c1: &sw::Affine<P>) {
        NonZeroProof::make_transcript(transcript, c1, &self.t1, &self.t2, &self.t3);
    }
}

impl<P: PedersenConfig> NonZeroProofTranscriptable for NonZeroProofIntermediateTranscript<P> {
    type Affine = sw::Affine<P>;
    fn add_to_transcript(&self, transcript: &mut Transcript, c1: &sw::Affine<P>) {
        NonZeroProof::make_transcript(transcript, c1, &self.t1, &self.t2, &self.t3);
    }
}

impl<P: PedersenConfig> NonZeroProofIntermediateTranscript<P> {
    /// serialized_size. Returns the number of bytes needed to represent this proof object once serialised.
    pub fn serialized_size(&self) -> usize {
        self.t1.compressed_size() + self.t2.compressed_size() + self.t3.compressed_size()
    }
}
