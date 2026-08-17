//! Declares a series of transcript types for Merlin transcripts.
//! WARNING: This trait differs slightly from how Merlin defines the same traits. Essentially, rather than
//! re-instantiating this type for each different point type that we use, we simply traffic bytes in and out for e.g
//! appending points or producing challenges. It is the responsibility of the caller to realise this functionality.

use merlin::Transcript;

pub const CHALLENGE_SIZE: usize = 64;

pub trait EqualityTranscript {
    /// Append a domain separator.
    fn domain_sep(&mut self);

    /// Append a point.
    fn append_point(&mut self, label: &'static [u8], point: &[u8]);

    /// Produce the challenge.
    fn challenge_scalar(&mut self, label: &'static [u8]) -> [u8; CHALLENGE_SIZE];
}

impl EqualityTranscript for Transcript {
    fn domain_sep(&mut self) {
        self.append_message(b"dom-sep", b"equality-proof")
    }

    fn append_point(&mut self, label: &'static [u8], point: &[u8]) {
        self.append_message(label, point);
    }

    fn challenge_scalar(&mut self, label: &'static [u8]) -> [u8; CHALLENGE_SIZE] {
        let mut buf = [0u8; CHALLENGE_SIZE];
        self.challenge_bytes(label, &mut buf);
        buf
    }
}

pub trait OpeningTranscript {
    /// Append a domain separator.
    fn domain_sep(&mut self);

    /// Append a point.
    fn append_point(&mut self, label: &'static [u8], point: &[u8]);

    /// Produce the challenge.
    fn challenge_scalar(&mut self, label: &'static [u8]) -> [u8; CHALLENGE_SIZE];
}

impl OpeningTranscript for Transcript {
    fn domain_sep(&mut self) {
        self.append_message(b"dom-sep", b"open-proof")
    }

    fn append_point(&mut self, label: &'static [u8], point: &[u8]) {
        self.append_message(label, point);
    }

    fn challenge_scalar(&mut self, label: &'static [u8]) -> [u8; CHALLENGE_SIZE] {
        let mut buf = [0u8; CHALLENGE_SIZE];
        self.challenge_bytes(label, &mut buf);
        buf
    }
}

pub trait MulTranscript {
    /// Append a domain separator.
    fn domain_sep(&mut self);

    /// Append a point.
    fn append_point(&mut self, label: &'static [u8], point: &[u8]);

    /// Produce the challenge.
    fn challenge_scalar(&mut self, label: &'static [u8]) -> [u8; CHALLENGE_SIZE];
}

impl MulTranscript for Transcript {
    fn domain_sep(&mut self) {
        self.append_message(b"dom-sep", b"mul-proof")
    }

    fn append_point(&mut self, label: &'static [u8], point: &[u8]) {
        self.append_message(label, point);
    }

    fn challenge_scalar(&mut self, label: &'static [u8]) -> [u8; CHALLENGE_SIZE] {
        let mut buf = [0u8; CHALLENGE_SIZE];
        self.challenge_bytes(label, &mut buf);
        buf
    }
}

/// SqTranscript. Transcript operations for the Π_Sq squaring proof.
pub trait SqTranscript {
    /// Apply the domain separator for the squaring proof.
    fn domain_sep(&mut self);
    /// Append a serialized point with a label.
    fn append_point(&mut self, label: &'static [u8], point: &[u8]);
    /// Derive a 64-byte challenge.
    fn challenge_scalar(&mut self, label: &'static [u8]) -> [u8; 64];
}

impl SqTranscript for Transcript {
    fn domain_sep(&mut self) {
        self.append_message(b"dom-sep", b"sq-proof-v1");
    }

    fn append_point(&mut self, label: &'static [u8], point: &[u8]) {
        self.append_message(label, point);
    }

    fn challenge_scalar(&mut self, label: &'static [u8]) -> [u8; 64] {
        let mut buf = [0u8; 64];
        self.challenge_bytes(label, &mut buf);
        buf
    }
}

pub trait NonZeroTranscript {
    /// Append a domain separator.
    fn domain_sep(&mut self);

    /// Append a point.
    fn append_point(&mut self, label: &'static [u8], point: &[u8]);

    /// Produce the challenge.
    fn challenge_scalar(&mut self, label: &'static [u8]) -> [u8; CHALLENGE_SIZE];
}

impl NonZeroTranscript for Transcript {
    fn domain_sep(&mut self) {
        self.append_message(b"dom-sep", b"non-zero-proof")
    }

    fn append_point(&mut self, label: &'static [u8], point: &[u8]) {
        self.append_message(label, point);
    }

    fn challenge_scalar(&mut self, label: &'static [u8]) -> [u8; CHALLENGE_SIZE] {
        let mut buf = [0u8; CHALLENGE_SIZE];
        self.challenge_bytes(label, &mut buf);
        buf
    }
}

pub trait ECPointAdditionTranscript {
    /// Append a domain separator.
    fn domain_sep(&mut self);

    /// Append a point.
    fn append_point(&mut self, label: &'static [u8], point: &[u8]);

    /// Produce the challenge.
    fn challenge_scalar(&mut self, label: &'static [u8]) -> [u8; CHALLENGE_SIZE];
}

impl ECPointAdditionTranscript for Transcript {
    fn domain_sep(&mut self) {
        self.append_message(b"dom-sep", b"ec-point-addition-proof");
    }

    fn append_point(&mut self, label: &'static [u8], point: &[u8]) {
        self.append_message(label, point);
    }

    fn challenge_scalar(&mut self, label: &'static [u8]) -> [u8; CHALLENGE_SIZE] {
        let mut buf = [0u8; CHALLENGE_SIZE];
        self.challenge_bytes(label, &mut buf);
        buf
    }
}

/// OptECPointAdditionTranscript. Transcript operations for Π'_PA (the optimised
/// point-addition protocol ).
pub trait OptECPointAdditionTranscript {
    /// Apply the domain separator for the optimised point-add proof.
    fn domain_sep(&mut self);
    /// Append a serialized point with a label.
    fn append_point(&mut self, label: &'static [u8], point: &[u8]);
    /// Derive a 64-byte challenge.
    fn challenge_scalar(&mut self, label: &'static [u8]) -> [u8; 64];
}

impl OptECPointAdditionTranscript for Transcript {
    fn domain_sep(&mut self) {
        self.append_message(b"dom-sep", b"opt-ec-point-add-v1");
    }

    fn append_point(&mut self, label: &'static [u8], point: &[u8]) {
        self.append_message(label, point);
    }

    fn challenge_scalar(&mut self, label: &'static [u8]) -> [u8; 64] {
        let mut buf = [0u8; 64];
        self.challenge_bytes(label, &mut buf);
        buf
    }
}

/// SqECPointAdditionTranscript. Transcript operations for Π_PA (the standalone
/// optimised point-addition protocol with Opt 1,2 but not Opt 3).
pub trait SqECPointAdditionTranscript {
    /// Apply the domain separator for the Sq point-add proof.
    fn domain_sep(&mut self);
    /// Append a serialised point with a label.
    fn append_point(&mut self, label: &'static [u8], point: &[u8]);
    /// Derive a 64-byte challenge.
    fn challenge_scalar(&mut self, label: &'static [u8]) -> [u8; 64];
}

impl SqECPointAdditionTranscript for Transcript {
    fn domain_sep(&mut self) {
        self.append_message(b"dom-sep", b"sq-ec-point-add-v1");
    }

    fn append_point(&mut self, label: &'static [u8], point: &[u8]) {
        self.append_message(label, point);
    }

    fn challenge_scalar(&mut self, label: &'static [u8]) -> [u8; 64] {
        let mut buf = [0u8; 64];
        self.challenge_bytes(label, &mut buf);
        buf
    }
}

pub trait ZKAttestECPointAdditionTranscript {
    /// Append a domain separator.
    fn domain_sep(&mut self);

    /// Append a point.
    fn append_point(&mut self, label: &'static [u8], point: &[u8]);

    /// Produce the challenge.
    fn challenge_scalar(&mut self, label: &'static [u8]) -> [u8; CHALLENGE_SIZE];
}

impl ZKAttestECPointAdditionTranscript for Transcript {
    fn domain_sep(&mut self) {
        self.append_message(b"dom-sep", b"zk-attest-ec-point-addition-proof");
    }

    fn append_point(&mut self, label: &'static [u8], point: &[u8]) {
        self.append_message(label, point);
    }

    fn challenge_scalar(&mut self, label: &'static [u8]) -> [u8; CHALLENGE_SIZE] {
        let mut buf = [0u8; 64];
        self.challenge_bytes(label, &mut buf);
        buf
    }
}
pub trait ECScalarMulTranscript {
    /// Append a domain separator.
    fn domain_sep(&mut self);

    /// Append a point.
    fn append_point(&mut self, label: &'static [u8], point: &[u8]);

    /// Produce the challenge.
    fn challenge_scalar(&mut self, label: &'static [u8]) -> [u8; CHALLENGE_SIZE];
}

impl ECScalarMulTranscript for Transcript {
    fn domain_sep(&mut self) {
        self.append_message(b"dom-sep", b"ec-point-scalar-mul-proof");
    }

    fn append_point(&mut self, label: &'static [u8], point: &[u8]) {
        self.append_message(label, point);
    }

    fn challenge_scalar(&mut self, label: &'static [u8]) -> [u8; CHALLENGE_SIZE] {
        let mut buf = [0u8; CHALLENGE_SIZE];
        self.challenge_bytes(label, &mut buf);
        buf
    }
}

pub trait ZKAttestECScalarMulTranscript {
    /// Append a domain separator.
    fn domain_sep(&mut self);

    /// Append a point.
    fn append_point(&mut self, label: &'static [u8], point: &[u8]);

    /// Produce the challenge.
    fn challenge_scalar(&mut self, label: &'static [u8]) -> [u8; CHALLENGE_SIZE];
}

impl ZKAttestECScalarMulTranscript for Transcript {
    fn domain_sep(&mut self) {
        self.append_message(b"dom-sep", b"zk-attest-ec-point-scalar-mul-proof");
    }

    fn append_point(&mut self, label: &'static [u8], point: &[u8]) {
        self.append_message(label, point);
    }

    fn challenge_scalar(&mut self, label: &'static [u8]) -> [u8; CHALLENGE_SIZE] {
        let mut buf = [0u8; CHALLENGE_SIZE];
        self.challenge_bytes(label, &mut buf);
        buf
    }
}

pub trait FSECScalarMulTranscript {
    /// Append a domain separator.
    fn domain_sep(&mut self);

    /// Append a point.
    fn append_point(&mut self, label: &'static [u8], point: &[u8]);

    /// Produce the challenge.
    /// N.B 32 byte challenge - 256 bit challenge. Callers can use less of
    /// this for e.g 128 bit challenges.
    fn challenge_scalar(&mut self, label: &'static [u8]) -> [u8; 64];
}

impl FSECScalarMulTranscript for Transcript {
    fn domain_sep(&mut self) {
        self.append_message(b"dom-sep", b"fs-ec-point-scalar-addition-proof");
    }

    fn append_point(&mut self, label: &'static [u8], point: &[u8]) {
        self.append_message(label, point);
    }

    fn challenge_scalar(&mut self, label: &'static [u8]) -> [u8; 64] {
        let mut buf = [0u8; 64];
        self.challenge_bytes(label, &mut buf);
        buf
    }
}

pub trait ZKAttestFSECScalarMulTranscript {
    /// Append a domain separator.
    fn domain_sep(&mut self);

    /// Append a point.
    fn append_point(&mut self, label: &'static [u8], point: &[u8]);

    /// Produce the challenge.
    /// N.B 64 byte challenge -> 512 bits.
    fn challenge_scalar(&mut self, label: &'static [u8]) -> [u8; 64];
}

impl ZKAttestFSECScalarMulTranscript for Transcript {
    fn domain_sep(&mut self) {
        self.append_message(b"dom-sep", b"fs-zk-attest-ec-point-scalar-mul-proof");
    }

    fn append_point(&mut self, label: &'static [u8], point: &[u8]) {
        self.append_message(label, point);
    }

    fn challenge_scalar(&mut self, label: &'static [u8]) -> [u8; 64] {
        let mut buf = [0u8; 64];
        self.challenge_bytes(label, &mut buf);
        buf
    }
}

pub trait GKZeroOneTranscript {
    /// Append a domain separator.
    fn domain_sep(&mut self);

    /// Append a point.
    fn append_point(&mut self, label: &'static [u8], point: &[u8]);

    /// Produce the challenge.
    fn challenge_scalar(&mut self, label: &'static [u8]) -> [u8; CHALLENGE_SIZE];
}

impl GKZeroOneTranscript for Transcript {
    fn domain_sep(&mut self) {
        self.append_message(b"dom-sep", b"gk-zero-one-proof");
    }

    fn append_point(&mut self, label: &'static [u8], point: &[u8]) {
        self.append_message(label, point);
    }

    fn challenge_scalar(&mut self, label: &'static [u8]) -> [u8; CHALLENGE_SIZE] {
        let mut buf = [0u8; CHALLENGE_SIZE];
        self.challenge_bytes(label, &mut buf);
        buf
    }
}

pub trait ECDSASignatureTranscript {
    /// Append a domain separator.
    fn domain_sep(&mut self);

    /// Append a point.
    fn append_point(&mut self, label: &'static [u8], point: &[u8]);

    /// Produce the challenge.
    fn challenge_scalar(&mut self, label: &'static [u8]) -> [u8; CHALLENGE_SIZE];
}

impl ECDSASignatureTranscript for Transcript {
    fn domain_sep(&mut self) {
        self.append_message(b"dom-sep", b"ecdsa-signature-proof");
    }

    fn append_point(&mut self, label: &'static [u8], point: &[u8]) {
        self.append_message(label, point);
    }

    fn challenge_scalar(&mut self, label: &'static [u8]) -> [u8; CHALLENGE_SIZE] {
        let mut buf = [0u8; CHALLENGE_SIZE];
        self.challenge_bytes(label, &mut buf);
        buf
    }
}
