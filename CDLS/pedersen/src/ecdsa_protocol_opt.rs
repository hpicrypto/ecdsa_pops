//! This file contains a protocol for proving knowledge of an ECDSA signature against
//! a committed-to public key, using the WC (without-commitment-to-scalar) variant
//! of the scalar-multiplication proof and the optimised standalone point-addition
//! proof.

use ark_ec::{
    short_weierstrass::{self as sw, SWCurveConfig},
    AffineRepr, CurveConfig, CurveGroup,
};
use merlin::Transcript;

use ark_ff::Field;
use ark_serialize::CanonicalSerialize;
use ark_std::ops::Mul;
use rand::{CryptoRng, RngCore};

use crate::{
    ec_point_add_protocol_opt_alone::{SqECPointAddIntermediate, SqECPointAddProof},
    fs_scalar_mul_wc_protocol::FSECScalarMulWCProof,
    pedersen_config::{PedersenComm, PedersenConfig},
    transcript::{ECDSASignatureTranscript, SqECPointAdditionTranscript},
};

/// ECDSASigWCProof. Container for a proof of ECDSA signature knowledge against a
/// committed public key, using the WC scalar-mul variant and Sq-PA standalone proof.
pub struct ECDSASigWCProof<P: PedersenConfig> {
    /// r: the signature value (i.e. R = u1*G + u2*Q).
    pub r: sw::Affine<P::OCurve>,

    /// cq_x: the commitment to the public key's x co-ordinate.
    pub cq_x: sw::Affine<P>,

    /// cq_y: the commitment to the public key's y co-ordinate.
    pub cq_y: sw::Affine<P>,

    /// c_lhs_x: commitment to lhs.x (lhs = tr^-1g + Q = zR).
    pub c_lhs_x: sw::Affine<P>,

    /// c_lhs_y: commitment to lhs.y.
    pub c_lhs_y: sw::Affine<P>,

    /// cs_x: the commitment to tr^-1g's x co-ordinate.
    pub cs_x: sw::Affine<P>,
    /// cs_xr: the randomness used when making cs_x.
    pub cs_xr: P::ScalarField,

    /// cs_y: the commitment to tr^-1g's y co-ordinate.
    pub cs_y: sw::Affine<P>,
    /// cs_yr: the randomness used when making cs_y.
    pub cs_yr: P::ScalarField,

    /// scalar_mul: WC-variant proof for zR = lhs.
    pub scalar_mul: FSECScalarMulWCProof<P>,

    /// point_add: Sq-PA proof that tr^-1g + Q = lhs.
    pub point_add: SqECPointAddProof<P>,
}

/// Intermediate prover state for [ECDSASigWCProof].
pub struct ECDSASigWCProofIntermediate<P: PedersenConfig> {
    pub r: sw::Affine<P::OCurve>,
    pub cq_x: PedersenComm<P>,
    pub cq_y: PedersenComm<P>,
    pub c_lhs_x: PedersenComm<P>,
    pub c_lhs_y: PedersenComm<P>,
    pub cs_x: PedersenComm<P>,
    pub cs_y: PedersenComm<P>,
    pub addpi: SqECPointAddIntermediate<P>,
    pub trm1g: sw::Affine<P::OCurve>,
    pub sum: sw::Affine<P::OCurve>,
    pub z: <<P as PedersenConfig>::OCurve as CurveConfig>::ScalarField,
}

impl<P: PedersenConfig> ECDSASigWCProof<P> {
    /// Add the public commitments to the transcript.
    pub fn make_transcript(
        transcript: &mut Transcript,
        r: &sw::Affine<<P as PedersenConfig>::OCurve>,
        cq_x: &sw::Affine<P>,
        cq_y: &sw::Affine<P>,
        cs_x: &sw::Affine<P>,
        cs_y: &sw::Affine<P>,
    ) {
        ECDSASignatureTranscript::domain_sep(transcript);
        let mut compressed_bytes = Vec::new();

        r.serialize_compressed(&mut compressed_bytes).unwrap();
        ECDSASignatureTranscript::append_point(transcript, b"r", &compressed_bytes[..]);
        compressed_bytes.clear();

        cq_x.serialize_compressed(&mut compressed_bytes).unwrap();
        ECDSASignatureTranscript::append_point(transcript, b"cq_x", &compressed_bytes[..]);
        compressed_bytes.clear();

        cq_y.serialize_compressed(&mut compressed_bytes).unwrap();
        ECDSASignatureTranscript::append_point(transcript, b"cq_y", &compressed_bytes[..]);
        compressed_bytes.clear();

        cs_x.serialize_compressed(&mut compressed_bytes).unwrap();
        ECDSASignatureTranscript::append_point(transcript, b"cs_x", &compressed_bytes[..]);
        compressed_bytes.clear();

        cs_y.serialize_compressed(&mut compressed_bytes).unwrap();
        ECDSASignatureTranscript::append_point(transcript, b"cs_y", &compressed_bytes[..]);
    }

    /// Compute tr^-1*G as a point on the OCurve.
    fn make_trm1g(
        t: &<<P as PedersenConfig>::OCurve as CurveConfig>::ScalarField,
        r_x: &<<P as PedersenConfig>::OCurve as CurveConfig>::ScalarField,
    ) -> sw::Affine<P::OCurve> {
        let r_inv = r_x.inverse().unwrap();
        <<P as PedersenConfig>::OCurve as SWCurveConfig>::GENERATOR
            .mul(t.mul(r_inv))
            .into_affine()
    }

    /// Create the prover's intermediate state. Used when the transcript needs further
    /// information appended before the proof is finalised.
    pub fn create_intermediates<T: RngCore + CryptoRng>(
        transcript: &mut Transcript,
        rng: &mut T,
        t: &<<P as PedersenConfig>::OCurve as CurveConfig>::ScalarField,
        r: &sw::Affine<<P as PedersenConfig>::OCurve>,
        r_x: &<<P as PedersenConfig>::OCurve as CurveConfig>::ScalarField,
        s: &<<P as PedersenConfig>::OCurve as CurveConfig>::ScalarField,
        q: &sw::Affine<<P as PedersenConfig>::OCurve>,
    ) -> ECDSASigWCProofIntermediate<P> {
        // Compute the tr⁻¹·G point and commit to its coordinates
        let trm1g = Self::make_trm1g(t, r_x);
        let cs_x = P::make_commitment_from_other(trm1g.x, rng);
        let cs_y = P::make_commitment_from_other(trm1g.y, rng);

        // Commit to the public-key coordinates.
        let cq_x = PedersenComm::new(P::from_ob_to_sf(q.x), rng);
        let cq_y = PedersenComm::new(P::from_ob_to_sf(q.y), rng);

        // z = s·r^-1
        let z = *s / *r_x;

        // Build the transcript with what we have so far
        Self::make_transcript(
            transcript, r, &cq_x.comm, &cq_y.comm, &cs_x.comm, &cs_y.comm,
        );

        // lhs = tr^-1*G + Q  (also equals z·R by the ECDSA identity).
        let lhs = (trm1g + q).into_affine();
        let c_lhs_x = PedersenComm::new(<P as PedersenConfig>::from_ob_to_sf(lhs.x), rng);
        let c_lhs_y = PedersenComm::new(<P as PedersenConfig>::from_ob_to_sf(lhs.y), rng);

        let addpi = SqECPointAddProof::<P>::create_intermediates(
            transcript, rng, trm1g, *q, &cs_x, &cs_y, &cq_x, &cq_y, &c_lhs_x, &c_lhs_y,
        );

        ECDSASigWCProofIntermediate {
            r: *r,
            cq_x,
            cq_y,
            cs_x,
            cs_y,
            c_lhs_x,
            c_lhs_y,
            addpi,
            sum: lhs,
            trm1g,
            z,
        }
    }

    /// Create a full proof: builds the intermediates then runs the sub-proofs.
    pub fn create<T: RngCore + CryptoRng>(
        transcript: &mut Transcript,
        rng: &mut T,
        t: &<<P as PedersenConfig>::OCurve as CurveConfig>::ScalarField,
        r: &sw::Affine<<P as PedersenConfig>::OCurve>,
        r_x: &<<P as PedersenConfig>::OCurve as CurveConfig>::ScalarField,
        s: &<<P as PedersenConfig>::OCurve as CurveConfig>::ScalarField,
        q: &sw::Affine<<P as PedersenConfig>::OCurve>,
    ) -> Self {
        let inter = Self::create_intermediates(transcript, rng, t, r, r_x, s, q);
        Self::create_proof(transcript, rng, r, &inter, q)
    }

    /// Build the proof from intermediates.
    pub fn create_proof<T: RngCore + CryptoRng>(
        transcript: &mut Transcript,
        rng: &mut T,
        r: &sw::Affine<<P as PedersenConfig>::OCurve>,
        inter: &ECDSASigWCProofIntermediate<P>,
        q: &sw::Affine<<P as PedersenConfig>::OCurve>,
    ) -> Self {
        // WC scalar-mul proof: proves z·R = lhs, where lhs is committed via (c_lhs_x, c_lhs_y).
        let scalar_mul = FSECScalarMulWCProof::<P>::create(
            transcript,
            rng,
            &inter.sum,                       // z_pt = z·R = lhs
            &inter.z,                         // the secret scalar z
            r,                                // K = R (base point for the scalar mult)
            (&inter.c_lhs_x, &inter.c_lhs_y), // commitments to lhs's coordinates
        );

        let chal_buf = SqECPointAdditionTranscript::challenge_scalar(transcript, b"c");
        let chal = <P as PedersenConfig>::make_challenge_from_buffer(&chal_buf);

        let point_add = SqECPointAddProof::<P>::create_proof_with_challenge(
            inter.trm1g, // a
            *q,          // b
            inter.sum,   // t (target)
            &inter.addpi,
            &inter.cs_x,
            &inter.cs_y, // c1, c2
            &inter.cq_x,
            &inter.cq_y, // c3, c4
            &inter.c_lhs_x,
            &inter.c_lhs_y, // c5, c6
            &chal,
        );

        Self {
            r: *r,
            cq_x: inter.cq_x.comm,
            cq_y: inter.cq_y.comm,
            cs_x: inter.cs_x.comm,
            cs_xr: inter.cs_x.r,
            cs_y: inter.cs_y.comm,
            cs_yr: inter.cs_y.r,
            c_lhs_x: inter.c_lhs_x.comm,
            c_lhs_y: inter.c_lhs_y.comm,
            scalar_mul,
            point_add,
        }
    }

    /// Verify the tr⁻¹·G commitments by reopening them with the revealed randomness.
    pub fn verify_trm1g_commitments(
        &self,
        r: &sw::Affine<<P as PedersenConfig>::OCurve>,
        t: &<<P as PedersenConfig>::OCurve as CurveConfig>::ScalarField,
    ) -> bool {
        let trm1g = Self::make_trm1g(t, &P::from_ob_to_os(r.x));

        let gx = P::msm_generators(&P::from_ob_to_sf(trm1g.x), &self.cs_xr);
        let gy = P::msm_generators(&P::from_ob_to_sf(trm1g.y), &self.cs_yr);

        gx == self.cs_x.into_group() && gy == self.cs_y.into_group()
    }

    pub fn verify(
        &self,
        transcript: &mut Transcript,
        r: &sw::Affine<<P as PedersenConfig>::OCurve>,
        t: &<<P as PedersenConfig>::OCurve as CurveConfig>::ScalarField,
    ) -> bool {
        Self::make_transcript(
            transcript, &self.r, &self.cq_x, &self.cq_y, &self.cs_x, &self.cs_y,
        );

        SqECPointAddProof::<P>::make_transcript(
            transcript,
            &self.cs_x,
            &self.cs_y,
            &self.cq_x,
            &self.cq_y,
            &self.c_lhs_x,
            &self.c_lhs_y,
            &self.point_add.c_tau,
            &self.point_add.t1,
            &self.point_add.t2,
            &self.point_add.t3,
            &self.point_add.t4,
            &self.point_add.t5,
            &self.point_add.t6,
            &self.point_add.t7,
            &self.point_add.u1,
            &self.point_add.u2,
            &self.point_add.u3,
        );

        if !self.scalar_mul.verify(transcript, r, &self.c_lhs_x, &self.c_lhs_y) {
            eprintln!("FAIL: scalar_mul");
            return false;
        }

        let chal_buf = SqECPointAdditionTranscript::challenge_scalar(transcript, b"c");
        let chal = <P as PedersenConfig>::make_challenge_from_buffer(&chal_buf);

        if !self.point_add.verify_with_challenge(
            &self.cs_x,
            &self.cs_y,
            &self.cq_x,
            &self.cq_y,
            &self.c_lhs_x,
            &self.c_lhs_y,
            &chal,
        ) {
            eprintln!("FAIL: point_add");
            return false;
        }

        if !self.verify_trm1g_commitments(r, t) {
            eprintln!("FAIL: trm1g_commitments");
            return false;
        }

        true
    }

    /// Bytes needed to serialize this proof (sum of field-by-field sizes).
    // Note: scalar_mul and point_add sizes not included. Use
    // CanonicalSerialize on the whole struct (via derive) for total size.
    pub fn serialized_size(&self) -> usize {
        self.r.compressed_size()
            + self.cq_x.compressed_size()
            + self.cq_y.compressed_size()
            + self.cs_x.compressed_size()
            + self.cs_xr.compressed_size()
            + self.cs_y.compressed_size()
            + self.cs_yr.compressed_size()
            + self.c_lhs_x.compressed_size()
            + self.c_lhs_y.compressed_size()
    }
}
