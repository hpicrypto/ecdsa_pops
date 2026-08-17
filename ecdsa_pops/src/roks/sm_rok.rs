//! SM RoK for reducing [RelSM] -> [RelTrivial], with CDLS WC scalar-mul.
use ark_ec::CurveGroup;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{end_timer, start_timer};

use halo2curves::t256::T256Affine;
use merlin::Transcript;
use r1csipa::TranscriptProtocol;

use rand_core::{CryptoRng, RngCore};

use rok::{RelTrivial, Relation, RoK};

use serde::{Deserialize, Deserializer, Serialize};

// CDLS library
use pedersen::{fs_scalar_mul_wc_protocol::FSECScalarMulWCProof, pedersen_config::PedersenComm};
use t256::Config as TomConfig;

use crate::{
    errors::PopError,
    relations::rsm::RelSM,
    utils::{fq_to_arkfq, fr_to_cdls_fr, p256_to_arkp256, t256_to_cdls_t256},
};

/// SM RoK proof with CDLS.
#[derive(Clone)]
pub struct SMProof {
    proof: FSECScalarMulWCProof<TomConfig>,
}

impl Serialize for SMProof {
    fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        let mut bytes = Vec::new();
        self.proof.serialize_compressed(&mut bytes).map_err(serde::ser::Error::custom)?;
        s.serialize_bytes(&bytes)
    }
}

impl<'de> Deserialize<'de> for SMProof {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        let bytes: Vec<u8> = Vec::<u8>::deserialize(d)?;
        let proof = FSECScalarMulWCProof::<TomConfig>::deserialize_compressed(&*bytes)
            .map_err(serde::de::Error::custom)?;
        Ok(SMProof { proof })
    }
}

#[derive(Clone)]
pub struct SMRoK {
    G: T256Affine,
    H: T256Affine,
}

impl SMRoK {
    pub fn from_ck(ck: &[T256Affine; 2]) -> Self {
        Self { G: ck[0], H: ck[1] }
    }
}

impl RoK for SMRoK {
    type RelationSource = RelSM;
    type RelationTarget = RelTrivial<PopError>;
    type Proof = SMProof;
    type Error = PopError;

    fn label() -> String {
        "SM RoK (CDLS)".into()
    }

    fn hash_statement(&self, rs: &Self::RelationSource, transcript: &mut Transcript) {
        transcript.append_u64(b"Append generator:", 1);
        transcript.append_point(b"G generator", &self.G);
        transcript.append_u64(b"Append generator:", 2);
        transcript.append_point(b"H generator", &self.H);

        transcript.append_point(b"Commitment to x", &rs.statement().c().0);
        transcript.append_point(b"Commitment to y", &rs.statement().c().1);
        transcript.append_point(b"Commitment to base point", rs.statement().g());
    }

    fn reduce<R: RngCore + CryptoRng>(
        &self,
        transcript: &mut Transcript,
        rs: &RelSM,
        rng: &mut R,
    ) -> Result<(Self::RelationTarget, Self::Proof), Self::Error> {
        let t = start_timer!(|| "SM RoK Prover (CDLS)");
        self.initialize(rs, transcript);

        let w = rs.witness().clone().ok_or_else(|| PopError::MissingWitness(RelSM::label()))?;

        // Public: base K = R, witness: scalar ω = z.
        let base = p256_to_arkp256(&rs.statement().g());
        let scalar = fq_to_arkfq(&w.scalar());

        // Result S = ω*K, committed coordinate-wise in T256.
        let result = (base * scalar).into_affine();

        // Build PedersenComms for S's coordinates from the relation's statement.
        let cx = t256_to_cdls_t256(&rs.statement().c().0);
        let cy = t256_to_cdls_t256(&rs.statement().c().1);
        let c_zx = PedersenComm::<TomConfig> {
            comm: cx,
            r: fr_to_cdls_fr(&w.rho().0),
        };
        let c_zy = PedersenComm::<TomConfig> {
            comm: cy,
            r: fr_to_cdls_fr(&w.rho().1),
        };

        let mut digest = [0u8; 32];
        transcript.challenge_bytes(b"outer transcript digest", &mut digest);
        let mut inner = Transcript::new(b"CDLS sm-wc for SMRoK");
        inner.append_message(b"outer transcript digest", &digest);

        let proof = FSECScalarMulWCProof::<TomConfig>::create(
            &mut inner,
            rng,
            &result,
            &scalar,
            &base,
            (&c_zx, &c_zy),
        );

        end_timer!(t);
        Ok((RelTrivial::default(), SMProof { proof }))
    }

    fn reduce_statement(
        &self,
        transcript: &mut Transcript,
        rs: &Self::RelationSource,
        proof: &Self::Proof,
    ) -> Result<Self::RelationTarget, Self::Error> {
        let t = start_timer!(|| "SM RoK Verifier (CDLS)");

        if self.G != *rs.params().g() || self.H != *rs.params().h() {
            return Err(PopError::RoKError(
                Self::label() + ": invalid parameters in statement",
            ));
        }
        self.initialize(rs, transcript);

        let base = p256_to_arkp256(&rs.statement().g());
        let cx = t256_to_cdls_t256(&rs.statement().c().0);
        let cy = t256_to_cdls_t256(&rs.statement().c().1);

        let mut digest = [0u8; 32];
        transcript.challenge_bytes(b"outer transcript digest", &mut digest);
        let mut inner = Transcript::new(b"CDLS sm-wc for SMRoK");
        inner.append_message(b"outer transcript digest", &digest);

        let ok = proof.proof.verify(&mut inner, &base, &cx, &cy);

        end_timer!(t);
        if ok {
            Ok(RelTrivial::default())
        } else {
            Err(PopError::RoKError(
                Self::label() + ": proof verification failed",
            ))
        }
    }
}
