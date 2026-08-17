use ark_ec::{short_weierstrass::Affine as SWAffine, AffineRepr};
use ark_secp256r1::Config as SecpConfig;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{end_timer, start_timer};
use halo2curves::t256::T256Affine;
use merlin::Transcript;
use r1csipa::TranscriptProtocol;
use rand_core::{CryptoRng, RngCore};
use rok::{RelTrivial, Relation, RoK};
use serde::{Deserialize, Deserializer, Serialize};

// CDLS library
use pedersen::{
    ec_point_add_protocol_opt_alone::SqECPointAddProof,
    pedersen_config::{PedersenComm, PedersenConfig},
};
use t256::Config as TomConfig;

use crate::{
    errors::PopError,
    relations::rpa::RelPA,
    utils::{fr_to_cdls_fr, p256_to_arkp256, t256_to_cdls_t256},
};

/// PA RoK proof, with the CDLS library. Uses the optimised standalone
/// point-addition proof (Opt 1 and 2, retains the C_2
/// opening proof, so safe to use standalone, not just inside SM).
pub struct PAProof {
    proof: SqECPointAddProof<TomConfig>,
}

impl Serialize for PAProof {
    fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        let mut bytes = Vec::new();
        self.proof.serialize_compressed(&mut bytes).map_err(serde::ser::Error::custom)?;
        s.serialize_bytes(&bytes)
    }
}

impl<'de> Deserialize<'de> for PAProof {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        let bytes: Vec<u8> = Vec::<u8>::deserialize(d)?;
        let proof = SqECPointAddProof::<TomConfig>::deserialize_compressed(&*bytes)
            .map_err(serde::de::Error::custom)?;
        Ok(PAProof { proof })
    }
}

#[derive(Clone)]
pub struct PARoK {
    G: T256Affine,
    H: T256Affine,
}

impl PARoK {
    pub fn from_ck(ck: &[T256Affine; 2]) -> Self {
        Self { G: ck[0], H: ck[1] }
    }
}

impl RoK for PARoK {
    type RelationSource = RelPA;
    type RelationTarget = RelTrivial<PopError>;
    type Proof = PAProof;
    type Error = PopError;

    fn label() -> String {
        "PA RoK (CDLS Sq)".into()
    }

    fn hash_statement(&self, rs: &Self::RelationSource, transcript: &mut Transcript) {
        transcript.append_u64(b"Append generator:", 1);
        transcript.append_point(b"G generator", &self.G);
        transcript.append_u64(b"Append generator:", 2);
        transcript.append_point(b"H generator", &self.H);
        (0..3usize).for_each(|i| {
            transcript.append_u64(b"Append Commitment:", i as u64);
            transcript.append_point(b"Commitment to Px", &rs.statement().c(i).unwrap().0);
            transcript.append_point(b"Commitment to Py", &rs.statement().c(i).unwrap().1);
        });
    }

    fn reduce<R: RngCore + CryptoRng>(
        &self,
        transcript: &mut Transcript,
        rs: &RelPA,
        rng: &mut R,
    ) -> Result<(Self::RelationTarget, Self::Proof), Self::Error> {
        let t = start_timer!(|| "PA RoK Prover (CDLS Sq)");
        self.initialize(rs, transcript);

        let w = rs.witness().clone().ok_or_else(|| PopError::MissingWitness(RelPA::label()))?;

        // Witness: openings (rhos) and the three Secp256r1 points (A, B, T).
        let rhos = w.rhos().map(|r| (fr_to_cdls_fr(&r.0), fr_to_cdls_fr(&r.1)));
        let ps = w.ps().map(|p| p256_to_arkp256(&p));
        // ps[0] = A, ps[1] = B, ps[2] = T

        // Statement: six commitment points (x and y of A, B, T).
        let cax = t256_to_cdls_t256(&rs.statement().c(0).unwrap().0);
        let cay = t256_to_cdls_t256(&rs.statement().c(0).unwrap().1);
        let cbx = t256_to_cdls_t256(&rs.statement().c(1).unwrap().0);
        let cby = t256_to_cdls_t256(&rs.statement().c(1).unwrap().1);
        let ctx = t256_to_cdls_t256(&rs.statement().c(2).unwrap().0);
        let cty = t256_to_cdls_t256(&rs.statement().c(2).unwrap().1);

        // Build the six PedersenComm<TomConfig>:
        // c1,c2 = a.x,a.y ; c3,c4 = b.x,b.y ; c5,c6 = t.x,t.y.
        let c1 = PedersenComm::<TomConfig> {
            comm: cax,
            r: rhos[0].0,
        };
        let c2 = PedersenComm::<TomConfig> {
            comm: cay,
            r: rhos[0].1,
        };
        let c3 = PedersenComm::<TomConfig> {
            comm: cbx,
            r: rhos[1].0,
        };
        let c4 = PedersenComm::<TomConfig> {
            comm: cby,
            r: rhos[1].1,
        };
        let c5 = PedersenComm::<TomConfig> {
            comm: ctx,
            r: rhos[2].0,
        };
        let c6 = PedersenComm::<TomConfig> {
            comm: cty,
            r: rhos[2].1,
        };

        // Bridge outer transcript, inner via challenge digest.
        let mut digest = [0u8; 32];
        transcript.challenge_bytes(b"outer transcript digest", &mut digest);
        let mut inner = Transcript::new(b"CDLS Sq pa for PARoK");
        inner.append_message(b"outer transcript digest", &digest);

        // Sq-PA create: takes (transcript, rng, a, b, t, c1..c6).
        let proof = SqECPointAddProof::<TomConfig>::create(
            &mut inner, rng, ps[0], ps[1], ps[2], &c1, &c2, &c3, &c4, &c5, &c6,
        );

        end_timer!(t);
        Ok((RelTrivial::default(), PAProof { proof }))
    }

    fn reduce_statement(
        &self,
        transcript: &mut Transcript,
        rs: &Self::RelationSource,
        proof: &Self::Proof,
    ) -> Result<Self::RelationTarget, Self::Error> {
        let t = start_timer!(|| "PA RoK Verifier (CDLS Sq)");

        if self.G != *rs.params().g() || self.H != *rs.params().h() {
            return Err(PopError::RoKError(
                Self::label() + ": invalid parameters in statement",
            ));
        }
        self.initialize(rs, transcript);

        // Verifier has only the commitment points, not openings.
        let cax = t256_to_cdls_t256(&rs.statement().c(0).unwrap().0);
        let cay = t256_to_cdls_t256(&rs.statement().c(0).unwrap().1);
        let cbx = t256_to_cdls_t256(&rs.statement().c(1).unwrap().0);
        let cby = t256_to_cdls_t256(&rs.statement().c(1).unwrap().1);
        let ctx = t256_to_cdls_t256(&rs.statement().c(2).unwrap().0);
        let cty = t256_to_cdls_t256(&rs.statement().c(2).unwrap().1);

        let mut digest = [0u8; 32];
        transcript.challenge_bytes(b"outer transcript digest", &mut digest);
        let mut inner = Transcript::new(b"CDLS Sq pa for PARoK");
        inner.append_message(b"outer transcript digest", &digest);

        // Sq-PA verify: absorbs proof, derives challenge, checks all 10 equations.
        let ok = proof.proof.verify(&mut inner, &cax, &cay, &cbx, &cby, &ctx, &cty);

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

#[cfg(test)]
mod tests {
    use ark_ec::short_weierstrass::SWCurveConfig;
    use ff::Field;
    use halo2curves::{secp256r1::Secp256r1Affine, t256::T256Affine};
    use merlin::Transcript;
    use pedersen::pedersen_config::PedersenConfig;
    use r1csipa::msm_function;
    use rand_core::OsRng;
    use rok::{Relation, RoK};

    use crate::{
        relations::rpa::{RelPA, RelPAParams, RelPAStatement, RelPAWitness},
        roks::pa_rok::PARoK,
        utils::{cdls_t256_to_t256, fp_to_fr, Fr},
    };

    #[test]
    fn test_pa_rok_cdls() {
        // Use CDLS's compile-time generators so commitments match the
        // generators the CDLS proof operates under.
        let g_ark = <t256::Config as SWCurveConfig>::GENERATOR;
        let h_ark = <t256::Config as PedersenConfig>::GENERATOR2;
        let g_halo: T256Affine = cdls_t256_to_t256(&g_ark);
        let h_halo: T256Affine = cdls_t256_to_t256(&h_ark);
        let ck = [g_halo, h_halo];

        // Witness: random A, B in Secp256r1, with T = A + B.
        let P0 = Secp256r1Affine::random(OsRng);
        let P1 = Secp256r1Affine::random(OsRng);
        let P2: Secp256r1Affine = (P0 + P1).into();

        // Random openings for each (x, y) coordinate.
        let rho0 = (Fr::random(OsRng), Fr::random(OsRng));
        let rho1 = (Fr::random(OsRng), Fr::random(OsRng));
        let rho2 = (Fr::random(OsRng), Fr::random(OsRng));

        // Commitments under (G, H) = (g_halo, h_halo) = CDLS's generators.
        let Cs = [
            (
                msm_function(&[fp_to_fr(&P0.x), rho0.0], &ck).into(),
                msm_function(&[fp_to_fr(&P0.y), rho0.1], &ck).into(),
            ),
            (
                msm_function(&[fp_to_fr(&P1.x), rho1.0], &ck).into(),
                msm_function(&[fp_to_fr(&P1.y), rho1.1], &ck).into(),
            ),
            (
                msm_function(&[fp_to_fr(&P2.x), rho2.0], &ck).into(),
                msm_function(&[fp_to_fr(&P2.y), rho2.1], &ck).into(),
            ),
        ];
        let rhos = [(rho0.0, rho0.1), (rho1.0, rho1.1), (rho2.0, rho2.1)];

        let pp = RelPAParams::new(ck[0], ck[1]);
        let x = RelPAStatement::new(Cs);
        let w = RelPAWitness::new([P0, P1, P2], rhos);

        let rs = RelPA::new(pp, x, Some(w));
        assert!(rs.in_relation().is_ok());

        let rok = PARoK::from_ck(&ck);

        let mut transcript_prover = Transcript::new(b"PA RoK CDLS Test");
        let (rt, proof) = rok.reduce(&mut transcript_prover, &rs, &mut OsRng).unwrap();
        let result = rt.in_relation();
        assert!(result.is_ok(), "reduce failed: {:?}", result);

        let mut transcript_verifier = Transcript::new(b"PA RoK CDLS Test");
        let result = rok.reduce_statement(&mut transcript_verifier, &rs, &proof);
        assert!(result.is_ok(), "verify failed: {:?}", result);
    }
}
