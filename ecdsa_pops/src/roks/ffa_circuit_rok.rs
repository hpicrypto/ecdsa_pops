//! [RoK] reducing [RelCSchnorrCompact] -> [RelTrivial] for the FFA case.
//!
//! The RoK proves that the compact commitment opens to P-256 points `Q, R`
//! and blinding factors satisfying `T = c * R + Q` in the Midnight FFA circuit.

use ark_std::{end_timer, start_timer};
use ff::{Field, PrimeField};
use halo2curves::{
    bls12381::{Fq as HaloBlsBase, G1Affine},
    secp256r1::Secp256r1Affine,
    CurveAffine,
};
use merlin::Transcript;
use midnight_curves::{
    p256::{affine_from_xy, Fp as MidnightP256Base, P256 as MidnightP256},
    Bls12, CurveAffine as MidnightCurveAffine, Fp as MidnightBlsBase, Fq as MidnightFq,
    G1Affine as MidnightG1Affine,
};
use midnight_proofs::{
    plonk::commit_to_instances,
    poly::kzg::{params::ParamsKZG, KZGCommitmentScheme},
};
#[cfg(debug_assertions)]
use midnight_zk_stdlib::Relation as MidnightRelation;
use midnight_zk_stdlib::{MidnightPK, MidnightVK};
use pop_circuit_ffa::{EcdsaPoPP256, B_FACTORS};
use r1csipa::TranscriptProtocol;
use rok::{RelTrivial, Relation, RoK};

use crate::{
    errors::PopError,
    relations::rcschnorr_compact::{
        RelCSchnorrCompact, RelCSchnorrCompactParams, RelCSchnorrCompactStatement,
        RelCSchnorrCompactWitness,
    },
    utils::Fq,
};

// limbs to represent elements of P256 base field
const L: usize = 2;
// number of blinding factors for committed input
const B: usize = B_FACTORS;
// total number of elements in committed input
const COMMITTED_INPUTS_LEN: usize = 2 * L + B;

/// Circuit RoK parameters and proving material for the Midnight FFA circuit.
#[derive(Clone)]
pub struct FFACircuitRoK<const NB_BITS_C: usize> {
    /// the srs containing the lagrange-based Pedersen key
    pub(crate) srs: ParamsKZG<Bls12>,
    /// circuit verification key
    pub(crate) vk: MidnightVK,
    /// circuit proving key
    pub(crate) pk: MidnightPK<EcdsaPoPP256<NB_BITS_C>>,
}

impl<const NB_BITS_C: usize> FFACircuitRoK<NB_BITS_C> {
    /// Constructs [FFACircuitRoK] from its SRS, verification key, and proving key.
    pub fn from_parts(
        srs: ParamsKZG<Bls12>,
        vk: MidnightVK,
        pk: MidnightPK<EcdsaPoPP256<NB_BITS_C>>,
    ) -> Self {
        Self { srs, vk, pk }
    }

    fn relation(&self) -> EcdsaPoPP256<NB_BITS_C> {
        EcdsaPoPP256
    }

    #[cfg(test)]
    pub(crate) fn setup_for_test() -> Self {
        use std::path::Path;

        use midnight_zk_stdlib::utils::plonk_api::srs_for_test;

        let relation = EcdsaPoPP256::<NB_BITS_C>;
        let k = midnight_zk_stdlib::cost_model(&relation, None).k;
        let asset_srs_dir = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("workspace root")
            .join("pop_circuit_ffa")
            .join("examples")
            .join("assets");
        std::env::set_var("SRS_DIR", asset_srs_dir);
        let srs = srs_for_test(&relation, Some(k));
        let vk = midnight_zk_stdlib::setup_vk(&srs, &relation);
        let pk = midnight_zk_stdlib::setup_pk(&relation, &vk);
        Self { srs, vk, pk }
    }

    /// Returns the compact commitment parameters induced by this circuit SRS/VK.
    ///
    /// The FFA circuit committed-input:
    /// `Q.x_low, Q.x_high, R.x_low, R.x_high, rho[0..8]`.
    pub(crate) fn ck_from_srs(&self) -> Result<RelCSchnorrCompactParams<G1Affine, L, B>, PopError> {
        if self.vk.k() != self.pk.k() {
            return Err(PopError::RoKError(
                Self::label() + ": proving and verification keys use different k",
            ));
        }

        // HACK: get the appropriate generators from the commitment keys
        // essentially committing to e_i (0 everywhere except i-th position where it is 1)
        // These are fixed so we can change this
        let generators = (0..COMMITTED_INPUTS_LEN)
            .map(|i| {
                let mut instances = vec![MidnightFq::ZERO; COMMITTED_INPUTS_LEN];
                instances[i] = MidnightFq::ONE;
                let commitment = commit_to_instances::<MidnightFq, KZGCommitmentScheme<_>>(
                    &self.srs,
                    self.vk.vk().get_domain(),
                    &instances,
                )
                .into_point()
                .into();
                midnight_g1_to_halo(&commitment)
            })
            .collect::<Result<Vec<_>, _>>()?;

        Ok(RelCSchnorrCompactParams {
            ck_Q: generators[0..2].try_into()?,
            ck_R: generators[2..4].try_into()?,
            h: generators[4..12].try_into()?,
        })
    }

    fn instance(
        statement: &RelCSchnorrCompactStatement<G1Affine, L>,
    ) -> Result<(MidnightP256, u128), PopError> {
        Ok((
            p256_to_midnight(&statement.T)?,
            challenge_to_u128::<NB_BITS_C>(&statement.c)?,
        ))
    }

    fn witness(
        witness: &RelCSchnorrCompactWitness<G1Affine, L, B>,
    ) -> Result<(MidnightP256, MidnightP256, [MidnightFq; B]), PopError> {
        Ok((
            p256_to_midnight(&witness.Q)?,
            p256_to_midnight(&witness.R)?,
            witness.rho.map(bls_scalar_to_midnight),
        ))
    }
}

impl<const NB_BITS_C: usize> RoK for FFACircuitRoK<NB_BITS_C> {
    type RelationSource = RelCSchnorrCompact<G1Affine, L, B>;
    type RelationTarget = RelTrivial<Self::Error>;
    type Proof = Vec<u8>;
    type Error = PopError;

    fn hash_statement(&self, rs: &Self::RelationSource, transcript: &mut Transcript) {
        rs.params().ck_Q.iter().enumerate().for_each(|(i, g)| {
            transcript.append_u64(b"ffa ck_Q index", i as u64);
            transcript.append_point(b"ffa ck_Q", g);
        });
        rs.params().ck_R.iter().enumerate().for_each(|(i, g)| {
            transcript.append_u64(b"ffa ck_R index", i as u64);
            transcript.append_point(b"ffa ck_R", g);
        });
        rs.params().h.iter().enumerate().for_each(|(i, h)| {
            transcript.append_u64(b"ffa h index", i as u64);
            transcript.append_point(b"ffa h", h);
        });
        transcript.append_point(b"C", &rs.statement().C);
        transcript.append_point(b"T", &rs.statement().T);
        transcript.append_scalar(b"c", &rs.statement().c);
    }

    fn label() -> String {
        "PoP: FFA circuit proof".into()
    }

    fn reduce<R>(
        &self,
        transcript: &mut Transcript,
        rs: &Self::RelationSource,
        rng: &mut R,
    ) -> Result<(Self::RelationTarget, Self::Proof), Self::Error>
    where
        R: rand_core::RngCore + rand_core::CryptoRng,
    {
        let t = start_timer!(|| "FFA Circuit RoK Prover");

        self.initialize(rs, transcript);

        let witness = rs
            .witness()
            .as_ref()
            .ok_or_else(|| PopError::MissingWitness(Self::RelationSource::label()))?;

        // convert the instance/witness to the types used in the circuit
        let instance = Self::instance(rs.statement())?;
        let witness = Self::witness(witness)?;
        let relation = self.relation();

        #[cfg(debug_assertions)]
        {
            let c_instance = EcdsaPoPP256::<NB_BITS_C>::format_committed_instances(&witness);
            let commitment = commit_to_instances::<MidnightFq, KZGCommitmentScheme<_>>(
                &self.srs,
                self.vk.vk().get_domain(),
                &c_instance,
            )
            .into_point()
            .into();
            if midnight_g1_to_halo(&commitment)? != rs.statement().C {
                return Err(PopError::RoKError(
                    Self::label() + ": witness committed inputs do not match source commitment",
                ));
            }
        }

        let proof = midnight_zk_stdlib::prove::<EcdsaPoPP256<NB_BITS_C>, blake2b_simd::State>(
            &self.srs, &self.pk, &relation, &instance, witness, rng,
        )
        .map_err(|e| PopError::RoKError(format!("{}: proving failed: {:?}", Self::label(), e)))?;

        transcript.append_message(b"ffa circuit proof", &proof);

        end_timer!(t);
        Ok((RelTrivial::default(), proof))
    }

    fn reduce_statement(
        &self,
        transcript: &mut Transcript,
        rs: &Self::RelationSource,
        proof: &Self::Proof,
    ) -> Result<Self::RelationTarget, Self::Error> {
        let t = start_timer!(|| "FFA Circuit RoK Verifier");

        self.initialize(rs, transcript);

        let instance = Self::instance(rs.statement())?;
        let commitment = halo_g1_to_midnight(&rs.statement().C)?;

        midnight_zk_stdlib::verify::<EcdsaPoPP256<NB_BITS_C>, blake2b_simd::State>(
            &self.srs.verifier_params(),
            &self.vk,
            &instance,
            Some(commitment),
            proof,
        )
        .map_err(|e| {
            PopError::RoKError(format!("{}: verification failed: {:?}", Self::label(), e))
        })?;

        transcript.append_message(b"ffa circuit proof", proof);

        end_timer!(t);
        Ok(RelTrivial::default())
    }
}

fn bls_scalar_to_midnight(scalar: <G1Affine as CurveAffine>::ScalarExt) -> MidnightFq {
    MidnightFq::from_repr(scalar.to_repr().into()).expect("same BLS12-381 scalar field")
}

fn challenge_to_u128<const NB_BITS_C: usize>(c: &Fq) -> Result<u128, PopError> {
    if NB_BITS_C > 128 {
        return Err(PopError::RoKError(
            "PoP: FFA circuit proof: NB_BITS_C cannot exceed 128".into(),
        ));
    }

    let bytes: [u8; 32] = c.to_repr().into();
    if bytes[16..].iter().any(|b| *b != 0) {
        return Err(PopError::RoKError(
            "PoP: FFA circuit proof: challenge does not fit in u128".into(),
        ));
    }

    let c_u128 = u128::from_le_bytes(bytes[0..16].try_into()?);
    if NB_BITS_C < 128 && c_u128 >= (1u128 << NB_BITS_C) {
        return Err(PopError::RoKError(
            "PoP: FFA circuit proof: challenge exceeds the circuit bit length".into(),
        ));
    }
    Ok(c_u128)
}

fn p256_base_to_midnight(x: &<Secp256r1Affine as CurveAffine>::Base) -> MidnightP256Base {
    let mut bytes: [u8; 32] = x.to_repr().into();
    bytes.reverse();
    MidnightP256Base::from_repr(bytes.into()).expect("valid P-256 base field element")
}

fn p256_to_midnight(point: &Secp256r1Affine) -> Result<MidnightP256, PopError> {
    let x = p256_base_to_midnight(&point.x);
    let y = p256_base_to_midnight(&point.y);
    let affine = affine_from_xy(x, y)
        .ok_or_else(|| PopError::RoKError("PoP: FFA circuit proof: invalid P-256 point".into()))?;
    Ok(affine.into())
}

fn halo_g1_to_midnight(point: &G1Affine) -> Result<MidnightG1Affine, PopError> {
    let coords = point.coordinates().into_option().ok_or_else(|| {
        PopError::RoKError("PoP: FFA circuit proof: identity BLS commitment".into())
    })?;
    let x = halo_bls_base_to_midnight(coords.x());
    let y = halo_bls_base_to_midnight(coords.y());
    MidnightG1Affine::from_xy(x, y).into_option().ok_or_else(|| {
        PopError::RoKError("PoP: FFA circuit proof: invalid BLS commitment encoding".into())
    })
}

fn midnight_g1_to_halo(point: &MidnightG1Affine) -> Result<G1Affine, PopError> {
    let coords = MidnightCurveAffine::coordinates(point).into_option().ok_or_else(|| {
        PopError::RoKError("PoP: FFA circuit proof: identity Midnight BLS commitment".into())
    })?;
    let x = midnight_bls_base_to_halo(coords.x());
    let y = midnight_bls_base_to_halo(coords.y());
    G1Affine::from_xy(x, y).into_option().ok_or_else(|| {
        PopError::RoKError("PoP: FFA circuit proof: invalid Midnight BLS commitment".into())
    })
}

fn halo_bls_base_to_midnight(x: &HaloBlsBase) -> MidnightBlsBase {
    let bytes: [u8; 48] = x.to_repr().into();
    MidnightBlsBase::from_repr(bytes.into()).expect("same BLS12-381 base field")
}

fn midnight_bls_base_to_halo(x: &MidnightBlsBase) -> HaloBlsBase {
    let bytes: [u8; 48] = x.to_repr().as_ref().try_into().expect("48-byte repr");
    HaloBlsBase::from_repr(bytes.into()).expect("same BLS12-381 base field")
}

#[cfg(test)]
mod tests {
    use std::path::{Path, PathBuf};

    use ff::{Field, PrimeField};
    use halo2curves::{bls12381::G1Affine, group::Curve, secp256r1::Secp256r1Affine, CurveAffine};
    use merlin::Transcript;
    use midnight_zk_stdlib::utils::plonk_api::srs_for_test;
    use rand_core::{OsRng, RngCore};
    use rok::{Relation, RoK};

    use super::*;

    fn asset_srs_dir() -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("workspace root")
            .join("pop_circuit_ffa")
            .join("examples")
            .join("assets")
    }

    fn c_from_u128(c: u128) -> Fq {
        let mut bytes = [0u8; 32];
        bytes[0..16].copy_from_slice(&c.to_le_bytes());
        Fq::from_repr(bytes.into()).expect("bounded challenge is a P-256 scalar")
    }

    fn random_c<const NB_BITS_C: usize>() -> Fq {
        assert!(NB_BITS_C <= 128);

        let mut bytes = [0u8; 16];
        OsRng.fill_bytes(&mut bytes);
        let c = u128::from_le_bytes(bytes);
        let c = if NB_BITS_C == 128 {
            c
        } else {
            c & ((1u128 << NB_BITS_C) - 1)
        };
        c_from_u128(c)
    }

    fn test_ffa_circuit_rok_helper<const NB_BITS_C: usize>() {
        let relation = EcdsaPoPP256::<NB_BITS_C>;

        // sample the srs and the circuit parameters
        let k = midnight_zk_stdlib::cost_model(&relation, None).k;
        std::env::set_var("SRS_DIR", asset_srs_dir());
        let srs = srs_for_test(&relation, Some(k));
        let vk = midnight_zk_stdlib::setup_vk(&srs, &relation);
        let pk = midnight_zk_stdlib::setup_pk(&relation, &vk);
        let rok = FFACircuitRoK::<NB_BITS_C> { srs, vk, pk };

        let pp = rok.ck_from_srs().expect("compact params should derive");

        let c = random_c::<NB_BITS_C>();
        let R = Secp256r1Affine::random(OsRng);
        let Q = Secp256r1Affine::random(OsRng);
        let rho = std::array::from_fn(|_| <G1Affine as CurveAffine>::ScalarExt::random(OsRng));
        let C = RelCSchnorrCompact::<G1Affine, L, B>::create_commitment(
            &R, &Q, &rho, &pp.ck_R, &pp.ck_Q, &pp.h,
        );
        let T = ((R * c) + Q).to_affine();
        let x = RelCSchnorrCompactStatement::<G1Affine, L> { C, T, c };
        let w = RelCSchnorrCompactWitness::<G1Affine, L, B>::new(R, Q, rho);
        let rs = RelCSchnorrCompact::new(pp, x, Some(w));

        rs.in_relation().expect("source relation should be valid");

        let mut transcript_prover = Transcript::new(b"FFA Circuit RoK test");
        let (_rt, proof) = rok
            .reduce(&mut transcript_prover, &rs, &mut OsRng)
            .expect("proving should succeed");
        println!(
            "c of {} bits: k={} and |prf| = {}B",
            NB_BITS_C,
            k,
            proof.len()
        );

        let rs_verifier =
            RelCSchnorrCompact::new(rs.params().clone(), rs.statement().clone(), None);
        let mut transcript_verifier = Transcript::new(b"FFA Circuit RoK test");
        let result = rok.reduce_statement(&mut transcript_verifier, &rs_verifier, &proof);
        assert!(result.is_ok(), "reduce failed: {:?}", result);
    }

    #[test]
    fn test_ffa_circuit_rok_128_bit_challenge() {
        test_ffa_circuit_rok_helper::<128>();
        test_ffa_circuit_rok_helper::<96>();
    }
}
