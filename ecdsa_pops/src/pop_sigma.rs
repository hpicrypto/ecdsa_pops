use halo2curves::{
    bls12381::{G1Affine, G1},
    t256::{T256Affine, T256},
    CurveExt,
};
use rok::{rok_compose, rok_compose_type, Nizk, RoK};

use crate::{
    errors::PopError,
    roks::{bls_to_tom::BlsToTomRoK, group_rok::GroupRoK, pa_rok::PARoK, sm_rok::SMRoK},
    RelECDSA,
};

/// A proof of possesion of a P256 signature using sigma protocols
pub struct PoPSigmaNizk {
    /// A Bls Generator for committing to the limbs of pk
    ck_bls: G1Affine,
    /// A Bls Generator for blinding
    ck_bls_blinding: G1Affine,
    /// A T256 generator for commiting to ECDSA pk Qx
    ck_t256: T256Affine,
    /// A common T256 generator for blinding
    ck_t256_blinding: T256Affine,
}

impl PoPSigmaNizk {
    /// Returns the BLS commitment generator.
    pub fn ck_bls(&self) -> &G1Affine {
        &self.ck_bls
    }

    /// Returns the BLS blinding generator.
    pub fn ck_bls_blinding(&self) -> &G1Affine {
        &self.ck_bls_blinding
    }

    /// Returns the T256 commitment generator.
    pub fn ck_t256(&self) -> &T256Affine {
        &self.ck_t256
    }

    /// Returns the T256 blinding generator.
    pub fn ck_t256_blinding(&self) -> &T256Affine {
        &self.ck_t256_blinding
    }
}

/// The type of the composed rok to prove proof-of-possession
type PoPSigmaComposedRoK = rok_compose_type!(
    PopError;
    // RelECDSA<BLS> ---> RelECDSA<T256> ---> (RelSM x RelPA) ---> (Trivial x Trivial)
    ((SMRoK x PARoK) o GroupRoK) o BlsToTomRoK
);

impl PoPSigmaNizk {
    /// Given a label, produces parameters for [PoPSigmaNizk]
    pub fn new(label: &str) -> Self {
        let hasher_bls = G1::hash_to_curve(&label);
        let ck_bls = hasher_bls(b"ck_bls").into();
        let ck_bls_blinding = hasher_bls(b"ck_bls_blinding").into();
        let hasher_t256 = T256::hash_to_curve(&label);
        let ck_t256 = hasher_t256(b"ck_t256").into();
        let ck_t256_blinding = hasher_t256(b"ck_t256_blinding").into();

        Self {
            ck_bls,
            ck_bls_blinding,
            ck_t256,
            ck_t256_blinding,
        }
    }

    /// Construct a [PoPSigmaNizk] with a caller-supplied T256 commitment key.
    ///
    /// Use this when the T256 generators must match a specific pair, e.g. the
    /// CDLS-side compile-time generators required by [SMRoK]'s WC scalar-mul proof.
    /// The BLS generators are still derived from `label` via hash-to-curve.
    pub fn new_with_t256_key(
        label: &str,
        ck_t256: T256Affine,
        ck_t256_blinding: T256Affine,
    ) -> Self {
        let hasher_bls = G1::hash_to_curve(&label);
        let ck_bls = hasher_bls(b"ck_bls").into();
        let ck_bls_blinding = hasher_bls(b"ck_bls_blinding").into();
        Self {
            ck_bls,
            ck_bls_blinding,
            ck_t256,
            ck_t256_blinding,
        }
    }

    /// Given a statement, specializes parameters and creates the composed rok
    fn get_rok(&self) -> PoPSigmaComposedRoK {
        // bls_to_tom_rok rok
        let ck_bls = [self.ck_bls, self.ck_bls_blinding];
        let ck_tom = [self.ck_t256, self.ck_t256_blinding];
        // the roks
        let bls_to_tom_rok = BlsToTomRoK::from_params(&ck_bls, &ck_tom);
        let group_rok = GroupRoK::from_ck(&ck_tom);
        let sm_rok = SMRoK::from_ck(&ck_tom);
        let pa_rok = PARoK::from_ck(&ck_tom);
        // return the composed RoK
        rok_compose!(
            PopError;
            // RelECDSA<BLS> ---> RelECDSA<T256> ---> (RelSM x RelPA) ---> (Trivial x Trivial)
            ((sm_rok x pa_rok) o group_rok) o bls_to_tom_rok
        )
    }
}

impl Nizk for PoPSigmaNizk {
    type Relation = RelECDSA<G1Affine, 2>;
    type Proof = <PoPSigmaComposedRoK as RoK>::Proof;
    type Error = PopError;

    fn label() -> String {
        PoPSigmaComposedRoK::label()
    }

    fn hash_statement(&self, r: &Self::Relation, transcript: &mut merlin::Transcript) {
        self.get_rok().hash_statement(r, transcript)
    }

    fn prove<R>(
        &self,
        transcript: &mut merlin::Transcript,
        r: &Self::Relation,
        rng: &mut R,
    ) -> Result<Self::Proof, Self::Error>
    where
        R: rand_core::RngCore + rand_core::CryptoRng,
    {
        self.get_rok().reduce(transcript, r, rng).map(|r| r.1)
    }

    fn verify(
        &self,
        transcript: &mut merlin::Transcript,
        r: &Self::Relation,
        proof: &Self::Proof,
    ) -> Result<(), Self::Error> {
        self.get_rok().reduce_statement(transcript, r, proof)?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {

    use ark_ec::short_weierstrass::SWCurveConfig;
    use halo2curves::bls12381::G1Affine;
    use merlin::Transcript;
    use rand_core::OsRng;
    use rok::{Nizk, Relation};

    use crate::utils::cdls_t256_to_t256;
    use crate::{
        relations::{recdsa::RelECDSA, tests::sample_random_ecdsa_instance_with_key},
        PoPSigmaNizk,
    };

    #[test]
    fn test_popsigma_nizk() {
        // CDLS fixes the generators
        let cdls_g = <t256::Config as SWCurveConfig>::GENERATOR;
        let cdls_h = <t256::Config as pedersen::pedersen_config::PedersenConfig>::GENERATOR2;
        let halo_g = cdls_t256_to_t256(&cdls_g);
        let halo_h = cdls_t256_to_t256(&cdls_h);

        let mut nizk = PoPSigmaNizk::new("test popsigma");
        nizk.ck_t256 = halo_g;
        nizk.ck_t256_blinding = halo_h;

        let mut r = sample_random_ecdsa_instance_with_key::<G1Affine, 2>(
            [nizk.ck_bls, nizk.ck_bls],
            nizk.ck_bls_blinding,
        );
        assert!(r.in_relation().is_ok());

        let mut transcript_prover = Transcript::new(b"pop sigma proof");
        let proof = nizk.prove(&mut transcript_prover, &r, &mut OsRng).unwrap();
        let bytes = bincode::serialize(&proof).unwrap();
        println!("proof size: {} bytes", bytes.len());

        let r_verifier = RelECDSA::new(r.params().clone(), r.statement().clone(), None);
        let mut transcript_verifier = Transcript::new(b"pop sigma proof");
        let result = nizk.verify(&mut transcript_verifier, &r_verifier, &proof);
        assert!(result.is_ok(), "nizk failed: {:?}", result);
    }
}
