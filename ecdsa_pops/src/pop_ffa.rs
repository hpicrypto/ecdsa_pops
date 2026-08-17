use halo2curves::{
    bls12381::{G1Affine, G1},
    CurveExt,
};
use rok::{rok_compose, rok_compose_type, Nizk, RoK};

use crate::{
    errors::PopError,
    relations::rcschnorr_compact::RelCSchnorrCompactParams,
    roks::{cschnorr_ffa_rok::CSchnorrFFARoK, cschnorr_rok::CSchnorrRoK},
    RelECDSA,
};

pub use crate::roks::ffa_circuit_rok::FFACircuitRoK;

/// A proof of possession of a P256 signature using the FFA circuit.
pub struct PoPFFANizk {
    /// A BLS generator for committing to the limbs of the public key.
    ck_bls: G1Affine,
    /// A BLS generator for blinding plain commitments.
    ck_bls_blinding: G1Affine,
    /// The composed reduction.
    rok: PoPFFAComposedRoK,
}

impl PoPFFANizk {
    /// Returns the BLS commitment generator.
    pub fn ck_bls(&self) -> &G1Affine {
        &self.ck_bls
    }

    /// Returns the BLS blinding generator.
    pub fn ck_bls_blinding(&self) -> &G1Affine {
        &self.ck_bls_blinding
    }

    /// Constructs [PoPFFANizk] from its parameter parts.
    pub fn from_parts(
        ck_bls: G1Affine,
        ck_bls_blinding: G1Affine,
        ffa_circuit_rok: FFACircuitRoK<128>,
    ) -> Result<Self, PopError> {
        let compact_params = ffa_circuit_rok.ck_from_srs()?;
        let rok = Self::compose_rok(ck_bls, ck_bls_blinding, compact_params, ffa_circuit_rok);
        Ok(Self {
            ck_bls,
            ck_bls_blinding,
            rok,
        })
    }

    /// Given a label, samples the plain BLS commitment parameters.
    pub fn plain_commitment_params(label: &str) -> (G1Affine, G1Affine) {
        let label = [label, ": BLS committed input parameters"].concat();
        let hasher_bls = G1::hash_to_curve(&label);
        (
            hasher_bls(b"ck_bls").into(),
            hasher_bls(b"ck_bls_blinding").into(),
        )
    }
}

type CSchnorrRoKG1128 = CSchnorrRoK<G1Affine, 16, 2>;
type FFACircuitRoK128 = FFACircuitRoK<128>;

/// The type of the composed RoK to prove proof-of-possession.
///
/// RelECDSA<BLS> -> RelCSchnorr<BLS> -> RelCSchnorrCompact<BLS> -> RelTrivial.
type PoPFFAComposedRoK = rok_compose_type!(
    PopError;
    (FFACircuitRoK128 o CSchnorrFFARoK) o CSchnorrRoKG1128
);

impl PoPFFANizk {
    /// Creates the composed RoK from its parameter parts.
    fn compose_rok(
        ck_bls: G1Affine,
        ck_bls_blinding: G1Affine,
        compact_params: RelCSchnorrCompactParams<G1Affine, 2, 8>,
        ffa_circuit_rok: FFACircuitRoK<128>,
    ) -> PoPFFAComposedRoK {
        let cschnorr_rok = CSchnorrRoK::<G1Affine, 16, 2> {
            G_R: [ck_bls; 2],
            G_Q: [ck_bls; 2],
            H: ck_bls_blinding,
        };

        let mut compact_gs = compact_params.ck_Q.to_vec();
        compact_gs.extend_from_slice(&compact_params.ck_R);

        let cschnorr_ffa_rok = CSchnorrFFARoK {
            G_plain: ck_bls,
            H_plain: ck_bls_blinding,
            Gs_compact: compact_gs.try_into().unwrap(),
            Hs_compact: compact_params.h,
        };

        rok_compose!(
            PopError;
            (ffa_circuit_rok o cschnorr_ffa_rok) o cschnorr_rok
        )
    }
}

impl Nizk for PoPFFANizk {
    type Relation = RelECDSA<G1Affine, 2>;
    type Proof = <PoPFFAComposedRoK as RoK>::Proof;
    type Error = PopError;

    fn label() -> String {
        <PoPFFAComposedRoK as RoK>::label()
    }

    fn hash_statement(&self, r: &Self::Relation, transcript: &mut merlin::Transcript) {
        Nizk::hash_statement(&self.rok, r, transcript)
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
        self.rok.reduce(transcript, r, rng).map(|r| r.1)
    }

    fn verify(
        &self,
        transcript: &mut merlin::Transcript,
        r: &Self::Relation,
        proof: &Self::Proof,
    ) -> Result<(), Self::Error> {
        self.rok.reduce_statement(transcript, r, proof)?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use halo2curves::bls12381::G1Affine;
    use merlin::Transcript;
    use rand_core::OsRng;
    use rok::{Nizk, Relation};

    use crate::{
        relations::{recdsa::RelECDSA, tests::sample_random_ecdsa_instance_with_key},
        roks::ffa_circuit_rok::FFACircuitRoK,
        PoPFFANizk,
    };

    #[test]
    fn test_popffa_nizk() {
        let label = "test popffa";
        let (ck_bls, ck_bls_blinding) = PoPFFANizk::plain_commitment_params(label);
        let ffa_circuit_rok = FFACircuitRoK::<128>::setup_for_test();
        let nizk = PoPFFANizk::from_parts(ck_bls, ck_bls_blinding, ffa_circuit_rok).unwrap();

        let mut r = sample_random_ecdsa_instance_with_key::<G1Affine, 2>(
            [*nizk.ck_bls(), *nizk.ck_bls()],
            *nizk.ck_bls_blinding(),
        );
        r.remove_cy();
        assert!(r.in_relation().is_ok());

        let mut transcript_prover = Transcript::new(b"pop ffa proof");
        let proof = nizk.prove(&mut transcript_prover, &r, &mut OsRng).unwrap();

        let bytes = bincode::serialize(&proof).unwrap();
        println!("proof size: {} bytes", bytes.len());

        let r_verifier = RelECDSA::new(r.params().clone(), r.statement().clone(), None);

        let mut transcript_verifier = Transcript::new(b"pop ffa proof");
        let result = nizk.verify(&mut transcript_verifier, &r_verifier, &proof);

        assert!(result.is_ok(), "nizk failed: {:?}", result);
    }
}
