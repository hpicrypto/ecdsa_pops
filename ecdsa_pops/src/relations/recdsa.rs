//! RelEcdsa:
//!     - params: pedersen commitment key in (Generic) Curve
//!     - statement C_pk\in Curve, m, K\in P256
//!     - witness: pk\in P256, z in P256::Scalar, rho\in Curve::Scalar
//!     s.t.
//!     1. C_pk_i = Commit(ck, pk.x_i; r_i) where pk.x_i is the i-th limb of pk
//!     2. sigma=(K,z) is a valid ECDSA signature on m w.r.t. pk (or -pk)

use ff::PrimeField;
use halo2curves::{group::Curve, secp256r1::Secp256r1Affine, CurveAffine};
use r1csipa::msm_function;
use rok::Relation;

use crate::{
    errors::PopError,
    utils::{
        ecdsa::{ECDSASignatureConverted, ECDSA},
        fp_to_scalars, Fq,
    },
};

#[derive(Debug, Clone)]
/// The ECDSA [Relation]
///
/// - CCom is the [CurveAffine] where we commit to.
/// - L is the number of limbs needed to decompose a P256 base element to CCom::Scalar field elements
pub struct RelECDSA<CCom, const L: usize>
where
    CCom: CurveAffine,
    CCom::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    pp: RelECDSAParams<CCom, L>,
    x: RelECDSAStatement<CCom, L>,
    w: Option<RelECDSAWitness<CCom, L>>,
}

impl<CCom, const L: usize> RelECDSA<CCom, L>
where
    CCom: CurveAffine,
    CCom::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    /// Helper function that creates the commitment to the i-th limb
    pub fn create_commitment(
        pp: &RelECDSAParams<CCom, L>,
        w: &RelECDSAWitness<CCom, L>,
        i: usize,
    ) -> Result<CCom, PopError> {
        // Q.x as limbs
        let limbs = fp_to_scalars::<CCom, L>(&w.Q.x).unwrap();

        // compute commitment
        let bases = [pp.Gs[i], pp.H];
        let scalars = [limbs[i], w.rho[i]];
        Ok(msm_function(&scalars, &bases).to_affine())
    }
}

#[derive(Clone, Debug)]
/// Parameters of the relation [RelECDSA]
///
/// L is the number of limbs needed to represent the public key coordinate
pub struct RelECDSAParams<CCom, const L: usize>
where
    CCom: CurveAffine,
    CCom::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    /// Generators for committing to limbs
    Gs: [CCom; L],
    /// Generator for blinding commitments (common for all)
    H: CCom,
    /// ECDSA Parameters
    ecdsa: ECDSA,
}

impl<CCom, const L: usize> RelECDSAParams<CCom, L>
where
    CCom: CurveAffine,
    CCom::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    /// Create a [RelECDSAStatement] from parts
    pub fn new(Gs: [CCom; L], H: CCom, ecdsa: ECDSA) -> Self {
        RelECDSAParams { Gs, H, ecdsa }
    }

    /// Returns the limb commitment generators.
    pub fn gs(&self) -> &[CCom; L] {
        &self.Gs
    }

    /// Returns the shared blinding generator.
    pub fn h(&self) -> &CCom {
        &self.H
    }

    /// Returns the ECDSA parameters.
    pub fn ecdsa(&self) -> &ECDSA {
        &self.ecdsa
    }
}

/// Public inputs of the relation [RelECDSA]
#[derive(Clone, Debug)]
pub struct RelECDSAStatement<CCom, const L: usize>
where
    CCom: CurveAffine,
    CCom::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    /// L commitments to Qx, each corresponding to a limb
    C: [CCom; L],
    /// Signature part K
    K: Secp256r1Affine,
    /// A message in [Fq]
    m: Fq,
}

impl<CCom, const L: usize> RelECDSAStatement<CCom, L>
where
    CCom: CurveAffine,
    CCom::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    /// Create a [RelECDSAStatement] from parts
    pub fn new(C: [CCom; L], m: Fq, K: Secp256r1Affine) -> Self {
        RelECDSAStatement { C, m, K }
    }

    /// Returns the commitments to the limbs of Qx.
    pub fn c(&self) -> &[CCom; L] {
        &self.C
    }

    /// Returns the signature component K.
    pub fn k(&self) -> &Secp256r1Affine {
        &self.K
    }

    /// Returns the message field element.
    pub fn m(&self) -> &Fq {
        &self.m
    }
}

/// Witness of the relation [RelECDSA]
///
/// L is the number of limbs needed to represent the public key coordinate
#[derive(Clone, Debug)]
pub struct RelECDSAWitness<CCom, const L: usize>
where
    CCom: CurveAffine,
    CCom::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    /// the [ECDSA] public key
    Q: Secp256r1Affine,
    /// the hidden signature part
    z: Fq,
    /// the commitment openings, one per commitment
    rho: [CCom::ScalarExt; L],
}

impl<CCom, const L: usize> RelECDSAWitness<CCom, L>
where
    CCom: CurveAffine,
    CCom::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    /// Create [RelECDSAWitness] from parts
    pub fn new(Q: Secp256r1Affine, z: Fq, rho: [CCom::ScalarExt; L]) -> Self {
        RelECDSAWitness { Q, z, rho }
    }

    /// Returns the ECDSA public key.
    pub fn q(&self) -> &Secp256r1Affine {
        &self.Q
    }

    /// Returns the hidden signature component.
    pub fn z(&self) -> &Fq {
        &self.z
    }

    /// Returns the commitment opening randomness values.
    pub fn rho(&self) -> &[CCom::ScalarExt; L] {
        &self.rho
    }
}

impl<CCom, const L: usize> Relation for RelECDSA<CCom, L>
where
    CCom: CurveAffine,
    CCom::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    type Params = RelECDSAParams<CCom, L>;
    type Statement = RelECDSAStatement<CCom, L>;
    type Witness = RelECDSAWitness<CCom, L>;
    type Error = PopError;

    fn label() -> String {
        format!("ECDSA Relation with {} limbs", L)
    }

    fn params(&self) -> &Self::Params {
        &self.pp
    }

    fn statement(&self) -> &Self::Statement {
        &self.x
    }

    fn witness(&self) -> &Option<Self::Witness> {
        &self.w
    }

    fn new(pp: Self::Params, x: Self::Statement, w: Option<Self::Witness>) -> Self {
        Self { pp, x, w }
    }

    /// Test whether (pp,x,w) is in the relation
    fn in_relation(&self) -> Result<(), PopError> {
        let w = self.w.as_ref().ok_or(PopError::MissingWitness(Self::label()))?;

        // 1. C_i = Commit(ck, Q.x_i; rho_i) for all i
        let b1 =
            self.x.C.iter().enumerate().all(|(i, C)| {
                RelECDSA::<CCom, L>::create_commitment(&self.pp, w, i).unwrap() == *C
            });

        // 2. ECDSA signature verifies
        let sigma = ECDSASignatureConverted {
            K: self.statement().K,
            z: w.z,
        };
        let b2 = self.pp.ecdsa.verify_prehashed_converted(&w.Q, &self.x.m, &sigma).is_ok();
        if b1 && b2 {
            Ok(())
        } else {
            Err(PopError::InvalidStatementWitness(Self::label()))
        }
    }
}
