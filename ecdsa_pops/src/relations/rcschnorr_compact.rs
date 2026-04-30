//! RelCSchnorrCompact:
//!
//! The same as [`RelCschnor`] but using a compact commitment to commit to Q and
//! R
//!
//!     - params: pedersen commitment key in (Generic) Curve
//!     - statement T (in [Secp256r1Affine]), c (in [Fq]), C (in generic
//!       [CurveAffine])
//!     - witness R, Q (in [Secp256r1Affine]), rho (in generic C scalar field)
//!     s.t.
//!     1. C = Commit(ck, R.x, Q.x; r1,...,rb)
//!     2. T = cR + Q (over [Secp256r1Affine]) where

use ff::PrimeField;
use halo2curves::{group::Curve, secp256r1::Secp256r1Affine, CurveAffine};
use r1csipa::msm_function;
use rok::Relation;

use crate::{
    errors::PopError,
    utils::{fp_to_scalars, Fq},
};
#[derive(Debug, Clone)]
/// The Committed Schnorr Relation with compact commitments
///
///  - CCom is the curve where we commit to.
///
///  - L denotes the number of limbs to encode a coordinate of [Secp256r1Affine]
///  - B denotes the number of blinding factors used
pub struct RelCSchnorrCompact<CCom, const L: usize, const B: usize>
where
    CCom: CurveAffine,
    CCom::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    pp: RelCSchnorrCompactParams<CCom, L, B>,
    x: RelCSchnorrCompactStatement<CCom, L>,
    w: Option<RelCSchnorrCompactWitness<CCom, L, B>>,
}

#[derive(Clone, Debug)]
/// Parameters of the relation [RelCSchnorr] which consist of a commitment key
pub struct RelCSchnorrCompactParams<CCom, const L: usize, const B: usize>
where
    CCom: CurveAffine,
    CCom::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    pub(crate) ck_R: [CCom; L],
    pub(crate) ck_Q: [CCom; L],
    pub(crate) h: [CCom; B],
}

/// Public inputs of the relation [RelCSchnorr]
#[derive(Clone, Debug)]
pub struct RelCSchnorrCompactStatement<CCom, const L: usize>
where
    CCom: CurveAffine,
    CCom::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    /// Commitment
    pub(crate) C: CCom,
    /// A public [Secp256r1Affine] point T
    pub(crate) T: Secp256r1Affine,
    /// The derived challenge in [Fq]
    pub(crate) c: Fq,
}

impl<CCom, const L: usize> RelCSchnorrCompactStatement<CCom, L>
where
    CCom: CurveAffine,
    CCom::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    /// Create a [RelCSchnorrStatement] from parts
    #[allow(dead_code)]
    pub(crate) fn new(C: CCom, T: Secp256r1Affine, c: Fq) -> Self {
        RelCSchnorrCompactStatement { C, T, c }
    }
}

/// Witness of the relation [RelCSchnorr]
#[derive(Clone, Debug)]
pub struct RelCSchnorrCompactWitness<CCom, const L: usize, const B: usize>
where
    CCom: CurveAffine,
    CCom::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    pub(crate) R: Secp256r1Affine,
    pub(crate) Q: Secp256r1Affine,
    pub(crate) rho: [CCom::ScalarExt; B],
}

impl<CCom, const L: usize, const B: usize> RelCSchnorrCompactWitness<CCom, L, B>
where
    CCom: CurveAffine,
    CCom::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    #[allow(dead_code)]
    /// Create [RelCSchnorrWitness] from parts
    pub(crate) fn new(R: Secp256r1Affine, Q: Secp256r1Affine, rho: [CCom::ScalarExt; B]) -> Self {
        RelCSchnorrCompactWitness { R, Q, rho }
    }
}

impl<CCom, const L: usize, const B: usize> RelCSchnorrCompact<CCom, L, B>
where
    CCom: CurveAffine,
    CCom::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    // create the commitment to Q or R
    pub(crate) fn create_commitment(
        R: &Secp256r1Affine,
        Q: &Secp256r1Affine,
        rho: &[CCom::ScalarExt; B],
        ck_R: &[CCom; L],
        ck_Q: &[CCom; L],
        h: &[CCom; B],
    ) -> CCom {
        let limbs_R = fp_to_scalars::<CCom, L>(&R.x).unwrap().to_vec();
        let limbs_Q = fp_to_scalars::<CCom, L>(&Q.x).unwrap().to_vec();
        let scalars = limbs_R
            .iter()
            .chain(limbs_Q.iter())
            .chain(rho.iter())
            .cloned()
            .collect::<Vec<_>>();
        let bases = ck_R.iter().chain(ck_Q.iter()).chain(h.iter()).cloned().collect::<Vec<_>>();
        msm_function(&scalars, &bases).to_affine()
    }
}

impl<CCom, const L: usize, const B: usize> Relation for RelCSchnorrCompact<CCom, L, B>
where
    CCom: CurveAffine,
    CCom::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    type Params = RelCSchnorrCompactParams<CCom, L, B>;
    type Statement = RelCSchnorrCompactStatement<CCom, L>;
    type Witness = RelCSchnorrCompactWitness<CCom, L, B>;
    type Error = PopError;

    fn label() -> String {
        format!(
            "CSchnorr compact relation with {} limbs and {} blinding factors",
            L, B
        )
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

    fn in_relation(&self) -> Result<(), PopError> {
        let w = self.w.as_ref().ok_or(PopError::MissingWitness(Self::label()))?;

        // commitments to Q and R
        let C = RelCSchnorrCompact::<CCom, L, B>::create_commitment(
            &w.R,
            &w.Q,
            &w.rho,
            &self.pp.ck_R,
            &self.pp.ck_Q,
            &self.pp.h,
        );

        // 1. C = Commit(ck, R.x, Q.x; r)
        let b1 = C == self.statement().C;

        // 2. T = cR + Q
        let b2 = self.x.T == ((w.R * self.x.c) + w.Q).into();
        if b1 && b2 {
            Ok(())
        } else {
            Err(PopError::InvalidStatementWitness(Self::label()))
        }
    }
}
