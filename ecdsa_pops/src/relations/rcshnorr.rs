//! RelCSchnorr:
//!     - params: pedersen commitment key in (Generic) Curve
//!     - statement T (in [Secp256r1Affine]), c (in [Fq]), C (in generic
//!       [CurveAffine])
//!     - witness R, Q (in [Secp256r1Affine]), rho (in generic C scalar field)
//!     s.t.
//!     1. CR = Commit(ck_R, R.x; rR), CR = Commit(ck_Q, Q.x; rQ),  where ck_R,
//!        ck_Q are
//!     Pedersen keys and the commitments to Q, R are in limbs.
//!     2. T = cR + Q (over [Secp256r1Affine]) where
//!
//! The relation captures the task of the sigma protocol verifier after running
//! a "committed" version of the Schnorr protocol (where the statement H=kG and
//! the first message R=rG are committed in some other curve).
//!
//! The relation is generic over some [CurveAffine] that defines the commitment
//! scheme and a constant L which defines the number of limbs needed to
//! represent [Secp256r1Affine] base elements in the generic curve's scalar
//! field

use ff::PrimeField;
use halo2curves::{group::Curve, secp256r1::Secp256r1Affine, CurveAffine};
use r1csipa::msm_function;
use rok::Relation;

use crate::{
    errors::PopError,
    utils::{fp_to_scalars, Fq},
};
#[derive(Debug, Clone)]
/// The Committed Schnorr Relation
///
///  - CCom is the curve where we commit to.
///
///  - L denotes the number of limbs to encode a coordinate of [Secp256r1Affine]
pub struct RelCSchnorr<CCom, const L: usize>
where
    CCom: CurveAffine,
    CCom::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    pp: RelCSchnorrParams<CCom, L>,
    x: RelCSchnorrStatement<CCom, L>,
    w: Option<RelCSchnorrWitness<CCom, L>>,
}

#[derive(Clone, Debug)]
/// Parameters of the relation [RelCSchnorr] which consist of a commitment key
pub struct RelCSchnorrParams<CCom, const L: usize>
where
    CCom: CurveAffine,
    CCom::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    pub(crate) ck_R: [CCom; L],
    pub(crate) ck_Q: [CCom; L],
    pub(crate) h: CCom,
}

/// Public inputs of the relation [RelCSchnorr]
#[derive(Clone, Debug)]
pub struct RelCSchnorrStatement<CCom, const L: usize>
where
    CCom: CurveAffine,
    CCom::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    /// Commitment to Rx
    pub(crate) CR: [CCom; L],
    /// Commitment to Qx
    pub(crate) CQ: [CCom; L],
    /// A public [Secp256r1Affine] point T
    pub(crate) T: Secp256r1Affine,
    /// The derived challenge in [Fq]
    pub(crate) c: Fq,
}

impl<CCom, const L: usize> RelCSchnorrStatement<CCom, L>
where
    CCom: CurveAffine,
    CCom::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    /// Create a [RelCSchnorrStatement] from parts
    #[allow(dead_code)]
    pub(crate) fn new(CQ: [CCom; L], CR: [CCom; L], T: Secp256r1Affine, c: Fq) -> Self {
        RelCSchnorrStatement { CQ, CR, T, c }
    }
}

/// Witness of the relation [RelCSchnorr]
#[derive(Clone, Debug)]
pub struct RelCSchnorrWitness<CCom, const L: usize>
where
    CCom: CurveAffine,
    CCom::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    pub(crate) R: Secp256r1Affine,
    pub(crate) Q: Secp256r1Affine,
    pub(crate) rhoR: [CCom::ScalarExt; L],
    pub(crate) rhoQ: [CCom::ScalarExt; L],
}

impl<CCom, const L: usize> RelCSchnorrWitness<CCom, L>
where
    CCom: CurveAffine,
    CCom::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    #[allow(dead_code)]
    /// Create [RelCSchnorrWitness] from parts
    pub(crate) fn new(
        R: Secp256r1Affine,
        Q: Secp256r1Affine,
        rhoR: [CCom::ScalarExt; L],
        rhoQ: [CCom::ScalarExt; L],
    ) -> Self {
        RelCSchnorrWitness { R, Q, rhoQ, rhoR }
    }
}

impl<CCom, const L: usize> RelCSchnorr<CCom, L>
where
    CCom: CurveAffine,
    CCom::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    // create the commitments to Q or R
    pub(crate) fn create_commitments(
        P: &Secp256r1Affine,
        rho: &[CCom::ScalarExt; L],
        ck_G: &[CCom; L],
        h: &CCom,
    ) -> [CCom; L] {
        let limbs = fp_to_scalars::<CCom, L>(&P.x).unwrap().to_vec();
        let scalars = limbs.iter().zip(rho).map(|(q, r)| vec![*q, *r]).collect::<Vec<_>>();
        let bases = ck_G.iter().map(|g| vec![*g, *h]).collect::<Vec<_>>();
        scalars
            .iter()
            .zip(bases.iter())
            .map(|(scalars, bases)| msm_function(scalars, bases).to_affine())
            .collect::<Vec<_>>()
            .try_into()
            .unwrap()
    }
}

impl<CCom, const L: usize> Relation for RelCSchnorr<CCom, L>
where
    CCom: CurveAffine,
    CCom::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    type Params = RelCSchnorrParams<CCom, L>;
    type Statement = RelCSchnorrStatement<CCom, L>;
    type Witness = RelCSchnorrWitness<CCom, L>;
    type Error = PopError;

    fn label() -> String {
        format!("CSchnorr relation with {} limbs", L)
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
        let CQ =
            RelCSchnorr::<CCom, L>::create_commitments(&w.Q, &w.rhoQ, &self.pp.ck_Q, &self.pp.h);
        let CR =
            RelCSchnorr::<CCom, L>::create_commitments(&w.R, &w.rhoR, &self.pp.ck_R, &self.pp.h);

        // 1. CR = Commit(ck, R.x; r) and CQ = Commit(ck, Q.x; r)
        let bR = self.x.CR.iter().zip(CR.iter()).all(|(C, C_computed)| C == C_computed);
        let bQ = self.x.CQ.iter().zip(CQ.iter()).all(|(C, C_computed)| C == C_computed);

        // 2. T = cR + Q
        let b2 = self.x.T == ((w.R * self.x.c) + w.Q).into();
        if bR && bQ && b2 {
            Ok(())
        } else {
            Err(PopError::InvalidStatementWitness(Self::label()))
        }
    }
}
