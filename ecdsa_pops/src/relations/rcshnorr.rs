//! RelCSchnorr:
//!     - params: pedersen commitment key in (Generic) Curve
//!     - statement T (in [Secp256r1Affine]), c (in [Fq]) (of SEC_PARAM bytes),
//!       C (in generic [CurveAffine])
//!     - witness R, Q (in [Secp256r1Affine]), rho (in generic C scalar field)
//!     s.t.
//!     1. C = Commit(ck, R.x, Q.x; r) where ck is a Pedersen key  and Q.x, R.x
//!        encoded in Curve
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
///  - L denotes the number of limbs to encode a coordinate of [Secp256r1Affine]
pub struct RelCSchnorr<CCom, const SEC_PARAM: usize, const L: usize>
where
    CCom: CurveAffine,
    CCom::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    pp: RelCSchnorrParams<CCom>,
    x: RelCSchnorrStatement<CCom, SEC_PARAM>,
    w: Option<RelCSchnorrWitness<CCom>>,
}

impl<CCom, const SEC_PARAM: usize, const L: usize> RelCSchnorr<CCom, SEC_PARAM, L>
where
    CCom: CurveAffine,
    CCom::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    /// Helper function that create the commitment to the vector [Rx, Qx, rho]
    pub(crate) fn create_commitment(
        pp: &RelCSchnorrParams<CCom>,
        w: &RelCSchnorrWitness<CCom>,
    ) -> Result<CCom, PopError> {
        // we have two [Fp] elements of L limbs (Rx and Qx) and a blinding element
        let mut scalars = Vec::with_capacity(2 * L + 1);
        scalars.extend_from_slice(fp_to_scalars::<CCom, L>(&w.R.x)?.as_slice());
        scalars.extend_from_slice(fp_to_scalars::<CCom, L>(&w.Q.x)?.as_slice());
        scalars.push(w.rho);
        Ok(msm_function(&scalars, &pp.ck).to_affine())
    }
}

#[derive(Clone, Debug)]
/// Parameters of the relation [RelCSchnorr] which consist of a commitment key
pub struct RelCSchnorrParams<CCom>
where
    CCom: CurveAffine,
    CCom::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    pub(crate) ck: Vec<CCom>,
}

/// Public inputs of the relation [RelCSchnorr]
#[derive(Clone, Debug)]
pub struct RelCSchnorrStatement<CCom, const SEC_PARAM_BYTES: usize>
where
    CCom: CurveAffine,
    CCom::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    /// (Compact) Commitment to Rx, Qx with randomness rho
    pub(crate) C: CCom,
    /// A public [Secp256r1Affine] point T
    pub(crate) T: Secp256r1Affine,
    /// The derived challenge in [Fq]
    pub(crate) c: Fq,
}

impl<CCom, const SEC_PARAM_BYTES: usize> RelCSchnorrStatement<CCom, SEC_PARAM_BYTES>
where
    CCom: CurveAffine,
    CCom::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    /// Create a [RelCSchnorrStatement] from parts
    #[allow(dead_code)]
    pub(crate) fn new(C: CCom, T: Secp256r1Affine, c: Fq) -> Self {
        RelCSchnorrStatement { C, T, c }
    }
}

/// Witness of the relation [RelCSchnorr]
#[derive(Clone, Debug)]
pub struct RelCSchnorrWitness<CCom>
where
    CCom: CurveAffine,
    CCom::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    pub(crate) R: Secp256r1Affine,
    pub(crate) Q: Secp256r1Affine,
    pub(crate) rho: CCom::ScalarExt,
}

impl<CCom> RelCSchnorrWitness<CCom>
where
    CCom: CurveAffine,
    CCom::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    #[allow(dead_code)]
    /// Create [RelCSchnorrWitness] from parts
    pub(crate) fn new(R: Secp256r1Affine, Q: Secp256r1Affine, rho: CCom::ScalarExt) -> Self {
        RelCSchnorrWitness { R, Q, rho }
    }
}

impl<CCom, const SEC_PARAM: usize, const L: usize> Relation for RelCSchnorr<CCom, SEC_PARAM, L>
where
    CCom: CurveAffine,
    CCom::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    type Params = RelCSchnorrParams<CCom>;
    type Statement = RelCSchnorrStatement<CCom, SEC_PARAM>;
    type Witness = RelCSchnorrWitness<CCom>;
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

        // 1. C = Commit(ck, R.x, Q.x; r)
        let b1 = RelCSchnorr::<CCom, SEC_PARAM, L>::create_commitment(&self.pp, w)? == self.x.C;

        // 2. T = cR + Q
        let b2 = self.x.T == ((w.R * self.x.c) + w.Q).into();
        if b1 && b2 {
            Ok(())
        } else {
            Err(PopError::InvalidStatementWitness(Self::label()))
        }
    }
}
