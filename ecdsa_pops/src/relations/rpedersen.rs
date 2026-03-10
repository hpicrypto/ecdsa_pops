//! RelPedersen:
//!     - params: pedersen commitment key
//!     - statement C\in Curve
//!     - witness: (m1,..,mn,r) in Curve::Scalar
//!     s.t. C = Commit(ck, m1,..,mn; r)

use ff::PrimeField;
use halo2curves::{group::Curve, secp256r1::Secp256r1Affine, CurveAffine};
use r1csipa::msm_function;
use rok::Relation;

use crate::errors::PopError;

#[derive(Debug, Clone)]
/// The Pedersen [Relation]
pub struct RelPedersen<C>
where
    C: CurveAffine,
    C::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    pp: RelPedersenParams<C>,
    x: RelPedersenStatement<C>,
    w: Option<RelPedersenWitness<C>>,
}

impl<C> RelPedersen<C>
where
    C: CurveAffine,
    C::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    /// Helper function to reate the commitment
    pub(crate) fn create_commitment(
        pp: &RelPedersenParams<C>,
        w: &RelPedersenWitness<C>,
    ) -> Result<C, PopError> {
        Ok(msm_function(&w.m, &pp.ck).to_affine())
    }
}

#[derive(Clone, Debug)]
/// Parameters of the Pedersen relation [RelPedersen]
pub struct RelPedersenParams<C>
where
    C: CurveAffine,
    C::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    /// commitment key
    pub(crate) ck: Vec<C>,
}

/// Public inputs of the Pedersen relation [RelPedersen]
#[derive(Clone, Debug)]
pub struct RelPedersenStatement<C>
where
    C: CurveAffine,
    C::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    /// Commitment to Qx
    pub(crate) C: C,
}

/// Witness of the Pedersen relation [RelPedersen]
#[derive(Clone, Debug)]
pub struct RelPedersenWitness<C>
where
    C: CurveAffine,
    C::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    /// the commitment opening (including randomness)
    pub(crate) m: Vec<C::ScalarExt>,
}

impl<C> Relation for RelPedersen<C>
where
    C: CurveAffine,
    C::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    type Params = RelPedersenParams<C>;
    type Statement = RelPedersenStatement<C>;
    type Witness = RelPedersenWitness<C>;
    type Error = PopError;

    fn label() -> String {
        "Pedersen Relation".into()
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

    /// Test whether (pp,x,w) is in the relation [RelPedersen]
    fn in_relation(&self) -> Result<(), PopError> {
        let w = self.w.as_ref().ok_or(PopError::MissingWitness(Self::label()))?;
        if w.m.len() != self.params().ck.len() {
            return Err(PopError::InvalidStatementWitness(Self::label()));
        }

        // C = Commit(ck, m; m_last)
        let b = RelPedersen::<C>::create_commitment(&self.pp, w)? == self.x.C;
        if b {
            Ok(())
        } else {
            Err(PopError::InvalidStatementWitness(Self::label()))
        }
    }
}
