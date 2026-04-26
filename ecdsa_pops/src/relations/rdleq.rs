//! Equality of dlogs in different groups relation as described in [this paper](https://eprint.iacr.org/2024/265)
//!
//! RelDLEQ:
//!     - params: a pedersen commitment key in each group
//!     - statement C1 \in Curve1, C2 \in Curve2,
//!     - witness: m, r1, r2 in (0..2^bx, Curve::Scalar1, Curve::Scalar2
//!     s.t.
//!        C1 = Commit(ck1, m; r1)
//!        C2 = Commit(ck2, m; r2)

use ff::PrimeField;
use halo2curves::{secp256r1::Secp256r1Affine, CurveAffine};
use num_bigint::BigUint;
use r1csipa::msm_function;
use rok::Relation;

use crate::{circuit_native::utils::biguint_to_scalar, errors::PopError};

#[derive(Debug, Clone)]
/// The DLEQ [Relation]
///
/// C1 and C2 are the two groups where we commit to the same value
pub(crate) struct RelDLEQ<C1, C2>
where
    C1: CurveAffine,
    C1::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
    C2: CurveAffine,
    C2::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    pub(crate) pp: RelDLEQParams<C1, C2>,
    pub(crate) x: RelDLEQStatement<C1, C2>,
    pub(crate) w: Option<RelDLEQWitness<C1, C2>>,
}

impl<C1, C2> RelDLEQ<C1, C2>
where
    C1: CurveAffine,
    C1::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
    C2: CurveAffine,
    C2::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
}

#[derive(Clone, Debug)]
/// Parameters of the relation [RelDLEQ] which consist of two Pedersen
/// commitment keys, one for each group
pub(crate) struct RelDLEQParams<C1, C2>
where
    C1: CurveAffine,
    C1::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
    C2: CurveAffine,
    C2::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    /// commitment key in first group
    pub(crate) ck1: Vec<C1>,
    /// commitment key in second group
    pub(crate) ck2: Vec<C2>,
}

/// Public inputs of the relation [RelDLEQ]
#[derive(Clone, Debug)]
pub(crate) struct RelDLEQStatement<C1, C2>
where
    C1: CurveAffine,
    C1::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
    C2: CurveAffine,
    C2::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    /// Commitment to m in G1
    pub(crate) C1: C1,
    /// Commitment to m in G2
    pub(crate) C2: C2,
}

/// Witness of the relation [RelDLEQ]
#[derive(Clone, Debug)]
pub(crate) struct RelDLEQWitness<C1, C2>
where
    C1: CurveAffine,
    C1::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
    C2: CurveAffine,
    C2::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    /// the opening in m. We represent it as a [BigUint]
    pub(crate) m: BigUint,
    /// the randomness for creating the C1 commitment
    pub(crate) r1: C1::ScalarExt,
    /// the randomness for creating the C2 commitment
    pub(crate) r2: C2::ScalarExt,
}

impl<C1, C2> Relation for RelDLEQ<C1, C2>
where
    C1: CurveAffine,
    C1::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
    C2: CurveAffine,
    C2::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    type Params = RelDLEQParams<C1, C2>;
    type Statement = RelDLEQStatement<C1, C2>;
    type Witness = RelDLEQWitness<C1, C2>;
    type Error = PopError;

    fn label() -> String {
        "DLOG Equality Relation".into()
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

        if self.params().ck1.len() != 2 || self.params().ck2.len() != 2 {
            return Err(PopError::InvalidStatementWitness(Self::label()));
        }

        let m_in_1: C1::ScalarExt = biguint_to_scalar(&w.m);
        let m_in_2: C2::ScalarExt = biguint_to_scalar(&w.m);

        let bases_1 = self.params().ck1.clone();
        let scalars_1 = [m_in_1, w.r1];

        let bases_2 = self.params().ck2.clone();
        let scalars_2 = [m_in_2, w.r2];

        if msm_function(&scalars_1, &bases_1) == self.statement().C1.into()
            && msm_function(&scalars_2, &bases_2) == self.statement().C2.into()
        {
            Ok(())
        } else {
            Err(PopError::InvalidStatementWitness(Self::label()))
        }
    }
}
