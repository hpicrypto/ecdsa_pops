//! RelPedersenEq:
//!     - params: plain and compact pedersen commitment key
//!     - statement C_1, ..., C_L, C\in Curve
//!     - witness: (m1,r1,..,mn,rn,rc_1, ..., rc_k) in Curve::Scalar
//!     s.t. C_i = Commit(ck, mi; r_i,) and C = Commit(ck_compact, mi; rc_1,...,rc_k)

use ff::PrimeField;
use halo2curves::{group::Curve, secp256r1::Secp256r1Affine, CurveAffine};
use r1csipa::msm_function;
use rok::Relation;

use crate::errors::PopError;

#[derive(Debug, Clone)]
/// The Pedersen Equality [Relation]
/// L is the number of committed values and B is the number of blinding factors for the compact commitment
pub struct RelPedersenEq<C, const L: usize, const B: usize>
where
    C: CurveAffine,
    C::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    pp: RelPedersenEqParams<C, L, B>,
    x: RelPedersenEqStatement<C, L>,
    w: Option<RelPedersenEqWitness<C, L, B>>,
}

impl<C, const L: usize, const B: usize> RelPedersenEq<C, L, B>
where
    C: CurveAffine,
    C::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    // Helper function to create the plain commitments from the witness
    pub(crate) fn create_plain_commitments(&self) -> Result<[C; L], PopError> {
        let pp = self.pp.clone();
        let w = self
            .witness()
            .as_ref()
            .ok_or_else(|| PopError::MissingWitness(RelPedersenEq::<C, L, B>::label()))?;
        let result =
            w.m.iter()
                .zip(w.r_plain.iter())
                .map(|(&m, &r)| {
                    let bases = [pp.G_plain, pp.H_plain];
                    let scalars = [m, r];
                    msm_function(&scalars, &bases).to_affine()
                })
                .collect::<Vec<_>>()
                .try_into()
                .unwrap();
        Ok(result)
    }

    // Helper function to create the compact commitment from the witness
    pub(crate) fn create_compact_commitment(&self) -> Result<C, PopError> {
        let pp = self.pp.clone();
        let w = self
            .witness()
            .as_ref()
            .ok_or_else(|| PopError::MissingWitness(RelPedersenEq::<C, L, B>::label()))?;
        let mut bases = pp.Gs_compact.to_vec();
        bases.extend(pp.Hs_compact.as_slice());
        let mut scalars = w.m.to_vec();
        scalars.extend(w.r_compact.as_slice());
        Ok(msm_function(scalars.as_slice(), bases.as_slice()).to_affine())
    }
}

#[derive(Clone, Debug)]
/// Parameters of the Pedersen relation [RelPedersenEq]
pub struct RelPedersenEqParams<C, const L: usize, const B: usize>
where
    C: CurveAffine,
    C::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    /// commitment key
    pub(crate) G_plain: C,
    pub(crate) H_plain: C,
    pub(crate) Gs_compact: [C; L],
    pub(crate) Hs_compact: [C; B],
}

/// Public inputs of the Pedersen equality relation [RelPedersenEq]
#[derive(Clone, Debug)]
pub struct RelPedersenEqStatement<C, const L: usize>
where
    C: CurveAffine,
    C::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    /// Plain commitments
    pub(crate) C_plain: [C; L],
    /// Compact commitment
    pub(crate) C_compact: C,
}

/// Witness of the Pedersen equality relation [RelPedersenEq]
#[derive(Clone, Debug)]
pub struct RelPedersenEqWitness<C, const L: usize, const B: usize>
where
    C: CurveAffine,
    C::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    /// the commitment openings
    pub(crate) m: [C::ScalarExt; L],
    /// the plain pedersen randomness
    pub(crate) r_plain: [C::ScalarExt; L],
    /// the compact pedersen randomness
    pub(crate) r_compact: [C::ScalarExt; B],
}

impl<C, const L: usize, const B: usize> Relation for RelPedersenEq<C, L, B>
where
    C: CurveAffine,
    C::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    type Params = RelPedersenEqParams<C, L, B>;
    type Statement = RelPedersenEqStatement<C, L>;
    type Witness = RelPedersenEqWitness<C, L, B>;
    type Error = PopError;

    fn label() -> String {
        "Plain and Compact Pedersen Relation".into()
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

    /// Test whether (pp,x,w) is in the relation [RelPedersenEq]
    fn in_relation(&self) -> Result<(), PopError> {
        let computed_cs_plain = self.create_plain_commitments()?;
        let computed_c_compact = self.create_compact_commitment()?;

        let b_plain = computed_cs_plain
            .iter()
            .zip(self.x.C_plain.iter())
            .all(|(computed_C, C)| C == computed_C);
        let b_compact = computed_c_compact == self.x.C_compact;

        if b_plain && b_compact {
            Ok(())
        } else {
            Err(PopError::InvalidStatementWitness(Self::label()))
        }
    }
}
