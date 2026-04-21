//! RelSM:
//!     - params: pedersen commitment key in T256 Curve
//!     - statement Cx,Cy \in T256 Curve, G \in P256 Curve
//!     - witness: H \in P256 Curve, z \in P256::Scalar rhox, rhoy
//!     s.t.
//!     1. Cx = Commit(ck, Hx; rhox)
//!     2. Cy = Commit(ck, Hy; rhoy)
//!     3. zG = P

use halo2curves::{
    secp256r1::{Fq, Secp256r1Affine},
    t256::T256Affine,
    CurveAffine,
};
use r1csipa::msm_function;
use rok::Relation;

use crate::{errors::PopError, utils::fp_to_fr};

#[derive(Debug, Clone)]
/// The SM [Relation]
pub struct RelSM {
    pp: RelSMParams,
    x: RelSMStatement,
    w: Option<RelSMWitness>,
}

#[derive(Clone, Debug)]
/// Parameters of the relation [RelSM]
pub struct RelSMParams {
    /// Generators for committing to limbs
    G: T256Affine,
    /// Generator for blinding commitments (common for all)
    H: T256Affine,
}

impl RelSMParams {
    /// Create [RelSMParams] from parts
    pub(crate) fn new(G: T256Affine, H: T256Affine) -> Self {
        RelSMParams { G, H }
    }

    /// Returns the commitment generator.
    pub(crate) fn g(&self) -> &T256Affine {
        &self.G
    }

    /// Returns the blinding generator.
    pub(crate) fn h(&self) -> &T256Affine {
        &self.H
    }
}

/// Public statement of the relation [RelPA]
#[derive(Clone, Debug)]
pub struct RelSMStatement {
    /// Commitments to the point H
    C: (T256Affine, T256Affine),
    /// The public point G
    G: Secp256r1Affine,
}

impl RelSMStatement {
    /// Create a [RelSMStatement] from parts
    pub(crate) fn new(C: (T256Affine, T256Affine), G: Secp256r1Affine) -> Self {
        RelSMStatement { C, G }
    }

    /// Returns the point commitment.
    pub(crate) fn c(&self) -> &(T256Affine, T256Affine) {
        &self.C
    }

    /// Returns the generator.
    pub(crate) fn g(&self) -> &Secp256r1Affine {
        &self.G
    }
}

/// Witness of the relation [RelSM]
#[derive(Clone, Debug)]
pub struct RelSMWitness {
    /// the committed point
    P: Secp256r1Affine,
    /// the commitment randomness for the  point
    rho: (
        <T256Affine as CurveAffine>::ScalarExt,
        <T256Affine as CurveAffine>::ScalarExt,
    ),
    /// the scalar
    z: Fq,
}

impl RelSMWitness {
    /// Create [RelPAWitness] from parts
    pub(crate) fn new(
        P: Secp256r1Affine,
        rho: (
            <T256Affine as CurveAffine>::ScalarExt,
            <T256Affine as CurveAffine>::ScalarExt,
        ),
        z: Fq,
    ) -> Self {
        RelSMWitness { P, rho, z }
    }

    /// Returns the point.
    pub(crate) fn p(&self) -> &Secp256r1Affine {
        &self.P
    }

    /// Returns the commitment randomness.
    pub(crate) fn rho(
        &self,
    ) -> &(
        <T256Affine as CurveAffine>::ScalarExt,
        <T256Affine as CurveAffine>::ScalarExt,
    ) {
        &self.rho
    }

    /// Returns the scalar.
    pub(crate) fn scalar(&self) -> &Fq {
        &self.z
    }
}

impl Relation for RelSM {
    type Params = RelSMParams;
    type Statement = RelSMStatement;
    type Witness = RelSMWitness;
    type Error = PopError;

    fn label() -> String {
        format!("Scalar multiplication over committed base")
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

        // 1. the commitment is correct
        let b1x = self.x.C.0
            == msm_function(&[fp_to_fr(&w.P.x), w.rho.0], &[self.pp.G, self.pp.H]).into();
        let b1y = self.x.C.1
            == msm_function(&[fp_to_fr(&w.P.y), w.rho.1], &[self.pp.G, self.pp.H]).into();
        let b1 = b1x && b1y;
        // 2. The points satisfy scalar multiplication
        let b2 = w.P == (self.x.G * w.z).into();
        if b1 && b2 {
            Ok(())
        } else {
            Err(PopError::InvalidStatementWitness(Self::label()))
        }
    }
}
