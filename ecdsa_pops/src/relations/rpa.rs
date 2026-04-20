//! RelPA:
//!     - params: pedersen commitment key in T256 Curve
//!     - statement C1x, C2x, C3x, C1y, C2y, C3y \in T256 Curve
//!     - witness: P1, P2, P3 \in P256 Curve
//!                rho1x, rho2x, rho3x in P256 base field
//!                rho1y, rho2y, rho3y in P256 base field
//!     s.t.
//!     1. Cix = Commit(ck, Pi.x; rhoix)
//!     2. Ciy = Commit(ck, Pi.y; rhoiy)
//!     3. P1 + P2 = P3

use halo2curves::{secp256r1::Secp256r1Affine, t256::T256Affine, CurveAffine};
use r1csipa::msm_function;
use rok::Relation;

use crate::{errors::PopError, utils::fp_to_fr};

#[derive(Debug, Clone)]
/// The PA [Relation]
pub struct RelPA {
    pp: RelPAParams,
    x: RelPAStatement,
    w: Option<RelPAWitness>,
}

#[derive(Clone, Debug)]
/// Parameters of the relation [RelPA]
pub struct RelPAParams {
    /// Generators for committing to limbs
    G: T256Affine,
    /// Generator for blinding commitments (common for all)
    H: T256Affine,
}

impl RelPAParams {
    /// Create [RelPAParams] from parts
    pub fn new(G: T256Affine, H: T256Affine) -> Self {
        RelPAParams { G, H }
    }

    /// Returns the commitment generator.
    pub fn g(&self) -> &T256Affine {
        &self.G
    }

    /// Returns the blinding generator.
    pub fn h(&self) -> &T256Affine {
        &self.H
    }
}

/// Public statement of the relation [RelPA]
#[derive(Clone, Debug)]
pub struct RelPAStatement {
    /// Commitments to the points
    Cs: [(T256Affine, T256Affine); 3],
}

impl RelPAStatement {
    /// Create a [RelPAStatement] from parts
    pub fn new(Cs: [(T256Affine, T256Affine); 3]) -> Self {
        RelPAStatement { Cs }
    }

    /// Returns the ith commitment.
    pub fn c(&self, i: usize) -> Result<&(T256Affine, T256Affine), PopError> {
        if i < 3 {
            Ok(&self.Cs[i])
        } else {
            Err(PopError::IndexOutOfBounds(format!(
                "{} >= 3 in RelPAStatemen",
                3
            )))
        }
    }
}

/// Witness of the relation [RelPA]
#[derive(Clone, Debug)]
pub struct RelPAWitness {
    /// the points
    Ps: [Secp256r1Affine; 3],
    /// the commitment randomness for the  points
    rhos: [(
        <T256Affine as CurveAffine>::ScalarExt,
        <T256Affine as CurveAffine>::ScalarExt,
    ); 3],
}

impl RelPAWitness {
    /// Create [RelPAWitness] from parts
    pub fn new(
        Ps: [Secp256r1Affine; 3],
        rhos: [(
            <T256Affine as CurveAffine>::ScalarExt,
            <T256Affine as CurveAffine>::ScalarExt,
        ); 3],
    ) -> Self {
        RelPAWitness { Ps, rhos }
    }

    /// Returns the points.
    pub fn ps(&self) -> &[Secp256r1Affine; 3] {
        &self.Ps
    }

    /// Returns the commitment randomness.
    pub fn rhos(
        &self,
    ) -> &[(
        <T256Affine as CurveAffine>::ScalarExt,
        <T256Affine as CurveAffine>::ScalarExt,
    ); 3] {
        &self.rhos
    }
}

impl Relation for RelPA {
    type Params = RelPAParams;
    type Statement = RelPAStatement;
    type Witness = RelPAWitness;
    type Error = PopError;

    fn label() -> String {
        format!("Point addition over committed values")
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

        // 1. the commitments are correct
        let b1 =
            self.x
                .Cs
                .iter()
                .zip(w.Ps.iter().zip(w.rhos.iter()))
                .all(|(C, (P, (rhox, rhoy)))| {
                    C.0 == msm_function(&[fp_to_fr(&P.x), *rhox], &[self.pp.G, self.pp.H]).into()
                        && C.1
                            == msm_function(&[fp_to_fr(&P.y), *rhoy], &[self.pp.G, self.pp.H])
                                .into()
                });
        // 2. The points satisfy point addition
        let Ps = w.Ps;
        let b2 = Ps[0] + Ps[1] == Ps[2].into();
        if b1 && b2 {
            Ok(())
        } else {
            Err(PopError::InvalidStatementWitness(Self::label()))
        }
    }
}
