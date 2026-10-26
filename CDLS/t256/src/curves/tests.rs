use crate::{Config, Projective};
use ark_algebra_test_templates::*;
use ark_ec::short_weierstrass::{self as sw};
use ark_secp256r1::Config as secp256r1conf;
use cdls_macros::test_pedersen;

type OtherProject = sw::Projective<secp256r1conf>;

test_group!(g1; Projective; sw);
test_pedersen!(tp; Config, OtherProject);

// T-256 has cofactor 1, arkworks 0.4 fix
// Check that every curve point has order r.
mod subgroup_check {
    use crate::{Config, Fr, Projective};
    use ark_ec::{short_weierstrass::SWCurveConfig, CurveGroup};
    use ark_ff::{Field, UniformRand, Zero};

    #[test]
    fn subgroup_check_is_vacuous() {
        let mut rng = ark_std::test_rng();
        for _ in 0..32 {
            let p = Projective::rand(&mut rng).into_affine();
            assert!(Config::mul_affine(&p, Fr::characteristic()).is_zero());
            assert!(Config::is_in_correct_subgroup_assuming_on_curve(&p));
        }
    }
}
