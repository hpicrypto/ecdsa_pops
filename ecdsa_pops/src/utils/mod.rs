//! Helper types and functions for implementing PoPs
use ark_std::One;
use ff::{Field, PrimeField};
use halo2curves::{secp256r1::Secp256r1Affine, t256::T256Affine, CurveAffine};
use num_bigint::BigUint;

use crate::{
    circuit_native::utils::{big_to_ff, ff_to_big},
    errors::PopError,
};

pub mod ecdsa;

/// The scalar field of [T256Affine] (which is the same as the base field of
/// [Secp256r1Affine])
pub type Fr = <T256Affine as CurveAffine>::ScalarExt;
/// The base field of [Secp256r1Affine] (which is the same as the scalar field
/// of [T256Affine])
pub type Fp = <Secp256r1Affine as CurveAffine>::Base;
/// The scalar field of [Secp256r1Affine]
pub type Fq = <Secp256r1Affine as CurveAffine>::ScalarExt;

/// Helper function to convert P256 base [Fp] to T256 Scalar [Fr]
pub(crate) fn fp_to_fr(a: &Fp) -> Fr {
    Fr::from_bytes(&a.to_bytes()).unwrap()
}

/// Helper function to convert P256 scalar [Fq] to T256 Scalar [Fr]
pub(crate) fn fq_to_fr(a: &Fq) -> Fr {
    Fr::from_bytes(&a.to_bytes()).unwrap()
}

/// Converts a P256 base  element [Fp] to a representation in
/// [CurveAffine::ScalarExt].
///
/// The result is given in little endian limbs
pub(crate) fn fp_to_scalars<C, const N_LIMBS: usize>(
    x: &Fp,
) -> Result<[C::ScalarExt; N_LIMBS], PopError>
where
    C: CurveAffine,
    C::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    // TODO: Generalize to more flexible limb representations
    if 32 % N_LIMBS != 0 {
        unimplemented!()
    }
    let x_bytes = x.to_repr();
    let mut res = [C::ScalarExt::ZERO; N_LIMBS];
    (0..N_LIMBS).try_for_each(|i| {
        let lower = i * 32 / N_LIMBS;
        let higher = lower + 32 / N_LIMBS;
        let mut limb_bytes = x_bytes[lower..higher].to_vec();
        limb_bytes.extend(std::iter::repeat_n(0, 32 - 32 / N_LIMBS));
        let limb_repr: [u8; 32] = limb_bytes.as_slice().try_into()?;
        res[i] = <C::ScalarExt as PrimeField>::from_repr(limb_repr.into()).unwrap();
        Ok::<_, PopError>(())
    })?;
    // sanity check
    debug_assert!(scalars_to_fp::<C, N_LIMBS>(&res) == *x);
    Ok(res)
}

/// Converts [CurveAffine::ScalarExt] limbs to a P256 Base element [Fp] fp
/// element Fp is little endian
pub(crate) fn scalars_to_fp<C, const N_LIMBS: usize>(limbs: &[C::ScalarExt; N_LIMBS]) -> Fp
where
    C: CurveAffine,
    C::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    let shift = BigUint::one() << ((32 / N_LIMBS) * 8);
    limbs.iter().rev().fold(Fp::ZERO, |acc, x| {
        acc * big_to_ff::<Fp>(&shift) + big_to_ff::<Fp>(&ff_to_big(x))
    })
}
