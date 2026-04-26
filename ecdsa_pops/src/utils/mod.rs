//! Helper types and functions for implementing PoPs
use ark_ff::{One, PrimeField as ArkPrimeField};
use ark_secp256r1::{Affine as Secp256r1AffineArk, Fq as FpArk, Fr as FqArk};
use equality_across_groups::tom256::{Affine as T256AffineArk, Fq as FtArk, Fr as FrArk};
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
/// The base field of [T256r1Affine] (which is the same as the scalar field
/// of [T256Affine])
type Ft = <T256Affine as CurveAffine>::Base;

/// Helper function to convert P256 base [Fp] to T256 Scalar [Fr]
pub(crate) fn fp_to_fr(a: &Fp) -> Fr {
    Fr::from_bytes(&a.to_bytes()).unwrap()
}

/// Helper function to convert P256 scalar [Fq] to T256 Scalar [Fr]
pub(crate) fn fq_to_fr(a: &Fq) -> Fr {
    Fr::from_bytes(&a.to_bytes()).unwrap()
}

/// Helper function to convert halo2 Fr elements to ark Fr elements
pub(crate) fn fr_to_arkfr(a: &Fr) -> FrArk {
    let halo_repr = a.to_repr();
    let halo_bytes = halo_repr.as_ref();
    <FrArk as ArkPrimeField>::from_le_bytes_mod_order(halo_bytes.as_ref())
}

/// Helper function to convert halo2 Fq elements to ark Fq elements
pub(crate) fn fq_to_arkfq(a: &Fq) -> FqArk {
    let halo_repr = a.to_repr();
    let halo_bytes = halo_repr.as_ref();
    <FqArk as ArkPrimeField>::from_le_bytes_mod_order(halo_bytes.as_ref())
}

/// Helper function to convert halo2 Fp elements to ark Fp elements
pub(crate) fn fp_to_arkfp(a: &Fp) -> FpArk {
    let halo_repr = a.to_repr();
    let halo_bytes = halo_repr.as_ref();
    <FpArk as ArkPrimeField>::from_le_bytes_mod_order(halo_bytes.as_ref())
}

/// Helper function to convert halo2 Ft elements to ark Ft elements
pub(crate) fn ft_to_arkft(a: &Ft) -> FtArk {
    let halo_repr = a.to_repr();
    let halo_bytes = halo_repr.as_ref();
    <FtArk as ArkPrimeField>::from_le_bytes_mod_order(halo_bytes.as_ref())
}

/// Helper function to convert halo2 [Secp256r1Affine] elements to
/// [Secp256r1AffineArk] elements
pub(crate) fn p256_to_arkp256(P: &Secp256r1Affine) -> Secp256r1AffineArk {
    let (x, y) = (fp_to_arkfp(&P.x), fp_to_arkfp(&P.y));
    Secp256r1AffineArk::new(x, y)
}

/// Helper function to convert halo2 [Secp256r1Affine] elements to
/// [Secp256r1AffineArk] elements
pub(crate) fn t256_to_arkt256(P: &T256Affine) -> T256AffineArk {
    let (x, y) = (ft_to_arkft(&P.x), ft_to_arkft(&P.y));
    T256AffineArk::new(x, y)
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

#[cfg(test)]
mod tests {
    use ff::Field;
    use halo2curves::{secp256r1::Secp256r1Affine, t256::T256Affine};
    use rand_core::OsRng;

    use super::{
        fp_to_arkfp, fq_to_arkfq, fr_to_arkfr, ft_to_arkft, p256_to_arkp256, t256_to_arkt256, Fp,
        Fq, Fr, Ft,
    };

    #[test]
    fn test_field_conversions() {
        let (a, b) = (<Fr as Field>::random(OsRng), <Fr as Field>::random(OsRng));
        let c = a + b;
        let (a_ark, b_ark, c_ark) = (fr_to_arkfr(&a), fr_to_arkfr(&b), fr_to_arkfr(&c));
        assert_eq!(c_ark, a_ark + b_ark);
        let (a, b) = (<Fp as Field>::random(OsRng), <Fp as Field>::random(OsRng));
        let c = a + b;
        let (a_ark, b_ark, c_ark) = (fp_to_arkfp(&a), fp_to_arkfp(&b), fp_to_arkfp(&c));
        assert_eq!(c_ark, a_ark + b_ark);
        let (a, b) = (<Fq as Field>::random(OsRng), <Fq as Field>::random(OsRng));
        let c = a + b;
        let (a_ark, b_ark, c_ark) = (fq_to_arkfq(&a), fq_to_arkfq(&b), fq_to_arkfq(&c));
        assert_eq!(c_ark, a_ark + b_ark);
        let (a, b) = (<Ft as Field>::random(OsRng), <Ft as Field>::random(OsRng));
        let c = a + b;
        let (a_ark, b_ark, c_ark) = (ft_to_arkft(&a), ft_to_arkft(&b), ft_to_arkft(&c));
        assert_eq!(c_ark, a_ark + b_ark);
    }

    #[test]
    fn test_group_conversions() {
        let P = Secp256r1Affine::random(OsRng);
        let z = Fq::random(OsRng);
        let Q: Secp256r1Affine = (P * z).into();

        let Park = p256_to_arkp256(&P);
        let zark = fq_to_arkfq(&z);
        let Qark = p256_to_arkp256(&Q);
        assert_eq!(Park * zark, Qark);

        let P = T256Affine::random(OsRng);
        let z = Fr::random(OsRng);
        let Q: T256Affine = (P * z).into();

        let Park = t256_to_arkt256(&P);
        let zark = fr_to_arkfr(&z);
        let Qark = t256_to_arkt256(&Q);
        assert_eq!(Park * zark, Qark);
    }
}
