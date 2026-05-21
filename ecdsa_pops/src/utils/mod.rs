//! Helper types and functions for implementing PoPs
use ark_ec::short_weierstrass::{Affine as SwAffine, SWCurveConfig};
use ark_ff::{BigInteger, One, PrimeField as ArkPrimeField};
use ark_secp256r1::{Affine as Secp256r1AffineArk, Fq as FpArk, Fr as FqArk};
use ff::{Field, PrimeField};
use halo2curves::{secp256r1::Secp256r1Affine, t256::T256Affine, CurveAffine};
use num_bigint::BigUint;
use num_traits::ToBytes;

use ark_serialize::CanonicalSerialize;

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
pub fn fp_to_fr(a: &Fp) -> Fr {
    Fr::from_bytes(&a.to_bytes()).unwrap()
}

/// Helper function to convert P256 scalar [Fq] to T256 Scalar [Fr]
pub fn fq_to_fr(a: &Fq) -> Fr {
    Fr::from_bytes(&a.to_bytes()).unwrap()
}

/// Helper function to convert halo2 Fr elements to ark Fr elements
pub fn fr_to_arkfr<F: ArkPrimeField>(a: &Fr) -> F {
    let halo_repr = a.to_repr();
    let halo_bytes = halo_repr.as_ref();
    F::from_le_bytes_mod_order(halo_bytes.as_ref())
}

/// Helper function to convert halo2 Fq elements to ark Fq elements
pub fn fq_to_arkfq(a: &Fq) -> FqArk {
    let halo_repr = a.to_repr();
    let halo_bytes = halo_repr.as_ref();
    <FqArk as ArkPrimeField>::from_le_bytes_mod_order(halo_bytes.as_ref())
}

/// Helper function to convert halo2 Fp elements to ark Fp elements
pub fn fp_to_arkfp(a: &Fp) -> FpArk {
    let halo_repr = a.to_repr();
    let halo_bytes = halo_repr.as_ref();
    <FpArk as ArkPrimeField>::from_le_bytes_mod_order(halo_bytes.as_ref())
}

/// Helper function to convert halo2 Ft elements to ark Ft elements
pub fn ft_to_arkft<F: ArkPrimeField>(a: &Ft) -> F {
    let halo_repr = a.to_repr();
    let halo_bytes = halo_repr.as_ref();
    F::from_le_bytes_mod_order(halo_bytes.as_ref())
}

/// Helper function to convert halo2 [Secp256r1Affine] elements to
/// [Secp256r1AffineArk] elements
pub fn p256_to_arkp256(P: &Secp256r1Affine) -> Secp256r1AffineArk {
    let (x, y) = (fp_to_arkfp(&P.x), fp_to_arkfp(&P.y));
    Secp256r1AffineArk::new(x, y)
}

/// Converts halo2 Ft elements to CDLS-side t256 Fq (the base field).
pub(crate) fn ft_to_cdls_ft(a: &Ft) -> t256::Fq {
    ft_to_arkft(a)
}

/// Converts a halo2curves [T256Affine] to a CDLS-side [t256::Affine].
pub(crate) fn t256_to_cdls_t256(p: &T256Affine) -> SwAffine<t256::Config> {
    t256_to_arkt256(p)
}

pub(crate) fn fr_to_cdls_fr(a: &Fr) -> t256::Fr {
    fr_to_arkfr(a)
}

/// Convert CDLS-side ark t256 Affine to halo2curves T256Affine.
/// Reverse of t256_to_cdls_t256.
pub fn cdls_t256_to_t256(p: &SwAffine<t256::Config>) -> T256Affine {
    let x = ark_ft_to_halo_ft(&p.x);
    let y = ark_ft_to_halo_ft(&p.y);
    T256Affine::from_xy(x, y).unwrap()
}

/// Convert CDLS-side ark t256 base-field element to halo2 Ft.
pub(crate) fn cdls_ft_to_halo_ft(a: &t256::Fq) -> Ft {
    let mut bytes = Vec::new();
    a.serialize_compressed(&mut bytes).unwrap();
    // ark serializes 32-byte LE, halo2 from_repr expects LE bytes.
    let mut buf = [0u8; 32];
    buf.copy_from_slice(&bytes[..32]);
    <Ft as PrimeField>::from_repr(buf.into()).unwrap()
}

/// Reverse of ft_to_cdls_ft.
pub(crate) fn ark_ft_to_halo_ft(a: &t256::Fq) -> Ft {
    // ark field -> bytes -> halo2 field
    let ark_repr = a.into_bigint().to_bytes_le(); // returns Vec<u8>
    let mut buf = [0u8; 32];
    buf.copy_from_slice(&ark_repr);
    <Ft as PrimeField>::from_repr(buf.into()).unwrap()
}

/// Helper function to convert halo2 [Secp256r1Affine] elements to
/// [Secp256r1AffineArk] elements
pub fn t256_to_arkt256<C>(P: &T256Affine) -> SwAffine<C>
where
    C: SWCurveConfig,
    C::BaseField: ArkPrimeField,
{
    let (x, y) = (ft_to_arkft(&P.x), ft_to_arkft(&P.y));
    SwAffine::<C>::new(x, y)
}

/// Converts a P256 base  element [Fp] to a representation in
/// [CurveAffine::ScalarExt].
///
/// The result is given in little endian limbs
pub fn fp_to_scalars<C, const N_LIMBS: usize>(x: &Fp) -> Result<[C::ScalarExt; N_LIMBS], PopError>
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
pub fn scalars_to_fp<C, const N_LIMBS: usize>(limbs: &[C::ScalarExt; N_LIMBS]) -> Fp
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

/// Helper function to convert ark Fq elements to halo2 Fq elements
pub fn arkfq_to_fq(ark_fq: &FqArk) -> Option<Fq> {
    // The conversion to BigUint is important!
    // arkworks stores the field element internally as
    // a signed BigInt!
    let fq_bigint: BigUint = ark_fq.clone().into();

    let fq_bytes = fq_bigint.to_le_bytes();
    let mut a_bytes: [u8; 32] = [0; 32];
    // we use a little endian, so fill bytes are to the right (trainling zeros)
    // The bounds for rejecting P256 elements is just short of the 32 bytes
    // so it can happen that we have 31 bytes (with a trailing zero).
    a_bytes[..fq_bytes.len()].copy_from_slice(&fq_bytes);
    Fq::from_repr(a_bytes.into()).into_option()
}
/// Helper function to convert ark Fp elements to halo2 Fp elements
pub fn arkfp_to_fp(ark_fp: &FpArk) -> Option<Fp> {
    // The conversion to BigUint is important!
    // arkworks stores the field element internally as
    // a signed BigInt!
    let fp_bigint: BigUint = ark_fp.clone().into();
    let fp_bigint_bytes = fp_bigint.to_le_bytes();
    let mut fp_bytes: [u8; 32] = [0; 32];
    // we use a little endian, so fill bytes are to the right (trainling zeros)
    // The bounds for rejecting P256 elements is just short of the 32 bytes
    // so it can happen that we have 31 bytes (with a trailing zero).
    fp_bytes[..fp_bigint_bytes.len()].copy_from_slice(&fp_bigint_bytes);
    Fp::from_repr(fp_bytes.into()).into_option()
}
/// Helper function to convert [Secp256r1AffineArk] elements to
/// halo2 [Secp256r1Affine] elements
pub fn arkp256_to_p256(P: &Secp256r1AffineArk) -> Option<Secp256r1Affine> {
    let (x, y) = (arkfp_to_fp(&P.x)?, arkfp_to_fp(&P.y)?);
    Some(Secp256r1Affine { x: x, y })
}

#[cfg(test)]
mod tests {
    use ff::Field;
    use halo2curves::{secp256r1::Secp256r1Affine, t256::T256Affine};
    use rand_core::OsRng;

    use crate::utils::{
        arkfq_to_fq, arkp256_to_p256, fr_to_cdls_fr, ft_to_cdls_ft, t256_to_cdls_t256,
    };

    use super::{fp_to_arkfp, fq_to_arkfq, p256_to_arkp256, Fp, Fq, Fr, Ft};
    #[test]
    fn test_converting_back_and_forth() {
        let P = Secp256r1Affine::random(OsRng);
        let z = Fq::random(OsRng);
        let Q: Secp256r1Affine = (P * z).into();

        let Park = p256_to_arkp256(&P);
        let zark = fq_to_arkfq(&z);
        let Qark = p256_to_arkp256(&Q);
        assert_eq!(Park * zark, Qark);
        let p2 = arkp256_to_p256(&Park).unwrap();
        let z2 = arkfq_to_fq(&zark).unwrap();
        let q2 = arkp256_to_p256(&Qark).unwrap();
        let d: Secp256r1Affine = (p2 * z2).into();
        assert_eq!(d, q2);
    }

    #[test]
    fn test_field_conversions() {
        let (a, b) = (<Fr as Field>::random(OsRng), <Fr as Field>::random(OsRng));
        let c = a + b;
        let (a_ark, b_ark, c_ark) = (fr_to_cdls_fr(&a), fr_to_cdls_fr(&b), fr_to_cdls_fr(&c));
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
        let (a_ark, b_ark, c_ark) = (ft_to_cdls_ft(&a), ft_to_cdls_ft(&b), ft_to_cdls_ft(&c));
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

        let Park = t256_to_cdls_t256(&P);
        let zark = fr_to_cdls_fr(&z);
        let Qark = t256_to_cdls_t256(&Q);
        assert_eq!(Park * zark, Qark);
    }
}
