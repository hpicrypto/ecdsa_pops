use ff::{Field, PrimeField};
use halo2curves::bls12381::Fr as BlsScalar;
use halo2curves::group::Curve;
use halo2curves::secp256r1::Secp256r1Affine;
use halo2curves::t256::T256Affine;
use halo2curves::CurveExt;
use halo2curves::{bls12381::G1Affine, CurveAffine};
use num_bigint::BigUint;
use r1csipa::msm_function;
use rand_core::{OsRng, RngCore};
use rok::{Relation, RelationProduct};

use crate::circuit::utils::big_to_ff;
use crate::errors::PopError;
use crate::relations::rcshnorr::{
    RelCSchnorr, RelCSchnorrParams, RelCSchnorrStatement, RelCSchnorrWitness,
};
use crate::relations::rdleq::{RelDLEQ, RelDLEQParams, RelDLEQStatement, RelDLEQWitness};
use crate::relations::recdsa::{RelECDSA, RelECDSAParams, RelECDSAStatement, RelECDSAWitness};
use crate::relations::rpedersen::{
    RelPedersen, RelPedersenParams, RelPedersenStatement, RelPedersenWitness,
};
use crate::utils::ecdsa::ECDSA;
use crate::utils::{fp_to_scalars, Fq, Fr};

/// Creates a random pedersen commitment key of size L
pub(crate) fn pedersen_key<CCom: CurveAffine>(key_size: usize, label: &'static str) -> Vec<CCom> {
    let label = format!("Pedersen key, {}", label);
    let hasher = <CCom as CurveAffine>::CurveExt::hash_to_curve(&label);
    (0..key_size)
        .map(|i| {
            let input = format!("G_{}", i).into_bytes();
            // <CCom as CurveAffine>::rando(OsRng)).collect::<Vec<_>>();
            hasher(&input)
        })
        .map(|c| c.to_affine())
        .collect()
}

// sample a field element from bytes
fn c_from_bytes<const SEC_PARAM_BYTES: usize>(bytes: [u8; SEC_PARAM_BYTES]) -> Fq {
    let c_big = BigUint::from_bytes_be(&bytes);
    Fq::from_str_vartime(&c_big.to_str_radix(10)).unwrap()
}

/// sample a random instance of [RelCSchnorr]
pub(crate) fn sample_random_cschnorr_instance<CCom, const SEC_PARAM_BYTES: usize, const L: usize>(
) -> RelCSchnorr<CCom, SEC_PARAM_BYTES, L>
where
    CCom: CurveAffine,
    CCom::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    // sample a commitment key
    let pp = RelCSchnorrParams {
        ck: pedersen_key::<CCom>(2 * L + 1, "sample_random_cschnorr_instance"),
    };

    // sample a random challenge of SEC_PARAM_BYTES  bytes
    let mut bytes = [0u8; SEC_PARAM_BYTES];
    OsRng.fill_bytes(&mut bytes);
    let c = c_from_bytes::<SEC_PARAM_BYTES>(bytes);

    // sample commitment randomness
    let rho = <CCom::ScalarExt as Field>::random(OsRng);

    // sample random group elements R, Q
    let R = Secp256r1Affine::random(OsRng);
    let Q = Secp256r1Affine::random(OsRng);

    let w = RelCSchnorrWitness::<CCom>::new(R, Q, rho);

    // compute a satisfying T
    let T = ((R * c) + Q).into();

    // compute commitment
    let C = RelCSchnorr::<CCom, SEC_PARAM_BYTES, L>::create_commitment(&pp, &w).unwrap();
    let x = RelCSchnorrStatement::<CCom, SEC_PARAM_BYTES> { C, T, c };

    RelCSchnorr::new(pp, x, Some(w))
}

/// sample a random instance of [RelECDSA]
pub(crate) fn sample_random_ecdsa_instance<CCom, const L: usize>() -> RelECDSA<CCom, L>
where
    CCom: CurveAffine,
    CCom::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    // sample a commitment key
    let key_size = L + 1;
    let ck = pedersen_key::<CCom>(key_size, "sample_random_ecdsa_instance");
    let Gs = ck[0..L].try_into().unwrap();
    let H = ck[L];

    sample_random_ecdsa_instance_with_key(Gs, H)
}

/// sample a random instance of [RelECDSA] given a commitment key
pub(crate) fn sample_random_ecdsa_instance_with_key<CCom, const L: usize>(
    Gs: [CCom; L],
    H: CCom,
) -> RelECDSA<CCom, L>
where
    CCom: CurveAffine,
    CCom::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    // sample a random keypair
    let ecdsa = ECDSA {
        pp: Secp256r1Affine::generator(),
    };
    let pp = RelECDSAParams::new(Gs, H, ecdsa);
    let (sk, pk) = ecdsa.keygen(&mut OsRng);

    // sample a random message and sign it
    let m = Fq::random(OsRng);
    let sigma = ecdsa.sign_prehashed(&sk, &m, &mut OsRng).unwrap();
    let sigma_converted = ecdsa.convert(&pk, &m, &sigma);

    // sample randomness for the commitments
    let rho = (0..L)
        .map(|_| <CCom::ScalarExt as Field>::random(OsRng))
        .collect::<Vec<_>>()
        .try_into()
        .unwrap();

    let w = RelECDSAWitness::new(pk, sigma_converted.z, rho);

    // compute a commitment to pk.x
    let C = (0..L)
        .map(|i| RelECDSA::<CCom, L>::create_commitment(&pp, &w, i).unwrap())
        .collect::<Vec<_>>()
        .try_into()
        .unwrap();

    // compute the statement
    let x = RelECDSAStatement::new(C, m, sigma_converted.K);

    RelECDSA::new(pp, x, Some(w))
}

// sample a random instance ofRelDLEQ] using 2 limbs
pub(crate) fn sample_random_dleq_instance() -> RelDLEQ<G1Affine, T256Affine> {
    // sample two commitment key
    let ck1 = pedersen_key::<G1Affine>(2, "sample_random_dleq_instance");
    let ck2 = pedersen_key::<T256Affine>(2, "sample_random_dleq_instance");
    // sample the witness
    let m = BigUint::from(OsRng.next_u32());
    let (m1, m2): (BlsScalar, Fr) = (big_to_ff(&m), big_to_ff(&m));
    let (r1, r2) = (BlsScalar::random(OsRng), Fr::random(OsRng));
    let (C1, C2) = (
        msm_function(&[m1, r1], &ck1).into(),
        msm_function(&[m2, r2], &ck2).into(),
    );

    let pp = RelDLEQParams { ck1, ck2 };
    let x = RelDLEQStatement { C1, C2 };
    let w = RelDLEQWitness { m, r1, r2 };

    RelDLEQ::new(pp, x, Some(w))
}

fn test_relations_helper<CCom, const L: usize>()
where
    CCom: CurveAffine,
    CCom::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    // RelCSchnorr
    let rcschnor = sample_random_cschnorr_instance::<CCom, 16, L>();
    let result = rcschnor.in_relation();
    assert!(result.is_ok(), "not in relation: {:?}", result);

    // RelECDSA
    let recdsa = sample_random_ecdsa_instance::<CCom, L>();
    let result = recdsa.in_relation();
    assert!(result.is_ok(), "not in relation: {:?}", result);

    // RelPedersen with the sum of the commitments
    let mut w_pedersen = fp_to_scalars::<CCom, L>(&recdsa.witness().clone().unwrap().q().x)
        .unwrap()
        .to_vec();
    // sum the randomness used for the L commitments to "compact" them
    w_pedersen.push(recdsa.witness().as_ref().unwrap().rho().iter().sum());
    let mut ck_combined = recdsa.params().gs().to_vec();
    ck_combined.push(*recdsa.params().h());

    // sum the L commitments
    let C_combined = recdsa
        .statement()
        .c()
        .iter()
        .fold(CCom::identity().to_curve(), |acc, &C| acc + C);
    let (pp, x, w) = (
        RelPedersenParams { ck: ck_combined },
        RelPedersenStatement {
            C: C_combined.into(),
        },
        RelPedersenWitness { m: w_pedersen },
    );
    let rpedersen = RelPedersen::<CCom>::new(pp, x, Some(w));
    let result = rpedersen.in_relation();
    assert!(result.is_ok(), "not in relation: {:?}", result);
}

#[test]
fn test_relations() {
    test_relations_helper::<T256Affine, 1>();
    test_relations_helper::<T256Affine, 2>();
    test_relations_helper::<T256Affine, 4>();
    // Bls needs at least two scalars to represent a p256 element
    test_relations_helper::<G1Affine, 2>();
    test_relations_helper::<G1Affine, 4>();

    // dleq
    let rdleq = sample_random_dleq_instance();
    assert!(rdleq.in_relation().is_ok());
    let result = rdleq.in_relation();
    assert!(result.is_ok(), "not in relation: {:?}", result);
}

#[test]
fn test_relation_product() {
    let rcschnorr = sample_random_cschnorr_instance::<T256Affine, 16, 1>();
    let recdsa = sample_random_ecdsa_instance::<T256Affine, 2>();

    let product_valid = RelationProduct::<
        RelCSchnorr<T256Affine, 16, 1>,
        RelECDSA<T256Affine, 2>,
        PopError,
    >::from_parts(rcschnorr, recdsa);
    assert!(product_valid.in_relation().is_ok());
}
