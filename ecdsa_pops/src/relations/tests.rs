use ff::{Field, PrimeField};
use halo2curves::{
    bls12381::{Fr as BlsScalar, G1Affine},
    group::Curve,
    secp256r1::Secp256r1Affine,
    t256::T256Affine,
    CurveAffine, CurveExt,
};
use num_bigint::BigUint;
use r1csipa::msm_function;
use rand_core::{OsRng, RngCore};
use rok::{Relation, RelationProduct};

use super::{
    rcschnorr_compact::{
        RelCSchnorrCompact, RelCSchnorrCompactParams, RelCSchnorrCompactStatement,
        RelCSchnorrCompactWitness,
    },
    rpa::{RelPA, RelPAParams, RelPAStatement, RelPAWitness},
    rsm::{RelSM, RelSMParams, RelSMStatement, RelSMWitness},
};
use crate::{
    circuit_native::utils::big_to_ff,
    errors::PopError,
    relations::{
        rcshnorr::{RelCSchnorr, RelCSchnorrParams, RelCSchnorrStatement, RelCSchnorrWitness},
        rdleq::{RelDLEQ, RelDLEQParams, RelDLEQStatement, RelDLEQWitness},
        recdsa::{RelECDSA, RelECDSAParams, RelECDSAStatement, RelECDSAWitness},
        rpedersen::{RelPedersen, RelPedersenParams, RelPedersenStatement, RelPedersenWitness},
        rpederseneq::{
            RelPedersenEq, RelPedersenEqParams, RelPedersenEqStatement, RelPedersenEqWitness,
        },
    },
    utils::{ecdsa::ECDSA, fp_to_fr, fp_to_scalars, Fq, Fr},
};

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

/// Creates a random pedersen commitment key of size L with the same g for each
/// component
pub(crate) fn pedersen_key_same_g<CCom: CurveAffine>(
    key_size: usize,
    label: &'static str,
) -> Vec<CCom> {
    let label = format!("Pedersen key same G, {}", label);
    let hasher = <CCom as CurveAffine>::CurveExt::hash_to_curve(&label);

    let G = hasher(b"G generator").to_affine();
    let H = hasher(b"H generator").to_affine();
    let mut ck: Vec<_> = (0..(key_size - 1)).map(|_i| G).collect();
    ck.push(H);
    ck
}

// sample a field element from bytes
fn c_from_bytes<const SEC_PARAM_BYTES: usize>(bytes: [u8; SEC_PARAM_BYTES]) -> Fq {
    let c_big = BigUint::from_bytes_be(&bytes);
    Fq::from_str_vartime(&c_big.to_str_radix(10)).unwrap()
}

/// sample a random instance of [RelCSchnorr]
pub(crate) fn sample_random_cschnorr_instance<CCom, const SEC_PARAM_BYTES: usize, const L: usize>(
) -> RelCSchnorr<CCom, L>
where
    CCom: CurveAffine,
    CCom::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    // sample a commitment key
    let ck_R = pedersen_key::<CCom>(L, "ck_R").try_into().unwrap();
    let ck_Q = pedersen_key::<CCom>(L, "ck_Q").try_into().unwrap();
    let h = pedersen_key::<CCom>(1, "H")[0];
    let pp = RelCSchnorrParams { ck_R, ck_Q, h };

    // sample a random challenge of SEC_PARAM_BYTES  bytes
    let mut bytes = [0u8; SEC_PARAM_BYTES];
    OsRng.fill_bytes(&mut bytes);
    let c = c_from_bytes::<SEC_PARAM_BYTES>(bytes);

    // sample commitment randomness
    let rhoR = (0..L)
        .map(|_| <CCom::ScalarExt as Field>::random(OsRng))
        .collect::<Vec<_>>()
        .try_into()
        .unwrap();
    let rhoQ = (0..L)
        .map(|_| <CCom::ScalarExt as Field>::random(OsRng))
        .collect::<Vec<_>>()
        .try_into()
        .unwrap();

    // sample random group elements R, Q
    let R = Secp256r1Affine::random(OsRng);
    let Q = Secp256r1Affine::random(OsRng);

    let w = RelCSchnorrWitness::<CCom, L>::new(R, Q, rhoR, rhoQ);

    // compute a satisfying T
    let T = ((R * c) + Q).into();

    // compute commitment
    let CQ = RelCSchnorr::<CCom, L>::create_commitments(&Q, &rhoQ, &pp.ck_Q, &pp.h);
    let CR = RelCSchnorr::<CCom, L>::create_commitments(&R, &rhoR, &pp.ck_R, &pp.h);

    let x = RelCSchnorrStatement::<CCom, L> { CQ, CR, T, c };

    RelCSchnorr::new(pp, x, Some(w))
}

/// sample a random instance of [RelCSchnorrComact]
pub(crate) fn sample_random_cschnorr_compact_instance<
    CCom,
    const SEC_PARAM_BYTES: usize,
    const L: usize,
    const B: usize,
>() -> RelCSchnorrCompact<CCom, L, B>
where
    CCom: CurveAffine,
    CCom::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    // sample a commitment key
    let ck_R = pedersen_key::<CCom>(L, "ck_R").try_into().unwrap();
    let ck_Q = pedersen_key::<CCom>(L, "ck_L").try_into().unwrap();
    let h = pedersen_key::<CCom>(B, "H").try_into().unwrap();
    let pp = RelCSchnorrCompactParams { ck_R, ck_Q, h };

    // sample a random challenge of SEC_PARAM_BYTES  bytes
    let mut bytes = [0u8; SEC_PARAM_BYTES];
    OsRng.fill_bytes(&mut bytes);
    let c = c_from_bytes::<SEC_PARAM_BYTES>(bytes);

    // sample commitment randomness
    let rho = (0..B)
        .map(|_| <CCom::ScalarExt as Field>::random(OsRng))
        .collect::<Vec<_>>()
        .try_into()
        .unwrap();

    // sample random group elements R, Q
    let R = Secp256r1Affine::random(OsRng);
    let Q = Secp256r1Affine::random(OsRng);

    let w = RelCSchnorrCompactWitness::<CCom, L, B>::new(R, Q, rho);

    // compute a satisfying T
    let T = ((R * c) + Q).into();

    // compute commitment
    let C = RelCSchnorrCompact::<CCom, L, B>::create_commitment(
        &R, &Q, &rho, &pp.ck_R, &pp.ck_Q, &pp.h,
    );

    let x = RelCSchnorrCompactStatement::<CCom, L> { C, T, c };

    RelCSchnorrCompact::new(pp, x, Some(w))
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
    let ck = pedersen_key_same_g::<CCom>(key_size, "sample_random_ecdsa_instance");
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
    let rhox = (0..L)
        .map(|_| <CCom::ScalarExt as Field>::random(OsRng))
        .collect::<Vec<_>>()
        .try_into()
        .unwrap();
    let rhoy = (0..L)
        .map(|_| <CCom::ScalarExt as Field>::random(OsRng))
        .collect::<Vec<_>>()
        .try_into()
        .unwrap();

    let w = RelECDSAWitness::new(pk, sigma_converted.z, rhox, Some(rhoy));

    // compute a commitment to pk.x
    let Cx = (0..L)
        .map(|i| RelECDSA::<CCom, L>::create_commitment(&pp, &w, i).unwrap().0)
        .collect::<Vec<_>>()
        .try_into()
        .unwrap();
    // compute a commitment to pk.y
    let Cy = (0..L)
        .map(|i| RelECDSA::<CCom, L>::create_commitment(&pp, &w, i).unwrap().1.unwrap())
        .collect::<Vec<_>>()
        .try_into()
        .unwrap();

    // compute the statement
    let x = RelECDSAStatement::new(Cx, Some(Cy), m, sigma_converted.K);

    RelECDSA::new(pp, x, Some(w))
}

// sample a random instance of [RelPA]
pub(crate) fn sample_random_pa_instance() -> RelPA {
    // sample the commitment key
    let ck = pedersen_key::<T256Affine>(2, "sample_random_pa_instance");

    // sample the witness
    let P0 = Secp256r1Affine::random(OsRng);
    let P1 = Secp256r1Affine::random(OsRng);
    let P2 = (P0 + P1).to_affine();
    let rho0 = (Fr::random(OsRng), Fr::random(OsRng));
    let rho1 = (Fr::random(OsRng), Fr::random(OsRng));
    let rho2 = (Fr::random(OsRng), Fr::random(OsRng));

    // compute the commitments
    let C0 = (
        msm_function(&[fp_to_fr(&P0.x), rho0.0], &ck).into(),
        msm_function(&[fp_to_fr(&P0.y), rho0.1], &ck).into(),
    );
    let C1 = (
        msm_function(&[fp_to_fr(&P1.x), rho1.0], &ck).into(),
        msm_function(&[fp_to_fr(&P1.y), rho1.1], &ck).into(),
    );
    let C2 = (
        msm_function(&[fp_to_fr(&P2.x), rho2.0], &ck).into(),
        msm_function(&[fp_to_fr(&P2.y), rho2.1], &ck).into(),
    );
    let pp = RelPAParams::new(ck[0], ck[1]);
    let x = RelPAStatement::new([C0, C1, C2]);
    let w = RelPAWitness::new([P0, P1, P2], [rho0, rho1, rho2]);

    RelPA::new(pp, x, Some(w))
}

// sample a random instance of [RelSM]
pub(crate) fn sample_random_sm_instance() -> RelSM {
    // sample the commitment key
    let ck = pedersen_key::<T256Affine>(2, "sample_random_pa_instance");

    // sample the witness
    let G = Secp256r1Affine::random(OsRng);
    let z = Fq::random(OsRng);
    let P: Secp256r1Affine = (G * z).into();
    let rho = (Fr::random(OsRng), Fr::random(OsRng));

    // compute the commitment
    let C = (
        msm_function(&[fp_to_fr(&P.x), rho.0], &ck).into(),
        msm_function(&[fp_to_fr(&P.y), rho.1], &ck).into(),
    );
    let pp = RelSMParams::new(ck[0], ck[1]);
    let x = RelSMStatement::new(C, G);
    let w = RelSMWitness::new(P, rho, z);

    RelSM::new(pp, x, Some(w))
}

// sample a random instance of [RelDLEQ] using 2 limbs
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

/// sample a random instance of [RelPedersenEq]
pub(crate) fn sample_random_pederseneq_instance<CCom, const L: usize, const B: usize>(
) -> RelPedersenEq<CCom, L, B>
where
    CCom: CurveAffine,
    CCom::ScalarExt:
        PrimeField<Repr = <<Secp256r1Affine as CurveAffine>::ScalarExt as PrimeField>::Repr>,
{
    let plain_ck = pedersen_key::<CCom>(2, "sample_random_pederseneq_instance plain");
    let compact_gs = pedersen_key::<CCom>(L, "sample_random_pederseneq_instance compact gs")
        .try_into()
        .unwrap();
    let compact_hs = pedersen_key::<CCom>(B, "sample_random_pederseneq_instance compact hs")
        .try_into()
        .unwrap();

    let pp = RelPedersenEqParams {
        G_plain: plain_ck[0],
        H_plain: plain_ck[1],
        Gs_compact: compact_gs,
        Hs_compact: compact_hs,
    };

    let m = (0..L)
        .map(|_| <CCom::ScalarExt as Field>::random(OsRng))
        .collect::<Vec<_>>()
        .try_into()
        .unwrap();
    let r_plain = (0..L)
        .map(|_| <CCom::ScalarExt as Field>::random(OsRng))
        .collect::<Vec<_>>()
        .try_into()
        .unwrap();
    let r_compact = (0..B)
        .map(|_| <CCom::ScalarExt as Field>::random(OsRng))
        .collect::<Vec<_>>()
        .try_into()
        .unwrap();

    let w = RelPedersenEqWitness {
        m,
        r_plain,
        r_compact,
    };

    let rs = RelPedersenEq::new(
        pp,
        RelPedersenEqStatement {
            C_plain: [CCom::identity(); L],
            C_compact: CCom::identity(),
        },
        Some(w),
    );

    let x = RelPedersenEqStatement {
        C_plain: rs.create_plain_commitments().unwrap(),
        C_compact: rs.create_compact_commitment().unwrap(),
    };

    RelPedersenEq::new(rs.params().clone(), x, rs.witness().clone())
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

    let rcschnor_compact = sample_random_cschnorr_compact_instance::<CCom, 16, L, 10>();
    let result = rcschnor_compact.in_relation();
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
    w_pedersen.push(recdsa.witness().as_ref().unwrap().rhox().iter().sum());
    let mut ck_combined = recdsa.params().gs().to_vec();
    ck_combined.push(*recdsa.params().h());

    // sum the L commitments
    let C_combined = recdsa
        .statement()
        .cx()
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

    let rpederseneq = sample_random_pederseneq_instance::<CCom, L, 8>();
    let result = rpederseneq.in_relation();
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

    // pa
    let rpa = sample_random_pa_instance();
    let result = rpa.in_relation();
    assert!(result.is_ok(), "not in relation: {:?}", result);

    // sm
    let rsm = sample_random_sm_instance();
    let result = rsm.in_relation();
    assert!(result.is_ok(), "not in relation: {:?}", result);
}

#[test]
fn test_relation_product() {
    let rcschnorr = sample_random_cschnorr_instance::<T256Affine, 16, 1>();
    let recdsa = sample_random_ecdsa_instance::<T256Affine, 2>();

    let product_valid = RelationProduct::<
        RelCSchnorr<T256Affine, 1>,
        RelECDSA<T256Affine, 2>,
        PopError,
    >::from_parts(rcschnorr, recdsa);
    assert!(product_valid.in_relation().is_ok());
}
