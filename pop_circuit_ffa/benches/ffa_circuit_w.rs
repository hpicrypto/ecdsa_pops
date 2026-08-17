use criterion::{criterion_group, criterion_main, Criterion};
use ff::Field;
use group::Group;
use midnight_circuits::CircuitField;
use midnight_curves::{
    p256::{Fq as P256Scalar, P256},
    Bls12, G1Projective,
};
use midnight_proofs::{
    plonk::commit_to_instances,
    poly::kzg::{params::ParamsKZG, KZGCommitmentScheme},
};
use midnight_zk_stdlib::{
    cost_model, utils::plonk_api::srs_for_test, MidnightPK, MidnightVK, Relation,
};
use pop_circuit_ffa::{EcdsaPoPP256, B_FACTORS};
use rand::{rngs::OsRng, Rng};

type F = midnight_curves::Fq;

const NB_BITS_C: usize = 128;

fn get_relation() -> ((P256, u128), (P256, P256, [F; 8])) {
    let mut rng = OsRng;

    // ── Generate a valid witness ─────────────────────────────────────────────
    let q = P256::random(&mut rng);
    let r = P256::random(&mut rng);
    let blinders = [0; B_FACTORS].map(|_| F::random(&mut rng));

    let c_u128: u128 = rng.gen::<u128>();

    let mut c_be = [0u8; 32];
    c_be[16..].copy_from_slice(&c_u128.to_be_bytes());
    let c_scalar = P256Scalar::from_bytes_be(&c_be).expect("valid bounded scalar");
    let t = r * c_scalar + q;

    ((t, c_u128), (q, r, blinders))
}

// we run setup once since a single key works for all cases
fn setup() -> (
    ParamsKZG<Bls12>,
    MidnightVK,
    MidnightPK<EcdsaPoPP256<NB_BITS_C>>,
) {
    let rel_w = EcdsaPoPP256::<NB_BITS_C>;
    let m_w = cost_model(&rel_w, None);
    let srs = srs_for_test(&rel_w, Some(m_w.k));
    let vk = midnight_zk_stdlib::setup_vk(&srs, &rel_w);
    let pk = midnight_zk_stdlib::setup_pk(&rel_w, &vk);

    (srs, vk, pk)
}

fn prove_w(
    srs: &ParamsKZG<Bls12>,
    pk: &MidnightPK<EcdsaPoPP256<NB_BITS_C>>,
    instance: &(P256, u128),
    witness: &(P256, P256, [F; 8]),
    rng: OsRng,
) -> Vec<u8> {
    let rel_w = EcdsaPoPP256::<NB_BITS_C>;
    midnight_zk_stdlib::prove::<EcdsaPoPP256<NB_BITS_C>, blake2b_simd::State>(
        srs, pk, &rel_w, instance, *witness, rng,
    )
    .expect("proof generation should not fail")
}

fn verify_w(
    srs: &ParamsKZG<Bls12>,
    vk: &MidnightVK,
    instance: &(P256, u128),
    commitment: &G1Projective,
    proof: &[u8],
) {
    midnight_zk_stdlib::verify::<EcdsaPoPP256<NB_BITS_C>, blake2b_simd::State>(
        &srs.verifier_params(),
        vk,
        instance,
        Some(commitment.into()),
        proof,
    )
    .expect("proof verification should not fail");
}

fn compute_commitment(
    srs: &ParamsKZG<Bls12>,
    vk: &MidnightVK,
    witness: &(P256, P256, [F; 8]),
) -> G1Projective {
    let c_instance = EcdsaPoPP256::<NB_BITS_C>::format_committed_instances(witness);
    commit_to_instances::<F, KZGCommitmentScheme<_>>(srs, vk.vk().get_domain(), &c_instance)
        .into_point()
}

fn criterion_benchmark(c: &mut Criterion) {
    let mut rng = OsRng;
    let sample_size = 50;

    // sample a single statement
    let relation = get_relation();

    // prover time
    let mut prover_group_daa = c.benchmark_group("ffa windowed circuit prover");

    let (srs, vk, pk) = setup();

    prover_group_daa.sample_size(sample_size);
    prover_group_daa.bench_function("ffa windowed circuit prover", |b| {
        b.iter(|| {
            let rel_w = relation;
            let instance = rel_w.0;
            let witness = rel_w.1;
            prove_w(&srs, &pk, &instance, &witness, rng);
        })
    });
    prover_group_daa.finish();

    // create a proof and a commitment
    let proof = prove_w(&srs, &pk, &relation.0, &relation.1, rng);
    let com = compute_commitment(&srs, &vk, &relation.1);

    let rows = cost_model(&EcdsaPoPP256::<NB_BITS_C>, None).rows;
    println!("Number of rows: {}", rows);
    println!("Proof size: {}B", proof.len());

    // verifier time
    let mut verifier_group_daa = c.benchmark_group("ffa windowed circuit verifier");

    verifier_group_daa.sample_size(sample_size);
    verifier_group_daa.bench_function("ffa windowed circuit verifier", |b| {
        b.iter(|| {
            let rel_w = relation;
            let instance = rel_w.0;
            verify_w(&srs, &vk, &instance, &com, &proof);
        })
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
