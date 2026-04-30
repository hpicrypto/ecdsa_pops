use criterion::{criterion_group, criterion_main, Criterion};

use pop_circuit_ffa::{EcdsaPoPP256Daa, B_FACTORS};

use ff::Field;
use group::Group;
use midnight_circuits::CircuitField;

use midnight_curves::{
    p256::{Fq as P256Scalar, P256},
    G1Projective,
};
use midnight_proofs::{plonk::commit_to_instances, poly::kzg::KZGCommitmentScheme};
use midnight_zk_stdlib::{cost_model, utils::plonk_api::srs_for_test, Relation};
use rand::{rngs::OsRng, Rng};

type F = midnight_curves::Fq;

const NB_BITS_C: usize = 96;

fn get_relation() -> (P256, u128, (P256, P256, [F; 8])) {
    let mut rng = OsRng;

    // ── Generate a valid witness ─────────────────────────────────────────────
    let q = P256::random(&mut rng);
    let r = P256::random(&mut rng);
    let blinders = [0; B_FACTORS].map(|_| F::random(&mut rng));

    let c_u128: u128 = rng.gen::<u128>() & ((1u128 << NB_BITS_C) - 1);

    let mut c_be = [0u8; 32];
    c_be[16..].copy_from_slice(&c_u128.to_be_bytes());
    let c_scalar = P256Scalar::from_bytes_be(&c_be).expect("valid bounded scalar");
    let t = r + q * c_scalar;

    (t, c_u128, (q, r, blinders))
}

fn prove_daa(c_u128: u128, instance: &P256, witness: &(P256, P256, [F; 8]), rng: OsRng) -> Vec<u8> {
    let rel_daa = EcdsaPoPP256Daa::new(c_u128);
    let m_daa = cost_model(&rel_daa, None);
    let srs = srs_for_test(&rel_daa, Some(m_daa.k));

    // we include the time to initialize the keys since they depend on the statement
    let vk = midnight_zk_stdlib::setup_vk(&srs, &rel_daa);
    let pk = midnight_zk_stdlib::setup_pk(&rel_daa, &vk);

    midnight_zk_stdlib::prove::<EcdsaPoPP256Daa, blake2b_simd::State>(
        &srs, &pk, &rel_daa, instance, *witness, rng,
    )
    .expect("proof generation should not fail")
}

fn verify_daa(c_u128: u128, instance: &P256, commitment: &G1Projective, proof: &[u8]) {
    let rel_daa = EcdsaPoPP256Daa::new(c_u128);
    let m_daa = cost_model(&rel_daa, None);
    let srs = srs_for_test(&rel_daa, Some(m_daa.k));

    // we include the time to initialize the key since they depend on the statement
    let vk = midnight_zk_stdlib::setup_vk(&srs, &rel_daa);

    midnight_zk_stdlib::verify::<EcdsaPoPP256Daa, blake2b_simd::State>(
        &srs.verifier_params(),
        &vk,
        instance,
        Some(commitment.into()),
        proof,
    )
    .expect("proof verification should not fail");
}

fn compute_commitment(c_u128: u128, witness: &(P256, P256, [F; 8])) -> G1Projective {
    let rel_daa = EcdsaPoPP256Daa::new(c_u128);
    let m_daa = cost_model(&rel_daa, None);
    let srs = srs_for_test(&rel_daa, Some(m_daa.k));
    let c_instance = EcdsaPoPP256Daa::format_committed_instances(witness);
    let vk = midnight_zk_stdlib::setup_vk(&srs, &rel_daa);
    commit_to_instances::<F, KZGCommitmentScheme<_>>(&srs, vk.vk().get_domain(), &c_instance)
}

fn criterion_benchmark(c: &mut Criterion) {
    let mut rng = OsRng;
    let sample_size = 50;

    // sample sample_size_statements
    let relations: Vec<_> = (0..sample_size).map(|_| get_relation()).collect();

    // prover time
    let mut idx = 0usize;
    let mut prover_group_daa = c.benchmark_group("ffa daa circuit prover");

    let mut proofs = Vec::new();
    prover_group_daa.sample_size(sample_size);
    prover_group_daa.bench_function("ffa daa circuit prover", |b| {
        b.iter(|| {
            let rel_daa = relations[idx % sample_size];
            let instance = rel_daa.0;
            let c = rel_daa.1;
            let witness = rel_daa.2;
            idx += 1;
            let proof = prove_daa(c, &instance, &witness, rng);
            proofs.push(proof)
        })
    });
    prover_group_daa.finish();

    let mut idx = 0usize;

    // compute the proofs and commitments to pass to verifier
    let v_inputs: Vec<_> = relations
        .iter()
        .map(|_| {
            let rel_daa = relations[idx % sample_size];
            let c = rel_daa.1;
            let witness = rel_daa.2;
            idx += 1;
            compute_commitment(c, &witness)
        })
        .collect();

    // rows avg
    let rows_sum: usize = relations
        .iter()
        .map(|r| {
            let rel_daa = EcdsaPoPP256Daa::new(r.1);
            cost_model(&rel_daa, None).rows
        })
        .sum();
    println!(
        "Average number of rows: {}",
        rows_sum as f64 / sample_size as f64
    );
    println!("Proof size: {}B", proofs[0].len());

    // verifier time
    let mut idx = 0usize;
    let mut verifier_group_daa = c.benchmark_group("ffa daa circuit verifier");

    verifier_group_daa.sample_size(sample_size);
    verifier_group_daa.bench_function("ffa daa circuit verifier", |b| {
        b.iter(|| {
            let rel_daa = relations[idx % sample_size];
            let instance = rel_daa.0;
            let c = rel_daa.1;
            let proof = &proofs[idx % sample_size];
            let commitment = &v_inputs[idx % sample_size];
            idx += 1;
            verify_daa(c, &instance, commitment, proof);
        })
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
