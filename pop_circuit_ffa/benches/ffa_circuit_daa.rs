use std::collections::HashMap;

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
use midnight_zk_stdlib::{cost_model, utils::plonk_api::srs_for_test, Relation};
use pop_circuit_ffa::{EcdsaPoPP256Daa, B_FACTORS};
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
    let t = r * c_scalar + q;

    (t, c_u128, (q, r, blinders))
}

fn prove_daa(
    srs: &ParamsKZG<Bls12>,
    c_u128: u128,
    instance: &P256,
    witness: &(P256, P256, [F; 8]),
    rng: OsRng,
) -> Vec<u8> {
    let rel_daa = EcdsaPoPP256Daa::new(c_u128);

    // we include the time to initialize the keys since they depend on the statement
    let vk = midnight_zk_stdlib::setup_vk(srs, &rel_daa);
    let pk = midnight_zk_stdlib::setup_pk(&rel_daa, &vk);

    midnight_zk_stdlib::prove::<EcdsaPoPP256Daa, blake2b_simd::State>(
        srs, &pk, &rel_daa, instance, *witness, rng,
    )
    .expect("proof generation should not fail")
}

fn verify_daa(
    srs: &ParamsKZG<Bls12>,
    c_u128: u128,
    instance: &P256,
    commitment: &G1Projective,
    proof: &[u8],
) {
    let rel_daa = EcdsaPoPP256Daa::new(c_u128);

    // we include the time to initialize the key since they depend on the statement
    let vk = midnight_zk_stdlib::setup_vk(srs, &rel_daa);

    midnight_zk_stdlib::verify::<EcdsaPoPP256Daa, blake2b_simd::State>(
        &srs.verifier_params(),
        &vk,
        instance,
        Some(commitment.into()),
        proof,
    )
    .expect("proof verification should not fail");
}

fn compute_commitment(
    srs: &ParamsKZG<Bls12>,
    c_u128: u128,
    witness: &(P256, P256, [F; 8]),
) -> G1Projective {
    let rel_daa = EcdsaPoPP256Daa::new(c_u128);
    let c_instance = EcdsaPoPP256Daa::format_committed_instances(witness);
    let vk = midnight_zk_stdlib::setup_vk(srs, &rel_daa);
    commit_to_instances::<F, KZGCommitmentScheme<_>>(srs, vk.vk().get_domain(), &c_instance)
        .into_point()
}

fn criterion_benchmark(c: &mut Criterion) {
    let mut rng = OsRng;
    let sample_size = 50;

    let relations: Vec<_> = (0..sample_size).map(|_| get_relation()).collect();

    // one SRS per unique k value across all statements
    let ks: Vec<u32> = relations
        .iter()
        .map(|(_, c_val, _)| cost_model(&EcdsaPoPP256Daa::new(*c_val), None).k)
        .collect();
    let mut unique_ks = ks.clone();
    unique_ks.sort_unstable();
    unique_ks.dedup();
    let srs_map: HashMap<u32, ParamsKZG<Bls12>> = unique_ks
        .into_iter()
        .map(|k| {
            (
                k,
                srs_for_test(&EcdsaPoPP256Daa::new(relations[0].1), Some(k)),
            )
        })
        .collect();

    // prover time
    let mut idx = 0usize;
    let mut prover_group_daa = c.benchmark_group("ffa daa circuit prover");

    let mut proofs = Vec::new();
    prover_group_daa.sample_size(sample_size);
    prover_group_daa.bench_function("ffa daa circuit prover", |b| {
        b.iter(|| {
            let i = idx % sample_size;
            let rel_daa = relations[i];
            let instance = rel_daa.0;
            let c = rel_daa.1;
            let witness = rel_daa.2;
            let srs = &srs_map[&ks[i]];
            idx += 1;
            let proof = prove_daa(srs, c, &instance, &witness, rng);
            proofs.push(proof)
        })
    });
    prover_group_daa.finish();

    let mut idx = 0usize;

    // compute the proofs and commitments to pass to verifier
    let v_inputs: Vec<_> = relations
        .iter()
        .map(|_| {
            let i = idx % sample_size;
            let rel_daa = relations[i];
            let c = rel_daa.1;
            let witness = rel_daa.2;
            let srs = &srs_map[&ks[i]];
            idx += 1;
            compute_commitment(srs, c, &witness)
        })
        .collect();

    // rows avg
    let rows_sum: usize = ks
        .iter()
        .zip(relations.iter())
        .map(|(_, r)| cost_model(&EcdsaPoPP256Daa::new(r.1), None).rows)
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
            let i = idx % sample_size;
            let rel_daa = relations[i];
            let instance = rel_daa.0;
            let c = rel_daa.1;
            let proof = &proofs[idx % sample_size];
            let commitment = &v_inputs[idx % sample_size];
            let srs = &srs_map[&ks[i]];
            idx += 1;
            verify_daa(srs, c, &instance, commitment, proof);
        })
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
