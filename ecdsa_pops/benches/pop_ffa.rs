#![allow(non_snake_case)]

use std::path::Path;

use criterion::Criterion;
use ecdsa_pops::{
    utils::ecdsa::ECDSA, FFACircuitRoK, PoPFFANizk, RelECDSA, RelECDSAParams, RelECDSAStatement,
    RelECDSAWitness,
};
use ff::Field;
use halo2curves::{
    bls12381::{Fr as BLS_SCALAR, G1Affine},
    secp256r1::{Fq, Secp256r1Affine},
};
use merlin::Transcript;
use midnight_zk_stdlib::utils::plonk_api::srs_for_test;
use pop_circuit_ffa::EcdsaPoPP256;
use rand_core::OsRng;
use rok::{Nizk, Relation};

#[macro_use]
extern crate criterion;

const NB_BITS_C: usize = 128;

fn setup_ffa_circuit_rok() -> FFACircuitRoK<NB_BITS_C> {
    let relation = EcdsaPoPP256::<NB_BITS_C>;
    let k = midnight_zk_stdlib::cost_model(&relation, None).k;
    let asset_srs_dir = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("workspace root")
        .join("pop_circuit_ffa")
        .join("examples")
        .join("assets");
    std::env::set_var("SRS_DIR", asset_srs_dir);
    let srs = srs_for_test(&relation, Some(k));
    let vk = midnight_zk_stdlib::setup_vk(&srs, &relation);
    let pk = midnight_zk_stdlib::setup_pk(&relation, &vk);
    FFACircuitRoK::from_parts(srs, vk, pk)
}

fn sample_random_ecdsa_instance(nizk: &PoPFFANizk) -> RelECDSA<G1Affine, 2> {
    // create parameters
    let ecdsa = ECDSA {
        pp: Secp256r1Affine::generator(),
    };
    let Gs = [*nizk.ck_bls(), *nizk.ck_bls()];
    let H = nizk.ck_bls_blinding();
    let pp = RelECDSAParams::<G1Affine, 2>::new(Gs, *H, ecdsa);

    // sample a random keypair
    let (sk, pk) = ecdsa.keygen(&mut OsRng);

    // sample a random message and sign it
    let m = Fq::random(OsRng);
    let sigma = ecdsa.sign_prehashed(&sk, &m, &mut OsRng).unwrap();
    let sigma_converted = ecdsa.convert(&pk, &m, &sigma);

    // sample randomness for the commitments
    let rho: [BLS_SCALAR; 2] = (0..2)
        .map(|_| <BLS_SCALAR>::random(OsRng))
        .collect::<Vec<_>>()
        .try_into()
        .unwrap();
    // create witness
    let w = RelECDSAWitness::new(pk, sigma_converted.z, rho, None);
    // create the commitment to the public key
    let C = (0..2)
        .map(|i| RelECDSA::<G1Affine, 2>::create_commitment(&pp, &w, i).unwrap().0)
        .collect::<Vec<_>>()
        .try_into()
        .unwrap();
    let x = RelECDSAStatement::new(C, None, m, sigma_converted.K);
    RelECDSA::new(pp, x, Some(w))
}

fn criterion_benchmark(c: &mut Criterion) {
    let label = "Bench popffa";
    let (ck_bls, ck_bls_blinding) = PoPFFANizk::plain_commitment_params(label);
    let ffa_circuit_rok = setup_ffa_circuit_rok();
    let nizk = PoPFFANizk::from_parts(ck_bls, ck_bls_blinding, ffa_circuit_rok).unwrap();
    let r_prover = sample_random_ecdsa_instance(&nizk);
    let r_verifier = RelECDSA::new(
        r_prover.params().clone(),
        r_prover.statement().clone(),
        None,
    );
    let sample_size = 100;
    // prover time
    let mut prover_group = c.benchmark_group("pop-ffa prover");
    prover_group.sample_size(sample_size);
    prover_group.bench_function("pop-ffa prover", |b| {
        b.iter(|| {
            let mut transcript = Transcript::new(b"Benchmark PoP FFA");
            nizk.prove(&mut transcript, &r_prover, &mut OsRng)
        })
    });
    prover_group.finish();
    // proof size
    let proof_bytes = {
        let mut transcript = Transcript::new(b"Benchmark PoP FFA");
        let proof = nizk.prove(&mut transcript, &r_prover, &mut OsRng).unwrap();
        bincode::serialize(&proof).unwrap()
    };
    println!("Proof size: {}", proof_bytes.len());

    // Verifier time
    let mut verifier_group = c.benchmark_group("pop-ffa verifier");

    verifier_group.sample_size(sample_size);
    verifier_group.bench_function("pop-ffa verifier", |b| {
        b.iter(|| {
            let mut transcript = Transcript::new(b"Benchmark PoP FFA");
            let proof = bincode::deserialize(&proof_bytes).unwrap();
            nizk.verify(&mut transcript, &r_verifier, &proof).unwrap()
        })
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
