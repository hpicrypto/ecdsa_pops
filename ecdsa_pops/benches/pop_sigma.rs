#![allow(non_snake_case)]

use criterion::Criterion;
use ecdsa_pops::{
    utils::ecdsa::ECDSA, PoPSigmaNizk, RelECDSA, RelECDSAParams, RelECDSAStatement, RelECDSAWitness,
};
use ff::Field;
use halo2curves::{
    bls12381::{Fr as BLS_SCALAR, G1Affine},
    secp256r1::{Fq, Secp256r1Affine},
};
use merlin::Transcript;
use rand_core::OsRng;
use rok::{Nizk, Relation};

#[macro_use]
extern crate criterion;

fn sample_random_ecdsa_instance(nizk: &PoPSigmaNizk) -> RelECDSA<G1Affine, 2> {
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
    let rho_x: [BLS_SCALAR; 2] = (0..2)
        .map(|_| <BLS_SCALAR>::random(OsRng))
        .collect::<Vec<_>>()
        .try_into()
        .unwrap();
    let rho_y: [BLS_SCALAR; 2] = (0..2)
        .map(|_| <BLS_SCALAR>::random(OsRng))
        .collect::<Vec<_>>()
        .try_into()
        .unwrap();
    // create witness
    let w = RelECDSAWitness::new(pk, sigma_converted.z, rho_x, Some(rho_y));
    // create the commitment to the public key
    let coms_x = (0..2)
        .map(|i| RelECDSA::<G1Affine, 2>::create_commitment(&pp, &w, i).unwrap().0)
        .collect::<Vec<_>>()
        .try_into()
        .unwrap();
    let coms_y = (0..2)
        .map(|i| RelECDSA::<G1Affine, 2>::create_commitment(&pp, &w, i).unwrap().1.unwrap())
        .collect::<Vec<_>>()
        .try_into()
        .unwrap();
    let x = RelECDSAStatement::new(coms_x, Some(coms_y), m, sigma_converted.K);

    RelECDSA::new(pp, x, Some(w))
}

fn criterion_benchmark(c: &mut Criterion) {
    let nizk = PoPSigmaNizk::new("Bench popsigma");
    let r_prover = sample_random_ecdsa_instance(&nizk);
    let r_verifier = RelECDSA::new(
        r_prover.params().clone(),
        r_prover.statement().clone(),
        None,
    );
    let sample_size = 50;
    // prover time
    let mut prover_group = c.benchmark_group("pop-sigma prover");
    prover_group.sample_size(sample_size);
    prover_group.bench_function("pop-sigma prover", |b| {
        b.iter(|| {
            let mut transcript = Transcript::new(b"Benchmark PoP Sigma");
            nizk.prove(&mut transcript, &r_prover, &mut OsRng)
        })
    });
    prover_group.finish();
    // proof size
    let proofs = (0..sample_size)
        .map(|_| {
            let mut transcript = Transcript::new(b"Benchmark PoP Sigma");
            nizk.prove(&mut transcript, &r_prover, &mut OsRng).unwrap()
        })
        .map(|proof| bincode::serialize(&proof).unwrap())
        .collect::<Vec<_>>();

    println!("Proof size: {}", proofs[1].len());

    // Verifier time
    let mut idx = 0usize;
    let mut verifier_group = c.benchmark_group("pop-sigma verifier");
    verifier_group.sample_size(sample_size);
    verifier_group.bench_function("pop-sigma verifier", |b| {
        b.iter(|| {
            let proof_bytes = &proofs[idx % proofs.len()];
            idx += 1;

            let mut transcript = Transcript::new(b"Benchmark PoP Sigma");
            let proof = bincode::deserialize(proof_bytes).unwrap();
            nizk.verify(&mut transcript, &r_verifier, &proof).unwrap()
        })
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
