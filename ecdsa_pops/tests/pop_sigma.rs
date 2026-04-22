use ecdsa_pops::{
    utils::{ecdsa::ECDSA, Fq},
    PoPSigmaNizk, RelECDSA, RelECDSAParams, RelECDSAStatement, RelECDSAWitness,
};
use ff::Field;
use halo2curves::{
    bls12381::{Fr as BLS_SCALAR, G1Affine},
    secp256r1::Secp256r1Affine,
};
use merlin::Transcript;
use rand_core::OsRng;
use rok::{Nizk, Relation};

#[test]
fn pop_sigma_nizk() {
    // create parameters
    let nizk = PoPSigmaNizk::new("PoP sigma intergration test");

    // sample a random statement
    let ecdsa = ECDSA {
        pp: Secp256r1Affine::generator(),
    };
    let gs = [*nizk.ck_bls(), *nizk.ck_bls()];
    let h = nizk.ck_bls_blinding();
    let pp = RelECDSAParams::<G1Affine, 2>::new(gs, *h, ecdsa);

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

    let r_prover = RelECDSA::new(pp, x, Some(w));

    // the statement of the verifier
    let r_verifier = RelECDSA::new(
        r_prover.params().clone(),
        r_prover.statement().clone(),
        None,
    );

    let mut transcript_prover = Transcript::new(b"pop sigma proof");
    let proof = nizk.prove(&mut transcript_prover, &r_prover, &mut OsRng).unwrap();

    let bytes = bincode::serialize(&proof).unwrap();
    println!("proof size: {} bytes", bytes.len());

    let mut transcript_verifier = Transcript::new(b"pop sigma proof");
    let result = nizk.verify(&mut transcript_verifier, &r_verifier, &proof);

    assert!(result.is_ok(), "nizk failed: {:?}", result);
}
