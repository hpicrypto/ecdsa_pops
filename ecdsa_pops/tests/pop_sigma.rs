use ark_ec::short_weierstrass::SWCurveConfig;
use ff::Field;
use halo2curves::{
    bls12381::{Fr as BLS_SCALAR, G1Affine},
    secp256r1::Secp256r1Affine,
};

use merlin::Transcript;

use pedersen::pedersen_config::PedersenConfig;

use rand_core::OsRng;

use ecdsa_pops::{
    utils::{cdls_t256_to_t256, ecdsa::ECDSA, Fq},
    PoPSigmaNizk, RelECDSA, RelECDSAParams, RelECDSAStatement, RelECDSAWitness,
};
use rok::{Nizk, Relation};

/// End-to-end integration test for the sigma-based ECDSA proof-of-possession.
///
/// It shows functional correctness of the composed RoK
/// `((SMRoK x PARoK) o GroupRoK) o BlsToTomRoK` on an honestly-generated input:
/// an ECDSA keypair is created, a message is signed, the signature is committed
/// to via the BLS-side commitment scheme, a NIZK proof is produced, and the
/// proof verifies.
///
#[test]
fn pop_sigma_nizk() {
    // CDLS-aligned T256 generators.
    let cdls_g = <t256::Config as SWCurveConfig>::GENERATOR;
    let cdls_h = <t256::Config as PedersenConfig>::GENERATOR2;
    let halo_g = cdls_t256_to_t256(&cdls_g);
    let halo_h = cdls_t256_to_t256(&cdls_h);

    // Create parameters
    // BLS-side generators are derived via hash-to-curve from the label inside
    let nizk = PoPSigmaNizk::new_with_t256_key("PoP sigma intergration test", halo_g, halo_h);

    // ECDSA
    // Sample a random statement
    let ecdsa = ECDSA {
        pp: Secp256r1Affine::generator(),
    };
    let gs = [*nizk.ck_bls(), *nizk.ck_bls()];
    let h = nizk.ck_bls_blinding();
    let pp = RelECDSAParams::<G1Affine, 2>::new(gs, *h, ecdsa);

    // Sample a random ECDSA keypair
    let (sk, pk) = ecdsa.keygen(&mut OsRng);

    // Sample a random message and sign it with the keypair
    let m = Fq::random(OsRng);
    let sigma = ecdsa.sign_prehashed(&sk, &m, &mut OsRng).unwrap();
    let sigma_converted = ecdsa.convert(&pk, &m, &sigma);

    // Assemble the witness
    // Sample randomness for the commitments
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

    // Create witness
    let w = RelECDSAWitness::new(pk, sigma_converted.z, rho_x, Some(rho_y));

    // Create the commitment to the public key
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

    // The statement of the verifier
    let r_verifier = RelECDSA::new(
        r_prover.params().clone(),
        r_prover.statement().clone(),
        None,
    );

    // And now we prove
    let mut transcript_prover = Transcript::new(b"pop sigma proof");
    let proof = nizk.prove(&mut transcript_prover, &r_prover, &mut OsRng).unwrap();
    let bytes = bincode::serialize(&proof).unwrap();
    println!("proof size: {} bytes", bytes.len());

    let mut transcript_verifier = Transcript::new(b"pop sigma proof");
    let result = nizk.verify(&mut transcript_verifier, &r_verifier, &proof);
    assert!(result.is_ok(), "nizk failed: {:?}", result);
}
