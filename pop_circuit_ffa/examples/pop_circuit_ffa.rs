use std::time::Instant;

use ff::Field;
use group::Group;
use midnight_circuits::CircuitField;
use midnight_curves::p256::{Fq as P256Scalar, P256};
use midnight_proofs::{plonk::commit_to_instances, poly::kzg::KZGCommitmentScheme};
use midnight_zk_stdlib::{cost_model, utils::plonk_api::srs_for_test, Relation};
use pop_circuit_ffa::{EcdsaPoPP256, EcdsaPoPP256Daa, B_FACTORS};
use rand::{rngs::OsRng, Rng};

type F = midnight_curves::Fq;

pub const NB_BITS_C: usize = 96;

fn main() {
    let mut rng = OsRng;

    // ── Generate a valid witness ─────────────────────────────────────────────
    let q = P256::random(&mut rng);
    let r = P256::random(&mut rng);
    let blinders = [0; B_FACTORS].map(|_| F::random(&mut rng));

    let c_u128: u128 = rng.gen::<u128>() & ((1u128 << NB_BITS_C) - 1);
    let c_bits: Vec<bool> = (0..NB_BITS_C).map(|i| (c_u128 >> i) & 1 == 1).collect();
    let popcount = c_bits.iter().filter(|&&b| b).count();

    let mut c_be = [0u8; 32];
    c_be[16..].copy_from_slice(&c_u128.to_be_bytes());
    let c_scalar = P256Scalar::from_bytes_be(&c_be).expect("valid bounded scalar");
    let t = r + q * c_scalar;

    println!("c: {NB_BITS_C}-bit scalar, popcount = {popcount}");

    // ── Compare circuit sizes ─────────────────────────────────────────────────
    let rel_windowed = EcdsaPoPP256::<NB_BITS_C>;
    let rel_daa = EcdsaPoPP256Daa::new(c_u128);

    let m_w = cost_model(&rel_windowed, None);
    let m_d = cost_model(&rel_daa, None);

    println!(
        "Windowed WS=4:  k={}, {} / {} rows  ({} advice, {} fixed, {} lookups)",
        m_w.k,
        m_w.rows,
        1u64 << m_w.k,
        m_w.advice_columns,
        m_w.fixed_columns,
        m_w.lookups,
    );
    println!(
        "Double-and-add: k={}, {} / {} rows  ({} advice, {} fixed, {} lookups)",
        m_d.k,
        m_d.rows,
        1u64 << m_d.k,
        m_d.advice_columns,
        m_d.fixed_columns,
        m_d.lookups,
    );

    // ── Full proof flow for the smaller circuit ───────────────────────────────
    let instance_windowed = (t.clone(), c_u128);
    if m_w.rows <= m_d.rows {
        println!("\nRunning full proof with windowed WS=4 (fewer rows).");
        run_proof(
            rel_windowed,
            m_w.k,
            &instance_windowed,
            (q, r, blinders),
            rng,
        );
    } else {
        println!("\nRunning full proof with double-and-add (fewer rows).");
        run_proof(rel_daa, m_d.k, &t, (q, r, blinders), rng);
    }
}

fn run_proof<Rel>(
    relation: Rel,
    k: u32,
    instance: &Rel::Instance,
    witness: Rel::Witness,
    rng: OsRng,
) where
    Rel: Relation,
    Rel::Error: std::fmt::Debug,
{
    let srs = srs_for_test(&relation, Some(k));

    let t_vk = Instant::now();
    let vk = midnight_zk_stdlib::setup_vk(&srs, &relation);
    println!("VK generation:      {:?}", t_vk.elapsed());

    let t_pk = Instant::now();
    let pk = midnight_zk_stdlib::setup_pk(&relation, &vk);
    println!("PK generation:      {:?}", t_pk.elapsed());

    let t_prove = Instant::now();
    let proof = midnight_zk_stdlib::prove::<Rel, blake2b_simd::State>(
        &srs,
        &pk,
        &relation,
        instance,
        witness.clone(),
        rng,
    )
    .expect("proof generation should not fail");
    println!(
        "Proof generation:   {:?}  ({} bytes)",
        t_prove.elapsed(),
        proof.len()
    );
    println!("Full prove (including pk/vk):      {:?}", t_vk.elapsed());

    let c_instance = Rel::format_committed_instances(&witness);
    let commitment =
        commit_to_instances::<F, KZGCommitmentScheme<_>>(&srs, vk.vk().get_domain(), &c_instance);

    let t_verify = Instant::now();
    assert!(
        midnight_zk_stdlib::verify::<Rel, blake2b_simd::State>(
            &srs.verifier_params(),
            &vk,
            instance,
            Some(commitment.into()),
            &proof,
        )
        .is_ok(),
        "proof verification failed"
    );
    println!("Proof verification: {:?}", t_verify.elapsed());
}
