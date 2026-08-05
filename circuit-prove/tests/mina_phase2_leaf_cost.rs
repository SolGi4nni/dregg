//! ⚑ **WHAT ONE Fq-SPONGE LINK COSTS AS A RECURSION LEAF** — the measurement the 46-permutation
//! residual was never priced against.
//!
//! Every "the residual is 45 witnesses" note priced the WITNESS (207 MB of trace text) and stopped.
//! The number that decides whether a 46-link chain is reachable is the LEAF WRAP: minting the IR2
//! batch proof over one 2048x469 Lean-emitted trace, then verifying that batch IN-CIRCUIT and
//! proving the wrap. This file measures both halves on the deployed `dregg-pasta-fq-wraplink::v1`
//! instance, so the chain's cost is derived from a measured leaf rather than asserted.
//!
//! Run: `cargo test -p dregg-circuit-prove --release --test mina_phase2_leaf_cost -- --nocapture`

use std::time::Instant;

use dregg_circuit::descriptor_ir2::{
    MemBoundaryWitness, UMemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2_for_config,
    verify_vm_descriptor2_with_config,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::ivc_turn_chain::{
    ir2_leaf_wrap_config, prove_descriptor_leaf_rotated_with_config,
};
use dregg_circuit_prove::plonky3_recursion_impl::recursive::{
    DreggRecursionConfig, verify_recursive_batch_proof_with_config,
};

const LINK_DESC_JSON: &str =
    include_str!("../../circuit/descriptors/by-name/pasta-fq-wraplink.json");
const LINK_TRACE: &str = include_str!("../../circuit/tests/fixtures/pasta-fq-wraplink-trace.txt");
const LINK_PIS: &str = include_str!("../../circuit/tests/fixtures/pasta-fq-wraplink-pis.txt");

fn parse_trace(text: &str) -> Vec<Vec<BabyBear>> {
    text.lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| {
            l.split_whitespace()
                .map(|c| BabyBear::new(c.parse::<u32>().expect("cell is a u32 decimal")))
                .collect()
        })
        .collect()
}

fn parse_pis(text: &str) -> Vec<BabyBear> {
    text.split_whitespace()
        .map(|c| BabyBear::new(c.parse::<u32>().expect("PI is a u32 decimal")))
        .collect()
}

#[test]
fn one_fq_sponge_link_wraps_as_a_recursion_leaf() {
    let desc = parse_vm_descriptor2(LINK_DESC_JSON).expect("wrap-link descriptor parses");
    let trace = parse_trace(LINK_TRACE);
    let pis = parse_pis(LINK_PIS);
    assert_eq!(trace.len(), 2048);
    assert_eq!(pis.len(), 224);

    let config = ir2_leaf_wrap_config();

    let t0 = Instant::now();
    let inner = prove_vm_descriptor2_for_config::<DreggRecursionConfig>(
        &desc,
        &trace,
        &pis,
        &MemBoundaryWitness::default(),
        &[],
        &UMemBoundaryWitness::default(),
        &config,
    )
    .expect("the Lean-emitted link proves as an IR2 batch under the leaf-wrap config");
    let inner_ms = t0.elapsed().as_millis();

    let t1 = Instant::now();
    verify_vm_descriptor2_with_config(&desc, &inner, &pis, &config).expect("inner batch verifies");
    let inner_verify_ms = t1.elapsed().as_millis();

    let t2 = Instant::now();
    let leaf = prove_descriptor_leaf_rotated_with_config(&desc, &inner, &pis, &config)
        .expect("the link wraps in-circuit as a recursion leaf");
    let wrap_ms = t2.elapsed().as_millis();

    let t3 = Instant::now();
    verify_recursive_batch_proof_with_config(&leaf.0, &config).expect("wrapped leaf verifies");
    let leaf_verify_ms = t3.elapsed().as_millis();

    println!("\n═══ ONE Fq-SPONGE LINK AS A RECURSION LEAF (measured) ═══");
    println!("  inner IR2 batch prove : {inner_ms:>7} ms   (2048 rows x 469 declared cols)");
    println!("  inner batch verify    : {inner_verify_ms:>7} ms");
    println!("  LEAF WRAP (in-circuit verify + prove) : {wrap_ms:>7} ms");
    println!("  wrapped leaf verify   : {leaf_verify_ms:>7} ms");
    println!(
        "  ⇒ per-leaf total {:.1} s; 46 leaves = {:.1} min of leaf work alone",
        (inner_ms + wrap_ms) as f64 / 1000.0,
        (inner_ms + wrap_ms) as f64 * 46.0 / 60_000.0
    );
}
