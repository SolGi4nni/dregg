//! ⚑⚑ **THE PRODUCTION LEAF EMITS AT `log_blowup 3`, READ OFF THE ROOT IT ACTUALLY PRODUCED.**
//!
//! `leaf_wrap_mint_blowup_repricing.rs` proves that `ir2_leaf_wrap_split_config()` reaches the
//! prover *when a test hands it to the dispatch*. That is a claim about the dispatch. This file is
//! the other half: that the **production entry points** — the functions the turn chain and the
//! accumulator actually call — reach it too, without any caller naming it.
//!
//! ## Why it has to be a separate claim
//!
//! The production leaves take a `config` argument that is the engine their CHILD (the IR-v2
//! descriptor batch) was minted at, and derive their own wrap engine from it with
//! `recursion_layer_over`. Nothing in the type system distinguishes the two roles — both are
//! `DreggRecursionConfig` — so "the leaf passes the right one" is exactly the kind of fact that
//! stayed false for two months while every test was green (`59b82fa60`: the GPU branch minted at a
//! hardcoded constant and never read its argument). A test that reads `mint_knobs()` off a config
//! object cannot see that; only a test that reads an emitted proof can.
//!
//! So every assertion below is a read of a real root:
//!
//! 1. the **emitted query count** — 38, the split engine's, not the child's 19;
//! 2. the **emitted LDE domain** as Merkle authentication-path depth — `degree_bits + 3`, i.e. the
//!    8× shrink, on the artifact rather than on a knob;
//! 3. it **verifies** at the tower's root config;
//! 4. and **REFUSES** at `ir2_leaf_wrap_config()` — without (4), (1) and (2) could be two labels
//!    on one object.
//!
//! And the dispatch-routed case runs the SAME assertions with `DREGG_GPU_RECURSION` pinned to
//! `cpu` and then `gpu`, because only one of those two branches was ever broken and a gate that
//! takes whichever branch the box offers is the "documented, not detected" shape.
//!
//! ```text
//! cargo test -p dregg-circuit-prove --release --test production_leaves_mint_at_their_own_engine \
//!   -- --nocapture
//! ```

use dregg_circuit::descriptor_ir2::{
    Ir2Air, MemBoundaryWitness, UMemBoundaryWitness, ir2_airs_and_common_for_config,
    prove_vm_descriptor2_for_config,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::membership_descriptor_4ary::{
    Digest8, create_test_witness, membership_descriptor_of_depth_4ary, membership_witness_4ary,
};
use dregg_circuit_prove::gpu_backend::{prove_recursion_layer_auto, recursion_dispatch_counters};
use dregg_circuit_prove::ivc_turn_chain::{
    ir2_leaf_wrap_config, prove_descriptor_leaf_rotated_with_config, turn_chain_root_config,
};
use dregg_circuit_prove::mina_accumulator_fold::{
    accumulator_inner_config, accumulator_root_config,
};
use dregg_circuit_prove::plonky3_recursion_impl::recursive::{
    DreggRecursionConfig, recursion_layer_over, verify_recursive_batch_proof_with_config,
};
use p3_recursion::{RecursionInput, RecursionOutput};

/// The FRI shape of an EMITTED recursion root, read off the proof rather than off a config field.
///
/// `log_lde_domain` is the length of the tallest committed matrix's Merkle authentication path.
/// `cap_height = 0` for this tower, so path length IS tree depth IS `log2` of the committed
/// domain — which is `degree_bits + mint log_blowup`. That is the quantity the repricing moves,
/// measured on the artifact.
struct EmittedFri {
    num_queries: usize,
    log_lde_domain: usize,
    max_degree_bits: usize,
}

fn emitted_fri(root: &RecursionOutput<DreggRecursionConfig>) -> EmittedFri {
    let fri = &root.0.proof.opening_proof;
    EmittedFri {
        num_queries: fri.query_proofs.len(),
        log_lde_domain: fri
            .query_proofs
            .iter()
            .flat_map(|q| q.input_proof.iter())
            .map(|b| b.opening_proof.len())
            .max()
            .unwrap_or(0),
        max_degree_bits: root.0.proof.degree_bits.iter().copied().max().unwrap_or(0),
    }
}

/// One cheap Lean-emitted child at the IR-v2 descriptor engine — depth 2, so this stays a gate
/// rather than a measurement. It is minted at `ir2_leaf_wrap_config()` because that is what a
/// deployed descriptor batch is minted at, and the whole point of the split is that this proof is
/// **unmodified**: the same bytes the old leaf wrap verified.
fn membership_child(
    inner_config: &DreggRecursionConfig,
) -> (
    dregg_circuit::descriptor_ir2::EffectVmDescriptor2,
    dregg_circuit::descriptor_ir2::Ir2BatchProof<DreggRecursionConfig>,
    Vec<BabyBear>,
) {
    let leaf: Digest8 = core::array::from_fn(|k| BabyBear::new(7_000_003 + k as u32));
    let (siblings, positions, _root) = create_test_witness(leaf, 2);
    let desc = membership_descriptor_of_depth_4ary(siblings.len());
    let (trace, pis) = membership_witness_4ary(leaf, &siblings, &positions).expect("witness");
    let proof = prove_vm_descriptor2_for_config::<DreggRecursionConfig>(
        &desc,
        &trace,
        &pis,
        &MemBoundaryWitness::default(),
        &[],
        &UMemBoundaryWitness::default(),
        inner_config,
    )
    .expect("the membership child mints at the IR-v2 descriptor engine");
    (desc, proof, pis)
}

/// The four artifact assertions, run over whatever root was just produced.
fn judge_the_root(label: &str, root: &RecursionOutput<DreggRecursionConfig>) {
    let e = emitted_fri(root);
    println!(
        "{label:<28} EMITTED: {} query proofs, committed LDE domain 2^{} (trace 2^{})",
        e.num_queries, e.log_lde_domain, e.max_degree_bits
    );

    // (1) THE EMITTED QUERY COUNT — the split engine's, not the child's.
    assert_eq!(
        e.num_queries, 38,
        "{label}: the production leaf emitted {} query proofs. 19 means the wrap minted at its \
         CHILD's engine — the split is inert on this path and the 13.8x is not in production.",
        e.num_queries
    );

    // (2) THE EMITTED LDE DOMAIN — `degree_bits + 3`, the 8x shrink on the artifact. At the old
    // engine this would be `degree_bits + 6`.
    assert_eq!(
        e.log_lde_domain,
        e.max_degree_bits + 3,
        "{label}: the committed domain must be the trace domain times the SPLIT mint blowup (8x), \
         not the child's 64x: 2^{} against a 2^{} trace",
        e.log_lde_domain,
        e.max_degree_bits
    );

    // (3) it verifies at the tower's ROOT config…
    verify_recursive_batch_proof_with_config(&root.0, &turn_chain_root_config()).unwrap_or_else(
        |e| panic!("{label}: the emitted root must verify at the root config: {e}"),
    );

    // (4) …and REFUSES at the child's engine. Without this, (1) and (2) are two labels on one
    // object rather than a claim that two distinct objects exist.
    assert!(
        verify_recursive_batch_proof_with_config(&root.0, &ir2_leaf_wrap_config()).is_err(),
        "{label}: a 38-query root must NOT verify under the 19-query engine — if it does, the two \
         engines are not distinguishable and neither assertion above means anything"
    );
}

/// ⚑ **THE PRODUCTION LEAF ENTRY POINT.** `prove_descriptor_leaf_rotated_with_config` is the
/// function every rotated descriptor leaf in the turn chain bottoms out in, and the only config it
/// is ever handed is the child's. Nothing here names the split config; the leaf derives it.
#[test]
fn the_rotated_descriptor_leaf_emits_at_the_split_engine() {
    let inner = ir2_leaf_wrap_config();
    let (desc, proof, pis) = membership_child(&inner);

    let root = prove_descriptor_leaf_rotated_with_config(&desc, &proof, &pis, &inner)
        .expect("the production rotated leaf wrap proves");

    judge_the_root("rotated descriptor leaf", &root);
}

/// ⚑⚑ **AND THE DISPATCH HONOURS IT ON BOTH BRANCHES.** The config under test is exactly the one
/// the production leaves derive — `recursion_layer_over(&ir2_leaf_wrap_config())` — never named
/// as a constant here or there. `DREGG_GPU_RECURSION` is pinned to `cpu` and then `gpu` and the
/// same four assertions run on each: the GPU branch is the one that was minting at a hardcoded
/// `(lb 6, q 19)` while the CPU branch beside it honoured the caller, so a gate that judged one
/// branch would have been green and blind.
#[test]
fn both_dispatch_branches_emit_the_derived_leaf_engine() {
    let inner = ir2_leaf_wrap_config();
    let derived = recursion_layer_over(&inner);
    let (desc, proof, pis) = membership_child(&inner);
    let (airs, table_public_inputs, common) =
        ir2_airs_and_common_for_config(&desc, &proof, &pis, &inner).expect("verify triple");
    let input: RecursionInput<'_, DreggRecursionConfig, Ir2Air> =
        RecursionInput::NativeBatchStark {
            airs: &airs,
            proof: &proof,
            common_data: &common,
            table_public_inputs,
        };

    for policy in ["cpu", "gpu"] {
        // SAFETY: `production_gpu_recursion_enabled()` reads this with no other thread of this
        // binary running a dispatch; nextest gives each test its own process. Same pattern as
        // `gpu_backend_shrink_e2e.rs` and `leaf_wrap_mint_blowup_repricing.rs`.
        unsafe { std::env::set_var("DREGG_GPU_RECURSION", policy) };
        let (gpu0, cpu0) = recursion_dispatch_counters();
        let root = prove_recursion_layer_auto(&input, &derived)
            .expect("the derived leaf-wrap engine proves through the production dispatch");
        let (gpu1, cpu1) = recursion_dispatch_counters();
        let (gpu_ran, cpu_ran) = (gpu1 - gpu0, cpu1 - cpu0);
        println!("\n══ DREGG_GPU_RECURSION={policy} ══ ({gpu_ran} GPU / {cpu_ran} CPU layer)");
        // ⚑ The gate must know WHICH branch it judged. `cpu` is honoured outright; `gpu` may fall
        // back when no adapter exists, but a `cpu` run that dispatched to the GPU would mean the
        // knob is dead and this loop judged one branch twice.
        if policy == "cpu" {
            assert_eq!(
                (gpu_ran, cpu_ran),
                (0, 1),
                "DREGG_GPU_RECURSION=cpu must dispatch to the CPU branch"
            );
        }
        judge_the_root(&format!("dispatch={policy}"), &root);
    }
    unsafe { std::env::remove_var("DREGG_GPU_RECURSION") };
}

/// ⚑ **THE TWO TOWERS AGREE ON WHERE THEIR ROOTS LIVE.** The accumulator and the turn chain are
/// separate fold trees, and each has its own named root config. Both must be the fixed point of
/// `recursion_layer_over`, because a fold verifies what a leaf emits and a leaf emits at the
/// recursion engine — if these ever diverged, one tower's root would be unverifiable by the other
/// tower's reader, which is precisely the shape `dregg-recursion-verify` exists to prevent.
#[test]
fn every_towers_root_config_is_the_same_fixed_point() {
    let chain = turn_chain_root_config();
    let acc = accumulator_root_config();
    assert_eq!(chain.mint_knobs(), acc.mint_knobs());
    assert_eq!(chain.verify_knobs(), acc.verify_knobs());
    assert_eq!(chain.mint_knobs().num_queries, 38);
    assert_eq!(chain.mint_knobs().log_blowup, 3);
    assert_eq!(chain.verify_knobs(), (3, 0, 0, 14));
    // …and the accumulator's INNER config is still the IR-v2 descriptor engine: the child's
    // minting knobs did not move, which is the "verify side bit-for-bit" half of the claim.
    assert_eq!(
        accumulator_inner_config().mint_knobs(),
        ir2_leaf_wrap_config().mint_knobs()
    );
    assert_eq!(
        recursion_layer_over(&accumulator_inner_config()).verify_knobs(),
        (6, 0, 0, 16),
        "the leaf wrap must still check its child at the IR-v2 descriptor engine — this is the \
         assertion that says no child proof's acceptance moved"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// THE SOUNDNESS LEDGER, PER LEAF, AT THE LEAF'S OWN MEASURED HEIGHT
// ─────────────────────────────────────────────────────────────────────────────

/// BCIKS20's proximity parameter, the same `m = 7` `fri_params_soundness_budget.rs` reads every
/// shipped config at. It is a parameter of the ANALYSIS, not of the prover.
const BCIKS_M: usize = 7;

/// ⚑⚑ **THE LEDGER IS RE-DERIVED PER LEAF, NEVER INHERITED — because `ε_C` is a function of the
/// STATEMENT's height, not of the knobs.**
///
/// `ε_C ∝ |D⁽⁰⁾|²` and `|D⁽⁰⁾| = 2^(trace_log_rows + log_blowup)`, so two leaves running identical
/// knobs at different trace heights have different commit columns. The 43 → 53 figure published
/// for this repricing is the ACCUMULATOR leaf wrap at `2^20` rows; quoting it for a leaf of a
/// different height would be inheriting a number rather than deriving one.
///
/// So this test does not take a height as a constant. It **proves the leaf, reads the tallest
/// committed trace domain off the emitted artifact**, and asks Lean's ledger
/// (`Dregg2.Circuit.FriLedger.friLedger`, through `dregg_lean_ffi::fri_ledger` — Rust computes
/// none of this arithmetic) for that leaf's columns under BOTH engines at that height.
///
/// ⚠ The two rows are read at the SAME trace height under each config's OWN blowup, which is the
/// only comparison that means anything: the deployed engine commits `2^(rows+6)`, the split one
/// `2^(rows+3)`, and the smaller domain is half of why the commit column improves.
#[test]
fn each_switched_leaf_gets_its_own_ledger_at_its_own_height() {
    use dregg_lean_ffi::{FriKnobs, fri_ledger, fri_ledger_available};

    assert!(
        fri_ledger_available(),
        "the VERIFIED Lean FRI ledger is not in the linked archive, so this test cannot report any \
         leaf's soundness numbers — and it must NOT compute them in Rust. Rebuild: `lake build \
         Dregg2.Circuit.FriLedger` in metatheory/, then `cargo build -p dregg-lean-ffi`."
    );

    let inner = ir2_leaf_wrap_config();
    let (desc, proof, pis) = membership_child(&inner);
    let root = prove_descriptor_leaf_rotated_with_config(&desc, &proof, &pis, &inner)
        .expect("the production rotated leaf wrap proves");
    let e = emitted_fri(&root);
    // The trace height is a MEASUREMENT of this leaf, read off its own proof.
    let log_rows = e.max_degree_bits;

    let row = |c: &DreggRecursionConfig| {
        let k = c.mint_knobs();
        fri_ledger(FriKnobs {
            log_blowup: k.log_blowup,
            num_queries: k.num_queries,
            query_pow_bits: k.query_pow_bits,
            max_log_arity: k.max_log_arity,
            log_final_poly_len: k.log_final_poly_len,
            ext_deg: 4,
            log_d0: log_rows + k.log_blowup,
            bciks_m: BCIKS_M,
            commit_pow_bits: k.commit_pow_bits,
        })
        .expect("Lean's ledger")
    };

    let deployed = row(&inner);
    let split = row(&recursion_layer_over(&inner));

    println!(
        "\nTHE ROTATED DESCRIPTOR LEAF WRAP — tallest committed trace 2^{log_rows}, MEASURED off \
         the emitted root, not assumed:\n  \
         {:<14} log_d0 {:>3}  commit {:>3}  johnson {:>3}  johnson@m {:>3}  capacity {:>3}  \
         per-fold {:>3}  composite {:>3}\n  \
         {:<14} log_d0 {:>3}  commit {:>3}  johnson {:>3}  johnson@m {:>3}  capacity {:>3}  \
         per-fold {:>3}  composite {:>3}",
        "deployed lb6",
        log_rows + 6,
        deployed.commit_pow_branch,
        deployed.johnson_bits,
        deployed.johnson_bits_at_m,
        deployed.capacity_bits,
        deployed.per_fold_bits,
        deployed.composite_bits,
        "split lb3",
        log_rows + 3,
        split.commit_pow_branch,
        split.johnson_bits,
        split.johnson_bits_at_m,
        split.capacity_bits,
        split.per_fold_bits,
        split.composite_bits,
    );

    // ⚑ THE ONE THING THAT MUST HOLD, WHATEVER THE HEIGHT: the composite — ethSTARK eq. (20) at one
    // `m`, with both grinding terms — must not FALL. The split trades 2 bits of capacity column for
    // a much larger gain on the commit branch, and at every height where the commit branch is what
    // binds, the composite rises. This asserts the direction rather than a constant, because the
    // constant is a function of a height this test measures.
    assert!(
        split.composite_bits >= deployed.composite_bits,
        "the split must not lower this leaf's composite column at its own height 2^{log_rows}: \
         {} -> {}. If this fires, the leaf is TALLER than the regime where the commit branch binds \
         and the trade has reversed — the fix is to report it, not to relax this.",
        deployed.composite_bits,
        split.composite_bits,
    );
    // …and the capacity column lands ON the standing drift margin, not below it.
    assert_eq!(split.capacity_bits, 128);
    assert_eq!(deployed.capacity_bits, 130);
}

// ─────────────────────────────────────────────────────────────────────────────
// THE MEASUREMENT — the ROTATED DESCRIPTOR LEAF, which had no published number
// ─────────────────────────────────────────────────────────────────────────────
//
// ⚠ `maxrss` and `peak memory footprint` are PROCESS-level, so each engine gets its own
// `#[ignore]`d test and each must be run ALONE under `/usr/bin/time -l`. Running them concurrently
// (with each other, or with any sibling proving job) makes both numbers meaningless — that is how
// "~72 GiB, no box can host it" got written down about two baselines racing each other.
//
//   /usr/bin/time -l cargo test -p dregg-circuit-prove --release \
//     --test production_leaves_mint_at_their_own_engine -- --ignored --nocapture \
//     the_rotated_leaf_at_the_deployed_engine
//   /usr/bin/time -l cargo test -p dregg-circuit-prove --release \
//     --test production_leaves_mint_at_their_own_engine -- --ignored --nocapture \
//     the_rotated_leaf_at_the_split_engine
//
// SAME BINARY, SAME BOX, one after the other, nothing else running.

/// Time and shape ONE rotated descriptor leaf wrap at an explicitly named pair of engines, and
/// refuse to report a number for the wrong object.
fn measure_rotated_leaf(label: &str, wrap: &DreggRecursionConfig, expect_queries: usize) {
    use std::time::Instant;
    let inner = ir2_leaf_wrap_config();
    let (desc, proof, pis) = membership_child(&inner);
    let (airs, table_public_inputs, common) =
        ir2_airs_and_common_for_config(&desc, &proof, &pis, &inner).expect("verify triple");
    let input: RecursionInput<'_, DreggRecursionConfig, Ir2Air> =
        RecursionInput::NativeBatchStark {
            airs: &airs,
            proof: &proof,
            common_data: &common,
            table_public_inputs,
        };

    let t = Instant::now();
    let root = prove_recursion_layer_auto(&input, wrap).expect("the leaf wrap proves");
    let wall = t.elapsed().as_secs_f64();

    let e = emitted_fri(&root);
    let (gpu, cpu) = recursion_dispatch_counters();
    println!(
        "\n{label}: {wall:.2} s\n  EMITTED: {} query proofs, committed LDE domain 2^{} \
         (trace 2^{})\n  dispatch: {gpu} GPU / {cpu} CPU layer(s)\n  \
         (maxrss + peak footprint come from `/usr/bin/time -l` around THIS process)",
        e.num_queries, e.log_lde_domain, e.max_degree_bits
    );
    // ⚑ The measurement refuses to publish a number for an object it did not time. Without this,
    // a run that silently took the other engine reports its wall clock under this label — which is
    // precisely what produced the retracted "≥72 GiB" figure.
    assert_eq!(
        e.num_queries, expect_queries,
        "{label} did not mint at the engine it claims; the number above is not this engine's"
    );
    verify_recursive_batch_proof_with_config(&root.0, wrap)
        .expect("the emitted root verifies at the engine it was minted under");
}

/// ⚑ **THE BASELINE.** The single-engine tower the rotated descriptor leaf ran at until the split:
/// verify AND mint both at `ir2_leaf_wrap_config()`. Reached only by naming the same config twice,
/// because the production entry point derives its wrap engine now.
#[test]
#[ignore = "MEASUREMENT. Run ALONE under /usr/bin/time -l, immediately before/after its split twin."]
fn the_rotated_leaf_at_the_deployed_engine() {
    let inner = ir2_leaf_wrap_config();
    measure_rotated_leaf("DEPLOYED (mint lb6/q19, verify lb6/q19)", &inner, 19);
}

/// ⚑ **THE SPLIT.** Identical child, identical in-circuit verification of it, identical
/// verification circuit — the only difference is the blowup this layer commits its OWN trace at.
/// This is exactly what the production leaf now does; the config is DERIVED here too.
#[test]
#[ignore = "MEASUREMENT. Run ALONE under /usr/bin/time -l, immediately before/after its deployed twin."]
fn the_rotated_leaf_at_the_split_engine() {
    let wrap = recursion_layer_over(&ir2_leaf_wrap_config());
    measure_rotated_leaf("SPLIT    (mint lb3/q38, verify lb6/q19)", &wrap, 38);
}
