//! ⚑⚑ **THE THREE MINA TOWERS EMIT AT `log_blowup 3`, READ OFF THE ROOTS THEY ACTUALLY PRODUCED.**
//!
//! `production_leaves_mint_at_their_own_engine.rs` says this about the turn chain's and the
//! accumulator's leaves. Those two towers were switched when the IR-v2 leaf wrap's mint was split;
//! **the phase-2 chain, the wrap-finalize fold and the kimchi-verifier gadget were deliberately left
//! whole**, each with a docblock saying so, and this file is the gate that says they no longer are.
//!
//! ## ⚠ WHY THIS CANNOT BE A TEST ABOUT CONFIG OBJECTS
//!
//! Every function in these towers takes a `config: &DreggRecursionConfig` that is the engine its
//! CHILD was minted at, and derives its own minting engine with `recursion_layer_over`. Nothing in
//! the type system distinguishes the two roles — both are `DreggRecursionConfig` — so "the leaf
//! passes the right one" is exactly the fact that stayed false for two months while every test was
//! green (`59b82fa60`: the GPU branch minted at a hardcoded constant and never read its argument).
//! **A test that reads `mint_knobs()` off a config object cannot see that.** So every assertion
//! below is a read of a real emitted proof:
//!
//! 1. the **emitted query count** — 38, the recursion engine's, not the IR-v2 descriptor batch's 19;
//! 2. the **emitted LDE domain** as Merkle authentication-path depth — `degree_bits + 3`, i.e. the
//!    8× shrink, on the artifact rather than on a knob;
//! 3. it **verifies** at that tower's root config;
//! 4. and **REFUSES** at that tower's inner config — without (4), (1) and (2) could be two labels
//!    on one object rather than a claim that two distinct engines exist.
//!
//! …and each runs with `DREGG_GPU_RECURSION` pinned to `cpu` and then `gpu`, because only one of
//! those two branches was ever broken and a gate that takes whichever branch the box offers is the
//! "documented, not detected" shape.
//!
//! ## ⚑ WHICH DISPATCHES THIS COVERS, STATED RATHER THAN IMPLIED
//!
//! These towers reach the prover through exactly two functions:
//! `gpu_backend::prove_recursion_layer_auto_with_expose` (every leaf) and
//! `gpu_backend::prove_recursion_aggregation_auto_with_expose` (every fold, including the kimchi
//! gadget's). Both are exercised here on both branches — the leaf path by the chain leaf and the
//! endo-lift leaf, the aggregation path by the chain fold.
//!
//! ⚠ **The kimchi gadget's OWN root is not minted here, and that is a property of the gadget rather
//! than an omission.** It accepts only a chain root whose incoming state is `(0,0,0)` *and* whose
//! outgoing lane 0 truncates to block 539508's `v′` — only the real 46-link fold has both, so there
//! is no cheap positive to judge (`mina_kimchi_verifier_gadget.rs` §"THERE IS NO CHEAP POSITIVE").
//! Its artifact assertions live in that file's §4, which asserts the emitted query count and
//! committed domain of all three roots and their refusal at the descriptor engine.
//!
//! ## ⚑⚑ MEASURED 2026-08-08 — same binary, same box, the two `#[ignore]`d halves back to back
//!
//! ```text
//!                        deployed lb6      split lb3      ratio
//!  CHAIN LEAF   wall         34.86 s        24.15 s       1.44x
//!               maxrss        8.51 GiB       1.89 GiB     4.50x
//!               footprint    13.32 GiB       1.88 GiB     7.09x
//!               LDE domain     2^22           2^19          8x   (trace 2^16)
//!  ENDO LEAF    wall         38.46 s        25.20 s       1.53x
//!               maxrss       12.47 GiB       2.19 GiB     5.69x
//!               footprint    18.77 GiB       3.22 GiB     5.83x
//!               LDE domain     2^23           2^20          8x   (trace 2^17)
//!  CONJ LEAF    wall            ---          74.27 s        --
//!               maxrss          ---          14.97 GiB      --
//!               footprint       ---          21.47 GiB      --
//!               LDE domain      2^26          2^23          8x   (trace 2^20)
//! ```
//!
//! ⚠ **THE WALL-CLOCK COLUMN IS THE WEAK ONE AND IS QUOTED LAST FOR THAT REASON.** These ran on a
//! 96 GiB M2 Max at load ~90 with sibling lanes proving; two runs twenty minutes apart on this box
//! differ by 2× from co-tenancy alone. The **memory ratios are box-independent** — they are
//! allocation, not scheduling — and the **LDE domain is exact**: it is read off the emitted proof's
//! Merkle authentication-path length, not computed.
//!
//! ⚠ **The conjunction leaf's DEPLOYED column is empty and that is a measurement that was not
//! taken, not a small number.** See `the_conjunction_leaf_at_the_deployed_engine`.
//!
//! ## PREREQUISITE — two chain-link witnesses
//!
//! ```text
//! cd metatheory && lake build mina_chain_emit
//! ./.lake/build/bin/mina_chain_emit ../circuit/tests/fixtures/pasta-fq-chainlink 4
//! ```
//!
//! ```text
//! cargo test -p dregg-circuit-prove --release --test mina_towers_mint_at_their_own_engine \
//!   -- --nocapture --test-threads=1
//! ```

use std::path::PathBuf;

use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::fold_vk_pin::FoldVkPins;
use dregg_circuit_prove::gpu_backend::recursion_dispatch_counters;
use dregg_circuit_prove::mina_phase2_chain_leaf::{
    CHAIN_PI_COUNT, chain_inner_config, chain_root_config, fold_chain_links, prove_chain_link_leaf,
};
use dregg_circuit_prove::mina_wrap_finalize_fold::{
    ENDO_PI_COUNT, finalize_inner_config, finalize_root_config, prove_endo_lift_leaf,
};
use dregg_circuit_prove::plonky3_recursion_impl::recursive::{
    DreggRecursionConfig, recursion_layer_over, verify_recursive_batch_proof_with_config,
};
use dregg_recursion_verify::kimchi_root::kimchi_root_config;
use p3_recursion::RecursionOutput;

const ENDO_TRACE: &str = include_str!("../../circuit/tests/fixtures/mina-xi-endo-lift-trace.txt");
const ENDO_PIS: &str = include_str!("../../circuit/tests/fixtures/mina-xi-endo-lift-pis.txt");
const CONJ_TRACE: &str =
    include_str!("../../circuit/tests/fixtures/mina-wrap-conjunction-trace.txt");
const CONJ_PIS: &str = include_str!("../../circuit/tests/fixtures/mina-wrap-conjunction-pis.txt");
const CHAIN_PIS_ALL: &str = include_str!("../../circuit/tests/fixtures/pasta-fq-chainlink-pis.txt");
const ENDO_TRACE_WIDTH: usize = 687;
const CONJ_TRACE_WIDTH: usize = 2536;

/// The recursion engine's query count — the number the split moves the towers TO. Read from the
/// config the rule generates rather than typed as a literal, so a retune of
/// `create_recursion_config` cannot leave this file asserting a number nobody mints at.
fn tower_queries() -> usize {
    chain_root_config().mint_knobs().num_queries
}

/// …and its mint blowup, the exponent the committed domain must sit `degree_bits` above.
fn tower_log_blowup() -> usize {
    chain_root_config().mint_knobs().log_blowup
}

/// The FRI shape of an EMITTED artifact, read off the proof rather than off a config field.
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

fn emitted_fri(out: &RecursionOutput<DreggRecursionConfig>) -> EmittedFri {
    let fri = &out.0.proof.opening_proof;
    EmittedFri {
        num_queries: fri.query_proofs.len(),
        log_lde_domain: fri
            .query_proofs
            .iter()
            .flat_map(|q| q.input_proof.iter())
            .map(|b| b.opening_proof.len())
            .max()
            .unwrap_or(0),
        max_degree_bits: out.0.proof.degree_bits.iter().copied().max().unwrap_or(0),
    }
}

/// The four artifact assertions, run over whatever root was just produced.
fn judge_the_root(
    label: &str,
    out: &RecursionOutput<DreggRecursionConfig>,
    root_config: &DreggRecursionConfig,
    inner_config: &DreggRecursionConfig,
) {
    let e = emitted_fri(out);
    println!(
        "{label:<34} EMITTED: {} query proofs, committed LDE domain 2^{} (trace 2^{})",
        e.num_queries, e.log_lde_domain, e.max_degree_bits
    );

    // (1) THE EMITTED QUERY COUNT — the recursion engine's, not the IR-v2 descriptor batch's.
    assert_eq!(
        e.num_queries,
        tower_queries(),
        "{label}: emitted {} query proofs. {} means the layer minted at its CHILD's engine — the \
         split is inert on this path and the 8x is not in this tower.",
        e.num_queries,
        inner_config.mint_knobs().num_queries,
    );

    // (2) THE EMITTED LDE DOMAIN — `degree_bits + 3`, the 8x shrink on the artifact. At the old
    // single-engine shape this would be `degree_bits + 6`.
    assert_eq!(
        e.log_lde_domain,
        e.max_degree_bits + tower_log_blowup(),
        "{label}: the committed domain must be the trace domain times the recursion engine's mint \
         blowup, not the descriptor engine's: 2^{} over a 2^{} trace",
        e.log_lde_domain,
        e.max_degree_bits
    );

    // (3) it verifies at the tower's ROOT config…
    verify_recursive_batch_proof_with_config(&out.0, root_config)
        .unwrap_or_else(|e| panic!("{label}: must verify at its tower's root config: {e}"));

    // (4) …and REFUSES at the descriptor engine. Without this, (1) and (2) are two labels on one
    // object rather than a claim that two distinct objects exist.
    assert!(
        verify_recursive_batch_proof_with_config(&out.0, inner_config).is_err(),
        "{label}: a {}-query artifact must NOT verify under the {}-query descriptor engine — if it \
         does, the two engines are not distinguishable and neither assertion above means anything",
        e.num_queries,
        inner_config.mint_knobs().num_queries,
    );
}

/// ⚑ **ONE PROVING JOB AT A TIME IN THIS BINARY, AND IT IS NOT POLITENESS.**
///
/// Two reasons, both of which have bitten this tree. (1) `recursion_dispatch_counters()` is
/// process-global, so a sibling test proving concurrently would land in the delta this file reads
/// and `with_dispatch`'s branch attribution would be measuring someone else. (2)
/// `DREGG_GPU_RECURSION` is process-global too — two tests setting it at once would each judge
/// whichever branch the other happened to pick. ⚠ And a third, which is the reason the wrap-finalize
/// tower's own tests ask for `--test-threads=1`: concurrent recursion wraps of wide descriptors are
/// how a harness gets SIGKILLed, which reads as a test failure and is an environment fault.
///
/// A `--test-threads=1` flag would fix all three and be invisible the first time someone forgets
/// it. This is the same discipline as a structural refusal rather than a remembered one.
static PROVE_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

fn prove_alone<T>(f: impl FnOnce() -> T) -> T {
    // A poisoned lock means a SIBLING test panicked, not that this one may not run.
    let _g = PROVE_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    f()
}

/// Pin the dispatch policy and report which branch actually ran.
///
/// ⚑ The gate must know WHICH branch it judged. `cpu` is honoured outright; `gpu` may fall back
/// when no adapter exists, but a `cpu` run that dispatched to the GPU would mean the knob is dead
/// and the loop judged one branch twice.
fn with_dispatch<T>(policy: &str, layers: u64, f: impl FnOnce() -> T) -> T {
    // SAFETY: `production_gpu_recursion_enabled()` reads this with no other thread of this binary
    // running a dispatch; `--test-threads=1` and nextest's process-per-test both give that. Same
    // pattern as `production_leaves_mint_at_their_own_engine.rs` and `gpu_backend_shrink_e2e.rs`.
    unsafe { std::env::set_var("DREGG_GPU_RECURSION", policy) };
    let (gpu0, cpu0) = recursion_dispatch_counters();
    let out = f();
    // ⚠ Cleared HERE, inside the caller's `prove_alone` guard. Clearing it after the loop would
    // leave a window where a concurrent test's layer reads a policy this one had already finished
    // with — `production_gpu_recursion_enabled()` is consulted per layer, not once per run.
    unsafe { std::env::remove_var("DREGG_GPU_RECURSION") };
    let (gpu1, cpu1) = recursion_dispatch_counters();
    let (gpu_ran, cpu_ran) = (gpu1 - gpu0, cpu1 - cpu0);
    println!("\n══ DREGG_GPU_RECURSION={policy} ══ ({gpu_ran} GPU / {cpu_ran} CPU layer)");
    assert_eq!(
        gpu_ran + cpu_ran,
        layers,
        "expected {layers} dispatched layer(s) under policy {policy}, saw {gpu_ran}+{cpu_ran}"
    );
    if policy == "cpu" {
        assert_eq!(
            (gpu_ran, cpu_ran),
            (0, layers),
            "DREGG_GPU_RECURSION=cpu must dispatch every layer to the CPU branch"
        );
    }
    out
}

// ── fixtures ─────────────────────────────────────────────────────────────────────────────────

fn parse_cells(text: &str) -> Vec<BabyBear> {
    text.split_whitespace()
        .map(|c| BabyBear::new(c.parse::<u32>().expect("cell is a u32 decimal")))
        .collect()
}

fn parse_trace(text: &str, width: usize) -> Vec<Vec<BabyBear>> {
    let t: Vec<Vec<BabyBear>> = text
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(parse_cells)
        .collect();
    assert!(!t.is_empty(), "an empty trace measures nothing");
    assert!(t.iter().all(|r| r.len() == width));
    t
}

fn all_link_pis() -> Vec<Vec<BabyBear>> {
    let pis: Vec<Vec<BabyBear>> = CHAIN_PIS_ALL
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(parse_cells)
        .collect();
    assert!(pis.iter().all(|p| p.len() == CHAIN_PI_COUNT));
    pis
}

fn witness_dir() -> PathBuf {
    std::env::var("DREGG_CHAINLINK_WITNESS_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|_| {
            PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("../circuit/tests/fixtures/pasta-fq-chainlink")
        })
}

/// Read link `j`'s Lean-emitted 2048x469 trace. Fails LOUDLY with the emit command rather than
/// skipping: a test that quietly does nothing when its input is absent is not a gate.
fn link_trace(j: usize) -> Vec<Vec<BabyBear>> {
    let path = witness_dir().join(format!("link-{j}-trace.txt"));
    let text = std::fs::read_to_string(&path).unwrap_or_else(|e| {
        panic!(
            "chain-link witness {} missing ({e}).\n\
             Emit it first (COMPILED — the interpreter costs 9m20s per link):\n  \
             cd metatheory && lake build mina_chain_emit \\\n    \
             && ./.lake/build/bin/mina_chain_emit ../circuit/tests/fixtures/pasta-fq-chainlink 4",
            path.display()
        )
    });
    parse_trace(&text, 469)
}

// ─────────────────────────────────────────────────────────────────────────────
// TOWER 1 — the phase-2 chain: a LEAF and a FOLD, both dispatch branches
// ─────────────────────────────────────────────────────────────────────────────

/// ⚑⚑ **THE PHASE-2 CHAIN LEAF AND FOLD BOTH EMIT AT THE DERIVED ENGINE, ON BOTH BRANCHES.**
///
/// The leaf exercises `prove_recursion_layer_auto_with_expose` and the fold exercises
/// `prove_recursion_aggregation_auto_with_expose` — the two dispatch functions every layer of all
/// three Mina towers goes through. Nothing here names the split config: `prove_chain_link_leaf`
/// derives its wrap engine from the inner config it is handed, and `fold_chain_links` runs at the
/// tower's root config, which is `recursion_layer_over`'s fixed point.
#[test]
fn the_phase2_chain_leaf_and_fold_emit_at_the_derived_engine() {
    let pis = all_link_pis();
    let inner = chain_inner_config();
    let root = chain_root_config();

    for policy in ["cpu", "gpu"] {
        // 2 leaves + 1 aggregation = 3 dispatched layers.
        let (l0, l1, node) = prove_alone(|| {
            with_dispatch(policy, 3, || {
                let l0 =
                    prove_chain_link_leaf(&link_trace(0), &pis[0], &inner).expect("link 0 leaf");
                let l1 =
                    prove_chain_link_leaf(&link_trace(1), &pis[1], &inner).expect("link 1 leaf");
                let node = fold_chain_links(
                    &l0,
                    &l1,
                    &FoldVkPins::tracked(&l0, &l1)
                        .expect("both children carry a preprocessed commit"),
                    &root,
                )
                .expect("links 0..1 fold");
                (l0, l1, node)
            })
        });
        judge_the_root(
            &format!("chain leaf   dispatch={policy}"),
            &l0,
            &root,
            &inner,
        );
        judge_the_root(
            &format!("chain leaf'  dispatch={policy}"),
            &l1,
            &root,
            &inner,
        );
        judge_the_root(
            &format!("chain fold   dispatch={policy}"),
            &node,
            &root,
            &inner,
        );
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// TOWER 2 — wrap-finalize: the endo-lift leaf, both dispatch branches
// ─────────────────────────────────────────────────────────────────────────────

/// ⚑ **THE WRAP-FINALIZE TOWER'S LEAF EMITS AT THE DERIVED ENGINE, ON BOTH BRANCHES.**
///
/// The endo-lift leaf and not the conjunction leaf, deliberately: the conjunction is 2 536 columns
/// and its wrap was measured at roughly **38 GiB** of pressure on 2026-08-07, which is not a thing
/// a gate should demand of a shared box. Both leaves go through the same
/// `prove_ir2_leaf` body and therefore the same derivation; the conjunction's own artifact is
/// judged in `mina_wrap_finalize_fold.rs` §4, which mints it once.
#[test]
fn the_wrap_finalize_endo_leaf_emits_at_the_derived_engine() {
    let inner = finalize_inner_config();
    let root = finalize_root_config();
    let trace = parse_trace(ENDO_TRACE, ENDO_TRACE_WIDTH);
    let pis = parse_cells(ENDO_PIS);
    assert_eq!(pis.len(), ENDO_PI_COUNT);

    for policy in ["cpu", "gpu"] {
        let leaf = prove_alone(|| {
            with_dispatch(policy, 1, || {
                prove_endo_lift_leaf(&trace, &pis, &inner).expect("the endo-lift leaf")
            })
        });
        judge_the_root(
            &format!("endo leaf    dispatch={policy}"),
            &leaf,
            &root,
            &inner,
        );
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// THE ALGEBRA — labelled as algebra, and not doing the artifact's job
// ─────────────────────────────────────────────────────────────────────────────

/// ⚑ **ALL FIVE TOWERS AGREE ON WHERE THEIR ROOTS LIVE.** Each fold tree has its own named root
/// config; all must be the fixed point of `recursion_layer_over`, because a fold verifies what a
/// leaf emits and a leaf emits at the recursion engine. For these three the requirement is sharper
/// than taste: the kimchi gadget FOLDS a phase-2 chain root and a wrap-finalize root in one
/// aggregation circuit, and an aggregation of two proofs minted at different FRI engines does not
/// build at all.
///
/// ⚠ This is a claim about CONFIG OBJECTS, which is exactly what was already true while the split
/// was inert. It is here for the cross-tower equality, not as evidence that anything minted.
#[test]
fn the_three_mina_towers_share_one_root_engine_and_one_inner_engine() {
    let chain = chain_root_config();
    let fin = finalize_root_config();
    let kimchi = kimchi_root_config();

    for (name, c) in [("finalize", &fin), ("kimchi", &kimchi)] {
        assert_eq!(
            c.mint_knobs(),
            chain.mint_knobs(),
            "{name} root mints at a different engine than the chain root — the gadget folds both \
             in one circuit and could not"
        );
        assert_eq!(c.verify_knobs(), chain.verify_knobs());
    }
    // The fixed point, reached by the rule rather than asserted as a literal.
    assert_eq!(
        recursion_layer_over(&chain).mint_knobs(),
        chain.mint_knobs(),
        "a tower root config must be recursion_layer_over's FIXED POINT"
    );
    assert_eq!(
        recursion_layer_over(&chain).verify_knobs(),
        chain.verify_knobs()
    );

    // …and the INNER engines did not move: the child proofs are the same bytes, checked by the
    // same in-circuit verifier. This is the "no child's acceptance moved" half.
    let chain_inner = chain_inner_config();
    let fin_inner = finalize_inner_config();
    assert_eq!(fin_inner.mint_knobs(), chain_inner.mint_knobs());
    assert_eq!(
        recursion_layer_over(&chain_inner).verify_knobs(),
        (6, 0, 0, 16),
        "a Mina leaf wrap must still check its IR-v2 child at the descriptor engine"
    );
    assert_ne!(
        chain_inner.mint_knobs().num_queries,
        chain.mint_knobs().num_queries,
        "the inner and root engines must be DISTINGUISHABLE, or judge_the_root's refusal leg is \
         checking nothing"
    );
    println!(
        "\nthe three Mina towers: inner {:?} → root {:?}",
        chain_inner.mint_knobs(),
        chain.mint_knobs()
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// THE SOUNDNESS LEDGER, RE-DERIVED PER TOWER AT EACH TOWER'S OWN MEASURED HEIGHT
// ─────────────────────────────────────────────────────────────────────────────

/// BCIKS20's proximity parameter, the same `m = 7` `fri_params_soundness_budget.rs` reads every
/// shipped config at. It is a parameter of the ANALYSIS, not of the prover.
const BCIKS_M: usize = 7;

/// ⚑⚑ **THE LEDGER IS RE-DERIVED PER TOWER, NEVER INHERITED — because `ε_C` is a function of the
/// STATEMENT's height, not of the knobs.**
///
/// `ε_C ∝ |D⁽⁰⁾|²` and `|D⁽⁰⁾| = 2^(trace_log_rows + log_blowup)`, so two layers running identical
/// knobs at different trace heights have different commit columns. The **43 → 53** figure published
/// for this repricing is the IR-v2 leaf wrap at `2^20` rows; quoting it for the phase-2 chain leaf
/// or the endo-lift leaf would be inheriting a number rather than deriving one, and the two towers
/// do not even have the same height as each other.
///
/// So this test takes no height as a constant. It **proves each tower's leaf, reads the tallest
/// committed trace domain off the emitted artifact**, and asks Lean's ledger
/// (`Dregg2.Circuit.FriLedger.friLedger`, through `dregg_lean_ffi::fri_ledger` — Rust computes none
/// of this arithmetic) for that leaf's columns under BOTH engines at that height.
///
/// ⚑ **What is NOT re-derived, because it is the same object in every row: the knob set.** The
/// mint half of every switched layer IS `create_recursion_config`'s — the weakest config already
/// shipped — so no new knob posture is introduced by this change in any of the three towers. That
/// is asserted below per tower rather than inherited from the leaf-wrap campaign's write-up.
///
/// ## ⚑⚑ MEASURED 2026-08-08 — and NEITHER TOWER'S `ε_C` IS THE PUBLISHED 43 → 53
///
/// ```text
///   phase-2 chain leaf, trace 2^16 (MEASURED off the emitted root)
///     deployed lb6   log_d0 22   commit 51   johnson 73   @m 71   capacity 130   composite 50
///     split    lb3   log_d0 19   commit 61   johnson 71   @m 67   capacity 128   composite 60
///   wrap-finalize endo leaf, trace 2^17
///     deployed lb6   log_d0 23   commit 49   johnson 73   @m 71   capacity 130   composite 48
///     split    lb3   log_d0 20   commit 59   johnson 71   @m 67   capacity 128   composite 58
/// ```
///
/// The commit branch moves **51 → 61** for the chain leaf and **49 → 59** for the endo leaf. The
/// figure published for this repricing was **43 → 53**, and that is the IR-v2 leaf wrap at `2^20`
/// rows: a taller statement, a larger `|D⁽⁰⁾|`, a weaker commit column. Quoting it here would have
/// been inheriting a number. The composite rises **+10 bits** in both towers, and the Johnson and
/// capacity columns fall by 2 in both — the trade is the same trade, priced at each height.
///
/// ⚠ **The kimchi gadget has no row here, and the reason is structural.** Its only layer is a fold
/// of two roots, and there is no cheap positive to mint one from (see the file header). What holds
/// for it without a measurement is the knob-set half: its mint engine IS the fold engine both rows
/// above already price at capacity 128, so it introduces no posture this file has not judged. Its
/// heights are reported by `mina_kimchi_verifier_gadget.rs` §4.
#[test]
fn each_mina_tower_gets_its_own_ledger_at_its_own_height() {
    use dregg_lean_ffi::{FriKnobs, fri_ledger, fri_ledger_available};

    assert!(
        fri_ledger_available(),
        "the VERIFIED Lean FRI ledger is not in the linked archive, so this test cannot report any \
         tower's soundness numbers — and it must NOT compute them in Rust. Rebuild: `lake build \
         Dregg2.Circuit.FriLedger` in metatheory/, then `cargo build -p dregg-lean-ffi`."
    );

    let row = |c: &DreggRecursionConfig, log_rows: usize| {
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
            // ⚑ Lean's field is `commit_pow`, Rust's `MintKnobs` spells it `commit_pow_bits`; the
            // field maps to `FriLedger::commit_pow_branch` one-for-one and is the ONLY lever on
            // that branch — the branch this split actually moves. A wrong name here prices a
            // config nobody runs while looking green.
            commit_pow: k.commit_pow_bits,
        })
        .expect("Lean's ledger")
    };

    // ── the two towers whose leaves are cheap enough to mint here. Each height is MEASURED.
    let pis = all_link_pis();
    let chain_inner = chain_inner_config();
    let fin_inner = finalize_inner_config();
    let (chain_leaf, endo_leaf) = prove_alone(|| {
        (
            prove_chain_link_leaf(&link_trace(0), &pis[0], &chain_inner)
                .expect("the phase-2 chain leaf proves"),
            prove_endo_lift_leaf(
                &parse_trace(ENDO_TRACE, ENDO_TRACE_WIDTH),
                &parse_cells(ENDO_PIS),
                &fin_inner,
            )
            .expect("the endo-lift leaf proves"),
        )
    });

    for (tower, inner, leaf) in [
        ("phase-2 chain leaf", &chain_inner, &chain_leaf),
        ("wrap-finalize endo leaf", &fin_inner, &endo_leaf),
    ] {
        let log_rows = emitted_fri(leaf).max_degree_bits;
        let deployed = row(inner, log_rows);
        let split = row(&recursion_layer_over(inner), log_rows);

        println!(
            "\n{tower} — tallest committed trace 2^{log_rows}, MEASURED off the emitted root:\n  \
             {:<14} log_d0 {:>3}  commit {:>3}  johnson {:>3}  johnson@m {:>3}  capacity {:>3}  \
             per-fold {:>3}  composite {:>3}\n  \
             {:<14} log_d0 {:>3}  commit {:>3}  johnson {:>3}  johnson@m {:>3}  capacity {:>3}  \
             per-fold {:>3}  composite {:>3}",
            "deployed lb6",
            log_rows + inner.mint_knobs().log_blowup,
            deployed.commit_pow_branch,
            deployed.johnson_bits,
            deployed.johnson_bits_at_m,
            deployed.capacity_bits,
            deployed.per_fold_bits,
            deployed.composite_bits,
            "split lb3",
            log_rows + recursion_layer_over(inner).mint_knobs().log_blowup,
            split.commit_pow_branch,
            split.johnson_bits,
            split.johnson_bits_at_m,
            split.capacity_bits,
            split.per_fold_bits,
            split.composite_bits,
        );

        // ⚑ THE ONE THING THAT MUST HOLD, WHATEVER THE HEIGHT: the composite — ethSTARK eq. (20)
        // at one `m`, with both grinding terms — must not FALL. This asserts the DIRECTION rather
        // than a constant, because the constant is a function of a height this test measures.
        assert!(
            split.composite_bits >= deployed.composite_bits,
            "{tower}: the split lowered the composite column at its own height 2^{log_rows}: \
             {} -> {}. If this fires, this tower's leaf is TALLER than the regime where the commit \
             branch binds and the trade has reversed — the fix is to REPORT it, not to relax this.",
            deployed.composite_bits,
            split.composite_bits,
        );
        // …and the capacity column lands ON the standing drift margin, not below it — per tower,
        // confirmed, never inherited.
        assert_eq!(
            split.capacity_bits, 128,
            "{tower}: the split half's capacity column must be create_recursion_config's 3·38+14"
        );
        assert_eq!(
            deployed.capacity_bits, 130,
            "{tower}: the deployed half's capacity column must be the IR-v2 engine's 6·19+16"
        );
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// THE MEASUREMENT — one leaf per tower, at BOTH engines, in ONE binary
// ─────────────────────────────────────────────────────────────────────────────
//
// ⚠ `maxrss` and `peak memory footprint` are PROCESS-level, so each engine gets its own
// `#[ignore]`d test and each must be run ALONE under `/usr/bin/time -l`. Running two proving jobs
// concurrently — with each other, or with any sibling lane's — makes both numbers meaningless. That
// is how "~72 GiB, no box can host it" got written down about two baselines racing each other, and
// neither of those runs had even applied the split.
//
//   /usr/bin/time -l cargo test -p dregg-circuit-prove --release \
//     --test mina_towers_mint_at_their_own_engine -- --ignored --nocapture \
//     the_chain_leaf_at_the_deployed_engine
//   /usr/bin/time -l cargo test -p dregg-circuit-prove --release \
//     --test mina_towers_mint_at_their_own_engine -- --ignored --nocapture \
//     the_chain_leaf_at_the_split_engine
//
// SAME BINARY, SAME BOX, one after the other, nothing else running. ⚠ Two runs twenty minutes
// apart can differ 2× from co-tenancy alone, so a pair run far apart is not a pair.

/// Time and shape ONE leaf at an explicitly named pair of engines, and refuse to publish a number
/// for the wrong object.
fn measure_leaf(
    label: &str,
    expect_queries: usize,
    prove: impl FnOnce() -> RecursionOutput<DreggRecursionConfig>,
) {
    let t = std::time::Instant::now();
    let out = prove_alone(prove);
    let wall = t.elapsed().as_secs_f64();

    let e = emitted_fri(&out);
    let (gpu, cpu) = recursion_dispatch_counters();
    println!(
        "\n{label}: {wall:.2} s\n  EMITTED: {} query proofs, committed LDE domain 2^{} \
         (trace 2^{})\n  dispatch: {gpu} GPU / {cpu} CPU layer(s)\n  \
         (maxrss + peak footprint come from `/usr/bin/time -l` around THIS process)",
        e.num_queries, e.log_lde_domain, e.max_degree_bits
    );
    // ⚑ The measurement refuses to publish a number for an object it did not time. Without this, a
    // run that silently took the other engine reports its wall clock under this label.
    assert_eq!(
        e.num_queries, expect_queries,
        "{label} did not mint at the engine it claims; the number above is not this engine's"
    );
}

/// ⚑ **THE PHASE-2 CHAIN LEAF'S BASELINE.** The single-engine tower this leaf ran at until
/// 2026-08-08: verify AND mint both at the IR-v2 descriptor engine. Reachable only by naming the
/// same config twice, because the production entry point derives its wrap engine now.
#[test]
#[ignore = "MEASUREMENT. Run ALONE under /usr/bin/time -l, immediately before/after its split twin."]
fn the_chain_leaf_at_the_deployed_engine() {
    use dregg_circuit_prove::mina_phase2_chain_leaf::{
        chain_link_descriptor, prove_chain_link_leaf_split,
    };
    let pis = all_link_pis();
    let inner = chain_inner_config();
    let desc = chain_link_descriptor().expect("the Lean chain-link descriptor parses");
    let trace = link_trace(0);
    measure_leaf(
        "CHAIN LEAF  DEPLOYED (mint lb6/q19, verify lb6/q19)",
        19,
        || {
            prove_chain_link_leaf_split(&desc, &trace, &pis[0], &inner, &inner)
                .expect("the chain leaf proves at the deployed engine")
        },
    );
}

/// ⚑ **THE PHASE-2 CHAIN LEAF, SPLIT.** Identical child, identical in-circuit verification of it,
/// identical verification circuit — the only difference is the blowup this layer commits its OWN
/// trace at. This is exactly what `prove_chain_link_leaf` now does; the config is DERIVED here too.
#[test]
#[ignore = "MEASUREMENT. Run ALONE under /usr/bin/time -l, immediately before/after its deployed twin."]
fn the_chain_leaf_at_the_split_engine() {
    let pis = all_link_pis();
    let inner = chain_inner_config();
    let trace = link_trace(0);
    measure_leaf(
        "CHAIN LEAF  SPLIT    (mint lb3/q38, verify lb6/q19)",
        38,
        || {
            prove_chain_link_leaf(&trace, &pis[0], &inner)
                .expect("the chain leaf proves at the split")
        },
    );
}

/// ⚑ **THE WRAP-FINALIZE ENDO LEAF'S BASELINE.** 687 columns × 2 048 rows; the recorded
/// single-engine figure was 55.7 s on 2026-08-06 and 14.0 s on 2026-08-07, on the same shape —
/// which is exactly why this file re-measures rather than quoting either.
#[test]
#[ignore = "MEASUREMENT. Run ALONE under /usr/bin/time -l, immediately before/after its split twin."]
fn the_endo_leaf_at_the_deployed_engine() {
    use dregg_circuit_prove::mina_wrap_finalize_fold::prove_endo_lift_leaf_split;
    let inner = finalize_inner_config();
    let trace = parse_trace(ENDO_TRACE, ENDO_TRACE_WIDTH);
    let pis = parse_cells(ENDO_PIS);
    measure_leaf(
        "ENDO LEAF   DEPLOYED (mint lb6/q19, verify lb6/q19)",
        19,
        || {
            prove_endo_lift_leaf_split(&trace, &pis, &inner, &inner)
                .expect("the endo leaf proves at the deployed engine")
        },
    );
}

/// ⚑ **THE WRAP-FINALIZE ENDO LEAF, SPLIT.**
#[test]
#[ignore = "MEASUREMENT. Run ALONE under /usr/bin/time -l, immediately before/after its deployed twin."]
fn the_endo_leaf_at_the_split_engine() {
    let inner = finalize_inner_config();
    let trace = parse_trace(ENDO_TRACE, ENDO_TRACE_WIDTH);
    let pis = parse_cells(ENDO_PIS);
    measure_leaf(
        "ENDO LEAF   SPLIT    (mint lb3/q38, verify lb6/q19)",
        38,
        || prove_endo_lift_leaf(&trace, &pis, &inner).expect("the endo leaf proves at the split"),
    );
}

/// ⚑⚑ **THE CONJUNCTION LEAF — the 2 536-column wrap that was measured at roughly 38 GiB of
/// pressure at the single-engine shape, and killed a watchdog run on 2026-08-07.**
///
/// It gets its own pair because it is the one layer in these three towers whose memory, not its
/// wall clock, decided whether the tower could run at all. ⚠ **Run the DEPLOYED one under a
/// watchdog and expect it to be expensive**; a killed run bounds nothing from above and the only
/// honest report of one is "killed at the cap".
///
/// ⚠⚠ **AND THE DEPLOYED HALF OF THIS PAIR HAS STILL NOT BEEN MEASURED — READ WHAT IS AND IS NOT
/// KNOWN.** On 2026-08-07 it was run under a 30 GiB RSS watchdog and the watchdog **killed it**;
/// the sampled figure at the kill was 26.05 GiB, and the system-free swing around it put the true
/// pressure near **38 GiB**. Both of those are FLOORS on a peak that was never reached, and a
/// killed run bounds nothing from above. On 2026-08-08 the split half was measured cleanly at
/// **21.47 GiB peak footprint / 14.97 GiB maxrss** — and the deployed twin was deliberately NOT
/// re-run, because the box was at load 88 with sibling proving jobs and 8× the committed domain of
/// a 2^20 trace does not fit a 96 GiB machine that is already busy. So the honest before/after for
/// THIS layer is "did not fit under a 30 GiB cap" against "21.47 GiB, clean exit", and the ratio is
/// unknown rather than large. Run this on a quiet box to close it.
#[test]
#[ignore = "MEASUREMENT. Run ALONE, on a QUIET box, under a watchdog. The deployed twin killed a 30 GiB cap on 2026-08-07."]
fn the_conjunction_leaf_at_the_deployed_engine() {
    use dregg_circuit_prove::mina_wrap_finalize_fold::prove_conjunction_leaf_split;
    let inner = finalize_inner_config();
    let trace = parse_trace(CONJ_TRACE, CONJ_TRACE_WIDTH);
    let pis = parse_cells(CONJ_PIS);
    measure_leaf(
        "CONJ LEAF   DEPLOYED (mint lb6/q19, verify lb6/q19)",
        19,
        || {
            prove_conjunction_leaf_split(&trace, &pis, &inner, &inner)
                .expect("the conjunction leaf proves at the deployed engine")
        },
    );
}

/// ⚑⚑ **THE CONJUNCTION LEAF, SPLIT.**
#[test]
#[ignore = "MEASUREMENT. Run ALONE under /usr/bin/time -l, immediately before/after its deployed twin."]
fn the_conjunction_leaf_at_the_split_engine() {
    use dregg_circuit_prove::mina_wrap_finalize_fold::prove_conjunction_leaf;
    let inner = finalize_inner_config();
    let trace = parse_trace(CONJ_TRACE, CONJ_TRACE_WIDTH);
    let pis = parse_cells(CONJ_PIS);
    measure_leaf(
        "CONJ LEAF   SPLIT    (mint lb3/q38, verify lb6/q19)",
        38,
        || {
            prove_conjunction_leaf(&trace, &pis, &inner)
                .expect("the conjunction leaf proves at split")
        },
    );
}
