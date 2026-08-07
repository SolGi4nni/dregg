//! ⚑⚑ **THE "COST WALL" IS A CONFIG CONFLATION, AND THIS IS THE MEASUREMENT.**
//!
//! `mina_accumulator_fold.rs`'s header prices ONE eight-row accumulator leaf — eight Vesta complete
//! additions — at **223.36 s / 48.85 GiB maxrss / 117.93 GiB peak footprint**, and its test file
//! concludes *"AND NO UNLOADED BOX IN THE FLEET CAN HOST IT."* That number is real. What it measures
//! is not eight curve additions.
//!
//! ⚑ **BOTH ARE NOW RETIRED, MEASURED (2026-08-07): the same leaf, minting at its own blowup, is
//! 21.63 s / 18.65 GiB maxrss / 23.23 GiB peak footprint.** persvati hosts it; so does a 32 GiB
//! laptop. The table below is the derivation; the measurement is at the bottom of this section.
//!
//! ## The two engines, and only one of them is constrained
//!
//! A recursion layer runs TWO FRI engines:
//!
//! | engine | object | who fixes it |
//! |--------|--------|--------------|
//! | **VERIFY** | `DreggRecursionConfig::fri_verifier_params` | the CHILD — it must be the knobs the child proof was minted at. Not a choice. |
//! | **MINT** | `StarkConfig`'s `TwoAdicFriPcs` → `FriParameters::log_blowup` | THIS layer. `two_adic_pcs.rs:317` LDEs every committed matrix by `2^log_blowup`. A free choice. |
//!
//! `create_recursion_config_with_fri` set both from one argument (`recursion-verify/src/config.rs`,
//! pre-split), so the deepest child's blowup became the whole tower's blowup. The IR-v2 descriptor
//! batch is minted at `IR2_INNER_LOG_BLOWUP = 6` — **64×** — and that 64× was then applied to the
//! WRAP's own trace, which is ~10^3 times larger than the descriptor's.
//!
//! Its own doc comment already said the two were separable and then accepted the tie:
//!
//! > *"'the blowup my child was minted at' and 'the blowup I mint at' are the same number by
//! > construction. **They are two different proofs' knobs.**"*
//!
//! ## ⚑ WHAT IT IS WORTH, MEASURED — and it is NOT the whole wall
//!
//! The leaf wrap's own tables, extracted at the DEPLOYED packing and profile
//! (`ProveNextLayerParams::default()` — `TablePacking::new(1, 4)`, `ConstraintProfile::Standard`,
//! `min_trace_height = 1`), for the 8-row `-final` accumulator segment:
//!
//! ```text
//! table                             log2       rows   main   prep    trace cells    LDE @lb6    LDE @lb3
//! Const                               14      16,384     4      6        163,840  10,485,760   1,310,720
//! Public                              13       8,192     4      2         49,152   3,145,728     393,216
//! Alu                                 20   1,048,576    76     59    141,557,760  9.06e9        1.13e9
//! poseidon2_perm/baby_bear_d4_w16     18     262,144   300     24     84,934,656  5.44e9        6.79e8
//! recompose                           20   1,048,576     4      2      6,291,456   4.03e8        5.03e7
//! expose_claim                         0           1   768    384          1,152      73,728       9,216
//! TOTAL                                                            232,998,016  14,911,873,024  1,863,984,128
//!                                                                              55.6 GiB       6.9 GiB
//! ```
//!
//! So the split removes **48.7 GiB of committed LDE** from a leaf whose completed footprint is
//! 117.79 GiB. ⚑ **AND THE FOOTPRINT FALLS BY FAR MORE THAN THE LDE DOES** — measured 2026-08-07,
//! both runs from ONE binary on ONE box, minutes apart, each alone under `/usr/bin/time -l`:
//!
//! ```text
//!                          wall        maxrss                 peak footprint          LDE domain
//!   deployed (lb6/q19)   298.08 s   46.47 GiB / 49.90 GB   117.79 GiB / 126.47 GB      2^26
//!   split    (lb3/q38)    21.63 s   18.65 GiB / 20.02 GB    23.23 GiB /  24.95 GB      2^23
//!                          13.8x            2.49x                   5.07x               8x
//! ```
//!
//! ⚠ **Part of the 13.8× is a memory cliff, and saying so is not a hedge.** The deployed run's
//! footprint (117.79 GiB) EXCEEDS this box's 96 GiB of RAM, and its `sys` time (348.27 s) is 2.5×
//! its `user` time (138.93 s) — it spends most of its life in the compressor. The split never gets
//! near the cliff. On a box with ≥128 GiB the deployed side would be faster and the wall-clock ratio
//! smaller; the MEMORY ratios are the box-independent ones. ⚠ Both runs were taken on a box under
//! load average ~21–34 from sibling work, which the wall clock feels and the footprint does not.
//!
//! ⚑ Two other things this table settles. **The preprocessed side is not the wall** — 30.2% of the
//! cells, and the only manifest-shaped table in the wrap (`expose_claim`) is ONE row. **And rows are
//! not the wall either**: `mina_accumulator_leaf_anatomy` measures 1 → 8 inner rows moving the wrap
//! by +0.54% in ops and 0% in cells. What IS the wall is `Q · W`: 19 queries against the child's
//! **10,756 committed** columns (3,048 declared; 71.7% of the committed row is `LIMB_BITS = 4`
//! range-check decomposition).
//!
//! ## What the split does, and does not
//!
//! [`ir2_leaf_wrap_split_config`] verifies the child at `(lb 6, qpow 16)` — **bit-for-bit the
//! verification that runs today, over the same unmodified `Ir2BatchProof`** — and mints its own
//! output at `create_recursion_config`'s knobs, `(lb 3, arity 2, 38 queries, qpow 14)`: the knob set
//! every non-IR-v2 recursion layer in this workspace already runs at.
//!
//! **No soundness knob moves down.** Capacity ledger `3·38 + 14 = 128` against the deployed leaf
//! wrap's `6·19 + 16 = 130`; the standing `create_recursion_config` posture is unchanged because
//! this IS that posture. Nothing is re-emitted: no AIR, no descriptor JSON, no trace. The wrap's
//! OUTPUT proof changes shape, so the recursion VK rotates and a parent fold must verify at
//! `create_recursion_config`'s knobs rather than `ir2_leaf_wrap_config`'s.
//!
//! ## Run
//!
//! ```text
//! # the census — cheap, builds the circuit, proves nothing
//! cargo test -p dregg-circuit-prove --release --test leaf_wrap_mint_blowup_repricing -- --nocapture
//!
//! # the two real proofs, one process each, under /usr/bin/time -l
//! /usr/bin/time -l cargo test -p dregg-circuit-prove --release \
//!   --test leaf_wrap_mint_blowup_repricing -- --ignored --nocapture the_split_mint
//! ```

use std::time::Instant;

use dregg_circuit::descriptor_ir2::{
    Ir2Air, MemBoundaryWitness, UMemBoundaryWitness, ir2_airs_and_common_for_config,
    prove_vm_descriptor2_for_config,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::membership_descriptor_4ary::{
    Digest8, create_test_witness, membership_descriptor_of_depth_4ary, membership_witness_4ary,
};
use dregg_circuit_prove::gpu_backend::{prove_recursion_layer_auto, recursion_dispatch_counters};
use dregg_circuit_prove::ivc_turn_chain::ir2_leaf_wrap_config;
use dregg_circuit_prove::mina_accumulator_fold::{
    ACC_PI_COUNT, Rung, accumulator_descriptor, prove_accumulator_segment_split,
    read_accumulator_claim, segment_public_inputs,
};
use dregg_circuit_prove::plonky3_recursion_impl::recursive::{
    DreggRecursionConfig, create_recursion_backend, ir2_leaf_wrap_split_config,
    verify_recursive_batch_proof_with_config,
};
use p3_air::BaseAir;
use p3_baby_bear::BabyBear as P3BabyBear;
use p3_circuit_prover::{
    ConstraintProfile, TablePacking,
    common::{CircuitTableAir, NpoAirBuilder, NpoPreprocessor, get_airs_and_degrees_with_prep},
    expose_claim_air_builders, expose_claim_preprocessor, poseidon2_air_builders,
    poseidon2_preprocessor, recompose_air_builders, recompose_preprocessor,
};
use p3_recursion::{RecursionInput, RecursionOutput, Target, build_next_layer_circuit_with_expose};

const D: usize = 4;
type RecursionChallenge = <DreggRecursionConfig as p3_uni_stark::StarkGenericConfig>::Challenge;

const DISCHARGING: &str =
    include_str!("../../circuit/tests/fixtures/mina-accumulator-discharging-trace.txt");

fn full_trace() -> Vec<Vec<BabyBear>> {
    let rows: Vec<Vec<BabyBear>> = DISCHARGING
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| {
            l.split_whitespace()
                .map(|t| BabyBear::new(t.parse::<u32>().expect("cell is a u32 decimal")))
                .collect()
        })
        .collect();
    assert_eq!(
        rows.len(),
        8,
        "the discharging chain is eight complete adds"
    );
    rows
}

/// ⚑⚑ **MAIN vs PREPROCESSED, SEPARATED — the term `mina_accumulator_leaf_anatomy` summed.**
///
/// That file reports `(main + preprocessed) width` as one number, so "is the wall a manifest sized
/// for the whole SRS rather than for the work" cannot be read off it. It is not: measured below,
/// the preprocessed side is a small minority and the `expose_claim` table — the only manifest-shaped
/// object in the wrap — is **one row**.
///
/// Everything here is a print except the two structural asserts; the numbers are the point.
#[test]
#[ignore = "MEASUREMENT, ~15 s: builds ONE leaf-wrap circuit (no wrap PROVING). --ignored --nocapture"]
fn the_preprocessed_side_is_not_the_wall_and_the_blowup_is() {
    let desc = accumulator_descriptor(Rung::Final).expect("the final segment descriptor");
    let trace = full_trace();
    let pis = segment_public_inputs(&trace).expect("public inputs");
    let config = ir2_leaf_wrap_config();

    let inner = prove_vm_descriptor2_for_config::<DreggRecursionConfig>(
        &desc,
        &trace,
        &pis,
        &MemBoundaryWitness::default(),
        &[],
        &UMemBoundaryWitness::default(),
        &config,
    )
    .expect("inner IR-v2 prove");
    let (airs, table_public_inputs, common) =
        ir2_airs_and_common_for_config(&desc, &inner, &pis, &config).expect("verify triple");

    let input: RecursionInput<'_, DreggRecursionConfig, Ir2Air> =
        RecursionInput::NativeBatchStark {
            airs: &airs,
            proof: &inner,
            common_data: &common,
            table_public_inputs,
        };
    let expose = move |cb: &mut p3_circuit::CircuitBuilder<RecursionChallenge>,
                       apt: &[Vec<Target>],
                       _vk_cap: &[Target]| {
        let main = apt.first().expect("a main instance");
        let claim: Vec<Target> = (0..ACC_PI_COUNT.min(main.len())).map(|k| main[k]).collect();
        cb.expose_as_public_output(&claim);
    };
    let backend = create_recursion_backend();
    let (circuit, _vr) =
        build_next_layer_circuit_with_expose::<DreggRecursionConfig, Ir2Air, _, D>(
            &input,
            &config,
            &backend,
            Some(&expose),
        )
        .expect("the leaf-wrap verification circuit builds");

    // ⚠ `ProveNextLayerParams::default()` — what `prove_recursion_layer_auto_with_expose` passes
    // (`gpu_backend.rs`) — is `TablePacking::new(1, 4)` with `ConstraintProfile::Standard` and
    // `min_trace_height = 1`. `mina_accumulator_leaf_anatomy.rs` censuses at `RecursionOptimized`
    // while calling itself "the same extraction the prover performs"; both are reported here so the
    // deployed shape is the one on the record.
    let packing = TablePacking::new(1, 4);
    let profile = ConstraintProfile::Standard;
    let preprocessors: Vec<Box<dyn NpoPreprocessor<P3BabyBear>>> = vec![
        poseidon2_preprocessor::<P3BabyBear>(),
        recompose_preprocessor::<P3BabyBear>(false),
        expose_claim_preprocessor::<P3BabyBear>(),
    ];
    let air_builders: Vec<Box<dyn NpoAirBuilder<DreggRecursionConfig, D>>> = {
        let mut b = poseidon2_air_builders::<DreggRecursionConfig, D>();
        b.extend(recompose_air_builders::<DreggRecursionConfig, D>(1, false));
        b.extend(expose_claim_air_builders::<DreggRecursionConfig, D>());
        b
    };
    let (airs_degrees, _prim, npo_prep) =
        get_airs_and_degrees_with_prep::<DreggRecursionConfig, RecursionChallenge, D>(
            &circuit,
            &packing,
            &preprocessors,
            &air_builders,
            profile,
        )
        .expect("table AIR extraction");
    println!("\nconstraint profile        : {profile:?}  (ProveNextLayerParams::default())");

    let mut npo_keys: Vec<String> = npo_prep.keys().map(|k| k.as_str().to_string()).collect();
    npo_keys.sort();
    let mut dynamic_names: Vec<String> = Vec::new();
    for prefix in ["poseidon2_perm/", "recompose", "expose_claim"] {
        for k in &npo_keys {
            let matched = if prefix.ends_with('/') {
                k.starts_with(prefix)
            } else {
                k == prefix
            };
            if matched {
                dynamic_names.push(k.clone());
            }
        }
    }

    println!(
        "\n{:<34} {:>5} {:>10} {:>7} {:>7} {:>15} {:>15} {:>15}",
        "table", "log2", "rows", "main", "prep", "trace cells", "LDE @ lb6", "LDE @ lb3"
    );
    let (mut t_main, mut t_prep, mut t_cells) = (0u64, 0u64, 0u64);
    let mut dyn_i = 0usize;
    for (air, deg) in &airs_degrees {
        let (name, w, pw) = match air {
            CircuitTableAir::Const(a) => (
                "Const".to_string(),
                BaseAir::<P3BabyBear>::width(a),
                BaseAir::<P3BabyBear>::preprocessed_width(a),
            ),
            CircuitTableAir::Public(a) => (
                "Public".to_string(),
                BaseAir::<P3BabyBear>::width(a),
                BaseAir::<P3BabyBear>::preprocessed_width(a),
            ),
            CircuitTableAir::Alu(a) => (
                "Alu".to_string(),
                BaseAir::<P3BabyBear>::width(a),
                BaseAir::<P3BabyBear>::preprocessed_width(a),
            ),
            CircuitTableAir::Dynamic(a) => {
                let n = dynamic_names
                    .get(dyn_i)
                    .cloned()
                    .unwrap_or_else(|| format!("dynamic#{dyn_i}"));
                dyn_i += 1;
                (
                    n,
                    BaseAir::<P3BabyBear>::width(a),
                    BaseAir::<P3BabyBear>::preprocessed_width(a),
                )
            }
        };
        let rows = 1u64 << *deg;
        let cells = rows * (w + pw) as u64;
        t_main += rows * w as u64;
        t_prep += rows * pw as u64;
        t_cells += cells;
        println!(
            "{:<34} {:>5} {:>10} {:>7} {:>7} {:>15} {:>15} {:>15}",
            name,
            deg,
            rows,
            w,
            pw,
            cells,
            cells << 6,
            cells << 3
        );
    }

    println!(
        "\nTOTAL wrap TRACE cells   : {t_cells}  (main {t_main} + preprocessed {t_prep}, \
         preprocessed = {:.1}%)",
        100.0 * t_prep as f64 / t_cells as f64
    );
    println!(
        "TOTAL committed LDE @ lb6: {:>15}  = {:.1} GiB of BabyBear (4 B/cell)",
        t_cells << 6,
        ((t_cells << 6) * 4) as f64 / (1u64 << 30) as f64
    );
    println!(
        "TOTAL committed LDE @ lb3: {:>15}  = {:.1} GiB of BabyBear (4 B/cell)",
        t_cells << 3,
        ((t_cells << 3) * 4) as f64 / (1u64 << 30) as f64
    );
    println!(
        "\nINNER trace (the eight curve additions themselves): 8 rows x {} declared columns = {} \
         cells",
        desc.trace_width,
        8 * desc.trace_width
    );
    println!(
        "wrap trace / inner trace = {:.0}x — and NONE of that ratio is the blowup",
        t_cells as f64 / (8 * desc.trace_width) as f64
    );

    // MEASURED 2026-08-07: preprocessed is 30.2% — a minority, and none of it is manifest-shaped.
    // The only manifest-shaped table in the wrap (`expose_claim`) is ONE row: 1,152 cells against
    // 233 million. "The leaf commits a manifest sized for the whole SRS" is refuted here.
    assert!(
        t_prep * 2 < t_cells,
        "preprocessed is a minority of the wrap's committed cells: {t_prep} of {t_cells}"
    );
    assert!(
        t_cells > 200_000_000,
        "the wrap trace is ~2.3e8 cells before any blowup: {t_cells}"
    );
}

/// The FRI shape of an EMITTED recursion root, read off the proof — the mint engine's own
/// fingerprint, not a config field.
///
/// * `num_queries` is `FriParameters::num_queries` verbatim: the prover pushes one
///   [`p3_fri::QueryProof`] per query.
/// * `log_lde_domain` is `log2` of the TALLEST matrix the prover actually committed, read as the
///   length of its Merkle authentication path (`cap_height = 0`, so path length = tree depth). This
///   is the mint `log_blowup` **on the artifact**: the committed domain is `2^(degree_bits +
///   log_blowup)` and it is the quantity the whole repricing is about.
///
/// ⚠ `commit_phase_commits.len()` is NOT a blowup discriminator and was asserted as one in the
/// first draft of this test. Derived from `vendor/plonky3-fri-82cfad73/src/prover.rs:197,199`: the
/// commit loop runs from `log_max_height = degree_bits + log_blowup` down to
/// `log_final_height = log_blowup + log_final_poly_len`, so at arity 2 the round count is
/// `degree_bits − log_final_poly_len` and the blowup CANCELS. Measured: 14 rounds at BOTH lb6 and
/// lb3.
struct EmittedFri {
    num_queries: usize,
    commit_rounds: usize,
    log_lde_domain: usize,
    max_degree_bits: usize,
}

fn emitted_fri(root: &RecursionOutput<DreggRecursionConfig>) -> EmittedFri {
    let fri = &root.0.proof.opening_proof;
    let log_lde_domain = fri
        .query_proofs
        .iter()
        .flat_map(|q| q.input_proof.iter())
        .map(|b| b.opening_proof.len())
        .max()
        .unwrap_or(0);
    EmittedFri {
        num_queries: fri.query_proofs.len(),
        commit_rounds: fri.commit_phase_commits.len(),
        log_lde_domain,
        max_degree_bits: root.0.proof.degree_bits.iter().copied().max().unwrap_or(0),
    }
}

/// ⚑⚑ **THE GATE: THE EMITTED ROOT'S OWN FRI SHAPE.** A test that reads `mint_knobs()` is testing
/// the config struct — and the config struct was already right when the split was INERT.
///
/// The version of this test that shipped with `657553a2d` asserted
/// `ir2_leaf_wrap_split_config().mint_knobs().num_queries == 38` and passed, while every root the
/// production dispatch emitted carried **19** query proofs, because
/// `prove_recursion_layer_auto_with_expose`'s GPU branch took its minting engine from a hardcoded
/// `create_gpu_ir2_leaf_wrap_config()` — `(lb 6, 19 queries)`, a CONSTANT — and never looked at the
/// config it was handed. Verifying such a root at its own config failed
/// `QueryProofCountMismatch { expected: 38, got: 19 }`. Green test, inert change, and the test could
/// not have told the difference because it never touched a proof.
///
/// So: one CHILD (a Lean-emitted depth-2 4-ary membership descriptor batch, minted at the IR-v2
/// leaf wrap's `lb 6 / 19 queries` — the knobs BOTH wrap configs verify at, so the same child feeds
/// both), wrapped TWICE through the **production dispatch** `prove_recursion_layer_auto`, and every
/// assertion below is a read of an emitted proof:
///
/// 1. each root carries its own config's query count (19 vs 38);
/// 2. the split root's tallest COMMITTED domain is exactly 3 bits shorter — the `lb 6 → lb 3`
///    8× LDE shrink, read off the artifact's Merkle path depth rather than off `MintKnobs`;
/// 3. each root verifies at its own engine;
/// 4. and REFUSES at the other's — which is what makes (1) and (2) claims about two distinct
///    objects rather than two labels on one.
///
/// ⚑⚑ **AND IT RUNS BOTH DISPATCH BRANCHES, FORCED.** Only the GPU branch was broken. A gate that
/// took whatever branch the box happens to offer would have been green on a CPU box and blind — the
/// "documented, not detected" shape. `DREGG_GPU_RECURSION` is pinned to `cpu` and then `gpu` and the
/// SAME assertions run on each, so neither branch can drift from the config it was handed.
#[test]
fn the_split_mint_reaches_the_prover_and_the_emitted_root_proves_it() {
    for policy in ["cpu", "gpu"] {
        // SAFETY: single-threaded read by `production_gpu_recursion_enabled()`; this is the only
        // non-ignored test in this binary and nextest gives each test its own process. Same pattern
        // as `gpu_backend_shrink_e2e.rs`.
        unsafe { std::env::set_var("DREGG_GPU_RECURSION", policy) };
        println!("\n══ DREGG_GPU_RECURSION={policy} ══");
        both_wraps_emit_their_own_engine(policy);
    }
    unsafe { std::env::remove_var("DREGG_GPU_RECURSION") };
}

fn both_wraps_emit_their_own_engine(policy: &str) {
    let deployed = ir2_leaf_wrap_config();
    let split = ir2_leaf_wrap_split_config();

    // ── the child: a Lean-emitted membership descriptor batch at the wrap's VERIFY knobs ──
    // Depth 2 keeps this a gate rather than a measurement. Both wrap configs verify the child at
    // `IR2_INNER_*` (lb 6 / qpow 16), so ONE child proof serves both wraps — which is exactly the
    // claim the split makes: the child's in-circuit verification is bit-for-bit unchanged.
    let leaf: Digest8 = core::array::from_fn(|k| BabyBear::new(7_000_003 + k as u32));
    let (siblings, positions, _root) = create_test_witness(leaf, 2);
    let desc = membership_descriptor_of_depth_4ary(siblings.len());
    let (trace, pis) = membership_witness_4ary(leaf, &siblings, &positions).expect("witness");
    let inner = prove_vm_descriptor2_for_config::<DreggRecursionConfig>(
        &desc,
        &trace,
        &pis,
        &MemBoundaryWitness::default(),
        &[],
        &UMemBoundaryWitness::default(),
        &deployed,
    )
    .expect("the membership child mints at the leaf-wrap engine");
    let (airs, table_public_inputs, common) =
        ir2_airs_and_common_for_config(&desc, &inner, &pis, &deployed).expect("verify triple");
    let input: RecursionInput<'_, DreggRecursionConfig, Ir2Air> =
        RecursionInput::NativeBatchStark {
            airs: &airs,
            proof: &inner,
            common_data: &common,
            table_public_inputs,
        };

    // ── the two wraps, through the PRODUCTION dispatch ──
    let (gpu0, cpu0) = recursion_dispatch_counters();
    let t = Instant::now();
    let dep_root = prove_recursion_layer_auto(&input, &deployed).expect("deployed wrap proves");
    let dep_wall = t.elapsed().as_secs_f64();
    let t = Instant::now();
    let spl_root = prove_recursion_layer_auto(&input, &split).expect("split wrap proves");
    let spl_wall = t.elapsed().as_secs_f64();
    let (gpu1, cpu1) = recursion_dispatch_counters();
    let (gpu_ran, cpu_ran) = (gpu1 - gpu0, cpu1 - cpu0);
    println!("dispatch: {gpu_ran} GPU layer(s), {cpu_ran} CPU layer(s)");
    // ⚑ The gate must know WHICH branch it just judged. `cpu` forces the CPU branch outright; `gpu`
    // is honoured only when a native adapter exists, so it is allowed to fall back — but it may not
    // fall back SILENTLY, and a `cpu` run that dispatched to the GPU would mean the policy knob is
    // dead and this loop is judging one branch twice.
    if policy == "cpu" {
        assert_eq!(
            (gpu_ran, cpu_ran),
            (0, 2),
            "DREGG_GPU_RECURSION=cpu must dispatch both wraps to the CPU branch"
        );
    }

    let dep = emitted_fri(&dep_root);
    let spl = emitted_fri(&spl_root);
    println!(
        "\n{:<16} {:>8} {:>8} {:>11} {:>11} {:>8} {:>8} {:>8}",
        "config", "mint lb", "mint q", "EMITTED q", "log2 LDE", "max db", "rounds", "wall s"
    );
    for (label, k, e, wall) in [
        ("ir2_leaf_wrap", *deployed.mint_knobs(), &dep, dep_wall),
        ("split", *split.mint_knobs(), &spl, spl_wall),
    ] {
        println!(
            "{:<16} {:>8} {:>8} {:>11} {:>11} {:>8} {:>8} {:>8.2}",
            label,
            k.log_blowup,
            k.num_queries,
            e.num_queries,
            e.log_lde_domain,
            e.max_degree_bits,
            e.commit_rounds,
            wall
        );
    }

    // (1) THE EMITTED QUERY COUNT. This is the assertion the inert version could not make.
    assert_eq!(
        dep.num_queries, 19,
        "the deployed wrap's ROOT must carry 19 query proofs"
    );
    assert_eq!(
        spl.num_queries, 38,
        "the split wrap's ROOT must carry 38 query proofs — if this is 19 the mint knobs are not \
         reaching the prover and the split is inert"
    );

    // (2) THE EMITTED BLOWUP — the LDE domain the prover really committed, as Merkle path depth.
    // Same circuit, same trace degrees, so the whole difference is the mint blowup: 6 − 3 = 3 bits,
    // i.e. the 8× this repricing is about. This is the quantity, not a proxy for it.
    assert_eq!(
        dep.max_degree_bits, spl.max_degree_bits,
        "both wraps prove the SAME verification circuit — a moved degree means the comparison is \
         between two different circuits"
    );
    assert_eq!(
        dep.log_lde_domain,
        spl.log_lde_domain + 3,
        "the deployed wrap must commit a domain 8x taller than the split one: 2^{} vs 2^{}",
        dep.log_lde_domain,
        spl.log_lde_domain
    );
    assert_eq!(
        spl.log_lde_domain,
        spl.max_degree_bits + 3,
        "the split root's committed domain must be its trace domain times the SPLIT mint blowup (8x)"
    );

    // (3) each root verifies at its OWN engine.
    verify_recursive_batch_proof_with_config(&dep_root.0, &deployed)
        .expect("the deployed root verifies at the deployed engine");
    verify_recursive_batch_proof_with_config(&spl_root.0, &split)
        .expect("the split root verifies at the split engine");

    // (4) and REFUSES at the other's. Without this, (1) and (2) could both be reads of one object
    // under two labels.
    assert!(
        verify_recursive_batch_proof_with_config(&spl_root.0, &deployed).is_err(),
        "a 38-query root must NOT verify under the 19-query engine"
    );
    assert!(
        verify_recursive_batch_proof_with_config(&dep_root.0, &split).is_err(),
        "a 19-query root must NOT verify under the 38-query engine"
    );

    // ⚑ THE SOUNDNESS LEDGER, on the objects. `lb*q + qpow` is the capacity column both configs are
    // gated against; 128 is the standing drift margin every other recursion layer already sits at.
    let (dep_k, spl_k) = (*deployed.mint_knobs(), *split.mint_knobs());
    assert_eq!(dep_k.capacity_bits(), 130);
    assert_eq!(spl_k.capacity_bits(), 128);
    assert!(
        spl_k.capacity_bits() >= 128,
        "the split must not drop below the 128 drift margin: {}",
        spl_k.capacity_bits()
    );
    println!(
        "\nmint LDE ratio deployed:split = {}x — every committed cell of the WRAP circuit",
        1u32 << (dep_k.log_blowup - spl_k.log_blowup)
    );
}

/// ⚑ **THE BASELINE.** One eight-row `-final` segment at the deployed config, exactly what
/// `mina_accumulator_fold.rs::a_one_segment_chain_is_the_final_rung` runs. Present here so the two
/// numbers come out of ONE binary on ONE box, rather than a fresh run compared against a header.
///
/// ⚠ ~300 s and ~118 GiB peak footprint — which EXCEEDS this box's 96 GiB of RAM. Run it alone.
#[test]
#[ignore = "MEASUREMENT, ~5 min, ~118 GiB peak footprint (> RAM). Run under /usr/bin/time -l, alone."]
fn the_deployed_mint_is_the_measured_wall() {
    let t = full_trace();
    let pis = segment_public_inputs(&t).expect("public inputs");
    let cfg = ir2_leaf_wrap_config();

    // ⚑⚑ **THE BASELINE MUST NAME BOTH ROLES EXPLICITLY NOW.** `prove_accumulator_segment` is the
    // PRODUCTION entry point and it SPLITS: it derives its wrap engine from the config it is
    // handed. Calling it here would silently measure the split and label the number "deployed" —
    // the falsifier-that-stopped-falsifying shape, and the exact way this file's own 13.8× would
    // become a comparison of one object against itself. The old single-engine tower is reached
    // only by passing the same config for both roles, which is what this line does.
    let start = Instant::now();
    let root = prove_accumulator_segment_split(Rung::Final, &t, &pis, &cfg, &cfg)
        .expect("the deployed leaf wrap proves");
    let wall = start.elapsed().as_secs_f64();

    verify_recursive_batch_proof_with_config(&root.0, &cfg)
        .expect("the deployed root verifies natively");
    let claim = read_accumulator_claim(&root).expect("claim");
    assert!(claim.is_identity(), "the eight-add chain must reach O");

    let e = emitted_fri(&root);
    let (gpu, cpu) = recursion_dispatch_counters();
    println!(
        "\nDEPLOYED  (mint lb6/q19, verify lb6/q19): {wall:.2} s\n  \
         EMITTED: {} query proofs, committed LDE domain 2^{} (trace 2^{}), {} FRI rounds\n  \
         dispatch: {gpu} GPU / {cpu} CPU layer(s)",
        e.num_queries, e.log_lde_domain, e.max_degree_bits, e.commit_rounds
    );
    assert_eq!(e.num_queries, 19, "the deployed baseline must be lb6/q19");
}

/// ⚑⚑ **THE SAME EIGHT CURVE ADDITIONS, MINTED AT A DOMAIN THAT FITS THEM.**
///
/// Identical trace, identical descriptor, identical inner proof, identical in-circuit verification
/// of that inner proof. The ONLY difference is the blowup this layer commits its OWN trace at.
///
/// **MEASURED 2026-08-07: 21.63 s, maxrss 18.65 GiB / 20.02 GB, peak footprint 23.23 GiB / 24.95
/// GB, committed LDE domain 2^23.** Against the deployed baseline from the SAME binary minutes
/// earlier: 298.08 s, 46.47 GiB / 49.90 GB, 117.79 GiB / 126.47 GB, 2^26.
///
/// ⚑⚑ **AND THIS RETRACTS THE PARAGRAPH THAT STOOD HERE.** It read: *"Two attempts were KILLED at
/// ~600 s having reached 72.2 / 73.7 GiB peak footprint … What they do establish is that the mint
/// blowup is not the whole wall: the committed LDE falls 55.6 → 6.9 GiB, and the leaf still wants
/// ≥72 GiB. The remainder is the verification circuit itself."*
///
/// **Those runs never applied the split.** `prove_recursion_layer_auto_with_expose`'s GPU branch
/// took its minting engine from a hardcoded `create_gpu_ir2_leaf_wrap_config()` and never read the
/// config it was handed, and this box dispatches to that branch — so both "split" attempts minted
/// at `lb 6`, i.e. they were two more copies of the baseline, run concurrently with each other. The
/// ≥72 GiB was the BASELINE's climb, and the conclusion drawn from it — that the wall is the
/// verification circuit rather than the blowup — was drawn from a measurement of the wrong object.
///
/// ⚠ The narrowing that paragraph pointed at (`MinaAccumulatorAir`'s 3,048 → 446) is still worth
/// doing; what is retracted is the EVIDENCE that it is where the remaining wall is. The real
/// remainder after the split is 23.23 GiB, not ≥72.
#[test]
#[ignore = "MEASUREMENT, ~22 s / ~23 GiB peak. Run under /usr/bin/time -l, ALONE."]
fn the_split_mint_proves_the_same_eight_additions() {
    let t = full_trace();
    let pis = segment_public_inputs(&t).expect("public inputs");
    let inner = ir2_leaf_wrap_config();
    let wrap = ir2_leaf_wrap_split_config();

    // ⚑ This is now what `prove_accumulator_segment(rung, t, pis, &inner)` does on its own — the
    // wrap config is DERIVED (`recursion_layer_over`) rather than named. Kept explicit here so the
    // measurement says which object it timed even if the derivation is later retuned.
    let start = Instant::now();
    let root = prove_accumulator_segment_split(Rung::Final, &t, &pis, &inner, &wrap)
        .expect("the split leaf wrap proves");
    let wall = start.elapsed().as_secs_f64();

    // ⚑ The root is verified at the SPLIT config's minting knobs — the engine it was minted at.
    verify_recursive_batch_proof_with_config(&root.0, &wrap)
        .expect("the split root verifies natively at its own engine");
    let claim = read_accumulator_claim(&root).expect("claim");
    assert!(
        claim.is_identity(),
        "the eight-add chain must still reach O — the split moved a commitment rate, not a claim"
    );

    let e = emitted_fri(&root);
    let (gpu, cpu) = recursion_dispatch_counters();
    println!(
        "\nSPLIT     (mint lb3/q38, verify lb6/q19): {wall:.2} s\n  \
         EMITTED: {} query proofs, committed LDE domain 2^{} (trace 2^{}), {} FRI rounds\n  \
         dispatch: {gpu} GPU / {cpu} CPU layer(s)",
        e.num_queries, e.log_lde_domain, e.max_degree_bits, e.commit_rounds
    );
    // ⚑ The measurement must refuse to report a number for the WRONG object. Without this the
    // headline is a timing of the deployed engine wearing the split's label — which is exactly what
    // shipped for one commit.
    assert_eq!(
        e.num_queries, 38,
        "this run did not mint at the split engine; the number above is not the split's"
    );
    assert_eq!(
        e.log_lde_domain,
        e.max_degree_bits + 3,
        "the committed LDE domain must be the trace domain x8, not x64"
    );
}
