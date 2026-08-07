//! ⚑⚑ **THE "COST WALL" IS A CONFIG CONFLATION, AND THIS IS THE MEASUREMENT.**
//!
//! `mina_accumulator_fold.rs`'s header prices ONE eight-row accumulator leaf — eight Vesta complete
//! additions — at **223.36 s / 48.85 GiB maxrss / 117.93 GiB peak footprint**, and concludes *"no
//! unloaded box in the fleet can host it."* That number is real. What it measures is not eight
//! curve additions.
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
//! 117.93 GiB. It does NOT remove 8/9 of the leaf. See
//! [`the_split_mint_proves_the_same_eight_additions`] for what the (killed) attempts measured.
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
use dregg_circuit_prove::ivc_turn_chain::ir2_leaf_wrap_config;
use dregg_circuit_prove::mina_accumulator_fold::{
    ACC_PI_COUNT, Rung, accumulator_descriptor, prove_accumulator_segment,
    prove_accumulator_segment_split, read_accumulator_claim, segment_public_inputs,
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
use p3_recursion::{RecursionInput, Target, build_next_layer_circuit_with_expose};

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

/// ⚑ **THE KNOBS EACH CONFIG ACTUALLY RUNS, READ OFF THE OBJECTS — not off a doc comment.**
///
/// The deployed leaf wrap mints at the blowup it VERIFIES at; the split one does not. If this test
/// ever goes green with the two blowups equal, the split has been silently undone and every figure
/// below is a measurement of the same thing twice.
#[test]
fn the_deployed_wrap_mints_at_its_childs_blowup_and_the_split_one_does_not() {
    let deployed = ir2_leaf_wrap_config();
    let split = ir2_leaf_wrap_split_config();

    let dep_mint = *deployed.mint_knobs();
    let spl_mint = *split.mint_knobs();

    println!(
        "\n{:<22} {:>10} {:>10} {:>8} {:>10} {:>10}",
        "config", "mint lb", "mint q", "arity", "mint qpow", "capacity"
    );
    for (label, p) in [("ir2_leaf_wrap", dep_mint), ("split", spl_mint)] {
        println!(
            "{:<22} {:>10} {:>10} {:>8} {:>10} {:>10}",
            label,
            p.log_blowup,
            p.num_queries,
            1 << p.max_log_arity,
            p.query_pow_bits,
            p.capacity_bits()
        );
    }

    assert_eq!(dep_mint.log_blowup, 6, "the deployed wrap mints at 64x");
    assert_eq!(dep_mint.num_queries, 19);
    assert_eq!(spl_mint.log_blowup, 3, "the split wrap mints at 8x");
    assert_eq!(spl_mint.num_queries, 38);

    // ⚑ NO SOUNDNESS KNOB MOVES DOWN. `lb*q + qpow` is the capacity ledger both configs are gated
    // against; 128 is the standing drift margin every other recursion layer already sits at.
    let dep_cap = dep_mint.capacity_bits();
    let spl_cap = spl_mint.capacity_bits();
    assert_eq!(dep_cap, 130);
    assert_eq!(spl_cap, 128);
    assert!(
        spl_cap >= 128,
        "the split must not drop below the 128 drift margin: {spl_cap}"
    );

    println!(
        "\nmint LDE ratio deployed:split = {}x — every committed cell of the WRAP circuit",
        1u32 << (dep_mint.log_blowup - spl_mint.log_blowup)
    );
}

/// ⚑ **THE BASELINE.** One eight-row `-final` segment at the deployed config, exactly what
/// `mina_accumulator_fold.rs::a_one_segment_chain_is_the_final_rung` runs. Present here so the two
/// numbers come out of ONE binary on ONE box, rather than a fresh run compared against a header.
///
/// ⚠ ~223 s and ~118 GiB peak footprint. Run it alone.
#[test]
#[ignore = "MEASUREMENT, ~4 min, ~118 GiB peak footprint. Run under /usr/bin/time -l, alone."]
fn the_deployed_mint_is_the_measured_wall() {
    let t = full_trace();
    let pis = segment_public_inputs(&t).expect("public inputs");
    let cfg = ir2_leaf_wrap_config();

    let start = Instant::now();
    let root = prove_accumulator_segment(Rung::Final, &t, &pis, &cfg)
        .expect("the deployed leaf wrap proves");
    let wall = start.elapsed().as_secs_f64();

    verify_recursive_batch_proof_with_config(&root.0, &cfg)
        .expect("the deployed root verifies natively");
    let claim = read_accumulator_claim(&root).expect("claim");
    assert!(claim.is_identity(), "the eight-add chain must reach O");

    println!("\nDEPLOYED  (mint lb6/q19, verify lb6/q19): {wall:.2} s");
}

/// ⚑⚑ **THE SAME EIGHT CURVE ADDITIONS, MINTED AT A DOMAIN THAT FITS THEM.**
///
/// Identical trace, identical descriptor, identical inner proof, identical in-circuit verification
/// of that inner proof. The ONLY difference is the blowup this layer commits its OWN trace at.
/// ⚠⚠ **RUN THIS ALONE. IT IS NOT SMALL, AND THE 8× IS ON THE LDE ONLY.**
///
/// Two attempts on 2026-08-07 were run CONCURRENTLY with each other on a box already carrying
/// several `lean` builds. Both were KILLED at ~600 s having reached **72.2 / 73.7 GiB peak
/// footprint** with 397–425 s of `sys` against 40–44 s of `user` — i.e. ~90% memory-stalled, still
/// climbing, proving almost nothing. A killed run bounds nothing from above, so those are a LOWER
/// bound on the split's peak and nothing else. What they do establish is that the mint blowup is
/// **not** the whole wall: the committed LDE falls 55.6 → 6.9 GiB, and the leaf still wants ≥72 GiB.
/// The remainder is the verification circuit itself — `Q · W` over the child's 10,756 COMMITTED
/// columns — which is the term `MinaAccumulatorAir`'s 3,048 → 446 narrowing addresses.
#[test]
#[ignore = "MEASUREMENT, ≥72 GiB peak. Run under /usr/bin/time -l, ALONE, on a quiet box."]
fn the_split_mint_proves_the_same_eight_additions() {
    let t = full_trace();
    let pis = segment_public_inputs(&t).expect("public inputs");
    let inner = ir2_leaf_wrap_config();
    let wrap = ir2_leaf_wrap_split_config();

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

    println!("\nSPLIT     (mint lb3/q38, verify lb6/q19): {wall:.2} s");
}
