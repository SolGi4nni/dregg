//! ⚑⚑ **WHERE THE ACCUMULATOR LEAF WRAP'S COST GOES — MEASURED, NOT MODELLED.**
//!
//! `tests/mina_accumulator_fold.rs` attributed a leaf wrap's memory wall to the descriptor's
//! **3,048** columns against the phase-2 chainlink's **469**. That attribution was an inference
//! from a ratio — taken while the two ALSO differed by 256× in ROWS, with only one of the two
//! named. This file is the measurement behind it, and it proves nothing: it REPORTS, so the
//! narrowing that follows is aimed at the term that actually dominates rather than at the one that
//! was noticed first.
//!
//! It does the expensive-looking thing cheaply. The INNER IR-v2 prove of an 8-row accumulator
//! segment costs **136 MB and ~1 s** (measured; `circuit/tests/mina_accumulator_air_proves.rs` runs
//! nine of them in 16 s at a 136 MB peak), and `build_next_layer_circuit_with_expose` BUILDS the
//! in-circuit verifier without proving it. So the leaf wrap's *shape* is observable in seconds for
//! a couple of gigabytes — **the entire 118 GiB is `prove_all_tables` over that shape**, and the
//! shape is what this file reports.
//!
//! ## What it compares
//!
//! Five leaf wraps, same recursion config, same expose arity:
//!
//! | descriptor                       | inner width | inner rows       |
//! |----------------------------------|-------------|------------------|
//! | `pasta-fq-chainlink::v1`         | 469         | 2,048 (link 0)   |
//! | `dregg-mina-accumulator-seg::v1` | 3,048       | 1, 2, 4, 8       |
//!
//! The chainlink is the one that DOES fold in production (46 leaves + 45 folds, 1,037 s), so it is
//! the width control. The 1/2/4/8 sweep is the ROW control the width claim needs — the previous
//! attribution compared 3,048 columns against 469 while the row counts also differed by 256×, and
//! named only one of the two. If the wrap circuit barely moves across the sweep, rows are nearly
//! free and "make the leaf taller" is a different remedy from narrowing.
//!
//! ⚠ The chainlink half is SKIPPED (loudly, not substituted) when its emitted fixture is absent;
//! regenerate with metatheory's `mina_chain_emit`.
//!
//! ## ⚑⚑ AND THE DENOMINATOR THIS FILE USED WAS THE WRONG ONE
//!
//! The sweep below reads `6.5×` the *declared* columns costing `11.5×` the wrap ops and calls the
//! law superlinear. It is not superlinear. `MainLayout::build` compiles every declared range lookup
//! into the declared column **plus** a nibble-decomposition aux block, and *that* extended trace is
//! what `Ir2Air::Main` is `width()`d at and what the prover commits:
//!
//! ```text
//!   pasta-fq-chainlink              469 declared →  1,037 committed   (2.21×)
//!   dregg-mina-accumulator-seg    3,048 declared → 10,756 committed   (3.53×)
//! ```
//!
//! `10,756 / 1,037 = 10.37×` against an op ratio of `11.52×`. **71.7% of the accumulator row the
//! prover commits is range-check decomposition**, at `LIMB_BITS = 4` — a sixteen-row byte table,
//! one aux column per four bits. `the_wrap_cost_tracks_committed_width_not_declared_width` is that
//! correction as a measurement, with the radix curve beside it.
//!
//! Run:
//! ```text
//! cargo test -p dregg-circuit-prove --release --test mina_accumulator_leaf_anatomy \
//!   -- --ignored --nocapture
//! ```

use std::time::Instant;

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, Ir2Air, MemBoundaryWitness, TableSem, UMemBoundaryWitness, VmConstraint2,
    decomp_cols_pub, ir2_airs_and_common_for_config, parse_vm_descriptor2,
    prove_vm_descriptor2_for_config,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::ivc_turn_chain::ir2_leaf_wrap_config;
use dregg_circuit_prove::mina_accumulator_fold::{
    ACC_PI_COUNT, Rung, accumulator_descriptor, segment_public_inputs,
};
use dregg_circuit_prove::plonky3_recursion_impl::recursive::{
    DreggRecursionConfig, create_recursion_backend,
};
use p3_air::BaseAir;
use p3_baby_bear::BabyBear as P3BabyBear;
use p3_circuit::{AluOpKind, Op};
use p3_circuit_prover::{
    ConstraintProfile, TablePacking,
    common::{CircuitTableAir, NpoAirBuilder, NpoPreprocessor, get_airs_and_degrees_with_prep},
    expose_claim_air_builders, expose_claim_preprocessor, poseidon2_air_builders,
    poseidon2_preprocessor, recompose_air_builders, recompose_preprocessor,
};
use p3_recursion::{RecursionInput, Target, build_next_layer_circuit_with_expose};

const D: usize = 4;
type RecursionChallenge = <DreggRecursionConfig as p3_uni_stark::StarkGenericConfig>::Challenge;
/// ⚑ The blowup the WRAP's own tables are committed at — `IR2_INNER_LOG_BLOWUP = 6`, i.e. **64×**
/// (`recursion-verify/src/config.rs:88`). Read from that constant rather than written as a literal,
/// because a literal here was wrong by 32× in this file's first draft and made every committed-cell
/// figure flatteringly small.
///
/// ⚠ It is worth knowing WHY the wrap mints at the INNER proof's blowup: `create_recursion_config_
/// with_fri` sets the minting `StarkConfig` PCS and the in-circuit `FriVerifierParams` from ONE
/// argument, so "the blowup my child was minted at" and "the blowup I mint at" are the same number
/// by construction. They are two different proofs' knobs.
const LOG_BLOWUP: usize = dregg_recursion_verify::config::IR2_INNER_LOG_BLOWUP;

const DISCHARGING: &str =
    include_str!("../../circuit/tests/fixtures/mina-accumulator-discharging-trace.txt");

fn rows_of(text: &str) -> Vec<Vec<BabyBear>> {
    text.lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| {
            l.split_whitespace()
                .map(|t| BabyBear::new(t.parse::<u32>().expect("cell is a u32 decimal")))
                .collect()
        })
        .collect()
}

/// The op census of one built verification circuit, plus the per-table shapes the prover would
/// commit. Nothing here is asserted; the numbers are the point.
struct Census {
    witness_count: u32,
    ops: usize,
    npo: u64,
    alu: u64,
    horner: u64,
    poseidon2_rows: u64,
    recompose_rows: u64,
    build_secs: f64,
    /// `(table name, log2 rows, main width)` at the leaf-wrap packing.
    shapes: Vec<(String, usize, usize)>,
}

impl Census {
    /// Committed LDE cells the prover must materialise, at the leaf wrap's blowup — the quantity a
    /// peak-RSS figure tracks. Reported per table and summed.
    fn committed_cells(&self) -> u64 {
        self.shapes
            .iter()
            .map(|(_, log_rows, w)| (1u64 << (*log_rows + LOG_BLOWUP)) * (*w as u64))
            .sum()
    }
}

fn census_leaf_wrap(
    label: &str,
    desc: &EffectVmDescriptor2,
    trace: &[Vec<BabyBear>],
    public_inputs: &[BabyBear],
    expose_len: usize,
) -> Census {
    let config = ir2_leaf_wrap_config();

    let t_inner = Instant::now();
    let inner = prove_vm_descriptor2_for_config::<DreggRecursionConfig>(
        desc,
        trace,
        public_inputs,
        &MemBoundaryWitness::default(),
        &[],
        &UMemBoundaryWitness::default(),
        &config,
    )
    .expect("inner IR-v2 prove");
    let inner_secs = t_inner.elapsed().as_secs_f64();

    let (airs, table_public_inputs, common) =
        ir2_airs_and_common_for_config(desc, &inner, public_inputs, &config)
            .expect("verify triple");

    // ⚑ THE INNER PROOF'S OWN SHAPE — what the wrap has to open. This is the quantity the
    // in-circuit verifier pays for, and it is NOT the descriptor's declared width alone.
    println!("\n===== {label} =====");
    println!("declared trace_width      : {}", desc.trace_width);
    println!("declared constraints      : {}", desc.constraints.len());
    println!("declared PI count         : {}", desc.public_input_count);
    println!("inner prove wall          : {inner_secs:.2} s");
    println!("inner AIR count (batch)   : {}", airs.len());

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
        // A descriptor with no public inputs exposes no per-instance targets, so the requested
        // arity is CLAMPED rather than indexed past the end. The expose_claim table is ~1.2k cells
        // against a 10^9-cell wrap, so clamping moves the measurement by nothing that matters —
        // and a panic here would have silently excluded every PI-free atom from the width law.
        let claim: Vec<Target> = (0..expose_len.min(main.len())).map(|k| main[k]).collect();
        cb.expose_as_public_output(&claim);
    };

    let backend = create_recursion_backend();
    let t_build = Instant::now();
    let (circuit, _vr) =
        build_next_layer_circuit_with_expose::<DreggRecursionConfig, Ir2Air, _, D>(
            &input,
            &config,
            &backend,
            Some(&expose),
        )
        .expect("the leaf-wrap verification circuit builds");
    let build_secs = t_build.elapsed().as_secs_f64();

    let mut npo = 0u64;
    let mut alu = 0u64;
    let mut horner = 0u64;
    for op in &circuit.ops {
        match op {
            Op::NonPrimitiveOpWithExecutor { .. } => npo += 1,
            Op::Alu { kind, .. } => {
                alu += 1;
                if matches!(kind, AluOpKind::HornerAcc) {
                    horner += 1;
                }
            }
            _ => {}
        }
    }

    // The REAL table shapes the prover would commit — the same extraction
    // `build_and_prove_next_layer_with_expose` performs before `prove_all_tables`.
    let packing = TablePacking::new(1, 4);
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
            ConstraintProfile::RecursionOptimized,
        )
        .expect("table AIR extraction");

    // Dynamic tables are named by the builders' registration order over the SORTED matched op
    // types — the same iteration `get_airs_and_degrees_with_prep` performs.
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

    let mut shapes = Vec::new();
    let mut poseidon2_rows = 0u64;
    let mut recompose_rows = 0u64;
    let mut dyn_i = 0usize;
    for (air, deg) in &airs_degrees {
        let (name, w, prep_w) = match air {
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
        if name.contains("poseidon") {
            poseidon2_rows += 1u64 << *deg;
        }
        if name.contains("recompose") {
            recompose_rows += 1u64 << *deg;
        }
        shapes.push((name, *deg, w + prep_w));
    }

    println!("--- verification circuit ---");
    println!("build wall                : {build_secs:.2} s");
    println!("witness_count             : {}", circuit.witness_count);
    println!("ops                       : {}", circuit.ops.len());
    println!("  NonPrimitive ops        : {npo}");
    println!("  Alu ops                 : {alu} (HornerAcc {horner})");
    println!("--- tables the wrap prover commits ---");
    println!(
        "{:<44} {:>6} {:>9} {:>16}",
        "table", "log2", "width", "cells"
    );
    for (n, deg, w) in &shapes {
        println!(
            "{:<44} {:>6} {:>9} {:>16}",
            n,
            deg,
            w,
            (1u64 << *deg) * (*w as u64)
        );
    }

    Census {
        witness_count: circuit.witness_count,
        ops: circuit.ops.len(),
        npo,
        alu,
        horner,
        poseidon2_rows,
        recompose_rows,
        build_secs,
        shapes,
    }
}

/// ⚑ **THE A/B PLUS THE ROWS SWEEP.**
///
/// Same recursion config, same everything but the inner shape:
///
/// * the **469**-column chainlink leaf that folds in production (46 leaves + 45 folds, 1,037 s);
/// * the **3,048**-column accumulator segment, at **1, 2, 4 and 8 rows**.
///
/// The rows sweep is the control the width claim needs. If the wrap circuit barely moves with the
/// inner ROW count, then rows are nearly free and a leaf should be as TALL as the inner prover
/// allows — which is a different remedy from narrowing, and the two are told apart here rather than
/// assumed apart.
#[test]
#[ignore = "MEASUREMENT, ~1 min: builds five leaf-wrap circuits (no wrap PROVING). --ignored --nocapture"]
fn where_the_accumulator_leaf_wrap_cost_goes() {
    let acc_rows = rows_of(DISCHARGING);
    assert_eq!(acc_rows.len(), 8);
    let acc_desc = accumulator_descriptor(Rung::Interior).expect("segment descriptor");

    let mut sweep: Vec<(usize, usize, Census)> = Vec::new();

    // --- the CONTROL: the 469-column chainlink that folds in production ---------------------
    if let Some((link_desc, link_trace, link_pis)) = chainlink_leaf() {
        let w = link_desc.trace_width;
        let h = link_trace.len();
        let pin = link_desc.public_input_count.min(200);
        let c = census_leaf_wrap(
            "CHAINLINK (the one that FOLDS)  pasta-fq-chainlink::v1",
            &link_desc,
            &link_trace,
            &link_pis,
            pin,
        );
        sweep.push((w, h, c));
    } else {
        println!(
            "\n(!) chainlink fixture absent — regenerate with metatheory's `mina_chain_emit`; the \
             width control is SKIPPED, not silently substituted"
        );
    }

    // --- the accumulator segment at 1, 2, 4, 8 rows -----------------------------------------
    for h in [1usize, 2, 4, 8] {
        let seg: Vec<Vec<BabyBear>> = acc_rows[..h].to_vec();
        let pis = segment_public_inputs(&seg).expect("segment public inputs");
        let c = census_leaf_wrap(
            &format!("ACCUMULATOR SEGMENT, {h} row(s)  dregg-mina-accumulator-seg::v1"),
            &acc_desc,
            &seg,
            &pis,
            ACC_PI_COUNT,
        );
        sweep.push((acc_desc.trace_width, h, c));
    }

    println!("\n\n########## SUMMARY — the leaf wrap's shape vs the inner shape ##########");
    println!(
        "{:>7} {:>5} {:>12} {:>12} {:>11} {:>12} {:>12} {:>17} {:>8}",
        "in_cols", "rows", "ops", "witness", "npo", "alu", "horner", "wrap LDE cells", "build_s"
    );
    for (w, h, c) in &sweep {
        println!(
            "{:>7} {:>5} {:>12} {:>12} {:>11} {:>12} {:>12} {:>17} {:>8.1}",
            w,
            h,
            c.ops,
            c.witness_count,
            c.npo,
            c.alu,
            c.horner,
            c.committed_cells(),
            c.build_secs
        );
    }
    println!(
        "\n(wrap LDE cells = Σ_table 2^(log2 rows + {LOG_BLOWUP}) × (main + preprocessed width) — \
         the cells `prove_all_tables` materialises, which is what a peak-RSS figure tracks.)"
    );
}

/// ⚑⚑ **THE COST LAW IS IN THE *COMMITTED* WIDTH, NOT THE DECLARED ONE — AND THE DIFFERENCE IS
/// 3.5× ON THE ACCUMULATOR ROW.**
///
/// The sweep above compares `3,048` declared columns against `469` and reads the wrap's `11.5×`
/// op ratio as superlinear in width. It is not superlinear; it is **linear in a width nobody had
/// printed.** A declared column carrying a range lookup is compiled by `MainLayout::build` into
/// the declared column PLUS a nibble-decomposition aux block (`decomp_cols_pub`: `bits/4` limbs at
/// `bits % 4 == 0`), and *that* extended trace is what `Ir2Air::Main` is `width()`d at and what the
/// prover commits. Measured here from the descriptors' own `tables`:
///
/// ```text
///   pasta-fq-chainlink              469 declared →  1,037 committed  (+568,  2.21×)
///   dregg-mina-accumulator-seg    3,048 declared → 10,756 committed  (+7,708, 3.53×)
/// ```
///
/// `10,756 / 1,037 = 10.37×` against an op ratio of `11.52×`. The declared-width ratio `6.50×`
/// was the wrong denominator, and the "superlinearity" was the gap between the two.
///
/// ⚑ **SO 71.7% OF THE ACCUMULATOR ROW THE PROVER COMMITS IS RANGE-CHECK DECOMPOSITION**, at
/// `LIMB_BITS = 4` — a **16-row** byte table. Kimchi range-checks the same kind of limb against a
/// **4,096-row** table (`RANGE_CHECK_UPPERBOUND = 1 << 12`, `kimchi/src/circuits/lookup/tables/
/// range_check.rs:11`), one lookup per 12 bits with no aux column at all. Ours spends one aux
/// column per 4 bits.
///
/// This test is a MEASUREMENT over the real emitted sound atoms — the one-op-per-row objects the
/// narrowing would be built out of — so the width law has points at both ends of the range instead
/// of two points 6.5× apart.
#[test]
#[ignore = "MEASUREMENT, ~1 min: builds five more leaf-wrap circuits (no wrap PROVING). --ignored --nocapture"]
fn the_wrap_cost_tracks_committed_width_not_declared_width() {
    /// One emitted atom: descriptor JSON + an honest Lean-emitted trace at the declared width.
    struct Atom {
        label: &'static str,
        json: &'static str,
        trace: &'static str,
        width: usize,
    }

    let atoms = [
        Atom {
            label: "pasta-fpadd-sound   (one ADD op)",
            json: include_str!("../../circuit/descriptors/by-name/pasta-fpadd-sound.json"),
            trace: include_str!("../../circuit/tests/fixtures/pasta-fpadd-sound-trace.txt"),
            width: 128,
        },
        Atom {
            label: "pasta-fpmul-sound   (one MULTIPLY op)",
            json: include_str!("../../circuit/descriptors/by-name/pasta-fpmul-sound.json"),
            trace: include_str!("../../circuit/tests/fixtures/pasta-fpmul-sound-trace.txt"),
            width: 190,
        },
        Atom {
            label: "pasta-alu-fq-sound  (the Fq ALU row)",
            json: include_str!("../../circuit/descriptors/by-name/pasta-alu-fq-sound.json"),
            trace: include_str!("../../circuit/tests/fixtures/pasta-alu-sound-trace.txt"),
            width: 226,
        },
    ];

    // ── §1 the ONE-OP ATOMS, priced on the descriptor the prover reads ─────────────────────────
    //
    // ⚠ These are NOT run through `census_leaf_wrap`: `ir2_leaf_wrap_config` refuses them at the
    // INNER prove (`OodEvaluationMismatch { index: Some(0) }` on an 8-row `pasta-fpadd-sound`),
    // and that refusal is REPORTED rather than routed around, because it is itself a finding — the
    // narrowing's atoms have never been proved under the recursion config the fold uses, so the
    // one-op-per-row leaf is not merely unbuilt, its ingredient is unproven at this config. What
    // IS measured here is the committed width, read through the deployed `decomp_cols_pub`.
    println!("\n########## §1 — THE ONE-OP ATOMS, AT THE WIDTH THE PROVER COMMITS ##########");
    println!(
        "{:<40} {:>8} {:>7} {:>10} {:>8} {:>7}",
        "atom", "declared", "aux", "committed", "comm/dec", "rows"
    );
    for a in &atoms {
        let desc = parse_vm_descriptor2(a.json).expect("the deployed checker parses the atom");
        assert_eq!(desc.trace_width, a.width, "{}: declared width", a.label);
        let base = rows_of(a.trace);
        assert!(
            base.iter().all(|r| r.len() == a.width),
            "{}: every fixture row is {} wide",
            a.label,
            a.width
        );
        let cw = committed_width(&desc);
        println!(
            "{:<40} {:>8} {:>7} {:>10} {:>8.2} {:>7}",
            a.label,
            desc.trace_width,
            cw - desc.trace_width,
            cw,
            cw as f64 / desc.trace_width as f64,
            base.len()
        );
    }

    let mut rows: Vec<(String, usize, usize, usize, Census)> = Vec::new();

    // ── §2 the two shapes that DO prove under the leaf-wrap config ────────────────────────────
    if let Some((link_desc, link_trace, link_pis)) = chainlink_leaf() {
        let pin = link_desc.public_input_count.min(200);
        let c = census_leaf_wrap(
            "pasta-fq-chainlink  (FOLDS in production)",
            &link_desc,
            &link_trace,
            &link_pis,
            pin,
        );
        let (d, cw, h) = (
            link_desc.trace_width,
            committed_width(&link_desc),
            link_trace.len(),
        );
        rows.push((
            "pasta-fq-chainlink  (FOLDS in production)".into(),
            d,
            cw,
            h,
            c,
        ));
    } else {
        println!(
            "\n(!) chainlink fixture absent — the production control is SKIPPED, not substituted"
        );
    }

    let acc_rows = rows_of(DISCHARGING);
    let acc_desc = accumulator_descriptor(Rung::Interior).expect("segment descriptor");
    let seg: Vec<Vec<BabyBear>> = acc_rows[..8].to_vec();
    let pis = segment_public_inputs(&seg).expect("segment public inputs");
    let c = census_leaf_wrap(
        "dregg-mina-accumulator-seg  (33 ops on ONE row)",
        &acc_desc,
        &seg,
        &pis,
        ACC_PI_COUNT,
    );
    rows.push((
        "dregg-mina-accumulator-seg  (33 ops on ONE row)".into(),
        acc_desc.trace_width,
        committed_width(&acc_desc),
        8,
        c,
    ));

    println!("\n\n########## THE WIDTH LAW, MEASURED OVER FIVE EMITTED DESCRIPTORS ##########");
    println!(
        "{:<48} {:>8} {:>10} {:>5} {:>12} {:>17} {:>11} {:>11}",
        "descriptor",
        "declared",
        "committed",
        "rows",
        "wrap ops",
        "wrap LDE cells",
        "ops/dec",
        "ops/comm"
    );
    for (label, decl, comm, h, c) in &rows {
        println!(
            "{:<48} {:>8} {:>10} {:>5} {:>12} {:>17} {:>11.1} {:>11.1}",
            label,
            decl,
            comm,
            h,
            c.ops,
            c.committed_cells(),
            c.ops as f64 / *decl as f64,
            c.ops as f64 / *comm as f64
        );
    }
    println!(
        "\n⚑ `ops/comm` is the column that should be FLAT if the cost law is linear in the width \
         the prover commits. `ops/dec` is the one the file's previous draft implicitly used."
    );

    // The two facts this measurement exists to pin, as assertions rather than prose.
    let acc = rows.last().expect("the accumulator row");
    assert_eq!(acc.1, 3048, "the accumulator declares 3,048 columns");
    assert_eq!(
        acc.2, 10756,
        "…and COMMITS 10,756 — the nibble aux block is 7,708 columns, 2.5x the declared width"
    );
    assert!(
        acc.2 * 10 > acc.1 * 35,
        "the committed/declared ratio is above 3.5x, which is why a declared-width cost model \
         reads as superlinear"
    );

    // ── §4 what the aux block would be at another range-table radix ───────────────────────────
    println!("\n########## §4 — THE AUX BLOCK AS A FUNCTION OF THE RANGE-TABLE RADIX ##########");
    println!(
        "⚑ `LIMB_BITS = {}` today, so the shared byte table is {} rows and one aux column buys {} \
         bits.\n   Kimchi range-checks the same kind of limb against a 4,096-row table \
         (RANGE_CHECK_UPPERBOUND = 1 << 12).",
        dregg_circuit::descriptor_ir2::LIMB_BITS,
        1usize << dregg_circuit::descriptor_ir2::LIMB_BITS,
        dregg_circuit::descriptor_ir2::LIMB_BITS,
    );
    println!(
        "{:<40} {:>7} {:>8} {:>10} {:>8}",
        "descriptor", "radix", "aux", "committed", "vs now"
    );
    for (label, desc) in [
        ("dregg-mina-accumulator-seg", &acc_desc),
        ("pasta-fpmul-sound (one MULTIPLY)", &{
            parse_vm_descriptor2(atoms[1].json).expect("fpmul parses")
        }),
    ] {
        let now = committed_width(desc);
        for radix in [4usize, 8, 12, 16] {
            let aux = aux_at_radix(desc, radix);
            println!(
                "{:<40} {:>7} {:>8} {:>10} {:>8.2}",
                label,
                radix,
                aux,
                desc.trace_width + aux,
                (desc.trace_width + aux) as f64 / now as f64
            );
        }
    }
    println!(
        "\n⚑ 12 and 16 are WORSE, and the reason is `eval_decomp`'s partial-top-limb path: a limb \
         WIDER than the value being checked forces the whole value into `top_bits` booleans, one \
         column per BIT. The win is at radix 8, where the deployed 8-bit limbs and 16-bit carries \
         both land on a whole number of limbs."
    );

    // Radix 8 halves the aux block — re-derived from the deployed `decomp_cols_pub`, not written
    // down, so a change to the decomposition moves this assertion rather than leaving it stale.
    let aux4 = aux_at_radix(&acc_desc, 4);
    let aux8 = aux_at_radix(&acc_desc, 8);
    assert_eq!(aux4, 7708, "the deployed radix-4 aux block");
    // ⚠ Not "exactly half": 19 of the 3,048 lookups are ONE bit wide and cost one column at every
    // radix, so the ratio is 0.5024, and an `aux8 * 2 <= aux4` assertion is FALSE by 38 columns.
    // Stated as the bracket it actually is rather than as the round number it nearly is.
    assert!(
        aux8 * 100 <= aux4 * 51 && aux8 * 100 >= aux4 * 50,
        "radix 8 takes the accumulator's aux block to within [0.50, 0.51] of radix 4 \
         ({aux8} against {aux4})"
    );
}

/// The aux block the nibble decomposition would add at an arbitrary radix, computed by the SAME
/// `limb_geom` rule `decomp_cols_pub` implements. Parameterised so the deployed `LIMB_BITS = 4` is
/// one point of a curve rather than the only number anyone has.
fn aux_at_radix(desc: &EffectVmDescriptor2, radix: usize) -> usize {
    let cols = |bits: usize| -> usize {
        let n = bits.div_ceil(radix);
        let top = bits - (n - 1) * radix;
        n + if top < radix { top } else { 0 }
    };
    let mut aux = 0usize;
    for c in &desc.constraints {
        if let VmConstraint2::Lookup(l) = c {
            if let Some(bits) =
                desc.tables
                    .iter()
                    .find(|t| t.id == l.table)
                    .and_then(|t| match t.sem {
                        TableSem::Range { bits } => Some(bits),
                        _ => None,
                    })
            {
                aux += cols(bits);
            }
        }
    }
    aux
}

/// The width `Ir2Air::Main` is actually `width()`d at: declared columns plus the nibble aux block
/// `MainLayout::build` adds per declared range lookup. Read off the descriptor's own `tables`
/// through the deployed `decomp_cols_pub`, exactly as
/// `circuit/tests/pasta_sound_atom_price_and_fri_repricing.rs::committed_width` does.
fn committed_width(desc: &EffectVmDescriptor2) -> usize {
    let mut aux = 0usize;
    for c in &desc.constraints {
        if let VmConstraint2::Lookup(l) = c {
            if let Some(bits) =
                desc.tables
                    .iter()
                    .find(|t| t.id == l.table)
                    .and_then(|t| match t.sem {
                        TableSem::Range { bits } => Some(bits),
                        _ => None,
                    })
            {
                aux += decomp_cols_pub(bits);
            }
        }
    }
    desc.trace_width + aux
}

/// The production chainlink leaf, if its emitted fixture is on disk. Returned rather than
/// `expect`ed so the accumulator sweep still reports when the fixture has not been regenerated.
fn chainlink_leaf() -> Option<(EffectVmDescriptor2, Vec<Vec<BabyBear>>, Vec<BabyBear>)> {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../circuit/tests/fixtures/pasta-fq-chainlink");
    let trace = std::fs::read_to_string(dir.join("link-0-trace.txt")).ok()?;
    let pis = std::fs::read_to_string(dir.join("link-0-pis.txt")).ok()?;
    let desc = dregg_circuit_prove::mina_phase2_chain_leaf::chain_link_descriptor().ok()?;
    let t = rows_of(&trace);
    let p: Vec<BabyBear> = pis
        .split_whitespace()
        .map(|s| BabyBear::new(s.parse::<u32>().expect("pi is a u32 decimal")))
        .collect();
    if t.is_empty() || p.len() != desc.public_input_count {
        return None;
    }
    Some((desc, t, p))
}
