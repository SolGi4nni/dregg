//! # A real STARK proof of the LEAN-AUTHORED windowed Pallas RCB AIR.
//!
//! ## Substrate, said out loud
//!
//! **The AIR is Lean-authored.** `dregg-pasta-rcb-windowed::v1` is
//! `Dregg2.Circuit.Emit.PastaMsmWindowed.windowedRowDesc` — 45 constraints (42 `gate`, 3
//! `window_gate`), emitted to `circuit/descriptors/by-name/pasta-rcb-windowed.json`. Nothing in
//! this file or in `dregg_circuit::pasta_windowed_witness` authors a constraint, a gate, a builder
//! gadget or an `air_accepts` predicate. The Rust side parses the emitted descriptor, fills trace
//! CELLS, and runs the deployed `descriptor_ir2` prover. When the prover refuses a trace, the
//! WITNESS is wrong — the Lean AIR is the thing doing the checking.
//!
//! ## What is proved here, at the CURRENT resolution
//!
//! The gate bodies are integers in the Lean model and BabyBear polynomials in the deployed
//! prover. Both witness sources here (Lean's `rowAsg` fixtures and the Rust generator) make every
//! body vanish EXACTLY over ℤ, so a fortiori mod `p_babybear`; the converse does not hold. A
//! proof object therefore establishes the mod-BabyBear reading of the emitted constraints and
//! leaves the ℤ ↔ felt gap exactly where `PastaMsmWindowed` §6.2 leaves it (the shared K1
//! residual). It also inherits the undischarged FRI/STARK soundness floor. "It proves on a box"
//! is not "verified", and having a proof object closes neither residual.
//!
//! ## What the acceptance probe found
//!
//! Before `lean_descriptor_air::JsonCursor::parse_int_field`, the deployed parser REFUSED this
//! descriptor outright — `malformed integer at byte 1032`. Lean emits its `ℤ` coefficients
//! faithfully and the Pasta 9×30 value heads reach 495 bits through a degree-2 `Head.mul`, while
//! `parse_int` capped at `i64`. So the Lean-side column-bounds theorem
//! (`windowedRowDesc_columns_in_bounds`) was true, and the deployed checker still could not read
//! the file: the refusal was one layer BELOW the predicate that had been discharged.

use dregg_circuit::BabyBear;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2,
    verify_vm_descriptor2,
};
use dregg_circuit::pasta_windowed_witness::{
    COL_ACCX, COL_ACCY, COL_ACCZ, COL_BIT, COL_DBL, COL_OUTX, COL_OUTY, COL_OUTZ, Pt, RowSpec,
    TRACE_WIDTH, U256, build_trace, fold_schedule, pallas_generator, proj_eq, rcb_add, read_point,
};
use sha2::{Digest, Sha256};
use std::time::Instant;

/// The Lean-emitted windowed row descriptor.
const DESC_JSON: &str = include_str!("../descriptors/by-name/pasta-rcb-windowed.json");
/// sha256 of `DESC_JSON` — a re-emit must announce itself, not slide under a green test.
const DESC_SHA256: &str = "6c77c51a4b6a79100e4f8ff28dbb3d616d97b44c4c069e1afc4c844ea3cfa82a";

/// A Lean-emitted HONEST witness (`metatheory/EmitPastaWindowedTrace.lean`), 4 terms × 8 planes.
/// Every cell comes from `PastaMsmWindowed.rowAsg`, the assignment whose acceptance by the emitted
/// `rowGates` is `#guard`-verified in the Lean kernel — not a second witness generator.
const TRACE_64: &str = include_str!("fixtures/pasta-rcb-windowed-trace-64.txt");
/// sha256 of `TRACE_64`.
const TRACE_64_SHA256: &str = "287e2f5e542be6672bb8263451791112ffc0453ff30dd884d5655c4e641dc2c9";

/// The same emitter at 34 terms × 25 planes — the REAL Mina term count, plane count reduced.
const TRACE_1024: &str = include_str!("fixtures/pasta-rcb-windowed-trace-1024.txt");
/// sha256 of `TRACE_1024`.
const TRACE_1024_SHA256: &str = "a889d1db943d26322ddce75143bc9f4d9de719b825d77cf09ed782b8ea730925";

fn sha256_hex(bytes: &[u8]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(bytes);
    hasher
        .finalize()
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect()
}

fn descriptor() -> EffectVmDescriptor2 {
    parse_vm_descriptor2(DESC_JSON).expect("the deployed checker must parse the Lean descriptor")
}

/// Parse a Lean-emitted witness fixture into a base trace.
fn fixture_trace(text: &str) -> Vec<Vec<BabyBear>> {
    let rows: Vec<Vec<BabyBear>> = text
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(|line| {
            let row: Vec<BabyBear> = line
                .split_whitespace()
                .map(|t| BabyBear::new(t.parse::<u32>().expect("fixture cell parses as u32")))
                .collect();
            assert_eq!(row.len(), TRACE_WIDTH, "fixture row width");
            row
        })
        .collect();
    assert!(rows.len().is_power_of_two(), "fixture height");
    rows
}

/// Prove, verify, and report. Returns `(prove, verify, proof_bytes)`.
fn prove_and_verify(
    label: &str,
    desc: &EffectVmDescriptor2,
    trace: &[Vec<BabyBear>],
) -> (std::time::Duration, std::time::Duration, usize) {
    let cells = trace.len() * TRACE_WIDTH;
    let t0 = Instant::now();
    let proof = prove_vm_descriptor2(desc, trace, &[], &MemBoundaryWitness::default(), &[])
        .unwrap_or_else(|e| {
            panic!(
                "{label}: the LEAN-AUTHORED AIR refused this witness: {e}\n\
                 (that error is the AIR checking the witness — fix the WITNESS, never the AIR)"
            )
        });
    let prove_time = t0.elapsed();

    let t1 = Instant::now();
    verify_vm_descriptor2(desc, &proof, &[]).unwrap_or_else(|e| panic!("{label}: verify: {e}"));
    let verify_time = t1.elapsed();

    let bytes = postcard::to_allocvec(&proof)
        .expect("serialize proof")
        .len();
    println!(
        "[{label}] trace {}x{} = {cells} cells | prove {:?} | verify {:?} | proof {bytes} bytes",
        trace.len(),
        TRACE_WIDTH,
        prove_time,
        verify_time
    );
    (prove_time, verify_time, bytes)
}

/// Every row but the last must thread: row `i+1`'s ACC group is row `i`'s output group. This is
/// the content of the three emitted `windowGate`s, checked on the witness before the prover sees
/// it so a thread break is reported as a thread break rather than as an opaque unsat row.
fn assert_threaded(trace: &[Vec<BabyBear>]) {
    for i in 0..trace.len() - 1 {
        let out = read_point(&trace[i], COL_OUTX, COL_OUTY, COL_OUTZ);
        let next = read_point(&trace[i + 1], COL_ACCX, COL_ACCY, COL_ACCZ);
        assert_eq!(out, next, "thread broken between rows {i} and {}", i + 1);
    }
}

// =============================================================================================
// (a) the artifacts are the ones this test was written against
// =============================================================================================

#[test]
fn lean_artifacts_are_pinned() {
    assert_eq!(
        sha256_hex(DESC_JSON.as_bytes()),
        DESC_SHA256,
        "the windowed descriptor was re-emitted; re-read the Lean and re-pin"
    );
    assert_eq!(sha256_hex(TRACE_64.as_bytes()), TRACE_64_SHA256);
    assert_eq!(sha256_hex(TRACE_1024.as_bytes()), TRACE_1024_SHA256);

    let desc = descriptor();
    assert_eq!(desc.name, "dregg-pasta-rcb-windowed::v1");
    assert_eq!(desc.trace_width, TRACE_WIDTH);
    assert_eq!(desc.public_input_count, 0);
    assert_eq!(desc.constraints.len(), 45);
    assert!(desc.tables.is_empty(), "no tables, so no chip lanes");
}

// =============================================================================================
// (b) THE DESCRIPTOR ACCEPTANCE PROBE
// =============================================================================================

/// `check_descriptor2` runs FIRST inside `prove_vm_descriptor2_inner`, before any trace-shape
/// check. So an empty trace rejected with exactly "base trace must be non-empty" witnesses that
/// the deployed structural checker ACCEPTED the Lean-emitted descriptor — in particular that no
/// constraint addresses a column `>= trace_width`, the predicate
/// `windowedRowDesc_columns_in_bounds` discharges by `decide` in the Lean kernel.
#[test]
fn deployed_checker_accepts_the_lean_descriptor() {
    let desc = descriptor();
    let err = match prove_vm_descriptor2(&desc, &[], &[], &MemBoundaryWitness::default(), &[]) {
        Err(e) => e,
        Ok(_) => panic!("an empty trace cannot prove"),
    };
    assert_eq!(
        err, "base trace must be non-empty",
        "the DESCRIPTOR was rejected, not the trace: {err}"
    );
    assert!(
        !err.contains("column") && !err.contains("trace_width"),
        "column-bounds refusal: {err}"
    );
}

// =============================================================================================
// (c) THE PROOFS — Lean-emitted honest witnesses, proved and verified
// =============================================================================================

/// ⚑ **The gate.** A Lean-generated 64-row witness for a Lean-generated AIR, through the deployed
/// prover and back through the deployed verifier. Nothing in this loop depends on the Rust RCB
/// arithmetic being byte-right.
#[test]
fn lean_witness_64_proves_and_verifies() {
    let desc = descriptor();
    let trace = fixture_trace(TRACE_64);
    assert_eq!(trace.len(), 64);
    // The schedule the fixture claims: 4 terms × 8 planes, one doubling row per plane.
    let doublings = trace.iter().filter(|r| r[COL_DBL].as_u32() == 1).count();
    assert_eq!(doublings, 8, "one doubling row per bit-plane");
    for row in &trace {
        if row[COL_DBL].as_u32() == 1 {
            assert_eq!(row[COL_BIT].as_u32(), 1, "dblBitHead pins BIT on a DBL row");
        }
    }
    assert_threaded(&trace);
    prove_and_verify("lean-64", &desc, &trace);
}

/// ⚑ **The measurement.** 34 terms — the REAL Mina opening-check term count — at 25 of the 255
/// bit-planes. 875 scheduled rows padded to 1024 with genuine `acc + O` adds. Planes are the
/// linear dimension, so per-row cost extrapolates to the full 34 × 255 shape.
#[test]
fn lean_witness_1024_proves_and_verifies() {
    let desc = descriptor();
    let trace = fixture_trace(TRACE_1024);
    assert_eq!(trace.len(), 1024);
    let doublings = trace.iter().filter(|r| r[COL_DBL].as_u32() == 1).count();
    assert_eq!(doublings, 25, "one doubling row per bit-plane");
    assert_threaded(&trace);
    let (prove, _verify, bytes) = prove_and_verify("lean-1024", &desc, &trace);
    println!(
        "[lean-1024] per-row prove {:?} | full 34x255 = 8925 adds -> 16384 rows extrapolates to ~{:.1}s",
        prove / 1024,
        prove.as_secs_f64() * 16.0
    );
    assert!(bytes > 0);
}

// =============================================================================================
// (c') THE DIFFERENTIAL — the Rust witness generator against the Lean one
// =============================================================================================

/// Term `i`'s fixed scalar, `EmitPastaWindowedTrace.scalarOf`:
/// `(1234567891 + i·987654323)^7 mod 2^255`.
///
/// Only the low `n_planes` bits are ever read and `n_planes ≤ 64` in every schedule here, so
/// computing the low 64 bits with wrapping arithmetic is EXACT for the bits consumed (reduction
/// mod `2^64` is a ring homomorphism).
fn scalar_low64(i: usize) -> u64 {
    (1_234_567_891u64)
        .wrapping_add(i as u64 * 987_654_323)
        .wrapping_pow(7)
}

/// `EmitPastaWindowedTrace.schedule` — per plane, one doubling row then `n_terms` conditional
/// adds, bits taken MSB-first over `n_planes`.
fn emit_schedule(points: &[Pt], n_terms: usize, n_planes: usize) -> Vec<RowSpec> {
    assert!(n_planes <= 64, "scalar_low64 covers at most 64 planes");
    let mut sched = Vec::with_capacity(n_planes * (n_terms + 1));
    for plane in 0..n_planes {
        sched.push(RowSpec::Double);
        let bit_index = n_planes - 1 - plane;
        for (t, src) in points.iter().enumerate().take(n_terms) {
            sched.push(RowSpec::CondAdd {
                src: *src,
                bit: (scalar_low64(t) >> bit_index) & 1 == 1,
            });
        }
    }
    sched
}

/// `[k]G` for `k = 1..=n` by repeated complete addition (`EmitPastaWindowedTrace.multG`).
fn multiples_of_g(n: usize) -> Vec<Pt> {
    let g = pallas_generator();
    let mut acc = Pt::INFINITY;
    (0..n)
        .map(|_| {
            acc = rcb_add(&acc, &g);
            acc
        })
        .collect()
}

/// ⚑ The Rust witness generator reproduces the LEAN-generated 64-row witness **cell for cell**.
///
/// This is what licenses using the Rust generator at heights Lean cannot reach: it is validated
/// against the Lean witness, not against itself. It is a differential over 33,600 cells, not a
/// theorem — no formal content is claimed for it.
#[test]
fn rust_witness_reproduces_the_lean_fixture() {
    let lean = fixture_trace(TRACE_64);
    let points = multiples_of_g(4);
    let sched = emit_schedule(&points, 4, 8);
    assert_eq!(sched.len(), 40, "8 planes x (1 doubling + 4 adds)");
    let rust = build_trace(&Pt::INFINITY, &pad_to(sched, 64));

    assert_eq!(rust.len(), lean.len());
    for (i, (r, l)) in rust.iter().zip(lean.iter()).enumerate() {
        for c in 0..TRACE_WIDTH {
            assert_eq!(
                r[c].as_u32(),
                l[c].as_u32(),
                "row {i} col {c}: rust {} != lean {}",
                r[c].as_u32(),
                l[c].as_u32()
            );
        }
    }
}

/// Extend a schedule with genuine `acc + O` rows (`DBL = 0`, `BIT = 0`) to a target height.
/// `when_transition` exempts only the LAST row, so every pad row is fully constrained and must be
/// a real addition — never a zero-fill.
fn pad_to(mut sched: Vec<RowSpec>, height: usize) -> Vec<RowSpec> {
    while sched.len() < height {
        sched.push(RowSpec::CondAdd {
            src: Pt::INFINITY,
            bit: false,
        });
    }
    sched
}

/// A small end-to-end proof from the RUST generator: height 8, seven constrained rows.
#[test]
fn rust_witness_small_end_to_end() {
    let desc = descriptor();
    let g = pallas_generator();
    assert!(g.on_curve(), "the Pallas generator is on the curve");

    // Compute [11]G the way the AIR does: MSB-first over 4 planes of the scalar 11 = 0b1011,
    // one term. 4 planes x (1 doubling + 1 add) = 8 rows; the 8th is exempt from the gates but is
    // still an honest row here.
    let sched: Vec<RowSpec> = (0..4)
        .flat_map(|plane| {
            let bit = (11u32 >> (3 - plane)) & 1 == 1;
            [RowSpec::Double, RowSpec::CondAdd { src: g, bit }]
        })
        .collect();
    assert_eq!(sched.len(), 8);

    let trace = build_trace(&Pt::INFINITY, &sched);
    assert_eq!(trace.len(), 8);
    assert_eq!(trace[0].len(), TRACE_WIDTH);
    assert_threaded(&trace);

    // NON-VACUITY: the trace really computes [11]G, and [11]G is a real curve point.
    let result = fold_schedule(&Pt::INFINITY, &sched);
    let mut want = Pt::INFINITY;
    for _ in 0..11 {
        want = rcb_add(&want, &g);
    }
    assert!(proj_eq(&result, &want), "the schedule computes [11]G");
    assert!(want.on_curve());
    assert!(!want.is_infinity());

    prove_and_verify("rust-8", &desc, &trace);
}

// =============================================================================================
// (d) THE FULL MINA SHAPE — 34 terms x 255 planes = 8,925 adds, height 2^14
// =============================================================================================

/// 34 terms x 255 bit-planes, the Mina opening-check shape: 8,925 complete adds, trace height
/// 2^14 = 16,384, 8,601,600 cells. `#[ignore]`d — it is a measurement, not a gate.
///
/// Run with: `cargo test -p dregg-circuit --release --test pasta_windowed_prove -- --ignored
/// --nocapture mina_opening_shape`
#[test]
#[ignore = "measurement: 2^14 x 525 trace"]
fn mina_opening_shape_measurement() {
    const TERMS: usize = 34;
    const PLANES: usize = 255;
    const HEIGHT: usize = 16_384;

    let desc = descriptor();
    let points = multiples_of_g(TERMS);

    // 255 planes exceeds `scalar_low64`'s window, so read the scalar bits from a U256 built the
    // same way (fixed, reproducible, no randomness in a measurement).
    let scalars: Vec<U256> = (0..TERMS)
        .map(|i| {
            let mut s = U256::from_u64(1_234_567_891u64.wrapping_add(i as u64 * 987_654_323));
            let base = s;
            for _ in 0..6 {
                // A 255-bit scalar: reduce mod p to stay inside U256. Any fixed bit pattern is a
                // valid scalar for a MEASUREMENT — the cost does not depend on the value.
                s = dregg_circuit::pasta_windowed_witness::mul_mod_p(&s, &base).0;
            }
            s
        })
        .collect();

    let mut sched = Vec::with_capacity(PLANES * (TERMS + 1));
    for plane in 0..PLANES {
        sched.push(RowSpec::Double);
        let bit_index = PLANES - 1 - plane;
        for (t, src) in points.iter().enumerate() {
            let bit = (scalars[t].0[bit_index / 64] >> (bit_index % 64)) & 1 == 1;
            sched.push(RowSpec::CondAdd { src: *src, bit });
        }
    }
    assert_eq!(sched.len(), PLANES * (TERMS + 1));
    assert_eq!(sched.len(), 8_925);

    let t0 = Instant::now();
    let trace = build_trace(&Pt::INFINITY, &pad_to(sched, HEIGHT));
    println!(
        "[mina-2^14] witness generation {:?} for {} rows",
        t0.elapsed(),
        trace.len()
    );
    assert_eq!(trace.len(), HEIGHT);
    assert_threaded(&trace);

    prove_and_verify("mina-2^14", &desc, &trace);
}

/// Prove an EXTERNAL witness file, in the fixture format, named by
/// `DREGG_PASTA_WINDOWED_TRACE`. The full 34 × 255 witness is ~52 MB, too large to check in, so
/// this is how a Lean-emitted witness at that shape gets measured without committing it.
/// Skips cleanly when the variable is unset or the file is missing — this must not become a hard
/// dependency on anyone's scratchpad.
///
/// `DREGG_PASTA_WINDOWED_TRACE=/path/to/trace.txt cargo test -p dregg-circuit --release
///  --test pasta_windowed_prove -- --ignored --nocapture external_witness`
#[test]
#[ignore = "measurement: needs DREGG_PASTA_WINDOWED_TRACE"]
fn external_witness_proves_and_verifies() {
    let Ok(path) = std::env::var("DREGG_PASTA_WINDOWED_TRACE") else {
        println!("DREGG_PASTA_WINDOWED_TRACE unset — skipping");
        return;
    };
    let Ok(text) = std::fs::read_to_string(&path) else {
        println!("{path}: unreadable — skipping");
        return;
    };
    let desc = descriptor();
    let t0 = Instant::now();
    let trace = fixture_trace(&text);
    println!(
        "[external] parsed {} rows in {:?}",
        trace.len(),
        t0.elapsed()
    );
    let doublings = trace.iter().filter(|r| r[COL_DBL].as_u32() == 1).count();
    println!("[external] {doublings} doubling rows (= bit-planes)");
    assert_threaded(&trace);
    prove_and_verify("external", &desc, &trace);
}
