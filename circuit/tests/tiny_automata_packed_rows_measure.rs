//! # PACK `s` STEPS PER TRACE ROW — does dividing TRACE ROWS by `s` divide PROVE TIME by `s`?
//!
//! `tiny_automata_prove_time_attack.rs` attributed 97.9% of a `k = 4, n = 1024` prove to
//! Poseidon2 Merkle commitment of the trace (first digest layer 55.9% + build merkle tree
//! 42.0%), so prove time is ~linear in TRACE ROWS. The Lean-authored packed descriptor
//! family `metatheory/Dregg2/Circuit/Emit/TinyAutomataPacked.lean` spends `s` DFA steps per
//! row instead of one, taking an `n`-symbol word from `n` rows to `n / s` rows at width
//! `2s + 1`. This file MEASURES what that buys.
//!
//! ## Two grids, and the difference between them is load-bearing
//!
//! * **`W` — THE WITNESSED GRID.** Bytes emitted by Lean (`EmitTinyAutomataPacked.lean`):
//!   `emitVmJson2 (packMeas n s)` plus the COLUMN VALUES of `packMeasWit n s`. Every point
//!   carries `TinyAutomataPacked.packMeas_satisfies : Satisfied2Public hash0 (packMeas n s)
//!   … (packMeasWit n s)` — a real Lean witness for the object being timed. The deployed
//!   `exact_public_rows` tooth pushes ONE batch AIR instance per DECLARED row and caps the
//!   manifest at `MAX_EXACT_PUBLIC_ROWS = 128` (`circuit/src/descriptor_ir2.rs:378`), and the
//!   declared table is the RUN table (one row per input symbol, invariant in `s`), so this
//!   grid stops at `n = 128`.
//!
//! * **`G` — THE GEOMETRY PROXY, NOT A WITNESSED DESCRIPTOR.** The SAME row geometry
//!   (`2s + 1` columns × `n / s` rows, `s` lookups + 1 window gate + 2 pi bindings) with the
//!   exact-public table swapped for the shared RANGE table, which is what
//!   `tiny_automata_prove_time_attack.rs`'s "shape B" does: 2 batch instances instead of
//!   `1 + n`. It proves and verifies in Rust, but it is NOT the Lean-witnessed object — it
//!   carries no DFA binding. It exists only to reach `n = 256` and `n = 1024`, where the
//!   row-scaling law lives. NEVER quote a `G` number as a cost of the packed DFA descriptor.
//!
//! ## ⚑ WHAT IT MEASURED (2026-07-25, this box, USER CPU per prove, `RAYON_NUM_THREADS=1`)
//!
//! Box at load average 78–280 on 12 cores, so in-process WALL numbers are not reported. Every
//! number below is `(user(reps=R) − user(reps=0))/R` under `/usr/bin/time -p`, `R = 12…20`,
//! and every point PROVED and VERIFIED before it was timed. `PACKED_POW=0` throughout: the
//! 16-bit FRI grind is a FIXED per-`(descriptor, witness)` geometric draw (0.7–36 ms,
//! size-independent) and at production PoW it BURIED the signal — the same `W n=128` grid read
//! 46 / 68 / 70 / 27 / 49 / 33 ms with no trend. Everything else stays at the deployed FRI point
//! (`log_blowup = 6`, 19 queries).
//!
//! **(1) `W` — THE LEAN-WITNESSED PACKED DESCRIPTOR. Packing buys 1.6×, and STOPS.**
//!
//! ```text
//!  n=128, 129 batch instances     s    1     2     4     8    16    32
//!    trace rows (= n/s)               128    64    32    16     8     4
//!    trace width (= 2s+1)               3     5     9    17    33    65
//!    prove ms (user CPU)            36.50 29.50 25.50 24.00 23.00 24.00
//!    speedup vs s=1                  1.00  1.24  1.43  1.52  1.59  1.52
//!    wire B                        289755 286569 284273 279921 281515 291927
//! ```
//!
//! The six points fit `T(s) = 0.1125 · (128/s) + 22.1 ms` to ±0.2 ms for `s ≤ 16` (the `s = 32`
//! point is +1.4 ms over the fit — the width-65 row). So **62% of this prove is a floor packing
//! cannot touch**: `22.1 ms / 129 = 0.171 ms` per `ExactPublicRow` batch instance, one per
//! DECLARED manifest row — and the declared table is the RUN table, invariant in `s`. The
//! `n = 32` grid (33 instances) is consistent: 10.50 / 7.00 / 6.50 / 7.00 ms at `s = 1,2,4,8`.
//!
//! **(2) `G` — THE GEOMETRY PROXY (2 instances). The row lever is REAL but SUBLINEAR.**
//!
//! ```text
//!  n=1024        s      1     2     4     8    16    32    64
//!    rows            1024   512   256   128    64    32    16
//!    width              3     5     9    17    33    65   129
//!    prove ms      137.50 74.17 46.67 33.33 25.00 23.33 19.17
//!    speedup         1.00  1.85  2.95  4.13  5.50  5.89  7.17     (ideal 1,2,4,8,16,32,64)
//!    wire B         74797 71421 69512 62562 66411 78792 99328
//!
//!  n=256         s      1     2     4     8    16    32
//!    prove ms       35.00 19.17 14.17 10.00  5.83  8.33
//!    speedup         1.00  1.83  2.47  3.50  6.00  4.20   <- TURNS BACK UP at 8 rows
//! ```
//!
//! Over `s = 1 → 8` the empirical exponent is `log₂(4.13)/log₂(8) = 0.68`, i.e. **`T ∝ s^-0.68`,
//! not `s^-1`** — exactly the width-sensitivity the profile predicts, because halving the rows
//! doubles the felts each first-digest-layer Poseidon2 row-hash must absorb. The per-row cost
//! `0.107–0.1125 ms` agrees between the `G` and `W` grids, as it must (same commit machinery).
//!
//! **(3) WHERE IT FLATTENS — the real "megafast" limit.** At `n = 1024` the curve is at 5.5× by
//! `s = 16` and gains only 1.7× more over the next TWO doublings (23.33 → 19.17 ms), against a
//! size-independent floor of ~13 ms of FRI folding/query/final-poly. At `n = 256` it INVERTS at
//! `s = 32` (8 rows, width 65: 5.83 → 8.33 ms). **The knee is at 8–32 trace rows.** Past it the
//! wire also turns: `n = 1024` bytes bottom out at `s = 8` (62.6 KB) and are +59% by `s = 64`
//! (99.3 KB), because every FRI query opens a wider row. `s = 8` is the byte-optimal point;
//! `s = 16–32` the time-optimal one.
//!
//! ## Running (release; debug times are lies and `debug_assertions` also switches on
//! plonky3's in-prover `check_constraints`)
//!
//! ```text
//! # emit the Lean artifacts first
//! cd metatheory && lake env lean --run EmitTinyAutomataPacked.lean /tmp/packed
//!
//! # the whole grid, in-process wall clock (noisy on a loaded box)
//! PACKED_DIR=/tmp/packed cargo test -p dregg-circuit --release \
//!   --test tiny_automata_packed_rows_measure -- --nocapture
//!
//! # ONE point, USER CPU (the contention-robust reading; subtract the REPS=0 baseline)
//! PACKED_DIR=/tmp/packed PACKED_ONE=W:128:4 PACKED_REPS=8 RAYON_NUM_THREADS=1 \
//!   /usr/bin/time -p <bin> packed_one_point --exact --nocapture
//! ```

use std::path::PathBuf;
use std::time::Instant;

use dregg_circuit::descriptor_ir2::{
    IR2_FRI_LOG_BLOWUP, IR2_FRI_LOG_FINAL_POLY_LEN, IR2_FRI_MAX_LOG_ARITY, IR2_FRI_NUM_QUERIES,
    IR2_FRI_QUERY_POW_BITS, MemBoundaryWitness, TID_RANGE, parse_vm_descriptor2,
    prove_vm_descriptor2_with_config, verify_vm_descriptor2_with_config,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::plonky3_prover::{DreggStarkConfig, create_config_with_fri};

// ============================================================================
// W — the Lean-emitted, Lean-witnessed packed descriptor
// ============================================================================

fn artifact_dir() -> Option<PathBuf> {
    std::env::var("PACKED_DIR").ok().map(PathBuf::from)
}

/// Read `<dir>/n{n}_s{s}.{json,trace,pis}` — the three artifacts Lean emits for one point.
/// NOTHING here reconstructs the descriptor or the witness: the bytes are Lean's.
fn load_witnessed(
    dir: &PathBuf,
    n: usize,
    s: usize,
) -> (String, Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let base = dir.join(format!("n{n}_s{s}"));
    let json = std::fs::read_to_string(base.with_extension("json"))
        .unwrap_or_else(|e| panic!("missing Lean descriptor for n={n} s={s}: {e}"));
    let trace_txt = std::fs::read_to_string(base.with_extension("trace"))
        .unwrap_or_else(|e| panic!("missing Lean trace for n={n} s={s}: {e}"));
    let pis_txt = std::fs::read_to_string(base.with_extension("pis"))
        .unwrap_or_else(|e| panic!("missing Lean pis for n={n} s={s}: {e}"));
    let trace: Vec<Vec<BabyBear>> = trace_txt
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| {
            l.split_whitespace()
                .map(|v| BabyBear::new(v.parse::<u32>().expect("felt")))
                .collect()
        })
        .collect();
    let pis: Vec<BabyBear> = pis_txt
        .split_whitespace()
        .map(|v| BabyBear::new(v.parse::<u32>().expect("felt")))
        .collect();
    (json, trace, pis)
}

// ============================================================================
// G — the geometry proxy (range table, 2 batch instances). NOT witnessed in Lean.
// ============================================================================

/// The packed row geometry with a RANGE-table lookup standing in for the exact-public
/// transition lookup: `2s + 1` columns, `s` lookups on the symbol columns `1, 3, …, 2s-1`,
/// one continuity window `nxt(0) - loc(2s)`, and the two boundary pins.
fn proxy_json(n: usize, s: usize) -> String {
    let width = 2 * s + 1;
    let last = 2 * s;
    let mut constraints: Vec<String> = Vec::new();
    for j in 0..s {
        constraints.push(format!(
            "{{\"t\":\"lookup\",\"table\":{TID_RANGE},\"tuple\":[{{\"t\":\"var\",\"v\":{}}}]}}",
            2 * j + 1
        ));
    }
    constraints.push(format!(
        "{{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{{\"t\":\"add\",\"l\":{{\"t\":\"nxt\",\"c\":0}},\"r\":{{\"t\":\"mul\",\"l\":{{\"t\":\"const\",\"v\":-1}},\"r\":{{\"t\":\"loc\",\"c\":{last}}}}}}}}}"
    ));
    constraints
        .push("{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":0,\"pi_index\":0}".to_string());
    constraints.push(format!(
        "{{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":{last},\"pi_index\":1}}"
    ));
    format!(
        "{{\"name\":\"packed-geometry-proxy-n{n}-s{s}\",\"ir\":2,\"trace_width\":{width},\"public_input_count\":2,\
         \"tables\":[{{\"id\":{TID_RANGE},\"name\":\"range\",\"arity\":1,\"sem\":\"range\",\"bits\":4}}],\
         \"constraints\":[{}],\"hash_sites\":[],\"ranges\":[]}}",
        constraints.join(",")
    )
}

fn proxy_sym(i: usize) -> u32 {
    ((i * 7 + i / 3) % 2) as u32
}

/// The proxy witness: the SAME interleaved layout the Lean witness uses
/// (`q0, y0, q1, y1, …, q_s`), chained across rows, with a toy step `q ^ y`.
fn proxy_trace(n: usize, s: usize) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let m = n / s;
    let mut cur: u32 = 0;
    let mut rows: Vec<Vec<BabyBear>> = Vec::with_capacity(m);
    let mut idx = 0usize;
    for _ in 0..m {
        let mut r: Vec<BabyBear> = Vec::with_capacity(2 * s + 1);
        r.push(BabyBear::new(cur));
        for _ in 0..s {
            let y = proxy_sym(idx);
            idx += 1;
            let nxt = cur ^ y;
            r.push(BabyBear::new(y));
            r.push(BabyBear::new(nxt));
            cur = nxt;
        }
        rows.push(r);
    }
    let first = rows[0][0];
    let last = rows[m - 1][2 * s];
    (rows, vec![first, last])
}

// ============================================================================
// The timed leg
// ============================================================================

struct Point {
    label: String,
    json: String,
    trace: Vec<Vec<BabyBear>>,
    pis: Vec<BabyBear>,
}

fn build_point(kind: &str, n: usize, s: usize) -> Point {
    match kind {
        "W" => {
            let dir = artifact_dir().expect("PACKED_DIR must point at the Lean-emitted artifacts");
            let (json, trace, pis) = load_witnessed(&dir, n, s);
            Point {
                label: format!("W n={n} s={s}"),
                json,
                trace,
                pis,
            }
        }
        "G" => {
            let (trace, pis) = proxy_trace(n, s);
            Point {
                label: format!("G n={n} s={s}"),
                json: proxy_json(n, s),
                trace,
                pis,
            }
        }
        other => panic!("unknown grid kind {other}"),
    }
}

/// The FRI query proof-of-work bits to prove under. Defaults to the production
/// `IR2_FRI_QUERY_POW_BITS = 16`; `PACKED_POW=0` removes the grind. Setting it to 0 is a
/// MEASUREMENT-ONLY knob: the committed harness established that the 16-bit grind is a FIXED
/// geometric draw per `(descriptor, witness)` costing anywhere from 0.7 ms to 36 ms and NOT
/// scaling with the trace, so it is pure per-point noise on a row-scaling law. Everything else
/// (`log_blowup = 6`, `19` queries) stays at the deployed point.
fn pow_bits() -> usize {
    std::env::var("PACKED_POW")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(IR2_FRI_QUERY_POW_BITS)
}

fn config() -> DreggStarkConfig {
    create_config_with_fri(
        IR2_FRI_LOG_BLOWUP,
        IR2_FRI_LOG_FINAL_POLY_LEN,
        IR2_FRI_MAX_LOG_ARITY,
        IR2_FRI_NUM_QUERIES,
        pow_bits(),
    )
}

/// Prove + verify ONCE (the witness leg: a number is only ever printed for an object that
/// really proves and really verifies), then time `reps` proves and keep the minimum.
fn measure(p: &Point, reps: usize) -> (f64, usize, usize, usize, usize) {
    let desc = parse_vm_descriptor2(&p.json).unwrap_or_else(|e| panic!("{} parse: {e}", p.label));
    let mem = MemBoundaryWitness::default();
    let heaps: Vec<Vec<dregg_circuit::heap_root::HeapLeaf>> = vec![];
    let cfg = config();
    let warm = prove_vm_descriptor2_with_config(&desc, &p.trace, &p.pis, &mem, &heaps, &cfg)
        .unwrap_or_else(|e| panic!("{} must prove: {e}", p.label));
    verify_vm_descriptor2_with_config(&desc, &warm, &p.pis, &cfg)
        .unwrap_or_else(|e| panic!("{} must verify: {e:?}", p.label));
    let inst = warm.degree_bits.len();
    let bytes = postcard::to_allocvec(&warm).expect("postcard").len();
    drop(warm);
    let mut best = f64::INFINITY;
    for _ in 0..reps {
        let t0 = Instant::now();
        let proof = prove_vm_descriptor2_with_config(&desc, &p.trace, &p.pis, &mem, &heaps, &cfg)
            .expect("proves");
        let ms = t0.elapsed().as_secs_f64() * 1000.0;
        std::hint::black_box(&proof);
        best = best.min(ms);
    }
    (best, inst, bytes, p.trace.len(), desc.trace_width)
}

/// **CPU-TIME MODE**, exactly the discipline `tiny_automata_prove_time_attack.rs` prescribes
/// for this co-tenant box: one process, one point, `PACKED_REPS` proves, read USER CPU off
/// `/usr/bin/time -p` and subtract the `PACKED_REPS=0` baseline. `PACKED_REPS=0` still runs
/// the prove+verify witness leg, so the baseline itself proves the timed object is satisfiable.
#[test]
#[ignore = "MEASUREMENT DRIVER, not a test: with PACKED_ONE unset it returns immediately and \
            reported PASSED, a green that asserted nothing. Ignored so it reports SKIPPED instead. \
            Run it as PACKED_ONE=W:16:4 PACKED_REPS=20 … -- --ignored --exact packed_one_point."]
fn packed_one_point() {
    let Ok(spec) = std::env::var("PACKED_ONE") else {
        return;
    };
    let f: Vec<&str> = spec.split(':').collect();
    assert_eq!(f.len(), 3, "PACKED_ONE=<W|G>:<n>:<s>");
    let n: usize = f[1].parse().expect("n");
    let s: usize = f[2].parse().expect("s");
    let reps: usize = std::env::var("PACKED_REPS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(8);
    let p = build_point(f[0], n, s);
    let (_, inst, bytes, rows, width) = measure(&p, reps);
    println!(
        "packed_one_point {spec} pow={} reps={reps} rows={rows} width={width} inst={inst} wire={bytes}",
        pow_bits()
    );
}

/// The whole grid with in-process wall timing. Useful when the box is quiet; on a loaded box
/// read the CPU-time mode above instead. Wall numbers are printed as `min of reps`.
#[test]
fn packed_grid_wall() {
    let reps: usize = std::env::var("PACKED_REPS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(3);
    if artifact_dir().is_some() {
        println!(
            "\n== W: THE LEAN-WITNESSED PACKED DESCRIPTOR (exact_public_rows, 1+n instances) =="
        );
        println!(
            "   {:>8} {:>3} {:>3}  {:>6} {:>6}  {:>6}  {:>10}  {:>10}",
            "label", "n", "s", "rows", "width", "inst", "min ms", "wire B"
        );
        for n in [32usize, 64, 128] {
            for s in [1usize, 2, 4, 8, 16] {
                if n % s != 0 {
                    continue;
                }
                let p = build_point("W", n, s);
                let (ms, inst, bytes, rows, width) = measure(&p, reps);
                println!(
                    "   {:>8} {n:>3} {s:>3}  {rows:>6} {width:>6}  {inst:>6}  {ms:>10.2}  {bytes:>10}",
                    "packed"
                );
            }
        }
    } else {
        println!("PACKED_DIR unset — skipping the WITNESSED grid (run the Lean emitter first)");
    }

    println!(
        "\n== G: GEOMETRY PROXY (range table, 2 instances) — NOT a Lean-witnessed descriptor =="
    );
    println!(
        "   {:>8} {:>5} {:>3}  {:>6} {:>6}  {:>6}  {:>10}  {:>10}",
        "label", "n", "s", "rows", "width", "inst", "min ms", "wire B"
    );
    for n in [256usize, 1024] {
        for s in [1usize, 2, 4, 8] {
            let p = build_point("G", n, s);
            let (ms, inst, bytes, rows, width) = measure(&p, reps);
            println!(
                "   {:>8} {n:>5} {s:>3}  {rows:>6} {width:>6}  {inst:>6}  {ms:>10.2}  {bytes:>10}",
                "proxy"
            );
        }
    }
}
