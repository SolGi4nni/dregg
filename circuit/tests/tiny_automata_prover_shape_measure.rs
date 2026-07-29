//! ⚑⚑ **SUPERSEDED AXIS (2026-07-29) — READ BEFORE QUOTING ANY PER-INSTANCE NUMBER BELOW.**
//!
//! Every figure in this file that prices an `Ir2Air::ExactPublicRow` BATCH INSTANCE, or that
//! treats `MAX_EXACT_PUBLIC_ROWS = 128` as a reachability limit, was measured against a
//! realization that no longer exists. `Ir2Air::ExactPublicTable` carries a whole Lean-emitted
//! manifest as ONE multiplicity-bearing instance with the rows in a preprocessed matrix — which
//! is the shape this file's own CONTROL (shape B, the range/byte table) always had. So the
//! deployed exact-public shape costs 2 instances at every `(k, n, m)`, the caps are `2^21` rows /
//! `2^25` cells, and the points this file reported as INEXPRESSIBLE now prove. The trace-row,
//! FRI-knob and Poseidon2-profile measurements are UNAFFECTED and still stand; the per-instance
//! and cap-reachability ones are HISTORY. The tests themselves have been updated and are green.
//!
//! # MEGAFAST-PROVER-PATH — what does a k-fold composed tiny automaton COST to prove?
//!
//! The composed-automaton size story (few columns, few gates) says nothing about PROVER time,
//! which is driven by trace ROWS x columns, the number of batch INSTANCES, the LogUp auxiliary
//! (extension-field) columns, and the FRI/commitment layer over all of them. This file MEASURES
//! the two candidate composition shapes at identical `(n rows, k lanes)` grids, on the REAL
//! deployed IR-v2 prover (`descriptor_ir2::prove_vm_descriptor2`, production `ir2_config`:
//! `log_blowup = 6, 19 queries, 16 PoW bits`).
//!
//! Both shapes prove the SAME per-lane statement — a toggle DFA (`step(s,y) = s XOR y`) run over
//! an n-symbol word, with the continuity window gate and the two boundary PI pins — differing
//! ONLY in how the transition tooth reaches a table:
//!
//!   * **Shape A — `exact_public_rows`** (the DEPLOYED table-as-input carrier that
//!     `metatheory/Dregg2/Circuit/Emit/DfaRoutingTableEmit.lean` emits): the manifest is committed
//!     by the descriptor bytes, and `descriptor_ir2::instance_airs` pushes ONE `Ir2Air::ExactPublicRow`
//!     BATCH INSTANCE PER DECLARED ROW, each unit-capacity. Exact-multiset LogUp ⇒ the manifest must
//!     be the exact multiset of queries ⇒ `#declared rows = k · n`. So the batch carries `1 + k·n`
//!     instances.
//!   * **Shape B — a SHARED multiplicity-carrying table** (the byte/range table, the same mechanism
//!     `eval_decomp` already uses in production): ONE table AIR of fixed height serves every lane's
//!     every row through `LookupBus::table_entry(.., multiplicity)`. The batch carries 2 instances
//!     regardless of `(n, k)`.
//!
//! Shape B here uses a 4-bit range lookup on the symbol column as the stand-in for the transition
//! lookup: same bus machinery, same one-global-interaction-per-lookup accounting (p3-lookup gives
//! each interaction its OWN extension aux column — `Lookups::from_interactions`), differing only in
//! tuple arity (1 vs 3), which changes the beta-combination but not the column count. It is a
//! LOWER BOUND proxy for the amortizing shape, not a proof that the amortizing shape is sound.
//!
//! Nothing here changes a production parameter. Run (release; debug times would be lies):
//!   cargo test -p dregg-circuit --release --test tiny_automata_prover_shape_measure -- --nocapture

use std::time::Instant;

use dregg_circuit::descriptor_ir2::{
    MemBoundaryWitness, TID_RANGE, parse_vm_descriptor2, prove_vm_descriptor2,
    verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;

/// `.custom 30` = wire id 35, exactly as `DfaRoutingTableEmit.TRT_TID`.
const TRT_TID: usize = 35;

fn kib(bytes: usize) -> f64 {
    bytes as f64 / 1024.0
}

/// A deterministic bit stream (no rand dep; the word content is irrelevant to cost).
fn sym_at(lane: usize, row: usize) -> u32 {
    let x = (lane as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15)
        ^ (row as u64).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    ((x >> 33) & 1) as u32
}

/// One lane's `(current, symbol, next)` chain for the toggle DFA from state 0.
fn lane_chain(lane: usize, n: usize) -> Vec<(u32, u32, u32)> {
    let mut cur = 0u32;
    let mut out = Vec::with_capacity(n);
    for row in 0..n {
        let sym = sym_at(lane, row);
        let next = cur ^ sym;
        out.push((cur, sym, next));
        cur = next;
    }
    out
}

/// Shape A: the deployed `exact_public_rows` table-routing descriptor, k lanes over ONE table.
/// The manifest is the exact multiset of all `k·n` queries (duplicates carry multiplicity).
fn shape_a_json(k: usize, n: usize) -> String {
    shape_a_json_m(k, n, 1)
}

/// Shape A with `m` IDENTICAL transition lookups per lane per row.
///
/// This is the DECLARED-ROW AXIS: it multiplies the declared manifest (and hence the
/// `ExactPublicRow` batch-instance count) by `m` while leaving the main trace — `n` rows,
/// `3k` columns, the same witness values — bit-identically unchanged. Exact-multiset LogUp
/// forces `#declared rows = #queries`, so declared rows CANNOT be varied without varying the
/// query count; `m` is the only way to move declared rows at a FIXED trace, and the
/// LogUp-aux-column cost that rides along with it is subtracted out by the matching
/// `shape_b_json_m` control (which adds the same `m` interactions and NO instances).
fn shape_a_json_m(k: usize, n: usize, m: usize) -> String {
    let mut manifest: Vec<String> = Vec::with_capacity(k * n * m);
    for lane in 0..k {
        for (c, s, x) in lane_chain(lane, n) {
            for _ in 0..m {
                manifest.push(format!("[{c},{s},{x}]"));
            }
        }
    }
    let mut constraints: Vec<String> = Vec::new();
    for j in 0..k {
        let (c, s, x) = (3 * j, 3 * j + 1, 3 * j + 2);
        for _ in 0..m {
            constraints.push(format!(
                "{{\"t\":\"lookup\",\"table\":{TRT_TID},\"tuple\":[{{\"t\":\"var\",\"v\":{c}}},{{\"t\":\"var\",\"v\":{s}}},{{\"t\":\"var\",\"v\":{x}}}]}}"
            ));
        }
        constraints.push(format!(
            "{{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{{\"t\":\"add\",\"l\":{{\"t\":\"nxt\",\"c\":{c}}},\"r\":{{\"t\":\"mul\",\"l\":{{\"t\":\"const\",\"v\":-1}},\"r\":{{\"t\":\"loc\",\"c\":{x}}}}}}}}}"
        ));
        constraints.push(format!(
            "{{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":{c},\"pi_index\":{}}}",
            2 * j
        ));
        constraints.push(format!(
            "{{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":{x},\"pi_index\":{}}}",
            2 * j + 1
        ));
    }
    format!(
        "{{\"name\":\"megafast-shape-a-k{k}-n{n}-m{m}\",\"ir\":2,\"trace_width\":{},\"public_input_count\":{},\
         \"tables\":[{{\"id\":{TRT_TID},\"name\":\"dfa_transition_table\",\"arity\":3,\"sem\":\"exact_public_rows\",\"rows\":[{}]}}],\
         \"constraints\":[{}],\"hash_sites\":[],\"ranges\":[]}}",
        3 * k,
        2 * k,
        manifest.join(","),
        constraints.join(",")
    )
}

/// Shape B: identical lanes, but the per-row tooth is a lookup into the SHARED
/// multiplicity-carrying range table (ONE table AIR of height `2^bits` for all lanes, all rows —
/// the same `LookupBus::table_entry(.., multiplicity)` machinery `eval_decomp` uses in production).
fn shape_b_json(k: usize, n: usize) -> String {
    shape_b_json_m(k, n, 1)
}

/// Shape B with `m` identical lookups per lane per row: the CONTROL for `shape_a_json_m`.
/// Same main trace, same `m·k` bus interactions (hence the same `m·k` LogUp extension aux
/// columns), and STILL exactly 2 batch instances. Subtracting this from `shape_a_json_m` at the
/// same `(k, n, m)` isolates the per-DECLARED-ROW (per-`ExactPublicRow`-instance) cost from the
/// aux-column cost that exact-multiset semantics forces to move with it.
fn shape_b_json_m(k: usize, n: usize, m: usize) -> String {
    let mut constraints: Vec<String> = Vec::new();
    for j in 0..k {
        let (c, s, x) = (3 * j, 3 * j + 1, 3 * j + 2);
        for _ in 0..m {
            constraints.push(format!(
                "{{\"t\":\"lookup\",\"table\":{TID_RANGE},\"tuple\":[{{\"t\":\"var\",\"v\":{s}}}]}}"
            ));
        }
        constraints.push(format!(
            "{{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{{\"t\":\"add\",\"l\":{{\"t\":\"nxt\",\"c\":{c}}},\"r\":{{\"t\":\"mul\",\"l\":{{\"t\":\"const\",\"v\":-1}},\"r\":{{\"t\":\"loc\",\"c\":{x}}}}}}}}}"
        ));
        constraints.push(format!(
            "{{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":{c},\"pi_index\":{}}}",
            2 * j
        ));
        constraints.push(format!(
            "{{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":{x},\"pi_index\":{}}}",
            2 * j + 1
        ));
    }
    format!(
        "{{\"name\":\"megafast-shape-b-k{k}-n{n}-m{m}\",\"ir\":2,\"trace_width\":{},\"public_input_count\":{},\
         \"tables\":[{{\"id\":{TID_RANGE},\"name\":\"range\",\"arity\":1,\"sem\":\"range\",\"bits\":4}}],\
         \"constraints\":[{}],\"hash_sites\":[],\"ranges\":[]}}",
        3 * k,
        2 * k,
        constraints.join(",")
    )
}

/// The shared main trace for both shapes: k lanes of `(current, symbol, next)`.
fn trace_and_pis(k: usize, n: usize) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let chains: Vec<Vec<(u32, u32, u32)>> = (0..k).map(|lane| lane_chain(lane, n)).collect();
    let mut rows = Vec::with_capacity(n);
    for row in 0..n {
        let mut r = Vec::with_capacity(3 * k);
        for chain in &chains {
            let (c, s, x) = chain[row];
            r.push(BabyBear::new(c));
            r.push(BabyBear::new(s));
            r.push(BabyBear::new(x));
        }
        rows.push(r);
    }
    let mut pis = Vec::with_capacity(2 * k);
    for chain in &chains {
        pis.push(BabyBear::new(chain[0].0));
        pis.push(BabyBear::new(chain[n - 1].2));
    }
    (rows, pis)
}

struct Measured {
    instances: usize,
    main_width: usize,
    /// BEST-OF-`reps()` prove wall time. This box is a shared co-tenant build machine
    /// (load average ~80-120 during this run), so the median is contaminated by other
    /// processes; the minimum is the least-contended sample and is what the scaling law
    /// is read off. The MEDIAN is printed beside it so the contamination is visible.
    prove_ms: f64,
    prove_median_ms: f64,
    verify_ms: f64,
    bytes: usize,
}

/// Repeats per grid point (`MEGAFAST_REPS`, default 31). The rayon pool + the thread-local `ir2_config` warm on the first
/// call, so a single timing is pure noise (28.5 ms then 11.6 ms then 6.9 ms on the same box for
/// MONOTONICALLY GROWING work). We report the MEDIAN of `REPS` timed runs after one discarded
/// warm-up, which is what the scaling law is read off.
fn reps() -> usize {
    std::env::var("MEGAFAST_REPS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(31)
}

fn median(mut xs: Vec<f64>) -> f64 {
    xs.sort_by(|a, b| a.partial_cmp(b).unwrap());
    xs[xs.len() / 2]
}

fn best(xs: &[f64]) -> f64 {
    xs.iter().copied().fold(f64::INFINITY, f64::min)
}

fn measure(label: &str, json: &str, k: usize, n: usize) -> Measured {
    let desc = parse_vm_descriptor2(json).expect("descriptor parses");
    let (trace, pis) = trace_and_pis(k, n);
    let mem = MemBoundaryWitness::default();
    let heaps: Vec<Vec<dregg_circuit::heap_root::HeapLeaf>> = vec![];

    // Warm-up (discarded): rayon pool spin-up + the thread-local FRI config build.
    let warm = prove_vm_descriptor2(&desc, &trace, &pis, &mem, &heaps)
        .unwrap_or_else(|e| panic!("{label} k={k} n={n} must prove: {e}"));
    verify_vm_descriptor2(&desc, &warm, &pis)
        .unwrap_or_else(|e| panic!("{label} k={k} n={n} must verify: {e:?}"));

    let reps = reps();
    let mut prove_samples = Vec::with_capacity(reps);
    let mut verify_samples = Vec::with_capacity(reps);
    let mut bytes = 0usize;
    let mut instances = 0usize;
    let mut degree_bits: Vec<usize> = Vec::new();
    for _ in 0..reps {
        let t0 = Instant::now();
        let proof = prove_vm_descriptor2(&desc, &trace, &pis, &mem, &heaps).expect("proves");
        prove_samples.push(t0.elapsed().as_secs_f64() * 1000.0);
        let t1 = Instant::now();
        verify_vm_descriptor2(&desc, &proof, &pis).expect("verifies");
        verify_samples.push(t1.elapsed().as_secs_f64() * 1000.0);
        bytes = postcard::to_allocvec(&proof).expect("postcard").len();
        instances = proof.degree_bits.len();
        degree_bits = proof.degree_bits.clone();
    }

    let m = Measured {
        instances,
        main_width: desc.trace_width,
        prove_ms: best(&prove_samples),
        prove_median_ms: median(prove_samples),
        verify_ms: best(&verify_samples),
        bytes,
    };
    println!(
        "{label:>8} k={k:<3} n={n:<5} inst={:<5} main_w={:<4} prove(best)={:>8.2} ms (med {:>8.2})  verify(best)={:>7.2} ms  wire={:>8} B ({:>7.1} KiB)  main_degree_bits={}",
        m.instances,
        m.main_width,
        m.prove_ms,
        m.prove_median_ms,
        m.verify_ms,
        m.bytes,
        kib(m.bytes),
        degree_bits[0],
    );
    m
}

/// A: the DEPLOYED exact-public shape. n sweep at k=1, then k sweep at n=16.
///
/// ⚑ **2026-07-29: THIS AXIS IS GONE, AND ITS DISAPPEARANCE IS THE MEASUREMENT.** Shape A used to
/// cost `1 + k·n` batch instances — one per declared manifest ROW — and `MAX_EXACT_PUBLIC_ROWS =
/// 128` hard-bounded `k·n ≤ 128` because of it. `Ir2Air::ExactPublicTable` realizes a manifest as
/// ONE multiplicity-bearing instance with the rows in a preprocessed matrix, which is precisely
/// the shape this file's own CONTROL (shape B, the range/byte table) always had. So shape A now
/// costs 2 instances at every `(k, n)`, exactly like shape B, and the sweep below asserts the
/// COLLAPSE rather than the slope. The caps are now `2^21` rows / `2^25` cells.
#[test]
fn shape_a_exact_public_scaling() {
    println!(
        "== SHAPE A: deployed `exact_public_rows` table routing (2 batch instances, ALWAYS) =="
    );
    for n in [8usize, 16, 32, 64, 128] {
        let m = measure("A", &shape_a_json(1, n), 1, n);
        assert_eq!(
            m.instances, 2,
            "the manifest is ONE instance now, not one per declared row"
        );
    }
    for k in [1usize, 2, 4, 8] {
        let n = 16;
        let m = measure("A", &shape_a_json(k, n), k, n);
        assert_eq!(m.instances, 2);
    }
}

/// B: the SHARED multiplicity table (2 instances forever). Same n and k grid, plus the reach
/// the exact-public cap forbids.
#[test]
fn shape_b_shared_table_scaling() {
    println!("== SHAPE B: shared multiplicity-carrying table (2 batch instances, always) ==");
    for n in [8usize, 16, 32, 64, 128, 256, 1024, 4096] {
        let m = measure("B", &shape_b_json(1, n), 1, n);
        assert_eq!(
            m.instances, 2,
            "main + one shared table AIR, independent of n"
        );
    }
    for k in [1usize, 2, 4, 8, 16, 32] {
        let n = 16;
        let m = measure("B", &shape_b_json(k, n), k, n);
        assert_eq!(
            m.instances, 2,
            "main + one shared table AIR, independent of k"
        );
    }
    println!("-- the reach the exact-public cap (k*n <= 128 rows) forbids outright --");
    for (k, n) in [(8usize, 1024usize), (32, 1024), (8, 4096)] {
        measure("B", &shape_b_json(k, n), k, n);
    }
}

/// The head-to-head at the ONE grid point both shapes can reach at width: k=8, n=16.
#[test]
fn shape_a_vs_b_head_to_head() {
    println!("== HEAD TO HEAD (identical main trace, identical lane statement) ==");
    for (k, n) in [
        (1usize, 16usize),
        (2, 16),
        (4, 16),
        (8, 16),
        (1, 64),
        (2, 64),
    ] {
        let a = measure("A", &shape_a_json(k, n), k, n);
        let b = measure("B", &shape_b_json(k, n), k, n);
        println!(
            "   -> k={k} n={n}: prove A/B = {:.2}x | wire A/B = {:.2}x | instances {} vs {}",
            a.prove_ms / b.prove_ms,
            a.bytes as f64 / b.bytes as f64,
            a.instances,
            b.instances
        );
    }
}

/// **CPU-TIME MODE (contention-robust).** This box is a shared co-tenant build machine; wall-clock
/// prove timings taken inside one process are dominated by preemption (5x spread run to run at
/// load ~80). So the timing law is read off USER CPU TIME instead, measured by the OS on a process
/// that does exactly one thing: prove ONE grid point `MEGAFAST_REPS` times, single-threaded
/// (`RAYON_NUM_THREADS=1`). The caller runs
///
/// ```text
/// MEGAFAST_ONE=A:4:16 MEGAFAST_REPS=20 RAYON_NUM_THREADS=1 /usr/bin/time -p <bin> one_point
/// ```
///
/// and subtracts the `MEGAFAST_REPS=0` baseline (process start + trace build) from the user time.
/// User CPU time is charged only when this process actually runs, so a busy box inflates WALL
/// time, not this.
#[test]
#[ignore = "MEASUREMENT DRIVER, not a test: with MEGAFAST_ONE unset it returns immediately and \
            reported PASSED, a green that asserted nothing. Ignored so it reports SKIPPED instead. \
            Run it as MEGAFAST_ONE=A:4:16 MEGAFAST_REPS=20 … -- --ignored --exact one_point."]
fn one_point() {
    let Ok(spec) = std::env::var("MEGAFAST_ONE") else {
        return;
    };
    let parts: Vec<&str> = spec.split(':').collect();
    assert!(
        parts.len() == 3 || parts.len() == 4,
        "MEGAFAST_ONE=<A|B>:<k>:<n>[:<m>]"
    );
    let k: usize = parts[1].parse().expect("k");
    let n: usize = parts[2].parse().expect("n");
    let m: usize = parts.get(3).map_or(1, |v| v.parse().expect("m"));
    let json = match parts[0] {
        "A" => shape_a_json_m(k, n, m),
        "B" => shape_b_json_m(k, n, m),
        other => panic!("unknown shape {other}"),
    };
    let desc = parse_vm_descriptor2(&json).expect("descriptor parses");
    let (trace, pis) = trace_and_pis(k, n);
    let mem = MemBoundaryWitness::default();
    let heaps: Vec<Vec<dregg_circuit::heap_root::HeapLeaf>> = vec![];
    // `MEGAFAST_POW` overrides the production 16-bit FRI query proof-of-work. The grind is a
    // FIXED, size-independent cost (expected 2^bits Poseidon2 hashes) whose actual cost is
    // geometric-distributed per (descriptor, witness) — at these trace sizes it is comparable to
    // the whole rest of the prover, so isolating it (POW=0) is what exposes the true scaling law.
    // Non-default configs are measurement-only and never reach the wire.
    let pow: Option<usize> = std::env::var("MEGAFAST_POW")
        .ok()
        .and_then(|v| v.parse().ok());
    let config = pow.map(|bits| {
        dregg_circuit::plonky3_prover::create_config_with_fri(
            dregg_circuit::descriptor_ir2::IR2_FRI_LOG_BLOWUP,
            dregg_circuit::descriptor_ir2::IR2_FRI_LOG_FINAL_POLY_LEN,
            dregg_circuit::descriptor_ir2::IR2_FRI_MAX_LOG_ARITY,
            dregg_circuit::descriptor_ir2::IR2_FRI_NUM_QUERIES,
            bits,
        )
    });
    let mut sink = 0usize;
    for _ in 0..reps() {
        let proof = match &config {
            Some(c) => dregg_circuit::descriptor_ir2::prove_vm_descriptor2_with_config(
                &desc, &trace, &pis, &mem, &heaps, c,
            )
            .expect("proves"),
            None => prove_vm_descriptor2(&desc, &trace, &pis, &mem, &heaps).expect("proves"),
        };
        sink = sink.wrapping_add(proof.degree_bits.len());
    }
    println!("one_point {spec} reps={} pow={pow:?} sink={sink}", reps());
}

// ============================================================================
// COMPOSED-PROVER-BENCH: absolute cost, and the DECLARED-ROW axis
// ============================================================================

/// One grid point's LOAD-INDEPENDENT facts: batch instances, main width, and the EXACT wire
/// size in bytes. These are deterministic functions of `(shape, k, n, m)` — they do not move
/// with box load, so they are reported without any statistical hedging. Every point is also
/// PROVED and VERIFIED here, so a printed size is a size of a proof that actually verifies.
fn size_point(label: &str, json: &str, k: usize, n: usize, m: usize) -> (usize, usize) {
    let desc = parse_vm_descriptor2(json).expect("descriptor parses");
    let (trace, pis) = trace_and_pis(k, n);
    let mem = MemBoundaryWitness::default();
    let heaps: Vec<Vec<dregg_circuit::heap_root::HeapLeaf>> = vec![];
    let proof = prove_vm_descriptor2(&desc, &trace, &pis, &mem, &heaps)
        .unwrap_or_else(|e| panic!("{label} k={k} n={n} m={m} must prove: {e}"));
    verify_vm_descriptor2(&desc, &proof, &pis)
        .unwrap_or_else(|e| panic!("{label} k={k} n={n} m={m} must verify: {e:?}"));
    let bytes = postcard::to_allocvec(&proof).expect("postcard").len();
    let instances = proof.degree_bits.len();
    println!(
        "{label:>2} k={k:<3} n={n:<5} m={m:<2} inst={:<5} main_w={:<4} wire={:>8} B ({:>7.2} KiB)",
        instances,
        desc.trace_width,
        bytes,
        kib(bytes)
    );
    (instances, bytes)
}

/// **THE ABSOLUTE SIZE TABLE.** A k=4 composition (four tiny automata over one word) at the
/// word lengths the goal names, plus the k=1 reference.
///
/// ⚑ **The "INEXPRESSIBLE" column is GONE (2026-07-29).** This test used to report `k=4, n ∈
/// {64, 256, 1024}` as points shape A could not reach at all, because `MAX_EXACT_PUBLIC_ROWS =
/// 128` refused `k·n > 128` manifests — and that refusal WAS the measurement. Those points now
/// prove. They are measured here alongside shape B, which is the honest successor: the two shapes
/// are the same shape.
#[test]
fn absolute_wire_sizes() {
    println!("== ABSOLUTE PROOF SIZE: composed tiny automata, production ir2_config ==");
    println!("-- shape A (deployed exact_public_rows), k=4 composition --");
    for n in [16usize, 32, 64, 256, 1024] {
        let (inst, _) = size_point("A", &shape_a_json(4, n), 4, n, 1);
        assert_eq!(
            inst, 2,
            "k=4 n={n} was INEXPRESSIBLE under the 128-row cap and is now two instances"
        );
    }
    println!("-- shape A, k=1 reference --");
    for n in [16usize, 64, 128] {
        size_point("A", &shape_a_json(1, n), 1, n, 1);
    }
    println!("-- shape B (shared multiplicity table), k=4 composition --");
    for n in [16usize, 64, 256, 1024] {
        let (inst, _) = size_point("B", &shape_b_json(4, n), 4, n, 1);
        assert_eq!(inst, 2);
    }
    println!("-- shape B, k=1 reference --");
    for n in [16usize, 64, 256, 1024] {
        size_point("B", &shape_b_json(1, n), 1, n, 1);
    }
}

/// **THE DECLARED-ROW AXIS, at a FIXED main trace.** `n = 16` rows and `3k` columns are held
/// bit-identical while the DECLARED manifest grows `m`-fold (16 → 128 rows).
///
/// ⚑ **The axis used to be an INSTANCE axis (17 → 129 batch instances) and is now a TABLE-ROW
/// axis (2 instances throughout).** Shape B — the range/byte table, a multiplicity-bearing single
/// instance — was the control precisely because it never grew an instance; shape A now has that
/// same property, so what this reports is the residual wire cost of carrying `m`-fold declared
/// rows as table rows rather than as instances.
#[test]
fn declared_row_axis_sizes() {
    println!("== DECLARED-ROW AXIS at FIXED trace (k=1, n=16; m = lookups per row) ==");
    for m in [1usize, 2, 4, 8] {
        let (ia, ba) = size_point("A", &shape_a_json_m(1, 16, m), 1, 16, m);
        let (ib, bb) = size_point("B", &shape_b_json_m(1, 16, m), 1, 16, m);
        assert_eq!(ia, 2, "the manifest is ONE instance now");
        assert_eq!(ib, 2, "the control never grew an instance either");
        println!(
            "   -> declared={:<4} A/B wire = {:.2}x  (A {} B, delta {} B)",
            16 * m,
            ba as f64 / bb as f64,
            ba,
            bb
        );
    }
}
