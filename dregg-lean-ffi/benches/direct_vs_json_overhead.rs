//! direct_vs_json_overhead.rs — re-measure the per-turn FFI cost: JSON path vs the no-copy path.
//!
//! The Stage-0 baseline (`perf/benches/lean_ffi_turn.rs`) attributed ~100–160µs/turn to the double
//! JSON marshalling (Rust encode → Lean parse → Lean encode → Rust parse), tracking ~0.14µs/byte.
//! This bench times, on the SAME extracted wire `(host, state, turn)`:
//!   * JSON path: `marshal_turn_hosted` (encode) → `shadow_exec_full_forest_auth` (the Lean
//!     parse→exec→encode round-trip) → `decode_shadow_state` (parse); and
//!   * no-copy path: `shadow_exec_direct` (build Lean inductives → exec → read back; NO string).
//! Both run the IDENTICAL verified executor, so the DELTA is purely the marshalling tax removed.
//!
//! `harness = false`: a plain timed binary printing a table (like the Stage-0 baseline). GATED on
//! `lean_available()` + `direct_available()`.

use std::time::Instant;

use dregg_lean_ffi::marshal::{
    conformance_input_corpus, marshal_turn_hosted, WForest, WireHostCtx, WireState, WireTurn,
};
use dregg_lean_ffi::{
    decode_shadow_state, direct_available, lean_available, shadow_exec_direct,
    shadow_exec_full_forest_auth, WireTurnHdr,
};

fn split(t: &WireTurn) -> (WireTurnHdr, &WForest) {
    (
        WireTurnHdr {
            agent: t.agent,
            nonce: t.nonce,
            fee: t.fee,
            valid_until: t.valid_until,
            block_height: t.block_height,
            prev_hash: t.prev_hash.0,
        },
        &t.root,
    )
}

fn time_median(iters: u32, mut f: impl FnMut()) -> f64 {
    for _ in 0..5 {
        std::hint::black_box(f());
    }
    let mut s = Vec::with_capacity(iters as usize);
    for _ in 0..iters {
        let t0 = Instant::now();
        std::hint::black_box(f());
        s.push(t0.elapsed().as_secs_f64());
    }
    s.sort_by(|a, b| a.partial_cmp(b).unwrap());
    s[s.len() / 2]
}

fn fmt(s: f64) -> String {
    if s < 1e-6 {
        format!("{:.0} ns", s * 1e9)
    } else {
        format!("{:.2} us", s * 1e6)
    }
}

fn json_once(host: &WireHostCtx, state: &WireState, turn: &WireTurn) {
    let wire = marshal_turn_hosted(host, state, turn).expect("marshal");
    let out = shadow_exec_full_forest_auth(&wire).expect("json ffi");
    let _ = decode_shadow_state(&out).expect("decode");
}

fn direct_once(host: &WireHostCtx, state: &WireState, root: &WForest, hdr: &WireTurnHdr) {
    let _ = shadow_exec_direct(host, state, root, hdr).expect("direct ffi");
}

fn main() {
    if !lean_available() {
        eprintln!("direct_vs_json_overhead: libdregg_lean.a not linked — skipped.");
        return;
    }
    if !direct_available() {
        eprintln!("direct_vs_json_overhead: direct export absent (stale archive) — skipped.");
        return;
    }

    let iters = 2000u32;
    // Representative shapes from the corpus: a committing transfer-shaped turn (state_demo) + the
    // big full-state echo (state_full) + a minimal action. Names match the corpus.
    let corpus = conformance_input_corpus();
    let pick = ["state_demo", "state_full", "action_0", "auth_0"];

    println!("\n========= LEAN↔RUST FFI PER-TURN: JSON vs NO-COPY (re-measure) =========");
    println!("iterations per leg: {iters} (median)\n");
    println!(
        "{:<16} {:>10} {:>12} {:>12} {:>10} {:>9}",
        "shape", "in_bytes", "json-ffi", "direct-ffi", "speedup", "saved"
    );
    println!("{}", "-".repeat(74));
    for name in pick {
        let Some((_, host, state, turn)) = corpus.iter().find(|(n, ..)| n == name) else {
            continue;
        };
        let (hdr, root) = split(turn);
        let in_bytes = marshal_turn_hosted(host, state, turn)
            .map(|w| w.len())
            .unwrap_or(0);
        let j = time_median(iters, || json_once(host, state, turn));
        let d = time_median(iters, || direct_once(host, state, root, &hdr));
        let speedup = if d > 0.0 { j / d } else { 0.0 };
        println!(
            "{:<16} {:>10} {:>12} {:>12} {:>9.1}x {:>9}",
            name,
            in_bytes,
            fmt(j),
            fmt(d),
            speedup,
            fmt(j - d),
        );
    }
    println!("{}", "-".repeat(74));
    println!(
        "json-ffi  = marshal_turn_hosted + shadow_exec_full_forest_auth + decode_shadow_state\n\
         direct-ffi = shadow_exec_direct (build lean_object* -> exec -> read; NO string)\n\
         Both run the SAME verified executor; the delta is the marshalling tax removed."
    );
}
