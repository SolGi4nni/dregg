//! Criterion bench: EMBEDDED-EXECUTOR commit_turn THROUGHPUT (the node / seL4-PD hot path).
//!
//! Times the VERIFIED Lean kernel commit the node and the seL4 `executor` PD drive on the
//! live commit path: `dregg_lean_ffi::shadow_exec_full_forest_auth` — the `@[export]
//! dregg_exec_full_forest_auth` proved in `metatheory/` (admission ∘ the gated forest). A
//! wire-encoded `(state, turn)` goes in; a committed/rejected verdict + post-state wire comes
//! out. This is the truest "embedded executor commit_turn" measure: the SAME verified entry
//! the firmament boots (HORIZONLOG: the 5-PD assembly boots this turn `status:2 ok:1`) and the
//! node's `World::commit_turn` routes through the embedded `DreggEngine`.
//!
//! The canonical turn is an unchecked 30-unit transfer cell-0 (100) → cell-1 (5), empty
//! side-tables — exactly the firmament boot turn's shape. Two legs are timed:
//!   * `commit` — run the verified kernel and get the raw output wire (the on-device cost).
//!   * `commit_decode` — run it AND decode the verdict (`decode_shadow_verdict`), the full
//!     node admit step (the node decides ACCEPT only on `body_committed`).
//!
//! GATED on `lean_available()`: if `libdregg_lean.a` was not linked (the wasm / `no-lean-link`
//! build), the bench prints a skip line and registers nothing — it never lies with a stub.
//! The input is fixed-size (microseconds-to-low-ms scale through the embedded runtime), so
//! SMOKE == FULL.
//!
//! Run: `cargo bench -p dregg-perf --bench embedded_commit`

use criterion::{Criterion, black_box, criterion_group, criterion_main};
use dregg_lean_ffi::{decode_shadow_verdict, lean_available, shadow_exec_full_forest_auth};
use dregg_perf::{embedded_commit_wire, regime};

fn bench_embedded_commit(c: &mut Criterion) {
    if !lean_available() {
        eprintln!(
            "embedded_commit: libdregg_lean.a not linked (no-lean-link / wasm build) — skipped. \
             Build with the default Lean link to measure the embedded commit path."
        );
        return;
    }

    let wire = embedded_commit_wire();

    // Sanity: the canonical transfer must COMMIT (body-committed) before timing, so the
    // numbers are over the happy commit path, not a rejection.
    let out = shadow_exec_full_forest_auth(&wire)
        .expect("embedded kernel must run the canonical transfer");
    let verdict = decode_shadow_verdict(&out).expect("verdict decodes");
    assert!(
        verdict.body_committed(),
        "canonical embedded transfer must body-commit (got {verdict:?})"
    );

    let mut group = c.benchmark_group(format!("embedded_commit/{}", regime()));

    // (a) the on-device commit: run the verified kernel, get the output wire.
    group.bench_function("forest_auth_transfer", |b| {
        b.iter(|| {
            let out =
                shadow_exec_full_forest_auth(black_box(&wire)).expect("embedded kernel runs");
            black_box(out);
        });
    });

    // (b) the full node admit step: run + decode the verdict (the ACCEPT decision).
    group.bench_function("forest_auth_transfer_decode", |b| {
        b.iter(|| {
            let out =
                shadow_exec_full_forest_auth(black_box(&wire)).expect("embedded kernel runs");
            let v = decode_shadow_verdict(&out).expect("verdict decodes");
            debug_assert!(v.body_committed());
            black_box(v);
        });
    });

    group.finish();
}

criterion_group!(benches, bench_embedded_commit);
criterion_main!(benches);
