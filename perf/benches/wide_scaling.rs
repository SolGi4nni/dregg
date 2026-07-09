//! Criterion bench: WIDE (horizontal) scaling of the ledger + nullifier set.
//!
//! The kernel's per-turn cost has two state-size-dependent legs, and they scale
//! DIFFERENTLY. This bench measures both vs the population N so the
//! horizontal-scaling story is grounded in numbers, not the dated "~130k×" note.
//!
//!   * NULLIFIER SET (`cell::NullifierSet`) — `insert` / `contains` are O(log N)
//!     `BTreeSet` ops, BUT `root()` and `prove_non_membership()` REBUILD the
//!     whole BLAKE3 Merkle tree from a freshly-materialized sorted vec on EVERY
//!     call (O(N) per call, ~2N hashes). This is the WIDE degradation point: the
//!     double-spend membership check is cheap, but committing/proving the
//!     nullifier root is linear in the spent-note population.
//!
//!   * LEDGER (`cell::Ledger`) — the cell-state Merkle commitment is LAZY +
//!     INCREMENTAL. A VALUE touch (`get_mut` / `update_with` → `touch_value`)
//!     costs a batched O(log N) `update_leaf` on the next `root()`; only a
//!     STRUCTURAL change (`insert_cell` → `touch_structural`) forces an O(N)
//!     rebuild. So the hot turn path (mutate existing cells) stays O(log N) as
//!     the ledger widens; cell CREATION is the linear leg.
//!
//! N ladder: SMOKE = [1_000]; FULL (`PERF_FULL=1`) = [1k, 10k, 100k, 1M].
//! The O(N) heavy ops (nullifier `root`/`prove`, ledger structural rebuild) use a
//! small sample size so the 1M point stays seconds-scale.
//!
//! Run: `cargo bench -p dregg-perf --bench wide_scaling`
//!      `PERF_FULL=1 cargo bench -p dregg-perf --bench wide_scaling`

use std::time::Duration;

use criterion::{BenchmarkId, Criterion, black_box, criterion_group, criterion_main};
use dregg_cell::{Cell, Ledger, Nullifier, NullifierSet};
use dregg_perf::{perf_full, regime};

/// The population ladder. SMOKE keeps `cargo bench` fast; FULL walks 1k→1M.
fn sizes() -> Vec<usize> {
    if perf_full() {
        vec![1_000, 10_000, 100_000, 1_000_000]
    } else {
        vec![1_000]
    }
}

/// A distinct nullifier for index `i` (the high bytes carry `i`, so the sorted
/// order and the Merkle leaves are well spread).
fn nullifier(i: u64) -> Nullifier {
    let mut b = [0u8; 32];
    b[0..8].copy_from_slice(&i.to_le_bytes());
    b[8..16].copy_from_slice(&i.wrapping_mul(0x9E37_79B9_7F4A_7C15).to_le_bytes());
    Nullifier(b)
}

/// A nullifier set pre-filled with `n` distinct nullifiers.
fn filled_set(n: usize) -> NullifierSet {
    let mut s = NullifierSet::new();
    for i in 0..n as u64 {
        s.insert(nullifier(i), 1).expect("distinct");
    }
    s
}

/// A cell with a distinct id for index `i`.
fn cell(i: u64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0..8].copy_from_slice(&i.to_le_bytes());
    Cell::with_balance(pk, [0u8; 32], 1_000)
}

/// A ledger pre-filled with `n` distinct cells, with the Merkle tree already
/// MATERIALIZED (so a subsequent value-touch measures the incremental path, not
/// a cold first build).
fn filled_ledger(n: usize) -> (Ledger, Vec<dregg_cell::CellId>) {
    let mut l = Ledger::new();
    let mut ids = Vec::with_capacity(n);
    for i in 0..n as u64 {
        ids.push(l.insert_cell(cell(i)).expect("distinct"));
    }
    let _ = l.root(); // materialize the tree (pay the cold build once, up front)
    (l, ids)
}

fn bench_wide(c: &mut Criterion) {
    let r = regime();

    // ----- NULLIFIER SET: O(log N) membership legs -----
    let mut g = c.benchmark_group(format!("wide/nullifier_logn/{r}"));
    for &n in &sizes() {
        let set = filled_set(n);
        // contains (present) — O(log N) BTreeSet lookup.
        let probe = nullifier((n / 2) as u64);
        g.bench_with_input(BenchmarkId::new("contains", n), &n, |b, _| {
            b.iter(|| black_box(set.contains(black_box(&probe))));
        });
        // insert (1 new nullifier into a set of N) — O(log N) BTreeSet insert.
        g.bench_with_input(BenchmarkId::new("insert", n), &n, |b, _| {
            b.iter_batched(
                || set.clone(),
                |mut s| {
                    let _ = s.insert(nullifier((n + 1) as u64), 1);
                    black_box(s.len())
                },
                criterion::BatchSize::SmallInput,
            );
        });
    }
    g.finish();

    // ----- NULLIFIER SET: O(N) FULL-REBUILD legs (the WIDE degradation) -----
    let mut g = c.benchmark_group(format!("wide/nullifier_on/{r}"));
    g.sample_size(10).measurement_time(Duration::from_secs(6));
    for &n in &sizes() {
        let set = filled_set(n);
        // root() — rebuilds the WHOLE BLAKE3 Merkle tree from a fresh sorted vec.
        g.bench_with_input(BenchmarkId::new("root", n), &n, |b, _| {
            b.iter(|| black_box(set.root()));
        });
        // prove_non_membership() — materialize + binary-search + rebuild path.
        let absent = {
            let mut x = nullifier((n / 2) as u64);
            x.0[31] = 0xFF; // perturb so it falls between two present neighbors
            x
        };
        g.bench_with_input(BenchmarkId::new("prove_non_membership", n), &n, |b, _| {
            b.iter(|| black_box(set.prove_non_membership(black_box(&absent))));
        });
    }
    g.finish();

    // ----- LEDGER: incremental value-touch root() (O(log N) hot path) -----
    let mut g = c.benchmark_group(format!("wide/ledger_value_logn/{r}"));
    for &n in &sizes() {
        let (ledger, ids) = filled_ledger(n);
        let touch = ids[n / 2];
        g.bench_with_input(BenchmarkId::new("touch_root", n), &n, |b, _| {
            b.iter_batched(
                || ledger.clone(),
                |mut l| {
                    // VALUE mutation → Pending::Values → batched O(log N) update.
                    if let Some(cell) = l.get_mut(&touch) {
                        cell.state.set_balance(cell.state.balance() + 1);
                    }
                    black_box(l.root())
                },
                criterion::BatchSize::SmallInput,
            );
        });
    }
    g.finish();

    // ----- LEDGER: structural insert root() (O(N) rebuild leg) -----
    let mut g = c.benchmark_group(format!("wide/ledger_structural_on/{r}"));
    g.sample_size(10).measurement_time(Duration::from_secs(6));
    for &n in &sizes() {
        let (ledger, _ids) = filled_ledger(n);
        g.bench_with_input(BenchmarkId::new("insert_root", n), &n, |b, _| {
            b.iter_batched(
                || ledger.clone(),
                |mut l| {
                    // STRUCTURAL change → Pending::Structural → O(N) full rebuild.
                    let _ = l.insert_cell(cell((n + 1) as u64));
                    black_box(l.root())
                },
                criterion::BatchSize::SmallInput,
            );
        });
    }
    g.finish();
}

criterion_group!(benches, bench_wide);
criterion_main!(benches);
