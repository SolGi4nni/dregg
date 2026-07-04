//! Criterion bench: FEDERATION cross-node gossip/sync per-turn cost.
//!
//! A turn that crosses a federation boundary rides the blocklace: the committing
//! node wraps the (signed) turn in a `Block` and disseminates it; every peer that
//! receives it pays an Ed25519 verify + a strand-integrity `insert`; finality is
//! reached when a quorum acks. This bench measures those REAL per-block primitives
//! (`dregg-blocklace`), which are the measured legs the N-node federation model
//! (`docs/PERF-KERNEL.md`) multiplies by the gossip topology.
//!
//! The cross-federation BRIDGE (`federation::CrossFedReceiptBundle` / BridgeMint)
//! is NOT benched here — the `federation` crate pulls a heavy ark-* / tokio
//! subtree, and a real multi-node bridge measurement needs the staging fleet. The
//! bridge cost is MODELED in the doc as (one local commit + one receipt-bundle
//! verify), grounded in `embedded_commit` + the per-block verify measured here.
//!
//! Measured legs (per turn = per block):
//!   * sign     — `Block::new_signed`: BLAKE3 block-id + Ed25519 sign (creator).
//!   * verify   — `Block::verify_signature`: Ed25519 verify (EVERY receiving peer).
//!   * id       — `Block::id`: the BLAKE3 content hash.
//!   * wire     — `to_bytes` + `from_bytes`: the postcard wire roundtrip.
//!   * insert   — `Blocklace::insert` into a lace of M blocks: verify + causal
//!                closure + strand bookkeeping (the receiver's full write path).
//!   * finality — `FinalityTracker::record_ack` over a Q-node quorum (per block).
//!
//! Run: `cargo bench -p dregg-perf --bench federation_gossip`
//!      `PERF_FULL=1 cargo bench -p dregg-perf --bench federation_gossip`

use criterion::{BenchmarkId, Criterion, black_box, criterion_group, criterion_main};
use dregg_blocklace::finality::FinalityTracker;
use dregg_blocklace::{Block, BlockId, Blocklace};
use dregg_perf::{perf_full, regime};
use ed25519_dalek::SigningKey;

/// A representative committed-turn payload (~the embedded-commit wire size class).
const PAYLOAD_LEN: usize = 256;

fn payload(seed: u64) -> Vec<u8> {
    let mut v = vec![0u8; PAYLOAD_LEN];
    v[0..8].copy_from_slice(&seed.to_le_bytes());
    v
}

fn key(seed: u8) -> SigningKey {
    SigningKey::from_bytes(&[seed; 32])
}

/// Lace depth ladder M (blocks already present when a new block lands).
fn lace_sizes() -> Vec<usize> {
    if perf_full() {
        vec![100, 1_000, 10_000]
    } else {
        vec![100]
    }
}

/// Quorum ladder Q (acks needed for finality).
fn quorum_sizes() -> Vec<usize> {
    if perf_full() {
        vec![4, 16, 64]
    } else {
        vec![4]
    }
}

/// Build a single-strand lace of `m` signed blocks (each referencing its
/// predecessor) and return the lace + the last block's id (the next block's
/// predecessor). Mirrors the per-strand append a node disseminates.
fn filled_lace(m: usize) -> (Blocklace, SigningKey, u64, Option<BlockId>) {
    let k = key(1);
    let mut lace = Blocklace::new();
    let mut prev: Option<BlockId> = None;
    for seq in 0..m as u64 {
        let preds = prev.into_iter().collect::<Vec<_>>();
        let block = Block::new_signed(&k, seq, preds, payload(seq));
        let id = lace.insert(block).expect("valid strand extension");
        prev = Some(id);
    }
    (lace, k, m as u64, prev)
}

fn bench_gossip(c: &mut Criterion) {
    let r = regime();
    let k = key(1);

    // ----- PER-BLOCK PRIMITIVES (the per-turn gossip unit) -----
    let mut g = c.benchmark_group(format!("federation/per_block/{r}"));
    let preds = vec![[7u8; 32]];
    let sample = Block::new_signed(&k, 5, preds.clone(), payload(5));
    let wire = sample.to_bytes();

    g.bench_function("sign", |b| {
        b.iter(|| black_box(Block::new_signed(&k, 5, preds.clone(), payload(5))));
    });
    g.bench_function("verify", |b| {
        b.iter(|| black_box(sample.verify_signature().is_ok()));
    });
    g.bench_function("id", |b| {
        b.iter(|| black_box(sample.id()));
    });
    g.bench_function("wire_roundtrip", |b| {
        b.iter(|| {
            let bytes = black_box(&sample).to_bytes();
            black_box(Block::from_bytes(black_box(&bytes)))
        });
    });
    g.bench_function("wire_bytes", |b| {
        b.iter(|| black_box(Block::from_bytes(black_box(&wire))));
    });
    g.finish();

    // ----- INSERT into a lace of M (the receiver's full write path) -----
    let mut g = c.benchmark_group(format!("federation/insert/{r}"));
    for &m in &lace_sizes() {
        let (lace, kk, next_seq, prev) = filled_lace(m);
        let next = Block::new_signed(&kk, next_seq, prev.into_iter().collect(), payload(next_seq));
        g.bench_with_input(BenchmarkId::new("insert", m), &m, |b, _| {
            b.iter_batched(
                || (lace.clone(), next.clone()),
                |(mut l, blk)| black_box(l.insert(blk).is_ok()),
                criterion::BatchSize::SmallInput,
            );
        });
    }
    g.finish();

    // ----- FINALITY: record acks over a Q-node quorum (per block) -----
    let mut g = c.benchmark_group(format!("federation/finality/{r}"));
    for &q in &quorum_sizes() {
        let bid: BlockId = sample.id();
        g.bench_with_input(BenchmarkId::new("quorum_acks", q), &q, |b, _| {
            b.iter_batched(
                || FinalityTracker::new(q),
                |mut ft| {
                    let mut level = None;
                    for acker in 0..q as u8 {
                        // The finality tracker keys by its own `finality::BlockId`
                        // newtype over the lace's raw `[u8; 32]` block id.
                        level = Some(
                            ft.record_ack(dregg_blocklace::finality::BlockId(bid), [acker; 32]),
                        );
                    }
                    black_box(level)
                },
                criterion::BatchSize::SmallInput,
            );
        });
    }
    g.finish();
}

criterion_group!(benches, bench_gossip);
criterion_main!(benches);
