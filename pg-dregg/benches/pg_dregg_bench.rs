//! pg-dregg throughput / latency benchmarks (criterion).
//!
//! ```text
//! cargo bench
//! ```
//!
//! These measure the load-bearing pg-dregg paths — the ones a deployment's
//! throughput and per-row latency actually ride on — over the postgres-free
//! cores (so the numbers are the *algorithmic* cost, isolated from any pg/IPC
//! overhead, which is the honest thing to quote for "what does the verification
//! itself cost"):
//!
//!   1. `submit_decision/*` — the verified-WRITE gate: the `submit_gate` RLS
//!      admission a pg role passes to enqueue a turn (`authz::decide(token,
//!      "submit", cell, now)`), both COLD (first row, full ed25519 chain verify)
//!      and HOT (the verified-credential LRU is warm — the per-row steady state).
//!   2. `read_projection/*` — the FREE-SQL read gate: the per-row `dregg_admits`
//!      RLS decision a reader pays scanning `dregg.cells`, hot-LRU (the realistic
//!      large-scan cost) — the number that says "how cheap is a cap-gated read?".
//!   3. `chain_gate/*` — the RootChain anti-substitution tooth: `verify_chain_step`
//!      (the pure per-row gate the Tier-C `dregg_verify_turn` trigger runs) and
//!      `RootChain::extend` (the full check_ordinals + chain step a MirrorBatch
//!      apply pays).
//!   4. `mirror_apply/*` — applying a verified turn: `MirrorBatch::from_parts`
//!      (the ordinal-stamp + well-formedness gate) and a whole-batch `extend`.
//!   5. `mirror_serde/*` — the `MirrorBatch` wire codec (postcard-free here: the
//!      serde_json + bincode-shaped round-trip the node↔pg boundary pays per turn)
//!      and `cells_json` (the Tier-C trigger payload the gate consumes).
//!
//! Each is reported as time-per-op AND, where it is a per-row cost, with a
//! throughput element so the bench prints rows/s directly.

use std::hint::black_box;

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};

use dregg_auth::credential::{Caveat, Pred, RootKey};
use pg_dregg::authz;
use pg_dregg::mirror::{verify_chain_step, MirrorBatch, RootChain};
use pg_dregg::synth::{self, ALICE, GENESIS_ROOT};

fn hx(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

/// Install a fixed issuer + return a `submit`-and-`read` token over any resource.
fn fixture_token() -> String {
    let issuer = RootKey::from_seed([7u8; 32]);
    authz::set_issuer_pubkey(issuer.public());
    issuer
        .mint([
            Caveat::FirstParty(Pred::AnyOf(vec![
                Pred::AttrEq { key: "action".into(), value: "submit".into() },
                Pred::AttrEq { key: "action".into(), value: "read".into() },
            ])),
            Caveat::FirstParty(Pred::AttrPrefix { key: "resource".into(), prefix: "".into() }),
            Caveat::FirstParty(Pred::NotAfter { at: 1_000_000 }),
        ])
        .encode()
}

// ===========================================================================
// 1. The verified-WRITE submit gate (the submit_gate RLS admission).
// ===========================================================================
fn bench_submit_decision(c: &mut Criterion) {
    let token = fixture_token();
    let resource = hx(&ALICE);
    let now = 1_000i64;

    let mut g = c.benchmark_group("submit_decision");
    g.throughput(Throughput::Elements(1));

    // COLD: every call pays the full ed25519 signature-chain verify (LRU cleared
    // each iteration). This is the first-row / cache-miss cost.
    g.bench_function("cold_full_chain_verify", |b| {
        b.iter(|| {
            authz::lru_clear();
            black_box(authz::decide(black_box(&token), "submit", black_box(&resource), now).allowed())
        })
    });

    // HOT: the verified-credential LRU is warm — only the revocation check + the
    // Pred re-evaluation run. This is the per-row STEADY STATE (the number that
    // matters at volume).
    authz::lru_clear();
    let _ = authz::decide(&token, "submit", &resource, now); // warm the LRU
    g.bench_function("hot_lru_reeval", |b| {
        b.iter(|| black_box(authz::decide(black_box(&token), "submit", black_box(&resource), now).allowed()))
    });

    g.finish();
}

// ===========================================================================
// 2. The free-SQL read gate (per-row dregg_admits over dregg.cells).
// ===========================================================================
fn bench_read_projection(c: &mut Criterion) {
    let token = fixture_token();
    let now = 1_000i64;
    // A realistic scan: N distinct cell-id resources, hot LRU (one credential,
    // re-evaluated per row) — exactly what an RLS-gated SELECT pays per candidate.
    let resources: Vec<String> = (0u8..255)
        .map(|t| {
            let mut id = [0x11u8; 32];
            id[0] = t;
            hx(&id)
        })
        .collect();
    authz::lru_clear();
    let _ = authz::decide(&token, "read", &resources[0], now); // warm

    let mut g = c.benchmark_group("read_projection");
    for n in [100usize, 1000] {
        g.throughput(Throughput::Elements(n as u64));
        g.bench_with_input(BenchmarkId::new("rls_filter_rows", n), &n, |b, &n| {
            b.iter(|| {
                let mut admitted = 0u64;
                for i in 0..n {
                    let r = &resources[i % resources.len()];
                    if authz::decide(black_box(&token), "read", black_box(r), now).allowed() {
                        admitted += 1;
                    }
                }
                black_box(admitted)
            })
        });
    }
    g.finish();
}

// ===========================================================================
// 3. The RootChain anti-substitution chain-gate.
// ===========================================================================
fn bench_chain_gate(c: &mut Criterion) {
    let story = synth::ledger_story();
    let head = story[2].turn.ledger_root;
    let batch3 = &story[3];

    let mut g = c.benchmark_group("chain_gate");
    g.throughput(Throughput::Elements(1));

    // The pure per-row step gate (what the Tier-C `dregg_verify_turn` trigger runs).
    g.bench_function("verify_chain_step", |b| {
        b.iter(|| {
            black_box(verify_chain_step(
                black_box(Some(head)),
                black_box(3),
                black_box(batch3.turn.prev_root),
                black_box(3),
            ))
            .is_ok()
        })
    });

    // The full RootChain::extend (check_ordinals + the chain step) — what a
    // MirrorBatch apply pays to be admitted.
    g.bench_function("rootchain_extend", |b| {
        b.iter(|| {
            let mut chain = RootChain::resume(head, 3);
            black_box(chain.extend(black_box(batch3))).is_ok()
        })
    });

    g.finish();
}

// ===========================================================================
// 4. Applying a verified turn (assemble + admit a whole batch).
// ===========================================================================
fn bench_mirror_apply(c: &mut Criterion) {
    let story = synth::ledger_story();

    let mut g = c.benchmark_group("mirror_apply");
    g.throughput(Throughput::Elements(1));

    // MirrorBatch::from_parts — the ordinal-stamp + well-formedness gate the node
    // pays per turn it ships.
    let b1 = &story[1];
    g.bench_function("from_parts_assemble", |bch| {
        bch.iter(|| {
            black_box(
                MirrorBatch::from_parts(
                    black_box(b1.turn.clone()),
                    black_box(b1.cells.clone()),
                    black_box(b1.caps.clone()),
                    black_box(b1.memory.clone()),
                )
                .unwrap(),
            )
        })
    });

    // Apply the WHOLE story end-to-end through a fresh chain (the cost to ingest a
    // mirror from genesis — N turns chained).
    g.throughput(Throughput::Elements(story.len() as u64));
    g.bench_function("ingest_story_chain", |bch| {
        bch.iter(|| {
            let mut chain = RootChain::resume(GENESIS_ROOT, 0);
            for b in &story {
                chain.extend(black_box(b)).unwrap();
            }
            black_box(chain.next_ordinal())
        })
    });

    g.finish();
}

// ===========================================================================
// 5. The MirrorBatch wire codec (node ↔ pg) + the Tier-C trigger payload.
// ===========================================================================
fn bench_mirror_serde(c: &mut Criterion) {
    let story = synth::ledger_story();
    let transfer = &story[1]; // the heaviest batch (3 cells + memory)
    let encoded = serde_json::to_vec(transfer).unwrap();

    let mut g = c.benchmark_group("mirror_serde");
    g.throughput(Throughput::Bytes(encoded.len() as u64));

    g.bench_function("encode_batch", |b| {
        b.iter(|| black_box(serde_json::to_vec(black_box(transfer)).unwrap()))
    });

    g.bench_function("decode_batch", |b| {
        b.iter(|| {
            let m: MirrorBatch = serde_json::from_slice(black_box(&encoded)).unwrap();
            black_box(m)
        })
    });

    // The Tier-C trigger payload (`cells_json`) — what the verified-store gate
    // consumes per submitted batch.
    g.throughput(Throughput::Elements(1));
    g.bench_function("cells_json", |b| {
        b.iter(|| black_box(black_box(transfer).cells_json()))
    });

    g.finish();
}

criterion_group!(
    benches,
    bench_submit_decision,
    bench_read_projection,
    bench_chain_gate,
    bench_mirror_apply,
    bench_mirror_serde,
);
criterion_main!(benches);
