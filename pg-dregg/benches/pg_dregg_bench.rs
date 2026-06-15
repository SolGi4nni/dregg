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
//!   6. `workflow/*` — the END-TO-END DBOS-shaped path: a full durable-workflow run
//!      (every step checkpointed) + the crash→recover→resume cycle.
//!   7. `gate_vs_handrolled/*` — THE MARKETABLE COMPARISON: the per-row cost of the
//!      dregg `dregg_admits` decision (`authz::decide`, the real RLS gate, hot LRU)
//!      vs a HAND-ROLLED policy — the owner/expiry/revoked predicate a developer
//!      writes by hand (`USING (owner = current_user AND expires > now() AND NOT
//!      revoked)`), modeled as the equivalent Rust so both are measured on the SAME
//!      axis. NOT apples-to-apples on GUARANTEES (the hand-rolled ACL is a
//!      string-compare a bug bypasses; the dregg gate is an unforgeable, attenuable,
//!      instantly-revocable capability decision) — it answers "what does the per-row
//!      decision cost, dregg vs naive?" so the overhead of verified authz is legible.
//!   8. `drain_spine/*` — the WRITE PATH as the node drains it: N intents through the
//!      real [`Drainer`] / [`FoldProducer`] four-gate spine (SUBMIT re-check → PRODUCE
//!      → CHAIN → advance), the per-turn cost of the verified-write outbox drain.
//!
//! Each is reported as time-per-op AND, where it is a per-row cost, with a
//! throughput element so the bench prints rows/s directly.

use std::collections::HashSet;
use std::hint::black_box;

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};

use dregg_auth::credential::{Caveat, Pred, RootKey};
use pg_dregg::authz;
use pg_dregg::drainer::{Drainer, FoldProducer, SubmitIntent};
use pg_dregg::mirror::{verify_chain_step, MirrorBatch, RootChain};
use pg_dregg::synth::{self, ALICE, GENESIS_ROOT};
use pg_dregg::workflow::{
    recover_from_durable, FoldProjector, MapTokens, MemLog, Step, Workflow, WorkflowEngine,
};

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
                Pred::AttrEq {
                    key: "action".into(),
                    value: "submit".into(),
                },
                Pred::AttrEq {
                    key: "action".into(),
                    value: "read".into(),
                },
            ])),
            Caveat::FirstParty(Pred::AttrPrefix {
                key: "resource".into(),
                prefix: "".into(),
            }),
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
            black_box(
                authz::decide(black_box(&token), "submit", black_box(&resource), now).allowed(),
            )
        })
    });

    // HOT: the verified-credential LRU is warm — only the revocation check + the
    // Pred re-evaluation run. This is the per-row STEADY STATE (the number that
    // matters at volume).
    authz::lru_clear();
    let _ = authz::decide(&token, "submit", &resource, now); // warm the LRU
    g.bench_function("hot_lru_reeval", |b| {
        b.iter(|| {
            black_box(
                authz::decide(black_box(&token), "submit", black_box(&resource), now).allowed(),
            )
        })
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

// ===========================================================================
// 6. THE DBOS-SHAPED WORKLOAD — a full durable workflow run + crash recovery.
//
// Groups 1-5 isolate the individual gates; this group measures the END-TO-END
// path a DBOS user actually rides: a multi-step durable workflow driven through
// the whole verified-write spine (the API `examples/supply_chain` is built on),
// AND the crash → recover → resume cycle that is DBOS's headline feature. The
// per-turn cost here is the realistic "what does one verified durable-workflow
// step cost" — the number to put next to DBOS's per-step checkpoint.
// ===========================================================================

/// A fixed issuer + a token store binding the workload agents to broad-but-real
/// `submit` capabilities (each turn still runs the full submit-gate decision).
fn workflow_tokens(agents: &[[u8; 32]]) -> MapTokens {
    let issuer = RootKey::from_seed([7u8; 32]);
    authz::set_issuer_pubkey(issuer.public());
    authz::lru_clear();
    authz::revoked_clear();
    let mut t = MapTokens::new();
    for &a in agents {
        let tok = issuer
            .mint([
                Caveat::FirstParty(Pred::AttrEq {
                    key: "action".into(),
                    value: "submit".into(),
                }),
                Caveat::FirstParty(Pred::AttrPrefix {
                    key: "resource".into(),
                    prefix: "".into(),
                }),
                Caveat::FirstParty(Pred::NotAfter { at: 1_000_000 }),
            ])
            .encode();
        t.bind(a, tok);
    }
    t
}

const fn wf_agent(tag: u8) -> [u8; 32] {
    let mut id = [0x11u8; 32];
    id[0] = tag;
    id
}

/// An `n`-step conserving workflow: a genesis mint, then a ring of transfers that
/// keeps Σ balances constant — the same shape `loadgen` drives, expressed as the
/// reusable `Workflow` API so the bench measures the real durable runtime.
fn ring_workflow(n: usize, agents: &[[u8; 32]]) -> Workflow {
    let float = 1_000_000i64;
    let mut wf = Workflow::new("dbos-shaped ring");
    wf.push(Step::new("genesis", agents[0]).set(agents[0], float, 0));
    // Each later step moves one unit around the ring (1 debit + 1 credit, Σδ = 0).
    let mut holder = 0usize;
    let mut bal: Vec<i64> = vec![0; agents.len()];
    bal[0] = float;
    let mut nonce: Vec<u64> = vec![1; agents.len()];
    for _ in 1..n {
        let to = (holder + 1) % agents.len();
        bal[holder] -= 1;
        bal[to] += 1;
        wf.push(
            Step::new("xfer", agents[holder])
                .set(agents[holder], bal[holder], nonce[holder])
                .set(agents[to], bal[to], nonce[to]),
        );
        nonce[holder] += 1;
        nonce[to] += 1;
        holder = to;
    }
    wf
}

fn bench_workflow(c: &mut Criterion) {
    let agents: Vec<[u8; 32]> = (0..4).map(|k| wf_agent(0x30 + k as u8)).collect();

    let mut g = c.benchmark_group("workflow");

    // (a) Run an N-step durable workflow end-to-end through the spine, CHECKPOINTING
    //     every committed turn to an external durable log (the DBOS-equivalent
    //     "each step persisted"). Throughput is in turns so the bench prints the
    //     per-step verified-durable-workflow rate directly.
    for n in [16usize, 128] {
        g.throughput(Throughput::Elements(n as u64));
        g.bench_with_input(BenchmarkId::new("run_durable_steps", n), &n, |b, &n| {
            let wf = ring_workflow(n, &agents);
            b.iter(|| {
                let mut engine = WorkflowEngine::new(workflow_tokens(&agents)).with_clock(1_000);
                let mut durable = MemLog::new();
                let out = engine.run_durable(black_box(&wf), &mut durable).unwrap();
                black_box(out.committed)
            })
        });
    }

    // (b) The DBOS headline: crash → recover → resume. Pre-build a durable log of a
    //     committed prefix, then time recover_from_durable (re-validate every
    //     persisted turn) + resume the uncommitted tail — exactly-once. This is the
    //     cost of surviving a crash, which is the thing DBOS sells.
    {
        let n = 64usize;
        let wf = ring_workflow(n, &agents);
        // Commit the whole workflow once to capture a realistic durable log; the
        // bench resumes from a PREFIX of it (half committed, half to replay).
        let half = n / 2;
        let prefix = Workflow {
            name: wf.name.clone(),
            steps: wf.steps[..half].to_vec(),
        };
        let mut seed_engine = WorkflowEngine::new(workflow_tokens(&agents)).with_clock(1_000);
        let mut seed_log = MemLog::new();
        seed_engine.run_durable(&prefix, &mut seed_log).unwrap();

        g.throughput(Throughput::Elements(n as u64));
        g.bench_function("crash_recover_resume", |b| {
            b.iter(|| {
                // Recover from the durable prefix (re-validates the chain on the way
                // up) and resume the tail — the full exactly-once crash-recovery path.
                let mut engine = recover_from_durable(
                    workflow_tokens(&agents),
                    FoldProjector,
                    black_box(&seed_log),
                )
                .expect("the durable log re-validates")
                .with_clock(1_000);
                let mut durable = seed_log.clone();
                let out = engine.resume_durable(black_box(&wf), &mut durable).unwrap();
                black_box((out.skipped, out.committed))
            })
        });
    }

    g.finish();
}

// ===========================================================================
// 7. THE MARKETABLE COMPARISON — dregg_admits vs a hand-rolled SQL policy.
//
// The single most-asked question when pitching "dregg capabilities as RLS": what
// does the verified gate COST versus the owner/expiry/revoked predicate I'd write
// by hand? This group answers it on the per-row decision axis.
//
// The hand-rolled baseline is the Rust equivalent of the policy a developer
// writes without dregg:
//     USING (owner_of(resource) = current_user      -- an ACL membership check
//            AND expires_at > now()                   -- an expiry compare
//            AND id NOT IN (SELECT id FROM revoked))  -- a revocation lookup
// i.e. a string/extract + a HashSet membership + an integer compare + a HashSet
// revocation lookup. That is a fair model of the *work* a hand-rolled SQL RLS
// predicate does per candidate row (the planner inlines it; the cost is these
// comparisons, not IPC).
//
// The dregg side is `authz::decide(token, "read", resource, now)` with a WARM LRU
// — the realistic large-scan steady state (the ed25519 chain verify is paid ONCE
// per token, then each row re-evaluates the first-party caveats off the cached,
// decoded credential).
//
// HONEST FRAMING (stated in the bench output too): this is NOT apples-to-apples on
// GUARANTEES. The hand-rolled ACL is a plaintext comparison a bug / stale cache /
// SQL-injection can bypass, with no attenuation and no cryptographic
// unforgeability; the dregg gate is an unforgeable, attenuable, instantly-revocable
// capability decision. The comparison isolates the per-row DECISION COST so the
// overhead of *verified* authz over a *naive* ACL is legible — that overhead is
// what buys the no-amplification + instant-revocation + unforgeability properties
// the rest of this crate's tests prove.
// ===========================================================================

/// The hand-rolled baseline policy: the owner/expiry/revoked predicate a developer
/// writes by hand, as the equivalent Rust. `owner_acl` is the allow-set the naive
/// `owner = current_user` check consults; `revoked` is the `NOT IN (revoked)` set.
/// Returns whether the row is admitted — exactly the bool a hand-coded RLS `USING`
/// clause returns, doing the same comparisons.
#[inline]
fn handrolled_policy(
    resource: &str,
    now: i64,
    not_after: i64,
    owner_acl: &HashSet<String>,
    revoked: &HashSet<String>,
) -> bool {
    // owner_of(resource): the naive policy derives the row's owner from the
    // resource id (here its 2-char prefix, the same shape dregg attenuates on).
    let owner = &resource[..resource.len().min(2)];
    // owner = current_user (ACL membership) AND expires > now() AND NOT revoked.
    owner_acl.contains(owner) && now < not_after && !revoked.contains(resource)
}

fn bench_gate_vs_handrolled(c: &mut Criterion) {
    let token = fixture_token();
    let now = 1_000i64;
    // The SAME 255 distinct cell-id resources `read_projection` scans, so the two
    // groups are directly comparable.
    let resources: Vec<String> = (0u8..255)
        .map(|t| {
            let mut id = [0x11u8; 32];
            id[0] = t;
            hx(&id)
        })
        .collect();

    // Warm the dregg LRU (the steady-state the per-row scan rides).
    authz::set_issuer_pubkey(RootKey::from_seed([7u8; 32]).public());
    authz::lru_clear();
    authz::revoked_clear();
    let _ = authz::decide(&token, "read", &resources[0], now);

    // The hand-rolled policy's state: the owner allow-set admits every prefix the
    // resources use (so the two policies admit the SAME rows — a fair cost
    // comparison, not one short-circuiting on a denial), an expiry, an empty
    // revocation set.
    let owner_acl: HashSet<String> = (0u8..255)
        .map(|t| {
            let mut id = [0x11u8; 32];
            id[0] = t;
            hx(&id)[..2].to_string()
        })
        .collect();
    let revoked: HashSet<String> = HashSet::new();
    let not_after = 1_000_000i64;

    let mut g = c.benchmark_group("gate_vs_handrolled");
    for n in [100usize, 1000] {
        g.throughput(Throughput::Elements(n as u64));

        // (a) the dregg gate — the real verified capability decision, hot LRU.
        g.bench_with_input(BenchmarkId::new("dregg_admits", n), &n, |b, &n| {
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

        // (b) the hand-rolled baseline — the owner/expiry/revoked ACL predicate.
        g.bench_with_input(BenchmarkId::new("handrolled_acl", n), &n, |b, &n| {
            b.iter(|| {
                let mut admitted = 0u64;
                for i in 0..n {
                    let r = &resources[i % resources.len()];
                    if handrolled_policy(
                        black_box(r),
                        now,
                        not_after,
                        black_box(&owner_acl),
                        black_box(&revoked),
                    ) {
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
// 8. THE WRITE PATH as the node drains it — the four-gate spine over N intents.
//
// `workflow/*` measures the engine-driven durable run; this measures the OTHER
// realizable write surface: the node-side DRAINER pulling intents off the submit
// outbox and running each through SUBMIT (re-check the capability) → PRODUCE (the
// executor seam, the deterministic `FoldProducer` stand-in here) → CHAIN (the
// anti-substitution tooth) → advance. The per-turn cost here is "what does one
// drained verified-write turn cost" — the number next to the workflow per-step
// figure, for the queue-drain deployment shape.
// ===========================================================================
fn bench_drain_spine(c: &mut Criterion) {
    // One issuer + a single broad submit token the drained agents present (each
    // drain still runs the full SUBMIT-gate decision against it).
    let issuer = RootKey::from_seed([7u8; 32]);
    authz::set_issuer_pubkey(issuer.public());
    let submit_token = issuer
        .mint([
            Caveat::FirstParty(Pred::AttrEq {
                key: "action".into(),
                value: "submit".into(),
            }),
            Caveat::FirstParty(Pred::AttrPrefix {
                key: "resource".into(),
                prefix: "".into(),
            }),
            Caveat::FirstParty(Pred::NotAfter { at: 1_000_000 }),
        ])
        .encode();

    // The float source the stand-in producer debits, and a ring of drained agents.
    let source = [0xc0u8; 32];
    let agents: Vec<[u8; 32]> = (0u8..8)
        .map(|k| {
            let mut id = [0x11u8; 32];
            id[0] = 0x40 + k;
            id
        })
        .collect();

    // Pre-build the intents (the bench times the DRAIN, not the intent assembly).
    // A non-empty `signed_turn` so the stand-in produces (it refuses an empty one),
    // the agent its capability is scoped to, the submit token it presents.
    let make_intents = |n: usize| -> Vec<SubmitIntent> {
        (0..n)
            .map(|i| SubmitIntent {
                id: {
                    let mut id = [0u8; 16];
                    id[..8].copy_from_slice(&(i as u64).to_le_bytes());
                    id
                },
                agent: agents[i % agents.len()],
                signed_turn: vec![1u8, 2, 3], // non-empty envelope (stand-in produces)
                token: submit_token.clone(),
            })
            .collect()
    };

    let mut g = c.benchmark_group("drain_spine");
    for n in [16usize, 128] {
        g.throughput(Throughput::Elements(n as u64));
        g.bench_with_input(BenchmarkId::new("drain_intents", n), &n, |b, &n| {
            let intents = make_intents(n);
            b.iter(|| {
                authz::lru_clear();
                authz::revoked_clear();
                // A fresh drainer with the deterministic stand-in producer, funded
                // float, unit 1 — the SAME shape `dregg_drain_once` resumes.
                let mut drainer =
                    Drainer::new(FoldProducer::new(source, 1_000_000_000, 1)).with_clock(1_000);
                let mut executed = 0u64;
                for intent in &intents {
                    if drainer.drain(black_box(intent)).is_executed() {
                        executed += 1;
                    }
                }
                black_box(executed)
            })
        });
    }
    g.finish();
}

criterion_group!(
    benches,
    bench_submit_decision,
    bench_read_projection,
    bench_chain_gate,
    bench_mirror_apply,
    bench_mirror_serde,
    bench_workflow,
    bench_gate_vs_handrolled,
    bench_drain_spine,
);
criterion_main!(benches);
