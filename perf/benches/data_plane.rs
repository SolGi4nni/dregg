//! Criterion bench: DATA-PLANE bus throughput (DP-2 — `captp/src/data_plane.rs`).
//!
//! Times the cap-gated, receipted message bus a deos app (or Hermes, or the harness)
//! uses to MOVE work — the userspace data plane that landed this epoch
//! (`captp::data_plane::Bus`):
//!
//!   * `enqueue`       — `Bus::enqueue`: admit a send through the `SendCap` gate
//!     (live cap, right recipient+channel, offered ≤ grant), enqueue the box on the
//!     relay, advance the monotone inbox root, and SIGN a custody receipt. The
//!     per-message send cost (the gate + the relay + the Ed25519 receipt signature).
//!   * `drain`         — `Bus::drain`: deliver a recipient's queued boxes and append
//!     their content hashes to the authenticated delivered-log (the "handled"
//!     witness). The per-message delivery cost.
//!   * `enqueue_drain` — a full round-trip: enqueue then drain one message (the unit
//!     of data-plane work, send + deliver).
//!   * `publish_fanout`— `Bus::publish`: fan one payload out to S subscribers (each a
//!     real cap-gated, receipted enqueue) — the pub/sub multicast cost.
//!
//! Every op is over the SAME real `Bus` the node's channels service drives. The cost
//! is dominated by BLAKE3 content-addressing + the Ed25519 custody-receipt signature
//! (enqueue) — the price of a CONVICTABLE delivery (a drop is provable, an honest
//! delivery acquitted), not a fire-and-forget queue.
//!
//! SMOKE (default): a single recipient / S=4 subscribers. FULL (`PERF_FULL=1`): S ∈
//! {4, 32, 128} for the fan-out leg.
//!
//! Run: `cargo bench -p dregg-perf --bench data_plane`

use criterion::{BatchSize, Criterion, black_box, criterion_group, criterion_main};
use dregg_captp::data_plane::{Bus, ChannelName, SendCap, TopicName};
use dregg_cell::AuthRequired;
use dregg_perf::regime;
use dregg_types::{FederationId, generate_keypair};

/// A bus with a relay identity whose `FederationId` IS its Ed25519 pubkey (the
/// custody binding — minted receipts verify against it).
fn fresh_bus() -> Bus {
    let (sk, pk) = generate_keypair();
    Bus::new(FederationId(pk.0), sk, 1 << 20, 1 << 20)
}

/// The fan-out subscriber-count ladder.
fn fanout_sizes() -> &'static [usize] {
    if dregg_perf::perf_full() {
        &[4, 32, 128]
    } else {
        &[4]
    }
}

fn bench_data_plane(c: &mut Criterion) {
    let mut group = c.benchmark_group(format!("data_plane/{}", regime()));

    let recipient = FederationId([0xBB; 32]);
    let name = ChannelName::new(b"app/inbox".to_vec());
    let cap = SendCap::grant(recipient, name.clone(), AuthRequired::Signature);
    let payload = vec![0xABu8; 256]; // a representative 256-byte message

    // ---- ENQUEUE: the cap-gated, receipted send ----------------------------
    group.bench_function("enqueue", |b| {
        b.iter_batched(
            fresh_bus,
            |mut bus| {
                let d = bus
                    .enqueue(
                        black_box(&cap),
                        recipient,
                        &name,
                        AuthRequired::Signature,
                        payload.clone(),
                        0,
                    )
                    .expect("authorized send admits");
                black_box(d);
            },
            BatchSize::SmallInput,
        );
    });

    // ---- DRAIN: the witnessed delivery -------------------------------------
    // Setup enqueues one box (untimed); the timed body drains it.
    group.bench_function("drain", |b| {
        b.iter_batched(
            || {
                let mut bus = fresh_bus();
                bus.enqueue(
                    &cap,
                    recipient,
                    &name,
                    AuthRequired::Signature,
                    payload.clone(),
                    0,
                )
                .expect("authorized send admits");
                bus
            },
            |mut bus| {
                let msgs = bus.drain(black_box(&recipient));
                // HARD, not `debug_assert` (`[profile.bench]` has no `debug-assertions`):
                // setup enqueued exactly one box, so a drain of 0 means this leg timed an
                // EMPTY drain. See `symbolic_collapse.rs::run_batch`.
                assert_eq!(msgs.len(), 1, "one enqueued box must be delivered");
                black_box(msgs);
            },
            BatchSize::SmallInput,
        );
    });

    // ---- ENQUEUE+DRAIN: the unit of data-plane work (send + deliver) --------
    group.bench_function("enqueue_drain", |b| {
        b.iter_batched(
            fresh_bus,
            |mut bus| {
                let _ = bus
                    .enqueue(
                        &cap,
                        recipient,
                        &name,
                        AuthRequired::Signature,
                        payload.clone(),
                        0,
                    )
                    .expect("authorized send admits");
                let msgs = bus.drain(&recipient);
                // HARD, not `debug_assert`: one enqueue then one drain. A 0 here means the
                // enqueue+drain "unit of work" moved no message at all.
                assert_eq!(
                    msgs.len(),
                    1,
                    "the enqueue+drain unit must move one message"
                );
                black_box(msgs);
            },
            BatchSize::SmallInput,
        );
    });

    // ---- PUBLISH: pub/sub fan-out to S subscribers -------------------------
    for &s in fanout_sizes() {
        let topic = TopicName::new(b"feed".to_vec());
        let pub_name = ChannelName::new(b"feed/inbox".to_vec());
        let subs: Vec<FederationId> = (0..s).map(|i| FederationId([i as u8; 32])).collect();
        // The publisher's cap over the topic channel; publish re-points it per sub.
        let pub_cap = SendCap::grant(subs[0], pub_name.clone(), AuthRequired::Signature);
        group.bench_function(format!("publish_fanout_{s}"), |b| {
            b.iter_batched(
                || {
                    let mut bus = fresh_bus();
                    for sub in &subs {
                        bus.subscribe(topic.clone(), *sub);
                    }
                    bus
                },
                |mut bus| {
                    let out = bus
                        .publish(
                            &topic,
                            &pub_cap,
                            AuthRequired::Signature,
                            payload.clone(),
                            0,
                        )
                        .expect("publish to a live topic");
                    // HARD, not `debug_assert`: the whole point of `publish_fanout_{s}` is
                    // that it fans out to S subscribers. A short fan-out is a cheaper number
                    // for a smaller job. See `symbolic_collapse.rs::run_batch`.
                    assert_eq!(out.len(), s, "all {s} subscribers must get a delivery");
                    black_box(out);
                },
                BatchSize::SmallInput,
            );
        });
    }

    group.finish();
}

criterion_group!(benches, bench_data_plane);
criterion_main!(benches);
