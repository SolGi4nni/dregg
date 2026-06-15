//! pg-dregg DRAINER DAEMON — the submit-queue drainer as a real background worker.
//!
//! ```text
//! cargo run --release --bin drainerd                  # demo: drive a synthetic queue to drain
//! cargo run --release --bin drainerd -- --rate 200    # 200 synthetic intents/sec offered
//! cargo run --release --bin drainerd -- --poll-ms 50 --batch 64
//! cargo run --release --bin drainerd -- --secs 5      # bounded run (else runs until SIGINT/SIGTERM)
//! ```
//!
//! This is the M3 follow-up to the write outbox (`docs/PG-DREGG.md` §11.4): the
//! enqueue half (`dregg_submit_turn` → `dregg.submit_queue`) is shipped; this is
//! the long-running node-side worker that DRAINS the queue through the verified
//! executor and mirrors the result back. It runs a real poll loop with graceful
//! shutdown (SIGINT/SIGTERM), periodic observability, and idle backoff —
//! everything a production daemon needs — over the [`pg_dregg::drainer`] core.
//!
//! # What the loop does each poll (the four gates)
//!
//! 1. SUBMIT — re-check the acting agent's capability admits `submit`
//!    (`authz::decide`); a revoked-since-enqueue token is refused HERE.
//! 2. PRODUCE — run the intent through the verified executor (the [`Producer`]
//!    seam). The live daemon plugs in the Lean executor (Tier-D / sidecar,
//!    `docs/PG-DREGG-TIER-D-SPIKE.md`); THIS demo binary uses the deterministic
//!    conserving stand-in so the loop is self-contained.
//! 3. CHAIN — admit the produced batch onto the durable head via the real
//!    `RootChain` anti-substitution tooth (a stale/forked drain conflicts).
//! 4. MIRROR — materialize the verified post-image + resolve the queue row
//!    (`executed` | `refused`), one logical commit.
//!
//! # Demo vs live
//!
//! The DEMO (this binary, postgres-free, the always-runnable proof) drives the
//! SAME [`Drainer`] core over an in-memory queue that offers synthetic signed
//! turns at `--rate`, so you watch the worker poll → drain → mirror → resolve and
//! report `drained/refused/conflict/lag` live, with conservation asserted at the
//! end. The LIVE deployment runs the identical loop over `dregg.submit_queue` /
//! `dregg.turns` via the `dregg_drain_once()` / `dregg_drain_stats()` externs
//! (`src/lib.rs`); the queue seams ([`QueueSource`] / [`OutcomeSink`]) are the one
//! thing that differs (in-memory here, SQL there).

use std::sync::atomic::{AtomicBool, Ordering};
use std::time::{Duration, Instant};

use dregg_auth::credential::{Caveat, Pred, RootKey};
use pg_dregg::authz;
use pg_dregg::drainer::{
    DrainOutcome, Drainer, FoldProducer, OutcomeSink, PollReport, QueueSource, SubmitIntent,
};
use pg_dregg::mirror::MirrorBatch;

const SOURCE: [u8; 32] = [0xc0u8; 32];
const CLOCK: i64 = 1_000;

fn agent_id(tag: u8) -> [u8; 32] {
    let mut id = [0x11u8; 32];
    id[0] = tag;
    id
}

// ---------------------------------------------------------------------------
// The DEMO queue: an in-memory `dregg.submit_queue` stand-in that OFFERS
// synthetic signed turns at a configured rate and RECORDS resolved outcomes.
// The live worker swaps this for SQL reads/writes; the Drainer core is identical.
// ---------------------------------------------------------------------------

struct DemoQueue {
    token: String,
    /// Pending intents not yet drained.
    pending: std::collections::VecDeque<SubmitIntent>,
    /// How many synthetic intents to OFFER per second (the inbound load).
    rate_per_sec: u64,
    /// Fractional accrual carried between polls (so low rates still produce).
    accrued: f64,
    /// Monotonic id for synthetic rows.
    next_id: u64,
    last_offer: Instant,
    /// One in `refuse_every` offered intents is deliberately malformed (empty
    /// envelope), so the `refused` counter is exercised on a live run.
    refuse_every: u64,
    /// Resolved outcomes (the audit the demo prints; the live sink is the UPDATE).
    resolved_executed: u64,
    resolved_refused: u64,
    /// The last mirrored batch (the demo "materialization").
    mirrored: u64,
}

impl DemoQueue {
    fn new(rate_per_sec: u64, refuse_every: u64) -> Self {
        let issuer = RootKey::from_seed([7u8; 32]);
        authz::set_issuer_pubkey(issuer.public());
        authz::lru_clear();
        authz::revoked_clear();
        // One broad-but-real `submit` token (the load token; the gate still runs
        // the full verify per cold turn).
        let token = issuer
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
        DemoQueue {
            token,
            pending: std::collections::VecDeque::new(),
            rate_per_sec,
            accrued: 0.0,
            next_id: 0,
            last_offer: Instant::now(),
            refuse_every: refuse_every.max(1),
            resolved_executed: 0,
            resolved_refused: 0,
            mirrored: 0,
        }
    }

    /// Accrue and enqueue synthetic intents based on the configured rate and the
    /// elapsed wall-time since the last call — the inbound submit load.
    fn offer(&mut self) {
        let now = Instant::now();
        let dt = now.duration_since(self.last_offer).as_secs_f64();
        self.last_offer = now;
        self.accrued += dt * self.rate_per_sec as f64;
        let to_make = self.accrued.floor() as u64;
        self.accrued -= to_make as f64;
        for _ in 0..to_make {
            let id = self.next_id;
            self.next_id += 1;
            let agent = agent_id(0x20 + (id % 4) as u8);
            let mut id_bytes = [0u8; 16];
            id_bytes[..8].copy_from_slice(&id.to_le_bytes());
            // Deliberately malform one in `refuse_every` so `refused` is live.
            let signed_turn = if id % self.refuse_every == self.refuse_every - 1 {
                vec![] // empty = malformed envelope → PRODUCE refusal
            } else {
                vec![0xab, 0xcd, (id & 0xff) as u8]
            };
            self.pending.push_back(SubmitIntent {
                id: id_bytes,
                agent,
                signed_turn,
                token: self.token.clone(),
            });
        }
    }
}

impl QueueSource for DemoQueue {
    fn durable_head(&self) -> Result<Option<([u8; 32], u64)>, String> {
        Ok(None) // a fresh demo store starts at genesis
    }
    fn pending(&mut self, limit: usize) -> Result<Vec<SubmitIntent>, String> {
        Ok((0..limit)
            .filter_map(|_| self.pending.pop_front())
            .collect())
    }
    fn pending_depth(&self) -> Result<u64, String> {
        Ok(self.pending.len() as u64)
    }
}

impl OutcomeSink for DemoQueue {
    fn resolve(
        &mut self,
        _intent: &SubmitIntent,
        outcome: &DrainOutcome,
        batch: Option<&MirrorBatch>,
    ) -> Result<(), String> {
        if let Some(_b) = batch {
            self.mirrored += 1; // the live sink MERGEs the post-image into dregg.cells
        }
        match outcome {
            DrainOutcome::Executed { .. } => self.resolved_executed += 1,
            DrainOutcome::Refused { .. } => self.resolved_refused += 1,
        }
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Graceful shutdown — SIGINT/SIGTERM set a stop flag the loop checks.
// ---------------------------------------------------------------------------

static STOP: AtomicBool = AtomicBool::new(false);

extern "C" fn on_signal(_sig: i32) {
    STOP.store(true, Ordering::SeqCst);
}

fn install_signal_handlers() {
    // SAFETY: `signal` with a trivial handler that only sets an atomic flag is
    // async-signal-safe. We install it for SIGINT (Ctrl-C) and SIGTERM (the
    // service stop), so the daemon finishes its current poll and exits cleanly.
    let handler = on_signal as *const () as libc::sighandler_t;
    unsafe {
        libc::signal(libc::SIGINT, handler);
        libc::signal(libc::SIGTERM, handler);
    }
}

// ---------------------------------------------------------------------------

struct Args {
    poll_ms: u64,
    batch: usize,
    rate: u64,
    secs: Option<u64>,
    refuse_every: u64,
}

fn parse_args() -> Args {
    let mut a = Args {
        poll_ms: 100,
        batch: 32,
        rate: 50,
        secs: None,
        refuse_every: 16,
    };
    let argv: Vec<String> = std::env::args().skip(1).collect();
    let mut i = 0;
    while i < argv.len() {
        let val = argv.get(i + 1).map(|s| s.as_str());
        match argv[i].as_str() {
            "--poll-ms" => {
                a.poll_ms = val.and_then(|s| s.parse().ok()).unwrap_or(100);
                i += 2;
            }
            "--batch" => {
                a.batch = val.and_then(|s| s.parse().ok()).unwrap_or(32usize).max(1);
                i += 2;
            }
            "--rate" => {
                a.rate = val.and_then(|s| s.parse().ok()).unwrap_or(50);
                i += 2;
            }
            "--secs" => {
                a.secs = val.and_then(|s| s.parse().ok());
                i += 2;
            }
            "--refuse-every" => {
                a.refuse_every = val.and_then(|s| s.parse().ok()).unwrap_or(16u64).max(1);
                i += 2;
            }
            other => {
                eprintln!(
                    "unknown arg: {other} (use --poll-ms --batch --rate --secs --refuse-every)"
                );
                i += 1;
            }
        }
    }
    a
}

fn main() {
    let args = parse_args();
    install_signal_handlers();

    println!("pg-dregg drainerd — the submit-queue drainer as a background worker");
    println!(
        "  poll: {}ms   batch: {}   offered load: {}/s   refuse 1-in-{}   {}",
        args.poll_ms,
        args.batch,
        args.rate,
        args.refuse_every,
        match args.secs {
            Some(s) => format!("run {s}s"),
            None => "run until SIGINT/SIGTERM".to_string(),
        }
    );
    println!("  gates per intent: SUBMIT(authz) → PRODUCE(executor seam) → CHAIN(RootChain) → MIRROR+resolve\n");

    let mut queue = DemoQueue::new(args.rate, args.refuse_every);
    // The verified-executor seam: a real node plugs in the Lean executor here
    // (the Tier-D / sidecar producer); this demo uses the conserving stand-in.
    let mut drainer = Drainer::new(FoldProducer::new(SOURCE, 1_000_000_000, 1)).with_clock(CLOCK);
    drainer
        .resume_from(&queue)
        .expect("resume from the durable head");

    let started = Instant::now();
    let deadline = args.secs.map(|s| started + Duration::from_secs(s));
    let mut last_report = Instant::now();
    let report_every = Duration::from_secs(1);

    loop {
        if STOP.load(Ordering::SeqCst) {
            println!("\n[drainerd] shutdown signal — finishing current poll and exiting");
            break;
        }
        if let Some(d) = deadline {
            if Instant::now() >= d {
                break;
            }
        }

        // Inbound load: offer synthetic intents accrued since the last poll.
        queue.offer();

        // ONE poll cycle through the four gates. We split the queue's source and
        // sink roles by draining into a staging vec first (the source read), then
        // resolving (the sink write) — mirroring the live worker's distinct SQL.
        let report = poll_cycle(&mut drainer, &mut queue, args.batch);

        // Periodic observability — the counters an operator dashboard reads.
        if last_report.elapsed() >= report_every {
            let c = drainer.counters();
            println!(
                "[drainerd] {} | this-poll: processed={} exec={} refused={}",
                c.summary(),
                report.processed,
                report.executed,
                report.refused
            );
            last_report = Instant::now();
        }

        // Idle backoff: if nothing was pending, sleep the poll interval; if we
        // drained a full batch there may be more, so spin immediately.
        if !report.did_work() {
            std::thread::sleep(Duration::from_millis(args.poll_ms));
        } else if report.processed < args.batch {
            std::thread::sleep(Duration::from_millis(args.poll_ms / 4 + 1));
        }
    }

    // ---- final report --------------------------------------------------------
    let elapsed = started.elapsed();
    let c = drainer.counters();
    println!("\n── drainerd stopped ────────────────────────────────────────");
    println!("  uptime:            {:.2}s", elapsed.as_secs_f64());
    println!("  verified turns:    {} drained", c.drained);
    println!(
        "  refused:           {} (unauth={} produce={} conflict={})",
        c.refused, c.unauthorized, c.produce_refused, c.conflict
    );
    println!("  mirrored batches:  {}", queue.mirrored);
    println!(
        "  resolved rows:     executed={} refused={}",
        queue.resolved_executed, queue.resolved_refused
    );
    println!(
        "  final chain head:  ordinal {} ({})",
        drainer.next_ordinal(),
        drainer.head().map(hx).unwrap_or_else(|| "<genesis>".into())
    );
    let rate = c.drained as f64 / elapsed.as_secs_f64().max(1e-9);
    println!("  sustained drain:   {rate:.0} verified turns/sec");

    // Bookkeeping invariants (the run is a real artifact, not a print job):
    assert_eq!(
        c.drained, queue.resolved_executed,
        "every drained turn must have resolved its queue row to executed"
    );
    assert_eq!(
        c.drained, queue.mirrored,
        "every drained turn mirrored its post-image"
    );
    assert_eq!(
        c.resolved(),
        queue.resolved_executed + queue.resolved_refused,
        "counters and the queue audit must agree on resolved rows"
    );
    // Conservation: the stand-in producer conserved value across the whole drain.
    let p = drainer.producer();
    let agents_total: i64 = (0..4u8).map(|t| p.balance(agent_id(0x20 + t))).sum();
    let total = p.balance(SOURCE) + agents_total;
    println!(
        "  conservation:      Σ balances = {total}  (== float 1000000000)  {}",
        if total == 1_000_000_000 {
            "✓"
        } else {
            "✗ BROKEN"
        }
    );
    assert_eq!(total, 1_000_000_000, "drained stream must conserve value");

    println!("\n  (postgres-free demo of the worker loop. The live daemon runs the SAME loop");
    println!("   over dregg.submit_queue via dregg_drain_once(); see docs/PG-DREGG.md §11.4.)");
}

/// One poll cycle, split into the source-read then sink-write phases (so a real
/// `&mut queue` plays both roles without aliasing) — the demo analog of the live
/// worker's "read pending rows, drain, UPDATE outcomes" transaction.
fn poll_cycle(
    drainer: &mut Drainer<FoldProducer>,
    queue: &mut DemoQueue,
    batch: usize,
) -> PollReport {
    let pending = queue.pending(batch).unwrap_or_default();
    let mut report = PollReport::default();
    for intent in &pending {
        let outcome = drainer.drain(intent);
        let mirrored_batch = if outcome.is_executed() {
            drainer.last_batch().cloned()
        } else {
            None
        };
        queue
            .resolve(intent, &outcome, mirrored_batch.as_ref())
            .expect("demo sink never fails");
        report.processed += 1;
        if outcome.is_executed() {
            report.executed += 1;
        } else {
            report.refused += 1;
        }
    }
    let lag = queue.pending_depth().unwrap_or(0);
    drainer.set_lag(lag);
    report.lag = lag;
    report
}

fn hx(b: [u8; 32]) -> String {
    b.iter().take(6).map(|x| format!("{x:02x}")).collect()
}
