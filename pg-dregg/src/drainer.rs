//! The submit-queue **drainer** — the node-side worker that turns queued submit
//! intents into verified state (the M3 follow-up named in [`crate::mirror::ddl::write_outbox`]).
//!
//! # Where this sits
//!
//! The write path has two halves (`docs/PG-DREGG.md` §11):
//!
//!   * the ENQUEUE half (shipped): a pg-user calls `dregg_submit_turn(signed, agent)`,
//!     which RLS-gates the insert on the `submit_gate` policy and lands a `pending`
//!     row in `dregg.submit_queue`. **Postgres never executes** — it only records an
//!     intent the verifier must accept.
//!   * the DRAIN half (THIS module): a long-running node-side worker polls the queue
//!     in arrival order, runs each intent through the verified-write spine, mirrors
//!     the post-image back, and resolves the row (`executed` | `refused`).
//!
//! The drainer is the bridge that keeps the spine invariant — *state mutates ONLY
//! through verified turns* — true for the write path: a queued intent becomes state
//! only after it passes the SAME three gates the mirror enforces.
//!
//! # The four gates (per drained intent)
//!
//!   1. **SUBMIT** — re-check the acting agent's capability admits `submit` on its
//!      cell ([`authz::decide`]). RLS already gated the *enqueue*, but the drainer
//!      runs as the BYPASSRLS kernel role, so it re-checks the token itself —
//!      defence in depth, and the only check on a row enqueued before a capability
//!      was revoked (revocation is consulted on every [`authz::decide`]).
//!   2. **PRODUCE** — run the intent through the real verified executor ([`Producer`]),
//!      which decodes the signed turn, executes it, and yields the verified-turn
//!      post-image as a [`MirrorBatch`]. This is the executor seam: a real node plugs
//!      in the Lean executor here (the Tier-D / sidecar producer, `docs/PG-DREGG-TIER-D-SPIKE.md`);
//!      the postgres-free core ships a deterministic stand-in ([`FoldProducer`]) so
//!      the gate plumbing is `cargo test`-provable without the executor in the build.
//!   3. **CHAIN** — admit the produced batch onto the durable head via the real
//!      [`RootChain`] anti-substitution tooth. A batch that does not chain (a stale
//!      head, a reordered drain, a forged root) is REFUSED — the head never moves.
//!   4. **MIRROR + RESOLVE** — materialize the post-image rows and resolve the queue
//!      row to `executed` (with the receipt hash) in ONE logical commit; a producer
//!      or chain refusal resolves it to `refused` (with the reason), so the submitter
//!      learns the outcome by reading its own row.
//!
//! # What is and is NOT in this crate
//!
//! pg-dregg deliberately does not depend on the executor (`dregg-cell` / the Lean
//! FFI) — it depends only on `dregg-auth` (circuit-free, offline). So the PRODUCE
//! gate is a trait ([`Producer`]), exactly as the workflow runtime's canonical-root
//! step is a trait ([`crate::workflow::Projector`]). The real executor is supplied
//! by the node binary; this module owns the gate sequencing, the chain discipline,
//! the outcome bookkeeping, and the observability — all of which are independent of
//! *which* executor runs and are proven here over the [`FoldProducer`] stand-in.
//!
//! # The live wiring
//!
//! The pgrx side ([`crate::pg`]) exposes `dregg_drain_once()` / `dregg_drain_stats()`
//! externs that drive this core over `dregg.submit_queue` rows read by the kernel
//! role, and the `src/bin/drainerd.rs` daemon runs the poll loop. The in-process
//! [`Drainer`] here is the postgres-free engine both call.

use crate::authz;
use crate::mirror::{MemCell, MirrorBatch, RootChain};
// The node-side post-image constructors (the SAME ones `bin/loadgen.rs` and the
// workflow runtime use), so a drained turn's rows are built identically to a
// workflow-driven turn's — no second projection to drift.
use crate::workflow::{balance_reg, cell_row, turn_row};

// ============================================================================
// The submit intent — one `dregg.submit_queue` row, as the drainer reads it.
// ============================================================================

/// A pending submit intent — the projection of a `dregg.submit_queue` row the
/// drainer needs to process it. The live path reads these (ordered by `id`, i.e.
/// arrival order, since the uuidv7 key is time-sortable) for `status = 'pending'`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SubmitIntent {
    /// The queue row id (the uuidv7 primary key, as 16 bytes). Carried so the
    /// drainer can resolve exactly this row; opaque to the gates.
    pub id: [u8; 16],
    /// The acting agent's cell id — the `agent` column. The SUBMIT gate decides
    /// `submit` on this; the produced turn records it as `creator`.
    pub agent: [u8; 32],
    /// The signed turn bytes — the `signed_turn` column (postcard `SignedTurn`).
    /// Opaque here; the [`Producer`] decodes + executes it.
    pub signed_turn: Vec<u8>,
    /// The submitter's presented capability token (the `dregg.token` the enqueue
    /// ran under). The live path persists it alongside the row so the drainer can
    /// re-check the SUBMIT gate against the same token RLS gated the enqueue with.
    pub token: String,
}

impl SubmitIntent {
    /// A short hex of the queue id, for logs / diagnostics.
    pub fn id_hex(&self) -> String {
        self.id.iter().map(|b| format!("{b:02x}")).collect()
    }
}

// ============================================================================
// The PRODUCE gate — the verified-executor seam.
// ============================================================================

/// The verified executor, as the drainer's PRODUCE gate sees it: decode a signed
/// turn for `agent`, execute it against the current state head, and yield the
/// verified-turn post-image as a [`MirrorBatch`] (or refuse it with a reason).
///
/// This is the adoptability seam between the postgres-resident drain machinery
/// (this crate) and the verified executor (the node, `dregg-cell` / the Lean FFI,
/// which this crate deliberately does not link). It mirrors
/// [`crate::workflow::Projector`]: the runtime stays independent of *which*
/// executor runs, and the postgres-free core proves the gate sequencing over a
/// deterministic stand-in ([`FoldProducer`]).
///
/// # Contract
///
/// * `produce` receives the intent and the CONTEXT the executor needs to build a
///   chaining post-image: the `ordinal` the chain next expects and the `prev_root`
///   it must chain onto. A faithful executor stamps these onto the returned turn
///   header so the CHAIN gate accepts it.
/// * It returns `Ok(batch)` with the verified post-image, or `Err(reason)` if the
///   turn does not execute (an overspend, an unauthorized effect, a malformed
///   envelope) — which the drainer records as a `refused` outcome.
/// * The returned batch's `creator` MUST be the intent's `agent` (provenance);
///   the drainer asserts this so a producer cannot misattribute a turn.
pub trait Producer {
    /// Execute the intent against `(ordinal, prev_root)` and return its verified
    /// post-image, or a refusal reason.
    fn produce(
        &mut self,
        intent: &SubmitIntent,
        ordinal: u64,
        prev_root: [u8; 32],
    ) -> Result<MirrorBatch, String>;
}

/// The deterministic stand-in [`Producer`] for the postgres-free core — the
/// drain-side twin of [`crate::workflow::FoldProjector`].
///
/// It does NOT decode the signed turn (this crate has no executor); instead it
/// derives a well-formed, chaining, value-CONSERVING post-image deterministically
/// from `(prev_root, ordinal, agent, signed_turn)`, so the gate plumbing — submit
/// re-check, chain admission, mirror, resolve, the counters — is exercised end to
/// end and `cargo test`-proven. A real node replaces this with the executor.
///
/// The synthesized turn credits the acting `agent`'s cell by a fixed unit and
/// debits a fixed `float` source cell, so a stream of drained intents conserves
/// value (the same shape `bin/loadgen.rs` drives) — which lets the demo assert
/// conservation over the drained result, not just "a row landed".
#[derive(Clone, Debug)]
pub struct FoldProducer {
    /// The source cell every synthesized transfer debits (the float holder).
    pub source: [u8; 32],
    /// The unit each synthesized transfer moves.
    pub unit: i64,
    /// The running per-cell `(balance, nonce)` the stand-in maintains so its
    /// post-images are internally consistent across a drain run (the executor
    /// would read this from state; the stand-in tracks it itself).
    balances: std::collections::BTreeMap<[u8; 32], (i64, u64)>,
}

impl FoldProducer {
    /// A stand-in producer with `source` funded to `float`, moving `unit` per turn.
    pub fn new(source: [u8; 32], float: i64, unit: i64) -> Self {
        let mut balances = std::collections::BTreeMap::new();
        balances.insert(source, (float, 0));
        FoldProducer {
            source,
            unit,
            balances,
        }
    }

    /// The stand-in's notion of a cell's `(balance, nonce)` (for assertions/demos).
    pub fn balance(&self, id: [u8; 32]) -> i64 {
        self.balances.get(&id).map(|&(b, _)| b).unwrap_or(0)
    }

    /// A deterministic FNV-1a fold over the chaining context — the stand-in's
    /// `ledger_root` (the executor would supply the kernel's real root). Pinned to
    /// the SAME algorithm `bin/loadgen.rs` uses so the two agree on a post-state.
    /// Delegates to the shared [`fold_chain_root`] so the Tier-D
    /// [`crate::lean_producer::LeanProducer`] derives a BIT-IDENTICAL root from the
    /// same context — a mixed-producer history (some turns from the stand-in, some
    /// from the verified executor) still chains.
    fn fold_root(prev: [u8; 32], ordinal: u64, touched: &[([u8; 32], i64, u64)]) -> [u8; 32] {
        fold_chain_root(prev, ordinal, touched)
    }
}

/// The deterministic FNV-1a chaining-root fold, shared by [`FoldProducer`] and the
/// Tier-D [`crate::lean_producer::LeanProducer`] (and bit-identical to
/// `bin/loadgen.rs`). This is the producers' `ledger_root` over the chaining
/// context `(prev_root, ordinal, touched-cells)`: the CHAIN gate's anti-substitution
/// tooth is structural on these roots (the kernel's in-circuit root is the
/// whole-chain IVC light client's concern, `docs/PG-DREGG.md` §10.2), so a single
/// shared derivation is what lets the two producers' turns share one chain.
pub fn fold_chain_root(prev: [u8; 32], ordinal: u64, touched: &[([u8; 32], i64, u64)]) -> [u8; 32] {
    let mut acc: u64 = 0xcbf29ce484222325 ^ ordinal.wrapping_mul(0x100000001b3);
    for b in prev {
        acc = (acc ^ b as u64).wrapping_mul(0x100000001b3);
    }
    for (id, bal, nonce) in touched {
        for b in id {
            acc = (acc ^ *b as u64).wrapping_mul(0x100000001b3);
        }
        acc = (acc ^ *bal as u64).wrapping_mul(0x100000001b3);
        acc = (acc ^ *nonce).wrapping_mul(0x100000001b3);
    }
    let mut out = [0u8; 32];
    for (i, chunk) in out.chunks_mut(8).enumerate() {
        let v = acc.wrapping_add((i as u64).wrapping_mul(0x9e3779b97f4a7c15));
        chunk.copy_from_slice(&v.to_le_bytes());
    }
    out
}

impl Producer for FoldProducer {
    fn produce(
        &mut self,
        intent: &SubmitIntent,
        ordinal: u64,
        prev_root: [u8; 32],
    ) -> Result<MirrorBatch, String> {
        // The stand-in refuses an empty envelope (a malformed intent), so the
        // `refused` outcome path is real and not synthetic.
        if intent.signed_turn.is_empty() {
            return Err("empty signed turn (malformed envelope)".to_string());
        }
        let (src_bal, src_nonce) = *self.balances.get(&self.source).unwrap_or(&(0, 0));
        if src_bal < self.unit {
            return Err(format!(
                "stand-in float exhausted: source holds {src_bal}, unit is {}",
                self.unit
            ));
        }
        let (dst_bal, _) = *self.balances.get(&intent.agent).unwrap_or(&(0, 0));
        // One debit (source), one credit (agent) — conserves value.
        let new_src = (self.source, src_bal - self.unit, src_nonce + 1);
        let new_dst = (intent.agent, dst_bal + self.unit, 0);
        let touched = [new_src, new_dst];
        let post = Self::fold_root(prev_root, ordinal, &touched);

        let cells = vec![
            cell_row(new_src.0, new_src.1, new_src.2),
            cell_row(new_dst.0, new_dst.1, new_dst.2),
        ];
        let memory: Vec<MemCell> = touched
            .iter()
            .map(|&(id, bal, _)| balance_reg(id, bal))
            .collect();
        // `creator` is the acting agent (provenance the drainer asserts).
        let turn = turn_row(ordinal, prev_root, post, intent.agent);
        let batch = MirrorBatch::from_parts(turn, cells, vec![], memory)
            .map_err(|m| format!("stand-in produced a malformed batch: {m}"))?;

        // Advance the stand-in's own state so the next produced turn is consistent.
        self.balances.insert(new_src.0, (new_src.1, new_src.2));
        self.balances.insert(new_dst.0, (new_dst.1, new_dst.2));
        Ok(batch)
    }
}

// ============================================================================
// The outcome — what the drainer resolved an intent to.
// ============================================================================

/// The terminal status the drainer resolves a queue row to (the `status` column
/// walks `pending → executed | refused`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DrainOutcome {
    /// The intent passed all four gates: the post-image is mirrored and the row is
    /// `executed`. Carries the receipt hash the submitter reads back.
    Executed { receipt_hash: [u8; 32] },
    /// The intent was REFUSED at a gate. Carries which gate and the human reason
    /// (written to the row's `error` column).
    Refused { gate: Gate, reason: String },
}

impl DrainOutcome {
    /// Whether the intent executed (mirrored to state).
    pub fn is_executed(&self) -> bool {
        matches!(self, DrainOutcome::Executed { .. })
    }
    /// The `status` text for the queue row.
    pub fn status(&self) -> &'static str {
        match self {
            DrainOutcome::Executed { .. } => "executed",
            DrainOutcome::Refused { .. } => "refused",
        }
    }
    /// The refusal reason, if refused.
    pub fn reason(&self) -> Option<&str> {
        match self {
            DrainOutcome::Refused { reason, .. } => Some(reason),
            DrainOutcome::Executed { .. } => None,
        }
    }
}

/// Which gate refused an intent — the bucket the [`DrainCounters`] increments and
/// the row's `error` is prefixed with, so an operator sees *where* drains fail.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Gate {
    /// GATE 1 — the capability did not admit `submit` (or was revoked between
    /// enqueue and drain).
    Submit,
    /// GATE 2 — the executor refused to produce a turn (overspend, unauthorized
    /// effect, malformed envelope).
    Produce,
    /// GATE 3 — the produced batch did not chain onto the head (a CONFLICT: a
    /// stale head, a reorder, a replay).
    Chain,
}

impl Gate {
    /// A short label for logs / the `error` prefix.
    pub fn label(&self) -> &'static str {
        match self {
            Gate::Submit => "submit",
            Gate::Produce => "produce",
            Gate::Chain => "chain",
        }
    }
}

// ============================================================================
// Observability — the drain counters an operator dashboard / health check reads.
// ============================================================================

/// The drain counters — the observability the worker exposes (drained / refused /
/// conflict, and the queue lag). Every field is a running total over the drains
/// this worker has performed, plus the instantaneous lag; the SQL each corresponds
/// to is noted so the in-process numbers and a live `dregg.*` query agree.
///
/// `refused` is the TOTAL refusals (all gates); `conflict` is the subset refused
/// specifically at the CHAIN gate (an anti-substitution / stale-head conflict),
/// surfaced separately because it is the one an operator acts on differently
/// (a chain conflict means concurrent writers or a stale drainer, not a bad turn).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct DrainCounters {
    /// Intents that EXECUTED (mirrored to state) — `SELECT count(*) FROM
    /// dregg.submit_queue WHERE status = 'executed'` over this worker's drains.
    pub drained: u64,
    /// Intents REFUSED at any gate — `… WHERE status = 'refused'`.
    pub refused: u64,
    /// The subset of `refused` refused at the CHAIN gate (an anti-substitution
    /// conflict). `conflict <= refused` always.
    pub conflict: u64,
    /// Intents refused at the SUBMIT gate (capability denied / revoked).
    pub unauthorized: u64,
    /// Intents refused at the PRODUCE gate (the executor rejected the turn).
    pub produce_refused: u64,
    /// The CURRENT queue lag — pending rows not yet drained — `SELECT count(*)
    /// FROM dregg.submit_queue WHERE status = 'pending'`. Updated each poll.
    pub lag: u64,
}

impl DrainCounters {
    /// Total intents this worker has resolved (executed + refused).
    pub fn resolved(&self) -> u64 {
        self.drained + self.refused
    }

    /// Fold one outcome into the counters (the per-intent bookkeeping).
    pub fn record(&mut self, outcome: &DrainOutcome) {
        match outcome {
            DrainOutcome::Executed { .. } => self.drained += 1,
            DrainOutcome::Refused { gate, .. } => {
                self.refused += 1;
                match gate {
                    Gate::Submit => self.unauthorized += 1,
                    Gate::Produce => self.produce_refused += 1,
                    Gate::Chain => self.conflict += 1,
                }
            }
        }
    }

    /// A one-line operator summary (logs / a `/metrics` line).
    pub fn summary(&self) -> String {
        format!(
            "drained={} refused={} (unauth={} produce={} conflict={}) lag={}",
            self.drained,
            self.refused,
            self.unauthorized,
            self.produce_refused,
            self.conflict,
            self.lag
        )
    }
}

// ============================================================================
// The Drainer — the in-process drain engine (the verified-write spine).
// ============================================================================

/// The drain engine — the postgres-free core the live worker drives. It owns the
/// chain-gate head ([`RootChain`], resumed from the durable `dregg.turns` head),
/// the [`Producer`] (the executor seam), the AUTHZ clock, and the [`DrainCounters`].
///
/// Each [`Drainer::drain`] call runs ONE intent through the four gates and returns
/// its [`DrainOutcome`] (which the live wiring writes back to the queue row and
/// whose mirrored rows it materializes). A refusal NEVER moves the head — the
/// engine state and the durable store stay consistent on a refused intent.
pub struct Drainer<P: Producer> {
    /// The chain-gate head over the durable turns. Resumed from `dregg.turns`
    /// (max-ordinal row) on the live path; pinned at genesis for a fresh store.
    chain: RootChain,
    /// The executor seam.
    producer: P,
    /// The clock the SUBMIT gate evaluates time caveats against (the backend
    /// `now()`); fixed per drain pass for reproducibility.
    clock: i64,
    /// The running observability.
    counters: DrainCounters,
    /// The post-images the most recent successful drain produced — the rows the
    /// live wiring materializes into `dregg.cells` / `dregg.memory` for that turn.
    last_batch: Option<MirrorBatch>,
}

impl<P: Producer> Drainer<P> {
    /// A fresh drainer expecting genesis (ordinal 0) with the given executor seam.
    /// `head()` is `None` until the first turn drains; the first produced batch
    /// chains onto the all-zero genesis root ([`RootChain::new`]).
    pub fn new(producer: P) -> Self {
        Drainer {
            chain: RootChain::new(),
            producer,
            clock: 1_000,
            counters: DrainCounters::default(),
            last_batch: None,
        }
    }

    /// Resume the drainer's chain from the durable head — the restart path. The
    /// live worker reads `(ledger_root, max_ordinal + 1)` from `dregg.turns` and
    /// passes them here so the next drained turn chains onto exactly where the
    /// store left off (and a stale replay is refused by the chain tooth).
    pub fn resume_chain(&mut self, head: [u8; 32], next_ordinal: u64) {
        self.chain = RootChain::resume(head, next_ordinal);
    }

    /// Set the SUBMIT-gate clock (builder).
    pub fn with_clock(mut self, clock: i64) -> Self {
        self.clock = clock;
        self
    }

    /// The current chain head root (post-state of the last drained turn).
    pub fn head(&self) -> Option<[u8; 32]> {
        self.chain.head()
    }

    /// The ordinal the chain next expects.
    pub fn next_ordinal(&self) -> u64 {
        self.chain.next_ordinal()
    }

    /// The running counters (a copy — they are cheap and `Copy`).
    pub fn counters(&self) -> DrainCounters {
        self.counters
    }

    /// Update the observed queue lag (pending rows not yet drained). The live
    /// worker calls this with `SELECT count(*) … WHERE status='pending'` each poll.
    pub fn set_lag(&mut self, pending: u64) {
        self.counters.lag = pending;
    }

    /// The post-image of the most recent successful drain — the rows to materialize
    /// for that turn (the live wiring reads this after a `drain` that executed).
    pub fn last_batch(&self) -> Option<&MirrorBatch> {
        self.last_batch.as_ref()
    }

    /// Borrow the executor seam (e.g. to read a [`FoldProducer`]'s balances in a
    /// demo / conservation assertion).
    pub fn producer(&self) -> &P {
        &self.producer
    }

    /// DRAIN one intent through the four gates. The heart of the worker.
    ///
    /// Returns the [`DrainOutcome`] AND folds it into the counters. On
    /// `Executed`, the chain head advanced and [`Drainer::last_batch`] holds the
    /// rows to mirror; on `Refused`, the head is UNCHANGED (no state leaked) and
    /// `last_batch` is cleared.
    pub fn drain(&mut self, intent: &SubmitIntent) -> DrainOutcome {
        let outcome = self.drain_inner(intent);
        self.counters.record(&outcome);
        outcome
    }

    fn drain_inner(&mut self, intent: &SubmitIntent) -> DrainOutcome {
        self.last_batch = None;

        // ---- GATE 1: SUBMIT — re-check the capability (defence in depth). ------
        // RLS gated the enqueue; the drainer runs BYPASSRLS, so it re-checks the
        // SAME decision against the persisted token. This is also the ONLY check
        // on a row enqueued before the capability was revoked (revocation is
        // consulted on every authz::decide), so a revoked-since-enqueue intent is
        // refused here, never executed.
        let decision = authz::decide(&intent.token, "submit", &hex(&intent.agent), self.clock);
        if !decision.allowed() {
            return DrainOutcome::Refused {
                gate: Gate::Submit,
                reason: decision.reason(),
            };
        }

        // ---- GATE 2: PRODUCE — run the verified executor (the seam). -----------
        let ordinal = self.chain.next_ordinal();
        let prev = self.chain.head().unwrap_or(crate::workflow::GENESIS_ROOT);
        let batch = match self.producer.produce(intent, ordinal, prev) {
            Ok(b) => b,
            Err(reason) => {
                return DrainOutcome::Refused {
                    gate: Gate::Produce,
                    reason,
                };
            }
        };
        // Provenance: a producer cannot misattribute the turn. The creator MUST be
        // the acting agent the SUBMIT gate authorized.
        if batch.turn.creator != intent.agent {
            return DrainOutcome::Refused {
                gate: Gate::Produce,
                reason: format!(
                    "producer misattributed the turn: creator {} != agent {}",
                    hex(&batch.turn.creator),
                    hex(&intent.agent)
                ),
            };
        }

        // ---- GATE 3: CHAIN — the anti-substitution tooth. ----------------------
        // Admitted ONLY if its ordinal is next-expected AND its prev_root equals
        // the head. A failure here is a CONFLICT (counted separately).
        if let Err(c) = self.chain.extend(&batch) {
            return DrainOutcome::Refused {
                gate: Gate::Chain,
                reason: c.to_string(),
            };
        }

        // ---- GATE 4: resolve EXECUTED — stash the rows to mirror. --------------
        // The chain advanced. The live wiring materializes `batch`'s rows and
        // resolves the queue row to `executed` with this receipt, in one commit.
        let receipt_hash = batch.turn.receipt_hash;
        self.last_batch = Some(batch);
        DrainOutcome::Executed { receipt_hash }
    }

    /// Drain a whole pending slice in arrival order, returning the per-intent
    /// outcomes (and folding each into the counters). Stops on NOTHING — a refused
    /// intent is recorded and the drainer moves on to the next (one bad turn does
    /// not stall the queue). This is the worker's inner batch step.
    pub fn drain_all(&mut self, pending: &[SubmitIntent]) -> Vec<(SubmitIntent, DrainOutcome)> {
        let mut out = Vec::with_capacity(pending.len());
        for intent in pending {
            let outcome = self.drain(intent);
            out.push((intent.clone(), outcome));
        }
        out
    }
}

// ============================================================================
// The worker loop — the seams a long-running daemon drives the Drainer over.
// ============================================================================

/// Where the worker reads pending intents from and where it learns the durable
/// head to resume on. The live implementation is `dregg.submit_queue` +
/// `dregg.turns` read as the kernel role; the daemon's demo uses an in-memory
/// queue. Kept a trait so the poll loop ([`Drainer::poll_once`]) is exercised by
/// `cargo test` without a database.
pub trait QueueSource {
    /// The durable head the chain resumes on at startup: `(ledger_root,
    /// next_ordinal)` from the max-ordinal `dregg.turns` row, or `None` for a
    /// fresh (genesis) store.
    fn durable_head(&self) -> Result<Option<([u8; 32], u64)>, String>;

    /// Read up to `limit` pending intents in arrival order (`status = 'pending'`
    /// ORDER BY id LIMIT limit). An empty vec means the queue is drained.
    fn pending(&mut self, limit: usize) -> Result<Vec<SubmitIntent>, String>;

    /// The current pending depth — the queue lag (`count(*) WHERE status =
    /// 'pending'`). Read each poll for the `lag` counter.
    fn pending_depth(&self) -> Result<u64, String>;
}

/// Where the worker writes outcomes: it materializes a drained turn's post-image
/// (into `dregg.cells` / `dregg.memory`, via the Tier-C path) and resolves the
/// queue row (`executed` | `refused`). The live implementation is the SECURITY
/// DEFINER apply + an `UPDATE dregg.submit_queue`; the demo records to memory.
pub trait OutcomeSink {
    /// Persist a drained turn's verified post-image (the mirror write) AND resolve
    /// its queue row to `executed`/`refused` — ONE logical commit. `batch` is
    /// `Some` only on an `executed` outcome (the rows to materialize).
    fn resolve(
        &mut self,
        intent: &SubmitIntent,
        outcome: &DrainOutcome,
        batch: Option<&MirrorBatch>,
    ) -> Result<(), String>;
}

/// What one [`Drainer::poll_once`] did — the per-poll report the daemon logs.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct PollReport {
    /// Intents processed this poll (drained + refused).
    pub processed: usize,
    /// Of those, how many executed.
    pub executed: usize,
    /// Of those, how many were refused (any gate).
    pub refused: usize,
    /// The queue lag observed at the END of the poll.
    pub lag: u64,
}

impl PollReport {
    /// Whether the poll did any work (drove progress). A daemon backs off its
    /// sleep when this is false (the queue is idle).
    pub fn did_work(&self) -> bool {
        self.processed > 0
    }
}

impl<P: Producer> Drainer<P> {
    /// Resume the chain from a [`QueueSource`]'s durable head — the worker's
    /// startup step. After this the next drained turn chains onto exactly where
    /// `dregg.turns` left off (and a stale replay is refused by the chain tooth).
    pub fn resume_from<Q: QueueSource>(&mut self, source: &Q) -> Result<(), String> {
        if let Some((head, next_ordinal)) = source.durable_head()? {
            self.resume_chain(head, next_ordinal);
        }
        Ok(())
    }

    /// ONE poll cycle of the worker loop: read up to `batch_limit` pending intents,
    /// drain each through the four gates, persist+resolve each via the [`OutcomeSink`],
    /// and refresh the lag counter. Returns the [`PollReport`]. This is the body the
    /// daemon repeats; a refused intent is resolved and the poll continues (one bad
    /// turn never stalls the queue).
    ///
    /// A persist failure on the sink is propagated (a durability fault the daemon
    /// must see) AFTER the chain already advanced — the engine and the store have
    /// then diverged by one turn until it is resolved, exactly the
    /// [`crate::workflow::StepError::Durability`] contract.
    pub fn poll_once<Q: QueueSource, S: OutcomeSink>(
        &mut self,
        source: &mut Q,
        sink: &mut S,
        batch_limit: usize,
    ) -> Result<PollReport, String> {
        let pending = source.pending(batch_limit)?;
        let mut report = PollReport::default();
        for intent in &pending {
            let outcome = self.drain(intent);
            let batch = if outcome.is_executed() {
                self.last_batch()
            } else {
                None
            };
            sink.resolve(intent, &outcome, batch)?;
            report.processed += 1;
            if outcome.is_executed() {
                report.executed += 1;
            } else {
                report.refused += 1;
            }
        }
        let lag = source.pending_depth()?;
        self.set_lag(lag);
        report.lag = lag;
        Ok(report)
    }
}

// ============================================================================
// Cosmetics.
// ============================================================================

fn hex(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        s.push_str(&format!("{b:02x}"));
    }
    s
}

// ============================================================================
// Tests — the drain properties, over the REAL spine (chain tooth + authz core).
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_auth::credential::{Caveat, Pred, RootKey};

    const SOURCE: [u8; 32] = [0xc0u8; 32];

    fn agent(tag: u8) -> [u8; 32] {
        let mut id = [0x11u8; 32];
        id[0] = tag;
        id
    }

    /// Install a fresh trust root and return `(guard, issuer)`. The guard is the
    /// SHARED process-wide serialization lock ([`authz::test_serial_lock`]) — these
    /// tests mutate the global authz state (issuer key + LRU + revocation set),
    /// which the whole `pg-dregg` lib-test binary shares, so each test MUST own that
    /// state for its body or a parallel authz/workflow/drainer test would see a
    /// foreign key and fail. Bind it for the test body: `let (_g, issuer) = ...`.
    #[must_use]
    fn fresh_issuer() -> (std::sync::MutexGuard<'static, ()>, RootKey) {
        let guard = authz::test_serial_lock();
        let issuer = RootKey::from_seed([7u8; 32]);
        authz::set_issuer_pubkey(issuer.public());
        authz::lru_clear();
        authz::revoked_clear();
        (guard, issuer)
    }

    /// A `submit`-on-everything token (the broad-but-real load token).
    fn submit_token(issuer: &RootKey) -> String {
        issuer
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
            .encode()
    }

    fn intent(id: u8, agent: [u8; 32], token: &str) -> SubmitIntent {
        SubmitIntent {
            id: [id; 16],
            agent,
            signed_turn: vec![0xab, 0xcd], // non-empty = well-formed to the stand-in
            token: token.to_string(),
        }
    }

    #[test]
    fn an_authorized_intent_drains_and_advances_the_chain() {
        let (_g, issuer) = fresh_issuer();
        let tok = submit_token(&issuer);
        let mut d = Drainer::new(FoldProducer::new(SOURCE, 1_000, 1)).with_clock(1_000);

        assert_eq!(d.next_ordinal(), 0);
        let out = d.drain(&intent(1, agent(0x20), &tok));
        assert!(out.is_executed(), "authorized intent must drain: {out:?}");
        // The chain advanced and the post-image is ready to mirror.
        assert_eq!(d.next_ordinal(), 1);
        assert!(d.head().is_some());
        assert!(d.last_batch().is_some());
        assert_eq!(d.counters().drained, 1);
        assert_eq!(d.counters().refused, 0);
    }

    #[test]
    fn an_unauthorized_intent_is_refused_and_the_head_never_moves() {
        let (_g, issuer) = fresh_issuer();
        // A token that admits `read`, NOT `submit` — the submit gate must refuse it.
        let read_tok = issuer
            .mint([Caveat::FirstParty(Pred::AttrEq {
                key: "action".into(),
                value: "read".into(),
            })])
            .encode();
        let mut d = Drainer::new(FoldProducer::new(SOURCE, 1_000, 1)).with_clock(1_000);

        let out = d.drain(&intent(1, agent(0x20), &read_tok));
        assert!(!out.is_executed());
        assert!(matches!(
            out,
            DrainOutcome::Refused {
                gate: Gate::Submit,
                ..
            }
        ));
        // Fail-closed: nothing produced, nothing chained, no state leaked.
        assert_eq!(d.next_ordinal(), 0);
        assert!(d.head().is_none());
        assert!(d.last_batch().is_none());
        assert_eq!(d.counters().unauthorized, 1);
        assert_eq!(d.counters().drained, 0);
    }

    #[test]
    fn a_revoked_since_enqueue_token_is_refused_at_drain() {
        let (_g, issuer) = fresh_issuer();
        let tok = submit_token(&issuer);
        // The row was enqueued fine, but the capability is revoked before the
        // drainer gets to it — the drainer's submit re-check catches it.
        let id = authz::cap_id(&tok).expect("token has an id");
        authz::revoke(&id);

        let mut d = Drainer::new(FoldProducer::new(SOURCE, 1_000, 1)).with_clock(1_000);
        let out = d.drain(&intent(1, agent(0x20), &tok));
        assert!(matches!(
            out,
            DrainOutcome::Refused {
                gate: Gate::Submit,
                ..
            }
        ));
        assert_eq!(out.reason(), Some("revoked"));
        assert_eq!(d.next_ordinal(), 0, "a revoked intent never executes");
    }

    #[test]
    fn a_malformed_envelope_is_refused_at_produce() {
        let (_g, issuer) = fresh_issuer();
        let tok = submit_token(&issuer);
        let mut d = Drainer::new(FoldProducer::new(SOURCE, 1_000, 1)).with_clock(1_000);

        let mut bad = intent(1, agent(0x20), &tok);
        bad.signed_turn = vec![]; // empty = malformed to the stand-in executor
        let out = d.drain(&bad);
        assert!(matches!(
            out,
            DrainOutcome::Refused {
                gate: Gate::Produce,
                ..
            }
        ));
        assert_eq!(d.counters().produce_refused, 1);
        assert_eq!(d.next_ordinal(), 0);
    }

    /// A deliberately STALE producer: it ignores the `(ordinal, prev_root)` the
    /// drainer hands it and always stamps the turn at a FIXED stale ordinal/root.
    /// This is the adversarial model of an executor working off a snapshot the
    /// store has already moved past — exactly what the CHAIN gate must catch.
    struct StaleProducer {
        stale_ordinal: u64,
        stale_prev: [u8; 32],
    }
    impl Producer for StaleProducer {
        fn produce(
            &mut self,
            intent: &SubmitIntent,
            _ordinal: u64,
            _prev_root: [u8; 32],
        ) -> Result<MirrorBatch, String> {
            // Build a well-formed batch, but at the STALE coordinates (not the ones
            // the drainer passed) — so the chain tooth sees an ordinal gap.
            let cells = vec![cell_row(intent.agent, 1, 0)];
            let memory = vec![balance_reg(intent.agent, 1)];
            let post = [0x99u8; 32];
            let turn = turn_row(self.stale_ordinal, self.stale_prev, post, intent.agent);
            MirrorBatch::from_parts(turn, cells, vec![], memory)
        }
    }

    #[test]
    fn a_stale_turn_conflicts_at_the_chain_gate() {
        // The store has advanced to ordinal 5 (resume there); a stale producer
        // hands the drainer a turn stamped for ordinal 0. The chain tooth refuses
        // it as an ordinal gap — a CONFLICT, counted separately.
        let (_g, issuer) = fresh_issuer();
        let tok = submit_token(&issuer);
        let mut d = Drainer::new(StaleProducer {
            stale_ordinal: 0,
            stale_prev: crate::workflow::GENESIS_ROOT,
        })
        .with_clock(1_000);
        d.resume_chain([0x55; 32], 5); // the durable head is at ordinal 5

        let out = d.drain(&intent(1, agent(0x20), &tok));
        assert!(matches!(
            out,
            DrainOutcome::Refused {
                gate: Gate::Chain,
                ..
            }
        ));
        assert_eq!(d.counters().conflict, 1);
        assert_eq!(d.counters().refused, 1);
        // Fail-closed: the stale conflict never advanced the head.
        assert_eq!(d.next_ordinal(), 5);
        assert!(d.last_batch().is_none());
    }

    #[test]
    fn draining_a_stream_conserves_value_end_to_end() {
        // A stream of authorized intents drains; the stand-in producer conserves
        // value every turn (one debit, one credit), so Σ balances is invariant.
        let (_g, issuer) = fresh_issuer();
        let tok = submit_token(&issuer);
        let float = 1_000i64;
        let mut d = Drainer::new(FoldProducer::new(SOURCE, float, 1)).with_clock(1_000);

        let pending: Vec<SubmitIntent> = (0..16)
            .map(|k| intent(k as u8, agent(0x20 + (k % 4) as u8), &tok))
            .collect();
        let results = d.drain_all(&pending);

        assert_eq!(results.len(), 16);
        assert!(results.iter().all(|(_, o)| o.is_executed()));
        assert_eq!(d.counters().drained, 16);
        assert_eq!(d.next_ordinal(), 16);

        // Conservation: the source's debits exactly fund the agents' credits.
        let p = d.producer();
        let agents_total: i64 = (0..4).map(|t| p.balance(agent(0x20 + t))).sum();
        assert_eq!(
            p.balance(SOURCE) + agents_total,
            float,
            "drained stream must conserve value"
        );
    }

    // ---- the worker loop over in-memory queue seams -----------------------

    /// An in-memory [`QueueSource`] + [`OutcomeSink`] — the demo/test queue. Holds
    /// pending intents and records resolved outcomes (status + mirrored batches),
    /// so the poll loop is exercised without a database.
    #[derive(Default)]
    struct MemQueue {
        pending: std::collections::VecDeque<SubmitIntent>,
        resolved: Vec<(SubmitIntent, DrainOutcome)>,
        mirrored: Vec<MirrorBatch>,
        durable: Option<([u8; 32], u64)>,
    }
    impl QueueSource for MemQueue {
        fn durable_head(&self) -> Result<Option<([u8; 32], u64)>, String> {
            Ok(self.durable)
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
    impl OutcomeSink for MemQueue {
        fn resolve(
            &mut self,
            intent: &SubmitIntent,
            outcome: &DrainOutcome,
            batch: Option<&MirrorBatch>,
        ) -> Result<(), String> {
            if let Some(b) = batch {
                self.mirrored.push(b.clone());
            }
            self.resolved.push((intent.clone(), outcome.clone()));
            Ok(())
        }
    }

    /// A tiny sink that borrows the resolved/mirrored vecs, so the test can keep
    /// the source and sink as separate borrows (the realistic two-object shape:
    /// the live worker's source is `dregg.submit_queue` reads and its sink is the
    /// apply+resolve, distinct SQL).
    struct MemSinkProxy<'a>(
        &'a mut Vec<(SubmitIntent, DrainOutcome)>,
        &'a mut Vec<MirrorBatch>,
    );
    impl OutcomeSink for MemSinkProxy<'_> {
        fn resolve(
            &mut self,
            intent: &SubmitIntent,
            outcome: &DrainOutcome,
            batch: Option<&MirrorBatch>,
        ) -> Result<(), String> {
            if let Some(b) = batch {
                self.1.push(b.clone());
            }
            self.0.push((intent.clone(), outcome.clone()));
            Ok(())
        }
    }

    #[test]
    fn the_worker_loop_drains_in_polls_until_empty() {
        let (_g, issuer) = fresh_issuer();
        let tok = submit_token(&issuer);
        // A queue + a separate sink (the realistic two-object shape).
        let mut source = MemQueue::default();
        for k in 0..10u8 {
            source
                .pending
                .push_back(intent(k, agent(0x20 + (k % 4)), &tok));
        }
        let mut resolved: Vec<(SubmitIntent, DrainOutcome)> = Vec::new();
        let mut mirrored: Vec<MirrorBatch> = Vec::new();
        let mut d = Drainer::new(FoldProducer::new(SOURCE, 1_000, 1)).with_clock(1_000);

        // Poll in batches of 4 until idle (the daemon's loop).
        let mut polls = 0;
        loop {
            let mut sink = MemSinkProxy(&mut resolved, &mut mirrored);
            let report = d.poll_once(&mut source, &mut sink, 4).expect("poll ok");
            polls += 1;
            if !report.did_work() {
                break;
            }
            if polls > 100 {
                panic!("loop did not terminate");
            }
        }

        assert_eq!(resolved.len(), 10, "every intent resolved");
        assert!(resolved.iter().all(|(_, o)| o.is_executed()));
        assert_eq!(mirrored.len(), 10, "every executed turn mirrored a batch");
        assert_eq!(d.counters().drained, 10);
        assert_eq!(d.counters().lag, 0, "queue fully drained ⇒ lag 0");
        assert_eq!(d.next_ordinal(), 10);
        // The mirrored batches form a chain (each prev_root = the prior ledger_root).
        for w in mirrored.windows(2) {
            assert_eq!(
                w[1].turn.prev_root, w[0].turn.ledger_root,
                "mirrored chain links"
            );
        }
    }

    #[test]
    fn the_worker_resumes_the_chain_from_the_durable_head() {
        let (_g, issuer) = fresh_issuer();
        let tok = submit_token(&issuer);
        let mut source = MemQueue::default();
        // The store says it is already at ordinal 7, head H.
        let head = [0x77u8; 32];
        source.durable = Some((head, 7));
        source.pending.push_back(intent(1, agent(0x20), &tok));

        let mut d = Drainer::new(FoldProducer::new(SOURCE, 1_000, 1)).with_clock(1_000);
        d.resume_from(&source).expect("resume ok");
        assert_eq!(d.next_ordinal(), 7, "resumed at the durable ordinal");
        assert_eq!(d.head(), Some(head));

        // The next drained turn chains onto ordinal 7 (prev_root = the durable head).
        let mut resolved = Vec::new();
        let mut mirrored = Vec::new();
        let mut sink = MemSinkProxy(&mut resolved, &mut mirrored);
        let report = d.poll_once(&mut source, &mut sink, 8).expect("poll ok");
        assert_eq!(report.executed, 1);
        assert_eq!(mirrored[0].turn.ordinal, 7);
        assert_eq!(
            mirrored[0].turn.prev_root, head,
            "chains onto the durable head"
        );
        assert_eq!(d.next_ordinal(), 8);
    }

    #[test]
    fn counters_summary_is_stable_and_total_adds_up() {
        let (_g, issuer) = fresh_issuer();
        let tok = submit_token(&issuer);
        let mut d = Drainer::new(FoldProducer::new(SOURCE, 100, 1)).with_clock(1_000);
        d.drain(&intent(1, agent(0x20), &tok)); // executed
        let mut bad = intent(2, agent(0x21), &tok);
        bad.signed_turn = vec![];
        d.drain(&bad); // produce-refused
        d.set_lag(5);

        let c = d.counters();
        assert_eq!(c.drained, 1);
        assert_eq!(c.refused, 1);
        assert_eq!(c.produce_refused, 1);
        assert_eq!(c.resolved(), 2);
        assert_eq!(c.lag, 5);
        assert!(c.summary().contains("drained=1"));
        assert!(c.summary().contains("lag=5"));
    }
}
