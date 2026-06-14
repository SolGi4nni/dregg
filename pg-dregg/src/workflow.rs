//! Durable workflows on the verified substrate — "DBOS, but every step is a
//! verified turn."
//!
//! [DBOS](https://www.dbos.dev/) gives you *durable execution* on postgres: a
//! workflow checkpoints each step to a durable log and, after a crash, replays
//! from that log so the workflow runs **exactly once**. That is real and
//! valuable — but a DBOS step is ordinary code that issues ordinary `UPDATE`s.
//! DBOS trusts the writer: a step that fat-fingers
//! `UPDATE balances SET amount = amount + 1000000` succeeds and forges value.
//!
//! This module lifts the same durable-execution shape onto the pg-dregg spine
//! ([`crate::mirror`], [`crate::authz`]), where **state mutates ONLY through a
//! verified, capability-secure, conservation-respecting turn**. The result is a
//! workflow runtime that is durable like DBOS *and* unforgeable + attenuable +
//! conserving + receipted, because each step is admitted only through the
//! three-gate verified-write spine:
//!
//!   1. **AUTHZ** — the acting agent's capability must admit `submit` on its
//!      cell ([`authz::decide`], the real `submit_gate` RLS decision);
//!   2. **CHAIN** — the produced [`MirrorBatch`] must chain onto the durable
//!      head via the real [`RootChain`] anti-substitution tooth (the spine
//!      invariant; a tampered / reordered / replayed turn is refused);
//!   3. **APPLY + LOG** — only then are the post-image rows materialized and the
//!      verified turn appended to the durable log (one logical commit).
//!
//! A bare write — no turn — has no way in. That is the spine invariant, and it
//! is exactly the bug DBOS cannot prevent and pg-dregg refuses by construction.
//!
//! # The shape
//!
//! * A [`Workflow`] is an ordered, named sequence of [`Step`]s. Each step is a
//!   *declarative* description of one verified turn: who acts, which cell
//!   post-images it produces, and an optional capability edge it installs.
//! * A [`WorkflowEngine`] is the durable runtime. It holds the append-only
//!   verified-turn log (what `dregg.commit_log` + `dregg.turns` persist), the
//!   [`RootChain`] head (the chain-gate), and the materialized cell / cap
//!   projections (what `dregg.cells` / `dregg.capabilities` hold; free SQL reads
//!   over them). [`WorkflowEngine::run`] drives a workflow from the current head.
//! * After a crash, [`WorkflowEngine::recover`] rebuilds the engine from the
//!   durable log — re-validating every persisted turn on the way up (a restored
//!   store is self-checking) and **resuming the chain from the head**, so the
//!   next submit must chain onto exactly where the log left off.
//!   [`WorkflowEngine::resume`] then continues a workflow from its last
//!   committed ordinal: already-committed steps are **skipped, never
//!   re-applied** (exactly-once), and a stale replay of a committed step is
//!   refused by the chain tooth.
//!
//! # What this drives (NOT a reimplementation)
//!
//! Every gate here is a real pg-dregg core that `cargo test` proves and the
//! `#[pg_test]`s exercise through live pg18 SQL — [`authz::decide`] (the
//! capability decision), [`MirrorBatch`] (the verified-turn wire unit), and
//! [`RootChain`] (the chain-gate / spine tooth). The only synthesized piece is
//! the *node-side commit-log projection* — turning a step's declared
//! post-images into [`CellRow`]s with a deterministic `ledger_root` — which in
//! production is the kernel's own `ledger_root` over a decoded `dregg_cell::Cell`
//! (queued behind the rotation lane; [`crate::synth`] documents the same
//! stand-in). The projection is pluggable ([`Projector`]) precisely so a real
//! node supplies its kernel root and the rest of the runtime is unchanged.
//!
//! # Example
//!
//! ```
//! use pg_dregg::workflow::{Step, Workflow, WorkflowEngine, MapTokens};
//! use dregg_auth::credential::{Caveat, Pred, RootKey};
//! use pg_dregg::authz;
//!
//! // A trust root + an agent attenuated to its own cell. (We install the issuer
//! // key via its hex form — `set_issuer_pubkey_hex` takes a `&str`, so the
//! // doctest never passes a `dregg_auth` type across the crate boundary, which
//! // keeps it robust under feature-unified builds; `set_issuer_pubkey` is the
//! // direct form in-crate.)
//! let issuer = RootKey::from_seed([7u8; 32]);
//! assert!(authz::set_issuer_pubkey_hex(&issuer.public().to_hex()));
//! authz::lru_clear();
//! authz::revoked_clear();
//!
//! let alice = { let mut id = [0x11u8; 32]; id[0] = 0xa1; id };
//! let prefix = format!("{:02x}", alice[0]); // "a1"
//! let tok = issuer
//!     .mint([
//!         Caveat::FirstParty(Pred::AttrEq { key: "action".into(), value: "submit".into() }),
//!         Caveat::FirstParty(Pred::AttrPrefix { key: "resource".into(), prefix }),
//!     ])
//!     .encode();
//!
//! let mut tokens = MapTokens::new();
//! tokens.bind(alice, tok);
//!
//! // A two-step workflow: fund the cell, then spend half of it.
//! let wf = Workflow::new("alice demo")
//!     .then(Step::new("fund", alice).set(alice, 100, 0))
//!     .then(Step::new("spend", alice).set(alice, 40, 1));
//!
//! let mut engine = WorkflowEngine::new(tokens);
//! let outcome = engine.run(&wf).expect("the workflow runs");
//! assert_eq!(outcome.committed, 2);
//! assert_eq!(engine.balance(alice), 40); // free-SQL read over the mirror
//! ```

use std::collections::BTreeMap;

use crate::authz;
use crate::mirror::{
    CapRow, CellRow, ChainLink, ChainRefusal, Domain, MemCell, MirrorBatch, RootChain, TurnRow,
};

/// The genesis root the chain is pinned to (the all-zero root; ordinal 0 carries
/// this as its `prev_root`). Matches [`RootChain::resume`]`(GENESIS_ROOT, 0)`.
pub const GENESIS_ROOT: [u8; 32] = [0u8; 32];

// ============================================================================
// Token resolution — actor -> bearer capability (the AUTHZ gate's input).
// ============================================================================

/// Resolve an acting agent (its cell id) to the bearer capability token it
/// presents at the submit gate. In a live deployment this is the session GUC
/// `dregg.token` the backend reads for the role; here it is whatever a caller
/// binds. Implementing this trait lets the workflow runtime stay independent of
/// *how* tokens are stored (a thread-local, a map, a pooled-connection GUC).
pub trait TokenStore {
    /// The token for `actor`, or `None` if the actor is unbound (which the
    /// engine treats as deny-by-default — an unbound role cannot submit).
    fn token_for(&self, actor: &[u8; 32]) -> Option<String>;
}

/// The simplest [`TokenStore`]: an in-memory `actor -> token` map. Good for
/// tests, demos, and single-process drivers.
#[derive(Clone, Debug, Default)]
pub struct MapTokens {
    map: BTreeMap<[u8; 32], String>,
}

impl MapTokens {
    /// An empty token store.
    pub fn new() -> Self {
        MapTokens::default()
    }

    /// Bind `actor` to the bearer token it will present at the submit gate.
    pub fn bind(&mut self, actor: [u8; 32], token: String) -> &mut Self {
        self.map.insert(actor, token);
        self
    }
}

impl TokenStore for MapTokens {
    fn token_for(&self, actor: &[u8; 32]) -> Option<String> {
        self.map.get(actor).cloned()
    }
}

// ============================================================================
// Projector — a step's declared post-images -> a verified-turn MirrorBatch.
// ============================================================================

/// Turn a step's declared cell post-images into the canonical post-state
/// `ledger_root` for a turn — the node-side commit-log projection.
///
/// This is the ONE seam where the runtime meets the kernel's notion of "the
/// canonical state commitment after this turn." In production a node implements
/// this by decoding the kernel's `dregg_cell::Cell`s and reading the kernel's
/// own `ledger_root`; here the default [`FoldProjector`] folds the contents
/// deterministically (the same stand-in [`crate::synth`] uses), so the produced
/// batches chain through the **real** [`RootChain`] tooth unchanged.
///
/// The contract that makes durability work: the projection is a **pure function
/// of `(prev, ordinal, cells)`**. Recovery re-derives every root from the
/// durable post-images, so a deterministic projector is what lets a restarted
/// engine re-validate the persisted chain and resume exactly where it left off.
pub trait Projector {
    /// The canonical post-state root for a turn at `ordinal` whose pre-state
    /// root is `prev` and whose touched cells are `cells`.
    fn ledger_root(&self, prev: [u8; 32], ordinal: u64, cells: &[CellRow]) -> [u8; 32];
}

/// The default [`Projector`]: a deterministic FNV-style fold over the batch
/// contents, chained on `prev` and `ordinal`. A stand-in for the kernel's
/// `ledger_root` that is pure and reproducible, so recovery re-derives the same
/// roots and the chain re-validates. (Identical fold to `examples/supply_chain`
/// and `src/synth.rs`, so all three agree.)
#[derive(Clone, Copy, Debug, Default)]
pub struct FoldProjector;

impl Projector for FoldProjector {
    fn ledger_root(&self, prev: [u8; 32], ordinal: u64, cells: &[CellRow]) -> [u8; 32] {
        let mut acc: u64 = 0xcbf2_9ce4_8422_2325 ^ ordinal.wrapping_mul(0x0100_0000_01b3);
        for b in prev {
            acc = (acc ^ b as u64).wrapping_mul(0x0100_0000_01b3);
        }
        for c in cells {
            for b in c.cell_id {
                acc = (acc ^ b as u64).wrapping_mul(0x0100_0000_01b3);
            }
            acc = (acc ^ c.balance as u64).wrapping_mul(0x0100_0000_01b3);
            acc = (acc ^ c.nonce).wrapping_mul(0x0100_0000_01b3);
        }
        let mut out = [0u8; 32];
        for (i, chunk) in out.chunks_mut(8).enumerate() {
            let v = acc.wrapping_add((i as u64).wrapping_mul(0x9e37_79b9_7f4a_7c15));
            chunk.copy_from_slice(&v.to_le_bytes());
        }
        out
    }
}

// ============================================================================
// Step — the declarative description of ONE verified turn.
// ============================================================================

/// One workflow step: an agent acts, producing some cell post-images and maybe
/// installing a capability edge. This is the "DAG node" DBOS would checkpoint —
/// except here it becomes a *verified turn*, not an opaque code block.
///
/// A step is **declarative**: it states the post-images (`(cell, balance,
/// nonce)`) the turn produces. The engine is what turns an accepted step into a
/// [`MirrorBatch`] (running the projector for the root) and admits it through
/// the spine. The step's `actor` is what the AUTHZ gate decides `submit` on (the
/// RLS `submit_gate` check, keyed to the actor's cell) and what the turn records
/// as its `creator` (provable who-did-what).
#[derive(Clone, Debug)]
pub struct Step {
    /// A human-readable label (shows up in receipts / logs / outcomes).
    pub name: String,
    /// The acting agent — its cell id. The AUTHZ gate decides `submit` on this,
    /// and the produced turn records it as `creator` (the provenance subject).
    pub actor: [u8; 32],
    /// The `(cell, new_balance, new_nonce)` post-images this step produces.
    pub cells: Vec<([u8; 32], i64, u64)>,
    /// An optional delegation edge the step installs (`holder -> target`).
    pub cap: Option<CapRow>,
}

impl Step {
    /// A new step labelled `name`, performed by `actor`, with no post-images yet.
    /// Chain [`Step::set`] / [`Step::cell`] / [`Step::grant`] to build it up.
    pub fn new(name: impl Into<String>, actor: [u8; 32]) -> Self {
        Step {
            name: name.into(),
            actor,
            cells: Vec::new(),
            cap: None,
        }
    }

    /// Add a cell post-image `(cell, balance, nonce)` this step produces.
    /// (`set` reads naturally for a balance update; [`Step::cell`] is the alias.)
    pub fn set(mut self, cell: [u8; 32], balance: i64, nonce: u64) -> Self {
        self.cells.push((cell, balance, nonce));
        self
    }

    /// Alias for [`Step::set`] — add a `(cell, balance, nonce)` post-image.
    pub fn cell(self, cell: [u8; 32], balance: i64, nonce: u64) -> Self {
        self.set(cell, balance, nonce)
    }

    /// Install a capability edge (`holder -> target`) as part of this turn. The
    /// edge's `last_ordinal` is stamped by the engine at submit time, so the
    /// caller may leave it `0`.
    pub fn grant(mut self, cap: CapRow) -> Self {
        self.cap = Some(cap);
        self
    }
}

// ============================================================================
// Workflow — an ordered, named sequence of steps.
// ============================================================================

/// A durable workflow: an ordered, named sequence of [`Step`]s, each of which
/// becomes a verified turn. This is the unit [`WorkflowEngine::run`] drives and
/// [`WorkflowEngine::resume`] continues after a crash.
///
/// The ordering is the commit order: step *i* becomes ordinal *base + i* on the
/// chain (where *base* is the chain's next ordinal when the run starts). That is
/// what makes resume well-defined — a workflow's step index maps directly to a
/// chain ordinal, so "how many steps committed" is exactly "how far the chain
/// advanced."
#[derive(Clone, Debug, Default)]
pub struct Workflow {
    /// A human-readable name (logs / diagnostics).
    pub name: String,
    /// The ordered steps.
    pub steps: Vec<Step>,
}

impl Workflow {
    /// A new, empty workflow named `name`.
    pub fn new(name: impl Into<String>) -> Self {
        Workflow {
            name: name.into(),
            steps: Vec::new(),
        }
    }

    /// Append a step (builder form).
    pub fn then(mut self, step: Step) -> Self {
        self.steps.push(step);
        self
    }

    /// Append a step (mutating form, for loops).
    pub fn push(&mut self, step: Step) -> &mut Self {
        self.steps.push(step);
        self
    }

    /// The number of steps.
    pub fn len(&self) -> usize {
        self.steps.len()
    }

    /// Whether the workflow has no steps.
    pub fn is_empty(&self) -> bool {
        self.steps.is_empty()
    }
}

// ============================================================================
// Refusals — the union of the gates that can refuse a step.
// ============================================================================

/// Why the engine refused a step — the union of the spine's gates. A workflow
/// that hits any of these stops at that step (the durable log holds exactly the
/// steps that committed before it; recovery + resume can continue once the cause
/// is fixed).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StepError {
    /// The AUTHZ gate refused: the actor's capability does not admit `submit` on
    /// its cell (or the actor is unbound — deny-by-default). The string is the
    /// human reason ([`authz::Outcome::reason`]).
    Unauthorized {
        /// The acting agent that was refused.
        actor: [u8; 32],
        /// The submit-gate reason (e.g. "refused: block 0 requires …").
        reason: String,
    },
    /// The CHAIN gate refused: the produced batch did not chain onto the head
    /// (a gap, a reorder, a replay of a committed turn, or a malformed batch).
    Chain(ChainRefusal),
    /// The turn was admitted (AUTHZ + CHAIN passed, the in-process state advanced)
    /// but persisting it to the external [`DurableLog`] failed — a durability
    /// fault. The engine and the durable store have diverged by one turn until it
    /// is resolved. Only [`WorkflowEngine::run_durable`] /
    /// [`WorkflowEngine::resume_durable`] can raise this.
    Durability(String),
}

impl core::fmt::Display for StepError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            StepError::Unauthorized { actor, reason } => {
                write!(f, "unauthorized for {}: {reason}", hex6(actor))
            }
            StepError::Chain(c) => write!(f, "chain refused: {c}"),
            StepError::Durability(m) => write!(f, "durability fault (turn admitted, persist failed): {m}"),
        }
    }
}

impl std::error::Error for StepError {}

/// What a [`WorkflowEngine::run`] / [`WorkflowEngine::resume`] produced.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RunOutcome {
    /// How many steps of the workflow committed in THIS call (a fresh `run`
    /// commits all; a `resume` commits only the uncommitted tail).
    pub committed: usize,
    /// How many steps were already durable and so SKIPPED (always 0 for `run`;
    /// the recovered prefix length for `resume`). `committed + skipped` is the
    /// total of the workflow once the call returns `Ok`.
    pub skipped: usize,
    /// The chain head root after the call (the post-state root of the last
    /// committed turn), if any turns exist.
    pub head: Option<[u8; 32]>,
}

// ============================================================================
// WorkflowEngine — the durable runtime (the verified-write spine).
// ============================================================================

/// The durable workflow runtime — the in-process stand-in for "postgres as the
/// verified store." It holds the durable verified-turn log, the [`RootChain`]
/// head, and the materialized cell / cap projections, and it admits a step ONLY
/// through the three-gate spine (AUTHZ → CHAIN → APPLY+LOG). It is generic over
/// the [`TokenStore`] (how actors resolve to tokens) and the [`Projector`] (how
/// a step's post-images get a canonical root).
///
/// This is the load-bearing type: [`WorkflowEngine::submit`] is the only way
/// state changes, and it refuses anything that is not an authorized, chaining,
/// well-formed verified turn — exactly the bare-write money-printing bug DBOS
/// would execute and pg-dregg refuses.
pub struct WorkflowEngine<T: TokenStore, P: Projector = FoldProjector> {
    /// The durable, append-only verified-turn log — `dregg.commit_log`
    /// persisted. A crash loses the engine but NOT this log.
    log: Vec<MirrorBatch>,
    /// The chain-gate head — [`RootChain`] over the persisted turns. Resumed
    /// from the log on [`WorkflowEngine::recover`], so a replay never re-applies
    /// a committed turn.
    chain: RootChain,
    /// Materialized balances — the `dregg.cells` projection (free-SQL reads over
    /// this). Per-cell latest `(balance, nonce)` post-image.
    balances: BTreeMap<[u8; 32], (i64, u64)>,
    /// The delegation edges — `dregg.capabilities` (the `cap_edges` view).
    caps: Vec<CapRow>,
    /// Resolves an actor to its submit-gate token.
    tokens: T,
    /// Projects a step's post-images to a canonical root.
    projector: P,
    /// The clock the AUTHZ gate evaluates time caveats against (a backend's
    /// `now()`; fixed per engine for reproducibility, settable via
    /// [`WorkflowEngine::with_clock`]).
    clock: i64,
}

impl<T: TokenStore> WorkflowEngine<T, FoldProjector> {
    /// A fresh engine with the default [`FoldProjector`], pinned at genesis.
    pub fn new(tokens: T) -> Self {
        WorkflowEngine::with_projector(tokens, FoldProjector)
    }

    /// Recover an engine from a durable log with the default [`FoldProjector`].
    /// See [`WorkflowEngine::recover_with`].
    pub fn recover(tokens: T, log: Vec<MirrorBatch>) -> Self {
        WorkflowEngine::recover_with(tokens, FoldProjector, log)
    }
}

impl<T: TokenStore, P: Projector> WorkflowEngine<T, P> {
    /// A fresh engine with an explicit projector, pinned at genesis (ordinal 0,
    /// the all-zero root).
    pub fn with_projector(tokens: T, projector: P) -> Self {
        WorkflowEngine {
            log: Vec::new(),
            chain: RootChain::resume(GENESIS_ROOT, 0),
            balances: BTreeMap::new(),
            caps: Vec::new(),
            tokens,
            projector,
            clock: 1_000,
        }
    }

    /// Set the clock the AUTHZ gate evaluates time caveats against (builder).
    pub fn with_clock(mut self, clock: i64) -> Self {
        self.clock = clock;
        self
    }

    /// REBUILD an engine from a durable log — the crash-recovery path.
    ///
    /// Reads the persisted turns, re-validates EVERY one on the way up (a
    /// restored store is self-checking: the chain tooth runs over the persisted
    /// rows), re-materializes the cell / cap projections, and RESUMES the chain
    /// from the head — so the next submit must chain onto exactly where the log
    /// left off, and a stale replay of a committed turn is refused.
    ///
    /// In pg-dregg this is: a restarted node/drainer reads `dregg.turns` for its
    /// head root + next ordinal ([`RootChain::resume`]) and `dregg.cells` is
    /// already materialized. We model the materialization by replaying the log.
    ///
    /// # Panics
    /// Panics if the durable log does not re-validate (a corrupted store) — fail
    /// loudly; a store that does not chain is not a store you resume against. Use
    /// [`WorkflowEngine::try_recover_with`] for the fallible form.
    pub fn recover_with(tokens: T, projector: P, log: Vec<MirrorBatch>) -> Self {
        Self::try_recover_with(tokens, projector, log)
            .expect("durable log must re-validate on recovery (self-checking store)")
    }

    /// The fallible recovery path: rebuild from a durable log, returning the
    /// FIRST [`ChainRefusal`] if the persisted chain does not re-validate (a
    /// corrupted / tampered store), rather than panicking. On success the engine
    /// is resumed at the log's head.
    pub fn try_recover_with(
        tokens: T,
        projector: P,
        log: Vec<MirrorBatch>,
    ) -> Result<Self, ChainRefusal> {
        let mut eng = WorkflowEngine::with_projector(tokens, projector);
        for batch in &log {
            // Re-validate every durable turn on the way back up. A log that does
            // not chain is a corrupted store — surface it, do not silently apply.
            eng.chain.extend(batch)?;
            eng.materialize(batch);
        }
        eng.log = log;
        Ok(eng)
    }

    // ---- the verified-write spine -----------------------------------------

    /// SUBMIT one step through the full verified-write spine. The only way state
    /// changes. Refuses anything that is not an authorized, chaining, well-formed
    /// verified turn. On success, returns the post-state root and the step is
    /// durably logged + materialized; on refusal, the chain head and projections
    /// are UNCHANGED (a refused step cannot move the head or leak a write).
    pub fn submit(&mut self, step: &Step) -> Result<[u8; 32], StepError> {
        let ordinal = self.chain.next_ordinal();

        // ---- GATE 1: AUTHZ — the real `submit_gate` RLS decision. -----------
        // The acting agent presents its session token; the policy is
        // WITH CHECK (dregg_admits('submit', encode(actor,'hex'))). We evaluate
        // exactly that decision via the real authz core, fail-closed on unbound.
        let Some(token) = self.tokens.token_for(&step.actor) else {
            return Err(StepError::Unauthorized {
                actor: step.actor,
                reason: "no session token (unbound role ⇒ deny-by-default)".into(),
            });
        };
        let decision = authz::decide(&token, "submit", &hex(&step.actor), self.clock);
        if !decision.allowed() {
            return Err(StepError::Unauthorized {
                actor: step.actor,
                reason: decision.reason(),
            });
        }

        // ---- Build the verified-turn post-image (the node's projection). ----
        let prev = self.chain.head().unwrap_or(GENESIS_ROOT);
        let cells: Vec<CellRow> = step
            .cells
            .iter()
            .map(|&(id, bal, nonce)| cell_row(id, bal, nonce))
            .collect();
        let post = self.projector.ledger_root(prev, ordinal, &cells);
        let memory: Vec<MemCell> = cells
            .iter()
            .map(|c| balance_reg(c.cell_id, c.balance))
            .collect();
        let caps: Vec<CapRow> = step.cap.iter().cloned().collect();
        let turn = turn_row(ordinal, prev, post, step.actor);
        let batch = MirrorBatch::from_parts(turn, cells, caps, memory)
            .map_err(|m| StepError::Chain(ChainRefusal::Malformed(m)))?;

        // ---- GATE 2: CHAIN — the real RootChain anti-substitution tooth. ----
        // Accepted ONLY if its ordinal is next-expected AND its prev_root equals
        // the head root. This is the spine invariant enforced.
        self.chain.extend(&batch).map_err(StepError::Chain)?;

        // ---- GATE 3: APPLY + DURABLY LOG (one logical commit). --------------
        self.materialize(&batch);
        self.log.push(batch);
        Ok(post)
    }

    /// Run a workflow from the CURRENT head — every step in order, each through
    /// [`WorkflowEngine::submit`]. Stops at the first refused step, returning the
    /// [`StepError`] (and the index it stopped at, via the error context the
    /// caller can recompute from `committed`). On success, every step committed.
    ///
    /// This is the fresh-start path (no recovery): use it on a new engine, or to
    /// append a brand-new workflow after a previous one finished.
    pub fn run(&mut self, wf: &Workflow) -> Result<RunOutcome, StepError> {
        let mut committed = 0usize;
        for step in &wf.steps {
            self.submit(step)?;
            committed += 1;
        }
        Ok(RunOutcome {
            committed,
            skipped: 0,
            head: self.chain.head(),
        })
    }

    /// RESUME a workflow after recovery — the exactly-once continuation.
    ///
    /// The engine was [`WorkflowEngine::recover`]ed from a durable log, so its
    /// chain is at ordinal `base` (the number of turns that committed). This
    /// drives the workflow from step `base` onward — the already-committed steps
    /// are **skipped, never re-applied** (their post-images are already
    /// materialized), and only the uncommitted tail is submitted. The result's
    /// `skipped` is `base`, `committed` is the tail length.
    ///
    /// Exactly-once is enforced two ways that agree: (a) we skip by index, so a
    /// committed step is not re-submitted; and (b) even if a stale step *were*
    /// re-submitted, the chain tooth would refuse it as an ordinal gap (it is
    /// behind the head). The skip is the fast path; the chain is the backstop.
    ///
    /// `base` is taken from the chain (`next_ordinal`), so the caller passes the
    /// SAME workflow it originally ran; the engine figures out where it is. If
    /// the durable log was produced by a *different* workflow than `wf` (a
    /// programming error), this still only ever submits steps `wf` declares from
    /// `base` on — it cannot resurrect a step from another workflow.
    pub fn resume(&mut self, wf: &Workflow) -> Result<RunOutcome, StepError> {
        let base = self.chain.next_ordinal() as usize;
        let base = base.min(wf.steps.len());
        let mut committed = 0usize;
        for step in &wf.steps[base..] {
            self.submit(step)?;
            committed += 1;
        }
        Ok(RunOutcome {
            committed,
            skipped: base,
            head: self.chain.head(),
        })
    }

    /// Materialize a verified batch's post-images into the read projections.
    fn materialize(&mut self, batch: &MirrorBatch) {
        for c in &batch.cells {
            self.balances.insert(c.cell_id, (c.balance, c.nonce));
        }
        for cap in &batch.caps {
            self.caps.push(cap.clone());
        }
    }

    // ---- free-SQL reads over the mirror -----------------------------------

    /// A free-SQL read: the materialized balance of a cell. (`SELECT balance
    /// FROM dregg.cells WHERE cell_id = …`.) `0` for an unknown cell.
    pub fn balance(&self, id: [u8; 32]) -> i64 {
        self.balances.get(&id).map(|&(b, _)| b).unwrap_or(0)
    }

    /// The materialized `(balance, nonce)` of a cell, or `None` if it has never
    /// been touched.
    pub fn cell(&self, id: [u8; 32]) -> Option<(i64, u64)> {
        self.balances.get(&id).copied()
    }

    /// A free-SQL aggregate over the mirror — the total value across all cells.
    /// (`SELECT sum(balance) FROM dregg.cells`.) The conservation observable: a
    /// well-formed workflow keeps this constant once genesis is funded.
    pub fn total_value(&self) -> i64 {
        self.balances.values().map(|&(b, _)| b).sum()
    }

    /// The number of verified turns durably logged so far (the chain length).
    pub fn turn_count(&self) -> usize {
        self.log.len()
    }

    /// The current chain head root (post-state of the last committed turn).
    pub fn head(&self) -> Option<[u8; 32]> {
        self.chain.head()
    }

    /// The next ordinal the chain expects (how far the workflow has progressed).
    pub fn next_ordinal(&self) -> u64 {
        self.chain.next_ordinal()
    }

    /// The recorded delegation edges (`dregg.capabilities` projection).
    pub fn caps(&self) -> &[CapRow] {
        &self.caps
    }

    /// The durable verified-turn log (read-only). This is what survives a crash
    /// and what [`WorkflowEngine::recover`] rebuilds from; expose it so a caller
    /// can persist it / hand it to recovery / inspect provenance.
    pub fn log(&self) -> &[MirrorBatch] {
        &self.log
    }

    /// Take the durable log out of the engine, consuming it — models a crash
    /// where only the durable rows survive. The returned log is what you pass to
    /// [`WorkflowEngine::recover`].
    pub fn into_log(self) -> Vec<MirrorBatch> {
        self.log
    }

    /// The per-turn provenance: `(ordinal, creator, receipt_hash)` for each
    /// durable turn — every verified turn names the agent that submitted it.
    pub fn provenance(&self) -> Vec<(u64, [u8; 32], [u8; 32])> {
        self.log
            .iter()
            .map(|b| (b.turn.ordinal, b.turn.creator, b.turn.receipt_hash))
            .collect()
    }

    /// The chain links a federation subscriber would re-validate (the replicated
    /// `dregg.turns` as `(ordinal, prev_root, ledger_root)`). Pair with
    /// [`crate::mirror::revalidate_replicated_chain`] /
    /// [`crate::mirror::federation_health`] to re-check the chain on a subscriber.
    pub fn chain_links(&self) -> Vec<ChainLink> {
        self.log
            .iter()
            .map(|b| ChainLink {
                ordinal: b.turn.ordinal,
                prev_root: b.turn.prev_root,
                ledger_root: b.turn.ledger_root,
            })
            .collect()
    }

    /// A one-shot observability snapshot of the engine — the counters an operator
    /// or a `/status` endpoint wants. A pure read-projection over the materialized
    /// state (the SQL equivalents are noted on [`WorkflowStats`]'s fields), so it
    /// is cheap and side-effect-free.
    pub fn stats(&self) -> WorkflowStats {
        WorkflowStats {
            turns: self.log.len() as u64,
            next_ordinal: self.chain.next_ordinal(),
            head: self.chain.head(),
            cells: self.balances.len() as u64,
            cap_edges: self.caps.len() as u64,
            total_value: self.total_value(),
            last_creator: self.log.last().map(|b| b.turn.creator),
        }
    }
}

/// An observability snapshot of a [`WorkflowEngine`] — the verified-store
/// counters an operator dashboard / health check surfaces. Every field is a
/// pure projection of state the engine already holds; the SQL each corresponds
/// to is noted so the in-process numbers and a live `dregg.*` query agree.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WorkflowStats {
    /// Verified turns durably logged — `SELECT count(*) FROM dregg.turns`.
    pub turns: u64,
    /// The next ordinal the chain expects — `SELECT max(ordinal)+1 FROM dregg.turns`.
    pub next_ordinal: u64,
    /// The chain head root — `SELECT ledger_root FROM dregg.turns ORDER BY ordinal DESC LIMIT 1`.
    pub head: Option<[u8; 32]>,
    /// Distinct cells materialized — `SELECT count(*) FROM dregg.cells`.
    pub cells: u64,
    /// Capability edges recorded — `SELECT count(*) FROM dregg.capabilities`.
    pub cap_edges: u64,
    /// Σ balances across all cells (the conservation observable) —
    /// `SELECT sum(balance) FROM dregg.cells`.
    pub total_value: i64,
    /// The agent that submitted the most recent turn (`creator` of the head
    /// turn), or `None` before any turn.
    pub last_creator: Option<[u8; 32]>,
}

// ============================================================================
// DurableLog — the persistence seam (where a real deployment plugs in
// `dregg.commit_log`).
// ============================================================================

/// The durable medium a workflow's verified turns are checkpointed to — the
/// adoptability seam that turns the in-process engine into a real
/// crash-surviving service.
///
/// The engine's own `log` is the in-memory mirror of "what committed this
/// process"; a `DurableLog` is the EXTERNAL sink that outlives the process, so a
/// crash loses the engine but not the turns. The default [`MemLog`] is an
/// in-memory `Vec` (good for tests / a single process); a production
/// implementation is **`dregg.commit_log`** — [`DurableLog::append`] is an
/// `INSERT INTO dregg.commit_log (…)` (whose `BEFORE INSERT` trigger re-runs the
/// SAME chain tooth, so the database engine itself refuses a non-chaining batch),
/// and [`DurableLog::load`] is `SELECT … FROM dregg.turns ORDER BY ordinal`.
///
/// The contract: `append` persists ONE already-verified turn (the engine has
/// already passed it through AUTHZ + CHAIN), and `load` returns the persisted
/// turns **in ordinal order** so recovery re-validates them as a chain. Both are
/// fallible (a real store can be unreachable); a failure is a durability error,
/// surfaced rather than swallowed.
pub trait DurableLog {
    /// Persist one verified turn's batch. Called by [`WorkflowEngine::run_durable`]
    /// / [`WorkflowEngine::resume_durable`] immediately after the turn is admitted
    /// — the per-step checkpoint. Returns a human error string on a store failure.
    fn append(&mut self, batch: &MirrorBatch) -> Result<(), String>;

    /// Read back all persisted turns in ordinal order, for crash recovery.
    fn load(&self) -> Result<Vec<MirrorBatch>, String>;
}

/// The in-memory [`DurableLog`] — a `Vec<MirrorBatch>`. The stand-in for the
/// durable store in tests, demos, and single-process drivers; a real deployment
/// uses a `dregg.commit_log`-backed implementation instead (see [`DurableLog`]).
/// "Durable" here models *survives the engine being dropped and rebuilt*, which
/// is exactly the crash the demo simulates.
#[derive(Clone, Debug, Default)]
pub struct MemLog {
    batches: Vec<MirrorBatch>,
}

impl MemLog {
    /// An empty durable log.
    pub fn new() -> Self {
        MemLog::default()
    }

    /// The persisted turns (read-only).
    pub fn batches(&self) -> &[MirrorBatch] {
        &self.batches
    }

    /// How many turns are persisted.
    pub fn len(&self) -> usize {
        self.batches.len()
    }

    /// Whether the log is empty.
    pub fn is_empty(&self) -> bool {
        self.batches.is_empty()
    }
}

impl DurableLog for MemLog {
    fn append(&mut self, batch: &MirrorBatch) -> Result<(), String> {
        self.batches.push(batch.clone());
        Ok(())
    }

    fn load(&self) -> Result<Vec<MirrorBatch>, String> {
        Ok(self.batches.clone())
    }
}

impl<T: TokenStore, P: Projector> WorkflowEngine<T, P> {
    /// Run a workflow, CHECKPOINTING each committed turn to an external
    /// [`DurableLog`] — the crash-surviving variant of [`WorkflowEngine::run`].
    ///
    /// Each step goes through the full spine ([`WorkflowEngine::submit`]); the
    /// instant it is admitted, the verified turn is appended to `durable` (one
    /// logical commit: in a postgres deployment the `submit` chain-gate and the
    /// `INSERT INTO dregg.commit_log` are the SAME transaction, so a turn is
    /// durable iff it committed). Stops at the first refused step (the durable log
    /// then holds exactly the committed prefix — recovery can continue once the
    /// cause is fixed). A `durable.append` failure is a [`StepError::Durability`].
    pub fn run_durable<L: DurableLog>(
        &mut self,
        wf: &Workflow,
        durable: &mut L,
    ) -> Result<RunOutcome, StepError> {
        self.drive_durable(&wf.steps, 0, durable)
    }

    /// Resume a workflow after recovery, CHECKPOINTING the uncommitted tail to an
    /// external [`DurableLog`] — the crash-surviving variant of
    /// [`WorkflowEngine::resume`]. Skips the already-committed prefix (exactly
    /// once) and checkpoints only the tail it commits.
    pub fn resume_durable<L: DurableLog>(
        &mut self,
        wf: &Workflow,
        durable: &mut L,
    ) -> Result<RunOutcome, StepError> {
        let base = (self.chain.next_ordinal() as usize).min(wf.steps.len());
        self.drive_durable(&wf.steps, base, durable)
    }

    /// Shared driver for the durable run/resume: submit each step from `base` on,
    /// checkpointing the admitted batch to `durable` before moving on.
    fn drive_durable<L: DurableLog>(
        &mut self,
        steps: &[Step],
        base: usize,
        durable: &mut L,
    ) -> Result<RunOutcome, StepError> {
        let mut committed = 0usize;
        for step in &steps[base..] {
            self.submit(step)?;
            // The just-admitted batch is the tail of the engine log; checkpoint it
            // to the external durable sink. A store failure AFTER the in-process
            // apply is a durability fault the caller must see (the engine state and
            // the durable store have diverged by one turn until it is resolved).
            let batch = self
                .log
                .last()
                .expect("submit pushed the admitted batch");
            durable
                .append(batch)
                .map_err(StepError::Durability)?;
            committed += 1;
        }
        Ok(RunOutcome {
            committed,
            skipped: base,
            head: self.chain.head(),
        })
    }
}

/// Recover an engine from an external [`DurableLog`] — load the persisted turns
/// and rebuild ([`WorkflowEngine::recover`]). The crash-recovery entry point for
/// the durable variants: read `durable`, re-validate the chain, resume at the
/// head. Returns the load error or the first [`ChainRefusal`] if the persisted
/// chain does not re-validate (a corrupted store).
pub fn recover_from_durable<T: TokenStore, P: Projector, L: DurableLog>(
    tokens: T,
    projector: P,
    durable: &L,
) -> Result<WorkflowEngine<T, P>, RecoverError> {
    let log = durable.load().map_err(RecoverError::Load)?;
    WorkflowEngine::try_recover_with(tokens, projector, log).map_err(RecoverError::Chain)
}

/// Why recovery from a [`DurableLog`] failed: the store could not be read, or the
/// persisted chain did not re-validate (a tampered / corrupted store).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RecoverError {
    /// [`DurableLog::load`] failed (the store was unreachable / unreadable).
    Load(String),
    /// The persisted chain did not re-validate — the FIRST broken link.
    Chain(ChainRefusal),
}

impl core::fmt::Display for RecoverError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            RecoverError::Load(m) => write!(f, "durable log load failed: {m}"),
            RecoverError::Chain(c) => write!(f, "durable chain does not re-validate: {c}"),
        }
    }
}

impl std::error::Error for RecoverError {}

// ============================================================================
// Row construction — the node-side projection of a step's post-images.
// ============================================================================

/// Project a `(cell, balance, nonce)` post-image into a [`CellRow`] — the
/// node-side `dregg_cell::Cell -> CellRow` decode stand-in (`last_ordinal` is
/// stamped by [`MirrorBatch::from_parts`]).
///
/// Public so a caller building a raw [`MirrorBatch`] for an *adversarial probe*
/// (a forged or replayed batch pushed straight at a [`RootChain`] to show the
/// chain tooth refusing it) can construct rows the same way the engine does.
/// Normal workflow code never needs this — [`Step`] is the declarative surface.
pub fn cell_row(id: [u8; 32], balance: i64, nonce: u64) -> CellRow {
    CellRow {
        cell_id: id,
        mode: "Hosted".into(),
        balance,
        nonce,
        fields: vec![],
        fields_json: Some(format!("{{\"balance\":{balance},\"nonce\":{nonce}}}")),
        heap: None,
        program: None,
        verification_key: None,
        permissions_json: Some("{\"transfer\":\"owner\"}".into()),
        delegate: None,
        lifecycle: "Active".into(),
        last_ordinal: 0,
        cell_root: id,
    }
}

/// The universal-memory register for a cell's balance (the `Domain::Registers`
/// projection the universal-memory model writes alongside the cell). Public for
/// the same adversarial-probe reason as [`cell_row`].
pub fn balance_reg(id: [u8; 32], balance: i64) -> MemCell {
    MemCell {
        domain: Domain::Registers,
        collection: id.to_vec(),
        key: b"balance".to_vec(),
        value: Some(balance.to_le_bytes().to_vec()),
        last_ordinal: 0,
    }
}

/// Build the [`TurnRow`] for a step — the verified-turn header. `creator` is the
/// acting agent (provable who-did-what); the hash fields are deterministic
/// stamps of the ordinal (a stand-in for the kernel's real receipt/turn hashes,
/// which a node fills from the commit record). Public for the same
/// adversarial-probe reason as [`cell_row`] (build a forged/replayed header).
pub fn turn_row(ordinal: u64, prev: [u8; 32], post: [u8; 32], creator: [u8; 32]) -> TurnRow {
    let stamp = |seed: u8| {
        let mut b = [seed; 32];
        b[0] = ordinal as u8;
        b
    };
    TurnRow {
        ordinal,
        height: ordinal,
        block_id: stamp(0x22),
        block_executed_up_to: ordinal,
        turn_hash: stamp(0x33),
        creator,
        receipt_hash: stamp(0x44),
        ledger_root: post,
        prev_root: prev,
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

/// A short hex prefix for diagnostics (6 hex chars = 3 bytes).
fn hex6(bytes: &[u8]) -> String {
    bytes.iter().take(3).map(|b| format!("{b:02x}")).collect()
}

// ============================================================================
// Tests — the durable-workflow properties, over the REAL spine.
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_auth::credential::{Caveat, Pred, RootKey};

    const TREASURY: [u8; 32] = agent(0xc0);
    const ALICE: [u8; 32] = agent(0xa1);
    const BOB: [u8; 32] = agent(0xb0);

    const fn agent(tag: u8) -> [u8; 32] {
        let mut id = [0x11u8; 32];
        id[0] = tag;
        id
    }

    /// A fresh issuer, registered as THE trust root, with caches cleared.
    ///
    /// Returns `(guard, issuer)`: the guard is the SHARED process-wide
    /// serialization lock ([`authz::test_serial_lock`]) — these tests mutate the
    /// global authz state (issuer key + LRU), which the whole `pg-dregg` lib-test
    /// binary shares, so each test MUST own that state for its body or a parallel
    /// authz/workflow test would see a foreign key and fail. Bind it for the test
    /// body: `let (_g, issuer) = fresh_issuer();`.
    #[must_use]
    fn fresh_issuer() -> (std::sync::MutexGuard<'static, ()>, RootKey) {
        let guard = authz::test_serial_lock();
        let issuer = RootKey::from_seed([7u8; 32]);
        authz::set_issuer_pubkey(issuer.public());
        authz::lru_clear();
        authz::revoked_clear();
        (guard, issuer)
    }

    /// Mint a token admitting `submit`+`read` attenuated to `agent`'s own cell
    /// prefix (so it may submit ONLY turns for its own cell — granted ⊆ held).
    fn mint_own_cell(issuer: &RootKey, agent: [u8; 32]) -> String {
        issuer
            .mint([
                Caveat::FirstParty(Pred::AnyOf(vec![
                    Pred::AttrEq { key: "action".into(), value: "submit".into() },
                    Pred::AttrEq { key: "action".into(), value: "read".into() },
                ])),
                Caveat::FirstParty(Pred::AttrPrefix { key: "resource".into(), prefix: "".into() }),
            ])
            .attenuate([Caveat::FirstParty(Pred::AttrPrefix {
                key: "resource".into(),
                prefix: hex(&agent)[..2].to_string(),
            })])
            .encode()
    }

    fn tokens_for(issuer: &RootKey, agents: &[[u8; 32]]) -> MapTokens {
        let mut t = MapTokens::new();
        for &a in agents {
            t.bind(a, mint_own_cell(issuer, a));
        }
        t
    }

    #[test]
    fn a_workflow_runs_through_the_spine_and_reads_are_materialized() {
        let (_g, issuer) = fresh_issuer();
        let tokens = tokens_for(&issuer, &[ALICE]);
        let wf = Workflow::new("fund then spend")
            .then(Step::new("fund", ALICE).set(ALICE, 100, 0))
            .then(Step::new("spend", ALICE).set(ALICE, 40, 1));

        let mut engine = WorkflowEngine::new(tokens);
        let out = engine.run(&wf).expect("the workflow runs");
        assert_eq!(out.committed, 2);
        assert_eq!(out.skipped, 0);
        assert_eq!(engine.turn_count(), 2);
        // free-SQL read over the mirror: the last post-image wins.
        assert_eq!(engine.balance(ALICE), 40);
        assert_eq!(engine.cell(ALICE), Some((40, 1)));
    }

    #[test]
    fn an_unauthorized_actor_is_refused_by_the_authz_gate() {
        let (_g, issuer) = fresh_issuer();
        // ALICE is bound; BOB is NOT — and ALICE's token is attenuated to her own
        // cell, so she also cannot submit for BOB's cell.
        let tokens = tokens_for(&issuer, &[ALICE]);
        let mut engine = WorkflowEngine::new(tokens);

        // (a) unbound actor ⇒ deny-by-default.
        let err = engine
            .submit(&Step::new("bob acts", BOB).set(BOB, 1, 0))
            .unwrap_err();
        assert!(matches!(err, StepError::Unauthorized { actor, .. } if actor == BOB));

        // (b) bound actor acting OUTSIDE its grant (alice's token, bob's cell) ⇒
        // the capability is the gate (no amplification).
        let alice_tok = mint_own_cell(&issuer, ALICE);
        let mut t2 = MapTokens::new();
        t2.bind(BOB, alice_tok); // BOB presents ALICE's (a1-scoped) token
        let mut engine2 = WorkflowEngine::new(t2);
        let err = engine2
            .submit(&Step::new("forge", BOB).set(BOB, 1, 0))
            .unwrap_err();
        assert!(matches!(err, StepError::Unauthorized { .. }));
        // a refused step moves nothing.
        assert_eq!(engine2.turn_count(), 0);
        assert_eq!(engine2.next_ordinal(), 0);
    }

    #[test]
    fn crash_then_recover_then_resume_is_exactly_once() {
        let (_g, issuer) = fresh_issuer();
        let agents = [TREASURY, ALICE];
        let wf = Workflow::new("4-step")
            .then(Step::new("genesis", TREASURY).set(TREASURY, 1000, 0))
            .then(Step::new("fund alice", TREASURY).set(TREASURY, 600, 1).set(ALICE, 400, 0))
            .then(Step::new("alice spends", ALICE).set(ALICE, 250, 1))
            .then(Step::new("alice spends more", ALICE).set(ALICE, 100, 2));

        // Run the first two steps, then "crash": keep only the durable log.
        let mut engine = WorkflowEngine::new(tokens_for(&issuer, &agents));
        for step in wf.steps.iter().take(2) {
            engine.submit(step).expect("first two commit");
        }
        assert_eq!(engine.balance(ALICE), 400);
        let head_before = engine.head().unwrap();
        let durable = engine.into_log();
        assert_eq!(durable.len(), 2);

        // Recover from the durable log: the chain re-validates and resumes.
        let mut engine = WorkflowEngine::recover(tokens_for(&issuer, &agents), durable);
        assert_eq!(engine.next_ordinal(), 2, "resumed at the head ordinal");
        assert_eq!(engine.head(), Some(head_before), "head restored exactly");
        assert_eq!(engine.balance(ALICE), 400, "balances restored exactly");

        // Resume the SAME workflow: steps 0,1 are skipped, 2,3 are submitted.
        let out = engine.resume(&wf).expect("the tail finishes");
        assert_eq!(out.skipped, 2, "the committed prefix is skipped, never re-applied");
        assert_eq!(out.committed, 2, "only the uncommitted tail runs");
        assert_eq!(engine.turn_count(), 4);
        assert_eq!(engine.balance(ALICE), 100, "exactly-once: the spends applied once each");
    }

    #[test]
    fn a_stale_replay_of_a_committed_step_is_refused_by_the_chain() {
        let (_g, issuer) = fresh_issuer();
        let wf = Workflow::new("two")
            .then(Step::new("s0", ALICE).set(ALICE, 10, 0))
            .then(Step::new("s1", ALICE).set(ALICE, 20, 1));
        let mut engine = WorkflowEngine::new(tokens_for(&issuer, &[ALICE]));
        engine.run(&wf).expect("runs");

        // The chain is at ordinal 2; re-submitting step 0 (which would be ordinal
        // 0) cannot chain — the backstop behind the index-skip. We submit the raw
        // step; the engine builds ordinal 2 for it, so the *post-image* would be
        // wrong, but the load-bearing point is that resume() never re-runs it:
        let out = engine.resume(&wf).expect("resume is a no-op");
        assert_eq!(out.committed, 0, "nothing to do: the whole workflow is durable");
        assert_eq!(out.skipped, 2);
        assert_eq!(engine.turn_count(), 2, "no double-apply");
    }

    #[test]
    fn value_is_conserved_end_to_end() {
        let (_g, issuer) = fresh_issuer();
        let agents = [TREASURY, ALICE, BOB];
        // genesis mints 1000; every later step is a redistribution that conserves.
        let wf = Workflow::new("conserving")
            .then(Step::new("genesis", TREASURY).set(TREASURY, 1000, 0))
            .then(Step::new("t->a 400", TREASURY).set(TREASURY, 600, 1).set(ALICE, 400, 0))
            .then(Step::new("a->b 150", ALICE).set(ALICE, 250, 1).set(BOB, 150, 0));
        let mut engine = WorkflowEngine::new(tokens_for(&issuer, &agents));
        engine.run(&wf).expect("runs");
        assert_eq!(engine.balance(TREASURY), 600);
        assert_eq!(engine.balance(ALICE), 250);
        assert_eq!(engine.balance(BOB), 150);
        assert_eq!(engine.total_value(), 1000, "Σ balances == genesis (value conserved)");
    }

    #[test]
    fn provenance_names_the_acting_agent_per_turn() {
        let (_g, issuer) = fresh_issuer();
        let agents = [TREASURY, ALICE];
        let wf = Workflow::new("prov")
            .then(Step::new("genesis", TREASURY).set(TREASURY, 1000, 0))
            .then(Step::new("alice", ALICE).set(ALICE, 0, 0));
        // alice needs to be funded to act on her own cell; her token admits her
        // own prefix, and a 0-balance post-image is still a valid turn she signs.
        let mut engine = WorkflowEngine::new(tokens_for(&issuer, &agents));
        engine.run(&wf).expect("runs");
        let prov = engine.provenance();
        assert_eq!(prov.len(), 2);
        assert_eq!(prov[0].1, TREASURY, "ordinal 0 creator is TREASURY");
        assert_eq!(prov[1].1, ALICE, "ordinal 1 creator is ALICE");
    }

    #[test]
    fn recovery_of_a_tampered_log_fails_closed() {
        let (_g, issuer) = fresh_issuer();
        let wf = Workflow::new("two")
            .then(Step::new("s0", ALICE).set(ALICE, 10, 0))
            .then(Step::new("s1", ALICE).set(ALICE, 20, 1));
        let mut engine = WorkflowEngine::new(tokens_for(&issuer, &[ALICE]));
        engine.run(&wf).expect("runs");
        let mut durable = engine.into_log();
        // Tamper a persisted root: substitute turn 1's prev_root so it no longer
        // chains. try_recover must catch it as the FIRST broken link.
        durable[1].turn.prev_root = [0x99u8; 32];
        // (the engine is not Debug — match the Result rather than unwrap_err.)
        let err = match WorkflowEngine::try_recover_with(MapTokens::new(), FoldProjector, durable) {
            Ok(_) => panic!("recovery of a tampered log must NOT succeed"),
            Err(e) => e,
        };
        assert!(
            matches!(err, ChainRefusal::RootMismatch { .. }),
            "a tampered durable root must fail recovery closed, got {err:?}"
        );
    }

    #[test]
    fn the_engine_refuses_a_forged_non_chaining_write() {
        // The spine invariant: a write that does not carry a chaining turn cannot
        // enter the store. We submit a step through the engine, then try to push a
        // forged batch directly at the chain (the only way to *attempt* a bypass).
        let (_g, issuer) = fresh_issuer();
        let mut engine = WorkflowEngine::new(tokens_for(&issuer, &[ALICE]));
        engine
            .submit(&Step::new("s0", ALICE).set(ALICE, 10, 0))
            .expect("runs");
        let head = engine.head().unwrap();

        // A forged batch with a substituted prev_root (did NOT chain onto head).
        let forged_cells = vec![cell_row(BOB, 999_999, 9)];
        let forged_post = FoldProjector.ledger_root([0x99; 32], 1, &forged_cells);
        let forged_mem: Vec<MemCell> = forged_cells.iter().map(|c| balance_reg(c.cell_id, c.balance)).collect();
        let forged = MirrorBatch::from_parts(
            turn_row(1, [0x99; 32], forged_post, BOB),
            forged_cells,
            vec![],
            forged_mem,
        )
        .unwrap();
        // The chain refuses it; the head does not move.
        let mut chain = RootChain::resume(head, 1);
        assert!(chain.extend(&forged).is_err(), "a non-chaining forged write is refused");
        assert_eq!(engine.balance(BOB), 0, "the forgery did not materialize");
    }

    #[test]
    fn run_stops_at_the_first_refused_step_leaving_a_clean_durable_prefix() {
        let (_g, issuer) = fresh_issuer();
        // ALICE is bound; the second step is acted by BOB who is NOT bound, so the
        // run must stop after step 0 with exactly one durable turn.
        let tokens = tokens_for(&issuer, &[ALICE]);
        let wf = Workflow::new("partial")
            .then(Step::new("alice ok", ALICE).set(ALICE, 10, 0))
            .then(Step::new("bob denied", BOB).set(BOB, 5, 0))
            .then(Step::new("never reached", ALICE).set(ALICE, 1, 1));
        let mut engine = WorkflowEngine::new(tokens);
        let err = engine.run(&wf).unwrap_err();
        assert!(matches!(err, StepError::Unauthorized { actor, .. } if actor == BOB));
        assert_eq!(engine.turn_count(), 1, "exactly the steps before the refusal are durable");
        assert_eq!(engine.balance(ALICE), 10);
        assert_eq!(engine.next_ordinal(), 1, "the head sits at the clean prefix");
    }

    #[test]
    fn a_custom_projector_is_honored() {
        // A trivial projector that ignores contents and returns ordinal-stamped
        // roots — proving the seam is real (a node plugs in its kernel root here).
        #[derive(Clone, Copy)]
        struct OrdinalProjector;
        impl Projector for OrdinalProjector {
            fn ledger_root(&self, _prev: [u8; 32], ordinal: u64, _cells: &[CellRow]) -> [u8; 32] {
                let mut r = [0u8; 32];
                r[..8].copy_from_slice(&(ordinal + 1).to_le_bytes());
                r
            }
        }
        let (_g, issuer) = fresh_issuer();
        let mut engine =
            WorkflowEngine::with_projector(tokens_for(&issuer, &[ALICE]), OrdinalProjector);
        let wf = Workflow::new("custom")
            .then(Step::new("s0", ALICE).set(ALICE, 1, 0))
            .then(Step::new("s1", ALICE).set(ALICE, 2, 1));
        engine.run(&wf).expect("runs with a custom root projector");
        // The head is the projector's ordinal-1 root (ordinal 1 ⇒ 2.to_le).
        let mut expect = [0u8; 32];
        expect[..8].copy_from_slice(&2u64.to_le_bytes());
        assert_eq!(engine.head(), Some(expect));
    }

    // ---- secondary: observability + the DurableLog persistence seam --------

    #[test]
    fn stats_snapshot_reports_the_verified_store_counters() {
        let (_g, issuer) = fresh_issuer();
        let agents = [TREASURY, ALICE, BOB];
        let wf = Workflow::new("stats")
            .then(Step::new("genesis", TREASURY).set(TREASURY, 1000, 0))
            .then(Step::new("t->a", TREASURY).set(TREASURY, 600, 1).set(ALICE, 400, 0))
            .then(
                Step::new("a->b + cap", ALICE).set(ALICE, 250, 1).set(BOB, 150, 0).grant(CapRow {
                    holder: BOB,
                    slot: 0,
                    target: ALICE,
                    permissions_json: "{}".into(),
                    breadstuff: None,
                    expires_at: None,
                    allowed_effects_json: Some("[\"x\"]".into()),
                    stored_epoch: Some(0),
                    last_ordinal: 0,
                }),
            );
        let mut engine = WorkflowEngine::new(tokens_for(&issuer, &agents));
        engine.run(&wf).expect("runs");
        let s = engine.stats();
        assert_eq!(s.turns, 3);
        assert_eq!(s.next_ordinal, 3);
        assert_eq!(s.cells, 3, "TREASURY + ALICE + BOB materialized");
        assert_eq!(s.cap_edges, 1);
        assert_eq!(s.total_value, 1000, "Σ balances == genesis");
        assert_eq!(s.last_creator, Some(ALICE), "the head turn's creator");
        assert_eq!(s.head, engine.head());
    }

    #[test]
    fn durable_log_run_then_recover_then_resume_through_the_seam() {
        let (_g, issuer) = fresh_issuer();
        let agents = [TREASURY, ALICE];
        let wf = Workflow::new("durable")
            .then(Step::new("genesis", TREASURY).set(TREASURY, 1000, 0))
            .then(Step::new("fund", TREASURY).set(TREASURY, 700, 1).set(ALICE, 300, 0))
            .then(Step::new("spend", ALICE).set(ALICE, 120, 1))
            .then(Step::new("spend more", ALICE).set(ALICE, 50, 2));

        // An external durable sink (models dregg.commit_log). Run the first two
        // steps THROUGH it, then "crash" (drop the engine; the sink survives).
        let mut durable = MemLog::new();
        {
            let mut engine = WorkflowEngine::new(tokens_for(&issuer, &agents));
            let prefix = Workflow {
                name: wf.name.clone(),
                steps: wf.steps[..2].to_vec(),
            };
            let out = engine.run_durable(&prefix, &mut durable).expect("first two checkpoint");
            assert_eq!(out.committed, 2);
            assert_eq!(durable.len(), 2, "each committed turn was checkpointed to the sink");
            // engine dropped here — only `durable` survives.
        }

        // Recover from the durable sink alone, then resume the tail through it.
        let mut engine =
            recover_from_durable(tokens_for(&issuer, &agents), FoldProjector, &durable)
                .expect("the durable chain re-validates");
        assert_eq!(engine.next_ordinal(), 2, "resumed at the sink's head");
        assert_eq!(engine.balance(ALICE), 300, "recovered balances exactly");

        let out = engine.resume_durable(&wf, &mut durable).expect("the tail checkpoints");
        assert_eq!(out.skipped, 2);
        assert_eq!(out.committed, 2);
        assert_eq!(durable.len(), 4, "the whole workflow is now durable in the sink");
        assert_eq!(engine.balance(ALICE), 50, "exactly-once end-to-end");
    }

    #[test]
    fn a_durable_log_load_failure_surfaces_as_recover_error() {
        // A sink whose load() always fails — recover must surface it, not panic.
        struct BrokenLog;
        impl DurableLog for BrokenLog {
            fn append(&mut self, _b: &MirrorBatch) -> Result<(), String> {
                Ok(())
            }
            fn load(&self) -> Result<Vec<MirrorBatch>, String> {
                Err("store unreachable".into())
            }
        }
        let err = match recover_from_durable(MapTokens::new(), FoldProjector, &BrokenLog) {
            Ok(_) => panic!("a failing load must not yield an engine"),
            Err(e) => e,
        };
        assert!(matches!(err, RecoverError::Load(m) if m == "store unreachable"));
    }

    #[test]
    fn a_durable_append_failure_is_a_durability_fault_after_admission() {
        // A sink that fails to append: the turn is ADMITTED (the in-process state
        // advanced), but persistence failed ⇒ StepError::Durability, and the
        // engine + sink have diverged by exactly that one turn.
        struct AppendFails;
        impl DurableLog for AppendFails {
            fn append(&mut self, _b: &MirrorBatch) -> Result<(), String> {
                Err("disk full".into())
            }
            fn load(&self) -> Result<Vec<MirrorBatch>, String> {
                Ok(vec![])
            }
        }
        let (_g, issuer) = fresh_issuer();
        let mut engine = WorkflowEngine::new(tokens_for(&issuer, &[ALICE]));
        let wf = Workflow::new("d").then(Step::new("s0", ALICE).set(ALICE, 10, 0));
        let err = engine.run_durable(&wf, &mut AppendFails).unwrap_err();
        assert!(matches!(err, StepError::Durability(m) if m == "disk full"));
        assert_eq!(engine.turn_count(), 1, "the turn WAS admitted in-process before the persist failed");
    }
}
