//! # The server side — the LAW. A real executor cell behind the affordance fire.
//!
//! This module CLOSES the one seam the prototype named: the island's button-press
//! used to go through a `MockExecutor` (a faithful stand-in that applied the effect
//! by hand). Here the fire goes through the **real** [`dregg_turn::TurnExecutor`] —
//! owned by [`dregg_sdk::AgentRuntime`] over an in-process verified ledger — so a
//! fire is a **genuine verified turn** that returns a real [`dregg_turn::TurnReceipt`],
//! and the reactive signal graph re-seeds from the state the executor actually
//! COMMITTED.
//!
//! ## The gate is the REAL one, and it is the SAME gate the island reacts on
//!
//! The fire is adjudicated by the genuine
//! [`starbridge_web_surface::ReactiveAffordance::fire`] — the cap∧transition∧window
//! gate (the Rust twin of the Lean `reactiveOK`). That is the SAME
//! `ReactiveAffordance` whose [`ReactiveAffordance::reactive_ok`] drives the island's
//! lit/dark Memo ([`crate::affordance_is_lit`]). So the client-WILL predicate (what
//! the island OFFERS) and the server-LAW gate (what actually COMMITS) are byte-for-
//! byte the same type — there is no second gate to drift. On a refusal the precise
//! [`starbridge_web_surface::FireError`] is returned **before any turn is built**
//! (anti-ghost: nothing committed). On a pass, the gate yields an
//! [`starbridge_web_surface::affordance::AffordanceIntent`] carrying the REAL
//! [`dregg_turn::Effect`]; that effect is submitted through the executor, and the
//! executor INDEPENDENTLY re-enforces the cell's installed [`dregg_cell::CellProgram`]
//! invariant on the post-state (the deepest tooth).
//!
//! ## Why server-side (the deos trust boundary, made literal)
//!
//! The executor sits atop the native STARK stack (`dregg-turn` → `dregg-circuit` →
//! plonky3 + the Lean FFI). That stack does NOT compile to
//! `wasm32-unknown-unknown` — so the gate + the executor are **native-only**. That
//! is not a wall; it IS the deos seam: *the island is the will, the server is the
//! law*. A light client must never be the authority. So the client island
//! ([`crate::CounterCell`]) POSTs a [`FireRequest`] to the server function
//! [`fire_affordance`]; the server runs the REAL gate + executor and returns the
//! committed state, which the island reflects into its signal.
//!
//! ## Why `AgentRuntime` directly (not `app-framework`'s `EmbeddedExecutor`)
//!
//! `EmbeddedExecutor` merely WRAPS [`AgentRuntime`] (this is what its `submit_turn`
//! does: clone turn → default fee → `turn.nonce = rt.nonce()` → `rt.execute_turn`).
//! We drive the runtime directly because `dregg-app-framework` currently carries an
//! in-flight, uncompilable `stark_rehydrate` module (an untracked WIP whose type
//! mismatch fails in the root workspace too — nothing to do with this crate). Driving
//! the SDK runtime directly is both the working path AND the cleaner architecture: a
//! Leptos SSR crate atop the SDK runtime, not dragging app-framework's
//! axum/captp/rehydrate surface.

use std::sync::{Arc, Mutex, OnceLock, RwLock};

use starbridge_web_surface::affordance::{AffordanceIntent, RecordPredicate};
use starbridge_web_surface::{
    AuthRequired, CellAffordance, EvalContext, FireError, ReactiveAffordance, SurfaceCapability,
    TransitionGate,
};

use dregg_cell::state::CellState;
use dregg_cell::{CellProgram, StateConstraint};
use dregg_sdk::{AgentCipherclerk, AgentRuntime, SdkError};
use dregg_turn::{Effect, TurnReceipt};
use dregg_types::CellId;

use crate::gate::{fe, fe_u64, CellSlots, PENDING, RESOLVED, STATUS_SLOT, TALLY_SLOT};

/// The inclusive reactive WINDOW the `vote`/`resolve` buttons light within (the same
/// `[10, 20]` window the prototype's [`crate::vote_btn`] uses). The window tooth is a
/// reactive-UI hint AND a real gate conjunct (the twin of the Lean `inWindow`).
pub const WINDOW_OPEN: u64 = 10;
/// The inclusive reactive window CLOSE height (the deadline).
pub const WINDOW_CLOSE: u64 = 20;

// ════════════════════════════════════════════════════════════════════════════
// THE SERVER-SIDE EXECUTOR CELL — the real `TurnExecutor` (owned by AgentRuntime),
// the council cell, the real gate. This is the LAW the island's fire is adjudicated
// against.
// ════════════════════════════════════════════════════════════════════════════

/// The council cell exposing the gated affordances, backed by a **real**
/// [`AgentRuntime`] (the in-process verified ledger that owns a genuine
/// [`dregg_turn::TurnExecutor`]). Every fire through this cell is a verified turn.
///
/// `AgentRuntime` is `!Send`/`!Sync` (its `TurnExecutor` holds a `RefCell` minter), so
/// we serialize access through a `Mutex` — adequate for an SSR cell whose turns all
/// mutate the same ledger. The cipherclerk handle is kept (shared with the runtime)
/// so the same key both signs the action and submits the turn.
pub struct DeosExecutorCell {
    /// The real executor runtime — owns `dregg_turn::TurnExecutor` + the verified
    /// ledger. Behind a `Mutex` for Send+Sync.
    runtime: Arc<Mutex<AgentRuntime>>,
    /// The action-signing handle (shares the runtime's agent identity + receipt
    /// chain). Kept so the same key signs + submits; the `_` silences unused-field
    /// while documenting the shared-identity contract.
    _cipherclerk: Arc<RwLock<AgentCipherclerk>>,
    /// The council cell (the agent's own cell — so the ledger holds it and the
    /// executor commits turns against it).
    cell_id: CellId,
}

impl DeosExecutorCell {
    /// Build a fresh council executor cell: a funded one-cell ledger, a real
    /// executor, the council invariant installed, seeded PENDING / tally 0.
    ///
    /// `fed_byte` seeds the federation id the runtime signs + checks against. No
    /// prover/circuit/key is required (proving is off unless a cell opts in — this
    /// council cell does not).
    pub fn new(fed_byte: u8) -> Self {
        let fed_id = [fed_byte; 32];
        let domain = "default";

        // The SDK surface: a cipherclerk (fresh keypair) shared with the runtime, so
        // the same key signs actions and submits turns. The council cell IS the
        // agent's OWN cell — `AgentRuntime::new` seeds it into the verified ledger
        // (1M computrons), so fires execute through the real executor.
        let cipherclerk = Arc::new(RwLock::new(AgentCipherclerk::new()));
        let mut runtime = AgentRuntime::new(cipherclerk.clone(), domain);
        // The runtime's federation id MUST match the one the actions are signed
        // against (so the executor's signature check passes).
        runtime.set_local_federation_id(fed_id);
        let cell_id = runtime.cell_id();

        // Install the council's lifetime INVARIANT (status + tally both monotonic) on
        // the agent cell AND seed it PENDING / tally 0 — the birth state the gate
        // reads back. The executor re-enforces the invariant on EVERY turn's
        // post-state: a `vote` (tally += 1, status unchanged) and a `resolve` (status
        // PENDING→RESOLVED) both satisfy it.
        {
            let mut ledger = runtime.ledger().lock().unwrap_or_else(|e| e.into_inner());
            if let Some(cell) = ledger.get_mut(&cell_id) {
                cell.program = council_invariant();
                cell.state.set_field(STATUS_SLOT, fe(PENDING));
                cell.state.set_field(TALLY_SLOT, fe(0));
            }
        }

        DeosExecutorCell {
            runtime: Arc::new(Mutex::new(runtime)),
            _cipherclerk: cipherclerk,
            cell_id,
        }
    }

    /// The council cell id (the agent's own cell).
    pub fn cell_id(&self) -> CellId {
        self.cell_id
    }

    /// The cell's **live** [`CellSlots`] — the read the reactive signal re-seeds from
    /// after a committed turn. Reads the genuine [`CellState`] the executor holds, so
    /// the signal reflects what the executor actually COMMITTED, not a client guess.
    pub fn live_slots(&self) -> CellSlots {
        self.with_live_state(CellSlots::from_cell_state)
            .unwrap_or_else(CellSlots::pending)
    }

    /// Read the live [`CellState`] of the council cell out of the verified ledger and
    /// project it with `f`. `None` if the cell is absent (fail-closed).
    fn with_live_state<R>(&self, f: impl FnOnce(&CellState) -> R) -> Option<R> {
        let rt = self.runtime.lock().unwrap_or_else(|e| e.into_inner());
        let ledger = rt.ledger().lock().unwrap_or_else(|e| e.into_inner());
        ledger.get(&self.cell_id).map(|c| f(&c.state))
    }

    /// **FIRE through the real executor** — the seam-closer. Run the REAL
    /// [`ReactiveAffordance::fire`] gate (cap∧transition∧window) IN-BAND against the
    /// cell's LIVE state; on a refusal return the precise [`FireError`] and commit
    /// NOTHING (anti-ghost); on a pass take the gate's [`AffordanceIntent`] effect and
    /// submit it through the executor, returning the real [`TurnReceipt`] plus the
    /// COMMITTED post-state. This is the body the [`fire_affordance`] server-fn runs.
    ///
    /// - `name` — the affordance the island fired (`"vote"` / `"resolve"`);
    /// - `held` — the viewer's held authority (the cap dimension; the server builds
    ///   the `SurfaceCapability` from it);
    /// - `height` — the turn height (the reactive window's clock).
    ///
    /// The `vote` affordance increments the tally; its candidate transition is `old →
    /// old{tally+1}` and its effect is `SetField(tally, live_tally+1)`. The `resolve`
    /// affordance is `old → old{status:RESOLVED}` writing `SetField(status, RESOLVED)`.
    pub fn fire(
        &self,
        name: &str,
        held: &AuthRequired,
        height: u64,
    ) -> Result<FireOutcome, FireRefusal> {
        // The live state the executor holds — the gate reads back what was committed,
        // never a client claim.
        let old = self
            .with_live_state(|s| s.clone())
            .ok_or(FireRefusal::Gate(FireError::NoSuchAffordance))?;
        let live = CellSlots::from_cell_state(&old);

        // The REAL reactive affordance for this name + its candidate post-state.
        let (btn, new) = match self.affordance_and_candidate(name, &live) {
            Some(pair) => pair,
            None => return Err(FireRefusal::Gate(FireError::NoSuchAffordance)),
        };

        // THE REAL GATE — cap∧transition∧window, IN-BAND. The held authority becomes a
        // `SurfaceCapability` (the same shape the island's viewer holds). On a refusal
        // the precise `FireError` is returned and NOTHING is submitted.
        let cap = SurfaceCapability::root(self.cell_id, held.clone());
        let ctx = EvalContext::at_height(height);
        let intent: AffordanceIntent = btn
            .fire(self.cell_id, &cap, &ctx, &old, &new)
            .map_err(FireRefusal::Gate)?;

        // THE REAL EXECUTOR — the gate passed; submit the REAL effect as a verified
        // turn. The effect targets the agent's own cell, so `AgentRuntime::execute`
        // signs + submits it through the owned `TurnExecutor`, which independently
        // re-enforces the cell's installed invariant on the post-state.
        let receipt = self
            .execute_effect(intent.effect.clone())
            .map_err(|e| FireRefusal::Executor(e.to_string()))?;

        // Read the COMMITTED post-state back from the executor (NOT a hand-applied
        // guess) — this is what the reactive signal reflects.
        let committed = self.live_slots();
        Ok(FireOutcome { receipt, committed })
    }

    /// Submit a single [`Effect`] on the agent's own cell as a verified turn, returning
    /// the executor's [`TurnReceipt`]. Uses [`AgentRuntime::execute`] (signs +
    /// submits + bumps nonce + sets fee) — the one-call path for a self-targeted
    /// effect. This is precisely what `EmbeddedExecutor::submit_*` does internally,
    /// minus the (currently-uncompilable) app-framework wrapper.
    fn execute_effect(&self, effect: Effect) -> Result<TurnReceipt, SdkError> {
        let rt = self.runtime.lock().unwrap_or_else(|e| e.into_inner());
        rt.execute(vec![effect])
    }

    /// The REAL [`ReactiveAffordance`] for `name` plus the candidate post-state the
    /// transition gate verifies, minted against the live state. `vote` → tally+1;
    /// `resolve` → status:RESOLVED. `None` for an unknown name.
    fn affordance_and_candidate(
        &self,
        name: &str,
        live: &CellSlots,
    ) -> Option<(ReactiveAffordance, CellState)> {
        match name {
            "vote" => {
                // The vote button: ballot cap `Either`, the add-a-ballot transition
                // (PENDING→PENDING, tally += 1), the `[open, close]` window. The
                // effect commits the successor tally.
                let btn = ReactiveAffordance::new(
                    CellAffordance::new(
                        "vote",
                        AuthRequired::Either,
                        Effect::SetField {
                            cell: self.cell_id,
                            index: TALLY_SLOT,
                            value: fe(live.tally + 1),
                        },
                    ),
                    vote_gate(),
                    WINDOW_OPEN,
                    WINDOW_CLOSE,
                );
                let new = council_state(PENDING, live.tally + 1);
                Some((btn, new))
            }
            "resolve" => {
                // The resolve button: ballot cap `Either`, the close transition
                // (PENDING→RESOLVED), the same window. The effect writes RESOLVED.
                let btn = ReactiveAffordance::new(
                    CellAffordance::new(
                        "resolve",
                        AuthRequired::Either,
                        Effect::SetField {
                            cell: self.cell_id,
                            index: STATUS_SLOT,
                            value: fe(RESOLVED),
                        },
                    ),
                    resolve_gate(),
                    WINDOW_OPEN,
                    WINDOW_CLOSE,
                );
                let new = council_state(RESOLVED, live.tally);
                Some((btn, new))
            }
            _ => None,
        }
    }
}

/// A council-cell [`CellState`] with the given `status` + `tally` (the genuine
/// `CellState`, using the prototype's slot encoding).
fn council_state(status: u64, tally: u64) -> CellState {
    let mut s = CellState::new(0);
    s.set_field(STATUS_SLOT, fe(status));
    s.set_field(TALLY_SLOT, fe(tally));
    s
}

/// A predicate "status slot == `want`" over a single record (a `RecordPredicate`).
fn status_is(want: u64) -> RecordPredicate {
    Box::new(move |s: &CellState| s.get_field(STATUS_SLOT).map(fe_u64) == Some(want))
}

/// The VOTE transition gate: PENDING → PENDING AND the tally went up by EXACTLY ONE —
/// the relational link reading BOTH records. Identical to the prototype's `vote_gate`.
fn vote_gate() -> TransitionGate {
    TransitionGate::new(
        status_is(PENDING),
        status_is(PENDING),
        Box::new(|old: &CellState, new: &CellState| {
            match (
                old.get_field(TALLY_SLOT).map(fe_u64),
                new.get_field(TALLY_SLOT).map(fe_u64),
            ) {
                (Some(a), Some(b)) => b == a + 1,
                _ => false,
            }
        }),
    )
}

/// The RESOLVE transition gate: PENDING → RESOLVED (the proposal closes). The `pre`
/// is PENDING (a resolved proposal cannot re-resolve), the `post` is RESOLVED, and the
/// link admits the status flip.
fn resolve_gate() -> TransitionGate {
    TransitionGate::new(
        status_is(PENDING),
        status_is(RESOLVED),
        Box::new(|_old: &CellState, _new: &CellState| true),
    )
}

/// The council cell's lifetime INVARIANT — `status` AND `tally` are both monotonic
/// (a proposal resolves but never un-resolves; votes only accumulate). The genuine
/// state-machine the executor re-enforces on every turn's post-state.
fn council_invariant() -> CellProgram {
    CellProgram::Predicate(vec![
        StateConstraint::Monotonic {
            index: STATUS_SLOT as u8,
        },
        StateConstraint::Monotonic {
            index: TALLY_SLOT as u8,
        },
    ])
}

/// The outcome of a committed fire: the executor's OWN [`TurnReceipt`] (proof the turn
/// committed) plus the COMMITTED post-state slots (what the reactive signal reflects).
#[derive(Clone, Debug)]
pub struct FireOutcome {
    /// The real receipt the executor returned for the committed turn.
    pub receipt: TurnReceipt,
    /// The cell's live slots AFTER the commit (read back from the executor).
    pub committed: CellSlots,
}

/// Why a fire was refused — either the REAL gate refused it (a precise [`FireError`],
/// nothing submitted — the anti-ghost path) or the executor declined the (gated) turn.
#[derive(Clone, Debug)]
pub enum FireRefusal {
    /// The REAL [`ReactiveAffordance::fire`] gate refused — the turn was NEVER built.
    /// This is the anti-ghost path (cap / transition / window tooth).
    Gate(FireError),
    /// The gate PASSED but the executor declined the submitted turn (e.g. an invariant
    /// bit on the post-state). The effect WAS the real one; the executor rejected it.
    /// Held as the rendered message (`SdkError` is not `Clone`, and a refusal only needs
    /// to be displayed, never re-thrown).
    Executor(String),
}

impl std::fmt::Display for FireRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FireRefusal::Gate(e) => write!(f, "fire refused by gate: {e:?}"),
            FireRefusal::Executor(e) => write!(f, "fire rejected by executor: {e}"),
        }
    }
}

impl std::error::Error for FireRefusal {}

// ════════════════════════════════════════════════════════════════════════════
// THE SERVER FUNCTION BOUNDARY — the island POSTs a FireRequest; the server runs the
// real executor and returns the committed state. The process-global executor cell IS
// the server's authoritative ledger.
// ════════════════════════════════════════════════════════════════════════════

/// The request the client island POSTs to fire an affordance — the wire shape of an
/// [`AffordanceIntent`] (the affordance name + the viewer's held authority + the turn
/// height). The island carries the *will*; the server applies the *law*.
///
/// The held authority is sent as the cap dimension (a real deployment resolves it from
/// a verified presentation, not the wire); here it names the exemplar viewer so the
/// demo + tests drive the real gate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FireRequest {
    /// The affordance the island fired (`"vote"` / `"resolve"`).
    pub affordance: String,
    /// The viewer's held authority (the cap dimension of the gate).
    pub held: AuthRequired,
    /// The turn height (the reactive window's clock).
    pub height: u64,
}

impl FireRequest {
    /// A fire request for `affordance` by a viewer holding `held`, mid-window (a
    /// height inside `[WINDOW_OPEN, WINDOW_CLOSE]`).
    pub fn at(affordance: impl Into<String>, held: AuthRequired) -> Self {
        FireRequest {
            affordance: affordance.into(),
            held,
            height: (WINDOW_OPEN + WINDOW_CLOSE) / 2,
        }
    }

    /// Set an explicit turn height (to exercise the window tooth).
    pub fn height(mut self, height: u64) -> Self {
        self.height = height;
        self
    }
}

/// The response the server returns: the committed slots (which the island reflects into
/// its signal) plus the receipt's turn-hash (proof of the verified turn). On a refusal
/// the server returns the precise reason and the (unchanged) live state.
#[derive(Clone, Debug)]
pub struct FireResponse {
    /// `Ok` carrying the committed state + the turn-hash, or `Err` carrying the
    /// precise refusal reason (the anti-ghost message) + the unchanged live state.
    pub result: Result<FireCommitted, FireRefused>,
}

/// A committed fire: the post-state the executor committed + the turn-hash.
#[derive(Clone, Debug)]
pub struct FireCommitted {
    /// The committed slots (what the reactive signal reflects).
    pub slots: CellSlots,
    /// The committed turn's hash (proof of the verified turn — read off the receipt).
    pub turn_hash: [u8; 32],
}

/// A refused fire: the precise reason + the unchanged live state (nothing committed).
#[derive(Clone, Debug)]
pub struct FireRefused {
    /// The precise refusal reason (cap/transition/window tooth, or executor decline).
    pub reason: String,
    /// The (unchanged) live state — the anti-ghost guarantee, surfaced to the island.
    pub slots: CellSlots,
}

/// The process-global server-side executor cell — the authoritative verified ledger
/// behind every fire. A single in-process cell (the embedded ledger is per-process).
/// Behind a `Mutex` because a fire mutates the ledger and the SSR server may handle
/// requests concurrently.
fn executor_cell() -> &'static Mutex<DeosExecutorCell> {
    static CELL: OnceLock<Mutex<DeosExecutorCell>> = OnceLock::new();
    CELL.get_or_init(|| Mutex::new(DeosExecutorCell::new(0xC0)))
}

/// **The server function** the island fires through — the closed seam. Runs the REAL
/// executor cell's [`DeosExecutorCell::fire`] against the process-global verified
/// ledger and maps the outcome to a [`FireResponse`]. This is the body a Leptos
/// `#[server]` macro wraps for the HTTP boundary (the island's POST → here, native);
/// here it is a plain function so the SSR demo + the tests exercise the REAL path
/// without standing up an HTTP server.
///
/// - an authorized in-state, in-window fire ⇒ `Ok(FireCommitted{ slots, turn_hash })`
///   — a real verified turn, the committed state, the receipt's hash;
/// - a refused fire (cap / transition / window / executor) ⇒
///   `Err(FireRefused{ reason, slots })` — the precise reason, the UNCHANGED state
///   (anti-ghost: nothing committed).
pub fn fire_affordance(req: FireRequest) -> FireResponse {
    let cell = executor_cell().lock().unwrap_or_else(|e| e.into_inner());
    let before = cell.live_slots();
    match cell.fire(&req.affordance, &req.held, req.height) {
        Ok(outcome) => FireResponse {
            result: Ok(FireCommitted {
                slots: outcome.committed,
                turn_hash: outcome.receipt.turn_hash,
            }),
        },
        Err(e) => {
            // The anti-ghost guarantee, surfaced: a refused fire leaves the live state
            // EXACTLY as it was (re-read here to prove it is unchanged).
            let after = cell.live_slots();
            debug_assert_eq!(before, after, "a refused fire must not mutate state");
            let reason = match &e {
                FireRefusal::Gate(fe) => format!("{fe:?}"),
                FireRefusal::Executor(se) => format!("executor declined: {se}"),
            };
            FireResponse {
                result: Err(FireRefused {
                    reason,
                    slots: after,
                }),
            }
        }
    }
}

/// Reset the process-global executor cell to a fresh council (for the demo, which fires
/// multiple times against a clean cell, and for deterministic tests). Returns the fresh
/// live slots.
pub fn reset_executor_cell() -> CellSlots {
    let mut guard = executor_cell().lock().unwrap_or_else(|e| e.into_inner());
    *guard = DeosExecutorCell::new(0xC0);
    guard.live_slots()
}

#[cfg(test)]
mod tests {
    use super::*;

    // The exemplar held authorities (the REAL is_attenuation lattice):
    //   councillor holds `Either` (clears the ballot cap);
    //   member holds only `Signature` (NOT the ballot cap);
    //   outsider holds an incomparable `Custom` identity.
    fn councillor() -> AuthRequired {
        AuthRequired::Either
    }
    fn member() -> AuthRequired {
        AuthRequired::Signature
    }
    fn outsider() -> AuthRequired {
        AuthRequired::Custom {
            vk_hash: [0x9E; 32],
        }
    }
    const MID: u64 = (WINDOW_OPEN + WINDOW_CLOSE) / 2;

    // ── THE SEAM IS CLOSED: a fire is a REAL verified turn through the REAL
    //    executor, returning a REAL receipt; the committed state advances. ──

    #[test]
    fn authorized_fire_is_a_real_verified_turn_and_state_advances() {
        let cell = DeosExecutorCell::new(0xC0);
        assert_eq!(cell.live_slots().tally, 0);
        assert!(cell.live_slots().is_pending());

        // A councillor (holds the ballot cap) votes in-window while PENDING: the REAL
        // gate passes (cap∧transition∧window), the REAL effect commits through the
        // executor, a real receipt comes back.
        let out = cell
            .fire("vote", &councillor(), MID)
            .expect("an authorized in-window vote commits a real verified turn");

        // The receipt is the REAL one: a non-zero turn-hash, a post-state commitment,
        // and computrons were actually spent running the verified turn.
        assert_ne!(
            out.receipt.turn_hash, [0u8; 32],
            "real turn has a real hash"
        );
        assert_ne!(out.receipt.post_state_hash, [0u8; 32]);
        assert!(out.receipt.computrons_used > 0, "the verified turn ran");
        assert_eq!(
            out.receipt.agent,
            cell.cell_id(),
            "committed by the council cell"
        );

        // The COMMITTED state advanced — the tally the executor wrote is 1 (read back
        // from the executor's own ledger, not a hand-applied guess).
        assert_eq!(out.committed.tally, 1);
        assert_eq!(
            cell.live_slots().tally,
            1,
            "the live ledger reflects the commit"
        );

        // A second vote advances to 2 (the monotonic tally accumulates through real
        // turns), a distinct turn.
        let out2 = cell
            .fire("vote", &councillor(), MID)
            .expect("a second vote commits");
        assert_eq!(out2.committed.tally, 2);
        assert_ne!(
            out2.receipt.turn_hash, out.receipt.turn_hash,
            "distinct turns"
        );
    }

    // ── THE ANTI-GHOST TEETH: a refused fire is a precise gate FireError and NOTHING
    //    is committed (the live state is byte-for-byte unchanged). ──

    #[test]
    fn cap_refusal_commits_nothing_anti_ghost() {
        let cell = DeosExecutorCell::new(0xC0);
        let before = cell.live_slots();

        // A member lacks the ballot cap (`Signature` does not attenuate `Either`): the
        // CAP tooth of the REAL gate refuses IN-BAND — `FireError::Unauthorized` — and
        // NOTHING is submitted to the executor.
        let err = cell
            .fire("vote", &member(), MID)
            .expect_err("a member without the ballot cap is refused");
        assert!(
            matches!(err, FireRefusal::Gate(FireError::Unauthorized { .. })),
            "cap tooth ⇒ Gate(Unauthorized), got {err:?}"
        );
        assert_eq!(cell.live_slots(), before, "a refused fire commits nothing");
    }

    #[test]
    fn outsider_refusal_commits_nothing_anti_ghost() {
        let cell = DeosExecutorCell::new(0xC0);
        let before = cell.live_slots();
        let err = cell
            .fire("vote", &outsider(), MID)
            .expect_err("an incomparable outsider is refused");
        assert!(matches!(
            err,
            FireRefusal::Gate(FireError::Unauthorized { .. })
        ));
        assert_eq!(cell.live_slots(), before);
    }

    #[test]
    fn window_refusal_commits_nothing_anti_ghost() {
        let cell = DeosExecutorCell::new(0xC0);
        let before = cell.live_slots();
        // A councillor with the ballot cap on a perfect transition, but AFTER the
        // deadline (close+5 > WINDOW_CLOSE): the WINDOW tooth refuses in-band.
        let err = cell
            .fire("vote", &councillor(), WINDOW_CLOSE + 5)
            .expect_err("voting after the deadline is refused on the window tooth");
        assert!(
            matches!(err, FireRefusal::Gate(FireError::OutsideWindow { .. })),
            "window tooth ⇒ Gate(OutsideWindow), got {err:?}"
        );
        assert_eq!(
            cell.live_slots(),
            before,
            "a window-refused fire commits nothing"
        );
    }

    #[test]
    fn state_refusal_commits_nothing_even_for_authorized_actor_anti_ghost() {
        let cell = DeosExecutorCell::new(0xC0);
        // Resolve the proposal (PENDING→RESOLVED) — an authorized in-window close.
        cell.fire("resolve", &councillor(), MID)
            .expect("a councillor may resolve a PENDING proposal in-window");
        assert_eq!(cell.live_slots().status, RESOLVED);
        let before = cell.live_slots();

        // Now even a councillor's vote is refused: the transition gate's `pre` (status
        // PENDING) fails on the RESOLVED `old` state — the TRANSITION tooth. This is
        // the half a cap-only gate could never express.
        let err = cell
            .fire("vote", &councillor(), MID)
            .expect_err("voting on a RESOLVED proposal is refused on the transition tooth");
        assert!(
            matches!(err, FireRefusal::Gate(FireError::TransitionUnmet { .. })),
            "transition tooth ⇒ Gate(TransitionUnmet), got {err:?}"
        );
        assert_eq!(
            cell.live_slots(),
            before,
            "a transition-refused fire commits nothing"
        );
    }

    #[test]
    fn unknown_affordance_is_no_such_affordance() {
        let cell = DeosExecutorCell::new(0xC0);
        let err = cell
            .fire("frobnicate", &councillor(), MID)
            .expect_err("an unknown affordance is refused");
        assert!(matches!(
            err,
            FireRefusal::Gate(FireError::NoSuchAffordance)
        ));
    }

    // ── THE SERVER-FN BOUNDARY: the island's POST shape runs the real executor and
    //    maps to a committed/refused response — the closed seam end to end. ──

    #[test]
    fn server_fn_authorized_fire_returns_committed_state_and_turn_hash() {
        reset_executor_cell();
        let resp = fire_affordance(FireRequest::at("vote", councillor()));
        let committed = resp.result.expect("an authorized fire commits");
        assert_eq!(
            committed.slots.tally, 1,
            "the server-fn returns the committed tally"
        );
        assert_ne!(committed.turn_hash, [0u8; 32], "and the real turn-hash");
    }

    #[test]
    fn server_fn_refused_fire_returns_precise_reason_and_unchanged_state() {
        reset_executor_cell();
        let resp = fire_affordance(FireRequest::at("vote", member())); // no ballot cap
        let refused = resp.result.expect_err("a member's fire is refused");
        // The precise anti-ghost reason names the cap tooth.
        assert!(
            refused.reason.contains("Unauthorized"),
            "precise cap-tooth reason: {}",
            refused.reason
        );
        assert_eq!(
            refused.slots.tally, 0,
            "a refused fire leaves the tally at 0"
        );
        assert!(refused.slots.is_pending());
    }

    #[test]
    fn server_fn_fire_sequence_threads_committed_state() {
        // Two authorized fires in a row thread the committed state through the real
        // executor: 0 → 1 → 2. The server is the single source of truth.
        reset_executor_cell();
        let r1 = fire_affordance(FireRequest::at("vote", councillor()));
        assert_eq!(r1.result.unwrap().slots.tally, 1);
        let r2 = fire_affordance(FireRequest::at("vote", councillor()));
        assert_eq!(r2.result.unwrap().slots.tally, 2);
    }
}
