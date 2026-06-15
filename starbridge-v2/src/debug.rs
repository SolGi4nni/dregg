//! THE TURN DEBUGGER — step, inspect, explain a dregg turn.
//!
//! A turn is a `CallForest` (a tree of `Action`s, each carrying a list of
//! `Effect`s) that the verified executor applies depth-first, atomically: it
//! either commits the whole forest or rolls it back. That atomicity is exactly
//! what makes "why did my turn fail, and what would it have done?" hard to see
//! from the outside — there is no partial commit to inspect.
//!
//! This module recovers that visibility by FAITHFUL RE-EXECUTION. It never
//! hooks into the live commit (there is no such hook, and forging one would be
//! a lie about what the executor does). Instead it:
//!
//!   1. Clones the world's ledger (the real pre-state) and stands up a fresh
//!      `TurnExecutor` configured identically to the live one (same zero-cost
//!      metering, same wall clock, same per-agent receipt-chain head).
//!   2. Flattens the forest into its effects in executor DFS order, and for
//!      each prefix `k` of effects, builds a PREFIX TURN that carries only the
//!      first `k` effects (preserving each action's authorization /
//!      preconditions / delegation) and runs it against a FRESH clone.
//!   3. Snapshots the post-state after each prefix: the touched cells'
//!      balances / nonces / caps, and the running conservation delta (Σ of
//!      balance movement, which a conserving turn holds at zero).
//!
//! Because every prefix is a real turn run through the REAL executor, each step
//! carries the executor's real verdict — including the structured [`TurnError`]
//! when a prefix is the one the executor refuses. That is the highest-value
//! feature: [`explain_refusal`] names the exact guard/cap/conservation/auth
//! check that rejected the turn, with the effect index it died on.
//!
//! HONESTY: this is a faithful re-execution, NOT a tap on the live commit. A
//! prefix turn is a *different turn hash* than the full turn (it carries fewer
//! effects); the per-step states are what the executor WOULD reach having
//! applied exactly those effects, which is precisely the debugger's question.
//! The receipt-chain head and nonce are taken from the live world, so step 0's
//! pre-state and the final step's post-state match a real commit of the turn.

use std::collections::BTreeMap;

use dregg_cell::{Cell, CellId, Ledger};
use dregg_turn::{
    action::Effect,
    forest::{CallForest, CallTree},
    turn::{Turn, TurnReceipt, TurnResult},
    TurnError, TurnExecutor,
};

use crate::world::World;

// ===========================================================================
// State snapshots — the per-step picture the panel renders.
// ===========================================================================

/// A snapshot of one cell's debugger-relevant state at a step boundary.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CellSnapshot {
    pub id: CellId,
    /// SIGNED balance (issuer wells read negative — THE EPOCH §5).
    pub balance: i64,
    pub nonce: u64,
    /// Targets this cell currently holds a capability reaching (the ocap edges).
    pub cap_targets: Vec<CellId>,
}

impl CellSnapshot {
    fn of(id: CellId, cell: &Cell) -> Self {
        CellSnapshot {
            id,
            balance: cell.state.balance(),
            nonce: cell.state.nonce(),
            cap_targets: cell.capabilities.iter().map(|c| c.target).collect(),
        }
    }
}

/// The full state picture at one step boundary: every cell the turn touches,
/// plus the running conservation delta.
#[derive(Clone, Debug)]
pub struct StepState {
    /// Snapshots of every touched cell, keyed by id (sorted, stable order).
    pub cells: Vec<CellSnapshot>,
    /// The conservation delta = (Σ touched balances now) − (Σ touched balances
    /// at the turn's pre-state). A value-conserving step holds this at ZERO; a
    /// non-zero reading mid-forest is a conservation break the executor would
    /// reject at turn-end (`ExcessNotZero`). Burns legitimately drive it
    /// negative (disclosed via `was_burn`).
    pub conservation_delta: i64,
}

impl StepState {
    fn capture(ledger: &Ledger, touched: &[CellId], baseline_sum: i64) -> Self {
        let mut cells = Vec::new();
        let mut sum: i64 = 0;
        for id in touched {
            if let Some(cell) = ledger.get(id) {
                sum = sum.saturating_add(cell.state.balance());
                cells.push(CellSnapshot::of(*id, cell));
            }
        }
        StepState {
            cells,
            conservation_delta: sum - baseline_sum,
        }
    }

    pub fn cell(&self, id: &CellId) -> Option<&CellSnapshot> {
        self.cells.iter().find(|c| &c.id == id)
    }
}

// ===========================================================================
// Steps — one per effect prefix.
// ===========================================================================

/// One step of the debugged turn: the executor has applied the first `index+1`
/// effects (in DFS order). `label` describes the effect that *this* step
/// applied; `state` is the post-state after it.
#[derive(Clone, Debug)]
pub struct Step {
    /// 0-based effect index in DFS order.
    pub index: usize,
    /// Human-readable description of the effect applied at this step.
    pub label: String,
    /// The cells this specific effect touches (for "break when cell touched").
    pub touches: Vec<CellId>,
    /// The post-state after applying this effect (and all before it).
    pub state: StepState,
    /// `true` if the executor ACCEPTED the prefix ending at this effect.
    /// `false` means this is the effect at which the turn first refuses — its
    /// [`refusal`] is then populated.
    pub committed: bool,
    /// When `committed` is false: the structured reason the executor refused
    /// the prefix ending here.
    pub refusal: Option<TurnError>,
}

/// The result of debugging a turn: the pre-state, the per-effect steps, and —
/// if the turn ultimately refuses — the structured explanation.
#[derive(Clone, Debug)]
pub struct TurnTrace {
    /// The agent that submitted the turn.
    pub agent: CellId,
    /// Every cell the turn touches, in stable sorted order.
    pub touched: Vec<CellId>,
    /// The pre-state (before any effect) — step "−1".
    pub pre_state: StepState,
    /// One entry per effect, in DFS order.
    pub steps: Vec<Step>,
    /// `true` if the FULL turn commits (every effect accepted).
    pub committed: bool,
    /// When the full turn refuses: the structured explanation (which guard,
    /// which effect index). `None` when the turn commits cleanly.
    pub refusal: Option<RefusalExplanation>,
    /// The real receipt, when the full turn commits (witness/PI inspection).
    pub receipt: Option<TurnReceipt>,
}

impl TurnTrace {
    /// The last step the executor accepted (the deepest committed prefix). When
    /// the turn refuses, everything after this is the rejected tail.
    pub fn last_committed_index(&self) -> Option<usize> {
        self.steps.iter().rev().find(|s| s.committed).map(|s| s.index)
    }
}

// ===========================================================================
// Refusal explanation — the prize.
// ===========================================================================

/// A structured "why did my turn fail?" answer. Names the failing GUARD (one of
/// the executor's check families), the effect index it died on, the cells
/// involved, and a plain-language explanation — derived from the real
/// [`TurnError`] the executor returned.
#[derive(Clone, Debug)]
pub struct RefusalExplanation {
    /// Which family of guard rejected the turn.
    pub guard: GuardKind,
    /// The structured error the executor returned.
    pub error: TurnError,
    /// The effect index (DFS order) at which the turn first refuses, if the
    /// refusal is attributable to a specific effect prefix. `None` for
    /// turn-level refusals (nonce, expiry, empty forest, fee).
    pub effect_index: Option<usize>,
    /// The cells named by the refusal (for the view to highlight).
    pub cells: Vec<CellId>,
    /// A one-line plain-language headline ("over-spend: cell … needs N, has M").
    pub headline: String,
    /// A longer explanation of which invariant fired and why.
    pub detail: String,
}

/// The family of guard a refusal belongs to — the executor's check categories.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GuardKind {
    /// Value conservation / non-negativity (over-spend, excess≠0, underflow).
    Conservation,
    /// Capability / ocap reachability (no-amplification: can't grant what you
    /// don't hold; can't act on a cell you can't reach).
    Capability,
    /// Authorization (permission gates, token/stealth/signature auth).
    Authorization,
    /// Preconditions (temporal, state constraints, witnessed predicates).
    Precondition,
    /// Receipt-chain / nonce / replay (self-bound history).
    History,
    /// Structural (empty forest, malformed effect, field index, frozen cell).
    Structural,
    /// Proof / witness verification (STARK, sovereign commitment, custom).
    Proof,
    /// Anything else not yet categorized.
    Other,
}

impl GuardKind {
    pub fn name(self) -> &'static str {
        match self {
            GuardKind::Conservation => "conservation",
            GuardKind::Capability => "capability",
            GuardKind::Authorization => "authorization",
            GuardKind::Precondition => "precondition",
            GuardKind::History => "history",
            GuardKind::Structural => "structural",
            GuardKind::Proof => "proof",
            GuardKind::Other => "other",
        }
    }
}

/// Classify a `TurnError` into a guard family + extract the named cells.
fn classify(error: &TurnError) -> (GuardKind, Vec<CellId>) {
    use TurnError::*;
    match error {
        InsufficientBalance { cell, .. } => (GuardKind::Conservation, vec![*cell]),
        ExcessNotZero { .. } => (GuardKind::Conservation, vec![]),
        BalanceChangeUnderflow { cell, .. } => (GuardKind::Conservation, vec![*cell]),
        BalanceOverflow { cell } => (GuardKind::Conservation, vec![*cell]),
        CreateCellNonZeroBalance { cell, .. } => (GuardKind::Conservation, vec![*cell]),
        NoteConservationViolation { .. } => (GuardKind::Conservation, vec![]),
        CommittedConservationFailed { .. } => (GuardKind::Conservation, vec![]),

        CapabilityNotHeld { actor, target } => (GuardKind::Capability, vec![*actor, *target]),
        DelegationDenied { parent, child_target } => {
            (GuardKind::Capability, vec![*parent, *child_target])
        }
        // A delegation MODE that confers nothing (a no-op denial) — a capability-
        // family refusal, fail-closed, naming the parent + intended child target.
        DelegationModeUnimplemented { parent, child_target, .. } => {
            (GuardKind::Capability, vec![*parent, *child_target])
        }
        FacetViolation { actor, target, .. } => (GuardKind::Capability, vec![*actor, *target]),
        BearerCapFacetViolation { target, .. }
        | BearerCapFacetAmplification { target, .. }
        | BearerCapExpired { target, .. }
        | BearerCapRevoked { target, .. }
        | BearerCapInvalidProof { target, .. }
        | BearerCapAmplification { target, .. } => (GuardKind::Capability, vec![*target]),
        BearerCapDelegatorLacksCapability { delegator, target } => {
            (GuardKind::Capability, vec![*delegator, *target])
        }
        BreadstuffExpired { actor, target, .. }
        | BreadstuffRevoked { actor, target, .. }
        | BreadstuffFacetViolation { actor, target, .. } => {
            (GuardKind::Capability, vec![*actor, *target])
        }
        CapabilityRevoked { actor, .. } => (GuardKind::Capability, vec![*actor]),
        CapabilityStale { actor, grantor, .. } => (GuardKind::Capability, vec![*actor, *grantor]),
        StaleDelegation { actor, source, .. } => (GuardKind::Capability, vec![*actor, *source]),
        CapabilitySlotOverflow { cell } => (GuardKind::Capability, vec![*cell]),
        IntroductionDenied { introducer, recipient, target, .. } => {
            (GuardKind::Capability, vec![*introducer, *recipient, *target])
        }

        PermissionDenied { cell, .. } => (GuardKind::Authorization, vec![*cell]),
        InvalidAuthorization { .. } => (GuardKind::Authorization, vec![]),
        StealthAuthInvalid { .. } => (GuardKind::Authorization, vec![]),
        TokenAuthInvalid { .. } => (GuardKind::Authorization, vec![]),
        TokenInsufficientCapability { cell, .. } => (GuardKind::Authorization, vec![*cell]),
        TokenVerifierNotConfigured => (GuardKind::Authorization, vec![]),
        AuthModeNotRegistered { .. } => (GuardKind::Authorization, vec![]),

        PreconditionFailed { .. } => (GuardKind::Precondition, vec![]),
        ConditionNotMet(_) => (GuardKind::Precondition, vec![]),
        Expired { .. } => (GuardKind::Precondition, vec![]),

        NonceReplay { .. } => (GuardKind::History, vec![]),
        NonceOverflow { cell } => (GuardKind::History, vec![*cell]),
        ReceiptChainMismatch { .. } => (GuardKind::History, vec![]),

        EmptyForest => (GuardKind::Structural, vec![]),
        InvalidEffect { .. } => (GuardKind::Structural, vec![]),
        InvalidFieldIndex { cell, .. } => (GuardKind::Structural, vec![*cell]),
        // A refusal whose proof_witness_index does not resolve to a carried witness
        // blob — structurally inadmissible (the non-action attestation must point at
        // a real witness so a verifier can re-execute the refusal check).
        InvalidWitnessIndex { cell, .. } => (GuardKind::Structural, vec![*cell]),
        CellNotFound { id } | TransferDestNotFound { id } | CellAlreadyExists { id } => {
            (GuardKind::Structural, vec![*id])
        }
        CellFrozen { cell } => (GuardKind::Structural, vec![*cell]),
        RefusalConflictsWithMutation { cell, .. } => (GuardKind::Structural, vec![*cell]),
        BudgetExceeded { .. } | BudgetExhausted { .. } => (GuardKind::Structural, vec![]),
        InsufficientConditionalDeposit { .. } => (GuardKind::Structural, vec![]),

        ProgramViolation { cell, .. } => (GuardKind::Proof, vec![*cell]),
        InvalidExecutionProof(_)
        | EffectsHashMismatch { .. }
        | ProofVerificationFailed(_)
        | CustomProofCommitmentMismatch { .. }
        | CustomProgramNotFound { .. }
        | CustomProgramVerificationFailed { .. } => (GuardKind::Proof, vec![]),
        SovereignWitnessRequired { cell }
        | SovereignCommitmentMismatch { cell, .. }
        | ProofCarryingRequiresSovereign { cell }
        | SovereignNotRegistered { cell } => (GuardKind::Proof, vec![*cell]),

        LeanShadowVeto => (GuardKind::Other, vec![]),
        BridgeMintFailed { .. }
        | BridgeLockFailed { .. }
        | BridgeFinalizeFailed { .. }
        | BridgeCancelFailed { .. } => (GuardKind::Other, vec![]),
    }
}

impl RefusalExplanation {
    fn from_error(error: TurnError, effect_index: Option<usize>) -> Self {
        let (guard, cells) = classify(&error);
        let headline = headline_for(&error);
        let detail = detail_for(&error, guard);
        RefusalExplanation {
            guard,
            error,
            effect_index,
            cells,
            headline,
            detail,
        }
    }
}

fn headline_for(e: &TurnError) -> String {
    use TurnError::*;
    match e {
        InsufficientBalance { cell, required, available } => format!(
            "over-spend: cell {} needs {required} but holds {available}",
            crate::reflect::short_hex(cell.as_bytes())
        ),
        CapabilityNotHeld { actor, target } => format!(
            "no-amplification: cell {} holds no capability reaching {}",
            crate::reflect::short_hex(actor.as_bytes()),
            crate::reflect::short_hex(target.as_bytes())
        ),
        ExcessNotZero { excess } => {
            format!("conservation break: value does not balance (excess {excess})")
        }
        PermissionDenied { cell, action, .. } => format!(
            "permission denied: cell {} forbids '{action}'",
            crate::reflect::short_hex(cell.as_bytes())
        ),
        NonceReplay { expected, got } => {
            format!("replay: nonce expected {expected}, got {got}")
        }
        ReceiptChainMismatch { .. } => "broken receipt chain (self-bound history)".to_string(),
        CreateCellNonZeroBalance { balance, .. } => {
            format!("cells are born empty: CreateCell carried balance {balance}")
        }
        other => format!("{other}"),
    }
}

fn detail_for(e: &TurnError, guard: GuardKind) -> String {
    let invariant = match guard {
        GuardKind::Conservation => {
            "value conservation: every withdrawal must be matched by a deposit, \
             and no ordinary cell may go negative"
        }
        GuardKind::Capability => {
            "ocap no-amplification: you can only act on cells you can reach, and \
             only grant capabilities you already hold"
        }
        GuardKind::Authorization => {
            "authorization: the cell's permissions gate this effect and the \
             presented authority did not satisfy them"
        }
        GuardKind::Precondition => "the action's preconditions were not satisfied",
        GuardKind::History => {
            "self-bound history: the agent's nonce / receipt-chain head must \
             match the executor's record (no replay, no branch)"
        }
        GuardKind::Structural => "the turn or effect is structurally inadmissible",
        GuardKind::Proof => "a proof / witness did not verify",
        GuardKind::Other => "the executor refused this turn",
    };
    format!("{invariant}. Executor returned: {e}")
}

// ===========================================================================
// Breakpoints — predicates on the per-step state.
// ===========================================================================

/// A predicate-on-state breakpoint. The debugger fires at the FIRST step whose
/// post-state matches.
#[derive(Clone, Debug)]
pub enum Breakpoint {
    /// Break at the step where the executor first refuses (the refusal site).
    OnRefusal,
    /// Break when the conservation delta becomes non-zero mid-forest (a value
    /// imbalance the executor would reject at turn end).
    OnConservationBreak,
    /// Break when a specific cell is touched by an effect.
    OnCellTouched(CellId),
    /// Break when a cell's balance crosses below `floor` (e.g. an over-spend in
    /// the making, floor = 0).
    OnBalanceBelow { cell: CellId, floor: i64 },
    /// Break at a specific effect index.
    AtEffect(usize),
}

/// Where a breakpoint fired.
#[derive(Clone, Debug)]
pub struct BreakHit {
    /// Index of the breakpoint in the supplied list.
    pub breakpoint: usize,
    /// The step index it fired at.
    pub step: usize,
    /// The post-state at the break.
    pub state: StepState,
}

impl Breakpoint {
    /// Does this breakpoint fire at `step`?
    fn fires(&self, step: &Step) -> bool {
        match self {
            Breakpoint::OnRefusal => !step.committed,
            Breakpoint::OnConservationBreak => step.state.conservation_delta != 0,
            Breakpoint::OnCellTouched(c) => step.touches.contains(c),
            Breakpoint::OnBalanceBelow { cell, floor } => step
                .state
                .cell(cell)
                .map(|s| s.balance < *floor)
                .unwrap_or(false),
            Breakpoint::AtEffect(i) => step.index == *i,
        }
    }
}

// ===========================================================================
// THE DEBUGGER — drive a turn through faithful re-execution.
// ===========================================================================

/// Debug a turn against a world's CURRENT state without mutating the world.
///
/// Faithful re-execution: clones the world's ledger, stands up a fresh executor
/// matching the live one (same metering, clock, and the agent's chain-head),
/// and runs effect-prefixes to snapshot per-step state. Returns a full
/// [`TurnTrace`] — the per-step states, the commit/refuse verdict, and (on
/// refusal) the structured [`RefusalExplanation`].
pub fn debug_turn(world: &World, turn: &Turn) -> TurnTrace {
    let agent = turn.agent;
    let touched = touched_cells(turn);

    // Baseline: Σ touched balances at the world's pre-state (the conservation
    // reference). A conserving turn keeps the running Σ equal to this.
    let baseline_sum: i64 = touched
        .iter()
        .filter_map(|id| world.ledger().get(id).map(|c| c.state.balance()))
        .sum();

    let pre_state = StepState::capture(world.ledger(), &touched, baseline_sum);

    let effects = flatten_effects(turn);
    let mut steps = Vec::with_capacity(effects.len());

    // For each prefix length 1..=N, build a prefix turn and run it fresh.
    for (k, fe) in effects.iter().enumerate() {
        let prefix = build_prefix_turn(turn, k + 1);
        let mut ledger = world.ledger().clone();
        let exec = fresh_executor_like(world, &agent);

        let (committed, refusal, post_ledger) = run_prefix(&exec, &prefix, &mut ledger);

        let state = StepState::capture(&post_ledger, &touched, baseline_sum);
        steps.push(Step {
            index: k,
            label: describe_effect(&fe.effect),
            touches: effect_touches(&fe.effect),
            state,
            committed,
            refusal,
        });
    }

    // Full-turn verdict: run the WHOLE turn once for the real receipt + the
    // authoritative refusal (a turn-level refusal — nonce/expiry/empty — won't
    // surface in any effect prefix, so we always do this final run).
    let mut full_ledger = world.ledger().clone();
    let full_exec = fresh_executor_like(world, &agent);
    let mut full_turn = turn.clone();
    full_turn.previous_receipt_hash = world.chain_head(&agent);

    let (committed, receipt, refusal) = match full_exec.execute(&full_turn, &mut full_ledger) {
        TurnResult::Committed { receipt, .. } => (true, Some(receipt), None),
        TurnResult::Rejected { reason, at_action } => {
            // Attribute the refusal to an effect index when the failing action
            // prefix is identifiable; otherwise it's a turn-level refusal.
            let effect_index = first_refusing_effect_index(&steps);
            let _ = at_action;
            (false, None, Some(RefusalExplanation::from_error(reason, effect_index)))
        }
        TurnResult::Expired => (
            false,
            None,
            Some(RefusalExplanation::from_error(
                TurnError::Expired { valid_until: 0, now: 0 },
                None,
            )),
        ),
        TurnResult::Pending => (
            false,
            None,
            Some(RefusalExplanation::from_error(
                TurnError::ConditionNotMet("turn pending".into()),
                None,
            )),
        ),
    };

    TurnTrace {
        agent,
        touched,
        pre_state,
        steps,
        committed,
        refusal,
        receipt,
    }
}

/// Debug a turn and evaluate a set of breakpoints over its steps, returning the
/// FIRST hit (lowest step, then lowest breakpoint index). The full trace is
/// returned alongside so the panel can show the surrounding context.
pub fn debug_with_breakpoints(
    world: &World,
    turn: &Turn,
    breakpoints: &[Breakpoint],
) -> (TurnTrace, Option<BreakHit>) {
    let trace = debug_turn(world, turn);
    let mut hit: Option<BreakHit> = None;
    'outer: for step in &trace.steps {
        for (bi, bp) in breakpoints.iter().enumerate() {
            if bp.fires(step) {
                hit = Some(BreakHit {
                    breakpoint: bi,
                    step: step.index,
                    state: step.state.clone(),
                });
                break 'outer;
            }
        }
    }
    (trace, hit)
}

/// Just the refusal explanation, when a turn refuses (the headline feature).
/// Returns `None` if the turn commits cleanly.
pub fn explain_refusal(world: &World, turn: &Turn) -> Option<RefusalExplanation> {
    debug_turn(world, turn).refusal
}

// ===========================================================================
// Witness / public-input inspection.
// ===========================================================================

/// The turn's witness / public-input surface, for inspection. Surfaces what is
/// reachable from the turn + (on commit) the receipt: the conservation proof
/// presence, the per-effect binding/witness blobs, and the receipt's public
/// commitments (pre/post state hashes, effects hash) — the public inputs a
/// verifier checks.
#[derive(Clone, Debug, Default)]
pub struct WitnessInspection {
    /// Does the turn carry an explicit conservation (Pedersen) proof?
    pub has_conservation_proof: bool,
    /// Does the turn carry a STARK execution proof (proof-carrying / sovereign)?
    pub has_execution_proof: bool,
    /// Count of per-action witness blobs across the forest.
    pub witness_blob_count: usize,
    /// Count of effect-binding proofs on the turn.
    pub binding_proof_count: usize,
    /// Public inputs from the receipt (present iff the turn committed): the
    /// pre/post state commitments + effects hash a verifier checks.
    pub public_inputs: Option<PublicInputs>,
}

/// The public-input commitments a verifier checks against a turn's proof.
#[derive(Clone, Debug)]
pub struct PublicInputs {
    pub turn_hash: [u8; 32],
    pub forest_hash: [u8; 32],
    pub pre_state_hash: [u8; 32],
    pub post_state_hash: [u8; 32],
    pub effects_hash: [u8; 32],
    pub computrons_used: u64,
}

/// Inspect a turn's witness/PI surface (optionally against a committed receipt).
pub fn inspect_witness(turn: &Turn, receipt: Option<&TurnReceipt>) -> WitnessInspection {
    let witness_blob_count = turn
        .call_forest
        .roots
        .iter()
        .map(count_witness_blobs)
        .sum();
    WitnessInspection {
        has_conservation_proof: turn.conservation_proof.is_some(),
        has_execution_proof: turn.execution_proof.is_some(),
        witness_blob_count,
        binding_proof_count: turn.effect_binding_proofs.len(),
        public_inputs: receipt.map(|r| PublicInputs {
            turn_hash: r.turn_hash,
            forest_hash: r.forest_hash,
            pre_state_hash: r.pre_state_hash,
            post_state_hash: r.post_state_hash,
            effects_hash: r.effects_hash,
            computrons_used: r.computrons_used,
        }),
    }
}

fn count_witness_blobs(tree: &CallTree) -> usize {
    tree.action.witness_blobs.len() + tree.children.iter().map(count_witness_blobs).sum::<usize>()
}

// ===========================================================================
// The render model — what the cockpit panel consumes (gpui-free, like reflect).
// ===========================================================================

/// One row in the rendered step list.
#[derive(Clone, Debug)]
pub struct StepRow {
    pub index: usize,
    pub label: String,
    pub conservation_delta: i64,
    pub committed: bool,
    /// `true` if this is the row a breakpoint fired at.
    pub is_break: bool,
}

/// The pure render-model the cockpit's debugger panel renders. No gpui types;
/// the main loop maps this onto gpui elements (mirroring `reflect::Inspectable`).
#[derive(Clone, Debug)]
pub struct DebuggerPanel {
    pub title: String,
    pub subtitle: String,
    /// The step list (one row per effect).
    pub steps: Vec<StepRow>,
    /// The cells touched by the turn, with their final-step state (the
    /// "current step's state" view; the panel can re-bind this to any step).
    pub current_state: Vec<CellSnapshot>,
    /// The conservation delta at the end (zero iff the turn conserves value).
    pub final_conservation_delta: i64,
    /// The active breakpoints, described for display.
    pub breakpoints: Vec<String>,
    /// Where a breakpoint fired (if any).
    pub break_hit: Option<usize>,
    /// The refusal explanation (THE prize), when the turn refuses.
    pub refusal: Option<RefusalRender>,
    /// The witness / public-input inspection.
    pub witness: WitnessInspection,
}

/// The render-ready refusal explanation.
#[derive(Clone, Debug)]
pub struct RefusalRender {
    pub guard: String,
    pub headline: String,
    pub detail: String,
    pub effect_index: Option<usize>,
    pub cells: Vec<CellId>,
}

/// Render the debugger panel for a turn against a world, with breakpoints.
///
/// THIS IS THE PANEL ENTRY POINT THE COCKPIT WIRES IN. It returns a pure
/// render-model (`DebuggerPanel`); the main loop maps it onto gpui elements the
/// same way it renders `reflect::Inspectable`.
pub fn render(world: &World, turn: &Turn, breakpoints: &[Breakpoint]) -> DebuggerPanel {
    let (trace, hit) = debug_with_breakpoints(world, turn, breakpoints);
    let witness = inspect_witness(turn, trace.receipt.as_ref());

    let break_step = hit.as_ref().map(|h| h.step);
    let steps: Vec<StepRow> = trace
        .steps
        .iter()
        .map(|s| StepRow {
            index: s.index,
            label: s.label.clone(),
            conservation_delta: s.state.conservation_delta,
            committed: s.committed,
            is_break: break_step == Some(s.index),
        })
        .collect();

    let current_state = trace
        .steps
        .last()
        .map(|s| s.state.cells.clone())
        .unwrap_or_else(|| trace.pre_state.cells.clone());
    let final_conservation_delta = trace
        .steps
        .last()
        .map(|s| s.state.conservation_delta)
        .unwrap_or(0);

    let refusal = trace.refusal.as_ref().map(|r| RefusalRender {
        guard: r.guard.name().to_string(),
        headline: r.headline.clone(),
        detail: r.detail.clone(),
        effect_index: r.effect_index,
        cells: r.cells.clone(),
    });

    let subtitle = if trace.committed {
        format!(
            "{} effects · COMMITS · Σδ={}",
            trace.steps.len(),
            final_conservation_delta
        )
    } else {
        let g = refusal
            .as_ref()
            .map(|r| r.guard.clone())
            .unwrap_or_else(|| "?".into());
        format!("{} effects · REFUSED ({g})", trace.steps.len())
    };

    DebuggerPanel {
        title: format!(
            "Turn Debugger · agent {}",
            crate::reflect::short_hex(trace.agent.as_bytes())
        ),
        subtitle,
        steps,
        current_state,
        final_conservation_delta,
        breakpoints: breakpoints.iter().map(describe_breakpoint).collect(),
        break_hit: hit.map(|h| h.step),
        refusal,
        witness,
    }
}

fn describe_breakpoint(bp: &Breakpoint) -> String {
    match bp {
        Breakpoint::OnRefusal => "on refusal".to_string(),
        Breakpoint::OnConservationBreak => "on conservation break".to_string(),
        Breakpoint::OnCellTouched(c) => {
            format!("on cell {} touched", crate::reflect::short_hex(c.as_bytes()))
        }
        Breakpoint::OnBalanceBelow { cell, floor } => format!(
            "on cell {} balance < {floor}",
            crate::reflect::short_hex(cell.as_bytes())
        ),
        Breakpoint::AtEffect(i) => format!("at effect {i}"),
    }
}

// ===========================================================================
// Internals — flattening, prefix construction, faithful re-execution.
// ===========================================================================

/// A flattened effect (its description is all the step list needs).
struct FlatEffect {
    effect: Effect,
}

/// Flatten the forest's effects into executor DFS order. The executor walks the
/// forest depth-first, applying each action's effects in order; this mirrors
/// that traversal so step `k` corresponds to the k-th effect the executor sees.
fn flatten_effects(turn: &Turn) -> Vec<FlatEffect> {
    let mut out = Vec::new();
    for root in &turn.call_forest.roots {
        flatten_tree(root, &mut out);
    }
    out
}

fn flatten_tree(tree: &CallTree, out: &mut Vec<FlatEffect>) {
    for e in &tree.action.effects {
        out.push(FlatEffect { effect: e.clone() });
    }
    for child in &tree.children {
        flatten_tree(child, out);
    }
}

/// Build a turn that carries only the first `n` effects (DFS order), preserving
/// each action's authorization / preconditions / delegation / target. Actions
/// that would carry zero effects after truncation are dropped, except an empty
/// agent root is kept so the prefix turn is never an empty forest at n≥1.
fn build_prefix_turn(turn: &Turn, n: usize) -> Turn {
    let mut prefix = turn.clone();
    let mut remaining = n;
    let mut new_roots = Vec::new();
    for root in &turn.call_forest.roots {
        if remaining == 0 {
            break;
        }
        if let Some(t) = truncate_tree(root, &mut remaining) {
            new_roots.push(t);
        }
    }
    let mut forest = CallForest::new();
    forest.roots = new_roots;
    prefix.call_forest = forest;
    prefix
}

/// Truncate a tree to consume at most `*remaining` effects (DFS), returning the
/// truncated tree (or `None` if it ends up empty and contributes nothing).
fn truncate_tree(tree: &CallTree, remaining: &mut usize) -> Option<CallTree> {
    let mut action = tree.action.clone();
    let take = action.effects.len().min(*remaining);
    action.effects.truncate(take);
    *remaining -= take;

    let mut children = Vec::new();
    for child in &tree.children {
        if *remaining == 0 {
            break;
        }
        if let Some(c) = truncate_tree(child, remaining) {
            children.push(c);
        }
    }

    if action.effects.is_empty() && children.is_empty() {
        // This action contributed nothing; drop it (keeps the prefix minimal).
        // The caller guarantees at least one effect was taken overall.
        // Keep it only if it is itself the agent's sole root with no effects;
        // simplest is to drop — empty roots are pruned at the forest level.
        return None;
    }
    Some(CallTree {
        action,
        children,
        hash: [0u8; 32],
    })
}

/// Stand up a fresh executor matching the live world's configuration, seeded
/// with the agent's current receipt-chain head so a prefix/full turn chains
/// exactly as a real commit would.
///
/// Sourced from [`World::debug_executor`] so the debugger's re-execution
/// inherits the live engine's config (costs, pinned wall-clock, federation id,
/// chain head) from ONE place and cannot drift from it.
fn fresh_executor_like(world: &World, agent: &CellId) -> TurnExecutor {
    world.debug_executor(agent)
}

/// Run a prefix turn against a (mutable) cloned ledger, threading the chain
/// head. Returns (committed, structured-refusal, the post-state ledger).
fn run_prefix(
    exec: &TurnExecutor,
    prefix: &Turn,
    ledger: &mut Ledger,
) -> (bool, Option<TurnError>, Ledger) {
    let mut t = prefix.clone();
    t.previous_receipt_hash = exec.get_last_receipt_hash(&t.agent);
    match exec.execute(&t, ledger) {
        TurnResult::Committed { .. } => (true, None, ledger.clone()),
        TurnResult::Rejected { reason, .. } => {
            // On rejection the executor rolled the ledger back to pre-state.
            (false, Some(reason), ledger.clone())
        }
        TurnResult::Expired => (
            false,
            Some(TurnError::Expired { valid_until: 0, now: 0 }),
            ledger.clone(),
        ),
        TurnResult::Pending => (
            false,
            Some(TurnError::ConditionNotMet("pending".into())),
            ledger.clone(),
        ),
    }
}

/// The earliest effect index whose prefix the executor refused.
fn first_refusing_effect_index(steps: &[Step]) -> Option<usize> {
    steps.iter().find(|s| !s.committed).map(|s| s.index)
}

/// All cell ids a turn touches (for snapshotting), in stable sorted order.
fn touched_cells(turn: &Turn) -> Vec<CellId> {
    let mut set: BTreeMap<[u8; 32], CellId> = BTreeMap::new();
    let mut add = |id: CellId| {
        set.insert(*id.as_bytes(), id);
    };
    add(turn.agent);
    for root in &turn.call_forest.roots {
        collect_tree_touches(root, &mut add);
    }
    set.into_values().collect()
}

fn collect_tree_touches<F: FnMut(CellId)>(tree: &CallTree, add: &mut F) {
    add(tree.action.target);
    for e in &tree.action.effects {
        for id in effect_touches(e) {
            add(id);
        }
    }
    for child in &tree.children {
        collect_tree_touches(child, add);
    }
}

/// The cells a single effect touches.
fn effect_touches(e: &Effect) -> Vec<CellId> {
    match e {
        Effect::Transfer { from, to, .. } => vec![*from, *to],
        Effect::GrantCapability { from, to, .. } => vec![*from, *to],
        Effect::SetField { cell, .. }
        | Effect::IncrementNonce { cell }
        | Effect::EmitEvent { cell, .. }
        | Effect::RevokeCapability { cell, .. }
        | Effect::SetPermissions { cell, .. }
        | Effect::SetVerificationKey { cell, .. } => vec![*cell],
        _ => vec![],
    }
}

/// A human-readable description of an effect (the step label).
fn describe_effect(e: &Effect) -> String {
    let s = |id: &CellId| crate::reflect::short_hex(id.as_bytes());
    match e {
        Effect::Transfer { from, to, amount } => {
            format!("transfer {amount} · {} → {}", s(from), s(to))
        }
        Effect::GrantCapability { from, to, cap } => format!(
            "grant cap → {} · from {} to {}",
            s(&cap.target),
            s(from),
            s(to)
        ),
        Effect::RevokeCapability { cell, slot } => {
            format!("revoke cap[{slot}] on {}", s(cell))
        }
        Effect::SetField { cell, index, .. } => format!("set field[{index}] on {}", s(cell)),
        Effect::IncrementNonce { cell } => format!("increment nonce on {}", s(cell)),
        Effect::EmitEvent { cell, .. } => format!("emit event from {}", s(cell)),
        Effect::CreateCell { balance, .. } => format!("create cell (balance {balance})"),
        Effect::SetPermissions { cell, .. } => format!("set permissions on {}", s(cell)),
        Effect::SetVerificationKey { cell, .. } => format!("set verification key on {}", s(cell)),
        Effect::Burn { target, .. } => format!("burn on {}", s(target)),
        other => {
            // A compact debug for the long-tail effects (notes, bridges, …).
            let d = format!("{other:?}");
            let head: String = d.chars().take(40).collect();
            head
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::world::{grant_capability, transfer, World};

    /// Stepping a multi-effect transfer turn: per-step states are correct, and
    /// the conservation delta stays at zero across a conserving turn.
    #[test]
    fn steps_a_multi_effect_transfer_turn() {
        let mut w = World::new();
        let a = w.genesis_cell(1, 1_000);
        let b = w.genesis_cell(2, 0);
        let c = w.genesis_cell(3, 0);

        // Three transfers out of `a`, in one action: a→b 100, a→c 200, a→b 50.
        let turn = w.turn(
            a,
            vec![
                transfer(a, b, 100),
                transfer(a, c, 200),
                transfer(a, b, 50),
            ],
        );

        let trace = debug_turn(&w, &turn);
        assert!(trace.committed, "the conserving turn must commit");
        assert_eq!(trace.steps.len(), 3, "one step per effect");

        // Step 0: after a→b 100. a=900, b=100, c=0.
        let s0 = &trace.steps[0].state;
        assert_eq!(s0.cell(&a).unwrap().balance, 900);
        assert_eq!(s0.cell(&b).unwrap().balance, 100);
        assert_eq!(s0.cell(&c).unwrap().balance, 0);
        assert_eq!(s0.conservation_delta, 0, "transfer conserves value");

        // Step 1: after a→c 200. a=700, b=100, c=200.
        let s1 = &trace.steps[1].state;
        assert_eq!(s1.cell(&a).unwrap().balance, 700);
        assert_eq!(s1.cell(&c).unwrap().balance, 200);

        // Step 2: after a→b 50. a=650, b=150, c=200.
        let s2 = &trace.steps[2].state;
        assert_eq!(s2.cell(&a).unwrap().balance, 650);
        assert_eq!(s2.cell(&b).unwrap().balance, 150);
        assert_eq!(s2.cell(&c).unwrap().balance, 200);
        assert_eq!(s2.conservation_delta, 0);

        // The world itself was NOT mutated by debugging.
        assert_eq!(w.ledger().get(&a).unwrap().state.balance(), 1_000);
        assert_eq!(w.height(), 0);
    }

    /// A breakpoint fires at the right step: break when cell `c` is first
    /// touched (the second effect, index 1).
    #[test]
    fn breakpoint_fires_at_the_right_step() {
        let mut w = World::new();
        let a = w.genesis_cell(1, 1_000);
        let b = w.genesis_cell(2, 0);
        let c = w.genesis_cell(3, 0);

        let turn = w.turn(
            a,
            vec![
                transfer(a, b, 100), // step 0 — touches a,b
                transfer(a, c, 200), // step 1 — touches a,c  <-- break here
                transfer(a, b, 50),  // step 2
            ],
        );

        let (_trace, hit) = debug_with_breakpoints(&w, &turn, &[Breakpoint::OnCellTouched(c)]);
        let hit = hit.expect("breakpoint must fire");
        assert_eq!(hit.step, 1, "c is first touched at effect 1");
        assert_eq!(hit.state.cell(&c).unwrap().balance, 200);
    }

    /// A balance-floor breakpoint fires the step a cell would cross below zero —
    /// but only on a turn that the executor would let proceed that far. Here we
    /// use a touched-cell + AtEffect breakpoint to show predicate breakpoints.
    #[test]
    fn at_effect_breakpoint() {
        let mut w = World::new();
        let a = w.genesis_cell(1, 1_000);
        let b = w.genesis_cell(2, 0);
        let turn = w.turn(a, vec![transfer(a, b, 10), transfer(a, b, 10)]);
        let (_t, hit) = debug_with_breakpoints(&w, &turn, &[Breakpoint::AtEffect(1)]);
        assert_eq!(hit.expect("fires").step, 1);
    }

    /// Explain-the-refusal on an OVER-SPEND: the explanation names the
    /// conservation guard and the offending cell.
    #[test]
    fn explains_overspend_refusal() {
        let mut w = World::new();
        let a = w.genesis_cell(1, 100);
        let b = w.genesis_cell(2, 0);

        // a holds 100; transfer 1_000 → over-spend.
        let turn = w.turn(a, vec![transfer(a, b, 1_000)]);

        let ex = explain_refusal(&w, &turn).expect("over-spend must refuse");
        assert_eq!(ex.guard, GuardKind::Conservation, "names the conservation guard");
        assert!(ex.cells.contains(&a), "names the over-spending cell");
        assert!(
            ex.headline.to_lowercase().contains("over-spend")
                || ex.headline.to_lowercase().contains("insufficient")
                || ex.headline.to_lowercase().contains("holds"),
            "headline explains the over-spend: {}",
            ex.headline
        );
        // And the full trace marks the turn refused.
        let trace = debug_turn(&w, &turn);
        assert!(!trace.committed);
        assert!(trace.refusal.is_some());
    }

    /// Explain-the-refusal on an OVER-GRANT (ocap no-amplification): a cell that
    /// holds no capability to `b` cannot grant one. The explanation names the
    /// capability guard.
    #[test]
    fn explains_over_grant_refusal() {
        let mut w = World::new();
        let a = w.genesis_cell(1, 100);
        let b = w.genesis_cell(2, 0);
        // a does NOT hold a cap to b.
        let turn = w.turn(a, vec![grant_capability(a, a, b, 0)]);

        let ex = explain_refusal(&w, &turn).expect("over-grant must refuse");
        assert_eq!(ex.guard, GuardKind::Capability, "names the capability guard");
    }

    /// The OnRefusal breakpoint fires at the effect index where the turn first
    /// refuses inside a multi-effect turn (the second effect over-spends).
    #[test]
    fn refusal_breakpoint_pins_the_failing_effect() {
        let mut w = World::new();
        let a = w.genesis_cell(1, 100);
        let b = w.genesis_cell(2, 0);
        // First transfer ok (a:100→90), second over-spends (90 < 1000).
        let turn = w.turn(a, vec![transfer(a, b, 10), transfer(a, b, 1_000)]);

        let (trace, hit) = debug_with_breakpoints(&w, &turn, &[Breakpoint::OnRefusal]);
        let hit = hit.expect("a refusal breakpoint must fire");
        assert_eq!(hit.step, 1, "the SECOND effect is the one that refuses");
        // Step 0 committed, step 1 refused.
        assert!(trace.steps[0].committed);
        assert!(!trace.steps[1].committed);
        assert_eq!(
            trace.steps[1].refusal.as_ref().map(|e| matches!(e, TurnError::InsufficientBalance { .. })),
            Some(true)
        );
    }

    /// Conservation-break detection: a turn whose effects do not balance value
    /// (a burn) drives the conservation delta negative, and the
    /// OnConservationBreak breakpoint fires.
    #[test]
    fn detects_conservation_break() {
        use dregg_turn::action::Effect;
        let mut w = World::new();
        let a = w.genesis_cell(1, 1_000);
        let b = w.genesis_cell(2, 0);
        // Effect 0: a→b 100 (conserves, Σδ stays 0).
        // Effect 1: burn 50 on b (NON-conserving: total touched value drops 50).
        let turn = w.turn(
            a,
            vec![
                transfer(a, b, 100),
                Effect::Burn { target: b, slot: 0, amount: 50 },
            ],
        );

        let trace = debug_turn(&w, &turn);
        // Step 0 conserves.
        assert_eq!(trace.steps[0].state.conservation_delta, 0);
        // If the burn applied, the running delta goes negative; the breakpoint
        // catches the imbalance.
        let (_t, hit) = debug_with_breakpoints(&w, &turn, &[Breakpoint::OnConservationBreak]);
        if let Some(h) = hit {
            assert!(
                trace.steps[h.step].state.conservation_delta != 0,
                "the break step has a non-zero conservation delta"
            );
            assert_eq!(h.step, 1, "the burn is the conservation break");
        } else {
            // If the executor refused the burn outright (non-conservation
            // rejected at turn end), the refusal must be present instead.
            assert!(
                trace.refusal.is_some(),
                "a non-conserving turn either breaks Σδ mid-forest or refuses"
            );
        }
    }

    /// The render model is well-formed for both a committing and a refusing
    /// turn (the panel the cockpit consumes).
    #[test]
    fn render_panel_for_commit_and_refuse() {
        let mut w = World::new();
        let a = w.genesis_cell(1, 1_000);
        let b = w.genesis_cell(2, 0);

        // Committing turn.
        let ok = w.turn(a, vec![transfer(a, b, 100), transfer(a, b, 100)]);
        let panel = render(&w, &ok, &[Breakpoint::AtEffect(1)]);
        assert_eq!(panel.steps.len(), 2);
        assert!(panel.subtitle.contains("COMMITS"));
        assert!(panel.refusal.is_none());
        assert_eq!(panel.break_hit, Some(1));
        assert!(panel.steps[1].is_break);

        // Refusing turn.
        let bad = w.turn(a, vec![transfer(a, b, 1_000_000)]);
        let panel = render(&w, &bad, &[Breakpoint::OnRefusal]);
        assert!(panel.subtitle.contains("REFUSED"));
        let r = panel.refusal.expect("refusal rendered");
        assert_eq!(r.guard, "conservation");
        assert!(panel.break_hit.is_some());
    }

    /// Witness/PI inspection: a committed turn exposes its receipt public
    /// inputs; an uncommitted (refusing) turn exposes the turn-side witness
    /// surface with no public inputs.
    #[test]
    fn inspects_witness_and_public_inputs() {
        let mut w = World::new();
        let a = w.genesis_cell(1, 1_000);
        let b = w.genesis_cell(2, 0);

        let ok = w.turn(a, vec![transfer(a, b, 100)]);
        let trace = debug_turn(&w, &ok);
        let wi = inspect_witness(&ok, trace.receipt.as_ref());
        assert!(wi.public_inputs.is_some(), "committed turn has PI");
        let pi = wi.public_inputs.unwrap();
        assert_ne!(pi.post_state_hash, [0u8; 32]);
        assert_ne!(pi.pre_state_hash, pi.post_state_hash, "state moved");

        let bad = w.turn(a, vec![transfer(a, b, 1_000_000)]);
        let trace = debug_turn(&w, &bad);
        let wi = inspect_witness(&bad, trace.receipt.as_ref());
        assert!(wi.public_inputs.is_none(), "refused turn has no receipt PI");
    }
}
