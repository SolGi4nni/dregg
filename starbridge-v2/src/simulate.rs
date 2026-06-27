//! WHAT-IF SIMULATION — compose any intent over any cell, predict its
//! consequences in a FORKED throwaway world, then commit it for real.
//!
//! site/studio's Playground has exhaustive protocol coverage but no live
//! executor; starbridge-v2's COMPOSER drives the REAL embedded executor but only
//! a fixed handful of demo verbs, and it commits immediately. This module closes
//! that gap: an **exhaustive intent builder** ([`IntentDraft`]) over a broad set
//! of protocol effects ([`EffectKind`]) against ANY cell(s) in the live image,
//! plus a **fork-and-simulate** engine ([`simulate`]) that runs the composed turn
//! through a [`World::fork`] — a deep copy of the live world running the SAME
//! verified executor — to show the PREDICTED post-state, the PREDICTED receipt,
//! and any REFUSAL, all WITHOUT committing. Only when the operator presses commit
//! does [`commit`] run the IDENTICAL turn on the live world.
//!
//! The prediction is REAL, not a model: the fork carries a clone of the live
//! ledger + the same factory registry + the same per-agent chain heads, so its
//! executor applies the identical conservation / ocap / program / lifecycle
//! guarantees — and (same timestamp + same pre-state) yields the byte-identical
//! receipt the live commit would. A bad intent (overspend, over-grant, a sealed-
//! cell write, a malformed forest) is REFUSED in the fork with the executor's own
//! reason — the operator sees the refusal before paying for it. The
//! [`SimOutcome::committed`] / [`SimOutcome::refused`] distinction the panel shows
//! is the live executor's verdict, run one turn ahead.
//!
//! gpui-free + `cargo test`-able: this is the simulation HEART; the cockpit's
//! panel ([`crate::cockpit`]) is a thin view over it.

use dregg_cell::{lifecycle::DeathReason, AuthRequired, CellId, FieldElement, Permissions};
use dregg_turn::{
    action::Effect,
    turn::{Turn, TurnReceipt},
};

use crate::dynamics::WorldEvent;
use crate::edit::{self, Verdict};
use crate::world::{self, CommitOutcome, World};

// ===========================================================================
// THE EFFECT PALETTE — the broad set of protocol effects an intent can compose.
//
// Coverage is the "studio-parity" ask: every effect the single-custody embedded
// world can run WITHOUT an out-of-band proof/witness (Transfer · grant/revoke
// capability · emit event · increment nonce · create cell · set field · set
// permissions · make sovereign · the lifecycle quartet seal/unseal/destroy/burn ·
// factory birth). The proof-bearing effects (NoteSpend/NoteCreate/BridgeMint/…)
// need witnesses that have no meaning in a single-custody simulate panel, so they
// are deliberately out of scope here (the panel says so honestly rather than
// offering a button that can only ever reject).
// ===========================================================================

/// One composable effect kind + the parameters it carries. Each variant maps to
/// exactly one `dregg_turn::action::Effect` via [`EffectKind::to_effect`]; the
/// `acting` cell is the action's target (the cell exercising the effect).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EffectKind {
    /// Move `amount` computrons `from` → `to` (conservation-checked).
    Transfer { to: CellId, amount: u64 },
    /// Grant `to` a capability reaching `target` at `slot` (the ocap edge; the
    /// executor's no-amplification rule gates it — you can only grant what you
    /// hold).
    GrantCapability {
        to: CellId,
        target: CellId,
        slot: u32,
    },
    /// Revoke the capability at `slot` on the acting cell.
    RevokeCapability { slot: u32 },
    /// Emit an event with `topic` (BLAKE3'd to the 32-byte symbol) on the cell.
    EmitEvent { topic: String },
    /// Bump the acting cell's nonce.
    IncrementNonce,
    /// Birth a fresh cell from `seed` (born with zero balance — value only moves).
    CreateCell { seed: u8 },
    /// Write `value` into state slot `index` of the acting cell (a deployed
    /// program may reject it — that is the point of simulating first).
    SetField { index: usize, value: FieldElement },
    /// Replace the acting cell's permissions with the open (gating-nothing) set.
    SetPermissionsOpen,
    /// Transition the acting (hosted) cell to sovereign mode.
    MakeSovereign,
    /// Seal the acting cell with a commitment to `reason` (lifecycle).
    Seal { reason: String },
    /// Unseal the acting cell (rejected by the executor if not currently sealed).
    Unseal,
    /// Permanently retire the acting cell (terminal — later effects reject).
    Destroy,
    /// Provably reduce the acting cell's balance by `amount`, no credited dest.
    Burn { amount: u64 },
    /// Birth a child cell from a deployed factory `factory_vk` with `owner` pubkey.
    CreateCellFromFactory {
        factory_vk: [u8; 32],
        owner: [u8; 32],
    },
}

impl EffectKind {
    /// A short, human label for the picker (the effect's name + its salient args).
    pub fn label(&self) -> String {
        match self {
            EffectKind::Transfer { to, amount } => {
                format!("Transfer {amount} → {}", world::short(to))
            }
            EffectKind::GrantCapability { to, target, slot } => format!(
                "GrantCapability → {} (reaches {}, slot {slot})",
                world::short(to),
                world::short(target)
            ),
            EffectKind::RevokeCapability { slot } => format!("RevokeCapability slot {slot}"),
            EffectKind::EmitEvent { topic } => format!("EmitEvent \"{topic}\""),
            EffectKind::IncrementNonce => "IncrementNonce".into(),
            EffectKind::CreateCell { seed } => format!("CreateCell (seed {seed:#04x})"),
            EffectKind::SetField { index, .. } => format!("SetField slot {index}"),
            EffectKind::SetPermissionsOpen => "SetPermissions (open)".into(),
            EffectKind::MakeSovereign => "MakeSovereign".into(),
            EffectKind::Seal { reason } => format!("Seal (\"{reason}\")"),
            EffectKind::Unseal => "Unseal".into(),
            EffectKind::Destroy => "Destroy".into(),
            EffectKind::Burn { amount } => format!("Burn {amount}"),
            EffectKind::CreateCellFromFactory { .. } => "CreateCellFromFactory".into(),
        }
    }

    /// The short protocol name (for grouping / coverage display).
    pub fn kind_name(&self) -> &'static str {
        match self {
            EffectKind::Transfer { .. } => "Transfer",
            EffectKind::GrantCapability { .. } => "GrantCapability",
            EffectKind::RevokeCapability { .. } => "RevokeCapability",
            EffectKind::EmitEvent { .. } => "EmitEvent",
            EffectKind::IncrementNonce => "IncrementNonce",
            EffectKind::CreateCell { .. } => "CreateCell",
            EffectKind::SetField { .. } => "SetField",
            EffectKind::SetPermissionsOpen => "SetPermissions",
            EffectKind::MakeSovereign => "MakeSovereign",
            EffectKind::Seal { .. } => "CellSeal",
            EffectKind::Unseal => "CellUnseal",
            EffectKind::Destroy => "CellDestroy",
            EffectKind::Burn { .. } => "Burn",
            EffectKind::CreateCellFromFactory { .. } => "CreateCellFromFactory",
        }
    }

    /// Lower into the real `dregg_turn::action::Effect`, given the `acting` cell
    /// (the action's target — the cell exercising the effect). `height` is the
    /// world's current height (the `Destroy` certificate binds it).
    pub fn to_effect(&self, acting: CellId, height: u64) -> Effect {
        match self {
            EffectKind::Transfer { to, amount } => world::transfer(acting, *to, *amount),
            EffectKind::GrantCapability { to, target, slot } => {
                world::grant_capability(acting, *to, *target, *slot)
            }
            EffectKind::RevokeCapability { slot } => world::revoke_capability(acting, *slot),
            EffectKind::EmitEvent { topic } => world::emit_event(acting, topic, vec![]),
            EffectKind::IncrementNonce => Effect::IncrementNonce { cell: acting },
            EffectKind::CreateCell { seed } => world::create_cell(*seed),
            EffectKind::SetField { index, value } => world::set_field(acting, *index, *value),
            EffectKind::SetPermissionsOpen => Effect::SetPermissions {
                cell: acting,
                new_permissions: open_permissions_value(),
            },
            EffectKind::MakeSovereign => Effect::MakeSovereign { cell: acting },
            EffectKind::Seal { reason } => world::seal(acting, reason),
            EffectKind::Unseal => world::unseal(acting),
            EffectKind::Destroy => world::destroy(acting, height, DeathReason::Voluntary),
            EffectKind::Burn { amount } => world::burn(acting, *amount),
            EffectKind::CreateCellFromFactory { factory_vk, owner } => {
                world::create_cell_from_factory(
                    *factory_vk,
                    *owner,
                    [0u8; 32],
                    dregg_cell::factory::FactoryCreationParams {
                        mode: dregg_cell::CellMode::Hosted,
                        program_vk: None,
                        initial_fields: vec![],
                        initial_caps: vec![],
                        owner_pubkey: *owner,
                    },
                )
            }
        }
    }
}

/// The open (gating-nothing) permissions value — re-derived here so `SetPermissions`
/// can carry it (the `world` module's `open_permissions` is the same set).
fn open_permissions_value() -> Permissions {
    Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    }
}

// ===========================================================================
// THE INTENT DRAFT — compose any intent over any cell(s).
// ===========================================================================

/// One action in the draft: a target cell + the effects it exercises. The
/// composer adds these; the whole draft becomes ONE atomic turn (the executor
/// commits the whole forest or refuses it).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DraftAction {
    /// The cell this action acts on (the action's target / acting cell).
    pub target: CellId,
    /// The effects this action exercises, in order.
    pub effects: Vec<EffectKind>,
}

/// An operator's in-progress intent: the agent that authorizes it + a forest of
/// actions. Built incrementally in the panel (pick the agent, add actions, add
/// effects), then simulated and — if desired — committed. The single-custody
/// embedded world authorizes through the operator path (`World::turn` /
/// `forest_turn`), so the draft carries no signatures; the cells' `Permissions`
/// and the executor's whole-turn guarantees still gate every effect.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IntentDraft {
    /// The agent cell that submits the turn (its nonce + chain head are threaded).
    pub agent: CellId,
    /// The actions composing the turn (sibling roots in the call-forest).
    pub actions: Vec<DraftAction>,
}

impl IntentDraft {
    /// A fresh draft from `agent` with no actions yet.
    pub fn new(agent: CellId) -> Self {
        IntentDraft {
            agent,
            actions: Vec::new(),
        }
    }

    /// Append a new action acting on `target` (with no effects yet). Returns its
    /// index so the caller can hang effects on it.
    pub fn add_action(&mut self, target: CellId) -> usize {
        self.actions.push(DraftAction {
            target,
            effects: Vec::new(),
        });
        self.actions.len() - 1
    }

    /// Append an effect to the action at `action_index` (no-op if out of range).
    pub fn add_effect(&mut self, action_index: usize, effect: EffectKind) {
        if let Some(a) = self.actions.get_mut(action_index) {
            a.effects.push(effect);
        }
    }

    /// Remove the action at `index` (e.g. the panel's per-row delete).
    pub fn remove_action(&mut self, index: usize) {
        if index < self.actions.len() {
            self.actions.remove(index);
        }
    }

    /// Total composed effects across all actions (for the panel summary).
    pub fn effect_count(&self) -> usize {
        self.actions.iter().map(|a| a.effects.len()).sum()
    }

    /// `true` iff the draft has at least one effect to run.
    pub fn is_empty(&self) -> bool {
        self.effect_count() == 0
    }

    /// Build the real `Turn` this draft represents against `world` (threading the
    /// agent's nonce + chain head via `World::forest_turn`). The SAME `Turn` is
    /// what both [`simulate`] (on a fork) and [`commit`] (on the live world) run —
    /// so the prediction and the real commit are the identical turn.
    pub fn build_turn(&self, world: &World) -> Turn {
        let height = world.height();
        let actions: Vec<(CellId, Vec<Effect>)> = self
            .actions
            .iter()
            .map(|a| {
                (
                    a.target,
                    a.effects
                        .iter()
                        .map(|e| e.to_effect(a.target, height))
                        .collect(),
                )
            })
            .collect();
        world.forest_turn(self.agent, actions)
    }

    /// The authored `CallForest` (for the static validation rail — same shape the
    /// editor's [`edit::validate`] consumes). Mirrors [`Self::build_turn`]'s
    /// lowering so the static verdict is over exactly the turn that runs.
    fn build_forest(&self, height: u64) -> dregg_turn::forest::CallForest {
        let mut fb = edit::ForestBuilder::new();
        for a in &self.actions {
            let effects: Vec<Effect> = a
                .effects
                .iter()
                .map(|e| e.to_effect(a.target, height))
                .collect();
            fb.root(edit::ActionBuilder::new(a.target).effects(effects));
        }
        fb.build()
    }
}

// ===========================================================================
// THE PREDICTED OUTCOME — a per-cell delta + the receipt OR the refusal.
// ===========================================================================

/// A predicted change to one cell, observed in the fork (pre vs. post the
/// simulated turn). `before == None` means the cell did not exist before (a
/// birth); the panel renders these as the what-if's effect on the image.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CellDelta {
    pub cell: CellId,
    /// Balance before the simulated turn (`None` = the cell was born by it).
    pub before: Option<i64>,
    /// Balance after the simulated turn (`None` = the cell was retired by it).
    pub after: Option<i64>,
    /// `true` iff the cell exists in the post-state (so the panel can mark births
    /// and retirements distinctly from a balance move).
    pub exists_after: bool,
}

impl CellDelta {
    /// `true` iff the balance actually moved (the salient case to highlight).
    pub fn balance_changed(&self) -> bool {
        self.before != self.after
    }
}

/// The outcome of a what-if simulation: the STATIC verdict (the userspace rail)
/// plus the DYNAMIC executor verdict run in the fork — either the predicted
/// receipt + the per-cell deltas + the dynamics it would emit, or the refusal
/// reason. This is the live executor's verdict, one turn ahead, with the live
/// world untouched.
pub enum SimOutcome {
    /// The fork's executor COMMITTED the turn — here is what WOULD happen live.
    Predicted {
        /// The static assurance verdict (necessary, not sufficient — here it
        /// passed AND the dynamic executor accepted).
        verdict: Verdict,
        /// The predicted receipt (byte-identical to the live commit's — same
        /// timestamp + same pre-state).
        receipt: Box<TurnReceipt>,
        /// Per-cell predicted deltas (touched cells + any births/retirements).
        deltas: Vec<CellDelta>,
        /// The dynamics events the turn would emit (the live transition story).
        events: Vec<WorldEvent>,
        /// Predicted change to the total cell count (births − retirements).
        cell_count_delta: i64,
        /// The fork's predicted image root after the turn (the new commitment).
        predicted_root: [u8; 32],
    },
    /// The fork's executor REFUSED the turn — the guarantee that WOULD fire live,
    /// surfaced BEFORE any gas is spent. Carries the executor's own reason +
    /// the static verdict (which may itself have caught it pre-submission).
    Refused {
        /// The static verdict (may already carry the finding, or may pass while
        /// the dynamic executor is what refuses).
        verdict: Verdict,
        /// The executor's refusal reason (the dynamic guarantee firing), or the
        /// static-rail refusal if it never reached the executor.
        reason: String,
        /// The action path the executor pinned the refusal to (if any).
        at_action: Vec<usize>,
        /// `true` iff the static rail (not the dynamic executor) was the refuser
        /// — i.e. the turn was caught before submission (no fork run needed).
        static_refusal: bool,
    },
}

impl SimOutcome {
    /// `true` iff the simulated turn WOULD commit live.
    pub fn would_commit(&self) -> bool {
        matches!(self, SimOutcome::Predicted { .. })
    }

    /// The static verdict either arm carries.
    pub fn verdict(&self) -> &Verdict {
        match self {
            SimOutcome::Predicted { verdict, .. } => verdict,
            SimOutcome::Refused { verdict, .. } => verdict,
        }
    }
}

// ===========================================================================
// SIMULATE — fork the world, run the turn, predict the consequences.
// ===========================================================================

/// **Predict an intent's consequences WITHOUT committing.**
///
/// 1. Run the static assurance rail ([`edit::validate`]) over the authored
///    forest. If it fails, REFUSE immediately as a [`SimOutcome::Refused`] with
///    `static_refusal: true` — the malformed/amplifying/non-conserving intent is
///    caught before even forking (exactly the editor's pre-submission rail).
/// 2. Otherwise [`World::fork`] the live world (a deep copy running the SAME
///    verified executor), snapshot the pre-state balances of the cells the turn
///    touches, and run the turn through the fork's [`World::commit_turn`].
/// 3. On the fork's commit, read back the predicted receipt + the per-cell
///    deltas (pre vs. fork-post) + the dynamics it emitted + the predicted image
///    root → [`SimOutcome::Predicted`]. On the fork's rejection, surface the
///    executor's reason → [`SimOutcome::Refused`] (`static_refusal: false`).
///
/// The live `world` is `&` — it is NEVER mutated. The prediction is the live
/// executor's real verdict, run one turn ahead on a throwaway copy.
pub fn simulate(world: &World, draft: &IntentDraft) -> SimOutcome {
    // (1) The static rail — caught here means never submitted (no fork needed).
    let forest = draft.build_forest(world.height());
    let verdict = edit::validate(&forest);
    if !verdict.pass() {
        let n = verdict.all().len();
        return SimOutcome::Refused {
            reason: format!(
                "static assurance rail caught {n} finding(s) — refused BEFORE submission \
                 (no gas, no fork): {}",
                verdict
                    .all()
                    .iter()
                    .map(|f| format!("[{}] {}", f.guarantee, f.message))
                    .collect::<Vec<_>>()
                    .join("; ")
            ),
            at_action: vec![],
            verdict,
            static_refusal: true,
        };
    }

    // (2) Fork the live world and run the SAME turn on the copy.
    let mut fork = world.fork();
    let turn = draft.build_turn(world);
    let touched = touched_cells(&turn);

    // Snapshot pre-state balances (None = the cell does not exist pre).
    let pre: Vec<(CellId, Option<i64>)> = touched
        .iter()
        .map(|id| (*id, fork.ledger().get(id).map(|c| c.state.balance())))
        .collect();
    let count_before = fork.cell_count();

    match fork.commit_turn(turn) {
        CommitOutcome::Committed { receipt, events } => {
            // (3) Read back the predicted deltas from the fork's post-state.
            let mut deltas: Vec<CellDelta> = pre
                .iter()
                .map(|(id, before)| {
                    let after_cell = fork.ledger().get(id);
                    CellDelta {
                        cell: *id,
                        before: *before,
                        after: after_cell.map(|c| c.state.balance()),
                        exists_after: after_cell.is_some(),
                    }
                })
                .collect();
            // A factory/create birth lands a cell whose id the turn didn't name —
            // surface any NEW ledger cell (post minus the cells we already listed)
            // as a birth delta so the panel shows the new cell appearing.
            let known: std::collections::HashSet<CellId> = deltas.iter().map(|d| d.cell).collect();
            for (id, cell) in fork.ledger().iter() {
                if !known.contains(id) && world.ledger().get(id).is_none() {
                    deltas.push(CellDelta {
                        cell: *id,
                        before: None,
                        after: Some(cell.state.balance()),
                        exists_after: true,
                    });
                }
            }
            let count_after = fork.cell_count();
            SimOutcome::Predicted {
                verdict,
                receipt,
                deltas,
                events,
                cell_count_delta: count_after as i64 - count_before as i64,
                predicted_root: fork.state_root(),
            }
        }
        CommitOutcome::Rejected { reason, at_action } => SimOutcome::Refused {
            verdict,
            reason,
            at_action,
            static_refusal: false,
        },
        // A prediction fork is never suspended (forks run freely), so this is
        // unreachable in practice; surfaced as a refusal for total honesty.
        CommitOutcome::Queued { .. } => SimOutcome::Refused {
            verdict,
            reason: "fork suspended (unexpected): turn queued, not predicted".to_string(),
            at_action: vec![],
            static_refusal: false,
        },
    }
}

// ===========================================================================
// RENDER — a gpui-free text rendering of a SimOutcome (the panel's content).
// ===========================================================================

/// Render a [`SimOutcome`] as text — the SAME content the cockpit's SIMULATE
/// panel presents, in a gpui-free form so it is `cargo test`-able (the
/// render-content verification) and the visual layer can present it however it
/// likes. A `Predicted` arm shows the predicted receipt hash + per-cell deltas +
/// dynamics; a `Refused` arm shows the executor's reason. Mirrors the editor's
/// `edit::render_panel` discipline.
pub fn render_outcome(out: &SimOutcome) -> String {
    let mut s = String::new();
    match out {
        SimOutcome::Predicted {
            receipt,
            deltas,
            events,
            cell_count_delta,
            predicted_root,
            ..
        } => {
            s.push_str("PREDICTED: would COMMIT\n");
            s.push_str(&format!(
                "  receipt {} · {} action(s) · {} computrons\n",
                crate::reflect::short_hex(&receipt.receipt_hash()),
                receipt.action_count,
                receipt.computrons_used,
            ));
            s.push_str(&format!(
                "  predicted image root {}\n",
                crate::reflect::short_hex(predicted_root)
            ));
            if *cell_count_delta != 0 {
                s.push_str(&format!("  cell count {:+}\n", cell_count_delta));
            }
            s.push_str("  predicted cell deltas:\n");
            for d in deltas {
                let cell = crate::reflect::short_hex(&d.cell.0);
                let line = match (d.before, d.after) {
                    (None, Some(a)) => format!("    {cell}  BORN → balance {a}"),
                    (Some(_), None) => format!("    {cell}  RETIRED"),
                    (Some(b), Some(a)) if b != a => format!("    {cell}  {b} → {a}"),
                    (Some(b), Some(_)) => format!("    {cell}  unchanged ({b})"),
                    (None, None) => format!("    {cell}  (absent)"),
                };
                s.push_str(&line);
                s.push('\n');
            }
            if !events.is_empty() {
                s.push_str("  predicted dynamics:\n");
                for ev in events {
                    s.push_str(&format!("    · {}\n", ev.label()));
                }
            }
        }
        SimOutcome::Refused {
            reason,
            static_refusal,
            at_action,
            ..
        } => {
            if *static_refusal {
                s.push_str("PREDICTED: REFUSED (static rail — caught before submission)\n");
            } else {
                s.push_str("PREDICTED: REFUSED (the executor's guarantee would fire)\n");
            }
            if !at_action.is_empty() {
                s.push_str(&format!("  @ action {at_action:?}\n"));
            }
            s.push_str(&format!("  reason: {reason}\n"));
            s.push_str("  (no gas spent · the live image untouched)\n");
        }
    }
    s
}

// ===========================================================================
// COMMIT — run the SAME turn on the LIVE world (the commit button).
// ===========================================================================

/// **Commit the intent for real** — run the IDENTICAL turn on the live `world`.
///
/// This is the panel's commit button: after the operator has seen the prediction,
/// run the SAME `Turn` [`simulate`] previewed, now on the live world (mutating its
/// ledger, appending the receipt, emitting the dynamics). Returns the real
/// [`CommitOutcome`] — which, because the simulation ran the same executor over a
/// faithful copy, matches the predicted outcome (a `SimOutcome::Predicted` commits;
/// a `SimOutcome::Refused` would reject identically — but the panel only enables
/// commit when the prediction committed).
pub fn commit(world: &mut World, draft: &IntentDraft) -> CommitOutcome {
    let turn = draft.build_turn(world);
    world.commit_turn(turn)
}

/// Append `id` to `ids` if not already present (dedup).
fn push_unique(ids: &mut Vec<CellId>, id: CellId) {
    if !ids.contains(&id) {
        ids.push(id);
    }
}

/// All cell ids a turn's effects touch (for the pre/post delta — mirrors the
/// `world` module's internal `touched_cells`, surfaced here for the predicted
/// deltas).
fn touched_cells(turn: &Turn) -> Vec<CellId> {
    let mut ids: Vec<CellId> = Vec::new();
    for tree in &turn.call_forest.roots {
        push_unique(&mut ids, tree.action.target);
        collect(&tree.action, &mut ids);
        for child in &tree.children {
            push_unique(&mut ids, child.action.target);
            collect(&child.action, &mut ids);
        }
    }
    ids
}

fn collect(action: &dregg_turn::action::Action, ids: &mut Vec<CellId>) {
    for e in &action.effects {
        match e {
            Effect::Transfer { from, to, .. } => {
                push_unique(ids, *from);
                push_unique(ids, *to);
            }
            Effect::GrantCapability { from, to, .. } => {
                push_unique(ids, *from);
                push_unique(ids, *to);
            }
            Effect::SetField { cell, .. }
            | Effect::IncrementNonce { cell }
            | Effect::EmitEvent { cell, .. }
            | Effect::RevokeCapability { cell, .. }
            | Effect::SetPermissions { cell, .. }
            | Effect::MakeSovereign { cell } => push_unique(ids, *cell),
            Effect::Burn { target, .. }
            | Effect::CellSeal { target, .. }
            | Effect::CellUnseal { target }
            | Effect::CellDestroy { target, .. } => push_unique(ids, *target),
            _ => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_cell::field_from_u64;

    /// A two-cell world: `a` holds 1_000, `b` holds 0.
    fn two_cell_world() -> (World, CellId, CellId) {
        let mut w = World::new();
        let a = w.genesis_cell(1, 1_000);
        let b = w.genesis_cell(2, 0);
        (w, a, b)
    }

    #[test]
    fn simulate_a_transfer_predicts_the_post_state_without_committing() {
        let (w, a, b) = two_cell_world();

        let mut draft = IntentDraft::new(a);
        let ai = draft.add_action(a);
        draft.add_effect(ai, EffectKind::Transfer { to: b, amount: 250 });

        let out = simulate(&w, &draft);
        assert!(
            out.would_commit(),
            "a conserving transfer must be predicted to commit"
        );

        // THE LIVE WORLD IS UNTOUCHED — the whole point of a what-if.
        assert_eq!(w.ledger().get(&a).unwrap().state.balance(), 1_000);
        assert_eq!(w.ledger().get(&b).unwrap().state.balance(), 0);
        assert_eq!(w.height(), 0, "no commit happened on the live world");
        assert_eq!(w.receipts().len(), 0);

        // The PREDICTION carries a REAL receipt + the per-cell deltas.
        match out {
            SimOutcome::Predicted {
                receipt,
                deltas,
                predicted_root,
                ..
            } => {
                assert_eq!(receipt.action_count, 1);
                let da = deltas.iter().find(|d| d.cell == a).unwrap();
                let db = deltas.iter().find(|d| d.cell == b).unwrap();
                assert_eq!(da.before, Some(1_000));
                assert_eq!(da.after, Some(750), "a would drop to 750");
                assert_eq!(db.before, Some(0));
                assert_eq!(db.after, Some(250), "b would rise to 250");
                assert_ne!(
                    predicted_root,
                    w.state_root(),
                    "the predicted image root moved"
                );
            }
            SimOutcome::Refused { reason, .. } => panic!("unexpected refusal: {reason}"),
        }
    }

    #[test]
    fn the_predicted_receipt_equals_the_real_commit_receipt() {
        // The prediction is FAITHFUL: simulate, then commit the SAME draft on the
        // live world — the receipt hashes match (same executor, same pre-state,
        // same pinned timestamp).
        const TS: i64 = 1_700_000_000;
        let mk = || {
            let mut w = World::with_costs_and_timestamp(dregg_turn::ComputronCosts::zero(), TS);
            let a = w.genesis_cell(1, 1_000);
            let b = w.genesis_cell(2, 0);
            (w, a, b)
        };
        let (mut w, a, b) = mk();
        let mut draft = IntentDraft::new(a);
        let ai = draft.add_action(a);
        draft.add_effect(ai, EffectKind::Transfer { to: b, amount: 250 });

        let predicted = match simulate(&w, &draft) {
            SimOutcome::Predicted { receipt, .. } => receipt.receipt_hash(),
            SimOutcome::Refused { reason, .. } => panic!("predicted refusal: {reason}"),
        };
        // Now commit for real on the live world.
        let real = match commit(&mut w, &draft) {
            CommitOutcome::Committed { receipt, .. } => receipt.receipt_hash(),
            CommitOutcome::Rejected { reason, .. } => panic!("real reject: {reason}"),
            CommitOutcome::Queued { .. } => panic!("unexpected queue (world not suspended)"),
        };
        assert_eq!(
            predicted, real,
            "the predicted receipt must equal the real commit's"
        );
        // And the live world now reflects the committed turn.
        assert_eq!(w.ledger().get(&b).unwrap().state.balance(), 250);
        assert_eq!(w.height(), 1);
    }

    #[test]
    fn simulate_an_overspend_predicts_a_refusal_without_touching_the_world() {
        let (w, a, b) = two_cell_world();
        let mut draft = IntentDraft::new(a);
        let ai = draft.add_action(a);
        // a holds 1_000; ask to move 5_000 — the executor must refuse.
        draft.add_effect(
            ai,
            EffectKind::Transfer {
                to: b,
                amount: 5_000,
            },
        );

        let out = simulate(&w, &draft);
        assert!(
            !out.would_commit(),
            "an overspend must be predicted to REFUSE"
        );
        match out {
            SimOutcome::Refused {
                reason,
                static_refusal,
                ..
            } => {
                assert!(
                    !static_refusal,
                    "overspend is a DYNAMIC refusal (the fork's executor)"
                );
                assert!(!reason.is_empty(), "the executor's reason is surfaced");
            }
            SimOutcome::Predicted { .. } => panic!("overspend should not be predicted to commit"),
        }
        // The live world is untouched (a refusal in the fork costs the live world nothing).
        assert_eq!(w.ledger().get(&a).unwrap().state.balance(), 1_000);
        assert_eq!(w.height(), 0);
    }

    #[test]
    fn simulate_an_over_grant_is_refused() {
        // The ocap no-amplification guarantee, predicted: `a` holds NO cap to `b`,
        // so granting one must refuse (the executor's dynamic check fires in the fork).
        let (w, a, b) = two_cell_world();
        let mut draft = IntentDraft::new(a);
        let ai = draft.add_action(a);
        draft.add_effect(
            ai,
            EffectKind::GrantCapability {
                to: a,
                target: b,
                slot: 0,
            },
        );

        let out = simulate(&w, &draft);
        assert!(
            !out.would_commit(),
            "an over-grant must be predicted to refuse"
        );
        assert_eq!(w.height(), 0, "the live world is untouched");
    }

    #[test]
    fn simulate_a_malformed_intent_is_caught_by_the_static_rail() {
        // An action with ZERO effects is a well-formedness sin — the static rail
        // catches it BEFORE the fork (static_refusal: true).
        let (w, a, _b) = two_cell_world();
        let mut draft = IntentDraft::new(a);
        draft.add_action(a); // no effects added → malformed

        let out = simulate(&w, &draft);
        assert!(!out.would_commit());
        match out {
            SimOutcome::Refused { static_refusal, .. } => {
                assert!(static_refusal, "an empty-effect action is a STATIC refusal");
            }
            _ => panic!("malformed intent should refuse statically"),
        }
    }

    #[test]
    fn simulate_a_create_cell_predicts_the_birth() {
        let (w, a, _b) = two_cell_world();
        let before = w.cell_count();
        let mut draft = IntentDraft::new(a);
        let ai = draft.add_action(a);
        draft.add_effect(ai, EffectKind::CreateCell { seed: 0x9A });

        let out = simulate(&w, &draft);
        assert!(
            out.would_commit(),
            "a create-cell must be predicted to commit"
        );
        match out {
            SimOutcome::Predicted {
                cell_count_delta,
                deltas,
                ..
            } => {
                assert_eq!(cell_count_delta, 1, "the image would gain one cell");
                // The birth appears as a `before: None` delta.
                assert!(
                    deltas.iter().any(|d| d.before.is_none() && d.exists_after),
                    "the born cell shows as a birth delta"
                );
            }
            _ => unreachable!(),
        }
        // The live world did NOT gain the cell (it was only a what-if).
        assert_eq!(w.cell_count(), before, "the live world did not grow");
    }

    #[test]
    fn simulate_a_multi_action_forest_predicts_all_deltas() {
        // Compose ANY intent over ANY cells: a pays b AND c in one atomic turn.
        let mut w = World::new();
        let a = w.genesis_cell(1, 1_000);
        let b = w.genesis_cell(2, 0);
        let c = w.genesis_cell(3, 0);
        let mut draft = IntentDraft::new(a);
        let a1 = draft.add_action(a);
        draft.add_effect(a1, EffectKind::Transfer { to: b, amount: 100 });
        let a2 = draft.add_action(a);
        draft.add_effect(a2, EffectKind::Transfer { to: c, amount: 200 });
        assert_eq!(draft.effect_count(), 2);

        let out = simulate(&w, &draft);
        match out {
            SimOutcome::Predicted {
                receipt, deltas, ..
            } => {
                assert_eq!(receipt.action_count, 2, "two sibling actions in one turn");
                assert_eq!(
                    deltas.iter().find(|d| d.cell == b).unwrap().after,
                    Some(100)
                );
                assert_eq!(
                    deltas.iter().find(|d| d.cell == c).unwrap().after,
                    Some(200)
                );
                assert_eq!(
                    deltas.iter().find(|d| d.cell == a).unwrap().after,
                    Some(700)
                );
            }
            SimOutcome::Refused { reason, .. } => panic!("unexpected refusal: {reason}"),
        }
        assert_eq!(w.height(), 0, "the live world is untouched");
    }

    #[test]
    fn simulate_a_program_violating_write_is_refused() {
        // A deployed program is REAL in the fork: an Immutable slot rejects a write.
        // (Proves the fork carries the live cell's PROGRAM, not just its balance.)
        let mut w = World::new();
        let program = edit::ProgramBuilder::new().immutable(0).build();
        let dep = edit::deploy_program(&mut w, 0x42, 100, program);
        let id = dep.cell;

        let mut draft = IntentDraft::new(id);
        let ai = draft.add_action(id);
        draft.add_effect(
            ai,
            EffectKind::SetField {
                index: 0,
                value: field_from_u64(7),
            },
        );

        let out = simulate(&w, &draft);
        assert!(
            !out.would_commit(),
            "the deployed Immutable program must refuse the write in the fork"
        );
        assert_eq!(w.height(), 0);
    }

    #[test]
    fn fork_carries_the_chain_head_so_a_chained_turn_predicts_correctly() {
        // Commit one real turn (advancing a's chain head), THEN simulate a second
        // turn from a. The fork must carry a's chain head or the second turn would
        // reject as ReceiptChainMismatch — this proves the fork seeds heads.
        let (mut w, a, b) = two_cell_world();
        let t1 = w.turn(a, vec![world::transfer(a, b, 100)]);
        assert!(w.commit_turn(t1).is_committed());
        assert!(w.chain_head(&a).is_some());

        let mut draft = IntentDraft::new(a);
        let ai = draft.add_action(a);
        draft.add_effect(ai, EffectKind::Transfer { to: b, amount: 100 });
        let out = simulate(&w, &draft);
        assert!(
            out.would_commit(),
            "a second chained turn must predict-commit (the fork carried a's chain head)"
        );
    }

    // ── THE RENDER-CONTENT VERIFICATION (the task's explicit check) ──────────
    //
    // The simulate path's RENDERED CONTENT (the gpui-free text the SIMULATE panel
    // presents) carries a REAL predicted receipt for a good intent and a REAL
    // refusal for a bad one — proving the panel reflects the live executor's
    // verdict, run one turn ahead, in the content it would draw.

    #[test]
    fn render_content_shows_a_real_predicted_receipt_and_a_real_refusal() {
        let (w, a, b) = two_cell_world();

        // (1) A GOOD intent → the rendered content carries the predicted receipt
        //     hash + the predicted balance deltas (the cells' real post-state).
        let mut good = IntentDraft::new(a);
        let gi = good.add_action(a);
        good.add_effect(gi, EffectKind::Transfer { to: b, amount: 250 });
        let good_out = simulate(&w, &good);
        let real_receipt = match &good_out {
            SimOutcome::Predicted { receipt, .. } => {
                crate::reflect::short_hex(&receipt.receipt_hash())
            }
            SimOutcome::Refused { reason, .. } => panic!("good intent refused: {reason}"),
        };
        let good_render = render_outcome(&good_out);
        assert!(
            good_render.contains("would COMMIT"),
            "render shows the predicted-commit"
        );
        assert!(
            good_render.contains(&real_receipt),
            "render must carry the REAL predicted receipt hash: {good_render}"
        );
        // The predicted post-state deltas are in the content (a → 750, b → 250).
        assert!(
            good_render.contains("750"),
            "render shows a's predicted post-balance"
        );
        assert!(
            good_render.contains("250"),
            "render shows b's predicted post-balance"
        );

        // (2) A BAD intent (overspend) → the rendered content carries a REAL
        //     refusal with the executor's reason, BEFORE anything commits.
        let mut bad = IntentDraft::new(a);
        let bi = bad.add_action(a);
        bad.add_effect(
            bi,
            EffectKind::Transfer {
                to: b,
                amount: 9_999,
            },
        );
        let bad_out = simulate(&w, &bad);
        assert!(
            !bad_out.would_commit(),
            "the overspend must be predicted to refuse"
        );
        let bad_render = render_outcome(&bad_out);
        assert!(
            bad_render.contains("REFUSED"),
            "render shows the refusal: {bad_render}"
        );
        assert!(
            bad_render.contains("reason:"),
            "render carries the executor's reason: {bad_render}"
        );

        // The live world is untouched by EITHER simulation — the whole point.
        assert_eq!(w.height(), 0, "no commit happened on the live world");
        assert_eq!(w.ledger().get(&a).unwrap().state.balance(), 1_000);
        assert_eq!(w.ledger().get(&b).unwrap().state.balance(), 0);
    }
}
