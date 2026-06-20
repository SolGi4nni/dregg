//! First-class reversibility — the *un-turn* on the real substrate (M-REV-0).
//!
//! This module is the protocol-level generalization of `dregg-doc`'s
//! `Patch::invert` (`dregg-doc/src/patch.rs`): it lifts the document patch
//! grammar's effect-inverse to the full [`Effect`](crate::action::Effect) set,
//! and wraps the verified replay recorder into a [`ReversibleHistory`] whose
//! [`ReversibleHistory::undo_to`] walks history *backward* — the dual of
//! `replay_to` — fail-closed at the irreversible boundary.
//!
//! The design is `docs/deos/FIRST-CLASS-REVERSIBILITY.md` (the RCCS frame:
//! Danos–Krivine reversible CCS with *committed actions*). The one sentence:
//!
//! > Every effect has an inverse (the un-turn); a stretch of unsettled history
//! > can be rolled back; and the only steps that genuinely cannot reverse are
//! > the deliberately-committed ones (Destroy, Burn, NoteSpend, nonce-ratchet,
//! > revoke) — irreversible *on purpose*, because reversing them would unmake a
//! > fact another party has already built upon.
//!
//! # Three honest tiers ([`Inversion`])
//!
//! - [`Inversion::Clean`] — the inverse is computable from the forward effect
//!   alone (Transfer↔Transfer, grant↔revoke, seal↔unseal, event-retract). These
//!   reverse anywhere.
//! - [`Inversion::Contextual`] — the inverse needs the *pre-image* (the old
//!   field value, the revoked cap's content), which the reversible-history
//!   object supplies as the pre-state ledger. Sound only against the history
//!   that produced the effect — the standard RCCS caveat (`Patch::invert`
//!   inherits it).
//! - [`Inversion::Committed`] — no inverse, *by design*. Destroy, Burn,
//!   NoteSpend, IncrementNonce-as-ratchet, RevokeCapability/RevokeDelegation,
//!   and the conservation/lifecycle-terminal moves. A turn containing one is
//!   **not reversible**; the un-turn says so honestly rather than producing a
//!   wrong inverse.
//!
//! # `undo_to` vs compensation (load-bearing distinction)
//!
//! [`ReversibleHistory::undo_to`] reverses within the **unsettled window** — it
//! restores the prior state and is only legal above the most recent committed
//! step. Reversing a *settled* turn is **not** an un-turn at all; it is a fresh
//! *forward* compensating turn (a reversing transfer, a re-grant) that itself
//! settles. This module deliberately offers only `undo_to` (the reversible
//! window) and never claims to rewrite finalized history.
//!
//! # Two honest caveats this module makes precise (not papers over)
//!
//! 1. **The nonce ratchet is the per-turn island of irreversibility.** Every
//!    committed turn advances the agent's freshness nonce, a *monotone* counter
//!    that — by the same §4.2 argument that makes revocation irreversible —
//!    cannot run backward. Re-applying an inverse turn through the executor
//!    therefore restores the **value/state** (balances, fields, caps) exactly
//!    but leaves the nonce ADVANCED. So "the same verified root, run backward"
//!    holds *modulo the nonce* ([`ledgers_agree_modulo_nonce`]) — a raw
//!    `Ledger::root` equality would (correctly) fail, because undoing must not
//!    rewind the ratchet. This is not a gap; it is the committed boundary
//!    located at the per-turn granularity.
//!
//! 2. **`undo_to` reverses a contiguous suffix, most-recent-first.** It treats
//!    *time-order* as the causal order — the conservative, always-sound reading
//!    of RCCS causal-consistency (§1.2). You cannot `undo_to` *past* a committed
//!    step, and you cannot (yet) undo a *middle* turn while keeping later ones.
//!    But a middle turn *is* causal-consistently reversible **iff nothing
//!    downstream depends on it** — concretely, iff no later turn touches a cell
//!    it wrote. [`ReversibleHistory::can_undo_isolated`] reports exactly that
//!    frontier (the maximally-permissive answer to "can I only undo the
//!    most-recent turn?": no — any turn whose causal cone is empty above it is
//!    reversible; the contiguous-suffix `undo_to` is just the conservative
//!    engine). Wiring a mutating `undo_isolated` that splices a middle reversal
//!    is the §3.3 follow-up.
//!
//! # The partial-turn (promise-pipelining) lift — why the split stays
//!
//! A "partial turn with holes" is concretely a `Pipeline`/`TurnBatch`
//! ([`crate::eventual`]) whose `EventualRef` edges are unresolved — the proven
//! Kahn-topological, all-or-nothing executor layer (`execute_pipeline`; the Lean
//! `execConditionalTurn`). The census verdict (`project-partial-turn-promises`)
//! is that this is **correctly an executor/spec layer, NOT a batch-bearing
//! `Effect` variant**, and reversibility *confirms* the placement:
//!
//! - **Determination is eager; witness is lazy.** A contribution's SHAPE
//!   (actions, δ, authority demand) is fixed when it joins the batch; only its
//!   WITNESS (the resolved value) arrives later. An inverse is computed against
//!   a *shape*, so the un-turn for a batch is the per-turn `Turn::invert` of each
//!   resolved node, in reverse topological order — there is nothing a
//!   batch-bearing `Effect` would add to the *inverse* story that the node-level
//!   inverse does not already give.
//! - **The one pipelining effect that IS first-class — [`Effect::PipelinedSend`]
//!   (carrying an [`crate::eventual::EventualRef`]) — is classified
//!   [`Inversion::Committed`]** ([`CommittedReason::NonLocalEffect`]): its honest
//!   inverse is not a single substrate effect (it would have to *un-resolve* a
//!   promise / un-dispatch the pipelined send). So a turn containing a
//!   pipelined send is not reversible by the un-turn, and `Turn::invert` says so
//!   — exactly the fail-closed posture a promise-hole demands (resolution is a
//!   one-shot, like a spend). The exhaustive `match` in [`Effect::invert`] forces
//!   any future batch-bearing variant to answer this same question.
//!
//! # Circuit / light-client handoff (do NOT edit circuit here)
//!
//! An un-turn is a turn, so it inherits light-client unfoolability *for free*
//! when proven: the inverse turn produces a receipt and a state transition the
//! light client checks like any forward turn (§3.6). The handoff note for the
//! circuit lane (ember's live `circuit/` + `metatheory/Dregg2/Circuit/`):
//!
//! - **An invertible effect needs NO new descriptor.** `Turn::invert` emits
//!   *ordinary* effects (a reverse `Transfer`, a restoring `SetField`, a
//!   `RevokeCapability` that retracts a grant) — every one already has a circuit
//!   descriptor. The un-turn rung is therefore the *existing* rungs; no VK bump.
//! - **The one binding obligation is the backward root tooth.** A dishonest
//!   rewind (claiming to restore σ₀ but landing elsewhere) must be caught by the
//!   same anti-substitution discipline as a tampered replay: the inverse turn's
//!   post-state commitment must equal the recorded pre-cursor commitment
//!   *modulo the monotone nonce*. The circuit already binds the nonce into the
//!   state commitment, so the light client sees the advanced-nonce post-state —
//!   the value/state restoration is witnessed, and the ratchet's advance is
//!   visible and correct. **Handoff ask:** confirm the state-commitment binding
//!   admits the "value restored, nonce advanced" post-state as a *genuine*
//!   transition (it should — it is just another forward turn).
//! - **A batch-bearing effect, IF ever added, must satisfy `holeFill_binds_in_
//!   circuit`** (the named guarded-hole theorem): every late fill binds its δ +
//!   guard into the proof the light client checks. Until then, the executor-layer
//!   split keeps batches OUT of the per-effect descriptor fold, which is why the
//!   apex (`FullForestA`) needs no batch node today.

use std::collections::BTreeMap;

use dregg_cell::{Cell, CellId, Ledger};

use crate::action::Effect;
use crate::forest::CallForest;
use crate::turn::{Turn, TurnReceipt, TurnResult};
use crate::Action;
use crate::{Authorization, ComputronCosts, TurnExecutor};

// ===========================================================================
// Effect::invert — the un-turn on the real substrate
// ===========================================================================

/// Why a forward [`Effect`] has no inverse — the irreversible boundary
/// (`FIRST-CLASS-REVERSIBILITY.md` §4). Each reason is a point where the system
/// has *published a fact another party relies on*.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CommittedReason {
    /// A nullifier was consumed (one-shot). Un-spending would re-admit it,
    /// breaking the double-spend defense the whole value layer rests on (§4.3).
    NullifierConsumed,
    /// Value was provably destroyed (`Burn`). Reversing would re-create value
    /// the conservation law has already accounted as gone (§4.3).
    ValueBurned,
    /// A monotone freshness ratchet advanced (`IncrementNonce`). A ratchet that
    /// ran backward is not a ratchet — it would re-admit a stale turn (§4.2).
    FreshnessRatchet,
    /// Authority was retracted (`RevokeCapability` / `RevokeDelegation`). A
    /// revocation that could be undone is not a revocation (§4.2). Restoring it
    /// requires a fresh forward *grant*, not an un-turn.
    AuthorityRevoked,
    /// A terminal lifecycle transition with no inverse (`CellDestroy`,
    /// `MakeSovereign`, `ReceiptArchive`).
    TerminalLifecycle,
    /// A one-way capability narrowing (`AttenuateCapability`); widening is
    /// rejected by the underlying primitive, so it cannot be undone.
    MonotoneNarrowing,
    /// The effect is a *generative* / cross-federation / proof-carrying move
    /// (`BridgeMint`, `CreateCell*`, `SpawnWithDelegation`, note-create) whose
    /// honest inverse is itself a committed move (a spend / destroy) — excluded
    /// from the reversible substrate to keep the un-turn fail-closed.
    GenerativeOrProofCarrying,
    /// A pipelining / capability-exercise / refusal effect whose inverse is not
    /// a single substrate effect (it would have to un-resolve a promise or
    /// un-exercise a cap). Out of scope for M-REV-0; reverses only by
    /// re-running the forward pipeline differently.
    NonLocalEffect,
}

impl CommittedReason {
    /// A short human label for the boundary view.
    pub fn label(self) -> &'static str {
        match self {
            CommittedReason::NullifierConsumed => "nullifier consumed (one-shot spend)",
            CommittedReason::ValueBurned => "value burned (conservation-committed)",
            CommittedReason::FreshnessRatchet => "nonce ratchet (monotone)",
            CommittedReason::AuthorityRevoked => "authority revoked (compensate by re-grant)",
            CommittedReason::TerminalLifecycle => "terminal lifecycle (no inverse)",
            CommittedReason::MonotoneNarrowing => "capability narrowed (one-way)",
            CommittedReason::GenerativeOrProofCarrying => "generative / proof-carrying",
            CommittedReason::NonLocalEffect => "non-local effect (re-run forward)",
        }
    }
}

/// The inverse of a single forward [`Effect`], split into the three honest
/// reversibility tiers (`FIRST-CLASS-REVERSIBILITY.md` §3.1).
#[derive(Clone, Debug)]
pub enum Inversion {
    /// Self-inverse from the forward effect alone — reverses anywhere.
    Clean(Effect),
    /// Inverse needs the pre-image; sound only against the producing history.
    Contextual(Effect),
    /// No inverse, by design (the irreversible boundary).
    Committed(CommittedReason),
}

impl Inversion {
    /// The inverse effect, if this effect is reversible (Clean or Contextual).
    pub fn effect(&self) -> Option<&Effect> {
        match self {
            Inversion::Clean(e) | Inversion::Contextual(e) => Some(e),
            Inversion::Committed(_) => None,
        }
    }

    /// Is this effect reversible at all (Clean or Contextual)?
    pub fn is_reversible(&self) -> bool {
        !matches!(self, Inversion::Committed(_))
    }
}

impl Effect {
    /// Compute the inverse of this effect against the pre-state `pre` it acted
    /// on — the *un-turn* (`FIRST-CLASS-REVERSIBILITY.md` §3.1).
    ///
    /// `pre` is the ledger **before** this effect applied; the contextual
    /// inverses (SetField's old value, the revoked cap's content) read their
    /// pre-image from it. For the clean inverses `pre` is ignored.
    ///
    /// **This match is exhaustive on purpose** — like [`Effect::linearity`],
    /// there is no `_ =>` arm. Any new [`Effect`] variant is forced by `rustc`
    /// to answer the reversibility question: declare it Clean, Contextual, or
    /// Committed. A contributor cannot silently leave a new effect's
    /// reversibility implicit.
    ///
    /// The faithfulness obligation (`§3.1`): for the Clean and Contextual
    /// tiers, `apply(invert(e, pre), apply(e, pre)) == pre`. The Committed tier
    /// is *excluded* from that round-trip — its irreversibility is a
    /// precondition, not a gap.
    pub fn invert(&self, pre: &Ledger) -> Inversion {
        match self {
            // ── CLEAN: the inverse is computable from the effect alone. ──────

            // Value is symmetric; conservation holds in both directions. The
            // reverse Transfer moves the same amount back.
            Effect::Transfer { from, to, amount } => Inversion::Clean(Effect::Transfer {
                from: *to,
                to: *from,
                amount: *amount,
            }),

            // grant is monotone-up; its retraction is a revoke of the granted
            // slot. The slot is the cap's slot in the *recipient* `to`'s c-list.
            Effect::GrantCapability { to, cap, .. } => {
                Inversion::Clean(Effect::RevokeCapability {
                    cell: *to,
                    slot: cap.slot,
                })
            }

            // The lifecycle quartet is a reversible pair: seal↔unseal. A seal's
            // inverse is an unseal (restores the Live lifecycle); the reason
            // commitment is bound into the receipt, not needed to reverse.
            Effect::CellSeal { target, .. } => Inversion::Clean(Effect::CellUnseal {
                target: *target,
            }),
            Effect::CellUnseal { target } => {
                // Unsealing reverses to a re-seal. The reason cleartext lives
                // off-chain; we re-seal under a zero reason-commitment (the
                // undo restores the *Sealed* lifecycle state, which is what the
                // root tooth checks). If the producing seal's reason is needed,
                // it is read from the receipt, not the unseal effect.
                Inversion::Contextual(Effect::CellSeal {
                    target: *target,
                    reason: [0u8; 32],
                })
            }

            // ── CONTEXTUAL: the inverse needs the pre-image from `pre`. ──────

            // SetField's inverse restores the OLD value, read from `pre`.
            Effect::SetField { cell, index, .. } => {
                let old = pre
                    .get(cell)
                    .and_then(|c| c.state.get_field(*index).copied())
                    .unwrap_or([0u8; 32]);
                Inversion::Contextual(Effect::SetField {
                    cell: *cell,
                    index: *index,
                    value: old,
                })
            }

            // SetPermissions / SetVerificationKey restore the pre-image
            // permissions / vk from `pre`.
            Effect::SetPermissions { cell, .. } => {
                let old = pre
                    .get(cell)
                    .map(|c| c.permissions.clone())
                    .unwrap_or_default();
                Inversion::Contextual(Effect::SetPermissions {
                    cell: *cell,
                    new_permissions: old,
                })
            }
            Effect::SetVerificationKey { cell, .. } => {
                let old = pre.get(cell).and_then(|c| c.verification_key.clone());
                Inversion::Contextual(Effect::SetVerificationKey {
                    cell: *cell,
                    new_vk: old,
                })
            }

            // EmitEvent is an append to the receipt-local view; un-emit drops
            // the append. There is no state-mutating inverse effect, so the
            // honest inverse is a no-op event (the event lives only in the
            // receipt, not in the ledger root). We classify it Clean and emit
            // the same event back as a marker; the undo's root equals the
            // pre-root because events do not move the canonical Ledger::root.
            Effect::EmitEvent { cell, event } => Inversion::Clean(Effect::EmitEvent {
                cell: *cell,
                event: event.clone(),
            }),

            // RefreshDelegation re-snapshots from the parent; it is idempotent
            // bookkeeping with no resource delta. Re-refreshing restores the
            // same snapshot (Contextual on the parent epoch in `pre`).
            Effect::RefreshDelegation => Inversion::Contextual(Effect::RefreshDelegation),

            // ── COMMITTED: no inverse, by design (the irreversible boundary). ─

            // A nullifier is one-shot; un-spending re-admits it (§4.3).
            Effect::NoteSpend { .. } => Inversion::Committed(CommittedReason::NullifierConsumed),
            // A note-create's honest inverse is a spend, itself one-shot.
            Effect::NoteCreate { .. } => {
                Inversion::Committed(CommittedReason::GenerativeOrProofCarrying)
            }
            // Provable value destruction (§4.3).
            Effect::Burn { .. } => Inversion::Committed(CommittedReason::ValueBurned),
            // The freshness ratchet (§4.2).
            Effect::IncrementNonce { .. } => {
                Inversion::Committed(CommittedReason::FreshnessRatchet)
            }
            // Authority retraction; compensate by a fresh re-grant (§4.2).
            Effect::RevokeCapability { .. } => {
                Inversion::Committed(CommittedReason::AuthorityRevoked)
            }
            Effect::RevokeDelegation { .. } => {
                Inversion::Committed(CommittedReason::AuthorityRevoked)
            }
            // Terminal lifecycle transitions.
            Effect::CellDestroy { .. } => Inversion::Committed(CommittedReason::TerminalLifecycle),
            Effect::MakeSovereign { .. } => {
                Inversion::Committed(CommittedReason::TerminalLifecycle)
            }
            Effect::ReceiptArchive { .. } => {
                Inversion::Committed(CommittedReason::TerminalLifecycle)
            }
            // One-way narrowing.
            Effect::AttenuateCapability { .. } => {
                Inversion::Committed(CommittedReason::MonotoneNarrowing)
            }
            // Generative / proof-carrying / cross-federation creation: the
            // honest inverse is a committed move (a destroy / spend / retire).
            Effect::CreateCell { .. } => {
                Inversion::Committed(CommittedReason::GenerativeOrProofCarrying)
            }
            Effect::CreateCellFromFactory { .. } => {
                Inversion::Committed(CommittedReason::GenerativeOrProofCarrying)
            }
            Effect::SpawnWithDelegation { .. } => {
                Inversion::Committed(CommittedReason::GenerativeOrProofCarrying)
            }
            Effect::BridgeMint { .. } => {
                Inversion::Committed(CommittedReason::GenerativeOrProofCarrying)
            }
            // Introduce mints a cap slot in the recipient; its honest inverse
            // would be a revoke of an externally-assigned slot we do not name
            // here — out of scope, treat as non-local.
            Effect::Introduce { .. } => Inversion::Committed(CommittedReason::NonLocalEffect),
            // Refusal is *evidence of absence* that bumps a nonce; the nonce
            // bump makes it monotone (a ratchet), so it is committed.
            Effect::Refusal { .. } => Inversion::Committed(CommittedReason::FreshnessRatchet),
            // Pipelining / cap-exercise: the inverse is not a single substrate
            // effect (it would un-resolve a promise or un-exercise a cap).
            Effect::PipelinedSend { .. } => Inversion::Committed(CommittedReason::NonLocalEffect),
            Effect::ExerciseViaCapability { .. } => {
                Inversion::Committed(CommittedReason::NonLocalEffect)
            }
        }
    }
}

// ===========================================================================
// Turn::invert — the inverse forest, fail-closed at the boundary
// ===========================================================================

/// Why a [`Turn`] could not be inverted (`Turn::invert` fail-closed paths).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InvertError {
    /// A contained effect is [`Inversion::Committed`] — the turn is not
    /// reversible. Carries the offending reason and the action/effect position.
    ContainsCommitted {
        reason: CommittedReason,
        action_index: usize,
        effect_index: usize,
    },
}

impl std::fmt::Display for InvertError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InvertError::ContainsCommitted {
                reason,
                action_index,
                effect_index,
            } => write!(
                f,
                "turn is not reversible: action {action_index} effect {effect_index} is committed ({})",
                reason.label()
            ),
        }
    }
}

impl std::error::Error for InvertError {}

impl Turn {
    /// Build the inverse turn against the pre-state `pre` (the ledger BEFORE
    /// this turn applied). Walks the turn's effects in **reverse order**,
    /// inverts each against `pre`, and **fails-closed** if any effect is
    /// [`Inversion::Committed`] (`FIRST-CLASS-REVERSIBILITY.md` §3.1).
    ///
    /// The inverse turn is an ordinary [`Turn`] — it goes through the same
    /// executor and the same cap-gate. Reversal is therefore causal-consistent
    /// by construction: you can only un-turn over cells you hold authority to,
    /// which is exactly "the downstream parties consent" (§1.2). The inverse
    /// turn's authorization is carried as [`Authorization::Unchecked`] on each
    /// inverse action; an *open* cell (test/demo) accepts it, and a *gated* cell
    /// requires the caller to re-authorize the reversal turn — the executor gate
    /// is the consent membrane, not a bypass.
    ///
    /// The inverse turn keeps `self.agent` as the agent and `self.nonce + 1` as
    /// the nonce (the un-turn is a *new* turn in the agent's chain, not a
    /// rewrite of the forward one). `previous_receipt_hash` is left `None` for
    /// the caller / recorder to chain.
    pub fn invert(&self, pre: &Ledger) -> Result<Turn, InvertError> {
        // Collect (in forest order) the per-action inverted effect lists, then
        // reverse BOTH the action order and the within-action effect order.
        let mut inverse_actions: Vec<Action> = Vec::new();

        // Walk the forest depth-first (the canonical action order the executor
        // applies); the un-turn unwinds it last-first below.
        let forward_actions: Vec<&Action> =
            self.call_forest.iter_dfs().map(|t| &t.action).collect();
        for (action_index, action) in forward_actions.iter().enumerate() {
            let mut inv_effects: Vec<Effect> = Vec::with_capacity(action.effects.len());
            // Reverse the within-action effect order (the un-turn unwinds the
            // last write first).
            for (effect_index, effect) in action.effects.iter().enumerate().rev() {
                match effect.invert(pre) {
                    Inversion::Clean(e) | Inversion::Contextual(e) => inv_effects.push(e),
                    Inversion::Committed(reason) => {
                        return Err(InvertError::ContainsCommitted {
                            reason,
                            action_index,
                            effect_index,
                        });
                    }
                }
            }
            if inv_effects.is_empty() {
                continue;
            }
            // The inverse action targets the inverse effect's PRIMARY cell — the
            // cell whose authority reverses the effect. For a reversed transfer
            // `b→a` that is `b` (the party returning the value); for a SetField
            // restore it is the field's cell. Targeting the primary cell keeps
            // the executor's `from == action_target` fast-path, so the un-turn
            // is gated by the *same* authority the forward turn needed (the
            // consent membrane), not a cross-cell amplification.
            let inv_target = inverse_primary_cell(&inv_effects).unwrap_or(action.target);
            inverse_actions.push(Action {
                target: inv_target,
                method: action.method,
                args: action.args.clone(),
                authorization: Authorization::Unchecked,
                preconditions: Default::default(),
                effects: inv_effects,
                may_delegate: action.may_delegate,
                commitment_mode: action.commitment_mode,
                balance_change: None,
                witness_blobs: Vec::new(),
            });
        }
        // Reverse the action order: the un-turn unwinds the last action first.
        inverse_actions.reverse();
        // The un-turn's agent is the primary cell of its first inverse action
        // (the actor whose authority the executor checks). For a single-cell
        // inverse this is exactly the consenting party.
        let inverse_agent = inverse_actions
            .first()
            .map(|a| a.target)
            .unwrap_or(self.agent);

        let mut forest = CallForest::new();
        for action in inverse_actions {
            forest.add_root(action);
        }

        // Build the inverse turn from a clone of `self` (preserving the
        // serde-positional fields), then override the body. The proof / witness
        // sidecars are zeroed — the un-turn is a fresh executor-trusted turn, not
        // a re-presentation of the forward turn's proofs.
        let mut inverse = self.clone();
        inverse.agent = inverse_agent;
        inverse.nonce = self.nonce.saturating_add(1);
        inverse.call_forest = forest;
        inverse.fee = 0;
        inverse.memo = Some("un-turn".to_string());
        inverse.valid_until = None;
        inverse.previous_receipt_hash = None;
        inverse.depends_on = Vec::new();
        inverse.conservation_proof = None;
        inverse.sovereign_witnesses = Default::default();
        inverse.execution_proof = None;
        inverse.execution_proof_cell = None;
        inverse.execution_proof_new_commitment = None;
        inverse.custom_program_proofs = None;
        inverse.effect_binding_proofs = Vec::new();
        inverse.cross_effect_dependencies = Vec::new();
        inverse.effect_witness_index_map = Vec::new();
        Ok(inverse)
    }

    /// Is this turn reversible against `pre` (no contained committed effect)?
    pub fn is_reversible(&self, pre: &Ledger) -> bool {
        self.invert(pre).is_ok()
    }
}

// ===========================================================================
// ReversibleHistory — undo_to, the backward dual of replay_to
// ===========================================================================

/// One recorded step of reversible history — genesis installs and committed
/// turns, in order. Replaying `0..=k` reconstructs the world at step k; undoing
/// `k+1..head` reverses back to it. Mirrors starbridge's `replay::RecordedStep`
/// (which is off-limits to this crate), self-contained here so the un-turn lives
/// beside `Effect::invert`.
#[derive(Clone)]
pub enum ReversibleStep {
    /// A cell installed directly at genesis (bypasses the executor).
    Genesis { cell: Cell },
    /// A turn committed against the embedded executor. Carries the input turn
    /// (so replay RE-EXECUTES it), the receipt, and the canonical post-state
    /// root tooth.
    Committed {
        turn: Turn,
        receipt: TurnReceipt,
        post_root: [u8; 32],
    },
}

/// Errors from the reversible-history navigation (fail-closed, mirroring
/// `replay::ReplayError` plus the irreversibility wall).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReversibleError {
    /// Asked to navigate to a step beyond the recorded history.
    OutOfRange { step: usize, len: usize },
    /// The reconstructed root did NOT match the recorded tooth — fail-closed
    /// anti-substitution (the backward companion to replay's RootMismatch).
    RootMismatch {
        step: usize,
        got: [u8; 32],
        want: [u8; 32],
    },
    /// A recorded turn that committed when first run did NOT commit on replay.
    NondeterministicReplay { step: usize, got: String },
    /// `undo_to(k)` hit a committed (irreversible) step in `k+1..head` — you
    /// cannot undo *past* a commit. This is the RCCS islands-of-irreversibility
    /// made an API boundary (`FIRST-CLASS-REVERSIBILITY.md` §3.2).
    IrreversibleStep {
        step: usize,
        reason: CommittedReason,
    },
    /// An inverse turn, though built, was REJECTED by the executor (e.g. the
    /// reversal lacked authority over a gated cell — the consent membrane held).
    InverseRejected { step: usize, reason: String },
}

impl std::fmt::Display for ReversibleError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ReversibleError::OutOfRange { step, len } => {
                write!(f, "undo step {step} out of range (history len {len})")
            }
            ReversibleError::RootMismatch { step, .. } => {
                write!(f, "undo root mismatch at step {step} (fail-closed)")
            }
            ReversibleError::NondeterministicReplay { step, got } => {
                write!(f, "nondeterministic replay at step {step}: {got}")
            }
            ReversibleError::IrreversibleStep { step, reason } => write!(
                f,
                "cannot undo past committed step {step}: {}",
                reason.label()
            ),
            ReversibleError::InverseRejected { step, reason } => {
                write!(f, "inverse turn for step {step} rejected: {reason}")
            }
        }
    }
}

impl std::error::Error for ReversibleError {}

/// The recorded, replayable AND reversible history of a world.
///
/// `History` (starbridge's `replay.rs`) records steps + roots and lands
/// forward; `ReversibleHistory` adds the backward walk: [`Self::undo_to`] builds
/// and applies the inverse turns for `k+1..head` in reverse, each gated by the
/// executor, and verifies the reconstructed root equals the recorded tooth at
/// `k` — the **same root tooth, run backward**.
pub struct ReversibleHistory {
    steps: Vec<ReversibleStep>,
    /// `roots[i]` = canonical [`Ledger::root`] after applying steps `0..i`;
    /// `roots[0]` is the empty-ledger root, `roots[len()]` the head.
    roots: Vec<[u8; 32]>,
    timestamp: i64,
    costs: ComputronCosts,
}

impl ReversibleHistory {
    /// A fresh, empty reversible history (free-metered).
    pub fn new(timestamp: i64) -> Self {
        Self::with_costs(timestamp, ComputronCosts::zero())
    }

    /// A fresh, empty reversible history metering at `costs`.
    pub fn with_costs(timestamp: i64, costs: ComputronCosts) -> Self {
        let mut roots = Vec::new();
        roots.push(Ledger::new().root());
        ReversibleHistory {
            steps: Vec::new(),
            roots,
            timestamp,
            costs,
        }
    }

    /// The recording executor (pinned costs + timestamp), so a recorded turn
    /// re-derives bit-identically on replay/undo.
    pub fn fresh_executor(&self) -> TurnExecutor {
        let mut e = TurnExecutor::new(self.costs.clone());
        e.set_timestamp(self.timestamp);
        e
    }

    /// The number of recorded steps (the head index).
    pub fn len(&self) -> usize {
        self.steps.len()
    }

    pub fn is_empty(&self) -> bool {
        self.steps.is_empty()
    }

    /// The recorded steps, in order.
    pub fn steps(&self) -> &[ReversibleStep] {
        &self.steps
    }

    /// The canonical root tooth after `step` steps (`step` in `0..=len()`).
    pub fn root_at(&self, step: usize) -> [u8; 32] {
        self.roots[step]
    }

    // --- recording (mirrors World's genesis + commit paths) -----------------

    /// Record a genesis install. Installs `cell` into `ledger` directly and
    /// appends the step + new root tooth.
    pub fn record_genesis(&mut self, ledger: &mut Ledger, cell: Cell) -> CellId {
        let id = cell.id();
        ledger
            .insert_cell(cell.clone())
            .expect("genesis insert is into a fresh slot");
        self.steps.push(ReversibleStep::Genesis { cell });
        self.roots.push(ledger.root());
        id
    }

    /// Record a committed turn (threads the chain head exactly as the live
    /// engine does). Returns the receipt on commit, or `None` if rejected (a
    /// rejected turn is NOT recorded — it did not change history).
    pub fn record_commit(
        &mut self,
        executor: &TurnExecutor,
        ledger: &mut Ledger,
        mut turn: Turn,
    ) -> Option<TurnReceipt> {
        turn.previous_receipt_hash = executor.get_last_receipt_hash(&turn.agent);
        match executor.execute(&turn, ledger) {
            TurnResult::Committed { receipt, .. } => {
                executor.set_last_receipt_hash(receipt.agent, receipt.receipt_hash());
                let post_root = ledger.root();
                self.steps.push(ReversibleStep::Committed {
                    turn,
                    receipt: receipt.clone(),
                    post_root,
                });
                self.roots.push(post_root);
                Some(receipt)
            }
            _ => None,
        }
    }

    // --- replay (forward, VERIFIED) -----------------------------------------

    /// Reconstruct the world at step `k` by REPLAY from genesis, verifying the
    /// reconstructed root against the recorded tooth. Fail-closed on mismatch.
    /// (The forward leg — `undo_to`'s landing must agree with this.)
    pub fn replay_to(&self, k: usize) -> Result<Ledger, ReversibleError> {
        if k > self.steps.len() {
            return Err(ReversibleError::OutOfRange {
                step: k,
                len: self.steps.len(),
            });
        }
        let mut ledger = Ledger::new();
        let executor = self.fresh_executor();
        for step in &self.steps[..k] {
            apply_step(&executor, &mut ledger, step)?;
        }
        let got = ledger.root();
        let want = self.roots[k];
        if got != want {
            return Err(ReversibleError::RootMismatch { step: k, got, want });
        }
        Ok(ledger)
    }

    // --- undo (backward, VERIFIED) ------------------------------------------

    /// Reverse history back to step `k` by building and applying the inverse
    /// turns for steps `k+1..head`, in **reverse order**, each gated by the
    /// executor — the backward dual of [`Self::replay_to`]
    /// (`FIRST-CLASS-REVERSIBILITY.md` §3.2 / §5.2).
    ///
    /// Fail-closed at the irreversible boundary: if any step in `k+1..head`
    /// contains a committed effect (a settled spend, a burn, a revoke, a nonce
    /// bump), `undo_to` refuses with [`ReversibleError::IrreversibleStep`] —
    /// you can only undo *within the reversible window* above the most recent
    /// commit.
    ///
    /// The verification is the **same root tooth, run backward**: after undoing
    /// back to `k`, the reconstructed root MUST equal `roots[k]`. Two ways to
    /// reach step `k` — replay-forward-from-genesis and undo-backward-from-head
    /// — must land on the identical verified root (the reversibility analog of
    /// `recover = replay`).
    ///
    /// Returns the ledger reconstructed at step `k` (the undo's landing).
    pub fn undo_to(&self, k: usize) -> Result<Ledger, ReversibleError> {
        let head = self.steps.len();
        if k > head {
            return Err(ReversibleError::OutOfRange { step: k, len: head });
        }

        // Start from the verified head state and walk backward.
        let mut ledger = self.replay_to(head)?;
        let executor = self.fresh_executor();
        // Prime the executor's per-agent chain-head table to the head by
        // replaying through `head` (so each inverse un-turn chains correctly as
        // a fresh forward turn in the agent's chain).
        {
            let mut warm = Ledger::new();
            for step in &self.steps[..head] {
                apply_step(&executor, &mut warm, step)?;
            }
        }

        // Walk steps head-1 .. k (inclusive of k+1, exclusive lower bound k),
        // most-recent-first — the causal cone reversed.
        for idx in (k..head).rev() {
            let step = &self.steps[idx];
            let ReversibleStep::Committed { turn, .. } = step else {
                // A genesis step in the undo window: its inverse is "retire the
                // freshly-born cell". Genesis installs are at the bottom of
                // history; if k sits below a genesis step, undoing it would
                // remove a cell. We treat reaching a genesis step as the
                // reversible floor and fail-closed (you cannot un-create the
                // genesis substrate via the un-turn — that is a destroy, a
                // committed move).
                return Err(ReversibleError::IrreversibleStep {
                    step: idx,
                    reason: CommittedReason::GenerativeOrProofCarrying,
                });
            };

            // The pre-state for this turn is the world at step `idx` (before it
            // applied) — reconstruct + verify it from the recorded history.
            let pre = self.replay_to(idx)?;

            // Build the inverse turn against that pre-state; fail-closed if any
            // effect is committed (the irreversibility wall).
            let inverse = turn.invert(&pre).map_err(|e| match e {
                InvertError::ContainsCommitted { reason, .. } => {
                    ReversibleError::IrreversibleStep { step: idx, reason }
                }
            })?;

            // Apply the inverse as an ordinary, gated turn through the executor.
            // The inverse turn's nonce is the agent's CURRENT nonce in the live
            // (being-undone) ledger — `Turn::invert` cannot know it without the
            // post-state, so the recorder supplies it here (the un-turn is a
            // fresh forward turn in the agent's chain, not a rewrite).
            let mut inv = inverse;
            inv.nonce = ledger
                .get(&inv.agent)
                .map(|c| c.state.nonce())
                .unwrap_or(inv.nonce);
            inv.previous_receipt_hash = executor.get_last_receipt_hash(&inv.agent);
            match executor.execute(&inv, &mut ledger) {
                TurnResult::Committed { receipt, .. } => {
                    executor.set_last_receipt_hash(receipt.agent, receipt.receipt_hash());
                }
                other => {
                    return Err(ReversibleError::InverseRejected {
                        step: idx,
                        reason: format!("{other:?}"),
                    });
                }
            }
        }

        // The root tooth, run backward — with the HONEST nonce caveat.
        //
        // Re-applying each inverse turn through the executor advances the
        // agent's NONCE (the freshness ratchet, §4.2 — a monotone counter that
        // *cannot* run backward; it is the canonical committed action at the
        // per-turn granularity). So the undone ledger reproduces the recorded
        // pre-state's VALUE/STATE (balances, fields, caps) exactly, but carries
        // ADVANCED nonces. The canonical `Ledger::root` binds the nonce, so a
        // raw root equality would (correctly) fail — undoing does not, and must
        // not, rewind the freshness ratchet.
        //
        // The verification is therefore the root tooth run backward MODULO the
        // monotone nonce: the undone ledger must agree with the recorded
        // pre-state `replay_to(k)` on every observable EXCEPT the nonce ratchet
        // (which only ever advances). This is RCCS's committed-action boundary
        // made precise: the reversible substrate restores state; the freshness
        // ratchet is the island of irreversibility every turn carries.
        let historical = self.replay_to(k)?;
        if !ledgers_agree_modulo_nonce(&ledger, &historical) {
            return Err(ReversibleError::RootMismatch {
                step: k,
                got: ledger.root(),
                want: self.roots[k],
            });
        }
        Ok(ledger)
    }

    /// Is the window `k+1..head` fully reversible (no committed step)? A cheap
    /// pre-check that does not mutate state — surfaces the boundary to a UI
    /// (the "rewind" button greys out below the most recent commit).
    pub fn window_reversible(&self, k: usize) -> bool {
        let head = self.steps.len();
        if k > head {
            return false;
        }
        for idx in k..head {
            match &self.steps[idx] {
                ReversibleStep::Genesis { .. } => return false,
                ReversibleStep::Committed { turn, .. } => {
                    // Reconstruct the pre-state to test invertibility honestly.
                    let Ok(pre) = self.replay_to(idx) else {
                        return false;
                    };
                    if turn.invert(&pre).is_err() {
                        return false;
                    }
                }
            }
        }
        true
    }

    /// **Causal-consistency check: can the single turn at step-index `idx` be
    /// undone *in isolation*, leaving the turns above it standing?**
    ///
    /// This is the honest answer to "can I only undo the most-recent turn?".
    /// `undo_to(k)` reverses the *contiguous suffix* `idx >= k` most-recent-first
    /// — the conservative reading of RCCS causal-consistency that treats
    /// *time-order* as the causal order (sound: it over-approximates the causal
    /// cone). But a *middle* turn can be undone in isolation iff **nothing
    /// causally downstream depends on it** — concretely, iff no later turn
    /// touches any cell this turn wrote (`FIRST-CLASS-REVERSIBILITY.md` §1.2).
    /// When that holds, isolated reversal is causal-consistent and *would* be
    /// sound; this method reports it (the maximally-permissive frontier, not yet
    /// wired into a mutating `undo_isolated` — that is the §3.3 follow-up).
    ///
    /// Returns `false` if the turn itself is irreversible (committed effect), if
    /// `idx` is a genesis step, or if any later turn shares a touched cell.
    pub fn can_undo_isolated(&self, idx: usize) -> bool {
        let head = self.steps.len();
        if idx >= head {
            return false;
        }
        let ReversibleStep::Committed { turn, .. } = &self.steps[idx] else {
            return false;
        };
        // The turn must itself be reversible against its pre-state.
        let Ok(pre) = self.replay_to(idx) else {
            return false;
        };
        if turn.invert(&pre).is_err() {
            return false;
        }
        // The cells this turn touched.
        let mine = turn_touched_cells(turn);
        // No LATER turn may touch any of them (else it causally depends on this
        // turn's write — undoing in isolation would leave it dangling).
        for later in &self.steps[idx + 1..] {
            if let ReversibleStep::Committed { turn: lt, .. } = later {
                for c in turn_touched_cells(lt) {
                    if mine.contains(&c) {
                        return false;
                    }
                }
            }
        }
        true
    }
}

/// The set of cells a turn touches (reads-or-writes), derived from its effects —
/// the causal footprint used by [`ReversibleHistory::can_undo_isolated`].
fn turn_touched_cells(turn: &Turn) -> std::collections::BTreeSet<CellId> {
    let mut set = std::collections::BTreeSet::new();
    set.insert(turn.agent);
    for tree in turn.call_forest.iter_dfs() {
        set.insert(tree.action.target);
        for e in &tree.action.effects {
            match e {
                Effect::Transfer { from, to, .. } => {
                    set.insert(*from);
                    set.insert(*to);
                }
                Effect::SetField { cell, .. }
                | Effect::RevokeCapability { cell, .. }
                | Effect::IncrementNonce { cell }
                | Effect::SetPermissions { cell, .. }
                | Effect::SetVerificationKey { cell, .. }
                | Effect::EmitEvent { cell, .. } => {
                    set.insert(*cell);
                }
                Effect::GrantCapability { from, to, .. } => {
                    set.insert(*from);
                    set.insert(*to);
                }
                Effect::CellSeal { target, .. }
                | Effect::CellUnseal { target }
                | Effect::CellDestroy { target, .. }
                | Effect::Burn { target, .. }
                | Effect::MakeSovereign { cell: target } => {
                    set.insert(*target);
                }
                Effect::Introduce {
                    introducer,
                    recipient,
                    target,
                    ..
                } => {
                    set.insert(*introducer);
                    set.insert(*recipient);
                    set.insert(*target);
                }
                _ => {}
            }
        }
    }
    set
}

/// Apply one recorded step to a ledger under a (warm) executor, re-deriving it.
fn apply_step(
    executor: &TurnExecutor,
    ledger: &mut Ledger,
    step: &ReversibleStep,
) -> Result<(), ReversibleError> {
    match step {
        ReversibleStep::Genesis { cell } => {
            let _ = ledger.insert_cell(cell.clone());
            Ok(())
        }
        ReversibleStep::Committed { turn, receipt, .. } => {
            let mut t = turn.clone();
            t.previous_receipt_hash = executor.get_last_receipt_hash(&t.agent);
            match executor.execute(&t, ledger) {
                TurnResult::Committed { receipt: r, .. } => {
                    executor.set_last_receipt_hash(r.agent, r.receipt_hash());
                    Ok(())
                }
                other => {
                    let _ = receipt;
                    Err(ReversibleError::NondeterministicReplay {
                        step: 0,
                        got: format!("{other:?}"),
                    })
                }
            }
        }
    }
}

/// The primary cell whose authority an inverse action exercises — the cell the
/// inverse action should target so the executor's `from == action_target`
/// fast-path holds (the un-turn is gated by the same authority the forward turn
/// needed). `None` for an inverse effect with no explicit cell argument
/// (`RefreshDelegation`), so the caller keeps the forward action's target.
fn inverse_primary_cell(inv_effects: &[Effect]) -> Option<CellId> {
    match inv_effects.first()? {
        Effect::Transfer { from, .. } => Some(*from),
        Effect::SetField { cell, .. } => Some(*cell),
        Effect::RevokeCapability { cell, .. } => Some(*cell),
        Effect::GrantCapability { from, .. } => Some(*from),
        Effect::SetPermissions { cell, .. } => Some(*cell),
        Effect::SetVerificationKey { cell, .. } => Some(*cell),
        Effect::EmitEvent { cell, .. } => Some(*cell),
        Effect::CellSeal { target, .. } => Some(*target),
        Effect::CellUnseal { target } => Some(*target),
        // RefreshDelegation (and any future no-cell inverse) keeps the forward
        // action's target.
        _ => None,
    }
}

/// Do two ledgers agree on every observable EXCEPT the monotone nonce ratchet?
///
/// The un-turn restores value/state (balances, fields, capabilities) but cannot
/// rewind the freshness nonce (the per-turn committed action, §4.2). This is the
/// "root tooth, run backward, modulo the ratchet" verification: same cells, same
/// balances, same fields, same cap-set size, with `undone.nonce >= historical`
/// (the ratchet only advances). A `false` is the fail-closed anti-substitution
/// catch (an undo that landed on the wrong *state*).
pub fn ledgers_agree_modulo_nonce(undone: &Ledger, historical: &Ledger) -> bool {
    let um: BTreeMap<[u8; 32], &Cell> =
        undone.iter().map(|(id, c)| (*id.as_bytes(), c)).collect();
    let hm: BTreeMap<[u8; 32], &Cell> =
        historical.iter().map(|(id, c)| (*id.as_bytes(), c)).collect();
    if um.len() != hm.len() {
        return false;
    }
    for (id, hc) in &hm {
        let Some(uc) = um.get(id) else {
            return false;
        };
        if uc.state.balance() != hc.state.balance()
            || uc.state.fields != hc.state.fields
            || uc.capabilities != hc.capabilities
        {
            return false;
        }
        // The nonce may only have ADVANCED (the ratchet); never regressed.
        if uc.state.nonce() < hc.state.nonce() {
            return false;
        }
    }
    true
}

/// Compute the diff between two ledgers (the changed cells/balances) — a small
/// helper for tests / the rewind UI. Sorted by cell id.
pub fn changed_cells(a: &Ledger, b: &Ledger) -> Vec<CellId> {
    let am: BTreeMap<[u8; 32], &Cell> = a.iter().map(|(id, c)| (*id.as_bytes(), c)).collect();
    let bm: BTreeMap<[u8; 32], &Cell> = b.iter().map(|(id, c)| (*id.as_bytes(), c)).collect();
    let mut out: Vec<CellId> = Vec::new();
    for (id, cb) in &bm {
        match am.get(id) {
            None => out.push(CellId::from_bytes(*id)),
            Some(ca) => {
                if ca.state.balance() != cb.state.balance()
                    || ca.state.fields != cb.state.fields
                    || ca.capabilities.len() != cb.capabilities.len()
                    || ca.state.nonce() != cb.state.nonce()
                {
                    out.push(CellId::from_bytes(*id));
                }
            }
        }
    }
    for (id, _) in &am {
        if !bm.contains_key(id) {
            out.push(CellId::from_bytes(*id));
        }
    }
    out.sort_by(|x, y| x.as_bytes().cmp(y.as_bytes()));
    out
}

// ===========================================================================
// Tests — the M-REV-0 headline + per-effect invert round-trips
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::action::Effect;
    use crate::builder::{ActionBuilder, TurnBuilder};
    use dregg_cell::{AuthRequired, Cell, Permissions};

    // --- fixtures -----------------------------------------------------------

    /// An open cell (no auth required for anything) — accepts `Unchecked`
    /// authorization, so an un-turn (which carries `Unchecked`) is gated only by
    /// the open permissions (the demo/test substrate; a gated cell would require
    /// the reversal turn to re-authorize).
    fn open_cell(seed: u8, balance: i64) -> Cell {
        let pk = [seed; 32];
        let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
        cell.permissions = Permissions {
            send: AuthRequired::None,
            receive: AuthRequired::None,
            set_state: AuthRequired::None,
            set_permissions: AuthRequired::None,
            set_verification_key: AuthRequired::None,
            increment_nonce: AuthRequired::None,
            delegate: AuthRequired::None,
            access: AuthRequired::None,
        };
        cell
    }

    /// A bare unchecked turn with the given effects, authored by `agent`. The
    /// action targets the agent itself (the executor-test template shape: the
    /// action target is the actor, and Transfer's `from` is the actor).
    fn turn_with(agent: CellId, nonce: u64, effects: Vec<Effect>) -> Turn {
        let mut ab = ActionBuilder::new_unchecked_for_tests(agent, "act", agent);
        for e in effects {
            ab = ab.effect(e);
        }
        let mut tb = TurnBuilder::new(agent, nonce);
        tb.add_action(ab.build());
        tb.fee(0).build()
    }

    fn nonce_of(l: &Ledger, id: &CellId) -> u64 {
        l.get(id).map(|c| c.state.nonce()).unwrap_or(0)
    }

    // --- THE HEADLINE: undo-backward == replay-forward, same verified root ---

    #[test]
    fn undo_to_lands_on_the_same_verified_state_as_replay_to() {
        // A fixture history of CLEAN turns only (transfers + a set-field), so the
        // whole window is reversible. Undo-backward-from-head must land on the
        // SAME verified STATE as replay-forward-from-genesis, for every k —
        // modulo the monotone nonce ratchet (which the un-turn cannot, and must
        // not, rewind; §4.2). This is the backward companion to recover=replay.
        let mut h = ReversibleHistory::new(1_700_000_000);
        let mut l = Ledger::new();
        let ex = h.fresh_executor();

        let a = h.record_genesis(&mut l, open_cell(1, 1_000));
        let b = h.record_genesis(&mut l, open_cell(2, 0));

        let t1 = turn_with(a, nonce_of(&l, &a), vec![Effect::Transfer { from: a, to: b, amount: 100 }]);
        assert!(h.record_commit(&ex, &mut l, t1).is_some(), "t1 must commit");
        let t2 = turn_with(a, nonce_of(&l, &a), vec![Effect::Transfer { from: a, to: b, amount: 50 }]);
        assert!(h.record_commit(&ex, &mut l, t2).is_some(), "t2 must commit");
        let t3 = turn_with(b, nonce_of(&l, &b), vec![Effect::SetField { cell: b, index: 0, value: [7u8; 32] }]);
        assert!(h.record_commit(&ex, &mut l, t3).is_some(), "t3 must commit");
        let t4 = turn_with(b, nonce_of(&l, &b), vec![Effect::Transfer { from: b, to: a, amount: 30 }]);
        assert!(h.record_commit(&ex, &mut l, t4).is_some(), "t4 must commit");

        // 2 genesis + 4 turns = 6 steps.
        assert_eq!(h.len(), 6);

        // For every reversible cursor k (k >= 2 so we never undo a genesis
        // step), undo_to(k) and replay_to(k) land on ledgers that agree on
        // every observable except the monotone nonce. (`undo_to` itself runs
        // this exact check internally and fail-closes on mismatch, so a returned
        // `Ok` already proves the equality; we re-assert it here for the test's
        // explicitness.)
        for k in 2..=h.len() {
            let fwd = h.replay_to(k).expect("forward replay must verify");
            let bwd = h.undo_to(k).expect("backward undo must verify (state modulo nonce)");
            assert!(
                ledgers_agree_modulo_nonce(&bwd, &fwd),
                "undo_to({k}) state != replay_to({k}) state (modulo nonce)",
            );
            // The value/state observables (balances, fields) match exactly.
            assert!(
                changed_cells(&bwd, &fwd)
                    .iter()
                    .all(|id| bwd.get(id).map(|c| c.state.nonce())
                        != fwd.get(id).map(|c| c.state.nonce())),
                "any residual difference at k={k} is the nonce ratchet only",
            );
        }

        // window_reversible agrees: the whole clean window is reversible.
        assert!(h.window_reversible(2), "the clean window above genesis is reversible");
    }

    // --- per-effect invert round-trips (clean + contextual) -----------------

    #[test]
    fn transfer_inverts_clean() {
        let mut l = Ledger::new();
        let a = open_cell(1, 1_000).id();
        let b = open_cell(2, 0).id();
        l.insert_cell(open_cell(1, 1_000)).unwrap();
        l.insert_cell(open_cell(2, 0)).unwrap();
        let e = Effect::Transfer { from: a, to: b, amount: 100 };
        match e.invert(&l) {
            Inversion::Clean(Effect::Transfer { from, to, amount }) => {
                assert_eq!((from, to, amount), (b, a, 100), "inverse swaps direction");
            }
            other => panic!("transfer must invert Clean, got {other:?}"),
        }
    }

    #[test]
    fn grant_inverts_clean_to_revoke() {
        use dregg_cell::CapabilityRef;
        let mut l = Ledger::new();
        let a = open_cell(1, 0).id();
        let b = open_cell(2, 0).id();
        l.insert_cell(open_cell(1, 0)).unwrap();
        l.insert_cell(open_cell(2, 0)).unwrap();
        let cap = CapabilityRef {
            target: b,
            slot: 3,
            permissions: AuthRequired::None,
            breadstuff: None,
            expires_at: None,
            allowed_effects: None,
            stored_epoch: None,
        };
        let e = Effect::GrantCapability { from: a, to: b, cap };
        match e.invert(&l) {
            Inversion::Clean(Effect::RevokeCapability { cell, slot }) => {
                assert_eq!((cell, slot), (b, 3), "grant inverts to a revoke of its slot");
            }
            other => panic!("grant must invert Clean to RevokeCapability, got {other:?}"),
        }
    }

    #[test]
    fn seal_and_unseal_are_a_clean_pair() {
        let mut l = Ledger::new();
        let c = open_cell(1, 0).id();
        l.insert_cell(open_cell(1, 0)).unwrap();
        let seal = Effect::CellSeal { target: c, reason: [9u8; 32] };
        assert!(matches!(seal.invert(&l), Inversion::Clean(Effect::CellUnseal { target }) if target == c));
        let unseal = Effect::CellUnseal { target: c };
        assert!(matches!(unseal.invert(&l), Inversion::Contextual(Effect::CellSeal { target, .. }) if target == c));
    }

    #[test]
    fn set_field_inverts_contextual_to_the_old_value() {
        // The contextual inverse reads the OLD field value from the pre-state.
        let mut l = Ledger::new();
        let mut cell = open_cell(1, 0);
        cell.state.fields[0] = [5u8; 32]; // the pre-image value
        let c = cell.id();
        l.insert_cell(cell).unwrap();
        let e = Effect::SetField { cell: c, index: 0, value: [99u8; 32] };
        match e.invert(&l) {
            Inversion::Contextual(Effect::SetField { cell, index, value }) => {
                assert_eq!(cell, c);
                assert_eq!(index, 0);
                assert_eq!(value, [5u8; 32], "inverse restores the pre-image value");
            }
            other => panic!("SetField must invert Contextual, got {other:?}"),
        }
    }

    /// The end-to-end round trip: a clean turn, applied then un-applied through
    /// the executor, restores the prior VALUE state exactly (balances back to
    /// where they were) — modulo the monotone nonce ratchet.
    #[test]
    fn applying_then_inverting_a_transfer_restores_the_value_state() {
        let mut h = ReversibleHistory::new(1_700_000_000);
        let mut l = Ledger::new();
        let ex = h.fresh_executor();
        let a = h.record_genesis(&mut l, open_cell(1, 1_000));
        let b = h.record_genesis(&mut l, open_cell(2, 0));
        let pre = h.replay_to(h.len()).unwrap();
        let a_bal_before = pre.get(&a).unwrap().state.balance();
        let b_bal_before = pre.get(&b).unwrap().state.balance();

        let t = turn_with(a, nonce_of(&l, &a), vec![Effect::Transfer { from: a, to: b, amount: 250 }]);
        assert!(h.record_commit(&ex, &mut l, t).is_some());
        assert_ne!(h.root_at(h.len()), pre.clone().root(), "the transfer moved the root");

        // Undo back to the pre-transfer cursor (step 2 = both genesis cells).
        // `undo_to` internally verifies "state modulo nonce" and fail-closes
        // otherwise, so a returned Ok already proves the value-state restore.
        let undone = h.undo_to(2).expect("undo must verify (state modulo nonce)");
        assert_eq!(undone.get(&a).unwrap().state.balance(), a_bal_before, "a balance restored");
        assert_eq!(undone.get(&b).unwrap().state.balance(), b_bal_before, "b balance restored");
        assert!(
            ledgers_agree_modulo_nonce(&undone, &pre),
            "un-turn restored the prior value-state (modulo the nonce ratchet)",
        );
    }

    // --- FAIL-CLOSED at the irreversible boundary ---------------------------

    #[test]
    fn increment_nonce_is_committed() {
        let mut l = Ledger::new();
        let c = open_cell(1, 0).id();
        l.insert_cell(open_cell(1, 0)).unwrap();
        assert!(matches!(
            Effect::IncrementNonce { cell: c }.invert(&l),
            Inversion::Committed(CommittedReason::FreshnessRatchet)
        ));
    }

    #[test]
    fn burn_and_notespend_and_revoke_are_committed() {
        let l = Ledger::new();
        let c = open_cell(1, 0).id();
        assert!(matches!(
            Effect::Burn { target: c, slot: 0, amount: 1 }.invert(&l),
            Inversion::Committed(CommittedReason::ValueBurned)
        ));
        assert!(matches!(
            Effect::RevokeCapability { cell: c, slot: 0 }.invert(&l),
            Inversion::Committed(CommittedReason::AuthorityRevoked)
        ));
        assert!(matches!(
            Effect::MakeSovereign { cell: c }.invert(&l),
            Inversion::Committed(CommittedReason::TerminalLifecycle)
        ));
        assert!(matches!(
            Effect::AttenuateCapability {
                cell: c,
                slot: 0,
                narrower_permissions: AuthRequired::None,
                narrower_effects: None,
                narrower_expiry: None,
            }
            .invert(&l),
            Inversion::Committed(CommittedReason::MonotoneNarrowing)
        ));
    }

    #[test]
    fn turn_invert_fails_closed_on_a_committed_effect() {
        let mut l = Ledger::new();
        let a = open_cell(1, 100).id();
        l.insert_cell(open_cell(1, 100)).unwrap();
        // A turn that bumps a nonce (committed) — Turn::invert must refuse.
        let t = turn_with(a, 0, vec![Effect::IncrementNonce { cell: a }]);
        match t.invert(&l) {
            Err(InvertError::ContainsCommitted { reason, .. }) => {
                assert_eq!(reason, CommittedReason::FreshnessRatchet);
            }
            other => panic!("a committed turn must fail-closed, got {other:?}"),
        }
        assert!(!t.is_reversible(&l));
    }

    #[test]
    fn can_undo_isolated_tracks_the_causal_footprint() {
        // Three independent cells a,b,c. Turn on (a→b), then a DISJOINT turn on
        // c (touches neither a nor b). The middle turn CAN be undone in
        // isolation (nothing later depends on it); the same is not true once a
        // later turn shares its cells.
        let mut h = ReversibleHistory::new(1_700_000_000);
        let mut l = Ledger::new();
        let ex = h.fresh_executor();
        let a = h.record_genesis(&mut l, open_cell(1, 1_000)); // idx 0
        let b = h.record_genesis(&mut l, open_cell(2, 0)); // idx 1
        let c = h.record_genesis(&mut l, open_cell(3, 500)); // idx 2
        let d = h.record_genesis(&mut l, open_cell(4, 0)); // idx 3

        // idx 4: a→b. idx 5: c→d (disjoint from a,b).
        let t_ab = turn_with(a, nonce_of(&l, &a), vec![Effect::Transfer { from: a, to: b, amount: 100 }]);
        assert!(h.record_commit(&ex, &mut l, t_ab).is_some());
        let t_cd = turn_with(c, nonce_of(&l, &c), vec![Effect::Transfer { from: c, to: d, amount: 50 }]);
        assert!(h.record_commit(&ex, &mut l, t_cd).is_some());

        // The a→b turn (idx 4) is followed only by the DISJOINT c→d turn → it
        // can be undone in isolation (nothing downstream depends on it).
        assert!(h.can_undo_isolated(4), "a→b is causally independent of the later c→d");
        // The top turn (idx 5) trivially has nothing above it.
        assert!(h.can_undo_isolated(5), "the most-recent turn is always isolable");

        // Now append a turn that DOES touch a → the a→b turn (idx 4) is no longer
        // isolable (a later turn causally depends on a's state).
        let t_a2 = turn_with(a, nonce_of(&l, &a), vec![Effect::SetField { cell: a, index: 0, value: [1u8; 32] }]);
        assert!(h.record_commit(&ex, &mut l, t_a2).is_some());
        assert!(!h.can_undo_isolated(4), "a later turn now touches a → not isolable");
        // Genesis steps are never isolable via the un-turn (un-create = destroy).
        assert!(!h.can_undo_isolated(0));
    }

    #[test]
    fn undo_to_refuses_to_cross_a_committed_step() {
        // History: genesis ×2 (a, b), then a COMMITTED nonce bump (the island of
        // irreversibility), then a CLEAN transfer on top. undo_to *below* the
        // commit must fail-closed; undo_to of the clean tail (above the commit)
        // must succeed.
        let mut h = ReversibleHistory::new(1_700_000_000);
        let mut l = Ledger::new();
        let ex = h.fresh_executor();
        let a = h.record_genesis(&mut l, open_cell(1, 1_000)); // step idx 0
        let b = h.record_genesis(&mut l, open_cell(2, 0)); // step idx 1

        // The COMMITTED step (idx 2): an explicit nonce bump on `a`.
        let committed = turn_with(a, nonce_of(&l, &a), vec![Effect::IncrementNonce { cell: a }]);
        assert!(h.record_commit(&ex, &mut l, committed).is_some());
        // The CLEAN tail (idx 3): a transfer above the commit.
        let clean = turn_with(a, nonce_of(&l, &a), vec![Effect::Transfer { from: a, to: b, amount: 40 }]);
        assert!(h.record_commit(&ex, &mut l, clean).is_some());

        // head = 4. The recorded steps (0-based idx) are:
        //   idx 0,1 = genesis(a), genesis(b)
        //   idx 2   = COMMITTED nonce bump  (produces roots[3])
        //   idx 3   = CLEAN transfer        (produces roots[4])
        // `undo_to(k)` reverses every step with idx >= k (those produced a root
        // above roots[k]).

        // undo_to(head) is the identity (reverses nothing) — always ok.
        assert!(h.undo_to(4).is_ok(), "undo_to(head) is the no-op identity");
        // undo_to(3) reverses only idx 3 (the clean transfer) and lands on
        // roots[3] — the reversible tail ABOVE the commit. Must succeed.
        assert!(
            h.undo_to(3).is_ok(),
            "undoing the clean tail above the most recent commit must succeed",
        );

        // undo_to(2) would reverse idx 3 AND idx 2 — crossing the COMMITTED nonce
        // bump at idx 2 → fail-closed with IrreversibleStep.
        let err = h.undo_to(2);
        assert!(
            matches!(err, Err(ReversibleError::IrreversibleStep { step: 2, reason: CommittedReason::FreshnessRatchet })),
            "undo across a committed step must fail-closed, got {err:?}",
        );
        // undo_to(1) also crosses the commit → fail-closed.
        assert!(matches!(
            h.undo_to(1),
            Err(ReversibleError::IrreversibleStep { step: 2, .. })
        ));

        // window_reversible agrees: the clean tail (k=3) is reversible; any
        // window crossing the commit (k<=2) is not.
        assert!(h.window_reversible(3), "the clean tail is reversible");
        assert!(!h.window_reversible(2), "crossing the commit is not reversible");
        assert!(!h.window_reversible(1), "crossing the commit is not reversible");
    }
}
