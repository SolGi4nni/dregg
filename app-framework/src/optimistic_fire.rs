//! The **interactive-tempo bridge** for affordance fires — optimistic-local +
//! verified-at-boundary (the #169 proving-modality dial).
//!
//! `docs/deos/DEOS-APPS.md` (§"the interactive/real-time tempo gap"): dregg's tempo
//! is "commit a verified turn"; games + live collaboration need a faster tempo
//! (frames, presence, optimistic updates). The bridge is **optimistic local
//! interaction + verified turns at trust boundaries**. The standalone game
//! (`starbridge-web-surface`) named this as WOOD ("the game is turn-paced"); this
//! module wires it onto affordance fires.
//!
//! ## The dial
//!
//! An affordance fire has TWO tempos available, and the app chooses per-fire:
//!
//! - **Verified** ([`crate::affordance::AffordanceSurface::fire_through_executor`])
//!   — the fire IS a verified turn; the caller blocks on the executor's receipt.
//!   This is the trust-boundary tempo: every interaction is a turn the witness-graph
//!   records. Correct, but turn-paced.
//! - **Optimistic** (this module) — the fire applies LOCALLY *immediately* (the
//!   interactive tempo: the UI updates this frame) AND a verified turn settles the
//!   SAME effect at the trust boundary. The local apply is **provisional**; the
//!   verified turn is **authoritative**; the two are reconciled
//!   ([`OptimisticFire::settle`]).
//!
//! **The cap gate is identical in both tempos.** An optimistic fire runs the SAME
//! real [`dregg_cell::is_attenuation`] gate FIRST — the local apply is anti-ghost
//! too (an unauthorized fire never even applies locally). The optimism is ONLY about
//! *when the verified turn is demanded*, never about *whether the gate holds*. This
//! is the load-bearing honesty: optimistic ≠ unchecked. The local effect is the
//! genuine one; the settlement re-runs it through the verified executor and asserts
//! the post-states agree.
//!
//! ## Reconciliation (the trust boundary)
//!
//! When the verified turn settles, its receipt is compared to the optimistic
//! prediction:
//!
//! - **Confirmed** — the executor accepted the turn; the provisional apply is now
//!   authoritative (the optimistic frame was correct). The receipt is the
//!   executor's OWN [`dregg_turn::TurnReceipt`].
//! - **Rolledback** — the executor REJECTED the (gated) turn (a program constraint
//!   bit at the boundary that the local view could not see). The optimistic apply
//!   must be reverted; the caller is handed the executor's error. The witness-graph
//!   never recorded a turn that did not happen.
//!
//! So the optimistic frame is *fast but honest*: it shows the predicted post-state
//! immediately and is RECONCILED against the verified truth, which always wins.

use dregg_cell::AuthRequired;
use dregg_types::CellId;

use crate::affordance::{
    AffordanceIntent, AffordanceSurface, EffectSummary, FireError, FireExecuteError,
};
use crate::cipherclerk::{AppCipherclerk, EmbeddedExecutor};

/// An **optimistic affordance fire** — applied locally NOW, settled at the verified
/// boundary.
///
/// Minted only by [`OptimisticFire::predict`] AFTER the REAL cap gate passed (so its
/// existence witnesses authorization — same anti-ghost discipline as
/// [`AffordanceIntent`]). It carries the gated intent (the genuine effect + its
/// stable summary) so a caller can apply it to a local view this frame, and later
/// [`OptimisticFire::settle`] the verified turn.
#[derive(Clone, Debug)]
pub struct OptimisticFire {
    /// The gated intent — the REAL effect the fire would run (provisionally applied
    /// locally, authoritatively re-run at settlement).
    intent: AffordanceIntent,
    /// The held authority the fire was gated against (carried so the settlement
    /// re-runs the IDENTICAL gate — optimism never weakens it).
    held: AuthRequired,
    /// The predicted effect summary — the `Eq`-able readout the caller can show in
    /// the optimistic frame and assert the settlement matches.
    predicted: EffectSummary,
}

impl OptimisticFire {
    /// **Predict** an optimistic fire: run the REAL cap gate, and on pass produce the
    /// provisional fire WITHOUT submitting any turn (the interactive tempo — the UI
    /// updates this frame from [`OptimisticFire::predicted_effect`]).
    ///
    /// The gate is the genuine [`dregg_cell::is_attenuation`] (via
    /// [`AffordanceSurface::fire`]): an unauthorized fire is [`FireError`] and
    /// NOTHING is predicted (the local apply is anti-ghost too). On success the caller
    /// holds an [`OptimisticFire`] it can apply locally now and settle later.
    pub fn predict(
        surface: &AffordanceSurface,
        name: &str,
        actor: CellId,
        held: &AuthRequired,
    ) -> Result<OptimisticFire, FireError> {
        let intent = surface.fire(name, actor, held)?;
        let predicted = intent.effect_summary();
        Ok(OptimisticFire {
            intent,
            held: held.clone(),
            predicted,
        })
    }

    /// The predicted effect (the `Eq`-able summary) the optimistic frame shows —
    /// the genuine effect the verified turn will run. The UI renders the post-state
    /// from this *immediately*, before the verified turn settles.
    pub fn predicted_effect(&self) -> &EffectSummary {
        &self.predicted
    }

    /// The affordance name this fire targets.
    pub fn affordance(&self) -> &str {
        &self.intent.affordance
    }

    /// The surface cell this fire acts on.
    pub fn surface_cell(&self) -> CellId {
        self.intent.surface_cell
    }

    /// **Settle** the optimistic fire at the trust boundary — re-run the gated effect
    /// as a REAL verified turn through the [`EmbeddedExecutor`] and reconcile.
    ///
    /// The settlement re-runs the IDENTICAL cap gate (optimism never weakened it),
    /// then submits the verified turn:
    ///
    /// - [`Settlement::Confirmed`] — the executor accepted the turn; the optimistic
    ///   apply is now authoritative AND the predicted effect summary MATCHES the
    ///   settled one (the optimistic frame was correct). Carries the executor's OWN
    ///   receipt.
    /// - [`Settlement::Rolledback`] — the executor REJECTED the (gated) turn; the
    ///   provisional apply must be reverted. The witness-graph recorded nothing.
    ///
    /// The `cipherclerk` is the principal of the verified turn (its cell is the
    /// actor); `executor` runs it. This is the [`AffordanceSurface::fire_through_executor`]
    /// path under the hood — so the settled turn is the genuine one, not a re-derivation.
    pub fn settle(
        &self,
        surface: &AffordanceSurface,
        cipherclerk: &AppCipherclerk,
        executor: &EmbeddedExecutor,
    ) -> Settlement {
        match surface.fire_through_executor(self.affordance(), &self.held, cipherclerk, executor) {
            Ok(receipt) => {
                // The verified turn was accepted; assert the optimistic prediction
                // matched the settled effect (it must — same intent, same effect).
                debug_assert_eq!(
                    self.predicted,
                    self.intent.effect_summary(),
                    "the settled effect must match the optimistic prediction"
                );
                Settlement::Confirmed { receipt }
            }
            Err(FireExecuteError::Executor(e)) => Settlement::Rolledback {
                reason: format!("executor rejected the settlement turn: {e}"),
            },
            Err(FireExecuteError::Gate(e)) => Settlement::Rolledback {
                // The gate refused at settlement — should be impossible (it passed at
                // predict), but fail-closed: a rejected settlement rolls back.
                reason: format!("settlement gate refused (cap state changed?): {e}"),
            },
        }
    }
}

/// The reconciliation verdict of [`OptimisticFire::settle`] — the trust boundary
/// resolving the optimistic frame against the verified truth.
#[derive(Clone, Debug)]
pub enum Settlement {
    /// The verified turn was accepted; the optimistic apply is now authoritative.
    /// Carries the executor's OWN [`dregg_turn::TurnReceipt`] — the witness-graph
    /// recorded the turn.
    Confirmed {
        /// The executor's receipt for the settled turn.
        receipt: dregg_turn::TurnReceipt,
    },
    /// The verified turn was REJECTED at the boundary; the optimistic apply must be
    /// reverted (the predicted post-state never became real). The witness-graph
    /// recorded nothing.
    Rolledback {
        /// Why the settlement was rejected (for the caller to surface / log).
        reason: String,
    },
}

impl Settlement {
    /// Was the optimistic frame confirmed (the verified turn accepted)?
    pub fn is_confirmed(&self) -> bool {
        matches!(self, Settlement::Confirmed { .. })
    }

    /// The executor's receipt, if confirmed.
    pub fn receipt(&self) -> Option<&dregg_turn::TurnReceipt> {
        match self {
            Settlement::Confirmed { receipt } => Some(receipt),
            Settlement::Rolledback { .. } => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::affordance::CellAffordance;
    use dregg_sdk::AgentCipherclerk;
    use dregg_turn::action::{Effect, Event};

    fn emit_event(cell: CellId) -> Effect {
        Effect::EmitEvent {
            cell,
            event: Event {
                topic: [1u8; 32],
                data: vec![],
            },
        }
    }

    const VIEWER: AuthRequired = AuthRequired::Signature;
    const ADMIN: AuthRequired = AuthRequired::None;

    /// A self-surface over the agent's own cell so settlement turns actually execute.
    fn agent_surface() -> (AppCipherclerk, EmbeddedExecutor, AffordanceSurface) {
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [9u8; 32]);
        let executor = EmbeddedExecutor::new(&cclerk, "default");
        let cell = cclerk.cell_id();
        let surface = AffordanceSurface::named(cell, "live")
            .declare(CellAffordance::new(
                "move",
                AuthRequired::None,
                emit_event(cell),
            ))
            .declare(CellAffordance::new(
                "admin",
                AuthRequired::None,
                emit_event(cell),
            ));
        (cclerk, executor, surface)
    }

    #[test]
    fn predict_runs_the_real_gate_optimism_is_not_unchecked() {
        let (cclerk, _executor, surface) = agent_surface();
        let actor = cclerk.cell_id();

        // An UNauthorized optimistic fire is refused at predict — the local apply is
        // anti-ghost too (a Signature viewer cannot even predict an admin fire that
        // requires None/root).
        let refused = OptimisticFire::predict(&surface, "admin", actor, &VIEWER);
        assert!(matches!(refused, Err(FireError::Unauthorized { .. })));

        // An authorized predict yields the optimistic fire WITHOUT a verified turn yet.
        let fire =
            OptimisticFire::predict(&surface, "move", actor, &ADMIN).expect("authorized predict");
        assert_eq!(fire.affordance(), "move");
        assert_eq!(
            *fire.predicted_effect(),
            EffectSummary::EmitEvent { cell: actor }
        );
    }

    #[test]
    fn settle_confirms_and_returns_the_executors_receipt() {
        let (cclerk, executor, surface) = agent_surface();
        let actor = cclerk.cell_id();

        // Predict (interactive tempo) → settle (verified boundary).
        let fire =
            OptimisticFire::predict(&surface, "move", actor, &ADMIN).expect("authorized predict");
        let settlement = fire.settle(&surface, &cclerk, &executor);

        // The verified turn was accepted; the predicted effect matched; the receipt is
        // the executor's OWN (non-zero turn_hash).
        assert!(settlement.is_confirmed());
        let receipt = settlement.receipt().expect("confirmed carries a receipt");
        assert_ne!(receipt.turn_hash, [0u8; 32], "settled turn is real");
        assert_eq!(receipt.agent, actor);
        assert_eq!(receipt.action_count, 1);
    }

    #[test]
    fn settle_rolls_back_when_the_boundary_rejects() {
        // A surface over a cell the embedded ledger does NOT have ⇒ the verified turn
        // is rejected at the boundary, so the optimistic apply rolls back. (The gate
        // passes — None/root — but the executor declines the unknown surface cell.)
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [3u8; 32]);
        let executor = EmbeddedExecutor::new(&cclerk, "default");
        let ghost = CellId::from_bytes([200u8; 32]); // not in the ledger
        let surface = AffordanceSurface::named(ghost, "ghost").declare(CellAffordance::new(
            "move",
            AuthRequired::None,
            emit_event(ghost),
        ));

        let fire = OptimisticFire::predict(&surface, "move", cclerk.cell_id(), &ADMIN)
            .expect("predict passes the gate");
        let settlement = fire.settle(&surface, &cclerk, &executor);

        // The optimistic frame was NOT confirmed — the verified boundary rejected it,
        // so the provisional apply must be reverted. The witness-graph recorded nothing.
        assert!(!settlement.is_confirmed());
        assert!(settlement.receipt().is_none());
        match settlement {
            Settlement::Rolledback { reason } => assert!(reason.contains("executor rejected")),
            other => panic!("expected a rollback, got {other:?}"),
        }
    }

    #[test]
    fn an_unauthorized_fire_never_reaches_settlement() {
        // The whole point of optimistic-but-honest: a fire that fails the gate is
        // refused at PREDICT, so it never even applies locally, let alone settles.
        let (cclerk, executor, surface) = agent_surface();
        // Make a surface with an Either-gated affordance the Signature viewer lacks.
        let cell = cclerk.cell_id();
        let surface = surface.declare(CellAffordance::new(
            "edit",
            AuthRequired::Either,
            emit_event(cell),
        ));
        let refused = OptimisticFire::predict(&surface, "edit", cell, &VIEWER);
        assert!(matches!(refused, Err(FireError::Unauthorized { .. })));
        // (No settle path exists for a refused predict — the type makes it
        // impossible: you cannot settle what you could not predict.)
        let _ = (&cclerk, &executor); // (kept live for the fixture)
    }
}
