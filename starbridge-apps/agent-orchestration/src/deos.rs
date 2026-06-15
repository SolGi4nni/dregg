//! # The orchestration board as a composed [`DeosApp`] — the live, per-viewer, cap-gated web surface.
//!
//! `docs/deos/DEOS.md` + `Dregg2/Deos/{GatedAffordance,WorkflowBridge}.lean`: a deos app is the SIX
//! kernel layers wired into ONE shape (cells × affordances, the SDK surface every fire routes through,
//! the web-of-cells distribution, the durable-state seam). This module re-expresses the agent
//! orchestration ON those bones — so the orchestration is not just a Rust API but a LIVE WEB SURFACE a
//! stranger fetches, projects their own button-set against, and fires through the verified executor.
//!
//! ## The rights ladder — `auditor ⊂ worker ⊂ coordinator` (`Signature ⊂ Either ⊂ None`)
//!
//! The board cell exposes three affordances on the progressive-attenuation ladder
//! ([`is_attenuation`]-ordered, mirroring the supply-chain verifier ⊂ custodian ⊂ manufacturer ladder):
//!
//!   * **`view_audit`** ([`AUDITOR_RIGHTS`] = `Signature`, cap-only) — an AUDITOR reads the run; the
//!     verdict is re-derived OFF the receipt chain ([`crate::audit_run`]). The narrowest tier: a holder
//!     of any rights at or above `Signature` may read.
//!   * **`worker_step`** ([`WORKER_RIGHTS`] = `Either`, **GATED** cap∧state) — a WORKER fires one
//!     mandated step. The state-gate is the htmx tooth: the button is DARK when the board is not open
//!     (`EPOCH < 1`) and LIT once open, so the surface REACTS to the cell. The fire is a real verified
//!     turn ([`DeosCell::fire_gated_through_executor`]); the executor re-enforces the budget program
//!     (`AffineLe Σspend ≤ budget`), so an over-budget step is REFUSED in-band.
//!   * **`delegate_mandate`** ([`COORDINATOR_RIGHTS`] = `None`, cap-only) — the COORDINATOR hands a
//!     worker its attenuated mandate, carrying a REAL [`Effect::GrantCapability`] (the cap-graph
//!     narrowing — `derive_no_amplify`: the worker gets a cap reaching the board NARROWED, never
//!     widened). The broadest tier: only a holder of the full `None` authority may delegate.
//!
//! ## Per-viewer projection (the divergence that needs no trust)
//!
//! Three viewers fetch the SAME surface and SEE DIFFERENT button-sets, by their caps alone:
//!   * an AUDITOR (holds `Signature`) projects `{view_audit}` — it can read, not act;
//!   * a WORKER (holds `Either`) projects `{view_audit, worker_step}` — but `worker_step` only when
//!     the board is open (the state-gate);
//!   * a COORDINATOR (holds `None`) projects all three.
//! This is `DeosCell::project_gated_for` + the cap-only surface's per-viewer view — the Rust twin of
//! the Lean `projectGatedFor`. No viewer can fire what its caps do not authorize, and the executor
//! re-checks on every fire — an auditor who lies "I am the coordinator" is refused by the cap-gate.
//!
//! ## Durable-state posture
//!
//! The app advertises [`PersistenceSeam::PgDregg`] — the orchestration's writes are verified turns over
//! durable state; a host with pg-dregg wired serves the durable orchestration (the receipt chain is the
//! commit log; see [`crate::durable`]). The manifest names it, so the durability posture is VISIBLE.

use dregg_app_framework::{
    AppCipherclerk, AuthRequired, CapabilityRef, CellAffordance, CellId, DeosApp, DeosCell, Effect,
    EmbeddedExecutor, Event, GatedAffordance, PersistenceSeam, StateConstraint, symbol,
};

use crate::{EPOCH_SLOT, field_from_bytes};

/// The AUDITOR rights tier (cap-only read — the narrowest). A holder of `Signature` or broader may
/// `view_audit`. Mirrors the supply-chain `VERIFIER_RIGHTS`.
pub const AUDITOR_RIGHTS: AuthRequired = AuthRequired::Signature;
/// The WORKER rights tier (sig-or-proof — `worker_step` + read). A holder of `Either` or broader.
pub const WORKER_RIGHTS: AuthRequired = AuthRequired::Either;
/// The COORDINATOR rights tier (root — `delegate_mandate`, `worker_step`, read; the broadest). Only a
/// holder of the full `None` authority may delegate a mandate.
pub const COORDINATOR_RIGHTS: AuthRequired = AuthRequired::None;

/// The `worker_step` **live-state precondition** — the board must be OPEN (`EPOCH >= 1`). A real
/// [`dregg_app_framework::CellProgram`] read against the cell's current state, so a worker's step
/// button is DARK before the board opens and LIT after (the htmx tooth). This gates "may `worker_step`
/// fire now"; the budget INVARIANT (`AffineLe Σspend ≤ budget`) is the installed [`coordinator_program`]
/// the executor re-enforces on the produced transition.
pub fn board_open_precondition() -> dregg_app_framework::CellProgram {
    dregg_app_framework::CellProgram::Predicate(vec![StateConstraint::FieldGte {
        index: EPOCH_SLOT,
        value: crate::field_from_u64(1),
    }])
}

/// Build the `delegate_mandate` effect — the coordinator hands `worker_cell` a capability reaching the
/// board, NARROWED (the `derive_no_amplify` cap-graph half). A real [`Effect::GrantCapability`] (the
/// same effect shape supply-chain's `grant_custody` uses). The granted authority is `worker_authority`
/// (e.g. [`WORKER_RIGHTS`]), strictly below the coordinator's `None` — so a worker can fire
/// `worker_step` but never `delegate_mandate`. The off-cell mandate triple ([`crate::Mandate`]) rides
/// alongside; THIS is the on-cell cap-graph grant the executor records.
pub fn delegate_mandate_effect(board: CellId, worker_cell: CellId, worker_authority: AuthRequired) -> Effect {
    Effect::GrantCapability {
        from: board,
        to: worker_cell,
        cap: CapabilityRef {
            target: board,
            slot: 0,
            permissions: worker_authority,
            breadstuff: None,
            expires_at: None,
            allowed_effects: None,
            stored_epoch: None,
        },
    }
}

/// Build the `worker_step` cap∧state-gate TEMPLATE effect — advance the EPOCH (the no-replay tick the
/// executor's `StrictMonotonic(EPOCH)` re-checks). This is the affordance's gate template (it names the
/// cell + effect-kind the cap∧state gate evaluates); the actual multi-step fire uses the
/// STATE-PARAMETERIZED [`fire_worker_step`], which derives `epoch := live_epoch + 1` (and the worker's
/// spend `spent := live_spent + cost`) from the cell's live state — so the SAME published button drives
/// the whole multi-step run, advancing each fire. (Closes the "single-fire surface affordance" gap via
/// the framework's [`dregg_app_framework::DeosCell::fire_gated_through_executor_with`].)
pub fn worker_step_effect(board: CellId) -> Effect {
    Effect::SetField {
        cell: board,
        index: EPOCH_SLOT as usize,
        value: crate::field_from_u64(2),
    }
}

/// **Fire `worker_step` as a STATE-PARAMETERIZED multi-step gated turn** over the deos surface — the
/// cap∧state gate (the htmx tooth) against the board's live state, then a verified turn whose effects
/// are DERIVED FROM that state: the worker's spend meter `spent := live_spent + cost` (`Monotonic` +
/// summed by the `AffineLe` swarm-budget gate) and the epoch `epoch := live_epoch + 1` (`StrictMonotonic`
/// no-replay). Because the effects read the LIVE state, the SAME published `worker_step` button advances
/// across the whole plan (via the framework's [`dregg_app_framework::DeosCell::fire_gated_through_executor_with`]).
///
/// The executor re-enforces the full budget program on the produced transition — an over-budget step is
/// REFUSED in-band (a [`dregg_app_framework::FireExecuteError::Executor`]); an unauthorised viewer or a
/// dark (un-opened) board is refused at the cap∧state gate (anti-ghost, nothing submitted). Returns the
/// executor's own receipt — the chained, auditable proof of the step.
pub fn fire_worker_step(
    cell: &DeosCell,
    held: &AuthRequired,
    worker: crate::WorkerSlot,
    cost: u64,
    cipherclerk: &AppCipherclerk,
    executor: &EmbeddedExecutor,
) -> Result<dregg_app_framework::TurnReceipt, dregg_app_framework::FireExecuteError> {
    let spend_slot = worker.spend_slot() as usize;
    let board = cell.cell();
    cell.fire_gated_through_executor_with(
        "worker_step",
        held,
        cipherclerk,
        executor,
        move |live| {
            // Read the worker's running spend + the live epoch from the cell's current state.
            let live_spent = field_tail_u64(&live.fields[spend_slot]);
            let live_epoch = field_tail_u64(&live.fields[EPOCH_SLOT as usize]);
            vec![
                Effect::SetField {
                    cell: board,
                    index: spend_slot,
                    value: crate::field_from_u64(live_spent.saturating_add(cost)),
                },
                Effect::SetField {
                    cell: board,
                    index: EPOCH_SLOT as usize,
                    value: crate::field_from_u64(live_epoch.saturating_add(1)),
                },
            ]
        },
    )
}

/// Read a [`dregg_app_framework::FieldElement`] as the big-endian u64 in its last 8 bytes (the
/// comparison the field's slot caveats use), for the state-parameterized fire.
fn field_tail_u64(fe: &dregg_app_framework::FieldElement) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&fe[24..32]);
    u64::from_be_bytes(b)
}

/// The orchestration board as a composed [`DeosApp`] — the SHIPPED deos surface for agent
/// orchestration. The board cell is the agent's own cell (so the embedded executor fires turns on it
/// directly). Three affordances on the auditor ⊂ worker ⊂ coordinator ladder; the `worker_step` is
/// GATED (cap∧state) on the board being open (the htmx tooth); the app advertises durable state via
/// [`PersistenceSeam::PgDregg`]; it is discoverable + publishes the board into the web-of-cells at the
/// auditor tier (the read surface a stranger reacquires).
///
/// To make `worker_step`'s budget gate REAL on the board cell, the caller should install
/// [`coordinator_program`] on the board cell (the `AffineLe Σspend ≤ budget` policy) via
/// `executor.install_program(board, coordinator_program())` and open the board (set `EPOCH >= 1`)
/// before firing — exactly as [`crate::OrchestrationEngine::open`] does. The
/// [`board_open_precondition`] state-gate then lights the button only when open.
pub fn orchestration_app(cipherclerk: &AppCipherclerk, executor: &EmbeddedExecutor) -> DeosApp {
    let board = cipherclerk.cell_id();

    // `view_audit` — an AUDITOR reads + re-derives the run from the receipt chain. Cap-only (the read
    // surface), the narrowest tier. The verdict is computed off-cell by `crate::audit_run`; this
    // affordance is the surface handle a stranger fires to request it.
    let view_audit = CellAffordance::new(
        "view_audit",
        AUDITOR_RIGHTS,
        Effect::EmitEvent {
            cell: board,
            event: Event::new(symbol("orchestration-audit-read"), vec![]),
        },
    );

    // `worker_step` — a WORKER fires one mandated step. GATED on the board being open (the htmx tooth:
    // dark before open, lit after). The decisive effect (the epoch tick) is the surface representative;
    // the executor re-enforces the full budget program on the produced transition (an over-budget step
    // is REFUSED in-band).
    let worker_step = GatedAffordance::new(
        CellAffordance::new("worker_step", WORKER_RIGHTS, worker_step_effect(board)),
        board_open_precondition(),
    );

    // `delegate_mandate` — the COORDINATOR hands a worker its attenuated mandate (a real cap-graph
    // grant, NARROWED). Cap-only, the broadest tier (only a `None`-holder may delegate). The grant
    // template targets a placeholder worker cell; the actual fire rebinds to the real worker.
    let delegate = CellAffordance::new(
        "delegate_mandate",
        COORDINATOR_RIGHTS,
        delegate_mandate_effect(board, CellId::from_bytes([0xAA; 32]), WORKER_RIGHTS),
    );

    DeosApp::builder("agent-orchestration", cipherclerk.clone(), executor.clone())
        .discoverable(vec![
            "agent-orchestration".into(),
            "ados".into(),
            "swarm".into(),
        ])
        .persistence(PersistenceSeam::PgDregg)
        .cell(
            DeosCell::new(board, "orchestration-board")
                .affordance(view_audit)
                .gated(worker_step)
                .affordance(delegate)
                .publish(AUDITOR_RIGHTS),
        )
        .build()
}

/// The board cell's identity scalar — the 32-byte public key the executor reads as a turn's sender
/// (`Authorization::Signature(pk, _)`). Used where a fire must bind to the firing identity (e.g. a
/// `senderInField`-style actor-bound write). Mirrors supply-chain's `signer_identity`.
pub fn coordinator_identity(cipherclerk: &AppCipherclerk) -> dregg_app_framework::FieldElement {
    cipherclerk.public_key().0
}

/// A convenience: the board's budget/epoch payload for an `orchestration-audit-read` event — binds the
/// swarm budget + the current epoch into the read event, so a `view_audit` fire's receipt carries the
/// audited bound (a light client reads it without a separate query). Used by the deos demo.
pub fn audit_read_payload(budget: u64, epoch: u64) -> Vec<dregg_app_framework::FieldElement> {
    vec![
        field_from_bytes(b"orchestration"),
        crate::field_from_u64(budget),
        crate::field_from_u64(epoch),
    ]
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{BUDGET_SLOT, coordinator_program};
    use dregg_app_framework::{AgentCipherclerk, AuthRequired};

    fn app() -> (AppCipherclerk, EmbeddedExecutor, DeosApp) {
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x5a; 32]);
        let exec = EmbeddedExecutor::new(&cclerk, "default");
        let app = orchestration_app(&cclerk, &exec);
        (cclerk, exec, app)
    }

    #[test]
    fn the_app_is_one_composed_registration() {
        let (_c, _e, app) = app();
        assert_eq!(app.name(), "agent-orchestration");
        assert_eq!(app.cells().len(), 1, "one board cell");
        assert!(
            matches!(app.persistence(), PersistenceSeam::PgDregg),
            "advertises durable pg-dregg state"
        );
        let board = &app.cells()[0];
        // The cap-only surface: the read + the cap-graph delegate (sorted by name).
        assert_eq!(
            board.surface().all_names(),
            vec!["delegate_mandate".to_string(), "view_audit".to_string()],
            "the cap-only surface: the audit read + the mandate delegation"
        );
    }

    #[test]
    fn the_rights_ladder_is_auditor_subset_worker_subset_coordinator() {
        // is_attenuation(held, granted): granted is narrower-or-equal to held.
        use dregg_cell::is_attenuation;
        // an auditor (Signature) is ⊑ a worker (Either) is ⊑ a coordinator (None).
        assert!(is_attenuation(&WORKER_RIGHTS, &AUDITOR_RIGHTS), "auditor ⊑ worker");
        assert!(is_attenuation(&COORDINATOR_RIGHTS, &WORKER_RIGHTS), "worker ⊑ coordinator");
        assert!(is_attenuation(&COORDINATOR_RIGHTS, &AUDITOR_RIGHTS), "auditor ⊑ coordinator");
        // and NOT the other way — a worker is not broad enough to be a coordinator.
        assert!(!is_attenuation(&WORKER_RIGHTS, &COORDINATOR_RIGHTS), "coordinator ⊄ worker (strict)");
    }

    #[test]
    fn per_viewer_projection_diverges_by_caps_and_state() {
        let (_c, exec, app) = app();
        let board = &app.cells()[0];

        // Before the board is open, NO viewer can fire the GATED worker_step (state-gate dark) —
        // even a coordinator (caps pass, state fails).
        let coord_held = AuthRequired::None;
        assert!(
            board.gated_fireable_names(&coord_held, &exec).is_empty(),
            "the board is not open ⇒ worker_step is DARK for everyone (htmx tooth)"
        );

        // Open the board: install the program + set EPOCH >= 1 so the state-gate lights.
        exec.install_program(board.cell(), coordinator_program());
        exec.with_ledger_mut(|l| {
            if let Some(c) = l.get_mut(&board.cell()) {
                // set EPOCH slot to 1 (open).
                c.state.fields[EPOCH_SLOT as usize] = crate::field_from_u64(1);
                // a real swarm budget so the gate is non-vacuous.
                c.state.fields[BUDGET_SLOT as usize] = crate::field_from_u64(1000);
            }
        });

        // NOW a worker (Either) projects worker_step (caps pass + state lit).
        let worker_held = AuthRequired::Either;
        assert!(
            board
                .gated_fireable_names(&worker_held, &exec)
                .contains(&"worker_step".to_string()),
            "an open board lights worker_step for a worker"
        );
        // An auditor (Signature) does NOT project worker_step (caps too narrow for Either).
        let auditor_held = AuthRequired::Signature;
        assert!(
            !board
                .gated_fireable_names(&auditor_held, &exec)
                .contains(&"worker_step".to_string()),
            "an auditor's caps are too narrow to fire worker_step"
        );
    }

    #[test]
    fn delegate_mandate_carries_a_real_cap_grant() {
        let board = CellId::from_bytes([7u8; 32]);
        let worker = CellId::from_bytes([9u8; 32]);
        let eff = delegate_mandate_effect(board, worker, WORKER_RIGHTS);
        match eff {
            Effect::GrantCapability { to, cap, .. } => {
                assert_eq!(to, worker);
                assert_eq!(cap.target, board, "the cap reaches the board");
                assert!(matches!(cap.permissions, AuthRequired::Either), "the worker gets the worker tier");
            }
            other => panic!("expected GrantCapability, got {other:?}"),
        }
    }
}
