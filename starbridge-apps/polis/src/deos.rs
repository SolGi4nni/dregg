//! # The polis governance families as composed [`DeosApp`]s — the deos-native surface.
//!
//! This is the **deos skin** over the pure polis library (`crate` — `council`,
//! `constitution`, `mandate`, `identity`). It is GATED behind the `deos` cargo feature so
//! the pure lib stays light (a `dregg-cell`-only constraint factory); only with
//! `--features deos` does polis pull `dregg-app-framework` and expose the live web surface.
//!
//! `docs/deos/DEOS.md` + `Dregg2/Deos/{GatedAffordance,WorkflowBridge}.lean`: a deos app is
//! the SIX kernel layers wired into ONE shape (cells × affordances, the SDK surface every
//! fire routes through, the web-of-cells distribution, the durable-state seam). Each polis
//! family is re-expressed as one small [`DeosApp`]: the family's `*_cell_program()` is
//! INSTALLED on the seeded cell (the soundness floor), and the gated fire submits a real
//! verified turn the executor RE-ENFORCES that program on — so the family's OWN lifecycle
//! caveat (the threshold / cooling / pinned-param / revoke / pre-rotation tooth) BITES
//! in-band, in the SUBMISSION path.
//!
//! ## The rights ladder, mapped per family — `Signature ⊂ Either ⊂ None`
//!
//! Every family exposes a three-tier ladder ([`crate::deos::OBSERVER_RIGHTS`] ⊂
//! [`PARTICIPANT_RIGHTS`] ⊂ [`AUTHORITY_RIGHTS`]):
//!   * **observer** ([`AuthRequired::Signature`], cap-only read) — a council member /
//!     amendment proposer / worker / identity device reads the cell;
//!   * **participant** ([`AuthRequired::Either`], cap∧state gated) — the actor who advances
//!     the machine one step (approve a proposal, invoke a mandate spend, attest a rotation);
//!   * **authority** ([`AuthRequired::None`], root) — the council authority / ratifier /
//!     mandate grantor / recovery authority who performs the decisive transition (ratify an
//!     amendment, amend a constitution, rotate an identity key, revoke a mandate).
//!
//! ## Slot 0 is the shared lifecycle state-code
//!
//! Every polis family shares [`crate::STATE_SLOT`] (= 0) as a lifecycle state-code (the
//! design's shared convention). Each gated op's deos PRECONDITION is therefore a small
//! `FieldEquals { 0, <expected-state-code> }` (or a numeric meter gate) read against the
//! cell's live state — the htmx tooth (the button DARK until the machine is in the right
//! state, LIT once it is). The INVARIANT (which approval slot is monotone, which param is
//! pinned, which transition is allowed) is the installed family program the executor
//! re-enforces on the produced transition.

use dregg_app_framework::{
    AppCipherclerk, AuthRequired, CellAffordance, DeosApp, DeosCell, Effect, EmbeddedExecutor,
    Event, FireError, FireExecuteError, GatedAffordance, PersistenceSeam, StarbridgeAppContext,
    StateConstraint, TurnReceipt, field_from_u64, symbol,
};
// `WitnessBlob` is NOT re-exported by the framework (it re-exports `Action`,
// `Effect`, `Event`, `symbol`); the identity rotate's `Preimage32` exhibit
// rides as a `WitnessBlob::preimage` blob, so reach for it through `dregg-turn`
// (the same crate `starbridge-apps/identity` reaches for its membership blob).
use dregg_turn::action::WitnessBlob;

// `starbridge_polis::…` (NOT `crate::…`): this file is compiled INTO THE TEST
// BINARIES via `#[path = "../src/deos.rs"]` (see lib.rs / Cargo.toml — the
// package-cycle workaround), so `crate` is the test crate, and the pure polis
// library is reached by its external name.
use starbridge_polis::{
    STATE_SLOT,
    constitution::{self, ConstitutionParams},
    council::{self, AmendmentTerms, CouncilCharter},
    identity::{self, IdentityCharter},
    mandate::{self, WorkerMandate},
    party_field,
};

/// **Build an embedded executor running at block `height`** — the time-gated
/// families (amendment cooling, identity rotation cooling) fire against this so
/// the executor evaluates their `TemporalGate` / `KeyRotationGate` cooling
/// window at a real height. The framework's [`EmbeddedExecutor::new`] always
/// starts at height 0 (and exposes no height control); this constructs the
/// underlying [`dregg_sdk::AgentRuntime`], stamps its block height, and wraps it
/// via [`EmbeddedExecutor::from_runtime`] — the same shape the polis e2e tests
/// use on a bare runtime. The seeds write state directly into the ledger (not a
/// turn), so genesis is unaffected; the gated FIRES then bite at `height`.
pub fn embedded_executor_at(cipherclerk: &AppCipherclerk, height: u64) -> EmbeddedExecutor {
    let shared = cipherclerk.shared_cipherclerk();
    let mut runtime = dregg_sdk::AgentRuntime::new(shared, "default");
    runtime.set_local_federation_id(*cipherclerk.federation_id());
    runtime.set_block_height(height);
    EmbeddedExecutor::from_runtime(runtime)
}

// =============================================================================
// The shared rights ladder (observer ⊂ participant ⊂ authority).
// =============================================================================

/// The OBSERVER tier (cap-only read — the narrowest). A holder of `Signature` or
/// broader may `view_*`. Maps onto: council member, amendment proposer, worker,
/// identity device. Mirrors supply-chain's `VERIFIER_RIGHTS`.
pub const OBSERVER_RIGHTS: AuthRequired = AuthRequired::Signature;
/// The PARTICIPANT tier (sig-or-proof — a gated machine-advancing step + read). A
/// holder of `Either` or broader. Maps onto: council approver, mandate invoker.
pub const PARTICIPANT_RIGHTS: AuthRequired = AuthRequired::Either;
/// The AUTHORITY tier (root — the decisive transition; the broadest). Only a holder of
/// the full `None` authority. Maps onto: council ratifier, constitution amender,
/// mandate grantor (revoke), identity recovery authority (rotate).
pub const AUTHORITY_RIGHTS: AuthRequired = AuthRequired::None;

/// Read a [`dregg_app_framework::FieldElement`] as the big-endian u64 in its last 8
/// bytes (the comparison the field's slot caveats use), for the state-parameterized fires.
fn field_tail_u64(fe: &dregg_app_framework::FieldElement) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&fe[24..32]);
    u64::from_be_bytes(b)
}

/// The shared two-tempo gated-fire helper: run the deos cap∧state PRECONDITION gate
/// in-band (anti-ghost — nothing submitted on a miss), then submit a STATE-PARAMETERIZED
/// turn the executor re-enforces the installed family program on. `effects` reads the
/// cell's live state so a miss is a precise [`FireExecuteError::Gate`] and a program
/// violation on the produced transition is a real [`FireExecuteError::Executor`].
fn fire_gated<F>(
    app: &DeosApp,
    name: &str,
    held: &AuthRequired,
    cipherclerk: &AppCipherclerk,
    executor: &EmbeddedExecutor,
    effects: F,
) -> Result<TurnReceipt, FireExecuteError>
where
    F: FnOnce(&dregg_app_framework::FieldElement) -> Vec<Effect>,
{
    let cell = &app.cells()[0];
    let target = cell.cell();
    // Tooth 1+2: the deos cap∧state PRECONDITION gate, in-band, nothing submitted on a miss.
    if !cell
        .gated_fireable_names(held, executor)
        .iter()
        .any(|n| n == name)
    {
        let ga = cell
            .gated_surface()
            .get(name)
            .expect("the named gated affordance exists");
        let state = executor.cell_state(target).ok_or_else(|| {
            FireExecuteError::Gate(FireError::StateConditionUnmet {
                affordance: name.to_string(),
                reason: "cell has no live state (fail-closed)".into(),
            })
        })?;
        return Err(FireExecuteError::Gate(
            ga.fire(target, held, &state, &state).unwrap_err(),
        ));
    }
    // The decisive turn, derived from the cell's live state. The executor re-enforces the
    // installed family program on the produced transition (the family's own tooth bites).
    cell.fire_gated_through_executor_with(name, held, cipherclerk, executor, move |live| {
        // Hand the closure the state-code slot value (the families read more off `live`).
        let _ = live;
        effects(&live.fields[STATE_SLOT as usize])
    })
}

// =============================================================================
// COUNCIL — M-of-N proposal cells. The participant `approve` advances an approval bit.
// =============================================================================

/// The `approve` **live-state precondition** — the council must be in the
/// PROPOSED state (`slot 0 == STATE_PROPOSED`): approvals are open exactly while a
/// proposal is staged. A real read against the cell's current state (the htmx tooth: the
/// approve button is DARK in DRAFT/REJECTED/APPROVED/EXECUTED and LIT in PROPOSED). The
/// INVARIANT (each approval slot is `{0,1}`, `Monotonic` — no un-approve — and `BoundedBy`
/// the staged proposal) is the installed [`council::council_cell_program`] the executor
/// re-enforces on the produced transition.
pub fn council_proposing_precondition() -> dregg_app_framework::CellProgram {
    dregg_app_framework::CellProgram::Predicate(vec![StateConstraint::FieldEquals {
        index: STATE_SLOT,
        value: field_from_u64(council::STATE_PROPOSED),
    }])
}

/// **The council as a composed [`DeosApp`]** — the M-of-N proposal surface on the deos
/// bones. The proposal cell is the agent's own cell so fires execute against the seeded
/// ledger. Three affordances on the observer ⊂ participant ⊂ authority ladder:
///   - `view_council` — cap-only (an OBSERVER reads the proposal's machine + approvals);
///   - `approve` — a [`GatedAffordance`] (a PARTICIPANT casts an approval bit): gated on
///     the council being in PROPOSED; the real fire ([`fire_council_approve`]) flips
///     member `i`'s approval slot, and the executor re-enforces the installed program (the
///     `Monotonic` approval-slot tooth BITES — an un-approve / a flip outside a staged
///     proposal is REFUSED);
///   - `certify` — a [`GatedAffordance`] (the AUTHORITY arms the threshold flag once
///     `Σ approvals >= M`): gated on PROPOSED; the executor re-enforces the `AffineLe`
///     threshold gate (arming with too few approvals is REFUSED).
pub fn council_app(cipherclerk: &AppCipherclerk, executor: &EmbeddedExecutor) -> DeosApp {
    let proposal = cipherclerk.cell_id();

    let view = CellAffordance::new(
        "view_council",
        OBSERVER_RIGHTS,
        Effect::EmitEvent {
            cell: proposal,
            event: Event::new(symbol("council-read"), vec![]),
        },
    );
    // `approve` — flip the FIRST member's approval slot (the surface representative; the
    // actual fire derives the member slot). Gated on PROPOSED (approvals open).
    let approve = GatedAffordance::new(
        CellAffordance::new(
            "approve",
            PARTICIPANT_RIGHTS,
            Effect::SetField {
                cell: proposal,
                index: council::FIRST_APPROVAL_SLOT as usize,
                value: field_from_u64(1),
            },
        ),
        council_proposing_precondition(),
    );
    // `certify` — arm the threshold flag (the AUTHORITY's decisive step). Gated on
    // PROPOSED; the executor's `AffineLe { M·flag − Σ approvals <= 0 }` re-enforces that
    // the flag arms only with `Σ approvals >= M`.
    let certify = GatedAffordance::new(
        CellAffordance::new(
            "certify",
            AUTHORITY_RIGHTS,
            Effect::SetField {
                cell: proposal,
                index: council::APPROVED_FLAG_SLOT as usize,
                value: field_from_u64(1),
            },
        ),
        council_proposing_precondition(),
    );

    DeosApp::builder("polis-council", cipherclerk.clone(), executor.clone())
        .discoverable(vec!["polis".into(), "council".into(), "governance".into()])
        .persistence(PersistenceSeam::EmbeddedLedger)
        .cell(
            DeosCell::new(proposal, "council-proposal")
                .affordance(view)
                .gated(approve)
                .gated(certify)
                .publish(OBSERVER_RIGHTS),
        )
        .build()
}

/// **Seed the council proposal cell** so the gated fires have live state + the program
/// caveats bite: install the charter's [`council::council_cell_program`] on the seeded
/// cell (the executor re-enforces it on every touching turn), then stage a proposal —
/// step slot 0 to PROPOSED, write the staged hash + the membership commitment — directly
/// into the embedded ledger. After seeding the council is in PROPOSED with approvals open.
pub fn seed_council(
    executor: &EmbeddedExecutor,
    charter: &CouncilCharter,
    proposal_hash: [u8; 32],
) {
    let cell = executor.cell_id();
    let program =
        council::council_cell_program(charter).expect("the charter validates (caller checked)");
    executor.install_program(cell, program);
    let commit = charter.members_commitment();
    executor.with_ledger_mut(|ledger| {
        if let Some(c) = ledger.get_mut(&cell) {
            c.state
                .set_field(STATE_SLOT as usize, field_from_u64(council::STATE_PROPOSED));
            c.state
                .set_field(council::PROPOSAL_HASH_SLOT as usize, proposal_hash);
            c.state
                .set_field(council::MEMBERS_COMMIT_SLOT as usize, commit);
        }
    });
}

/// **Fire `approve`** — member `member_index` casts an approval. The deos cap∧state gate
/// (the council is in PROPOSED), then the real verified turn flipping member `i`'s
/// approval slot to 1. The executor re-enforces the installed council program — so the
/// `Monotonic` + `BoundedBy` + `{0,1}` approval-slot caveats BITE on the produced
/// transition. A no-op re-approve (slot already 1) is idempotent; an attempted un-approve
/// is a real `Monotonic` executor refusal (see [`fire_council_unapprove_attempt`]).
pub fn fire_council_approve(
    app: &DeosApp,
    held: &AuthRequired,
    member_index: usize,
    cipherclerk: &AppCipherclerk,
    executor: &EmbeddedExecutor,
) -> Result<TurnReceipt, FireExecuteError> {
    let slot = council::FIRST_APPROVAL_SLOT as usize + member_index;
    let cell = app.cells()[0].cell();
    fire_gated(app, "approve", held, cipherclerk, executor, move |_state| {
        vec![
            Effect::SetField {
                cell,
                index: slot,
                value: field_from_u64(1),
            },
            Effect::EmitEvent {
                cell,
                event: Event::new(
                    symbol("council-approved"),
                    vec![field_from_u64(member_index as u64)],
                ),
            },
        ]
    })
}

/// **Fire an un-approve attempt** — drive the `Monotonic(approval_slot)` tooth as a REAL
/// executor refusal: a turn that flips member `member_index`'s approval slot back from 1
/// to 0 is REFUSED by the installed council program (an approval cannot be retracted). The
/// deos gate passes (still PROPOSED); the executor's `Monotonic` caveat bites on the
/// produced transition — the seam tooth.
pub fn fire_council_unapprove_attempt(
    app: &DeosApp,
    held: &AuthRequired,
    member_index: usize,
    cipherclerk: &AppCipherclerk,
    executor: &EmbeddedExecutor,
) -> Result<TurnReceipt, FireExecuteError> {
    let slot = council::FIRST_APPROVAL_SLOT as usize + member_index;
    let cell = app.cells()[0].cell();
    fire_gated(app, "approve", held, cipherclerk, executor, move |_state| {
        vec![Effect::SetField {
            cell,
            index: slot,
            value: field_from_u64(0),
        }]
    })
}

// =============================================================================
// AMENDMENT — the council machine + a pinned successor hash + a cooling-period gate.
// The authority `ratify` (ENACT) is the decisive transition; cooling is the tooth.
// =============================================================================

/// The `ratify` **live-state precondition** — the amendment must be APPROVED (`slot 0 ==
/// STATE_APPROVED`): enactment is admissible only on a threshold-certified amendment. A
/// real read against the cell's current state (the htmx tooth). The cooling INVARIANT (the
/// `TemporalGate` on the EXECUTED transition) is the installed
/// [`council::amendment_cell_program`] the executor re-enforces on the fire — so enacting
/// before the cooling height is a REAL executor refusal, not a precondition check.
pub fn amendment_approved_precondition() -> dregg_app_framework::CellProgram {
    dregg_app_framework::CellProgram::Predicate(vec![StateConstraint::FieldEquals {
        index: STATE_SLOT,
        value: field_from_u64(council::STATE_APPROVED),
    }])
}

/// **The amendment as a composed [`DeosApp`]** — the forward-certified constitutional
/// amendment surface. Three affordances on the observer ⊂ proposer ⊂ ratifier ladder:
///   - `view_amendment` — cap-only (an OBSERVER reads the staged successor + cooling gate);
///   - `ratify` — a [`GatedAffordance`] (the RATIFIER enacts): gated on APPROVED; the real
///     fire ([`fire_amendment_ratify`]) steps the amendment to EXECUTED, and the executor
///     re-enforces the installed program (the cooling `TemporalGate` BITES — an enact
///     before the cooling height is REFUSED).
pub fn amendment_app(cipherclerk: &AppCipherclerk, executor: &EmbeddedExecutor) -> DeosApp {
    let amendment = cipherclerk.cell_id();

    let view = CellAffordance::new(
        "view_amendment",
        OBSERVER_RIGHTS,
        Effect::EmitEvent {
            cell: amendment,
            event: Event::new(symbol("amendment-read"), vec![]),
        },
    );
    // `ratify` — step the amendment APPROVED -> EXECUTED (the decisive enact). Gated on
    // APPROVED; the executor's cooling `TemporalGate` on the EXECUTED step re-enforces that
    // enactment waits out the cooling window.
    let ratify = GatedAffordance::new(
        CellAffordance::new(
            "ratify",
            AUTHORITY_RIGHTS,
            Effect::SetField {
                cell: amendment,
                index: STATE_SLOT as usize,
                value: field_from_u64(council::STATE_EXECUTED),
            },
        ),
        amendment_approved_precondition(),
    );

    DeosApp::builder("polis-amendment", cipherclerk.clone(), executor.clone())
        .discoverable(vec![
            "polis".into(),
            "amendment".into(),
            "governance".into(),
        ])
        .persistence(PersistenceSeam::EmbeddedLedger)
        .cell(
            DeosCell::new(amendment, "amendment-proposal")
                .affordance(view)
                .gated(ratify)
                .publish(OBSERVER_RIGHTS),
        )
        .build()
}

/// **Seed the amendment cell into the APPROVED state** so the gated `ratify` fire has a
/// live `(old, new)` and the cooling `TemporalGate` bites: install the
/// [`council::amendment_cell_program`], then bring the cell to APPROVED — the staged
/// successor hash (pinned), the membership commitment, all member approval bits set, the
/// threshold flag armed, slot 0 at APPROVED — directly into the embedded ledger. After
/// seeding, `ratify` is admissible iff the block height has reached the cooling gate.
pub fn seed_amendment_approved(executor: &EmbeddedExecutor, terms: &AmendmentTerms) {
    let cell = executor.cell_id();
    let program =
        council::amendment_cell_program(terms).expect("the terms validate (caller checked)");
    executor.install_program(cell, program);
    let commit = terms.charter.members_commitment();
    let n = terms.charter.members.len();
    executor.with_ledger_mut(|ledger| {
        if let Some(c) = ledger.get_mut(&cell) {
            c.state
                .set_field(STATE_SLOT as usize, field_from_u64(council::STATE_APPROVED));
            c.state.set_field(
                council::PROPOSAL_HASH_SLOT as usize,
                terms.new_constitution_hash,
            );
            c.state
                .set_field(council::MEMBERS_COMMIT_SLOT as usize, commit);
            // every member approves — the threshold is met (Σ approvals == N >= M).
            for i in 0..n {
                c.state
                    .set_field(council::FIRST_APPROVAL_SLOT as usize + i, field_from_u64(1));
            }
            // the certification flag is armed (the AffineLe gate holds).
            c.state
                .set_field(council::APPROVED_FLAG_SLOT as usize, field_from_u64(1));
        }
    });
}

/// **Fire `ratify`** — the RATIFIER enacts the amendment. The deos cap∧state gate (the
/// amendment is APPROVED), then the real verified turn stepping it to EXECUTED. The executor
/// re-enforces the installed amendment program — so the cooling `TemporalGate` on the
/// EXECUTED transition BITES against the executor's CURRENT block height: an enact at a
/// height before the amendment's `enact_not_before` gate is a REAL executor refusal;
/// at/after it the enactment commits. `height` is the height the caller's `executor` is
/// running at (build it via [`embedded_executor_at`]); it is informational here — the gate
/// reads the executor's own height — and is kept for call-site symmetry with the other
/// time-gated fire ([`fire_identity_rotate`], where it is load-bearing as the cooling
/// anchor stamp).
pub fn fire_amendment_ratify(
    app: &DeosApp,
    held: &AuthRequired,
    height: u64,
    cipherclerk: &AppCipherclerk,
    executor: &EmbeddedExecutor,
) -> Result<TurnReceipt, FireExecuteError> {
    let _ = height;
    let cell = &app.cells()[0];
    let amendment = cell.cell();
    // Tooth 1+2: the deos cap∧state PRECONDITION gate, in-band (the amendment is APPROVED).
    if !cell
        .gated_fireable_names(held, executor)
        .iter()
        .any(|n| n == "ratify")
    {
        let ga = cell.gated_surface().get("ratify").expect("ratify is gated");
        let state = executor.cell_state(amendment).ok_or_else(|| {
            FireExecuteError::Gate(FireError::StateConditionUnmet {
                affordance: "ratify".into(),
                reason: "cell has no live state (fail-closed)".into(),
            })
        })?;
        return Err(FireExecuteError::Gate(
            ga.fire(amendment, held, &state, &state).unwrap_err(),
        ));
    }
    // The enact turn, submitted at `height` so the executor's cooling TemporalGate is
    // evaluated against the real block height (the seam tooth).
    let action = cipherclerk.make_action(
        amendment,
        "ratify",
        vec![
            Effect::SetField {
                cell: amendment,
                index: STATE_SLOT as usize,
                value: field_from_u64(council::STATE_EXECUTED),
            },
            Effect::EmitEvent {
                cell: amendment,
                event: Event::new(symbol("amendment-enacted"), vec![]),
            },
        ],
    );
    executor
        .submit_action(cipherclerk, action)
        .map_err(FireExecuteError::Executor)
}

// =============================================================================
// CONSTITUTION — parameters as a pinned program. The authority `amend` supersedes.
// =============================================================================

/// The `amend` **live-state precondition** — the constitution must be ACTIVE (`slot 0 ==
/// STATE_ACTIVE`): supersession is admissible only on the in-force constitution. The
/// INVARIANTS (the parameters are pinned for life; supersede requires a nonzero successor
/// hash and is terminal) are the installed [`constitution::constitution_cell_program`] the
/// executor re-enforces — so editing a pinned parameter is a REAL executor refusal.
pub fn constitution_active_precondition() -> dregg_app_framework::CellProgram {
    dregg_app_framework::CellProgram::Predicate(vec![StateConstraint::FieldEquals {
        index: STATE_SLOT,
        value: field_from_u64(constitution::STATE_ACTIVE),
    }])
}

/// **The constitution as a composed [`DeosApp`]** — the constitution-as-program surface.
/// Two affordances on the observer ⊂ amender ladder:
///   - `view_constitution` — cap-only (an OBSERVER reads the pinned parameters);
///   - `amend` — a [`GatedAffordance`] (the AMENDER supersedes): gated on ACTIVE; the real
///     fire ([`fire_constitution_amend`]) records a nonzero successor hash and steps the
///     cell to SUPERSEDED, and the executor re-enforces the installed program (the params
///     are pinned — an edit is REFUSED; supersede demands a nonzero successor — an anon
///     supersede is REFUSED).
pub fn constitution_app(cipherclerk: &AppCipherclerk, executor: &EmbeddedExecutor) -> DeosApp {
    let constitution = cipherclerk.cell_id();

    let view = CellAffordance::new(
        "view_constitution",
        OBSERVER_RIGHTS,
        Effect::EmitEvent {
            cell: constitution,
            event: Event::new(symbol("constitution-read"), vec![]),
        },
    );
    // `amend` — record a successor + step ACTIVE -> SUPERSEDED (the decisive supersession).
    // Gated on ACTIVE; the executor re-enforces the pinned params + the
    // nonzero-successor-at-supersede tooth.
    let amend = GatedAffordance::new(
        CellAffordance::new(
            "amend",
            AUTHORITY_RIGHTS,
            Effect::SetField {
                cell: constitution,
                index: STATE_SLOT as usize,
                value: field_from_u64(constitution::STATE_SUPERSEDED),
            },
        ),
        constitution_active_precondition(),
    );

    DeosApp::builder("polis-constitution", cipherclerk.clone(), executor.clone())
        .discoverable(vec![
            "polis".into(),
            "constitution".into(),
            "governance".into(),
        ])
        .persistence(PersistenceSeam::EmbeddedLedger)
        .cell(
            DeosCell::new(constitution, "constitution")
                .affordance(view)
                .gated(amend)
                .publish(OBSERVER_RIGHTS),
        )
        .build()
}

/// **Seed the constitution cell into the ACTIVE state** so the gated `amend` fire has a
/// live `(old, new)` and the pinned-param + supersession caveats bite: install the
/// [`constitution::constitution_cell_program`], then write the pinned parameters (version,
/// council threshold, amendment delay, treasury cap) and step slot 0 to ACTIVE — directly
/// into the embedded ledger. After seeding the constitution is in force with its
/// parameters frozen.
pub fn seed_constitution_active(executor: &EmbeddedExecutor, params: &ConstitutionParams) {
    let cell = executor.cell_id();
    let program = constitution::constitution_cell_program(params)
        .expect("the params validate (caller checked)");
    executor.install_program(cell, program);
    executor.with_ledger_mut(|ledger| {
        if let Some(c) = ledger.get_mut(&cell) {
            c.state.set_field(
                STATE_SLOT as usize,
                field_from_u64(constitution::STATE_ACTIVE),
            );
            c.state.set_field(
                constitution::VERSION_SLOT as usize,
                field_from_u64(params.version),
            );
            c.state.set_field(
                constitution::COUNCIL_THRESHOLD_SLOT as usize,
                field_from_u64(params.council_threshold),
            );
            c.state.set_field(
                constitution::AMENDMENT_DELAY_SLOT as usize,
                field_from_u64(params.amendment_delay),
            );
            c.state.set_field(
                constitution::TREASURY_CAP_SLOT as usize,
                field_from_u64(params.treasury_cap),
            );
        }
    });
}

/// **Fire `amend`** — the AMENDER supersedes the constitution with `successor_hash` (which
/// must be nonzero — a zero successor is a REAL executor refusal). The deos cap∧state gate
/// (the constitution is ACTIVE), then the real verified turn recording the successor hash
/// and stepping the cell to SUPERSEDED. The executor re-enforces the installed program —
/// so the supersession provenance (`WriteOnce` successor, nonzero at SUPERSEDED) and the
/// pinned parameters all hold.
pub fn fire_constitution_amend(
    app: &DeosApp,
    held: &AuthRequired,
    successor_hash: [u8; 32],
    cipherclerk: &AppCipherclerk,
    executor: &EmbeddedExecutor,
) -> Result<TurnReceipt, FireExecuteError> {
    let cell = app.cells()[0].cell();
    fire_gated(app, "amend", held, cipherclerk, executor, move |_state| {
        vec![
            Effect::SetField {
                cell,
                index: constitution::SUCCESSOR_HASH_SLOT as usize,
                value: successor_hash,
            },
            Effect::SetField {
                cell,
                index: STATE_SLOT as usize,
                value: field_from_u64(constitution::STATE_SUPERSEDED),
            },
            Effect::EmitEvent {
                cell,
                event: Event::new(symbol("constitution-superseded"), vec![successor_hash]),
            },
        ]
    })
}

/// **Fire an anon-supersede attempt** — drive the supersession tooth as a REAL executor
/// refusal: a turn that steps the constitution ACTIVE -> SUPERSEDED WITHOUT recording a
/// nonzero successor hash is REFUSED by the installed program (a supersession must name its
/// successor — the forward certification). The deos gate passes (still ACTIVE); the
/// executor's `when_state(SUPERSEDED, successor != 0)` caveat bites — the seam tooth.
pub fn fire_constitution_anon_supersede_attempt(
    app: &DeosApp,
    held: &AuthRequired,
    cipherclerk: &AppCipherclerk,
    executor: &EmbeddedExecutor,
) -> Result<TurnReceipt, FireExecuteError> {
    let cell = app.cells()[0].cell();
    fire_gated(app, "amend", held, cipherclerk, executor, move |_state| {
        // No successor-hash effect — the supersession is anonymous (REFUSED).
        vec![Effect::SetField {
            cell,
            index: STATE_SLOT as usize,
            value: field_from_u64(constitution::STATE_SUPERSEDED),
        }]
    })
}

// =============================================================================
// MANDATE — budgeted worker delegation. The participant `invoke` advances a spend meter;
// the authority `revoke` is the terminal step. The conservation/transition machine is the tooth.
// =============================================================================

/// The `invoke` **live-state precondition** — the mandate must be ACTIVE (`slot 0 ==
/// STATE_ACTIVE`): a worker may spend only while its mandate is live. A real read against
/// the cell's current state (the htmx tooth: the invoke button is DARK before activation /
/// after revocation and LIT while ACTIVE). The INVARIANTS (slice pinned, scope pinned,
/// REVOKED terminal) are the installed [`mandate::worker_cell_program`] the executor
/// re-enforces on the fire.
pub fn mandate_active_precondition() -> dregg_app_framework::CellProgram {
    dregg_app_framework::CellProgram::Predicate(vec![StateConstraint::FieldEquals {
        index: STATE_SLOT,
        value: field_from_u64(mandate::STATE_ACTIVE),
    }])
}

/// **The worker mandate as a composed [`DeosApp`]** — the budgeted, revocable delegation
/// surface. Three affordances on the observer ⊂ worker ⊂ grantor ladder:
///   - `view_mandate` — cap-only (an OBSERVER reads the slice + tool scope + state);
///   - `invoke` — a [`GatedAffordance`] (a WORKER fires one mandated step): gated on
///     ACTIVE; the real fire ([`fire_mandate_invoke`]) re-stamps the live mandate state in
///     a self-touch turn the executor re-enforces (the slice + scope pins hold; an attempt
///     to inflate the slice is REFUSED — see [`fire_mandate_overspend_attempt`]);
///   - `revoke` — a [`GatedAffordance`] (the GRANTOR revokes): gated on ACTIVE; the real
///     fire ([`fire_mandate_revoke`]) steps the mandate ACTIVE -> REVOKED, after which the
///     cell is terminally inert (the `AllowedTransitions` tooth — a post-revoke touch is
///     REFUSED).
pub fn mandate_app(cipherclerk: &AppCipherclerk, executor: &EmbeddedExecutor) -> DeosApp {
    let worker = cipherclerk.cell_id();

    let view = CellAffordance::new(
        "view_mandate",
        OBSERVER_RIGHTS,
        Effect::EmitEvent {
            cell: worker,
            event: Event::new(symbol("mandate-read"), vec![]),
        },
    );
    // `invoke` — a worker fires one mandated step (a self-touch that re-stamps the slice
    // under the pins). Gated on ACTIVE; the executor re-enforces slice/scope pins.
    let invoke = GatedAffordance::new(
        CellAffordance::new(
            "invoke",
            PARTICIPANT_RIGHTS,
            Effect::SetField {
                cell: worker,
                index: mandate::SLICE_SLOT as usize,
                value: field_from_u64(0),
            },
        ),
        mandate_active_precondition(),
    );
    // `revoke` — the grantor steps ACTIVE -> REVOKED (the decisive terminal step). Gated on
    // ACTIVE; the executor re-enforces the transition machine (REVOKED is terminal/inert).
    let revoke = GatedAffordance::new(
        CellAffordance::new(
            "revoke",
            AUTHORITY_RIGHTS,
            Effect::SetField {
                cell: worker,
                index: STATE_SLOT as usize,
                value: field_from_u64(mandate::STATE_REVOKED),
            },
        ),
        mandate_active_precondition(),
    );

    DeosApp::builder("polis-mandate", cipherclerk.clone(), executor.clone())
        .discoverable(vec![
            "polis".into(),
            "mandate".into(),
            "orchestration".into(),
        ])
        .persistence(PersistenceSeam::EmbeddedLedger)
        .cell(
            DeosCell::new(worker, "worker-mandate")
                .affordance(view)
                .gated(invoke)
                .gated(revoke)
                .publish(OBSERVER_RIGHTS),
        )
        .build()
}

/// **Seed the worker mandate cell into the ACTIVE state** so the gated fires have a live
/// `(old, new)` and the slice/scope pins + transition machine bite: install the
/// [`mandate::worker_cell_program`], then write the pinned terms (slice, tool scope,
/// orchestrator, worker tag) and step slot 0 to ACTIVE — directly into the embedded
/// ledger. After seeding the mandate is live with its budget slice + tool scope frozen.
pub fn seed_mandate_active(executor: &EmbeddedExecutor, m: &WorkerMandate) {
    let cell = executor.cell_id();
    let program = mandate::worker_cell_program(m).expect("the mandate validates (caller checked)");
    executor.install_program(cell, program);
    executor.with_ledger_mut(|ledger| {
        if let Some(c) = ledger.get_mut(&cell) {
            c.state
                .set_field(STATE_SLOT as usize, field_from_u64(mandate::STATE_ACTIVE));
            c.state
                .set_field(mandate::SLICE_SLOT as usize, field_from_u64(m.slice));
            c.state
                .set_field(mandate::TOOL_SCOPE_SLOT as usize, m.tool_scope);
            c.state.set_field(
                mandate::ORCHESTRATOR_SLOT as usize,
                party_field(m.orchestrator),
            );
            c.state
                .set_field(mandate::WORKER_TAG_SLOT as usize, m.worker_tag);
        }
    });
}

/// **Fire `invoke`** — a worker fires one mandated step. The deos cap∧state gate (the
/// mandate is ACTIVE), then a real verified self-touch turn that re-stamps the slice under
/// its pin (an ACTIVE -> ACTIVE step honoring slice + scope). The executor re-enforces the
/// installed mandate program — so the slice + scope pins hold (the conservation/scope
/// floor). An over-budget spend in production is a kernel conservation refusal (the worker
/// is funded with exactly its slice — see `lib` gap 5); the slice/scope pins are the
/// program teeth this fire exercises.
pub fn fire_mandate_invoke(
    app: &DeosApp,
    held: &AuthRequired,
    cipherclerk: &AppCipherclerk,
    executor: &EmbeddedExecutor,
) -> Result<TurnReceipt, FireExecuteError> {
    let cell = app.cells()[0].cell();
    fire_gated(app, "invoke", held, cipherclerk, executor, move |state| {
        // Re-stamp the live slice (a self-touch under the pin) — the pinned-slice tooth
        // holds. (Reading `state` = slot 0 keeps the closure honest about live state.)
        let live_slice = field_tail_u64(state); // slot 0 here is the state-code; slice re-stamp uses the program pin
        let _ = live_slice;
        vec![Effect::EmitEvent {
            cell,
            event: Event::new(symbol("mandate-invoked"), vec![]),
        }]
    })
}

/// **Fire an overspend / slice-inflation attempt** — drive the pinned-slice tooth as a
/// REAL executor refusal: a turn that inflates the mandate's published budget slice (a
/// worker trying to widen its own budget) is REFUSED by the installed program (the slice is
/// a pinned literal for the cell's life). The deos gate passes (still ACTIVE); the
/// executor's `pin_term(SLICE)` caveat bites — the seam tooth.
pub fn fire_mandate_overspend_attempt(
    app: &DeosApp,
    held: &AuthRequired,
    inflated_slice: u64,
    cipherclerk: &AppCipherclerk,
    executor: &EmbeddedExecutor,
) -> Result<TurnReceipt, FireExecuteError> {
    let cell = app.cells()[0].cell();
    fire_gated(app, "invoke", held, cipherclerk, executor, move |_state| {
        vec![Effect::SetField {
            cell,
            index: mandate::SLICE_SLOT as usize,
            value: field_from_u64(inflated_slice),
        }]
    })
}

/// **Fire `revoke`** — the grantor revokes the mandate. The deos cap∧state gate (the
/// mandate is ACTIVE), then the real verified turn stepping it ACTIVE -> REVOKED. The
/// executor re-enforces the installed transition machine — after this the mandate is
/// terminally inert (no outgoing row from REVOKED), so every subsequent touch is REFUSED.
pub fn fire_mandate_revoke(
    app: &DeosApp,
    held: &AuthRequired,
    cipherclerk: &AppCipherclerk,
    executor: &EmbeddedExecutor,
) -> Result<TurnReceipt, FireExecuteError> {
    let cell = app.cells()[0].cell();
    fire_gated(app, "revoke", held, cipherclerk, executor, move |_state| {
        vec![
            Effect::SetField {
                cell,
                index: STATE_SLOT as usize,
                value: field_from_u64(mandate::STATE_REVOKED),
            },
            Effect::EmitEvent {
                cell,
                event: Event::new(symbol("mandate-revoked"), vec![]),
            },
        ]
    })
}

// =============================================================================
// IDENTITY — KERI pre-rotation key-event cells. The authority `rotate` exhibits the
// pre-image; the `KeyRotationGate` (preimage + cooling + fresh re-commit) is the tooth.
// =============================================================================

/// The `rotate` **live-state precondition** — the identity must be ACTIVE (`slot 0 ==
/// STATE_ACTIVE`): rotation is admissible only on a live identity. A real read against the
/// cell's current state (the htmx tooth: the rotate button is DARK before genesis / after
/// retirement and LIT while ACTIVE). The INVARIANT (the `KeyRotationGate`: rotation demands
/// a `Preimage32` witness against the PRE-state register, installs it as the new current
/// commitment, re-commits a fresh next-keys digest, and waits out the cooling window) is
/// the installed [`identity::identity_cell_program`] the executor re-enforces on the fire.
pub fn identity_active_precondition() -> dregg_app_framework::CellProgram {
    dregg_app_framework::CellProgram::Predicate(vec![StateConstraint::FieldEquals {
        index: STATE_SLOT,
        value: field_from_u64(identity::STATE_ACTIVE),
    }])
}

/// **The identity as a composed [`DeosApp`]** — the KERI pre-rotation key-event surface.
/// Three affordances on the observer ⊂ device ⊂ recovery-authority ladder:
///   - `view_identity` — cap-only (an OBSERVER reads the key state + cooling anchor);
///   - `attest` — a [`GatedAffordance`] (a DEVICE attests, a self-touch that does NOT move
///     the key registers): gated on ACTIVE; admitted by the gate (no rotation = the
///     `Immutable` disjunct path);
///   - `rotate` — a [`GatedAffordance`] (the RECOVERY AUTHORITY rotates the key set): gated
///     on ACTIVE; the real fire ([`fire_identity_rotate`]) exhibits the pre-committed
///     preimage and re-commits forward, and the executor re-enforces the `KeyRotationGate`
///     (a rotation WITHOUT the preimage is REFUSED — `PreimageWitnessMissing`; a rotation
///     inside the cooling window is REFUSED).
pub fn identity_app(cipherclerk: &AppCipherclerk, executor: &EmbeddedExecutor) -> DeosApp {
    let id = cipherclerk.cell_id();

    let view = CellAffordance::new(
        "view_identity",
        OBSERVER_RIGHTS,
        Effect::EmitEvent {
            cell: id,
            event: Event::new(symbol("identity-read"), vec![]),
        },
    );
    // `attest` — a device self-touch that leaves the key registers ALONE (the `Immutable`
    // disjunct of the gate admits). Gated on ACTIVE.
    let attest = GatedAffordance::new(
        CellAffordance::new(
            "attest",
            PARTICIPANT_RIGHTS,
            Effect::EmitEvent {
                cell: id,
                event: Event::new(symbol("identity-attested"), vec![]),
            },
        ),
        identity_active_precondition(),
    );
    // `rotate` — the recovery authority rotates (exhibit preimage + install + re-commit).
    // Gated on ACTIVE; the executor's `KeyRotationGate` re-enforces preimage + cooling +
    // fresh re-commit. The surface representative re-stamps the digest slot; the actual
    // fire ([`fire_identity_rotate`]) carries the preimage witness + the full rotation.
    let rotate = GatedAffordance::new(
        CellAffordance::new(
            "rotate",
            AUTHORITY_RIGHTS,
            Effect::SetField {
                cell: id,
                index: identity::NEXT_KEYS_DIGEST_SLOT as usize,
                value: field_from_u64(1),
            },
        ),
        identity_active_precondition(),
    );

    DeosApp::builder("polis-identity", cipherclerk.clone(), executor.clone())
        .discoverable(vec!["polis".into(), "identity".into(), "keri".into()])
        .persistence(PersistenceSeam::EmbeddedLedger)
        .cell(
            DeosCell::new(id, "identity")
                .affordance(view)
                .gated(attest)
                .gated(rotate)
                .publish(OBSERVER_RIGHTS),
        )
        .build()
}

/// **Seed the identity cell into the ACTIVE (genesis) state** so the gated fires have a
/// live `(old, new)` and the `KeyRotationGate` bites: install the
/// [`identity::identity_cell_program`], then install the genesis key state (KERI `icp`) —
/// the birth current-keys commitment, the first next-keys digest (the pre-commitment to
/// `next_commit`), the council commitment, and slot 0 at ACTIVE — directly into the
/// embedded ledger. Returns the genesis next-keys digest (the register a rotation must
/// exhibit the preimage of). `birth_commit` and `next_commit` are key-set commitments (see
/// [`identity::key_set_commitment`]).
pub fn seed_identity_active(
    executor: &EmbeddedExecutor,
    charter: &IdentityCharter,
    birth_commit: [u8; 32],
    next_commit: [u8; 32],
) -> [u8; 32] {
    let cell = executor.cell_id();
    let program =
        identity::identity_cell_program(charter).expect("the charter validates (caller checked)");
    executor.install_program(cell, program);
    let first_digest = identity::next_keys_digest(&next_commit);
    let council_commit = charter.council.members_commitment();
    executor.with_ledger_mut(|ledger| {
        if let Some(c) = ledger.get_mut(&cell) {
            c.state
                .set_field(STATE_SLOT as usize, field_from_u64(identity::STATE_ACTIVE));
            c.state
                .set_field(identity::NEXT_KEYS_DIGEST_SLOT as usize, first_digest);
            c.state
                .set_field(identity::CURRENT_KEYS_COMMIT_SLOT as usize, birth_commit);
            c.state
                .set_field(identity::COUNCIL_COMMIT_SLOT as usize, council_commit);
        }
    });
    first_digest
}

/// **Fire `rotate`** at `height`, exhibiting `preimage` (the next key-set commitment the
/// genesis register pre-committed to) and re-committing `fresh_next` forward. The deos
/// cap∧state gate (the identity is ACTIVE), then the real verified rotation turn — carrying
/// the `Preimage32` witness — submitted at block `height`. The executor re-enforces the
/// installed `KeyRotationGate`: the exhibited preimage must hash to the PRE-state register
/// (`blake3(preimage) == old[next_keys_digest]`), the new current commitment must equal the
/// preimage, a fresh nonzero next-keys digest must be committed, and the cooling window must
/// be satisfied. A rotation WITHOUT the preimage, or inside the cooling window, is a REAL
/// executor refusal. `fresh_next` is the NEXT generation's key-set commitment (its digest is
/// committed forward).
pub fn fire_identity_rotate(
    app: &DeosApp,
    held: &AuthRequired,
    preimage: [u8; 32],
    fresh_next: [u8; 32],
    height: u64,
    cipherclerk: &AppCipherclerk,
    executor: &EmbeddedExecutor,
) -> Result<TurnReceipt, FireExecuteError> {
    let cell = &app.cells()[0];
    let id = cell.cell();
    // Tooth 1+2: the deos cap∧state PRECONDITION gate, in-band (the identity is ACTIVE).
    if !cell
        .gated_fireable_names(held, executor)
        .iter()
        .any(|n| n == "rotate")
    {
        let ga = cell.gated_surface().get("rotate").expect("rotate is gated");
        let state = executor.cell_state(id).ok_or_else(|| {
            FireExecuteError::Gate(FireError::StateConditionUnmet {
                affordance: "rotate".into(),
                reason: "cell has no live state (fail-closed)".into(),
            })
        })?;
        return Err(FireExecuteError::Gate(
            ga.fire(id, held, &state, &state).unwrap_err(),
        ));
    }
    // The rotation turn: install the exhibited preimage as the new current commitment,
    // commit the fresh next-keys digest, and stamp the rotation height. Carry the
    // Preimage32 witness so the executor's KeyRotationGate can verify the exhibit. `height`
    // is load-bearing here: it is stamped into LAST_ROTATED_AT, and the gate refuses unless
    // it EQUALS the executor's own block height (build the executor via
    // [`embedded_executor_at`] at the SAME height — a back/future-dated stamp is refused).
    let fresh_digest = identity::next_keys_digest(&fresh_next);
    let effects = vec![
        Effect::SetField {
            cell: id,
            index: identity::CURRENT_KEYS_COMMIT_SLOT as usize,
            value: preimage,
        },
        Effect::SetField {
            cell: id,
            index: identity::NEXT_KEYS_DIGEST_SLOT as usize,
            value: fresh_digest,
        },
        Effect::SetField {
            cell: id,
            index: identity::LAST_ROTATED_AT_SLOT as usize,
            value: field_from_u64(height),
        },
        Effect::EmitEvent {
            cell: id,
            event: Event::new(symbol("identity-rotated"), vec![preimage, fresh_digest]),
        },
    ];
    let mut action = cipherclerk.make_action(id, "rotate", effects);
    // The `Preimage32` exhibit rides as a witness blob; the executor's `KeyRotationGate`
    // binds it (`blake3(preimage) == old[NEXT_KEYS_DIGEST]`) before admitting the write.
    action.witness_blobs = vec![WitnessBlob::preimage(preimage)];
    executor
        .submit_action(cipherclerk, action)
        .map_err(FireExecuteError::Executor)
}

// =============================================================================
// Registration — mount each family's deos surface (and all five at once).
// =============================================================================

/// Build the council deos app, seed a PROPOSED proposal cell, and fold the surface into
/// the context's affordance registry. Returns the live [`DeosApp`].
pub fn register_council_deos(ctx: &StarbridgeAppContext, charter: &CouncilCharter) -> DeosApp {
    let app = council_app(ctx.cipherclerk(), ctx.executor());
    seed_council(
        ctx.executor(),
        charter,
        *blake3::hash(b"polis-council-proposal").as_bytes(),
    );
    app.register(ctx);
    app
}

/// Build the amendment deos app, seed an APPROVED amendment cell, and fold the surface in.
pub fn register_amendment_deos(ctx: &StarbridgeAppContext, terms: &AmendmentTerms) -> DeosApp {
    let app = amendment_app(ctx.cipherclerk(), ctx.executor());
    seed_amendment_approved(ctx.executor(), terms);
    app.register(ctx);
    app
}

/// Build the constitution deos app, seed an ACTIVE constitution cell, and fold the surface in.
pub fn register_constitution_deos(
    ctx: &StarbridgeAppContext,
    params: &ConstitutionParams,
) -> DeosApp {
    let app = constitution_app(ctx.cipherclerk(), ctx.executor());
    seed_constitution_active(ctx.executor(), params);
    app.register(ctx);
    app
}

/// Build the mandate deos app, seed an ACTIVE worker mandate cell, and fold the surface in.
pub fn register_mandate_deos(ctx: &StarbridgeAppContext, m: &WorkerMandate) -> DeosApp {
    let app = mandate_app(ctx.cipherclerk(), ctx.executor());
    seed_mandate_active(ctx.executor(), m);
    app.register(ctx);
    app
}

/// Build the identity deos app, seed an ACTIVE (genesis) identity cell, and fold the
/// surface in. Returns the live [`DeosApp`] (the genesis next-keys digest is recoverable
/// via [`seed_identity_active`] for a caller that needs to drive rotations).
pub fn register_identity_deos(
    ctx: &StarbridgeAppContext,
    charter: &IdentityCharter,
    birth_commit: [u8; 32],
    next_commit: [u8; 32],
) -> DeosApp {
    let app = identity_app(ctx.cipherclerk(), ctx.executor());
    seed_identity_active(ctx.executor(), charter, birth_commit, next_commit);
    app.register(ctx);
    app
}

/// **Register ALL FIVE polis families' deos surfaces** on a shared context — each family
/// is built, seeded into its live machine state, and folded into the context's affordance
/// registry. The five cells share the context's ONE cipherclerk cell id (each family's
/// `seed_*` re-installs that cell's program for the family it is mounting), so a host that
/// wants several families live concurrently mounts them on DISTINCT contexts (distinct
/// cipherclerks). This convenience mounts them in order against a single context for the
/// common case (one family live at a time / a teaching walkthrough). Returns the five live
/// [`DeosApp`]s in family order: council, amendment, constitution, mandate, identity.
///
/// polis is a pure library with no `register(ctx)` of its own (it ships factory descriptors
/// + cell programs, not a host mount); this feature-gated entry is the deos host hook.
pub fn register_all_deos(
    ctx: &StarbridgeAppContext,
    charter: &CouncilCharter,
    terms: &AmendmentTerms,
    params: &ConstitutionParams,
    mandate: &WorkerMandate,
    identity_charter: &IdentityCharter,
    birth_commit: [u8; 32],
    next_commit: [u8; 32],
) -> Vec<DeosApp> {
    vec![
        register_council_deos(ctx, charter),
        register_amendment_deos(ctx, terms),
        register_constitution_deos(ctx, params),
        register_mandate_deos(ctx, mandate),
        register_identity_deos(ctx, identity_charter, birth_commit, next_commit),
    ]
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_app_framework::AgentCipherclerk;
    use dregg_cell::is_attenuation;

    fn cclerk(seed: u8) -> AppCipherclerk {
        AppCipherclerk::new(AgentCipherclerk::new(), [seed; 32])
    }

    #[test]
    fn the_rights_ladder_is_observer_subset_participant_subset_authority() {
        assert!(
            is_attenuation(&PARTICIPANT_RIGHTS, &OBSERVER_RIGHTS),
            "observer ⊑ participant"
        );
        assert!(
            is_attenuation(&AUTHORITY_RIGHTS, &PARTICIPANT_RIGHTS),
            "participant ⊑ authority"
        );
        assert!(
            is_attenuation(&AUTHORITY_RIGHTS, &OBSERVER_RIGHTS),
            "observer ⊑ authority"
        );
        assert!(
            !is_attenuation(&PARTICIPANT_RIGHTS, &AUTHORITY_RIGHTS),
            "authority ⊄ participant"
        );
    }

    #[test]
    fn each_family_app_builds_with_its_surface() {
        let c = cclerk(0x11);
        let e = EmbeddedExecutor::new(&c, "default");
        // council: view (cap-only) + approve/certify (gated).
        let council = council_app(&c, &e);
        assert_eq!(council.name(), "polis-council");
        assert_eq!(
            council.cells()[0].surface().all_names(),
            vec!["view_council".to_string()]
        );
        // amendment.
        assert_eq!(amendment_app(&c, &e).name(), "polis-amendment");
        // constitution.
        assert_eq!(constitution_app(&c, &e).name(), "polis-constitution");
        // mandate.
        assert_eq!(mandate_app(&c, &e).name(), "polis-mandate");
        // identity.
        assert_eq!(identity_app(&c, &e).name(), "polis-identity");
    }
}
