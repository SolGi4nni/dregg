//! # starbridge-bounty-board
//!
//! Greenfield rebuild of the legacy `apps/bounty-board/` HTTP app as a
//! dregg-native **starbridge-app**: a thin library of [`FactoryDescriptor`]s
//! plus signed turn-builder helpers that compose dregg primitives only
//! (`FactoryDescriptor` + `Effect::SetField` + `Effect::EmitEvent` +
//! `StateConstraint` slot caveats). No domain-specific bounty `Effect`, no
//! `Authorization::Unchecked`, no placeholder signatures.
//!
//! ## The bounty lifecycle is a substrate-enforced state machine
//!
//! A bounty is a single factory-born sovereign cell ([`bounty_factory_descriptor`])
//! whose slot caveats *are* the workflow rules — the executor rejects any turn
//! that would take the cell off its legal path:
//!
//! | Slot              | Meaning                          | Caveat            |
//! |-------------------|----------------------------------|-------------------|
//! | [`TITLE_HASH_SLOT`]    | `blake3(title)`              | `WriteOnce`       |
//! | [`REWARD_SLOT`]        | escrowed reward amount       | `WriteOnce`       |
//! | [`STATE_SLOT`]         | lifecycle state code         | `StrictMonotonic` |
//! | [`CLAIMANT_HASH_SLOT`] | `blake3(claimant)`           | `WriteOnce`       |
//! | [`SUBMISSION_HASH_SLOT`]| `blake3(work artifact uri)` | `WriteOnce`       |
//!
//! The [`STATE_SLOT`] codes are [`STATE_OPEN`] (1) → [`STATE_CLAIMED`] (2) →
//! [`STATE_SUBMITTED`] (3) → [`STATE_PAID`] (4). Because the slot is
//! `StrictMonotonic`, the executor enforces that the state strictly increases:
//!
//! - You cannot skip backward (a paid bounty cannot be re-opened).
//! - You cannot re-enter a state (no double-claim into `CLAIMED`, because the
//!   second claim would write the *same* state code and `StrictMonotonic`
//!   requires `new > old`).
//! - Paired with [`CLAIMANT_HASH_SLOT`] being `WriteOnce`, the **first claimer
//!   wins**: once the claimant hash is bound, a competing claim cannot
//!   overwrite it to steal the bounty.
//!
//! The [`REWARD_SLOT`] is `WriteOnce`: the reward is set when the bounty is
//! posted (its first write, admitted from zero) and then frozen — it cannot be
//! silently lowered after a worker commits to the bounty.
//!
//! ## What this crate exports
//!
//! - [`bounty_factory_descriptor`] — the `FactoryDescriptor`, with its slot
//!   caveats baked into `state_constraints` so every born bounty cell inherits
//!   the gating.
//! - [`factory_descriptors`] — the descriptor slice for host registration.
//! - [`build_post_action`] — writes `TITLE_HASH`, `REWARD`, and `STATE=OPEN`,
//!   emits `bounty-posted`. Run against a freshly factory-born bounty cell.
//! - [`build_claim_action`] — binds `CLAIMANT_HASH` (write-once → first-claimer-
//!   wins) and advances `STATE=CLAIMED`, emits `bounty-claimed`.
//! - [`build_submit_action`] — binds `SUBMISSION_HASH` and advances
//!   `STATE=SUBMITTED`, emits `bounty-submitted`.
//! - [`build_payout_action`] — advances `STATE=PAID`, emits `bounty-paid`.
//! - [`register`] — mounts the app's factory + inspector on a
//!   [`StarbridgeAppContext`].

use dregg_app_framework::{
    Action, AppCipherclerk, AuthRequired, CapTarget, CapTemplate, CellAffordance, CellId, CellMode,
    CellProgram, ChildVkStrategy, ConstantsModule, DeosApp, DeosCell, Effect, EmbeddedExecutor,
    Event, FactoryDescriptor, FieldElement, FireExecuteError, GatedAffordance, InspectorDescriptor,
    StarbridgeAppContext, StateConstraint, TurnReceipt, canonical_program_vk, field_from_bytes,
    field_from_u64, hex_encode_32, symbol,
};

// =============================================================================
// Bounty-cell state schema
// =============================================================================

/// Bounty cell slot: `blake3` of the bounty title text. `WriteOnce` — the
/// title is fixed at posting and can never be re-bound.
pub const TITLE_HASH_SLOT: usize = 2;
/// Bounty cell slot: the escrowed reward amount. `WriteOnce` — set once when
/// the bounty is posted, then frozen for the cell's lifetime.
pub const REWARD_SLOT: usize = 3;
/// Bounty cell slot: the lifecycle state code. `StrictMonotonic` — the state
/// can only ever strictly increase (OPEN → CLAIMED → SUBMITTED → PAID).
pub const STATE_SLOT: usize = 4;
/// Bounty cell slot: `blake3` of the claimant identity. `WriteOnce` — first
/// claimer wins; a competing claim cannot overwrite it.
pub const CLAIMANT_HASH_SLOT: usize = 5;
/// Bounty cell slot: `blake3` of the submitted-work artifact URI. `WriteOnce`
/// — the submission is bound exactly once (at the OPEN→SUBMITTED step).
pub const SUBMISSION_HASH_SLOT: usize = 6;

// =============================================================================
// Lifecycle state codes (written into STATE_SLOT)
// =============================================================================

/// State code: the bounty is open for claims.
pub const STATE_OPEN: u64 = 1;
/// State code: a worker has claimed the bounty.
pub const STATE_CLAIMED: u64 = 2;
/// State code: the claimant has submitted work for review.
pub const STATE_SUBMITTED: u64 = 3;
/// State code: the bounty has been paid out (terminal).
pub const STATE_PAID: u64 = 4;

// =============================================================================
// Factory VK
// =============================================================================

/// Factory VK we publish for the bounty factory.
pub const BOUNTY_FACTORY_VK: [u8; 32] = *b"starbridge-bounty-board-factory!";

// =============================================================================
// Cell program (the slot caveats, also returned by the descriptor)
// =============================================================================

/// The `CellProgram` installed on every bounty cell: title + claimant +
/// submission write-once, reward write-once, state strictly monotone.
pub fn bounty_cell_program() -> CellProgram {
    CellProgram::always(bounty_state_constraints())
}

fn bounty_state_constraints() -> Vec<StateConstraint> {
    vec![
        StateConstraint::WriteOnce {
            index: TITLE_HASH_SLOT as u8,
        },
        StateConstraint::WriteOnce {
            index: REWARD_SLOT as u8,
        },
        StateConstraint::StrictMonotonic {
            index: STATE_SLOT as u8,
        },
        StateConstraint::WriteOnce {
            index: CLAIMANT_HASH_SLOT as u8,
        },
        StateConstraint::WriteOnce {
            index: SUBMISSION_HASH_SLOT as u8,
        },
    ]
}

/// Canonical child-program VK for bounty cells.
pub fn bounty_child_program_vk() -> [u8; 32] {
    canonical_program_vk(&bounty_cell_program())
}

// =============================================================================
// FactoryDescriptor
// =============================================================================

/// Build the bounty-cell `FactoryDescriptor`.
///
/// The bounty is born empty and posted by its first turn: `TITLE_HASH`,
/// `REWARD`, and `STATE=OPEN` are written by [`build_post_action`] against the
/// freshly-minted cell. We deliberately carry **no creation-time
/// `field_constraints`** — those validate against `params.initial_fields`,
/// which are `(u32, u64)` pairs that cannot carry the 32-byte `blake3(title)` /
/// claimant hashes the workflow uses. The meaningful gating is the *perpetual*
/// `state_constraints`: title/claimant/submission are `WriteOnce`, reward is
/// `WriteOnce`, and state is `StrictMonotonic`. Those are installed as the
/// born cell's `CellProgram` and bite on every subsequent turn — including the
/// `post` turn (write-once admits the first write from zero) and every
/// lifecycle advance.
pub fn bounty_factory_descriptor() -> FactoryDescriptor {
    FactoryDescriptor {
        factory_vk: BOUNTY_FACTORY_VK,
        child_program_vk: Some(bounty_child_program_vk()),
        child_vk_strategy: Some(ChildVkStrategy::Fixed(Some(bounty_child_program_vk()))),
        allowed_cap_templates: vec![CapTemplate {
            target: CapTarget::SelfCell,
            max_permissions: AuthRequired::Signature,
            attenuatable: true,
        }],
        field_constraints: vec![],
        state_constraints: bounty_state_constraints(),
        default_mode: CellMode::Sovereign,
        creation_budget: Some(1_000_000),
    }
}

/// All factory descriptors this starbridge-app contributes.
pub fn factory_descriptors() -> Vec<FactoryDescriptor> {
    vec![bounty_factory_descriptor()]
}

// =============================================================================
// Turn-builders
// =============================================================================

/// Build the signed `Action` that posts a bounty: writes the title hash, the
/// escrowed reward, and `STATE=OPEN`, then emits `bounty-posted`. Run against a
/// freshly factory-born bounty cell.
pub fn build_post_action(
    cipherclerk: &AppCipherclerk,
    bounty_cell: CellId,
    title: &str,
    reward: u64,
) -> Action {
    let title_h = field_from_bytes(title.as_bytes());
    let reward_f = field_from_u64(reward);
    let effects = vec![
        Effect::SetField {
            cell: bounty_cell,
            index: TITLE_HASH_SLOT,
            value: title_h,
        },
        Effect::SetField {
            cell: bounty_cell,
            index: REWARD_SLOT,
            value: reward_f,
        },
        Effect::SetField {
            cell: bounty_cell,
            index: STATE_SLOT,
            value: field_from_u64(STATE_OPEN),
        },
        Effect::EmitEvent {
            cell: bounty_cell,
            event: Event::new(symbol("bounty-posted"), vec![title_h, reward_f]),
        },
    ];
    cipherclerk.make_action(bounty_cell, "post_bounty", effects)
}

/// Build the signed `Action` that claims a bounty.
///
/// Binds the claimant hash (`CLAIMANT_HASH`, write-once → first-claimer-wins)
/// and advances `STATE` from OPEN to CLAIMED (strictly monotone → a second
/// claim on an already-claimed bounty is rejected, because it would try to
/// re-write the same CLAIMED state code). Emits `bounty-claimed`.
pub fn build_claim_action(
    cipherclerk: &AppCipherclerk,
    bounty_cell: CellId,
    claimant: &str,
) -> Action {
    let claimant_h = field_from_bytes(claimant.as_bytes());
    let effects = vec![
        Effect::SetField {
            cell: bounty_cell,
            index: CLAIMANT_HASH_SLOT,
            value: claimant_h,
        },
        Effect::SetField {
            cell: bounty_cell,
            index: STATE_SLOT,
            value: field_from_u64(STATE_CLAIMED),
        },
        Effect::EmitEvent {
            cell: bounty_cell,
            event: Event::new(symbol("bounty-claimed"), vec![claimant_h]),
        },
    ];
    cipherclerk.make_action(bounty_cell, "claim_bounty", effects)
}

/// Build the signed `Action` that submits work for a claimed bounty.
///
/// Binds the submission-artifact hash (`SUBMISSION_HASH`, write-once) and
/// advances `STATE` from CLAIMED to SUBMITTED. Emits `bounty-submitted`.
pub fn build_submit_action(
    cipherclerk: &AppCipherclerk,
    bounty_cell: CellId,
    artifact_uri: &str,
) -> Action {
    let artifact_h = field_from_bytes(artifact_uri.as_bytes());
    let effects = vec![
        Effect::SetField {
            cell: bounty_cell,
            index: SUBMISSION_HASH_SLOT,
            value: artifact_h,
        },
        Effect::SetField {
            cell: bounty_cell,
            index: STATE_SLOT,
            value: field_from_u64(STATE_SUBMITTED),
        },
        Effect::EmitEvent {
            cell: bounty_cell,
            event: Event::new(symbol("bounty-submitted"), vec![artifact_h]),
        },
    ];
    cipherclerk.make_action(bounty_cell, "submit_work", effects)
}

/// Build the signed `Action` that pays out a submitted bounty.
///
/// Advances `STATE` from SUBMITTED to PAID (terminal). Emits `bounty-paid`.
/// Because `STATE` is strictly monotone, a paid bounty cannot be re-opened, and
/// a payout cannot be issued twice.
pub fn build_payout_action(cipherclerk: &AppCipherclerk, bounty_cell: CellId) -> Action {
    let paid = field_from_u64(STATE_PAID);
    let effects = vec![
        Effect::SetField {
            cell: bounty_cell,
            index: STATE_SLOT,
            value: paid,
        },
        Effect::EmitEvent {
            cell: bounty_cell,
            event: Event::new(symbol("bounty-paid"), vec![paid]),
        },
    ];
    cipherclerk.make_action(bounty_cell, "payout_bounty", effects)
}

// =============================================================================
// Convenience encoders (mirror what the executor + CLI see)
// =============================================================================

/// `blake3(title)` — the value written into `TITLE_HASH_SLOT`.
pub fn title_hash(title: &str) -> FieldElement {
    field_from_bytes(title.as_bytes())
}

/// `blake3(claimant)` — the value written into `CLAIMANT_HASH_SLOT`.
pub fn claimant_hash(claimant: &str) -> FieldElement {
    field_from_bytes(claimant.as_bytes())
}

/// The big-endian-padded reward field written into `REWARD_SLOT`.
pub fn reward_field(reward: u64) -> FieldElement {
    field_from_u64(reward)
}

/// The state code field written into `STATE_SLOT`.
pub fn state_field(state: u64) -> FieldElement {
    field_from_u64(state)
}

// =============================================================================
// The deos-native surface — the BOUNTY as a composed `DeosApp`.
// =============================================================================
//
// `docs/deos/APPS-DEOS-INTEGRATION-CENSUS.md`: the bounty-board, re-expressed as a
// composed deos app and PROMOTED into `src/`. The four-state gated lifecycle is ONE
// [`DeosApp`] ([`bounty_app`] below); the framework wires the rest — per-viewer
// projection, web-of-cells publish (the BOUNTY cell IS a `dregg://` sturdyref), the
// rehydratable frustum-snapshot, the generated `<dregg-affordance-surface>` component,
// and the manifest — none of which the floor's bones had. `register(ctx)` now mounts it
// (see [`register_deos`]).
//
// **The seam is closed** — a TWO-TEMPO fire. The three state-advancing lifecycle ops
// (`claim`, `submit`, `payout`) are [`GatedAffordance`]s carrying a live-state
// PRECONDITION (the cell is in exactly the state this op advances FROM); the FULL bounty
// program ([`bounty_cell_program`] = title/reward/claimant/submission `WriteOnce` +
// `StrictMonotonic(STATE)`) is INSTALLED on the seeded bounty cell ([`seed_bounty`]) and
// RE-ENFORCED by the executor on every touching turn:
//
//   1. the deos PRECONDITION gate (the cap-gate `is_attenuation` AND the live-state
//      precondition `CellProgram::evaluate`) decides the button's verdict IN-BAND —
//      nothing submitted on a miss (anti-ghost; the htmx reactivity rides this), so on a
//      POSTED bounty `claim` is LIT and `payout` is DARK, and the instant the cell
//      advances the lit/dark sets flip;
//   2. [`fire_claim`] / [`fire_submit`] / [`fire_payout`] then submit the FULL
//      multi-effect lifecycle turn (state-parameterized off the live cell), and the
//      executor RE-ENFORCES the installed bounty program — so a NO-ADVANCE / REWOUND
//      `STATE` (`StrictMonotonic(STATE)` requires strict `new > old`) and a CLAIMANT
//      OVERWRITE (`WriteOnce(CLAIMANT_HASH)`) are REAL executor refusals in the
//      SUBMISSION path — the half the floor's `program.evaluate`-only tests never
//      exercised through a real signed turn (see `tests/deos_seam.rs`).
//
// Both gates are the genuine ones (`is_attenuation` + `CellProgram::evaluate`). Because
// `STATE` is `StrictMonotonic` (strict `>`), a no-advance DOES bite (unlike `Monotonic`),
// so the lifecycle is a true one-way ratchet: each state can be entered exactly once.

/// The bounty rights tiers, ON THE REAL ATTENUATION LATTICE — these ARE the roles the
/// floor crate's cap-graph enforces:
///
///   - a WATCHER (the public / an indexer) holds [`AuthRequired::Signature`] — the narrow
///     read tier: it can `view_bounty` (read the lifecycle state) and nothing else;
///   - a WORKER (a claimant / submitter) holds [`AuthRequired::Either`] — it can `claim`
///     (take an OPEN bounty) and `submit` (deliver work on a CLAIMED bounty) AND view;
///   - the POSTER (the bounty owner) holds [`AuthRequired::None`]/root — it can `payout`
///     (settle a SUBMITTED bounty) on top of everything a worker can do.
///
/// So `Signature ⊂ Either ⊂ None` IS the watcher ⊂ worker ⊂ poster ladder.
pub const WATCHER_RIGHTS: AuthRequired = AuthRequired::Signature;
/// The worker rights tier (sig-or-proof — claim + submit + view). See [`WATCHER_RIGHTS`].
pub const WORKER_RIGHTS: AuthRequired = AuthRequired::Either;
/// The poster/owner rights tier (root — payout + all). See [`WATCHER_RIGHTS`].
pub const POSTER_RIGHTS: AuthRequired = AuthRequired::None;

/// The `claim` **live-state precondition** — the bounty must be POSTED/OPEN
/// (`STATE == STATE_OPEN`). A real [`CellProgram`] read against the cell's current state,
/// so a `claim` button is LIT on an open bounty and DARK the instant it is claimed (the
/// htmx tooth). This gates "may `claim` fire now"; the lifecycle INVARIANT
/// (`StrictMonotonic(STATE)` + `WriteOnce(CLAIMANT_HASH)`, first-claimer-wins) is the
/// installed [`bounty_cell_program`] the executor re-enforces on the produced transition.
pub fn posted_precondition() -> CellProgram {
    CellProgram::Predicate(vec![StateConstraint::FieldEquals {
        index: STATE_SLOT as u8,
        value: field_from_u64(STATE_OPEN),
    }])
}

/// The `submit` **live-state precondition** — the bounty must be CLAIMED
/// (`STATE == STATE_CLAIMED`). So `submit` is DARK until a worker claims and LIT once
/// claimed (then DARK again once submitted). The executor's `StrictMonotonic(STATE)` is
/// the second guard (a submit out of order is a real refusal).
pub fn claimed_precondition() -> CellProgram {
    CellProgram::Predicate(vec![StateConstraint::FieldEquals {
        index: STATE_SLOT as u8,
        value: field_from_u64(STATE_CLAIMED),
    }])
}

/// The `payout` **live-state precondition** — the bounty must be SUBMITTED
/// (`STATE == STATE_SUBMITTED`). So the poster's `payout` button is DARK until work is
/// submitted and LIT once it is. The executor's `StrictMonotonic(STATE)` re-enforces that
/// a paid bounty cannot be re-paid (PAID > SUBMITTED, and a second payout is a no-advance
/// PAID -> PAID which strict-mono refuses).
pub fn submitted_precondition() -> CellProgram {
    CellProgram::Predicate(vec![StateConstraint::FieldEquals {
        index: STATE_SLOT as u8,
        value: field_from_u64(STATE_SUBMITTED),
    }])
}

/// **The bounty-board BOUNTY as a composed [`DeosApp`]** — the whole canonical 4-state
/// gated lifecycle, on the deos bones. The bounty cell is the agent's OWN cell
/// (`cipherclerk.cell_id()`) so fires execute against the seeded embedded ledger.
///
/// Four operations on the BOUNTY cell, on the watcher ⊂ worker ⊂ poster rights ladder:
///
///   - `view_bounty` — a cap-only affordance (a WATCHER reads the lifecycle state):
///     `Signature`, an `EmitEvent`;
///   - `claim` — a [`GatedAffordance`] (a WORKER takes an OPEN bounty): `Either`, a
///     live-state PRECONDITION (the bounty is POSTED/OPEN); the real fire ([`fire_claim`])
///     submits the FULL claim turn (bind `CLAIMANT_HASH` + advance `STATE` OPEN ->
///     CLAIMED), re-enforced by the executor's installed program (`WriteOnce(CLAIMANT)`
///     first-claimer-wins + `StrictMonotonic(STATE)`);
///   - `submit` — a [`GatedAffordance`] (a WORKER delivers): `Either`, a live-state
///     PRECONDITION (the bounty is CLAIMED); the real fire ([`fire_submit`]) binds
///     `SUBMISSION_HASH` + advances `STATE` CLAIMED -> SUBMITTED, re-enforced by the
///     executor;
///   - `payout` — a [`GatedAffordance`] (the POSTER settles): `None`/root, a live-state
///     PRECONDITION (the bounty is SUBMITTED); the real fire ([`fire_payout`]) advances
///     `STATE` SUBMITTED -> PAID (terminal), re-enforced by the executor.
///
/// The bounty cell is published into the web-of-cells at the watcher tier (an indexer on
/// another federation reacquires the bounty's lifecycle across the membrane) and is
/// discoverable under `bounties`.
///
/// Seed the cell's program + POSTED state with [`seed_bounty`] so the gated fires have a
/// live state and the executor re-enforces the lifecycle program.
pub fn bounty_app(cipherclerk: &AppCipherclerk, executor: &EmbeddedExecutor) -> DeosApp {
    let bounty = cipherclerk.cell_id();

    // `claim` — a WORKER takes an OPEN bounty. The GatedAffordance carries the DECISIVE
    // effect (the `STATE` advance to CLAIMED) as its surface representative AND a
    // live-state PRECONDITION ([`posted_precondition`]: the bounty is OPEN) — so the
    // button is LIT on a posted bounty and DARK once claimed (the htmx tooth) and the
    // cap∧state gate decides its verdict in-band. The actual fire ([`fire_claim`]) submits
    // the FULL multi-effect claim ([`claim_effects`]: bind CLAIMANT_HASH + advance STATE),
    // which the executor re-enforces the FULL bounty program on — so `WriteOnce(CLAIMANT)`
    // (first-claimer-wins) and `StrictMonotonic(STATE)` BITE: a competing re-claim is
    // REFUSED.
    let claim = GatedAffordance::new(
        CellAffordance::new(
            "claim",
            WORKER_RIGHTS,
            Effect::SetField {
                cell: bounty,
                index: STATE_SLOT,
                value: field_from_u64(STATE_CLAIMED),
            },
        ),
        posted_precondition(),
    );
    // `submit` — a WORKER delivers work on a CLAIMED bounty. The decisive effect advances
    // `STATE` to SUBMITTED; gated on the CLAIMED precondition. The executor re-enforces the
    // installed program (`StrictMonotonic(STATE)` + `WriteOnce(SUBMISSION_HASH)` bite).
    let submit = GatedAffordance::new(
        CellAffordance::new(
            "submit",
            WORKER_RIGHTS,
            Effect::SetField {
                cell: bounty,
                index: STATE_SLOT,
                value: field_from_u64(STATE_SUBMITTED),
            },
        ),
        claimed_precondition(),
    );
    // `payout` — the POSTER settles a SUBMITTED bounty. The decisive effect advances
    // `STATE` to PAID (terminal); gated on the SUBMITTED precondition + the root cap tier
    // (only the poster pays out). The executor re-enforces `StrictMonotonic(STATE)` — a
    // re-payout (PAID -> PAID, no advance) is REFUSED.
    let payout = GatedAffordance::new(
        CellAffordance::new(
            "payout",
            POSTER_RIGHTS,
            Effect::SetField {
                cell: bounty,
                index: STATE_SLOT,
                value: field_from_u64(STATE_PAID),
            },
        ),
        submitted_precondition(),
    );
    // `view_bounty` — a watcher reads the lifecycle state. Cap-only.
    let view = CellAffordance::new(
        "view_bounty",
        WATCHER_RIGHTS,
        Effect::EmitEvent {
            cell: bounty,
            event: Event::new(symbol("bounty-read"), vec![]),
        },
    );

    DeosApp::builder("bounty-board", cipherclerk.clone(), executor.clone())
        .discoverable(vec!["bounties".into()])
        .cell(
            DeosCell::new(bounty, "bounty")
                .affordance(view)
                .gated(claim)
                .gated(submit)
                .gated(payout)
                .publish(WATCHER_RIGHTS),
        )
        .build()
}

/// **Seed the BOUNTY cell** so the gated fires have live state + the caveats bite: install
/// the full bounty [`bounty_cell_program`] on the seeded bounty cell (so the executor
/// re-enforces it on every touching turn), then post the genesis state (bind
/// `TITLE_HASH` and `REWARD` under `WriteOnce`, set `STATE = STATE_OPEN`) directly into
/// the embedded ledger.
///
/// After seeding, the bounty is POSTED/OPEN with its title + reward bound — a real
/// `(old, new)` baseline against which `claim` advances. Returns the posted `STATE` value.
pub fn seed_bounty(executor: &EmbeddedExecutor, title: &str, reward: u64) -> u64 {
    let bounty = executor.cell_id();
    executor.install_program(bounty, bounty_cell_program());
    executor.with_ledger_mut(|ledger| {
        if let Some(cell) = ledger.get_mut(&bounty) {
            cell.state.set_field(TITLE_HASH_SLOT, title_hash(title));
            cell.state.set_field(REWARD_SLOT, reward_field(reward));
            cell.state.set_field(STATE_SLOT, state_field(STATE_OPEN));
        }
    });
    STATE_OPEN
}

/// **`claim` effects** — the multi-effect claim body: bind `CLAIMANT_HASH` (`WriteOnce` →
/// first-claimer-wins) and advance `STATE` OPEN -> CLAIMED (`StrictMonotonic`). This is the
/// ONE coherent transition the installed program admits. The deos `claim` gated affordance
/// is the cap∧state PRECONDITION face; THIS is the turn [`fire_claim`] submits.
pub fn claim_effects(bounty: CellId, claimant: &str) -> Vec<Effect> {
    let claimant_h = claimant_hash(claimant);
    vec![
        Effect::SetField {
            cell: bounty,
            index: CLAIMANT_HASH_SLOT,
            value: claimant_h,
        },
        Effect::SetField {
            cell: bounty,
            index: STATE_SLOT,
            value: field_from_u64(STATE_CLAIMED),
        },
        Effect::EmitEvent {
            cell: bounty,
            event: Event::new(symbol("bounty-claimed"), vec![claimant_h]),
        },
    ]
}

/// **`submit` effects** — the multi-effect submit body: bind `SUBMISSION_HASH`
/// (`WriteOnce`) and advance `STATE` CLAIMED -> SUBMITTED (`StrictMonotonic`). THIS is the
/// turn [`fire_submit`] submits.
pub fn submit_effects(bounty: CellId, artifact_uri: &str) -> Vec<Effect> {
    let artifact_h = field_from_bytes(artifact_uri.as_bytes());
    vec![
        Effect::SetField {
            cell: bounty,
            index: SUBMISSION_HASH_SLOT,
            value: artifact_h,
        },
        Effect::SetField {
            cell: bounty,
            index: STATE_SLOT,
            value: field_from_u64(STATE_SUBMITTED),
        },
        Effect::EmitEvent {
            cell: bounty,
            event: Event::new(symbol("bounty-submitted"), vec![artifact_h]),
        },
    ]
}

/// **`payout` effects** — the multi-effect payout body: advance `STATE` SUBMITTED -> PAID
/// (terminal, `StrictMonotonic`). THIS is the turn [`fire_payout`] submits.
pub fn payout_effects(bounty: CellId) -> Vec<Effect> {
    let paid = field_from_u64(STATE_PAID);
    vec![
        Effect::SetField {
            cell: bounty,
            index: STATE_SLOT,
            value: paid,
        },
        Effect::EmitEvent {
            cell: bounty,
            event: Event::new(symbol("bounty-paid"), vec![paid]),
        },
    ]
}

/// **Fire `claim`** — the deos cap∧state PRECONDITION gate (anti-ghost, in-band), then the
/// FULL multi-effect claim turn the executor re-enforces the bounty program on. The
/// two-tempo bridge: the gated affordance decides the button's verdict (cap ⊇ Either AND
/// the bounty is POSTED) WITHOUT touching the executor; on both passing, the complete claim
/// turn ([`claim_effects`]) is submitted (via [`DeosCell::fire_gated_through_executor_with`],
/// state-parameterized off the live cell), and the executor's re-enforcement of
/// [`bounty_cell_program`] is the SECOND, verified gate (`WriteOnce(CLAIMANT)` +
/// `StrictMonotonic(STATE)` bite). Anti-ghost both ways: a precondition miss never submits;
/// a program violation is a real executor refusal. Use [`seed_bounty`] first.
pub fn fire_claim(
    app: &DeosApp,
    held: &AuthRequired,
    claimant: &str,
    cipherclerk: &AppCipherclerk,
    executor: &EmbeddedExecutor,
) -> Result<TurnReceipt, FireExecuteError> {
    let cell = &app.cells()[0];
    let bounty = cell.cell();
    let claimant = claimant.to_string();
    cell.fire_gated_through_executor_with("claim", held, cipherclerk, executor, move |_live| {
        claim_effects(bounty, &claimant)
    })
}

/// **Fire `submit`** — the deos cap∧state PRECONDITION gate (cap ⊇ Either AND the bounty is
/// CLAIMED), then the FULL submit turn ([`submit_effects`]). Like [`fire_claim`], the gated
/// affordance decides the button in-band and the executor's program re-enforcement
/// (`StrictMonotonic(STATE)` CLAIMED -> SUBMITTED, `WriteOnce(SUBMISSION)`) is the verified
/// second gate. Use [`seed_bounty`] first.
pub fn fire_submit(
    app: &DeosApp,
    held: &AuthRequired,
    artifact_uri: &str,
    cipherclerk: &AppCipherclerk,
    executor: &EmbeddedExecutor,
) -> Result<TurnReceipt, FireExecuteError> {
    let cell = &app.cells()[0];
    let bounty = cell.cell();
    let artifact_uri = artifact_uri.to_string();
    cell.fire_gated_through_executor_with("submit", held, cipherclerk, executor, move |_live| {
        submit_effects(bounty, &artifact_uri)
    })
}

/// **Fire `payout`** — the deos cap∧state PRECONDITION gate (cap ⊇ root AND the bounty is
/// SUBMITTED), then the FULL payout turn ([`payout_effects`]). The gated affordance decides
/// the button in-band and the executor's `StrictMonotonic(STATE)` (SUBMITTED -> PAID, and a
/// re-payout's no-advance PAID -> PAID is REFUSED) is the verified second gate. Use
/// [`seed_bounty`] first.
pub fn fire_payout(
    app: &DeosApp,
    held: &AuthRequired,
    cipherclerk: &AppCipherclerk,
    executor: &EmbeddedExecutor,
) -> Result<TurnReceipt, FireExecuteError> {
    let cell = &app.cells()[0];
    let bounty = cell.cell();
    cell.fire_gated_through_executor_with("payout", held, cipherclerk, executor, move |_live| {
        payout_effects(bounty)
    })
}

/// **Mount the deos-native surface** ([`bounty_app`]) on a shared context: build the
/// composed [`DeosApp`] from the context's cipherclerk + executor, seed the bounty cell's
/// program + POSTED state (so the gated fires bite), and fold the app into the context's
/// affordance registry ([`DeosApp::register`]). Returns the live [`DeosApp`] (so a host
/// can also [`DeosApp::mount`] its axum router / [`DeosApp::publish_all`] into the
/// web-of-cells). This is the PROMOTION the census asks for: the deos surface now ships
/// from `src/`, not from a side-proof in `tests/`.
pub fn register_deos(ctx: &StarbridgeAppContext) -> DeosApp {
    let app = bounty_app(ctx.cipherclerk(), ctx.executor());
    // Seed the bounty cell so the gated `claim` / `submit` / `payout` fires have a live
    // `(old, new)` and the full bounty program (installed here) is re-enforced by the
    // executor on every touching turn.
    seed_bounty(ctx.executor(), "fix the bug", 500);
    app.register(ctx);
    app
}

// =============================================================================
// StarbridgeAppContext mount
// =============================================================================

/// Web-constants module (single source of truth for the JS surface).
pub fn web_constants() -> ConstantsModule {
    ConstantsModule::new("bounty-board")
        .slot("TITLE_HASH_SLOT", TITLE_HASH_SLOT as u64)
        .slot("REWARD_SLOT", REWARD_SLOT as u64)
        .slot("STATE_SLOT", STATE_SLOT as u64)
        .slot("CLAIMANT_HASH_SLOT", CLAIMANT_HASH_SLOT as u64)
        .slot("SUBMISSION_HASH_SLOT", SUBMISSION_HASH_SLOT as u64)
        .string("FACTORY_VK_HEX", hex_encode_32(&BOUNTY_FACTORY_VK))
        .topic("POSTED", "bounty-posted")
        .topic("CLAIMED", "bounty-claimed")
        .topic("SUBMITTED", "bounty-submitted")
        .topic("PAID", "bounty-paid")
}

/// Register this starbridge-app on a [`StarbridgeAppContext`].
///
/// Installs the bounty factory descriptor and the bounty inspector. Returns the
/// registered factory VK.
pub fn register(ctx: &StarbridgeAppContext) -> [u8; 32] {
    let factory_vk = ctx.register_factory(bounty_factory_descriptor());

    ctx.register_inspector(InspectorDescriptor {
        kind: "bounty".into(),
        descriptor: serde_json::json!({
            "component": "dregg-bounty",
            "module": "/starbridge-apps/bounty-board/inspectors.js",
            "uri_prefix": "dregg://cell/",
            "summary_fields": ["title_hash", "reward", "state", "claimant_hash", "submission_hash"],
            "slot_layout": {
                "title_hash":      TITLE_HASH_SLOT,
                "reward":          REWARD_SLOT,
                "state":           STATE_SLOT,
                "claimant_hash":   CLAIMANT_HASH_SLOT,
                "submission_hash": SUBMISSION_HASH_SLOT,
            },
            "state_codes": {
                "open":      STATE_OPEN,
                "claimed":   STATE_CLAIMED,
                "submitted": STATE_SUBMITTED,
                "paid":      STATE_PAID,
            },
            "factory_vk_hex": hex_encode_32(&factory_vk),
            "child_program_vk_hex": hex_encode_32(&bounty_child_program_vk()),
        }),
    });

    // Mount the deos-native composition surface (the `DeosApp`) on the SAME context — the
    // census promotion: the deos surface now ships from `src/`. The factory + inspector are
    // where SOUNDNESS lives (an out-of-order / re-claim turn is a real executor refusal on
    // the born cell); the deos surface is the composition skin (per-viewer projection, the
    // cap∧state gated fires, the `dregg://` publish, the rehydratable snapshot, the manifest).
    register_deos(ctx);

    factory_vk
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_app_framework::{AgentCipherclerk, Authorization, EmbeddedExecutor};
    use dregg_cell::FactoryCreationParams;

    fn test_cipherclerk() -> AppCipherclerk {
        AppCipherclerk::new(AgentCipherclerk::new(), [9u8; 32])
    }

    fn bounty_cell() -> CellId {
        CellId::from_bytes([4u8; 32])
    }

    // ── Descriptor shape ────────────────────────────────────────────────

    #[test]
    fn descriptor_is_deterministic() {
        assert_eq!(
            bounty_factory_descriptor().hash(),
            bounty_factory_descriptor().hash()
        );
    }

    #[test]
    fn factory_bakes_lifecycle_caveats() {
        let d = bounty_factory_descriptor();
        // title / reward / claimant / submission are write-once
        for idx in [
            TITLE_HASH_SLOT,
            REWARD_SLOT,
            CLAIMANT_HASH_SLOT,
            SUBMISSION_HASH_SLOT,
        ] {
            assert!(
                d.state_constraints.iter().any(
                    |c| matches!(c, StateConstraint::WriteOnce { index } if *index == idx as u8)
                ),
                "expected WriteOnce on slot {idx}"
            );
        }
        // state is strictly monotone
        assert!(
            d.state_constraints
                .iter()
                .any(|c| matches!(c, StateConstraint::StrictMonotonic { index } if *index == STATE_SLOT as u8)),
            "STATE slot must be StrictMonotonic"
        );
        assert_eq!(d.state_constraints.len(), 5);
    }

    #[test]
    fn child_program_vk_is_canonical_recipe() {
        let expected = canonical_program_vk(&bounty_cell_program());
        assert_eq!(bounty_child_program_vk(), expected);
        assert_eq!(bounty_factory_descriptor().child_program_vk, Some(expected));
    }

    // ── Slot-caveat evaluation (executor-side regression) ────────────────

    fn bounty_program() -> dregg_cell::CellProgram {
        dregg_cell::CellProgram::Predicate(bounty_state_constraints())
    }

    fn empty() -> dregg_cell::state::CellState {
        dregg_cell::state::CellState::new(0)
    }

    fn posted_state(reward: u64) -> dregg_cell::state::CellState {
        let mut s = empty();
        s.fields[TITLE_HASH_SLOT] = title_hash("fix the bug");
        s.fields[REWARD_SLOT] = reward_field(reward);
        s.fields[STATE_SLOT] = state_field(STATE_OPEN);
        s
    }

    #[test]
    fn legal_post_succeeds() {
        let program = bounty_program();
        let old = empty();
        let new = posted_state(500);
        assert!(program.evaluate(&new, Some(&old), None).is_ok());
    }

    #[test]
    fn legal_claim_advances_state() {
        let program = bounty_program();
        let mut old = posted_state(500);
        old.set_nonce(1);
        let mut new = old.clone();
        new.fields[CLAIMANT_HASH_SLOT] = claimant_hash("bob");
        new.fields[STATE_SLOT] = state_field(STATE_CLAIMED);
        assert!(program.evaluate(&new, Some(&old), None).is_ok());
    }

    #[test]
    fn double_claim_is_strict_monotonic_violation() {
        // A bounty already in CLAIMED; a competing claim writes the same
        // CLAIMED state code → StrictMonotonic rejects (new must be > old).
        let program = bounty_program();
        let mut old = posted_state(500);
        old.fields[CLAIMANT_HASH_SLOT] = claimant_hash("bob");
        old.fields[STATE_SLOT] = state_field(STATE_CLAIMED);
        old.set_nonce(2);
        let mut new = old.clone();
        // attacker tries to re-claim into the same state
        new.fields[STATE_SLOT] = state_field(STATE_CLAIMED);
        let err = program
            .evaluate(&new, Some(&old), None)
            .expect_err("re-claim into the same state must be rejected");
        match err {
            dregg_cell::ProgramError::ConstraintViolated {
                constraint: StateConstraint::StrictMonotonic { index },
                ..
            } => assert_eq!(index, STATE_SLOT as u8),
            other => panic!("expected StrictMonotonic violation, got {other:?}"),
        }
    }

    #[test]
    fn claimant_overwrite_is_write_once_violation() {
        // First claimer is bound; a second claimer tries to overwrite the
        // claimant hash to steal the bounty → WriteOnce rejects.
        let program = bounty_program();
        let mut old = posted_state(500);
        old.fields[CLAIMANT_HASH_SLOT] = claimant_hash("bob");
        old.fields[STATE_SLOT] = state_field(STATE_CLAIMED);
        old.set_nonce(2);
        let mut new = old.clone();
        new.fields[CLAIMANT_HASH_SLOT] = claimant_hash("mallory");
        new.fields[STATE_SLOT] = state_field(STATE_SUBMITTED);
        let err = program
            .evaluate(&new, Some(&old), None)
            .expect_err("overwriting the claimant must be rejected");
        match err {
            dregg_cell::ProgramError::ConstraintViolated {
                constraint: StateConstraint::WriteOnce { index },
                ..
            } => assert_eq!(index, CLAIMANT_HASH_SLOT as u8),
            other => panic!("expected WriteOnce violation, got {other:?}"),
        }
    }

    #[test]
    fn reward_change_is_write_once_violation() {
        // The reward is set at posting; lowering it later (after a worker has
        // committed) is rejected by the WriteOnce caveat on REWARD_SLOT.
        let program = bounty_program();
        let mut old = posted_state(500);
        old.set_nonce(1);
        let mut new = old.clone();
        new.fields[REWARD_SLOT] = reward_field(100); // lower the reward
        new.fields[STATE_SLOT] = state_field(STATE_CLAIMED);
        new.fields[CLAIMANT_HASH_SLOT] = claimant_hash("bob");
        let err = program
            .evaluate(&new, Some(&old), None)
            .expect_err("lowering the reward must be rejected");
        match err {
            dregg_cell::ProgramError::ConstraintViolated {
                constraint: StateConstraint::WriteOnce { index },
                ..
            } => assert_eq!(index, REWARD_SLOT as u8),
            other => panic!("expected WriteOnce violation, got {other:?}"),
        }
    }

    #[test]
    fn state_cannot_go_backward() {
        // A submitted bounty cannot be reverted to claimed.
        let program = bounty_program();
        let mut old = posted_state(500);
        old.fields[STATE_SLOT] = state_field(STATE_SUBMITTED);
        old.set_nonce(3);
        let mut new = old.clone();
        new.fields[STATE_SLOT] = state_field(STATE_CLAIMED);
        let err = program
            .evaluate(&new, Some(&old), None)
            .expect_err("state regression must be rejected");
        assert!(matches!(
            err,
            dregg_cell::ProgramError::ConstraintViolated {
                constraint: StateConstraint::StrictMonotonic { .. },
                ..
            }
        ));
    }

    // ── Turn-builder shape ───────────────────────────────────────────────

    #[test]
    fn post_action_writes_three_slots_and_emits_event() {
        let cclerk = test_cipherclerk();
        let action = build_post_action(&cclerk, bounty_cell(), "fix the bug", 500);
        assert_eq!(action.effects.len(), 4);
        assert!(matches!(
            &action.effects[0],
            Effect::SetField { index, .. } if *index == TITLE_HASH_SLOT
        ));
        assert!(matches!(
            &action.effects[1],
            Effect::SetField { index, .. } if *index == REWARD_SLOT
        ));
        assert!(matches!(
            &action.effects[2],
            Effect::SetField { index, value, .. } if *index == STATE_SLOT && *value == state_field(STATE_OPEN)
        ));
        match action.authorization {
            Authorization::Signature(a, b) => assert!(a != [0u8; 32] || b != [0u8; 32]),
            other => panic!("expected Signature, got {other:?}"),
        }
    }

    // ── End-to-end factory-birth + caveat-biting through EmbeddedExecutor ─

    /// Births a bounty cell from the deployed factory, posts → claims → submits
    /// → pays out (all accepted), then proves the gating bites: a competing
    /// second claim is rejected by the WriteOnce/StrictMonotonic caveats
    /// installed at birth. This is the gating actually biting on a
    /// *factory-born* cell, end to end.
    #[test]
    fn factory_born_bounty_runs_lifecycle_and_rejects_double_claim() {
        let cclerk = test_cipherclerk();
        let exec = EmbeddedExecutor::new(&cclerk, "default");
        exec.deploy_factory(bounty_factory_descriptor());

        // Fund the operator agent cell so it can pay turn fees.
        let agent = cclerk.cell_id();
        exec.with_ledger_mut(|ledger| {
            if let Some(cell) = ledger.get_mut(&agent) {
                cell.state.set_balance(100_000_000);
            }
        });

        // Birth a bounty cell from the factory.
        let owner = cclerk.public_key().0;
        let token: [u8; 32] = *blake3::hash(b"bounty-token-1").as_bytes();
        let params = FactoryCreationParams {
            mode: CellMode::Sovereign,
            program_vk: Some(bounty_child_program_vk()),
            initial_fields: vec![],
            initial_caps: vec![],
            owner_pubkey: owner,
        };
        let birth = cclerk.create_from_factory(BOUNTY_FACTORY_VK, owner, token, params);
        exec.submit_turn(&birth).expect("bounty birth commits");

        let bounty = CellId::derive_raw(&owner, &token);

        // The born cell must carry the slot caveats as its program.
        let has_program = exec.with_ledger_mut(|ledger| {
            ledger
                .get(&bounty)
                .map(|c| !c.program.is_none())
                .unwrap_or(false)
        });
        assert!(has_program, "factory-born bounty must carry a CellProgram");

        // Hand the creator an owner capability over the born cell, so the
        // operator agent can author turns that reach it (the creator-owns-its-
        // factory-cell handoff). The slot caveats still bite on every write.
        exec.with_ledger_mut(|ledger| {
            if let Some(agent_cell) = ledger.get_mut(&agent) {
                agent_cell
                    .capabilities
                    .grant(bounty, dregg_app_framework::AuthRequired::Signature);
            }
        });

        // Post → Claim → Submit → Payout: the legal lifecycle is accepted.
        exec.submit_action(
            &cclerk,
            build_post_action(&cclerk, bounty, "fix the bug", 500),
        )
        .expect("post commits");
        exec.submit_action(&cclerk, build_claim_action(&cclerk, bounty, "bob"))
            .expect("claim commits");

        // A competing claim on the already-claimed bounty: rejected by the
        // caveats (StrictMonotonic on STATE and/or WriteOnce on CLAIMANT).
        let steal = build_claim_action(&cclerk, bounty, "mallory");
        let err = exec
            .submit_action(&cclerk, steal)
            .expect_err("second claim must be rejected");
        let msg = format!("{err}").to_lowercase();
        assert!(
            msg.contains("monotonic")
                || msg.contains("writeonce")
                || msg.contains("write-once")
                || msg.contains("program"),
            "rejection must cite the slot-caveat violation, got: {msg}"
        );

        // The legitimate claimant continues the workflow.
        exec.submit_action(
            &cclerk,
            build_submit_action(&cclerk, bounty, "dregg://cell/work-artifact"),
        )
        .expect("submit commits");
        exec.submit_action(&cclerk, build_payout_action(&cclerk, bounty))
            .expect("payout commits");
    }

    #[test]
    fn register_installs_factory() {
        let cclerk = test_cipherclerk();
        let exec = EmbeddedExecutor::new(&cclerk, "default");
        let ctx = StarbridgeAppContext::new(cclerk, exec);
        let vk = register(&ctx);
        assert_eq!(vk, BOUNTY_FACTORY_VK);
        assert_eq!(ctx.factory_registry().len(), 1);
    }
}
