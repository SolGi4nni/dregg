//! # starbridge-privacy-voting
//!
//! Greenfield rebuild of the legacy `apps/privacy-voting/` HTTP app as a
//! dregg-native **starbridge-app**: a thin library of [`FactoryDescriptor`]s
//! plus signed turn-builder helpers that compose dregg primitives only
//! (`FactoryDescriptor` + `Effect::SetField` + `Effect::EmitEvent` +
//! `StateConstraint` slot caveats). No `Effect::CastVote`, no
//! `Authorization::Unchecked`, no placeholder signatures.
//!
//! ## The voting model in two factory-born cell kinds
//!
//! A poll is two cell kinds, each born from its own factory:
//!
//! 1. **Poll cell** ([`poll_factory_descriptor`]) — the public tally board.
//!    - `QUESTION_HASH` slot is [`StateConstraint::WriteOnce`] — the question
//!      is fixed at poll creation and can never be re-bound.
//!    - `TALLY_YES` / `TALLY_NO` / `TALLY_ABSTAIN` slots are
//!      [`StateConstraint::Monotonic`] — a tally can only ever **increase**.
//!      An attacker cannot rewrite a tally downward to erase votes.
//!    - `CLOSED` slot is [`StateConstraint::WriteOnce`] — a poll closes
//!      exactly once and cannot be re-opened.
//!
//! 2. **Ballot cell** ([`ballot_factory_descriptor`]) — one per voter, the
//!    capability that authorizes a single vote.
//!    - `POLL_REF` slot is [`StateConstraint::WriteOnce`] — pins which poll
//!      this ballot belongs to.
//!    - `VOTE` slot is [`StateConstraint::WriteOnce`] — **one vote per ballot
//!      cell**. Once a voter writes their choice the slot is frozen; a second
//!      `cast_vote` on the same ballot is rejected by the executor with a
//!      `WriteOnce` violation. This is the core anti-double-vote guarantee,
//!      enforced by the *substrate*, not by app bookkeeping.
//!
//! ### Privacy stance
//!
//! Ballot cells are minted from a caller-chosen blinding `token_id`, so the
//! ballot cell id (`derive_raw(owner, token_id)`) is not linkable to the
//! voter's primary agent cell unless they reuse the token. The `VOTE` slot
//! records the *choice code* ([`VOTE_YES`] / [`VOTE_NO`] / [`VOTE_ABSTAIN`]),
//! not the voter identity. A production privacy tier would additionally
//! blind the choice and prove tally consistency in zero knowledge; this crate
//! lands the *unlinkable-ballot-cell + one-vote-per-cell + monotone-tally*
//! substrate that such a tier composes on top of.
//!
//! ## What this crate exports
//!
//! - [`poll_factory_descriptor`] / [`ballot_factory_descriptor`] — the two
//!   `FactoryDescriptor`s, with their slot caveats baked into
//!   `state_constraints` so every born cell inherits the gating.
//! - [`factory_descriptors`] — both descriptors for host registration.
//! - [`build_open_poll_action`] — writes `QUESTION_HASH`, emits `poll-opened`.
//! - [`build_cast_vote_action`] — writes the ballot `VOTE` slot + bumps the
//!   matching poll tally slot in one signed turn, emits `vote-cast`.
//! - [`build_close_poll_action`] — sets the poll `CLOSED` slot (one-way),
//!   emits `poll-closed`.
//! - [`register`] — mounts the app's factories + inspectors on a
//!   [`StarbridgeAppContext`].

use dregg_app_framework::{
    Action, AppCipherclerk, AuthRequired, CapTarget, CapTemplate, CellAffordance, CellId, CellMode,
    CellProgram, ChildVkStrategy, ConstantsModule, DeosApp, DeosCell, Effect, EmbeddedExecutor,
    Event, FactoryDescriptor, FieldElement, FireError, FireExecuteError, GatedAffordance,
    InspectorDescriptor, StarbridgeAppContext, StateConstraint, TurnReceipt, canonical_program_vk,
    field_from_bytes, field_from_u64, hex_encode_32, symbol,
};

// =============================================================================
// Poll-cell state schema
// =============================================================================

/// Poll cell slot: BLAKE3 of the poll question text. `WriteOnce`.
pub const QUESTION_HASH_SLOT: usize = 2;
/// Poll cell slot: running count of YES votes. `Monotonic`.
pub const TALLY_YES_SLOT: usize = 3;
/// Poll cell slot: running count of NO votes. `Monotonic`.
pub const TALLY_NO_SLOT: usize = 4;
/// Poll cell slot: running count of ABSTAIN votes. `Monotonic`.
pub const TALLY_ABSTAIN_SLOT: usize = 5;
/// Poll cell slot: non-zero once the poll is closed. `WriteOnce`.
pub const CLOSED_SLOT: usize = 6;

// =============================================================================
// Ballot-cell state schema
// =============================================================================

/// Ballot cell slot: BLAKE3-bound reference to the poll cell this ballot votes
/// in. `WriteOnce` — a ballot is permanently bound to one poll.
pub const POLL_REF_SLOT: usize = 2;
/// Ballot cell slot: the voter's choice code. `WriteOnce` — **one vote per
/// ballot cell**.
pub const VOTE_SLOT: usize = 3;

// =============================================================================
// Vote choice codes (written into the ballot `VOTE` slot)
// =============================================================================

/// Choice code for a YES vote (non-zero so `WriteOnce` treats it as "set").
pub const VOTE_YES: u64 = 1;
/// Choice code for a NO vote.
pub const VOTE_NO: u64 = 2;
/// Choice code for an ABSTAIN vote.
pub const VOTE_ABSTAIN: u64 = 3;

/// Marker value written into the poll `CLOSED` slot (any non-zero works under
/// `WriteOnce`; a fixed sentinel keeps the encoding reproducible).
pub const CLOSED_MARKER: u64 = 1;

// =============================================================================
// Factory VKs
// =============================================================================

/// Factory VK we publish for the poll factory.
pub const POLL_FACTORY_VK: [u8; 32] = *b"starbridge-privacy-voting-poll!!";
/// Factory VK we publish for the ballot factory.
pub const BALLOT_FACTORY_VK: [u8; 32] = *b"starbridge-privacy-voting-ballot";

// =============================================================================
// Cell programs (the slot caveats, also returned by the descriptors)
// =============================================================================

/// The `CellProgram` installed on every poll cell: question is write-once,
/// tallies are monotone, the closed flag is write-once.
pub fn poll_cell_program() -> CellProgram {
    CellProgram::always(poll_state_constraints())
}

fn poll_state_constraints() -> Vec<StateConstraint> {
    vec![
        StateConstraint::WriteOnce {
            index: QUESTION_HASH_SLOT as u8,
        },
        StateConstraint::Monotonic {
            index: TALLY_YES_SLOT as u8,
        },
        StateConstraint::Monotonic {
            index: TALLY_NO_SLOT as u8,
        },
        StateConstraint::Monotonic {
            index: TALLY_ABSTAIN_SLOT as u8,
        },
        StateConstraint::WriteOnce {
            index: CLOSED_SLOT as u8,
        },
    ]
}

/// The `CellProgram` installed on every ballot cell: poll-ref is write-once,
/// and the vote slot is write-once (one vote per ballot cell).
pub fn ballot_cell_program() -> CellProgram {
    CellProgram::always(ballot_state_constraints())
}

fn ballot_state_constraints() -> Vec<StateConstraint> {
    vec![
        StateConstraint::WriteOnce {
            index: POLL_REF_SLOT as u8,
        },
        StateConstraint::WriteOnce {
            index: VOTE_SLOT as u8,
        },
    ]
}

/// Canonical child-program VK for poll cells.
pub fn poll_child_program_vk() -> [u8; 32] {
    canonical_program_vk(&poll_cell_program())
}

/// Canonical child-program VK for ballot cells.
pub fn ballot_child_program_vk() -> [u8; 32] {
    canonical_program_vk(&ballot_cell_program())
}

// =============================================================================
// FactoryDescriptors
// =============================================================================

/// Build the poll-cell `FactoryDescriptor`.
///
/// The poll is born empty and opened by its first turn: `QUESTION_HASH` is
/// written by [`build_open_poll_action`] against the freshly-minted cell. We
/// carry **no creation-time `field_constraints`** — those validate against
/// `params.initial_fields` (`(u32, u64)` pairs that cannot carry the 32-byte
/// `blake3(question)`). The meaningful gating is the *perpetual*
/// `state_constraints`: question + closed are `WriteOnce`, the three tallies are
/// `Monotonic`. Those are installed as the born cell's `CellProgram` and bite on
/// every subsequent turn (including `open_poll`, where `WriteOnce` admits the
/// first write from zero).
pub fn poll_factory_descriptor() -> FactoryDescriptor {
    FactoryDescriptor {
        factory_vk: POLL_FACTORY_VK,
        child_program_vk: Some(poll_child_program_vk()),
        child_vk_strategy: Some(ChildVkStrategy::Fixed(Some(poll_child_program_vk()))),
        allowed_cap_templates: vec![CapTemplate {
            target: CapTarget::SelfCell,
            max_permissions: AuthRequired::Signature,
            attenuatable: true,
        }],
        field_constraints: vec![],
        state_constraints: poll_state_constraints(),
        default_mode: CellMode::Sovereign,
        creation_budget: Some(1_000_000),
    }
}

/// Build the ballot-cell `FactoryDescriptor`.
///
/// Perpetual: `POLL_REF` and `VOTE` are both `WriteOnce`. No creation-time
/// field constraint — a freshly-minted ballot is empty until the voter binds
/// it to a poll and casts (the `cast_vote` turn writes both slots).
pub fn ballot_factory_descriptor() -> FactoryDescriptor {
    FactoryDescriptor {
        factory_vk: BALLOT_FACTORY_VK,
        child_program_vk: Some(ballot_child_program_vk()),
        child_vk_strategy: Some(ChildVkStrategy::Fixed(Some(ballot_child_program_vk()))),
        allowed_cap_templates: vec![CapTemplate {
            target: CapTarget::SelfCell,
            max_permissions: AuthRequired::Signature,
            attenuatable: true,
        }],
        field_constraints: vec![],
        state_constraints: ballot_state_constraints(),
        default_mode: CellMode::Sovereign,
        creation_budget: Some(100_000_000),
    }
}

/// All factory descriptors this starbridge-app contributes.
pub fn factory_descriptors() -> Vec<FactoryDescriptor> {
    vec![poll_factory_descriptor(), ballot_factory_descriptor()]
}

// =============================================================================
// Turn-builders
// =============================================================================

/// Build the signed `Action` that opens a poll: writes the question hash and
/// emits `poll-opened`. Run against a freshly factory-born poll cell.
pub fn build_open_poll_action(
    cipherclerk: &AppCipherclerk,
    poll_cell: CellId,
    question: &str,
) -> Action {
    let q = field_from_bytes(question.as_bytes());
    let effects = vec![
        Effect::SetField {
            cell: poll_cell,
            index: QUESTION_HASH_SLOT,
            value: q,
        },
        Effect::EmitEvent {
            cell: poll_cell,
            event: Event::new(symbol("poll-opened"), vec![q]),
        },
    ];
    cipherclerk.make_action(poll_cell, "open_poll", effects)
}

/// Build the signed `Action` that casts a vote on the voter's *ballot* cell.
///
/// The action targets the ballot cell (the voter's own factory-born cell) and:
/// 1. binds the ballot to the poll (`POLL_REF`, write-once),
/// 2. records the choice in the ballot `VOTE` slot (write-once — the
///    one-vote-per-cell tooth),
/// 3. emits `vote-cast` (carrying only the poll ref + choice, not the voter).
///
/// The matching poll-tally bump is a *separate* action against the poll cell
/// ([`build_record_tally_action`]) — the ballot and poll are independently-
/// owned cells, so the voter writes their ballot and the tally is recorded
/// against the poll cell on its own authority. The two are composed into one
/// turn at the call-site (see [`AppCipherclerk::make_turn_with_actions`]) when a
/// single atomic vote-and-tally is wanted and the poll cell's `set_state`
/// permission admits the caller.
pub fn build_cast_vote_action(
    cipherclerk: &AppCipherclerk,
    ballot_cell: CellId,
    poll_cell: CellId,
    choice: u64,
) -> Action {
    let poll_ref = field_from_bytes(poll_cell.as_bytes());
    let choice_field = field_from_u64(choice);
    let effects = vec![
        Effect::SetField {
            cell: ballot_cell,
            index: POLL_REF_SLOT,
            value: poll_ref,
        },
        Effect::SetField {
            cell: ballot_cell,
            index: VOTE_SLOT,
            value: choice_field,
        },
        Effect::EmitEvent {
            cell: ballot_cell,
            event: Event::new(symbol("vote-cast"), vec![poll_ref, choice_field]),
        },
    ];
    cipherclerk.make_action(ballot_cell, "cast_vote", effects)
}

/// Build the signed `Action` that bumps a poll tally on the *poll* cell.
///
/// Targets the poll cell directly and sets the matching tally slot to
/// `new_tally` (the post-increment count the caller read off the poll cell:
/// old + 1). The poll's `Monotonic` caveat rejects any value below the current
/// tally, so a stale/replayed value cannot shrink the board. Emits `vote-cast`.
pub fn build_record_tally_action(
    cipherclerk: &AppCipherclerk,
    poll_cell: CellId,
    choice: u64,
    new_tally: u64,
) -> Action {
    let choice_field = field_from_u64(choice);
    let tally_slot = tally_slot_for_choice(choice);
    let effects = vec![
        Effect::SetField {
            cell: poll_cell,
            index: tally_slot,
            value: field_from_u64(new_tally),
        },
        Effect::EmitEvent {
            cell: poll_cell,
            event: Event::new(symbol("vote-cast"), vec![choice_field]),
        },
    ];
    cipherclerk.make_action(poll_cell, "record_tally", effects)
}

/// Build the signed `Action` that closes a poll (one-way `CLOSED` slot).
pub fn build_close_poll_action(cipherclerk: &AppCipherclerk, poll_cell: CellId) -> Action {
    let marker = field_from_u64(CLOSED_MARKER);
    let effects = vec![
        Effect::SetField {
            cell: poll_cell,
            index: CLOSED_SLOT,
            value: marker,
        },
        Effect::EmitEvent {
            cell: poll_cell,
            event: Event::new(symbol("poll-closed"), vec![marker]),
        },
    ];
    cipherclerk.make_action(poll_cell, "close_poll", effects)
}

/// Which poll tally slot a choice code increments.
pub fn tally_slot_for_choice(choice: u64) -> usize {
    match choice {
        VOTE_YES => TALLY_YES_SLOT,
        VOTE_NO => TALLY_NO_SLOT,
        _ => TALLY_ABSTAIN_SLOT,
    }
}

// =============================================================================
// Convenience encoders (mirror what the executor + CLI see)
// =============================================================================

/// `blake3(question)` — the value written into `QUESTION_HASH_SLOT`.
pub fn question_hash(question: &str) -> FieldElement {
    field_from_bytes(question.as_bytes())
}

/// The poll-ref value a ballot records (`blake3(poll_cell_bytes)`).
pub fn poll_ref(poll_cell: CellId) -> FieldElement {
    field_from_bytes(poll_cell.as_bytes())
}

// =============================================================================
// StarbridgeAppContext mount
// =============================================================================

/// Web-constants module (single source of truth for the JS surface).
pub fn web_constants() -> ConstantsModule {
    ConstantsModule::new("privacy-voting")
        .slot("QUESTION_HASH_SLOT", QUESTION_HASH_SLOT as u64)
        .slot("TALLY_YES_SLOT", TALLY_YES_SLOT as u64)
        .slot("TALLY_NO_SLOT", TALLY_NO_SLOT as u64)
        .slot("TALLY_ABSTAIN_SLOT", TALLY_ABSTAIN_SLOT as u64)
        .slot("CLOSED_SLOT", CLOSED_SLOT as u64)
        .slot("POLL_REF_SLOT", POLL_REF_SLOT as u64)
        .slot("VOTE_SLOT", VOTE_SLOT as u64)
        .string("POLL_FACTORY_VK_HEX", hex_encode_32(&POLL_FACTORY_VK))
        .string("BALLOT_FACTORY_VK_HEX", hex_encode_32(&BALLOT_FACTORY_VK))
        .topic("POLL_OPENED", "poll-opened")
        .topic("VOTE_CAST", "vote-cast")
        .topic("POLL_CLOSED", "poll-closed")
}

/// Register this starbridge-app on a [`StarbridgeAppContext`].
///
/// Installs both factory descriptors and the poll/ballot inspectors. Returns
/// the two registered factory VKs `(poll, ballot)`.
pub fn register(ctx: &StarbridgeAppContext) -> ([u8; 32], [u8; 32]) {
    let poll_vk = ctx.register_factory(poll_factory_descriptor());
    let ballot_vk = ctx.register_factory(ballot_factory_descriptor());

    ctx.register_inspector(InspectorDescriptor {
        kind: "poll".into(),
        descriptor: serde_json::json!({
            "component": "dregg-poll",
            "module": "/starbridge-apps/privacy-voting/inspectors.js",
            "uri_prefix": "dregg://cell/",
            "summary_fields": ["question_hash", "tally_yes", "tally_no", "tally_abstain", "closed"],
            "slot_layout": {
                "question_hash": QUESTION_HASH_SLOT,
                "tally_yes":     TALLY_YES_SLOT,
                "tally_no":      TALLY_NO_SLOT,
                "tally_abstain": TALLY_ABSTAIN_SLOT,
                "closed":        CLOSED_SLOT,
            },
            "factory_vk_hex": hex_encode_32(&poll_vk),
            "child_program_vk_hex": hex_encode_32(&poll_child_program_vk()),
        }),
    });

    ctx.register_inspector(InspectorDescriptor {
        kind: "ballot".into(),
        descriptor: serde_json::json!({
            "component": "dregg-ballot",
            "module": "/starbridge-apps/privacy-voting/inspectors.js",
            "uri_prefix": "dregg://cell/",
            "summary_fields": ["poll_ref", "vote"],
            "slot_layout": {
                "poll_ref": POLL_REF_SLOT,
                "vote":     VOTE_SLOT,
            },
            "factory_vk_hex": hex_encode_32(&ballot_vk),
            "child_program_vk_hex": hex_encode_32(&ballot_child_program_vk()),
        }),
    });

    // Mount the deos-native composition surface (the two-cell `DeosApp`) on the SAME
    // context — the census promotion: the deos surface now ships from `src/`, not from a
    // side-proof in `tests/`. The factory + inspectors are where SOUNDNESS lives (a double
    // vote / monotone-tally rewind is a real executor refusal on the born cell); the deos
    // surface is the composition skin (per-viewer projection, the cap∧state gated fires,
    // the `dregg://` publish, the rehydratable snapshot, the manifest).
    register_deos(ctx);

    (poll_vk, ballot_vk)
}

// =============================================================================
// The deos-native surface — the POLL + BALLOT as a composed two-cell `DeosApp`.
// =============================================================================
//
// `docs/deos/APPS-DEOS-INTEGRATION-CENSUS.md`: privacy-voting, re-expressed as a composed
// [`DeosApp`] and PROMOTED into `src/` (it lived only in the floor's factory-birth tests).
// The interaction surface is ONE [`DeosApp`] ([`voting_app`] below) with **TWO cells** —
// the poll cell (the public tally board) and the ballot cell (the per-voter capability) —
// each carrying its own affordances; the framework wires the rest (per-viewer projection,
// the web-of-cells publish, the rehydratable snapshot, the generated component, the
// manifest), none of which the floor's factory-born bones had.
//
// ## Two cells, distinct CellIds (the two-cell subtlety)
//
// A `DeosApp`'s cells must have distinct [`CellId`]s. The POLL cell is the agent's OWN cell
// (`cipherclerk.cell_id()`) so fires execute against the seeded embedded ledger. The BALLOT
// cell is a distinct COMPANION cell, derived deterministically from the agent's pubkey under
// a fixed blinding token ([`ballot_cell_id`]) and birthed into the SAME embedded ledger
// ([`seed_ballot`] does `EmbeddedExecutor::ensure_cell` + grants the agent a cap reaching it,
// mirroring the factory-birth companion-cell pattern). BOTH cells are seeded so the gated
// fires have live state — a fire whose target cell has no live state is fail-closed
// (`cell_state` returns `None` ⇒ `StateConditionUnmet`). In production the ballot is a real
// per-voter factory-born cell (`ballot_factory_descriptor` mints it under the voter's own
// blinding token); here one operator agent seeds both for the end-to-end fire.
//
// ## The seam is closed — a TWO-TEMPO fire
//
// The state-mutating operations (`cast_vote`, `record_tally`, `close_poll`) are
// [`GatedAffordance`]s carrying a live-state PRECONDITION; the FULL slot caveats (the
// ballot's `WriteOnce(VOTE)`, the poll's `Monotonic(tally)` + `WriteOnce(CLOSED)`) are
// INSTALLED on the seeded cells ([`seed_poll`] / [`seed_ballot`]) and RE-ENFORCED by the
// executor on every touching turn:
//
//   1. the deos PRECONDITION gate (the cap-gate `is_attenuation` AND the live-state
//      precondition `CellProgram::evaluate`) decides the button's verdict IN-BAND — nothing
//      submitted on a miss (anti-ghost; the htmx reactivity rides this);
//   2. [`fire_cast_vote`] / [`fire_record_tally`] / [`fire_close_poll`] then submit the FULL
//      turn, and the executor RE-ENFORCES the installed caveats — so a SECOND `cast_vote`
//      rewriting the ballot's `VOTE` (`WriteOnce(VOTE)`), a tally REWIND
//      (`Monotonic(TALLY_*)`), and a poll RE-OPEN (`WriteOnce(CLOSED)`) are REAL executor
//      refusals in the SUBMISSION path — the half the floor's `evaluate`-only tests never
//      exercised through a real signed turn (see `tests/deos_seam.rs`).

/// The privacy-voting rights tiers, ON THE REAL ATTENUATION LATTICE — these ARE the roles
/// the floor crate's cap-graph enforces:
///
///   - a VIEWER (the public) holds [`AuthRequired::Signature`] — the narrow read tier: it
///     can `view_poll` (read the tally board) and nothing else;
///   - a VOTER holds [`AuthRequired::Either`] — it can `cast_vote` (one vote on its ballot)
///     AND view;
///   - the ADMINISTRATOR (the poll runner) holds [`AuthRequired::None`]/root — it can
///     `record_tally` and `close_poll` on top of everything a voter can do.
///
/// So `Signature ⊂ Either ⊂ None` IS the viewer ⊂ voter ⊂ administrator ladder.
pub const VIEWER_RIGHTS: AuthRequired = AuthRequired::Signature;
/// The voter rights tier (sig-or-proof — cast a vote + view). See [`VIEWER_RIGHTS`].
pub const VOTER_RIGHTS: AuthRequired = AuthRequired::Either;
/// The administrator rights tier (root — record tallies + close the poll + all). See [`VIEWER_RIGHTS`].
pub const ADMINISTRATOR_RIGHTS: AuthRequired = AuthRequired::None;

/// The fixed blinding token the in-test/seeded BALLOT companion cell is derived under (the
/// production ballot uses the voter's own blinding token via the factory). The derived id
/// ([`ballot_cell_id`]) is distinct from the agent's primary poll cell id, satisfying the
/// `DeosApp` distinct-CellId requirement.
pub const SEEDED_BALLOT_TOKEN: [u8; 32] = *b"starbridge-voting-ballot-seed!!!";

/// The BALLOT companion cell id for `agent_pubkey` — `derive_raw(agent_pubkey,
/// SEEDED_BALLOT_TOKEN)`, distinct from the agent's own poll cell. The fire targets this id
/// (the gated `cast_vote` affordance's effect names it), so it must be seeded into the
/// executor ([`seed_ballot`]) for the fire to reach live state.
pub fn ballot_cell_id(agent_pubkey: &[u8; 32]) -> CellId {
    CellId::derive_raw(agent_pubkey, &SEEDED_BALLOT_TOKEN)
}

/// The **POLL live-state precondition** for `record_tally` / `close_poll` — the poll must be
/// OPEN (`CLOSED == 0`). A real [`CellProgram`] read against the cell's current state, so a
/// tally/close button is DARK on a closed poll and LIT while it is open (the htmx tooth).
/// This gates "may the administrator act now"; the tally/close INVARIANTS
/// (`Monotonic(TALLY_*)` / `WriteOnce(CLOSED)`) are the installed [`poll_cell_program`] the
/// executor re-enforces on the produced transition.
pub fn poll_open_precondition() -> CellProgram {
    CellProgram::Predicate(vec![StateConstraint::FieldEquals {
        index: CLOSED_SLOT as u8,
        value: field_from_u64(0),
    }])
}

/// The **BALLOT live-state precondition** for `cast_vote` — the ballot must be UNSET
/// (`VOTE == 0`, i.e. this ballot has not yet voted). So the `cast_vote` button is LIT on a
/// fresh ballot and goes DARK the instant a vote is cast (the htmx tooth — one vote per
/// ballot is visible in the surface). The executor's installed `WriteOnce(VOTE)` is the
/// second guard (a second `cast_vote` is a real refusal).
pub fn ballot_unset_precondition() -> CellProgram {
    CellProgram::Predicate(vec![StateConstraint::FieldEquals {
        index: VOTE_SLOT as u8,
        value: field_from_u64(0),
    }])
}

/// **The privacy-voting POLL + BALLOT as a composed two-cell [`DeosApp`]** — the whole
/// interaction surface, on the deos bones. The POLL cell is the agent's OWN cell
/// (`cipherclerk.cell_id()`); the BALLOT cell is the distinct companion ([`ballot_cell_id`]).
/// Both are seeded so fires execute against live state.
///
/// Operations on the viewer ⊂ voter ⊂ administrator rights ladder:
///
///   - `view_poll` — a cap-only affordance on the POLL cell (a VIEWER reads the tally board):
///     `Signature`, an `EmitEvent`;
///   - `cast_vote` — a [`GatedAffordance`] on the BALLOT cell (a VOTER casts one vote):
///     `Either`, a live-state PRECONDITION (the ballot is unset, `VOTE == 0`); the real fire
///     ([`fire_cast_vote`]) submits the FULL vote turn, re-enforced by the executor's
///     installed `WriteOnce(VOTE)` (a second vote REFUSED);
///   - `record_tally` — a [`GatedAffordance`] on the POLL cell (the ADMINISTRATOR bumps a
///     tally): `None`/root, a live-state PRECONDITION (the poll is open, `CLOSED == 0`); the
///     real fire ([`fire_record_tally`]) reads the live tally and writes `live + 1`,
///     re-enforced by `Monotonic(TALLY_*)` (a rewind REFUSED);
///   - `close_poll` — a [`GatedAffordance`] on the POLL cell (the ADMINISTRATOR closes the
///     poll): `None`/root, a live-state PRECONDITION (the poll is open); the real fire
///     ([`fire_close_poll`]) sets `CLOSED := 1`, re-enforced by `WriteOnce(CLOSED)` (a
///     re-open REFUSED).
///
/// The POLL cell is published into the web-of-cells at the viewer tier (a peer on another
/// federation reacquires the public tally board across the membrane) and is discoverable
/// under `voting` / `poll`.
///
/// Seed both cells with [`seed_poll`] + [`seed_ballot`] so the gated fires have live state
/// and the executor re-enforces the caveats.
pub fn voting_app(cipherclerk: &AppCipherclerk, executor: &EmbeddedExecutor) -> DeosApp {
    let poll = cipherclerk.cell_id();
    let ballot = ballot_cell_id(&cipherclerk.public_key().0);

    // `view_poll` — a VIEWER reads the public tally board. Cap-only (the read surface), the
    // narrowest tier.
    let view = CellAffordance::new(
        "view_poll",
        VIEWER_RIGHTS,
        Effect::EmitEvent {
            cell: poll,
            event: Event::new(symbol("poll-read"), vec![]),
        },
    );

    // `cast_vote` — a VOTER casts ONE vote on its BALLOT cell. The GatedAffordance carries
    // the DECISIVE effect (the `VOTE` write) as its surface representative AND a live-state
    // PRECONDITION ([`ballot_unset_precondition`]: `VOTE == 0`) — so the button is lit on a
    // fresh ballot and DARK after the vote (the htmx tooth), and the cap∧state gate decides
    // its verdict in-band. The actual fire ([`fire_cast_vote`]) submits the FULL vote turn
    // (poll-ref + vote + event), which the executor re-enforces `WriteOnce(VOTE)` on — a
    // SECOND vote is REFUSED.
    let cast_vote = GatedAffordance::new(
        CellAffordance::new(
            "cast_vote",
            VOTER_RIGHTS,
            Effect::SetField {
                cell: ballot,
                index: VOTE_SLOT,
                value: field_from_u64(VOTE_YES),
            },
        ),
        ballot_unset_precondition(),
    );

    // `record_tally` — the ADMINISTRATOR bumps a poll tally. The decisive effect advances a
    // tally slot; gated on the OPEN precondition ([`poll_open_precondition`]: `CLOSED == 0`).
    // The executor re-enforces `Monotonic(TALLY_*)` (a rewind is refused).
    let record_tally = GatedAffordance::new(
        CellAffordance::new(
            "record_tally",
            ADMINISTRATOR_RIGHTS,
            Effect::SetField {
                cell: poll,
                index: TALLY_YES_SLOT,
                value: field_from_u64(1),
            },
        ),
        poll_open_precondition(),
    );

    // `close_poll` — the ADMINISTRATOR closes the poll (one-way). The decisive effect sets
    // `CLOSED := 1`; gated on the OPEN precondition (so the button darkens after the first
    // close). The executor re-enforces `WriteOnce(CLOSED)` (a re-open is refused).
    let close_poll = GatedAffordance::new(
        CellAffordance::new(
            "close_poll",
            ADMINISTRATOR_RIGHTS,
            Effect::SetField {
                cell: poll,
                index: CLOSED_SLOT,
                value: field_from_u64(CLOSED_MARKER),
            },
        ),
        poll_open_precondition(),
    );

    DeosApp::builder("privacy-voting", cipherclerk.clone(), executor.clone())
        .discoverable(vec!["voting".into(), "poll".into()])
        .cell(
            DeosCell::new(poll, "poll")
                .affordance(view)
                .gated(record_tally)
                .gated(close_poll)
                .publish(VIEWER_RIGHTS),
        )
        .cell(
            DeosCell::new(ballot, "ballot")
                .gated(cast_vote)
                .at_route("/ballot"),
        )
        .build()
}

/// **Seed the POLL cell** so the gated fires have live state + the caveats bite: install the
/// full [`poll_cell_program`] on the poll cell (so the executor re-enforces it on every
/// touching turn), then bind the genesis state directly into the embedded ledger — the
/// question hash (`WriteOnce`), the three tallies at 0, and `CLOSED` at 0 (open). After
/// seeding, the poll is open with a fixed question — a real `(old, new)` baseline against
/// which `record_tally` advances and `close_poll` flips `CLOSED`. Returns the question hash.
pub fn seed_poll(executor: &EmbeddedExecutor, question: &str) -> FieldElement {
    let poll = executor.cell_id();
    executor.install_program(poll, poll_cell_program());
    let q = question_hash(question);
    executor.with_ledger_mut(|ledger| {
        if let Some(cell) = ledger.get_mut(&poll) {
            cell.state.set_field(QUESTION_HASH_SLOT, q);
            cell.state.set_field(TALLY_YES_SLOT, field_from_u64(0));
            cell.state.set_field(TALLY_NO_SLOT, field_from_u64(0));
            cell.state.set_field(TALLY_ABSTAIN_SLOT, field_from_u64(0));
            cell.state.set_field(CLOSED_SLOT, field_from_u64(0));
        }
    });
    q
}

/// **Seed the BALLOT companion cell** so the `cast_vote` gated fire has live state + the
/// `WriteOnce(VOTE)` caveat bites. Unlike the poll cell (the agent's own), the ballot is a
/// distinct companion: it is birthed into the SAME embedded ledger via
/// [`EmbeddedExecutor::ensure_cell`] (a Sovereign cell owned by the agent's pubkey under
/// [`SEEDED_BALLOT_TOKEN`]), carrying the [`ballot_cell_program`] as its installed program
/// so the executor re-enforces the slot caveats, and the agent is granted a `Signature` cap
/// reaching it so the operator can author the `cast_vote` turn. The genesis state binds
/// `POLL_REF` (`WriteOnce`, the poll this ballot votes in) and leaves `VOTE` at 0 (unset).
/// Mirrors the factory-birth companion-cell pattern. Returns the ballot cell id.
pub fn seed_ballot(
    executor: &EmbeddedExecutor,
    cipherclerk: &AppCipherclerk,
    poll: CellId,
) -> CellId {
    let pk = cipherclerk.public_key().0;
    let ballot = ballot_cell_id(&pk);

    // Birth the companion ballot cell into the embedded ledger (Sovereign, agent-owned).
    let mut cell = dregg_cell::Cell::new(pk, SEEDED_BALLOT_TOKEN);
    cell.program = ballot_cell_program();
    cell.state.set_field(POLL_REF_SLOT, poll_ref(poll));
    cell.state.set_field(VOTE_SLOT, field_from_u64(0));
    let _ = executor.ensure_cell(cell);

    // Re-assert the program in case the cell already existed (ensure_cell is a no-op then).
    executor.install_program(ballot, ballot_cell_program());

    // Grant the operator agent an owner cap reaching the ballot so the cast-vote turn can
    // author against it (the executor's c-list authorization gate requires a reaching cap).
    let agent = cipherclerk.cell_id();
    executor.with_ledger_mut(|ledger| {
        if let Some(agent_cell) = ledger.get_mut(&agent) {
            agent_cell
                .capabilities
                .grant(ballot, AuthRequired::Signature);
        }
    });
    ballot
}

/// **Fire `cast_vote`** — the deos cap∧state PRECONDITION gate (anti-ghost, in-band), then
/// the FULL multi-effect vote turn the executor re-enforces the ballot caveats on. The
/// two-tempo bridge: the gated affordance decides the button's verdict (cap ⊇ Either AND the
/// ballot is unset) WITHOUT touching the executor; on both passing, the complete vote turn
/// ([`build_cast_vote_action`]'s effects: poll-ref + vote + event) is submitted, and the
/// executor's re-enforcement of [`ballot_cell_program`] is the SECOND, verified gate
/// (`WriteOnce(VOTE)` bites — a SECOND vote is REFUSED). Anti-ghost both ways: a precondition
/// miss never submits; a caveat violation is a real executor refusal.
///
/// `choice` is the vote code ([`VOTE_YES`] / [`VOTE_NO`] / [`VOTE_ABSTAIN`]); the poll-ref is
/// read from the ballot's live `POLL_REF`. Use [`seed_ballot`] first.
pub fn fire_cast_vote(
    app: &DeosApp,
    held: &AuthRequired,
    choice: u64,
    cipherclerk: &AppCipherclerk,
    executor: &EmbeddedExecutor,
) -> Result<TurnReceipt, FireExecuteError> {
    let ballot = ballot_cell_id(&cipherclerk.public_key().0);
    let cell = app
        .cell(&ballot)
        .ok_or(FireExecuteError::Gate(FireError::NoSuchAffordance))?;
    let poll_ref_value = executor
        .cell_state(ballot)
        .map(|s| s.fields[POLL_REF_SLOT])
        .unwrap_or([0u8; 32]);
    let choice_field = field_from_u64(choice);
    cell.fire_gated_through_executor_with("cast_vote", held, cipherclerk, executor, move |_live| {
        vec![
            Effect::SetField {
                cell: ballot,
                index: POLL_REF_SLOT,
                value: poll_ref_value,
            },
            Effect::SetField {
                cell: ballot,
                index: VOTE_SLOT,
                value: choice_field,
            },
            Effect::EmitEvent {
                cell: ballot,
                event: Event::new(symbol("vote-cast"), vec![poll_ref_value, choice_field]),
            },
        ]
    })
}

/// **Fire `record_tally`** — the deos cap∧state PRECONDITION gate (cap ⊇ root AND the poll is
/// open), then the FULL tally-bump turn read from the poll's LIVE state: the matching tally
/// slot is set to `live_tally + 1` (so the SAME published button advances each fire). The
/// executor re-enforces `Monotonic(TALLY_*)` (a stale/replayed value cannot shrink the
/// board). Use [`seed_poll`] first.
pub fn fire_record_tally(
    app: &DeosApp,
    held: &AuthRequired,
    choice: u64,
    cipherclerk: &AppCipherclerk,
    executor: &EmbeddedExecutor,
) -> Result<TurnReceipt, FireExecuteError> {
    let poll = cipherclerk.cell_id();
    let cell = app
        .cell(&poll)
        .ok_or(FireExecuteError::Gate(FireError::NoSuchAffordance))?;
    let tally_slot = tally_slot_for_choice(choice);
    let choice_field = field_from_u64(choice);
    cell.fire_gated_through_executor_with(
        "record_tally",
        held,
        cipherclerk,
        executor,
        move |live| {
            let live_tally = field_to_u64(&live.fields[tally_slot]);
            vec![
                Effect::SetField {
                    cell: poll,
                    index: tally_slot,
                    value: field_from_u64(live_tally.saturating_add(1)),
                },
                Effect::EmitEvent {
                    cell: poll,
                    event: Event::new(symbol("vote-cast"), vec![choice_field]),
                },
            ]
        },
    )
}

/// **Fire `close_poll`** — the deos cap∧state PRECONDITION gate (cap ⊇ root AND the poll is
/// open), then the FULL close turn (`CLOSED := 1` + `poll-closed` event). The executor
/// re-enforces `WriteOnce(CLOSED)` (a re-open — `CLOSED` 1 -> 0 — is refused). The button
/// goes DARK the instant the poll closes (the `poll_open_precondition` then fails). Use
/// [`seed_poll`] first.
pub fn fire_close_poll(
    app: &DeosApp,
    held: &AuthRequired,
    cipherclerk: &AppCipherclerk,
    executor: &EmbeddedExecutor,
) -> Result<TurnReceipt, FireExecuteError> {
    let poll = cipherclerk.cell_id();
    let cell = app
        .cell(&poll)
        .ok_or(FireExecuteError::Gate(FireError::NoSuchAffordance))?;
    let marker = field_from_u64(CLOSED_MARKER);
    cell.fire_gated_through_executor_with("close_poll", held, cipherclerk, executor, move |_live| {
        vec![
            Effect::SetField {
                cell: poll,
                index: CLOSED_SLOT,
                value: marker,
            },
            Effect::EmitEvent {
                cell: poll,
                event: Event::new(symbol("poll-closed"), vec![marker]),
            },
        ]
    })
}

/// Read a `u64` from the last 8 big-endian bytes of a field element (the inverse of
/// [`field_from_u64`] for the tally counters the poll stores).
fn field_to_u64(f: &FieldElement) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&f[24..32]);
    u64::from_be_bytes(b)
}

/// **Mount the deos-native surface** ([`voting_app`]) on a shared context: build the composed
/// two-cell [`DeosApp`] from the context's cipherclerk + executor, seed BOTH cells (the poll
/// cell's program + genesis state, the ballot companion cell's program + genesis state), and
/// fold the app into the context's affordance registry ([`DeosApp::register`]). Returns the
/// live [`DeosApp`] (so a host can also [`DeosApp::mount`] its axum router /
/// [`DeosApp::publish_all`] into the web-of-cells). This is the PROMOTION: the deos surface
/// now ships from `src/`, not from a side-proof in `tests/`.
pub fn register_deos(ctx: &StarbridgeAppContext) -> DeosApp {
    let app = voting_app(ctx.cipherclerk(), ctx.executor());
    // Seed BOTH cells so the gated fires have live `(old, new)` and the full slot caveats are
    // re-enforced by the executor on every touching turn. The ballot is bound to the poll.
    let poll = ctx.cipherclerk().cell_id();
    seed_poll(ctx.executor(), "ship it?");
    seed_ballot(ctx.executor(), ctx.cipherclerk(), poll);
    app.register(ctx);
    app
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
        AppCipherclerk::new(AgentCipherclerk::new(), [7u8; 32])
    }

    fn poll_cell() -> CellId {
        CellId::from_bytes([2u8; 32])
    }

    fn ballot_cell() -> CellId {
        CellId::from_bytes([3u8; 32])
    }

    // ── Descriptor shape ────────────────────────────────────────────────

    #[test]
    fn descriptors_are_deterministic_and_distinct() {
        assert_eq!(
            poll_factory_descriptor().hash(),
            poll_factory_descriptor().hash()
        );
        assert_ne!(
            poll_factory_descriptor().hash(),
            ballot_factory_descriptor().hash()
        );
    }

    #[test]
    fn poll_factory_bakes_tally_and_writeonce_caveats() {
        let d = poll_factory_descriptor();
        // Question + closed are write-once.
        for idx in [QUESTION_HASH_SLOT, CLOSED_SLOT] {
            assert!(
                d.state_constraints.iter().any(
                    |c| matches!(c, StateConstraint::WriteOnce { index } if *index == idx as u8)
                ),
                "expected WriteOnce on slot {idx}"
            );
        }
        // Three tally slots are monotone.
        for idx in [TALLY_YES_SLOT, TALLY_NO_SLOT, TALLY_ABSTAIN_SLOT] {
            assert!(
                d.state_constraints.iter().any(
                    |c| matches!(c, StateConstraint::Monotonic { index } if *index == idx as u8)
                ),
                "expected Monotonic on slot {idx}"
            );
        }
        assert_eq!(d.state_constraints.len(), 5);
    }

    #[test]
    fn ballot_factory_makes_vote_write_once() {
        let d = ballot_factory_descriptor();
        assert!(
            d.state_constraints.iter().any(
                |c| matches!(c, StateConstraint::WriteOnce { index } if *index == VOTE_SLOT as u8)
            ),
            "ballot VOTE slot must be WriteOnce (one vote per ballot cell)"
        );
        assert_eq!(d.state_constraints.len(), 2);
    }

    // ── Slot-caveat evaluation (executor-side regression) ────────────────

    fn ballot_program() -> dregg_cell::CellProgram {
        dregg_cell::CellProgram::Predicate(ballot_state_constraints())
    }

    fn poll_program() -> dregg_cell::CellProgram {
        dregg_cell::CellProgram::Predicate(poll_state_constraints())
    }

    fn empty() -> dregg_cell::state::CellState {
        dregg_cell::state::CellState::new(0)
    }

    #[test]
    fn first_vote_succeeds() {
        let program = ballot_program();
        let old = empty();
        let mut new = empty();
        new.fields[POLL_REF_SLOT] = poll_ref(poll_cell());
        new.fields[VOTE_SLOT] = field_from_u64(VOTE_YES);
        assert!(program.evaluate(&new, Some(&old), None).is_ok());
    }

    #[test]
    fn double_vote_is_write_once_violation() {
        let program = ballot_program();
        // already voted YES on a non-fresh ballot cell
        let mut old = empty();
        old.fields[POLL_REF_SLOT] = poll_ref(poll_cell());
        old.fields[VOTE_SLOT] = field_from_u64(VOTE_YES);
        old.set_nonce(1);
        // attempt: change the vote to NO
        let mut new = old.clone();
        new.fields[VOTE_SLOT] = field_from_u64(VOTE_NO);
        let err = program
            .evaluate(&new, Some(&old), None)
            .expect_err("second vote must be rejected");
        match err {
            dregg_cell::ProgramError::ConstraintViolated {
                constraint: StateConstraint::WriteOnce { index },
                ..
            } => assert_eq!(index, VOTE_SLOT as u8),
            other => panic!("expected WriteOnce violation, got {other:?}"),
        }
    }

    #[test]
    fn tally_decrease_is_monotonic_violation() {
        let program = poll_program();
        let mut old = empty();
        old.fields[QUESTION_HASH_SLOT] = question_hash("ship it?");
        old.fields[TALLY_YES_SLOT] = field_from_u64(5);
        old.set_nonce(1);
        // attempt: shrink the YES tally from 5 → 4
        let mut new = old.clone();
        new.fields[TALLY_YES_SLOT] = field_from_u64(4);
        let err = program
            .evaluate(&new, Some(&old), None)
            .expect_err("tally decrease must be rejected");
        match err {
            dregg_cell::ProgramError::ConstraintViolated {
                constraint: StateConstraint::Monotonic { index },
                ..
            } => assert_eq!(index, TALLY_YES_SLOT as u8),
            other => panic!("expected Monotonic violation, got {other:?}"),
        }
    }

    #[test]
    fn tally_increase_succeeds() {
        let program = poll_program();
        let mut old = empty();
        old.fields[QUESTION_HASH_SLOT] = question_hash("ship it?");
        old.fields[TALLY_YES_SLOT] = field_from_u64(5);
        old.set_nonce(1);
        let mut new = old.clone();
        new.fields[TALLY_YES_SLOT] = field_from_u64(6);
        assert!(program.evaluate(&new, Some(&old), None).is_ok());
    }

    // ── Turn-builder shape ───────────────────────────────────────────────

    #[test]
    fn cast_vote_action_writes_ballot_slots() {
        let cclerk = test_cipherclerk();
        let action = build_cast_vote_action(&cclerk, ballot_cell(), poll_cell(), VOTE_YES);
        assert_eq!(action.effects.len(), 3);
        assert!(matches!(
            &action.effects[0],
            Effect::SetField { index, .. } if *index == POLL_REF_SLOT
        ));
        assert!(matches!(
            &action.effects[1],
            Effect::SetField { index, .. } if *index == VOTE_SLOT
        ));
        // real signature, not a placeholder
        match action.authorization {
            Authorization::Signature(a, b) => assert!(a != [0u8; 32] || b != [0u8; 32]),
            other => panic!("expected Signature, got {other:?}"),
        }
    }

    #[test]
    fn record_tally_action_bumps_poll_slot() {
        let cclerk = test_cipherclerk();
        let action = build_record_tally_action(&cclerk, poll_cell(), VOTE_YES, 1);
        assert!(matches!(
            &action.effects[0],
            Effect::SetField { index, value, .. }
                if *index == TALLY_YES_SLOT && *value == field_from_u64(1)
        ));
    }

    #[test]
    fn tally_slot_routing_is_correct() {
        assert_eq!(tally_slot_for_choice(VOTE_YES), TALLY_YES_SLOT);
        assert_eq!(tally_slot_for_choice(VOTE_NO), TALLY_NO_SLOT);
        assert_eq!(tally_slot_for_choice(VOTE_ABSTAIN), TALLY_ABSTAIN_SLOT);
    }

    // ── End-to-end factory-birth + caveat-biting through EmbeddedExecutor ─

    /// Births a ballot cell from the deployed factory, casts a vote (accepted),
    /// then attempts a second vote on the same ballot — which the executor
    /// rejects via the `WriteOnce` caveat installed at birth. This is the
    /// gating actually biting on a *factory-born* cell, end to end.
    #[test]
    fn factory_born_ballot_enforces_one_vote_per_cell() {
        let cclerk = test_cipherclerk();
        let exec = EmbeddedExecutor::new(&cclerk, "default");
        exec.deploy_factory(ballot_factory_descriptor());

        // Fund the operator agent cell so it can pay turn fees.
        let agent = cclerk.cell_id();
        exec.with_ledger_mut(|ledger| {
            if let Some(cell) = ledger.get_mut(&agent) {
                cell.state.set_balance(10_000_000);
            }
        });

        // Birth a ballot cell from the factory under a blinding token.
        let owner = cclerk.public_key().0;
        let token: [u8; 32] = *blake3::hash(b"voter-blinding-nonce-1").as_bytes();
        let params = FactoryCreationParams {
            mode: CellMode::Sovereign,
            program_vk: Some(ballot_child_program_vk()),
            initial_fields: vec![],
            initial_caps: vec![],
            owner_pubkey: owner,
        };
        let birth = cclerk.create_from_factory(BALLOT_FACTORY_VK, owner, token, params);
        exec.submit_turn(&birth).expect("ballot birth commits");

        let ballot = CellId::derive_raw(&owner, &token);

        // The born cell must carry the WriteOnce caveats as its program.
        let has_program = exec.with_ledger_mut(|ledger| {
            ledger
                .get(&ballot)
                .map(|c| !c.program.is_none())
                .unwrap_or(false)
        });
        assert!(has_program, "factory-born ballot must carry a CellProgram");

        // Hand the voter an owner capability over their freshly-born ballot
        // cell so the operator agent can author the cast-vote turn that reaches
        // it. The WriteOnce caveat still bites on the second vote.
        exec.with_ledger_mut(|ledger| {
            if let Some(agent_cell) = ledger.get_mut(&agent) {
                agent_cell
                    .capabilities
                    .grant(ballot, dregg_app_framework::AuthRequired::Signature);
            }
        });

        // First vote: accepted.
        let vote1 = build_cast_vote_action(&cclerk, ballot, poll_cell(), VOTE_YES);
        exec.submit_action(&cclerk, vote1)
            .expect("first vote must commit");

        // Second vote on the SAME ballot: rejected by the WriteOnce caveat.
        let vote2 = build_cast_vote_action(&cclerk, ballot, poll_cell(), VOTE_NO);
        let err = exec
            .submit_action(&cclerk, vote2)
            .expect_err("second vote on the same ballot must be rejected");
        let msg = format!("{err}");
        assert!(
            msg.to_lowercase().contains("writeonce")
                || msg.to_lowercase().contains("write-once")
                || msg.to_lowercase().contains("program"),
            "rejection must cite the slot-caveat violation, got: {msg}"
        );
    }

    /// Births a *poll* cell from the deployed factory, opens it, records a tally
    /// bump (accepted), then attempts to shrink the tally — which the executor
    /// rejects via the `Monotonic` caveat installed at birth. The poll cell is
    /// the action target throughout (its own authority), so the gating bites on
    /// a real factory-born poll board.
    #[test]
    fn factory_born_poll_enforces_monotone_tally() {
        let cclerk = test_cipherclerk();
        let exec = EmbeddedExecutor::new(&cclerk, "default");
        exec.deploy_factory(poll_factory_descriptor());

        let agent = cclerk.cell_id();
        exec.with_ledger_mut(|ledger| {
            if let Some(cell) = ledger.get_mut(&agent) {
                cell.state.set_balance(10_000_000);
            }
        });

        let owner = cclerk.public_key().0;
        let token: [u8; 32] = *blake3::hash(b"poll-token-1").as_bytes();
        let params = FactoryCreationParams {
            mode: CellMode::Sovereign,
            program_vk: Some(poll_child_program_vk()),
            initial_fields: vec![],
            initial_caps: vec![],
            owner_pubkey: owner,
        };
        let birth = cclerk.create_from_factory(POLL_FACTORY_VK, owner, token, params);
        exec.submit_turn(&birth).expect("poll birth commits");
        let poll = CellId::derive_raw(&owner, &token);

        exec.with_ledger_mut(|ledger| {
            if let Some(agent_cell) = ledger.get_mut(&agent) {
                agent_cell
                    .capabilities
                    .grant(poll, dregg_app_framework::AuthRequired::Signature);
            }
        });

        // Open the poll (writes the question, write-once).
        exec.submit_action(&cclerk, build_open_poll_action(&cclerk, poll, "ship it?"))
            .expect("open poll commits");

        // Record a YES tally bump 0 -> 1: accepted (monotone increase).
        exec.submit_action(
            &cclerk,
            build_record_tally_action(&cclerk, poll, VOTE_YES, 1),
        )
        .expect("tally bump commits");

        // Attempt to shrink the YES tally 1 -> 0: rejected by Monotonic caveat.
        let shrink = build_record_tally_action(&cclerk, poll, VOTE_YES, 0);
        let err = exec
            .submit_action(&cclerk, shrink)
            .expect_err("tally decrease must be rejected");
        let msg = format!("{err}").to_lowercase();
        assert!(
            msg.contains("monotonic") || msg.contains("program"),
            "rejection must cite the Monotonic caveat, got: {msg}"
        );
    }

    #[test]
    fn register_installs_two_factories() {
        let cclerk = test_cipherclerk();
        let exec = EmbeddedExecutor::new(&cclerk, "default");
        let ctx = StarbridgeAppContext::new(cclerk, exec);
        let (poll_vk, ballot_vk) = register(&ctx);
        assert_eq!(poll_vk, POLL_FACTORY_VK);
        assert_eq!(ballot_vk, BALLOT_FACTORY_VK);
        assert_eq!(ctx.factory_registry().len(), 2);
    }
}
