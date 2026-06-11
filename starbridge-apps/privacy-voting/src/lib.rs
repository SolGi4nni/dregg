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
    Action, AppCipherclerk, AuthRequired, CapTarget, CapTemplate, CellId, CellMode, CellProgram,
    ChildVkStrategy, ConstantsModule, Effect, Event, FactoryDescriptor, FieldElement,
    InspectorDescriptor, StarbridgeAppContext, StateConstraint, canonical_program_vk,
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

    (poll_vk, ballot_vk)
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
