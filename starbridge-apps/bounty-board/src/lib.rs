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
    Action, AppCipherclerk, AuthRequired, CapTarget, CapTemplate, CellId, CellMode, CellProgram,
    ChildVkStrategy, ConstantsModule, Effect, Event, FactoryDescriptor, FieldElement,
    InspectorDescriptor, StarbridgeAppContext, StateConstraint, canonical_program_vk,
    field_from_bytes, field_from_u64, hex_encode_32, symbol,
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
