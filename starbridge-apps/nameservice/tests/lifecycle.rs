//! Integration tests for the `starbridge-nameservice` lifecycle.
//!
//! These exercise the public Rust surface end-to-end:
//!
//! - **Register → set-target → renew → transfer → revoke** as a single
//!   sequence, walking the per-slot state machine the factory descriptor
//!   pins.
//! - **Adversarial executions** that should be rejected by the slot
//!   caveats baked into the factory descriptor:
//!   - Duplicate-name registration (WriteOnce on NAME_HASH_SLOT)
//!   - Expiry decrement (Monotonic on EXPIRY_SLOT)
//!   - Double revocation (WriteOnce on REVOKED_SLOT)
//! - **Authorization adversarial**: an `Authorization::Unchecked` action
//!   does *not* round-trip through `build_*_action` — the AppCipherclerk path
//!   always carries a real Ed25519 signature. We exercise that here as
//!   the regression guard for the `[0u8; 64]` pattern.
//!
//! Tests in this file evaluate the factory's [`StateConstraint`] set
//! directly via `CellProgram::evaluate`. They do *not* spin up a full
//! `Ledger` + `TurnExecutor`, because the executor wires the same
//! `program.evaluate(..)` path on the post-state and the constraint
//! semantics are what these tests need to pin. Integrating against a
//! full `TurnExecutor` is the responsibility of the
//! `protocol-tests/` crate (which exercises the executor + program
//! together) — duplicating that wiring here would just couple this
//! crate to an executor it does not depend on.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, Authorization, CellId, Effect, FieldElement,
};
use dregg_cell::{CellProgram, EvalContext, ProgramError, StateConstraint};
use starbridge_nameservice::{
    EXPIRY_SLOT, NAME_FACTORY_VK, NAME_HASH_SLOT, OWNER_HASH_SLOT, OWNER_PK_SLOT,
    PENDING_OWNER_PK_SLOT, RESOLVE_TARGET_SLOT, REVOKED_SLOT, build_accept_transfer_action,
    build_register_action, build_renew_action, build_revoke_action, build_set_target_action,
    build_transfer_action, expiry_field, factory_descriptors, name_factory_descriptor, name_hash,
    register, resolve_target, revoked_tombstone,
};

// =============================================================================
// Helpers
// =============================================================================

fn cclerk_with_seed(seed_byte: u8) -> AppCipherclerk {
    AppCipherclerk::new(AgentCipherclerk::new(), [seed_byte; 32])
}

fn registry_cell() -> CellId {
    CellId::from_bytes([0x42u8; 32])
}

fn fresh_program() -> CellProgram {
    CellProgram::Predicate(name_factory_descriptor().state_constraints.clone())
}

fn empty_state() -> dregg_cell::state::CellState {
    dregg_cell::state::CellState::new(0)
}

fn project_setfield(action: &dregg_app_framework::Action, slot: usize) -> Option<FieldElement> {
    for effect in &action.effects {
        if let Effect::SetField { index, value, .. } = effect {
            if *index == slot as u64 {
                return Some(*value);
            }
        }
    }
    None
}

/// An [`EvalContext`] carrying `sender` — the raw signer pubkey the executor
/// binds from the verified turn parent (`execute_tree.rs`: `ctx.sender =
/// parent_pk_opt`). The owner-authorization caveats compare this against the
/// authority register (`OWNER_PK_SLOT`).
fn ctx_with_sender(sender: [u8; 32]) -> EvalContext {
    EvalContext {
        sender: Some(sender),
        ..EvalContext::default()
    }
}

// =============================================================================
// Round-trip lifecycle
// =============================================================================

/// Walk a name through its entire lifecycle and confirm each step's
/// post-state passes the factory's `StateConstraint` set when evaluated
/// against the prior state.
#[test]
fn lifecycle_register_set_target_renew_transfer_revoke_round_trips() {
    let program = fresh_program();
    let cipherclerk = cclerk_with_seed(0x10);
    let cell = registry_cell();
    let owner = [0xAAu8; 32];
    let new_owner = [0xBBu8; 32];
    let name = "alice.dregg";

    // ── Step 1: register (creation; old = empty). ────────────────────
    let initial_expiry: u64 = 1_000;
    let register_action = build_register_action(&cipherclerk, cell, name, owner, initial_expiry);
    let mut state_after_register = empty_state();
    state_after_register.fields[NAME_HASH_SLOT] =
        project_setfield(&register_action, NAME_HASH_SLOT).unwrap();
    state_after_register.fields[OWNER_HASH_SLOT] =
        project_setfield(&register_action, OWNER_HASH_SLOT).unwrap();
    state_after_register.fields[OWNER_PK_SLOT] =
        project_setfield(&register_action, OWNER_PK_SLOT).unwrap();
    state_after_register.fields[EXPIRY_SLOT] =
        project_setfield(&register_action, EXPIRY_SLOT).unwrap();
    state_after_register.set_nonce(1);
    program
        .evaluate(&state_after_register, Some(&empty_state()), None)
        .expect("register: passes WriteOnce(name)+Monotonic(expiry)+WriteOnce(revoked)");
    assert_eq!(state_after_register.fields[NAME_HASH_SLOT], name_hash(name));
    assert_eq!(
        state_after_register.fields[OWNER_PK_SLOT], owner,
        "register anchors the raw owner key as the authority register"
    );

    // ── Step 2: set-target (no slot caveat applies). ────────────────
    let target = resolve_target("dregg://cell/alices-document");
    let set_target_action = build_set_target_action(&cipherclerk, cell, name, target);
    let mut state_after_set_target = state_after_register.clone();
    state_after_set_target.fields[RESOLVE_TARGET_SLOT] =
        project_setfield(&set_target_action, RESOLVE_TARGET_SLOT).unwrap();
    state_after_set_target.set_nonce(2);
    program
        .evaluate(&state_after_set_target, Some(&state_after_register), None)
        .expect("set_target: no caveat applies; transition must succeed");
    assert_eq!(state_after_set_target.fields[RESOLVE_TARGET_SLOT], target);

    // ── Step 3: renew (extend expiry forward — Monotonic permits). ──
    let new_expiry: u64 = 5_000;
    let renew_action = build_renew_action(&cipherclerk, cell, name, new_expiry);
    let mut state_after_renew = state_after_set_target.clone();
    state_after_renew.fields[EXPIRY_SLOT] = project_setfield(&renew_action, EXPIRY_SLOT).unwrap();
    state_after_renew.set_nonce(3);
    program
        .evaluate(&state_after_renew, Some(&state_after_set_target), None)
        .expect("renew: Monotonic permits expiry extension");
    assert_eq!(
        state_after_renew.fields[EXPIRY_SLOT],
        expiry_field(new_expiry)
    );

    // ── Step 4: transfer (owner-image re-point + stage), SIGNED BY THE
    //    CURRENT OWNER — the owner-authorization caveats admit the move
    //    only when ctx.sender == the authority register. ───────────────
    let transfer_action = build_transfer_action(&cipherclerk, cell, name, owner, new_owner);
    let mut state_after_transfer = state_after_renew.clone();
    state_after_transfer.fields[OWNER_HASH_SLOT] =
        project_setfield(&transfer_action, OWNER_HASH_SLOT).unwrap();
    state_after_transfer.fields[PENDING_OWNER_PK_SLOT] =
        project_setfield(&transfer_action, PENDING_OWNER_PK_SLOT).unwrap();
    state_after_transfer.set_nonce(4);
    program
        .evaluate(
            &state_after_transfer,
            Some(&state_after_renew),
            Some(&ctx_with_sender(owner)),
        )
        .expect("transfer: the CURRENT owner may move the owner image + stage the handoff");

    // ── Step 4b: the incoming owner ACCEPTS — the authority register
    //    rotates to the staged key, signed by that key. ────────────────
    let accept_action = build_accept_transfer_action(&cipherclerk, cell, name, new_owner);
    let mut state_after_accept = state_after_transfer.clone();
    state_after_accept.fields[OWNER_PK_SLOT] =
        project_setfield(&accept_action, OWNER_PK_SLOT).unwrap();
    state_after_accept.set_nonce(5);
    program
        .evaluate(
            &state_after_accept,
            Some(&state_after_transfer),
            Some(&ctx_with_sender(new_owner)),
        )
        .expect("accept: the staged incoming owner may rotate the authority register");
    assert_eq!(state_after_accept.fields[OWNER_PK_SLOT], new_owner);

    // ── Step 5: revoke (REVOKED_SLOT zero → tombstone — WriteOnce permits). ──
    let revoke_action = build_revoke_action(&cipherclerk, cell, name);
    let mut state_after_revoke = state_after_accept.clone();
    state_after_revoke.fields[REVOKED_SLOT] =
        project_setfield(&revoke_action, REVOKED_SLOT).unwrap();
    state_after_revoke.set_nonce(6);
    program
        .evaluate(&state_after_revoke, Some(&state_after_accept), None)
        .expect("revoke: WriteOnce permits the first revocation");
    assert_eq!(
        state_after_revoke.fields[REVOKED_SLOT],
        revoked_tombstone(name)
    );
}

// =============================================================================
// Adversarial: duplicate-name registration
// =============================================================================

#[test]
fn adversarial_duplicate_name_registration_rejected_by_write_once() {
    let program = fresh_program();
    // Active "alice.dregg" on the cell.
    let mut old = empty_state();
    old.fields[NAME_HASH_SLOT] = name_hash("alice.dregg");
    old.fields[EXPIRY_SLOT] = expiry_field(1_000);
    old.set_nonce(1);
    // Attacker tries to repurpose the cell with a different name.
    let mut new = empty_state();
    new.fields[NAME_HASH_SLOT] = name_hash("eve.dregg");
    new.fields[EXPIRY_SLOT] = expiry_field(1_000);
    new.set_nonce(2);
    let err = program
        .evaluate(&new, Some(&old), None)
        .expect_err("duplicate name registration must be rejected");
    match err {
        ProgramError::ConstraintViolated {
            constraint: StateConstraint::WriteOnce { index },
            ..
        } => assert_eq!(index, NAME_HASH_SLOT as u8),
        other => panic!("expected WriteOnce on NAME_HASH_SLOT, got {other:?}"),
    }
}

// =============================================================================
// Adversarial: expiry decrement
// =============================================================================

#[test]
fn adversarial_expiry_decrement_rejected_by_monotonic() {
    let program = fresh_program();
    let mut old = empty_state();
    old.fields[NAME_HASH_SLOT] = name_hash("alice.dregg");
    old.fields[EXPIRY_SLOT] = expiry_field(10_000);
    old.set_nonce(1);
    // Attacker tries to shorten the rental.
    let mut new = old.clone();
    new.fields[EXPIRY_SLOT] = expiry_field(5_000);
    new.set_nonce(2);
    let err = program
        .evaluate(&new, Some(&old), None)
        .expect_err("expiry decrement must be rejected");
    match err {
        ProgramError::ConstraintViolated {
            constraint: StateConstraint::Monotonic { index },
            ..
        } => assert_eq!(index, EXPIRY_SLOT as u8),
        other => panic!("expected Monotonic on EXPIRY_SLOT, got {other:?}"),
    }
}

#[test]
fn adversarial_expiry_held_equal_is_permitted_by_monotonic() {
    // Monotonic permits `new == old`. A no-op renew (e.g., a paranoid
    // sweep where the executor re-emits the same expiry) must not be
    // rejected.
    let program = fresh_program();
    let mut old = empty_state();
    old.fields[NAME_HASH_SLOT] = name_hash("alice.dregg");
    old.fields[EXPIRY_SLOT] = expiry_field(10_000);
    old.set_nonce(1);
    let mut new = old.clone();
    new.set_nonce(2);
    program
        .evaluate(&new, Some(&old), None)
        .expect("no-op transition must pass all slot caveats");
}

// =============================================================================
// Adversarial: double revocation
// =============================================================================

#[test]
fn adversarial_double_revoke_rejected_by_write_once_on_revoked_slot() {
    let program = fresh_program();
    let mut old = empty_state();
    old.fields[NAME_HASH_SLOT] = name_hash("alice.dregg");
    old.fields[EXPIRY_SLOT] = expiry_field(10_000);
    old.fields[REVOKED_SLOT] = revoked_tombstone("alice.dregg");
    old.set_nonce(2);
    // Attacker tries to write a different tombstone (e.g., to pretend
    // a different name was revoked at this cell).
    let mut new = old.clone();
    new.fields[REVOKED_SLOT] = revoked_tombstone("eve.dregg");
    new.set_nonce(3);
    let err = program
        .evaluate(&new, Some(&old), None)
        .expect_err("second revocation must be rejected");
    match err {
        ProgramError::ConstraintViolated {
            constraint: StateConstraint::WriteOnce { index },
            ..
        } => assert_eq!(index, REVOKED_SLOT as u8),
        other => panic!("expected WriteOnce on REVOKED_SLOT, got {other:?}"),
    }
}

// =============================================================================
// Authorization: action carries a real Ed25519 signature (no [0u8;64])
// =============================================================================

#[test]
fn auth_register_action_carries_real_signature() {
    let cipherclerk = cclerk_with_seed(0xAA);
    let action = build_register_action(
        &cipherclerk,
        registry_cell(),
        "alice.dregg",
        [3u8; 32],
        1_000,
    );
    match action.authorization {
        Authorization::HybridSignature { ed25519, .. } => {
            assert!(
                ed25519 != [0u8; 64],
                "the framework signing path must not emit [0u8; 64] placeholders"
            );
        }
        other => panic!("expected HybridSignature variant, got {other:?}"),
    }
}

#[test]
fn auth_all_lifecycle_actions_carry_real_signatures() {
    // Every entry point must emit a hybrid-signed authorization.
    let cipherclerk = cclerk_with_seed(0xCC);
    let cell = registry_cell();
    let name = "alice.dregg";
    let actions = vec![
        (
            "register",
            build_register_action(&cipherclerk, cell, name, [3u8; 32], 1_000),
        ),
        ("renew", build_renew_action(&cipherclerk, cell, name, 5_000)),
        (
            "transfer",
            build_transfer_action(&cipherclerk, cell, name, [3u8; 32], [4u8; 32]),
        ),
        ("revoke", build_revoke_action(&cipherclerk, cell, name)),
        (
            "set_target",
            build_set_target_action(&cipherclerk, cell, name, resolve_target("dregg://cell/x")),
        ),
    ];
    for (name, action) in actions {
        match action.authorization {
            Authorization::HybridSignature { ed25519, .. } => assert!(
                ed25519 != [0u8; 64],
                "{name} action signature must be non-zero"
            ),
            other => panic!("expected HybridSignature for `{name}`, got {other:?}"),
        }
    }
}

#[test]
fn auth_different_cclerks_produce_different_signatures_on_same_logical_action() {
    // Same federation_id, different cipherclerks — signatures must diverge.
    let w1 = cclerk_with_seed(0x01);
    let w2 = cclerk_with_seed(0x01);
    let cell = registry_cell();
    let a1 = build_register_action(&w1, cell, "alice", [3u8; 32], 1_000);
    let a2 = build_register_action(&w2, cell, "alice", [3u8; 32], 1_000);
    let (
        Authorization::HybridSignature { ed25519: r1, .. },
        Authorization::HybridSignature { ed25519: r2, .. },
    ) = (&a1.authorization, &a2.authorization)
    else {
        panic!("expected HybridSignature variants");
    };
    assert_ne!(
        r1, r2,
        "different cipherclerks must produce different signatures even for identical action data"
    );
}

// =============================================================================
// Owner authorization: two-pole (owner admitted ∧ impostor refused)
// =============================================================================

/// Build the "alice.dregg is owned by `owner_pk`" baseline state the
/// owner-authorization tests transition from.
fn owned_state(name: &str, owner_pk: [u8; 32]) -> dregg_cell::state::CellState {
    let mut s = empty_state();
    s.fields[NAME_HASH_SLOT] = name_hash(name);
    s.fields[OWNER_HASH_SLOT] = *blake3::hash(&owner_pk).as_bytes();
    s.fields[OWNER_PK_SLOT] = owner_pk;
    s.fields[EXPIRY_SLOT] = expiry_field(5_000);
    s.set_nonce(1);
    s
}

/// **The impostor is REFUSED at the state-constraint layer.**
///
/// A non-owner attempting the same logical transfer produces a different
/// `Authorization::Signature` (pinned below), AND — since the
/// owner-authorization caveats landed on `name_factory_descriptor()` /
/// `name_cell_program()` — the projection of the impostor's action onto
/// the cell's post-state is REJECTED by `CellProgram::evaluate` itself:
/// past the first write, `OWNER_HASH_SLOT` moves only in a turn whose
/// executor-verified sender equals the authority register
/// (`OWNER_PK_SLOT`, frozen in the same turn). This inverts the old
/// "slot caveats are silent about *who* may write OWNER_HASH_SLOT"
/// documentation test: the write that used to PASS now REFUSES.
#[test]
fn adversarial_transfer_from_non_owner_authorization_diverges() {
    let owner_cclerk = cclerk_with_seed(0xA1);
    let impostor_cclerk = cclerk_with_seed(0xB2);
    let cell = registry_cell();
    let name = "alice.dregg";
    let old_owner_pk = [0xAAu8; 32];
    let new_owner_pk = [0xCCu8; 32];
    let impostor_pk = [0xEEu8; 32];

    // Both cipherclerks produce the *same* effect payload (the data the
    // executor would write into OWNER_HASH_SLOT is identical) — but the
    // `Authorization::Signature(r, s)` diverges because each cipherclerk's
    // Ed25519 key is distinct.
    let legit = build_transfer_action(&owner_cclerk, cell, name, old_owner_pk, new_owner_pk);
    let impostor = build_transfer_action(&impostor_cclerk, cell, name, old_owner_pk, new_owner_pk);

    let (
        Authorization::HybridSignature {
            ed25519: sig_owner, ..
        },
        Authorization::HybridSignature {
            ed25519: sig_imp, ..
        },
    ) = (&legit.authorization, &impostor.authorization)
    else {
        panic!("expected HybridSignature variants");
    };
    assert!(
        sig_owner != sig_imp,
        "non-owner's signature must diverge from the owner's"
    );

    // ...AND the projection of the impostor's action onto the cell's
    // post-state is REFUSED by the slot-caveat program: the sender
    // (the impostor's key) is not the authority register's key.
    let program = fresh_program();
    let old = owned_state(name, old_owner_pk);
    let mut new = old.clone();
    new.fields[OWNER_HASH_SLOT] = project_setfield(&impostor, OWNER_HASH_SLOT).unwrap();
    new.fields[PENDING_OWNER_PK_SLOT] = project_setfield(&impostor, PENDING_OWNER_PK_SLOT).unwrap();
    new.set_nonce(2);
    let err = program
        .evaluate(&new, Some(&old), Some(&ctx_with_sender(impostor_pk)))
        .expect_err("an impostor's owner-slot write MUST be refused by the cell program");
    // The AnyOf evaluator surfaces the decisive branch's violation: the
    // sender is not the identity held in the authority register.
    match err {
        ProgramError::ConstraintViolated {
            constraint: StateConstraint::SenderInSlot { index },
            ..
        } => assert_eq!(
            index, OWNER_PK_SLOT as u8,
            "the violated gate must be sender == authority register (OWNER_PK_SLOT)"
        ),
        other => panic!(
            "expected the owner-authorization SenderInSlot(OWNER_PK_SLOT) violation, got {other:?}"
        ),
    }

    // Fail-closed: with NO sender context at all (system/legacy caller),
    // the owner-slot write is refused too — never silently admitted.
    program
        .evaluate(&new, Some(&old), None)
        .expect_err("an owner-slot write without a sender context must fail closed");
}

/// **Completeness pole:** the LEGITIMATE current owner CAN still move the
/// owner field — the same transition the impostor is refused on is
/// admitted when the sender IS the authority register's key.
#[test]
fn owner_transfer_from_current_owner_is_admitted() {
    let owner_cclerk = cclerk_with_seed(0xA1);
    let cell = registry_cell();
    let name = "alice.dregg";
    let old_owner_pk = [0xAAu8; 32];
    let new_owner_pk = [0xCCu8; 32];

    let transfer = build_transfer_action(&owner_cclerk, cell, name, old_owner_pk, new_owner_pk);

    let program = fresh_program();
    let old = owned_state(name, old_owner_pk);
    let mut new = old.clone();
    new.fields[OWNER_HASH_SLOT] = project_setfield(&transfer, OWNER_HASH_SLOT).unwrap();
    new.fields[PENDING_OWNER_PK_SLOT] = project_setfield(&transfer, PENDING_OWNER_PK_SLOT).unwrap();
    new.set_nonce(2);
    program
        .evaluate(&new, Some(&old), Some(&ctx_with_sender(old_owner_pk)))
        .expect("the CURRENT owner's transfer (re-point + stage) must be admitted");
    assert_eq!(
        new.fields[PENDING_OWNER_PK_SLOT], new_owner_pk,
        "the transfer stages the incoming owner's raw key"
    );
}

/// **Authority follows ownership.** After the staged handoff is accepted,
/// the NEW owner is the one admitted on the next owner-field move and the
/// OLD owner is refused — `sender == current owner` tracks the live
/// owner, not the birth owner.
#[test]
fn owner_authority_follows_accepted_transfer() {
    let cell = registry_cell();
    let cclerk = cclerk_with_seed(0xA1);
    let name = "alice.dregg";
    let owner_a = [0xAAu8; 32];
    let owner_b = [0xBBu8; 32];
    let owner_c = [0xCCu8; 32];
    let program = fresh_program();

    // A stages the handoff to B (and re-points the image).
    let transfer_ab = build_transfer_action(&cclerk, cell, name, owner_a, owner_b);
    let s0 = owned_state(name, owner_a);
    let mut s1 = s0.clone();
    s1.fields[OWNER_HASH_SLOT] = project_setfield(&transfer_ab, OWNER_HASH_SLOT).unwrap();
    s1.fields[PENDING_OWNER_PK_SLOT] =
        project_setfield(&transfer_ab, PENDING_OWNER_PK_SLOT).unwrap();
    s1.set_nonce(2);
    program
        .evaluate(&s1, Some(&s0), Some(&ctx_with_sender(owner_a)))
        .expect("A (current owner) stages the handoff");

    // B accepts: the authority register rotates to the STAGED key,
    // signed by that key.
    let accept_b = build_accept_transfer_action(&cclerk, cell, name, owner_b);
    let mut s2 = s1.clone();
    s2.fields[OWNER_PK_SLOT] = project_setfield(&accept_b, OWNER_PK_SLOT).unwrap();
    s2.set_nonce(3);
    program
        .evaluate(&s2, Some(&s1), Some(&ctx_with_sender(owner_b)))
        .expect("B (the staged incoming owner) accepts the handoff");

    // An impostor cannot accept in B's place (not the staged key)...
    let mut seize = s1.clone();
    seize.fields[OWNER_PK_SLOT] = [0xEEu8; 32];
    seize.set_nonce(3);
    program
        .evaluate(&seize, Some(&s1), Some(&ctx_with_sender([0xEEu8; 32])))
        .expect_err("rotating the authority register to a non-staged key must be refused");

    // ...and A, having handed off, is REFUSED on the next owner move,
    // while B (the CURRENT owner) is admitted.
    let transfer_bc = build_transfer_action(&cclerk, cell, name, owner_b, owner_c);
    let mut s3 = s2.clone();
    s3.fields[OWNER_HASH_SLOT] = project_setfield(&transfer_bc, OWNER_HASH_SLOT).unwrap();
    s3.fields[PENDING_OWNER_PK_SLOT] =
        project_setfield(&transfer_bc, PENDING_OWNER_PK_SLOT).unwrap();
    s3.set_nonce(4);
    program
        .evaluate(&s3, Some(&s2), Some(&ctx_with_sender(owner_a)))
        .expect_err("the FORMER owner must be refused after the handoff");
    program
        .evaluate(&s3, Some(&s2), Some(&ctx_with_sender(owner_b)))
        .expect("the CURRENT owner (B) is admitted after the handoff");
}

/// **Anti-seizure:** an impostor cannot stage themselves, nor stage and
/// rotate atomically — the staged register is owner-written and frozen
/// during rotation.
#[test]
fn adversarial_staging_and_atomic_seizure_are_refused() {
    let name = "alice.dregg";
    let owner_pk = [0xAAu8; 32];
    let impostor_pk = [0xEEu8; 32];
    let program = fresh_program();
    let old = owned_state(name, owner_pk);

    // Impostor stages themselves.
    let mut stage = old.clone();
    stage.fields[PENDING_OWNER_PK_SLOT] = impostor_pk;
    stage.set_nonce(2);
    program
        .evaluate(&stage, Some(&old), Some(&ctx_with_sender(impostor_pk)))
        .expect_err("a non-owner staging the handoff register must be refused");

    // Impostor stages AND rotates in one turn (the atomic seizure).
    let mut seize = old.clone();
    seize.fields[PENDING_OWNER_PK_SLOT] = impostor_pk;
    seize.fields[OWNER_PK_SLOT] = impostor_pk;
    seize.set_nonce(2);
    program
        .evaluate(&seize, Some(&old), Some(&ctx_with_sender(impostor_pk)))
        .expect_err("an atomic stage-and-rotate seizure must be refused");

    // Impostor re-points the owner image directly (the original hole).
    let mut repoint = old.clone();
    repoint.fields[OWNER_HASH_SLOT] = *blake3::hash(&impostor_pk).as_bytes();
    repoint.set_nonce(2);
    program
        .evaluate(&repoint, Some(&old), Some(&ctx_with_sender(impostor_pk)))
        .expect_err("a non-owner's owner-image write must be refused");
}

// =============================================================================
// Factory descriptor stability
// =============================================================================

#[test]
fn factory_descriptors_publishes_exactly_one_factory_today() {
    let all = factory_descriptors();
    assert_eq!(
        all.len(),
        1,
        "today the nameservice publishes exactly the name factory; future expansions (dispute, registry) should update this assertion deliberately"
    );
    assert_eq!(all[0].factory_vk, NAME_FACTORY_VK);
}

#[test]
fn factory_descriptor_hash_is_deterministic_across_builds() {
    // The descriptor hash is the on-chain identity — two builds must
    // produce the same hash (no map iteration ordering, no rng,
    // no env-dependent fields).
    let h1 = name_factory_descriptor().hash();
    let h2 = name_factory_descriptor().hash();
    assert_eq!(h1, h2);
    assert_ne!(h1, [0u8; 32], "descriptor hash must not be zero");
}

#[test]
fn factory_descriptor_hash_changes_with_state_constraints() {
    // If a future commit adds or removes a slot caveat, the descriptor
    // hash *must* change — that is the constructor-transparency
    // guarantee. We exercise the property by building two descriptors:
    // the canonical one, and one with one fewer state constraint, and
    // checking they hash differently.
    let canonical = name_factory_descriptor();
    let mut weakened = canonical.clone();
    weakened.state_constraints.pop();
    assert_ne!(
        canonical.hash(),
        weakened.hash(),
        "dropping a state constraint must change the factory descriptor hash"
    );
}

#[test]
fn register_function_is_idempotent_across_repeated_calls() {
    let cipherclerk = cclerk_with_seed(0x42);
    let executor = dregg_app_framework::EmbeddedExecutor::new(&cipherclerk, "default");
    let ctx = dregg_app_framework::StarbridgeAppContext::new(cipherclerk, executor);
    let vk1 = register(&ctx);
    let vk2 = register(&ctx);
    let vk3 = register(&ctx);
    assert_eq!(vk1, vk2);
    assert_eq!(vk2, vk3);
    assert_eq!(
        ctx.factory_registry().len(),
        1,
        "repeated register() calls must not duplicate the factory entry"
    );
    // Inspectors: name, name-registry, name-register-form.
    assert_eq!(ctx.inspector_registry().len(), 3);
}
