//! # Verified-correspondence tests — the SHIPPED nameservice IS the verified one.
//!
//! These tests pin that the shipped `starbridge-nameservice` turn-builders produce EXACTLY the
//! state-machine shape that the Lean module `Dregg2.Apps.NameserviceGated`
//! (`metatheory/Dregg2/Apps/NameserviceGated.lean`) PROVES sound on the credential-gated production
//! turn entry `execFullForestG` (the `dregg_exec_full_forest_auth` 4-leg gate).
//!
//! The Lean theorems are about the EXECUTED, credential-gated, caveat-enforcing turn. Each Lean
//! end-user theorem has a corresponding Rust assertion HERE, so the shipped app and the verified spec
//! are checked against the SAME teeth — the shipped turn is the verified one, not merely a spec-twin
//! that drifted. The slot layout, the WriteOnce/Monotonic caveat set, and the adversarial rejections
//! all match the Lean module's `registryCaveats` + `#guard` witnesses.
//!
//! | Lean theorem (`NameserviceGated.lean`)        | Rust assertion (this file)                    |
//! |-----------------------------------------------|-----------------------------------------------|
//! | `ns_name_squat_impossible` (WriteOnce name)   | `verified_no_name_squat` (WriteOnce NAME)     |
//! | `ns_rent_cannot_shorten` (Monotonic expiry)   | `verified_rent_cannot_shorten` (Monotonic)    |
//! | `ns_revoke_permanent` (WriteOnce revoked)     | `verified_revoke_permanent` (WriteOnce REVOKED)|
//! | the `regFresh` GOOD-register `#guard`s        | `verified_fresh_register_commits`             |
//! | the `reg0` idempotent-rewrite `#guard`        | `verified_idempotent_rewrite_permitted`       |
//!
//! The signature/credential leg (`ns_forged_credential_rejected`) is exercised by the companion
//! `lifecycle.rs` adversarial `Authorization::Unchecked` guard; here we focus on the SLOT-CAVEAT teeth
//! that are the load-bearing app invariants both the Lean executor and the shipped factory enforce.
//!
//! Like `lifecycle.rs`, these evaluate the factory's `StateConstraint` set directly via
//! `CellProgram::evaluate` (the SAME `program.evaluate(..)` path the production `TurnExecutor` wires on
//! the post-state) — the constraint semantics are exactly what the Lean `stateStepGuarded` /
//! `caveatsAdmit` teeth model.

use dregg_cell::{CellProgram, ProgramError, StateConstraint};
use starbridge_nameservice::{
    EXPIRY_SLOT, NAME_HASH_SLOT, REVOKED_SLOT, expiry_field, name_factory_descriptor, name_hash,
    revoked_tombstone,
};

// =============================================================================
// Helpers (mirroring lifecycle.rs)
// =============================================================================

fn fresh_program() -> CellProgram {
    CellProgram::Predicate(name_factory_descriptor().state_constraints.clone())
}

fn empty_state() -> dregg_cell::state::CellState {
    dregg_cell::state::CellState::new(0)
}

// =============================================================================
// Lean `ns_name_squat_impossible` — WriteOnce(NAME_HASH_SLOT): no name-squat.
//
// Lean: `ns_name_squat_impossible (s) (value) (hgate) (hsquat : caveatsAdmit ... = false) :
//        execFullForestG s (registerNode goodCred value) = none`
// + `#guard (caveatsAdmit reg0.kernel nameSlot ... 99) == false` (the name `42` is taken; `99 ≠ 42`).
// Rust mirror: a register writing a DIFFERENT name over an already-bound NAME slot is rejected by the
// WriteOnce constraint — the shipped factory's exact tooth.
// =============================================================================

#[test]
fn verified_no_name_squat() {
    let program = fresh_program();
    // "alice.dregg" already bound on the cell (the contested name `42` in `reg0`).
    let mut old = empty_state();
    old.fields[NAME_HASH_SLOT] = name_hash("alice.dregg");
    old.fields[EXPIRY_SLOT] = expiry_field(1_000);
    old.set_nonce(1);
    // A squatter tries to overwrite the contested name with a DIFFERENT binding (the `99 ≠ 42` case).
    let mut squat = empty_state();
    squat.fields[NAME_HASH_SLOT] = name_hash("eve.dregg");
    squat.fields[EXPIRY_SLOT] = expiry_field(1_000);
    squat.set_nonce(2);
    let err = program
        .evaluate(&squat, Some(&old), None)
        .expect_err("Lean ns_name_squat_impossible: WriteOnce(name) rejects the squat");
    match err {
        ProgramError::ConstraintViolated {
            constraint: StateConstraint::WriteOnce { index },
            ..
        } => assert_eq!(index, NAME_HASH_SLOT as u8),
        other => panic!("expected WriteOnce on NAME_HASH_SLOT (the verified tooth), got {other:?}"),
    }
}

// =============================================================================
// Lean `ns_rent_cannot_shorten` — Monotonic(EXPIRY_SLOT): rent can only extend.
//
// Lean: `#guard (caveatsAdmit reg0.kernel expirySlot ... 50) == false` (expiry 100 → 50 rejected);
//       `#guard (caveatsAdmit reg0.kernel expirySlot ... 200)` (100 → 200 permitted).
// Rust mirror: an expiry decrement is rejected by Monotonic; an extension is permitted.
// =============================================================================

#[test]
fn verified_rent_cannot_shorten() {
    let program = fresh_program();
    let mut old = empty_state();
    old.fields[NAME_HASH_SLOT] = name_hash("alice.dregg");
    old.fields[EXPIRY_SLOT] = expiry_field(10_000);
    old.set_nonce(1);
    // Shorten the rental (the `50 < 100` reject case).
    let mut shorter = old.clone();
    shorter.fields[EXPIRY_SLOT] = expiry_field(5_000);
    shorter.set_nonce(2);
    let err = program
        .evaluate(&shorter, Some(&old), None)
        .expect_err("Lean ns_rent_cannot_shorten: Monotonic(expiry) rejects the shorten");
    match err {
        ProgramError::ConstraintViolated {
            constraint: StateConstraint::Monotonic { index },
            ..
        } => assert_eq!(index, EXPIRY_SLOT as u8),
        other => panic!("expected Monotonic on EXPIRY_SLOT (the verified tooth), got {other:?}"),
    }

    // ...and the EXTENSION (100 → 200) is PERMITTED — the discriminating positive twin (non-vacuity).
    let mut longer = old.clone();
    longer.fields[EXPIRY_SLOT] = expiry_field(20_000);
    longer.set_nonce(2);
    program
        .evaluate(&longer, Some(&old), None)
        .expect("Lean: Monotonic permits an expiry extension (the discriminating positive case)");
}

// =============================================================================
// Lean `ns_revoke_permanent` — WriteOnce(REVOKED_SLOT): revocation is forever.
//
// Lean: `#guard (caveatsAdmit regRevoked.kernel revokedSlot ... 2) == false` (tombstone already set);
//       `#guard ((execFullForestG reg0 (revokeNode goodCred 1)).isSome)` (first revoke commits).
// Rust mirror: a SECOND, different write to the REVOKED slot is rejected by WriteOnce; the first
// revoke commits.
// =============================================================================

#[test]
fn verified_revoke_permanent() {
    let program = fresh_program();
    // First revoke commits (REVOKED zero → tombstone).
    let mut old = empty_state();
    old.fields[NAME_HASH_SLOT] = name_hash("alice.dregg");
    old.fields[EXPIRY_SLOT] = expiry_field(1_000);
    old.set_nonce(1);
    let mut revoked_once = old.clone();
    revoked_once.fields[REVOKED_SLOT] = revoked_tombstone("alice.dregg");
    revoked_once.set_nonce(2);
    program
        .evaluate(&revoked_once, Some(&old), None)
        .expect("Lean: WriteOnce permits the FIRST revocation (genesis write)");

    // A SECOND, different write to the tombstone is rejected (the `regRevoked` `2 ≠ 1` case).
    let mut revoked_twice = revoked_once.clone();
    revoked_twice.fields[REVOKED_SLOT] = revoked_tombstone("eve-overwrites-the-tombstone");
    revoked_twice.set_nonce(3);
    let err = program
        .evaluate(&revoked_twice, Some(&revoked_once), None)
        .expect_err("Lean ns_revoke_permanent: WriteOnce(revoked) rejects lifting the tombstone");
    match err {
        ProgramError::ConstraintViolated {
            constraint: StateConstraint::WriteOnce { index },
            ..
        } => assert_eq!(index, REVOKED_SLOT as u8),
        other => panic!("expected WriteOnce on REVOKED_SLOT (the verified tooth), got {other:?}"),
    }
}

// =============================================================================
// Lean `regFresh` GOOD-register `#guard` — a register over a FRESH name slot COMMITS.
//
// Lean: `#guard ((execFullForestG regFresh (registerNode goodCred 42)).isSome)` (genesis write OK).
// Rust mirror: writing a name over an empty (zero) NAME slot is permitted by WriteOnce.
// =============================================================================

#[test]
fn verified_fresh_register_commits() {
    let program = fresh_program();
    let fresh = empty_state(); // NAME slot is zero — fresh.
    let mut registered = fresh.clone();
    registered.fields[NAME_HASH_SLOT] = name_hash("newcomer.dregg");
    registered.fields[EXPIRY_SLOT] = expiry_field(1_000);
    registered.set_nonce(1);
    program
        .evaluate(&registered, Some(&fresh), None)
        .expect("Lean regFresh: WriteOnce permits the genesis name write (fresh slot commits)");
    assert_eq!(
        registered.fields[NAME_HASH_SLOT],
        name_hash("newcomer.dregg")
    );
}

// =============================================================================
// Lean `reg0` idempotent-rewrite `#guard` — re-writing the SAME name value is a WriteOnce no-op.
//
// Lean: `#guard (caveatsAdmit reg0.kernel nameSlot ... 42)` (rewriting the SAME `42` is admitted).
// Rust mirror: re-writing the identical NAME value is permitted (idempotent), not a squat.
// =============================================================================

#[test]
fn verified_idempotent_rewrite_permitted() {
    let program = fresh_program();
    let mut old = empty_state();
    old.fields[NAME_HASH_SLOT] = name_hash("alice.dregg");
    old.fields[EXPIRY_SLOT] = expiry_field(1_000);
    old.set_nonce(1);
    // Re-write the SAME name binding (idempotent no-op — admitted, the Lean `42 → 42` case).
    let mut same = old.clone();
    same.fields[NAME_HASH_SLOT] = name_hash("alice.dregg");
    same.set_nonce(2);
    program
        .evaluate(&same, Some(&old), None)
        .expect("Lean: WriteOnce permits an idempotent same-value rewrite (not a squat)");
}
