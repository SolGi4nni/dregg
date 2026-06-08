//! Integration tests for the two-step atomic cell migration handoff
//! (`cell/src/migration.rs` + `cell/src/ledger.rs::{migrate_prepare,
//! migrate_accept, migrate_commit}`).
//!
//! Two load-bearing properties:
//!   * **No double-existence** — at no instant do source and destination both hold a *live* copy;
//!     the source COMMIT tombstones the cell terminally, and the destination refuses a second
//!     install (the `DestinationOccupied` gate).
//!   * **Authority-conservation** — balance and capabilities are carried byte-for-byte; the
//!     voucher's bound `state_commitment` rejects any tampering en route.
//!
//! These live as an *integration* test (separate compilation unit) so they exercise the public
//! migration API exactly as a downstream caller (node / coordinator) would.

use dregg_cell::cell::{Cell, CellMode};
use dregg_cell::id::CellId;
use dregg_cell::ledger::Ledger;
use dregg_cell::lifecycle::CellLifecycle;
use dregg_cell::migration::{FederationId, MigrationError, MigrationReceipt, MigrationVoucher};
use dregg_cell::permissions::AuthRequired;

const FED_A: FederationId = [0xA1; 32];
const FED_B: FederationId = [0xB2; 32];

/// A funded hosted cell with a capability in its c-list (so authority-conservation has teeth).
fn funded_cell(seed: u8) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    let mut c = Cell::with_balance(pk, [0u8; 32], 1000);
    // Give it a capability so we can check the c-list carries across the move.
    let target = CellId::derive_raw(&[0xEE; 32], &[0u8; 32]);
    c.capabilities.grant(target, AuthRequired::None);
    c
}

/// Drive the full PREPARE -> ACCEPT -> COMMIT handoff between two ledgers and return both.
fn full_handoff(target_mode: CellMode) -> (Ledger, Ledger, CellId) {
    let mut src = Ledger::new();
    let mut dst = Ledger::new();
    let cell = funded_cell(7);
    let id = cell.id();
    let pre_commit = cell.state_commitment();
    src.insert_cell(cell.clone()).unwrap();

    // 1. PREPARE on source.
    let voucher = src
        .migrate_prepare(&id, FED_A, FED_B, target_mode.clone(), 10)
        .unwrap();
    assert_eq!(voucher.state_commitment, pre_commit);
    assert!(src.is_migration_locked(&id));

    // 2. ACCEPT on destination (carry the cell + voucher).
    let receipt = dst.migrate_accept(&voucher, cell, FED_B, 20).unwrap();
    assert_eq!(receipt.voucher_hash, voucher.voucher_hash());

    // 3. COMMIT on source.
    src.migrate_commit(&id, &receipt).unwrap();
    assert!(!src.is_migration_locked(&id));

    (src, dst, id)
}

#[test]
fn hosted_to_hosted_handoff_preserves_authority_and_no_double_existence() {
    let (src, dst, id) = full_handoff(CellMode::Hosted);

    // No double-existence: source cell is a terminal Migrated tombstone (rejects effects),
    // destination holds the unique LIVE copy.
    let src_cell = src.get(&id).expect("source keeps a tombstone");
    assert!(matches!(src_cell.lifecycle, CellLifecycle::Migrated { .. }));
    assert!(!src_cell.accepts_effects(), "tombstone must reject effects");

    let dst_cell = dst.get(&id).expect("destination holds the live cell");
    assert!(dst_cell.accepts_effects(), "destination copy is live");

    // Authority-conservation: balance and c-list carried byte-for-byte.
    assert_eq!(dst_cell.state.balance(), 1000);
    assert_eq!(dst_cell.capabilities.len(), 1);
    assert_eq!(dst_cell.mode, CellMode::Hosted);
}

#[test]
fn hosted_to_sovereign_handoff_registers_only_commitment() {
    let cell = funded_cell(3);
    let id = cell.id();
    let commit = cell.state_commitment();
    let mut src = Ledger::new();
    let mut dst = Ledger::new();
    src.insert_cell(cell.clone()).unwrap();

    let voucher = src
        .migrate_prepare(&id, FED_A, FED_B, CellMode::Sovereign, 1)
        .unwrap();
    dst.migrate_accept(&voucher, cell, FED_B, 2).unwrap();

    // Sovereign target: destination stores only the commitment, not the full state.
    assert!(dst.is_sovereign(&id));
    assert!(dst.get(&id).is_none());
    assert_eq!(dst.get_sovereign_commitment(&id), Some(&commit));
}

#[test]
fn double_accept_is_rejected_no_double_existence() {
    let cell = funded_cell(9);
    let id = cell.id();
    let mut src = Ledger::new();
    let mut dst = Ledger::new();
    src.insert_cell(cell.clone()).unwrap();
    let voucher = src
        .migrate_prepare(&id, FED_A, FED_B, CellMode::Hosted, 1)
        .unwrap();

    dst.migrate_accept(&voucher, cell.clone(), FED_B, 2).unwrap();
    // A SECOND accept of the same cell at the destination must be refused: this is the
    // no-double-existence gate (a replayed voucher cannot fork the cell).
    let err = dst.migrate_accept(&voucher, cell, FED_B, 3).unwrap_err();
    assert_eq!(err, MigrationError::DestinationOccupied(id));
    assert_eq!(dst.len(), 1, "still exactly one copy");
}

#[test]
fn tampered_state_in_transit_is_rejected() {
    let cell = funded_cell(4);
    let id = cell.id();
    let mut src = Ledger::new();
    let mut dst = Ledger::new();
    src.insert_cell(cell.clone()).unwrap();
    let voucher = src
        .migrate_prepare(&id, FED_A, FED_B, CellMode::Hosted, 1)
        .unwrap();

    // Adversary inflates the balance after PREPARE by minting a higher-balance cell with the same
    // identity — the commitment no longer matches the voucher.
    let mut pk = [0u8; 32];
    pk[0] = 4;
    let mut tampered = Cell::with_balance(pk, [0u8; 32], 999_999);
    let target = CellId::derive_raw(&[0xEE; 32], &[0u8; 32]);
    tampered.capabilities.grant(target, AuthRequired::None);
    assert_eq!(tampered.id(), id, "same identity, inflated authority");

    let err = dst.migrate_accept(&voucher, tampered, FED_B, 2).unwrap_err();
    assert_eq!(err, MigrationError::StateMismatch);
    assert!(dst.get(&id).is_none(), "tampered cell was not installed");
}

#[test]
fn voucher_for_other_federation_is_rejected() {
    let cell = funded_cell(5);
    let id = cell.id();
    let mut src = Ledger::new();
    let mut dst = Ledger::new();
    src.insert_cell(cell.clone()).unwrap();
    let voucher = src
        .migrate_prepare(&id, FED_A, FED_B, CellMode::Hosted, 1)
        .unwrap();

    // A federation that is NOT the addressed destination cannot accept the voucher.
    let wrong_fed: FederationId = [0xCC; 32];
    let err = dst.migrate_accept(&voucher, cell, wrong_fed, 2).unwrap_err();
    assert_eq!(err, MigrationError::WrongDestination);
}

#[test]
fn commit_with_forged_receipt_is_rejected() {
    let cell = funded_cell(6);
    let id = cell.id();
    let mut src = Ledger::new();
    let mut dst = Ledger::new();
    src.insert_cell(cell.clone()).unwrap();
    let voucher = src
        .migrate_prepare(&id, FED_A, FED_B, CellMode::Hosted, 1)
        .unwrap();
    let _ = dst.migrate_accept(&voucher, cell, FED_B, 2).unwrap();

    // A receipt that echoes the WRONG voucher hash must not finalize the source tombstone.
    let forged = MigrationReceipt {
        cell_id: id,
        voucher_hash: [0u8; 32],
        accepted_by: FED_B,
        accepted_at: 2,
    };
    let err = src.migrate_commit(&id, &forged).unwrap_err();
    assert_eq!(err, MigrationError::ReceiptMismatch);
    // Source cell is STILL live + STILL locked: COMMIT did not take effect.
    assert!(src.get(&id).unwrap().accepts_effects());
    assert!(src.is_migration_locked(&id));
}

#[test]
fn double_prepare_is_rejected() {
    let cell = funded_cell(8);
    let id = cell.id();
    let mut src = Ledger::new();
    src.insert_cell(cell).unwrap();
    src.migrate_prepare(&id, FED_A, FED_B, CellMode::Hosted, 1)
        .unwrap();
    // A cell can be in flight to at most one destination at a time.
    let err = src
        .migrate_prepare(&id, FED_A, FED_B, CellMode::Hosted, 2)
        .unwrap_err();
    assert_eq!(err, MigrationError::NotMigratable);
}

#[test]
fn migrated_cell_cannot_be_re_migrated() {
    let (mut src, _dst, id) = full_handoff(CellMode::Hosted);
    // The terminal tombstone cannot be PREPAREd again.
    let err = src
        .migrate_prepare(&id, FED_A, FED_B, CellMode::Hosted, 99)
        .unwrap_err();
    assert_eq!(err, MigrationError::NotMigratable);
}

#[test]
fn voucher_and_receipt_hashes_bind_every_field() {
    let base = MigrationVoucher {
        cell_id: CellId::derive_raw(&[1u8; 32], &[0u8; 32]),
        state_commitment: [2u8; 32],
        from: FED_A,
        to: FED_B,
        target_mode: CellMode::Hosted,
        prepared_at: 5,
    };
    let h = base.voucher_hash();

    let mut v = base.clone();
    v.state_commitment = [9u8; 32];
    assert_ne!(v.voucher_hash(), h, "state_commitment must bind");

    let mut v = base.clone();
    v.to = [9u8; 32];
    assert_ne!(v.voucher_hash(), h, "destination must bind");

    let mut v = base.clone();
    v.target_mode = CellMode::Sovereign;
    assert_ne!(v.voucher_hash(), h, "target_mode must bind");

    let r1 = MigrationReceipt {
        cell_id: base.cell_id,
        voucher_hash: h,
        accepted_by: FED_B,
        accepted_at: 7,
    };
    let mut r2 = r1.clone();
    r2.accepted_at = 8;
    assert_ne!(r1.attestation(), r2.attestation(), "accepted_at must bind");
}

/// Three-federation onward chain: A -> B -> C. The cell is live at exactly one federation at every
/// step, and balance is conserved across both hops. This is the n > 1 end-to-end check.
#[test]
fn onward_migration_chain_keeps_single_home_and_conserves_balance() {
    let mut led_a = Ledger::new();
    let mut led_b = Ledger::new();
    let mut led_c = Ledger::new();
    const FED_C: FederationId = [0xC3; 32];

    let cell = funded_cell(2);
    let id = cell.id();
    led_a.insert_cell(cell.clone()).unwrap();

    // Hop 1: A -> B.
    let v1 = led_a
        .migrate_prepare(&id, FED_A, FED_B, CellMode::Hosted, 1)
        .unwrap();
    let r1 = led_b.migrate_accept(&v1, cell, FED_B, 2).unwrap();
    led_a.migrate_commit(&id, &r1).unwrap();
    assert!(!led_a.get(&id).unwrap().accepts_effects());
    assert_eq!(led_b.get(&id).unwrap().state.balance(), 1000);

    // Hop 2: B -> C. Carry the now-live B cell onward.
    let b_cell = led_b.get(&id).unwrap().clone();
    let v2 = led_b
        .migrate_prepare(&id, FED_B, FED_C, CellMode::Hosted, 3)
        .unwrap();
    let r2 = led_c.migrate_accept(&v2, b_cell, FED_C, 4).unwrap();
    led_b.migrate_commit(&id, &r2).unwrap();

    // Single live home throughout: A tombstoned, B tombstoned, C live.
    assert!(!led_a.get(&id).unwrap().accepts_effects());
    assert!(!led_b.get(&id).unwrap().accepts_effects());
    assert!(led_c.get(&id).unwrap().accepts_effects());
    // Balance conserved across both hops.
    assert_eq!(led_c.get(&id).unwrap().state.balance(), 1000);
    assert_eq!(led_c.get(&id).unwrap().capabilities.len(), 1);
}
