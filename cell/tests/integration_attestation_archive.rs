//! Integration tests: receipt-chain archival and ArchivalAttestation.
//!
//! Exercises:
//! - archive with a valid attestation → lifecycle == Archived, cell remains live.
//! - checkpoint_hash in lifecycle matches attestation.checkpoint_hash().
//! - archive is rejected on a Sealed cell.
//! - archive is rejected on a Destroyed (terminal) cell.
//! - archive is rejected when attestation.cell_id mismatches.
//! - archive is rejected for non-monotone cutover (end_height <= current archived_through).
//! - archive is rejected when attestation fails structural validation (zero blob hash).
//! - archived cell still accepts effects.

use dregg_cell::{
    Cell, CellId, Ledger,
    lifecycle::{
        ArchivalAttestation, CellLifecycle, DeathCertificate, DeathReason, LifecycleTransitionError,
    },
};

fn make_cell(seed: u8) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(37);
    Cell::with_balance(pk, [0u8; 32], 1000)
}

fn valid_attestation(cell_id: CellId, start: u64, end: u64) -> ArchivalAttestation {
    ArchivalAttestation {
        cell_id,
        archive_start_height: start,
        archive_end_height: end,
        archive_blob_hash: [0xAAu8; 32],
        archive_terminal_commitment: [0xBBu8; 32],
        archive_terminal_receipt_hash: [0xCCu8; 32],
    }
}

// ---------------------------------------------------------------------------
// Test 1 (happy path): archive transitions to Archived; cell remains live.
// ---------------------------------------------------------------------------

#[test]
fn archive_transitions_to_archived_and_cell_remains_live() {
    let mut cell = make_cell(1);
    let cell_id = cell.id();
    let attest = valid_attestation(cell_id, 0, 100);
    let expected_checkpoint_hash = attest.checkpoint_hash();

    cell.archive(&attest)
        .expect("archive must succeed on a Live cell");

    assert!(!cell.lifecycle.is_terminal(), "Archived is not terminal");
    assert!(!cell.lifecycle.is_sealed(), "Archived is not sealed");
    assert!(
        cell.accepts_effects(),
        "Archived cell must still accept effects"
    );

    match &cell.lifecycle {
        CellLifecycle::Archived {
            checkpoint_hash,
            archived_through,
        } => {
            assert_eq!(
                *checkpoint_hash, expected_checkpoint_hash,
                "checkpoint_hash must equal attestation.checkpoint_hash()"
            );
            assert_eq!(
                *archived_through, 100,
                "archived_through must equal archive_end_height"
            );
        }
        other => panic!("expected Archived, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Test 2: checkpoint_hash binds all attestation fields.
// ---------------------------------------------------------------------------

#[test]
fn archival_checkpoint_hash_binds_all_fields() {
    let cell = make_cell(2);
    let cell_id = cell.id();
    let base = valid_attestation(cell_id, 0, 50);
    let base_hash = base.checkpoint_hash();

    let mut v = base.clone();
    v.archive_start_height = 1;
    assert_ne!(
        v.checkpoint_hash(),
        base_hash,
        "archive_start_height must bind"
    );

    let mut v = base.clone();
    v.archive_end_height = 51;
    assert_ne!(
        v.checkpoint_hash(),
        base_hash,
        "archive_end_height must bind"
    );

    let mut v = base.clone();
    v.archive_blob_hash = [0xFFu8; 32];
    assert_ne!(
        v.checkpoint_hash(),
        base_hash,
        "archive_blob_hash must bind"
    );

    let mut v = base.clone();
    v.archive_terminal_commitment = [0xFFu8; 32];
    assert_ne!(
        v.checkpoint_hash(),
        base_hash,
        "archive_terminal_commitment must bind"
    );

    let mut v = base.clone();
    v.archive_terminal_receipt_hash = [0xFFu8; 32];
    assert_ne!(
        v.checkpoint_hash(),
        base_hash,
        "archive_terminal_receipt_hash must bind"
    );

    let mut v = base.clone();
    v.cell_id = CellId::derive_raw(&[0xFFu8; 32], &[0u8; 32]);
    assert_ne!(v.checkpoint_hash(), base_hash, "cell_id must bind");
}

// ---------------------------------------------------------------------------
// Test 3 (adversarial): archive on a Sealed cell is rejected.
// ---------------------------------------------------------------------------

#[test]
fn archive_on_sealed_cell_rejected() {
    let mut cell = make_cell(3);
    let cell_id = cell.id();

    // Seal first.
    cell.seal([0xAA; 32], 10).unwrap();
    assert!(cell.lifecycle.is_sealed());

    let attest = valid_attestation(cell_id, 0, 50);
    let err = cell.archive(&attest).unwrap_err();
    assert_eq!(
        err,
        LifecycleTransitionError::SealedCannotArchive,
        "archive on a Sealed cell must return SealedCannotArchive"
    );
    // Still Sealed.
    assert!(cell.lifecycle.is_sealed());
}

// ---------------------------------------------------------------------------
// Test 4 (adversarial): archive on a Destroyed (terminal) cell is rejected.
// ---------------------------------------------------------------------------

#[test]
fn archive_on_destroyed_cell_rejected() {
    let mut cell = make_cell(4);
    let cell_id = cell.id();

    let cert = DeathCertificate {
        cell_id,
        last_receipt_hash: [1u8; 32],
        final_state_commitment: cell.state_commitment(),
        destroyed_at_height: 5,
        reason: DeathReason::Voluntary,
    };
    cell.destroy(&cert).unwrap();
    assert!(cell.lifecycle.is_terminal());

    let attest = valid_attestation(cell_id, 0, 50);
    let err = cell.archive(&attest).unwrap_err();
    assert_eq!(
        err,
        LifecycleTransitionError::Terminal,
        "archive on a Destroyed cell must return Terminal"
    );
}

// ---------------------------------------------------------------------------
// Test 5 (adversarial): archive with mismatched cell_id is rejected.
// ---------------------------------------------------------------------------

#[test]
fn archive_certificate_mismatch_rejected() {
    let mut cell = make_cell(5);

    let wrong_id = CellId::derive_raw(&[0xEEu8; 32], &[0u8; 32]);
    let attest = valid_attestation(wrong_id, 0, 50);

    let err = cell.archive(&attest).unwrap_err();
    assert_eq!(
        err,
        LifecycleTransitionError::CertificateMismatch,
        "archive with wrong cell_id must return CertificateMismatch"
    );
    assert_eq!(cell.lifecycle, CellLifecycle::Live);
}

// ---------------------------------------------------------------------------
// Test 6 (adversarial): non-monotone archive cutover is rejected.
// ---------------------------------------------------------------------------

#[test]
fn archive_non_monotone_cutover_rejected() {
    let mut cell = make_cell(6);
    let cell_id = cell.id();

    // First archive: end_height = 100.
    let first = valid_attestation(cell_id, 0, 100);
    cell.archive(&first).unwrap();

    // Try to archive with end_height = 50 (< 100): must be rejected.
    let second = valid_attestation(cell_id, 0, 50);
    let err = cell.archive(&second).unwrap_err();
    assert_eq!(
        err,
        LifecycleTransitionError::ArchiveNotMonotone,
        "archive with lower end_height must return ArchiveNotMonotone"
    );

    // archived_through is still 100.
    match &cell.lifecycle {
        CellLifecycle::Archived {
            archived_through, ..
        } => {
            assert_eq!(*archived_through, 100, "archived_through must not regress");
        }
        other => panic!("expected Archived, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Test 7 (adversarial): archive with zero blob hash is rejected (structural validation).
// ---------------------------------------------------------------------------

#[test]
fn archive_zero_blob_hash_rejected() {
    let mut cell = make_cell(7);
    let cell_id = cell.id();

    let bad_attest = ArchivalAttestation {
        cell_id,
        archive_start_height: 0,
        archive_end_height: 50,
        archive_blob_hash: [0u8; 32], // zero — invalid
        archive_terminal_commitment: [1u8; 32],
        archive_terminal_receipt_hash: [2u8; 32],
    };
    let err = cell.archive(&bad_attest).unwrap_err();
    assert!(
        matches!(err, LifecycleTransitionError::InvalidAttestation(_)),
        "zero archive_blob_hash must return InvalidAttestation; got {err:?}"
    );
    assert_eq!(cell.lifecycle, CellLifecycle::Live);
}

// ---------------------------------------------------------------------------
// Test 8 (happy path): Archived cell accepts effects; monotone re-archive extends cutover.
// ---------------------------------------------------------------------------

#[test]
fn archived_cell_accepts_effects_and_supports_extended_archive() {
    let mut cell = make_cell(8);
    let cell_id = cell.id();

    // First archive at height 100.
    let first = valid_attestation(cell_id, 0, 100);
    cell.archive(&first).unwrap();
    assert!(cell.accepts_effects(), "archived cell must accept effects");

    // Extend archive to height 200 (monotone).
    let second = ArchivalAttestation {
        cell_id,
        archive_start_height: 0,
        archive_end_height: 200,
        archive_blob_hash: [0xDDu8; 32],
        archive_terminal_commitment: [0xEEu8; 32],
        archive_terminal_receipt_hash: [0xFFu8; 32],
    };
    cell.archive(&second).unwrap();

    match &cell.lifecycle {
        CellLifecycle::Archived {
            archived_through, ..
        } => {
            assert_eq!(
                *archived_through, 200,
                "archived_through must advance to 200"
            );
        }
        other => panic!("expected Archived, got {other:?}"),
    }
    assert!(
        cell.accepts_effects(),
        "extended-archived cell must still accept effects"
    );
}

// ---------------------------------------------------------------------------
// Test 9: archive via Ledger::update_with is reflected in ledger state.
// ---------------------------------------------------------------------------

#[test]
fn archive_reflected_in_ledger_after_update_with() {
    let cell = make_cell(9);
    let cell_id = cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell).unwrap();

    let attest = valid_attestation(cell_id, 0, 75);
    let expected_checkpoint = attest.checkpoint_hash();

    ledger
        .update_with(&cell_id, |c| {
            c.archive(&attest).unwrap();
        })
        .expect("update_with must succeed for an archive transition");

    let cell = ledger.get(&cell_id).unwrap();
    match &cell.lifecycle {
        CellLifecycle::Archived {
            checkpoint_hash,
            archived_through,
        } => {
            assert_eq!(*checkpoint_hash, expected_checkpoint);
            assert_eq!(*archived_through, 75);
        }
        other => panic!("expected Archived in ledger, got {other:?}"),
    }
}
