//! Driven demonstration of GENESIS-FROM-SNAPSHOT.
//!
//! The hard gate: export a cell-set (cells + IVC history proofs + content
//! addresses + cross-epoch vouchers) → seed a FRESH genesis → the cells survive,
//! re-address IDENTICALLY, and their history validates; a TAMPERED export
//! (forged cell / broken proof) is REFUSED; a fresh genesis without the snapshot
//! is empty (the baseline WIPE).

use super::*;
use dregg_cell::Cell;

/// The OLD chain's federation id (committee epoch N).
fn old_fed() -> FederationId {
    [0xA1; 32]
}

/// The FRESH genesis's federation id (committee epoch N+1) — minted from new
/// committee keys, distinct from the old one.
fn new_fed() -> FederationId {
    [0xB2; 32]
}

/// A "character" cell: a hosted cell whose balance is the character's score and
/// whose state fields carry level / class. Its identity is content-addressed
/// from (public_key, token_id), independent of the chain hosting it.
fn character_cell() -> Cell {
    let public_key = [0x11; 32];
    let token_id = *b"the-descent:character:hero-0001\0"; // 32-byte token domain
    let mut cell = Cell::with_balance(public_key, token_id, 1337 /* score */);
    // level = 7, class = 3 (arbitrary character state).
    cell.state.fields[0] = {
        let mut f = [0u8; 32];
        f[0] = 7;
        f
    };
    cell.state.fields[1] = {
        let mut f = [0u8; 32];
        f[0] = 3;
        f
    };
    cell
}

/// A "universe" cell — a second carried object (a procgen seed + generation count).
fn universe_cell() -> Cell {
    let public_key = [0x22; 32];
    let token_id = *b"the-descent:universe:seed-000042"; // 32 bytes
    let mut cell = Cell::with_balance(public_key, token_id, 0);
    cell.state.fields[0] = {
        let mut f = [0u8; 32];
        f[0..8].copy_from_slice(&42u64.to_le_bytes()); // seed
        f
    };
    cell
}

/// A couple of modeled prior state commitments (the character's history).
fn prior_history() -> Vec<[u8; 32]> {
    vec![[0x33; 32], [0x44; 32], [0x55; 32]]
}

// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn honest_snapshot_survives_readdresses_and_verifies() {
    let cells = vec![
        (character_cell(), prior_history()),
        (universe_cell(), vec![[0x66; 32]]),
    ];

    // FREEZE + EXPORT from the old chain, targeting the fresh genesis.
    let snapshot = GenesisSnapshot::export(old_fed(), new_fed(), 4096, &cells)
        .expect("export builds a snapshot with IVC history proofs");
    assert_eq!(snapshot.entries.len(), 2);

    // Remember the exported content-addresses.
    let char_addr = character_cell().id();
    let uni_addr = universe_cell().id();

    // IMPORT / SEED a fresh genesis (new committee keys → new_fed()).
    let seeded = seed_genesis(&snapshot, new_fed()).expect("honest snapshot seeds cleanly");
    assert_eq!(seeded.new_federation_id, new_fed());
    assert_eq!(seeded.cells.len(), 2, "both cells survive the re-genesis");

    // RE-ADDRESS IDENTICALLY: each carried cell recomputes to the SAME content
    // address it had on the old chain, and to what a fresh derive would produce.
    let survived_char = &seeded.cells[0];
    assert_eq!(
        survived_char.id(),
        char_addr,
        "character re-addresses identically"
    );
    assert_eq!(recompute_content_address(survived_char), char_addr);
    assert_eq!(
        Cell::new(*survived_char.public_key(), *survived_char.token_id()).id(),
        char_addr,
        "a fresh derive in the new chain yields the identical address",
    );

    let survived_uni = &seeded.cells[1];
    assert_eq!(
        survived_uni.id(),
        uni_addr,
        "universe re-addresses identically"
    );

    // The carried character state is intact (score + level preserved).
    assert_eq!(survived_char.state.balance(), 1337);
    assert_eq!(survived_char.state.fields[0][0], 7);

    // History validates directly too (the IVC proof accepts against old genesis).
    for entry in &snapshot.entries {
        assert_eq!(
            verify_ivc(&entry.history, None),
            IvcVerification::Valid,
            "each carried cell's IVC history-from-old-genesis verifies",
        );
    }
}

#[test]
fn baseline_empty_snapshot_seeds_an_empty_genesis() {
    // A re-genesis with NOTHING to carry forward → an empty cell-set (today's
    // WIPE behaviour, recovered as the degenerate case).
    let empty = GenesisSnapshot::export(old_fed(), new_fed(), 0, &[]).unwrap();
    let seeded = seed_genesis(&empty, new_fed()).unwrap();
    assert!(seeded.cells.is_empty(), "no snapshot ⇒ empty fresh genesis");
}

#[test]
fn tampered_forged_cell_is_refused_but_honest_imports() {
    // Non-vacuity: the SAME snapshot imports honestly; only the forged copy is refused.
    let cells = vec![(character_cell(), prior_history())];
    let snapshot = GenesisSnapshot::export(old_fed(), new_fed(), 4096, &cells).unwrap();

    // Honest import succeeds.
    assert!(seed_genesis(&snapshot, new_fed()).is_ok());

    // Forge the carried cell: bump the character's level AFTER freeze. This
    // changes the cell's state_commitment, breaking the voucher binding (and the
    // IVC final-root binding).
    let mut forged = snapshot.clone();
    forged.entries[0].cell.state.fields[0][0] = 99; // level 7 → 99

    let err = seed_genesis(&forged, new_fed()).expect_err("a forged cell is refused");
    match err {
        ImportError::Entry {
            index: 0,
            kind: EntryReject::VoucherMismatch,
        } => {}
        other => panic!("expected VoucherMismatch on the forged cell, got {other:?}"),
    }
}

#[test]
fn tampered_forged_cell_trips_history_binding_when_voucher_is_also_forged() {
    // A more determined forger also rewrites the voucher's state_commitment to
    // match the forged cell (so the voucher check passes) — but the IVC history's
    // final root still binds the ORIGINAL state, so import is still refused.
    let cells = vec![(character_cell(), prior_history())];
    let snapshot = GenesisSnapshot::export(old_fed(), new_fed(), 4096, &cells).unwrap();

    let mut forged = snapshot.clone();
    forged.entries[0].cell.state.fields[0][0] = 99;
    // Re-point the voucher's state commitment at the forged cell so check (2) passes.
    let forged_sc = forged.entries[0].cell.state_commitment();
    forged.entries[0].voucher.state_commitment = forged_sc;

    let err = seed_genesis(&forged, new_fed()).expect_err("history binding still catches it");
    match err {
        ImportError::Entry {
            index: 0,
            kind: EntryReject::HistoryStateMismatch,
        } => {}
        other => panic!("expected HistoryStateMismatch, got {other:?}"),
    }
}

#[test]
fn tampered_broken_history_proof_is_refused() {
    let cells = vec![(character_cell(), prior_history())];
    let snapshot = GenesisSnapshot::export(old_fed(), new_fed(), 4096, &cells).unwrap();

    // Break the IVC history proof: flip the accumulated hash. verify_ivc's digest
    // binding no longer matches → the entry is refused.
    let mut forged = snapshot.clone();
    let acc = forged.entries[0].history.accumulated_hash;
    forged.entries[0].history.accumulated_hash =
        dregg_circuit::field::BabyBear::new(acc.0.wrapping_add(1));

    let err = seed_genesis(&forged, new_fed()).expect_err("a broken proof is refused");
    match err {
        ImportError::Entry {
            index: 0,
            kind: EntryReject::HistoryInvalid(_),
        } => {}
        other => panic!("expected HistoryInvalid, got {other:?}"),
    }
}

#[test]
fn snapshot_minted_for_a_different_epoch_is_refused() {
    let cells = vec![(character_cell(), prior_history())];
    let snapshot = GenesisSnapshot::export(old_fed(), new_fed(), 4096, &cells).unwrap();

    // Seeding a chain whose federation id is NOT the snapshot's target → refused.
    let wrong_fed = [0xCC; 32];
    assert_eq!(
        seed_genesis(&snapshot, wrong_fed),
        Err(ImportError::WrongDestination),
    );
}

#[test]
fn snapshot_round_trips_through_serde() {
    // The snapshot is meant to be written to a file the operator hands to the
    // fresh-genesis boot, so it must serialize and deserialize losslessly.
    let cells = vec![(character_cell(), prior_history())];
    let snapshot = GenesisSnapshot::export(old_fed(), new_fed(), 4096, &cells).unwrap();

    let json = serde_json::to_string(&snapshot).expect("serialize snapshot");
    let back: GenesisSnapshot = serde_json::from_str(&json).expect("deserialize snapshot");
    // GenesisSnapshot has no PartialEq (IvcProof lacks it), so compare the
    // canonical re-serialization instead.
    assert_eq!(
        json,
        serde_json::to_string(&back).expect("re-serialize"),
        "snapshot round-trips through serde losslessly",
    );

    // The deserialized snapshot still seeds and its cells still re-address identically.
    let seeded = seed_genesis(&back, new_fed()).expect("deserialized snapshot seeds");
    assert_eq!(seeded.cells[0].id(), character_cell().id());
}
