//! Tests on synthetic captures, built from the REAL system types:
//!
//!   * a clean blocklace → authenticated, no equivocation;
//!   * a blocklace with PLANTED equivocation → detected (real verifier);
//!   * a clean receipt chain → integrity verified;
//!   * a TAMPERED receipt chain → flagged at the break;
//!   * a conserving vs a non-conserving turn forest → attested by the real
//!     `dregg_userspace_verify`;
//!   * a clean WAL vs a torn one → crash-consistency invariants checked.

use ed25519_dalek::SigningKey;

use dregg_blocklace::finality::{Block, CheckpointData, Payload};
use dregg_persist::commit_log::CommitRecord;
use dregg_turn::TurnReceipt;

use crate::blocklace::BlocklaceCapture;
use crate::findings::Severity;
use crate::receipts::ReceiptStrandCapture;
use crate::wal::WalCapture;

// ─── helpers ─────────────────────────────────────────────────────────────────

fn key(b: u8) -> SigningKey {
    SigningKey::from_bytes(&[b; 32])
}

fn pk(b: u8) -> [u8; 32] {
    key(b).verifying_key().to_bytes()
}

/// Build a CheckpointData from a fully-built blocklace by serializing its blocks
/// (the same shape `persist` writes).
fn checkpoint_from_blocks(blocks: &[Block]) -> CheckpointData {
    CheckpointData {
        blocks: blocks.iter().map(|b| b.to_bytes()).collect(),
        tips: Default::default(),
        equivocators: Vec::new(),
        ordered_block_ids: Vec::new(),
        attested_block_ids: Vec::new(),
    }
}

// ─── blocklace: clean ──────────────────────────────────────────────────────────

#[test]
fn clean_blocklace_authenticates_and_has_no_equivocation() {
    // Three creators, a small honest causally-closed DAG. All blocks are
    // real-signed via `Block::new` (real Ed25519). Creator 1 chains seq 1→2 over
    // creators 2 and 3's genesis blocks (so the DAG has real causal edges).
    let g1 = Block::new(&key(1), 1, Payload::Data(b"a".to_vec()), vec![]);
    let b2 = Block::new(&key(2), 1, Payload::Data(b"b".to_vec()), vec![]);
    let b3 = Block::new(&key(3), 1, Payload::Data(b"c".to_vec()), vec![]);
    let top = Block::new(
        &key(1),
        2,
        Payload::Data(b"d".to_vec()),
        vec![g1.id(), b2.id(), b3.id()],
    );
    let all = vec![g1, b2, b3, top];

    let capture = BlocklaceCapture {
        checkpoint: checkpoint_from_blocks(&all),
        participants: vec![pk(1), pk(2), pk(3)],
        wavelength: None,
    };
    let report = crate::blocklace::analyze(&capture);

    assert!(report.is_clean(), "clean blocklace should have no critical finding: {:#?}", report.findings);
    assert!(report.findings.iter().any(|f| f.code == "blocklace.authenticated" && f.is_verified()));
    assert!(report.findings.iter().any(|f| f.code == "blocklace.no_equivocation" && f.is_verified()));
    assert!(report.verified_count() >= 2);
}

// ─── blocklace: planted equivocation ────────────────────────────────────────────

#[test]
fn planted_equivocation_is_detected_by_real_verifier() {
    // Creator 9 produces TWO causally-incomparable seq-1 blocks (a fork): both
    // reference the same genesis, neither observes the other.
    let g = Block::new(&key(1), 1, Payload::Data(b"genesis".to_vec()), vec![]);
    let gid = g.id();
    let fork_a = Block::new(&key(9), 1, Payload::Data(b"fork-a".to_vec()), vec![gid]);
    let fork_b = Block::new(&key(9), 1, Payload::Data(b"fork-b".to_vec()), vec![gid]);
    assert_ne!(fork_a.id(), fork_b.id());

    let blocks = vec![g, fork_a, fork_b];
    let capture = BlocklaceCapture {
        checkpoint: checkpoint_from_blocks(&blocks),
        participants: vec![pk(1), pk(9)],
        wavelength: None,
    };
    let report = crate::blocklace::analyze(&capture);

    let equiv = report
        .findings
        .iter()
        .find(|f| f.code == "blocklace.equivocation")
        .expect("equivocation must be detected");
    assert_eq!(equiv.severity, Severity::Critical);
    assert!(equiv.is_verified(), "equivocation finding must be attested by the real verifier");
    assert!(!report.is_clean());
}

#[test]
fn planted_equivocation_surfaces_the_concrete_fork_witness() {
    // Same planted fork as above, but assert the DEEPENED finding: the concrete
    // EquivocationProof witness pair (block_a ∥ block_b) recovered from the REAL
    // `detect_equivocation`.
    let g = Block::new(&key(1), 1, Payload::Data(b"genesis".to_vec()), vec![]);
    let gid = g.id();
    let fork_a = Block::new(&key(9), 1, Payload::Data(b"fork-a".to_vec()), vec![gid]);
    let fork_b = Block::new(&key(9), 1, Payload::Data(b"fork-b".to_vec()), vec![gid]);

    let blocks = vec![g, fork_a, fork_b];
    let capture = BlocklaceCapture {
        checkpoint: checkpoint_from_blocks(&blocks),
        participants: vec![pk(1), pk(9)],
        wavelength: None,
    };
    let report = crate::blocklace::analyze(&capture);

    let witness = report
        .findings
        .iter()
        .find(|f| f.code == "blocklace.equivocation_fork_witness")
        .expect("the concrete fork-witness pair must be surfaced");
    assert_eq!(witness.severity, Severity::Critical);
    assert!(witness.is_verified(), "the fork witness is attested by the real detect_equivocation");
    // The witness names two distinct conflicting block ids at the same seq.
    assert!(witness.message.contains("block_a") && witness.message.contains("block_b"));
    assert!(report.summary.iter().any(|(k, _)| k == "equivocation_forks"));
}

// ─── blocklace: forged signature rejected ───────────────────────────────────────

#[test]
fn forged_signature_capture_is_rejected_by_authenticating_loader() {
    // A block signed by key 2 but CLAIMING creator = pk(1): the real loader's
    // verify_signature rejects it.
    let mut forged = Block::new(&key(2), 1, Payload::Data(b"x".to_vec()), vec![]);
    forged.creator = pk(1); // lie about the creator; signature no longer matches

    let capture = BlocklaceCapture {
        checkpoint: checkpoint_from_blocks(&[forged]),
        participants: vec![pk(1)],
        wavelength: None,
    };
    let report = crate::blocklace::analyze(&capture);
    assert!(report.findings.iter().any(|f| f.code == "blocklace.authentication_failed" && f.is_verified()));
    assert!(!report.is_clean());
}

// ─── receipts: clean chain ──────────────────────────────────────────────────────

fn receipt(prev: Option<[u8; 32]>, pre: [u8; 32], post: [u8; 32], burn: bool) -> TurnReceipt {
    TurnReceipt {
        pre_state_hash: pre,
        post_state_hash: post,
        previous_receipt_hash: prev,
        was_burn: burn,
        computrons_used: 10,
        ..Default::default()
    }
}

fn clean_chain() -> Vec<TurnReceipt> {
    let r0 = receipt(None, [0u8; 32], [1u8; 32], false);
    let h0 = r0.receipt_hash();
    let r1 = receipt(Some(h0), [1u8; 32], [2u8; 32], false);
    let h1 = r1.receipt_hash();
    let r2 = receipt(Some(h1), [2u8; 32], [3u8; 32], false);
    vec![r0, r1, r2]
}

#[test]
fn clean_receipt_chain_integrity_verified() {
    let capture = ReceiptStrandCapture {
        receipts: clean_chain(),
        executor_keys: vec![],
    };
    let report = crate::receipts::analyze(&capture);
    assert!(report.is_clean(), "clean chain should pass: {:#?}", report.findings);
    assert!(report.findings.iter().any(|f| f.code == "receipts.chain_intact" && f.is_verified()));
    assert!(report.findings.iter().any(|f| f.code == "receipts.conservation_disclosed"));
}

#[test]
fn tampered_receipt_chain_is_flagged() {
    let mut chain = clean_chain();
    // Tamper receipt #1's post-state AFTER the chain was linked: its recomputed
    // hash changes, so receipt #2's previous_receipt_hash no longer matches.
    chain[1].post_state_hash = [0xFFu8; 32];

    let capture = ReceiptStrandCapture {
        receipts: chain,
        executor_keys: vec![],
    };
    let report = crate::receipts::analyze(&capture);
    let brk = report
        .findings
        .iter()
        .find(|f| f.code == "receipts.chain_break")
        .expect("tamper must break the chain");
    assert_eq!(brk.severity, Severity::Critical);
    assert!(brk.is_verified(), "chain-break is attested via the real receipt_hash");
    assert!(!report.is_clean());
}

#[test]
fn clean_chain_surfaces_the_receipt_link_graph() {
    // The deepened receipt-link-graph view is present on an intact chain and,
    // because the graph fields are bound into the v3 hash, it is ATTESTED.
    let capture = ReceiptStrandCapture {
        receipts: clean_chain(),
        executor_keys: vec![],
    };
    let report = crate::receipts::analyze(&capture);
    let graph = report
        .findings
        .iter()
        .find(|f| f.code == "receipts.link_graph")
        .expect("the receipt-link graph must be surfaced");
    assert!(graph.is_verified(), "on an intact chain the graph is bound (verified)");
    // Single-agent, single-federation, all-final clean strand.
    assert!(report.summary.iter().any(|(k, v)| k == "distinct_agents" && v == "1"));
    assert!(report.summary.iter().any(|(k, v)| k == "distinct_federations" && v == "1"));
    assert!(report.findings.iter().any(|f| f.code == "receipts.finality_all_final"));
}

#[test]
fn cross_federation_strand_is_flagged() {
    // A linear strand whose receipts carry two different federation_ids: the
    // deepened graph flags the cross-federation replay-domain stitch.
    let mut r0 = receipt(None, [0u8; 32], [1u8; 32], false);
    r0.federation_id = [0xAAu8; 32];
    let h0 = r0.receipt_hash();
    let mut r1 = receipt(Some(h0), [1u8; 32], [2u8; 32], false);
    r1.federation_id = [0xBBu8; 32]; // a DIFFERENT federation

    let capture = ReceiptStrandCapture {
        receipts: vec![r0, r1],
        executor_keys: vec![],
    };
    let report = crate::receipts::analyze(&capture);
    assert!(report.findings.iter().any(|f| f.code == "receipts.cross_federation_strand"));
    assert!(report.summary.iter().any(|(k, v)| k == "distinct_federations" && v == "2"));
    // Cross-federation is a NOTICE, not Critical — the chain itself is intact.
    assert!(report.is_clean());
}

#[test]
fn tentative_finality_receipts_are_surfaced() {
    use dregg_turn::Finality;
    let mut r0 = receipt(None, [0u8; 32], [1u8; 32], false);
    r0.finality = Finality::Tentative;
    let capture = ReceiptStrandCapture {
        receipts: vec![r0],
        executor_keys: vec![],
    };
    let report = crate::receipts::analyze(&capture);
    assert!(report.findings.iter().any(|f| f.code == "receipts.finality_tentative"));
    assert!(report.summary.iter().any(|(k, v)| k == "receipts_tentative" && v == "1"));
}

#[test]
fn burn_disclosure_surfaced_as_nonconservation() {
    let r0 = receipt(None, [0u8; 32], [1u8; 32], false);
    let h0 = r0.receipt_hash();
    let r1 = receipt(Some(h0), [1u8; 32], [2u8; 32], true); // was_burn = true
    let capture = ReceiptStrandCapture {
        receipts: vec![r0, r1],
        executor_keys: vec![],
    };
    let report = crate::receipts::analyze(&capture);
    // Chain still intact (burn is a disclosed, bound bit), but a burn notice fires.
    assert!(report.findings.iter().any(|f| f.code == "receipts.chain_intact"));
    assert!(report.findings.iter().any(|f| f.code == "receipts.burn_disclosed"));
}

// ─── receipts: executor signature ───────────────────────────────────────────────

#[test]
fn executor_signature_verified_against_real_canonical_message() {
    use ed25519_dalek::Signer;
    let exec = key(42);
    let mut r0 = receipt(None, [0u8; 32], [1u8; 32], false);
    let msg = r0.canonical_executor_signed_message();
    r0.executor_signature = Some(exec.sign(&msg).to_bytes().to_vec());

    let capture = ReceiptStrandCapture {
        receipts: vec![r0],
        executor_keys: vec![exec.verifying_key().to_bytes()],
    };
    let report = crate::receipts::analyze(&capture);
    assert!(report.findings.iter().any(|f| f.code == "receipts.executor_sigs_ok" && f.is_verified()));
    assert!(report.is_clean());
}

#[test]
fn forged_executor_signature_is_flagged() {
    use ed25519_dalek::Signer;
    let exec = key(42);
    let wrong = key(7);
    let mut r0 = receipt(None, [0u8; 32], [1u8; 32], false);
    let msg = r0.canonical_executor_signed_message();
    // Signed by `wrong`, but we only supply `exec`'s key: verification fails.
    r0.executor_signature = Some(wrong.sign(&msg).to_bytes().to_vec());

    let capture = ReceiptStrandCapture {
        receipts: vec![r0],
        executor_keys: vec![exec.verifying_key().to_bytes()],
    };
    let report = crate::receipts::analyze(&capture);
    assert!(report.findings.iter().any(|f| f.code == "receipts.executor_sig_invalid" && f.is_verified()));
    assert!(!report.is_clean());
}

// ─── forest: conservation attested by the real verifier ─────────────────────────

#[test]
fn conserving_forest_is_attested() {
    use dregg_turn::action::{Action, Authorization, DelegationMode, Effect};
    use dregg_turn::{CallForest, CallTree};
    use dregg_types::CellId;

    fn cell(n: u8) -> CellId {
        let mut b = [0u8; 32];
        b[0] = n;
        CellId(b)
    }
    fn act(target: CellId, effects: Vec<Effect>) -> Action {
        Action {
            target,
            method: [0u8; 32],
            args: Vec::new(),
            authorization: Authorization::Signature([1u8; 32], [2u8; 32]),
            preconditions: Default::default(),
            effects,
            may_delegate: DelegationMode::None,
            commitment_mode: Default::default(),
            balance_change: None,
            witness_blobs: vec![],
        }
    }
    let forest = CallForest {
        roots: vec![CallTree::new(act(cell(1), vec![Effect::Transfer { from: cell(1), to: cell(2), amount: 100 }]))],
        forest_hash: [0u8; 32],
    };
    let report = crate::forest::analyze(&crate::forest::ForestCapture { forest, treat_as_ring: false });
    assert!(report.is_clean(), "conserving forest should pass: {:#?}", report.findings);
    assert!(report.findings.iter().any(|f| f.code == "forest.assured" && f.is_verified()));
}

#[test]
fn nonconserving_forest_is_flagged() {
    use dregg_turn::action::{Action, Authorization, DelegationMode, Effect};
    use dregg_turn::{CallForest, CallTree};
    use dregg_types::CellId;

    fn cell(n: u8) -> CellId {
        let mut b = [0u8; 32];
        b[0] = n;
        CellId(b)
    }
    let mut a = Action {
        target: cell(1),
        method: [0u8; 32],
        args: Vec::new(),
        authorization: Authorization::Signature([1u8; 32], [2u8; 32]),
        preconditions: Default::default(),
        effects: vec![Effect::IncrementNonce { cell: cell(1) }],
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    };
    a.balance_change = Some(50); // +50 with no offset: does not conserve.
    let forest = CallForest { roots: vec![CallTree::new(a)], forest_hash: [0u8; 32] };
    let report = crate::forest::analyze(&crate::forest::ForestCapture { forest, treat_as_ring: false });
    assert!(report.findings.iter().any(|f| f.code == "forest.check_fail" && f.is_verified()));
    assert!(!report.is_clean());
}

// ─── WAL: clean vs torn ──────────────────────────────────────────────────────────

fn commit_rec(ordinal: u64, height: u64, hwm: u64) -> CommitRecord {
    CommitRecord {
        ordinal,
        height,
        block_id: [ordinal as u8; 32],
        block_executed_up_to: hwm,
        turn_hash: [ordinal as u8; 32],
        creator: [1u8; 32],
        receipt_hash: [ordinal as u8; 32],
        ledger_root: [ordinal as u8; 32],
        touched_cells: Vec::new(),
    }
}

#[test]
fn clean_wal_passes_crash_consistency() {
    let records = vec![
        commit_rec(0, 1, 1),
        commit_rec(1, 2, 2),
        commit_rec(2, 3, 4),
    ];
    let capture = WalCapture { records, commit_cursor: Some(3) };
    let report = crate::wal::analyze(&capture);
    assert!(report.is_clean(), "clean WAL: {:#?}", report.findings);
    assert!(report.findings.iter().any(|f| f.code == "wal.ordinals_dense" && f.is_verified()));
    assert!(report.findings.iter().any(|f| f.code == "wal.cursor_consistent" && f.is_verified()));
    assert!(report.findings.iter().any(|f| f.code == "wal.hwm_monotone" && f.is_verified()));
}

#[test]
fn torn_cursor_wal_is_flagged() {
    // cursor claims 5 turns committed but only 3 records exist: torn cursor.
    let records = vec![commit_rec(0, 1, 1), commit_rec(1, 2, 2), commit_rec(2, 3, 3)];
    let capture = WalCapture { records, commit_cursor: Some(5) };
    let report = crate::wal::analyze(&capture);
    assert!(report.findings.iter().any(|f| f.code == "wal.cursor_torn" && f.is_verified()));
    assert!(!report.is_clean());
}

#[test]
fn ordinal_gap_wal_is_flagged() {
    // ordinals 0, 1, 3 (missing 2): not dense.
    let records = vec![commit_rec(0, 1, 1), commit_rec(1, 2, 2), commit_rec(3, 3, 3)];
    let capture = WalCapture { records, commit_cursor: Some(3) };
    let report = crate::wal::analyze(&capture);
    assert!(report.findings.iter().any(|f| f.code == "wal.ordinal_gap" && f.is_verified()));
    assert!(!report.is_clean());
}

#[test]
fn replay_set_surfaced_as_recovery_overlay() {
    // cursor below len: the tail is the replay set (a crash mid-batch).
    let records = vec![commit_rec(0, 1, 1), commit_rec(1, 2, 2), commit_rec(2, 3, 3)];
    let capture = WalCapture { records, commit_cursor: Some(1) };
    let report = crate::wal::analyze(&capture);
    assert!(report.findings.iter().any(|f| f.code == "wal.replay_pending"));
    // A pending-replay capture is NOT critical (it is an expected recovery state).
    assert!(report.is_clean());
    assert!(report.summary.iter().any(|(k, v)| k == "replay_turns" && v == "2"));
}

/// A commit record carrying explicit touched-cell snapshots and an explicit
/// ledger root (for the convergence-trail / root-stall overlay tests).
fn commit_rec_cells(
    ordinal: u64,
    height: u64,
    hwm: u64,
    ledger_root: [u8; 32],
    cells: Vec<dregg_cell::Cell>,
) -> CommitRecord {
    CommitRecord {
        ordinal,
        height,
        block_id: [ordinal as u8; 32],
        block_executed_up_to: hwm,
        turn_hash: [ordinal as u8; 32],
        creator: [1u8; 32],
        receipt_hash: [ordinal as u8; 32],
        ledger_root,
        touched_cells: cells,
    }
}

#[test]
fn replay_overlay_details_the_replayed_turns() {
    // The deepened replay overlay names the exact replayed turns + their cell
    // re-touch count.
    let one_cell = vec![dregg_cell::Cell::new([9u8; 32], [0u8; 32])];
    let records = vec![
        commit_rec_cells(0, 1, 1, [1u8; 32], vec![]),
        commit_rec_cells(1, 2, 2, [2u8; 32], one_cell.clone()),
        commit_rec_cells(2, 3, 3, [3u8; 32], one_cell),
    ];
    let capture = WalCapture { records, commit_cursor: Some(1) };
    let report = crate::wal::analyze(&capture);
    let overlay = report
        .findings
        .iter()
        .find(|f| f.code == "wal.replay_overlay")
        .expect("the replay overlay detail must be surfaced");
    // Two records replay (#1, #2), re-touching two cell snapshots.
    assert!(overlay.message.contains("#1") && overlay.message.contains("#2"));
    assert!(report.summary.iter().any(|(k, v)| k == "replay_touched_cells" && v == "2"));
}

#[test]
fn stagnant_ledger_root_with_touched_cells_is_flagged() {
    // A record that touched a cell yet left the ledger root UNCHANGED from its
    // predecessor: a mutation that did not advance the authenticated state.
    let one_cell = vec![dregg_cell::Cell::new([9u8; 32], [0u8; 32])];
    let records = vec![
        commit_rec_cells(0, 1, 1, [7u8; 32], vec![]),
        // same root [7;32] as #0, but touches a cell → stall anomaly.
        commit_rec_cells(1, 2, 2, [7u8; 32], one_cell),
    ];
    let capture = WalCapture { records, commit_cursor: Some(2) };
    let report = crate::wal::analyze(&capture);
    let stall = report
        .findings
        .iter()
        .find(|f| f.code == "wal.root_stall")
        .expect("a stagnant-root mutation must be flagged");
    assert_eq!(stall.severity, Severity::Critical);
    assert!(stall.is_verified());
    assert!(!report.is_clean());
}

#[test]
fn coherent_ledger_root_trail_is_attested() {
    // Distinct advancing roots on every cell-touching turn → coherent trail.
    let one_cell = vec![dregg_cell::Cell::new([9u8; 32], [0u8; 32])];
    let records = vec![
        commit_rec_cells(0, 1, 1, [1u8; 32], one_cell.clone()),
        commit_rec_cells(1, 2, 2, [2u8; 32], one_cell),
    ];
    let capture = WalCapture { records, commit_cursor: Some(2) };
    let report = crate::wal::analyze(&capture);
    assert!(report.findings.iter().any(|f| f.code == "wal.root_trail_coherent" && f.is_verified()));
    assert!(report.summary.iter().any(|(k, v)| k == "distinct_ledger_roots" && v == "2"));
    assert!(report.is_clean());
}
