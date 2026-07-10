//! **VK-epoch nullifier-root FAITHFUL FILL — the Rust ghost mirrors the canonical Lean.**
//!
//! The R=24 rotated circuit binds the nullifier root as a FAITHFUL 8-felt group (limb 26 lane-0 ‖
//! completion limbs 67..=73). These integration tests prove the Rust producers now fill all 8 lanes
//! from a genuine `CanonicalHeapTree8` node8 root (closing the vacuous zero-fill of 67..73 and the
//! lossy 1-felt `hash_bytes` at limb 26), that the cell/turn twins agree byte-for-byte, that the
//! empty default is the NATIVE empty root (not `[0u8; 32]`), and that distinct nullifier frontiers
//! publish distinct committed roots (the cross-node anti-replay property).
//!
//! Lives as an INTEGRATION test (links the green `dregg-turn` lib + public API) so it runs
//! independently of unrelated in-flight breakage in the crate's `#[cfg(test)]` unit modules.

use dregg_cell::commitment::{V9RotationContext, compute_rotated_pre_limbs};
use dregg_cell::note::Nullifier;
use dregg_cell::nullifier_set::NullifierSet;
use dregg_cell::{Cell, Ledger};
use dregg_circuit::field::BabyBear;
use dregg_circuit::heap_root::{HeapLeaf, compute_canonical_heap_root_8, empty_heap_root_8};
use dregg_turn::rotation_witness::{
    cells_root, empty_nullifier_root_8, iroot, produce, root_felt, wire_commit_8,
};

/// (a)+(b) A non-empty nullifier accumulator root fills ALL 8 rotated lanes — limb 26 = root lane 0,
/// limbs 67..=73 = root lanes 1..7 (NON-ZERO, closing the vacuous zero-fill) — and the cell twin
/// (`compute_rotated_pre_limbs`) and turn twin (`produce`) write those 8 lanes BYTE-IDENTICALLY.
#[test]
fn nullifier_root_fills_all_8_lanes_and_twins_agree() {
    // A non-empty accumulator root (one spent nullifier leaf) — a genuine node8 tree root, the SAME
    // representation `NullifierSet::root8` yields for a live (nf, value) map.
    let nf_root = compute_canonical_heap_root_8(vec![HeapLeaf {
        addr: BabyBear::new(1_500_000_000),
        value: BabyBear::new(1),
    }]);
    assert!(
        nf_root.limbs()[1..8].iter().any(|f| *f != BabyBear::ZERO),
        "the test fixture must be a NON-empty (non-zero-completion) accumulator root"
    );

    let mut ledger = Ledger::new();
    let cell = Cell::with_balance([9u8; 32], [0u8; 32], 4242);
    ledger.insert_cell(cell.clone()).unwrap();
    let receipts: Vec<[u8; 32]> = vec![[1u8; 32], [2u8; 32]];

    // The turn twin (producer).
    let w = produce(
        &cell,
        &ledger,
        &nf_root,
        &dregg_turn::rotation_witness::empty_commitments_root_8(),
        &receipts,
        &Default::default(),
    );
    // The cell twin (commitment reconstruction) over the SAME turn-context.
    let ctx = V9RotationContext {
        cells_root: cells_root(&ledger),
        nullifier_root: nf_root,
        commitments_root: dregg_circuit::heap_root::empty_heap_root_8(),
        iroot: iroot(&receipts),
        material: Default::default(),
    };
    let pre_cell = compute_rotated_pre_limbs(&cell, &ctx);

    let lanes = [26usize, 67, 68, 69, 70, 71, 72, 73];
    for (i, &pos) in lanes.iter().enumerate() {
        assert_eq!(
            w.pre_limbs[pos],
            nf_root.limbs()[i],
            "turn producer limb {pos} must carry nullifier-root lane {i}"
        );
        assert_eq!(
            w.pre_limbs[pos], pre_cell[pos],
            "producer twins must write nullifier lane {i} (limb {pos}) byte-identically"
        );
    }
    // (a) The completion lanes 67..73 are NON-ZERO (the vacuity closure).
    assert!(
        (67..=73).any(|pos| w.pre_limbs[pos] != BabyBear::ZERO),
        "rotated nullifier completion limbs 67..73 must be NON-ZERO for a non-empty accumulator"
    );
}

/// (c) A non-spend turn commits the NATIVE empty default (`empty_heap_root_8`), NOT `[0u8; 32]`: the
/// empty-frontier fill writes limbs [26,67..73] as the native empty root's 8 felts, and limb 26
/// DIFFERS from the OLD lossy `root_felt(&[0u8; 32])` — the committed value genuinely SHIFTED.
#[test]
fn non_spend_turn_commits_native_empty_not_zero_bytes() {
    let empty = empty_nullifier_root_8();
    assert_eq!(
        empty,
        empty_heap_root_8(),
        "the empty default is the native CanonicalHeapTree8 empty root"
    );

    let mut ledger = Ledger::new();
    let cell = Cell::with_balance([3u8; 32], [0u8; 32], 100);
    ledger.insert_cell(cell.clone()).unwrap();
    let w = produce(
        &cell,
        &ledger,
        &empty,
        &dregg_turn::rotation_witness::empty_commitments_root_8(),
        &[[1u8; 32]],
        &Default::default(),
    );
    let lanes = [26usize, 67, 68, 69, 70, 71, 72, 73];
    for (i, &pos) in lanes.iter().enumerate() {
        assert_eq!(
            w.pre_limbs[pos],
            empty.limbs()[i],
            "empty-frontier limb {pos} must carry the native empty-root lane {i}"
        );
    }
    assert_ne!(
        w.pre_limbs[26],
        root_felt(&[0u8; 32]),
        "limb 26 must NOT be the OLD lossy hash_bytes([0u8;32]) — the committed value shifted"
    );
}

/// (d) CROSS-NODE ANTI-REPLAY: two DIFFERENT nullifier sets ⇒ DIFFERENT committed roots. The
/// executor's live `NullifierSet::root8()` frontier flows into the committed `nullifier_root`, so two
/// nodes whose (nf, value) frontiers differ publish DIFFERENT 8-felt turn commits.
#[test]
fn different_nullifier_sets_yield_different_committed_roots() {
    let mut set_a = NullifierSet::new();
    set_a.insert(Nullifier([7u8; 32]), 1_000).unwrap();
    let mut set_b = NullifierSet::new();
    set_b.insert(Nullifier([9u8; 32]), 2_000).unwrap();
    let root_a = set_a.root8();
    let root_b = set_b.root8();
    assert_ne!(
        root_a, root_b,
        "distinct nullifier frontiers must have distinct node8 roots"
    );

    let mut ledger = Ledger::new();
    let cell = Cell::with_balance([4u8; 32], [0u8; 32], 500);
    ledger.insert_cell(cell.clone()).unwrap();
    let receipts: Vec<[u8; 32]> = vec![[5u8; 32]];

    let commit = |root: &dregg_circuit::Faithful8| {
        let w = produce(
            &cell,
            &ledger,
            root,
            &dregg_turn::rotation_witness::empty_commitments_root_8(),
            &receipts,
            &Default::default(),
        );
        wire_commit_8(&w.pre_limbs, iroot(&receipts))
    };
    assert_ne!(
        commit(&root_a),
        commit(&root_b),
        "two executors with DIFFERENT nullifier frontiers must publish DIFFERENT committed roots"
    );
}
