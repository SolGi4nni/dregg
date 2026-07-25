//! **THE EXECUTOR CELLS TREE AND THE CIRCUIT ACCOUNTS TREE ARE DIFFERENT OBJECTS.**
//!
//! Named as a residual by the wound-#23 closure (`498d27a2b8`) and not created by it. This file is
//! the EXHIBIT: three facts, each asserted against the DEPLOYED constructions, no proving.
//!
//! ## The two objects, quoted
//!
//! **Executor side** — `dregg_turn::rotation_witness::cells_root` (the producer of
//! `V9RotationContext.cells_root`, which `compute_rotated_pre_limbs` writes into limb 0 ‖ 169..=175
//! and `state_commit::consensus_state_commitment` chip-chains into the receipt
//! `pre_state_hash`/`post_state_hash` the executor signs and the federation receipt QC aggregates):
//!
//! ```text
//! for (id, _) in ledger.iter() {
//!     entries.push(((BabyBear::new(CELLS_COLLECTION), hash_bytes(id.as_bytes())), BabyBear::ONE));
//! }
//! compute_canonical_heap_root_8_entries(&entries)
//!   // leaf = HeapLeaf::entry(heap_addr(CELLS_COLLECTION, hash_bytes(id)), 1)
//!   // tree = CanonicalHeapTree8::new(..)  — sort by addr, dedup, relink, sorted-compact rebuild
//! ```
//!
//! **Circuit side** — `dregg_circuit::effect_vm::trace_rotated::
//! generate_rotated_create_cell_trace_with_accounts_tree` (the limb-0 override the birth family's
//! `cellsFreshOp .absent` / `cellsInsertOp .aafiInsert` map-ops open against —
//! `EffectVmEmitRotationV3.{createCellV3,factoryV3,spawnV3}`):
//!
//! ```text
//! let cell_key   = trace[0][PARAM_BASE + key_col];              // = create_hash[0]
//! let before_tree = CanonicalHeapTree8::new(before_accounts.to_vec(), HEAP_TREE_DEPTH);
//! let aafi = before_tree.insert_witness_aafi(HeapLeaf::entry(cell_key, cell_key))?;
//! //  leaf = HeapLeaf::entry(cell_key, cell_key)  — the RAW param felt as its own addr AND value
//! //  after = append-at-free-index, NOT the sorted-compact rebuild
//! ```
//!
//! and every deployed caller passes `before_accounts = &[]`
//! (`sdk::cipherclerk` create/factory/spawn arms; `sdk::full_turn_proof`'s `spawn_dual_tree` arm).
//!
//! ## What the three tests establish
//!
//! 1. [`executor_cells_leaf_construction_is_the_deployed_one`] — the leaf construction quoted above
//!    IS `rotation_witness::cells_root` (so the rest of this file is not arguing against a
//!    reconstruction).
//! 2. [`circuit_accounts_limb_is_independent_of_the_executor_ledger`] — the limb-0 group the trace
//!    commits on a birth turn is the SAME felts for two ledgers whose `cells_root` DIFFER, and is
//!    not the producer's own committed `cells_root` group. The anchor's tree and the proof's tree
//!    are not the same object under two encodings; the proof's is a free-floating prover object.
//! 3. [`freshness_gate_admits_the_birth_of_an_ALREADY_PRESENT_cell`] — the `.absent` "no
//!    account-id collision" tooth admits a birth whose `CellId` is ALREADY in the ledger, both at
//!    the deployed `before_accounts = &[]` and when the executor's REAL cells-tree leaf set is
//!    threaded. The second half is the one that matters: the repair is NOT "thread the real leaf
//!    set", because the key domains do not align — `heap_addr(CELLS, hash_bytes(id))` vs the raw
//!    `create_hash[0]` param felt.

use dregg_cell::{Cell, CellId, Ledger};
use dregg_circuit::effect_vm::layout_generated::CELLS_ROOT_GROUP;
use dregg_circuit::effect_vm::trace_rotated::{
    AFTER_BASE, BEFORE_BASE, RotatedBlockWitness, empty_caveat_manifest,
    generate_rotated_create_cell_trace_with_accounts_tree,
};
use dregg_circuit::effect_vm::{CellState, Effect, bytes32_to_8_limbs};
use dregg_circuit::field::BabyBear;
use dregg_circuit::heap_root::{
    CanonicalHeapTree8, HEAP_TREE_DEPTH, HeapLeaf, compute_canonical_heap_root_8_entries, heap_addr,
};
use dregg_circuit::poseidon2::hash_bytes;
use dregg_turn::rotation_witness as rw;

/// The collection id present-cell existence leaves are keyed under — the value of the private
/// `rotation_witness::CELLS_COLLECTION`, pinned by
/// [`executor_cells_leaf_construction_is_the_deployed_one`].
const CELLS_COLLECTION: u32 = 0;

/// The token domain every cell here lives in.
const TOKEN: [u8; 32] = [0u8; 32];

/// The birth actor (the cell whose turn creates another).
const AGENT_PK: [u8; 32] = [7u8; 32];

/// The BORN cell's owner key.
const BORN_PK: [u8; 32] = [9u8; 32];

fn cell_from(pk: [u8; 32]) -> Cell {
    Cell::new(pk, TOKEN)
}

/// The executor's existence leaf for one present cell, spelled out from the deployed
/// `cells_root` body. Pinned against the real producer below.
fn executor_cells_leaves(ledger: &Ledger) -> Vec<HeapLeaf> {
    ledger
        .iter()
        .map(|(id, _)| {
            HeapLeaf::entry(
                heap_addr(BabyBear::new(CELLS_COLLECTION), hash_bytes(id.as_bytes())),
                BabyBear::ONE,
            )
        })
        .collect()
}

/// The VM `create_hash` the executor bridge folds for `Effect::CreateCell`
/// (`executor::effect_vm_bridge`: `BLAKE3(public_key ‖ token_id ‖ balance_le)` → 8 limbs). Its
/// limb 0 IS the circuit's accounts-tree key (`NEW_CELL_KEY_PARAM_COL = prmCol 0`).
fn create_hash(public_key: &[u8; 32], token_id: &[u8; 32], balance: u64) -> [BabyBear; 8] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(public_key);
    hasher.update(token_id);
    hasher.update(&balance.to_le_bytes());
    bytes32_to_8_limbs(hasher.finalize().as_bytes())
}

/// The producer witness pair for a birth turn over `ledger` (balance frozen, nonce ticks).
fn birth_witnesses(ledger: &Ledger) -> (RotatedBlockWitness, RotatedBlockWitness, Vec<BabyBear>) {
    let before_cell = cell_from(AGENT_PK);
    let mut after_cell = cell_from(AGENT_PK);
    let _ = after_cell.state.increment_nonce();
    let nullifier_root = rw::empty_nullifier_root_8();
    let commitments_root = rw::empty_commitments_root_8();
    let revoked_root = rw::empty_revoked_root_8();
    let receipts: Vec<[u8; 32]> = Vec::new();
    let bw = rw::produce(
        &before_cell,
        ledger,
        &nullifier_root,
        &commitments_root,
        &revoked_root,
        &receipts,
        &Default::default(),
    );
    let aw = rw::produce(
        &after_cell,
        ledger,
        &nullifier_root,
        &commitments_root,
        &revoked_root,
        &receipts,
        &Default::default(),
    );
    let producer_cells_group: Vec<BabyBear> =
        CELLS_ROOT_GROUP.iter().map(|&p| bw.pre_limbs[p]).collect();
    (
        RotatedBlockWitness::new(bw.pre_limbs.clone(), bw.iroot).expect("178 pre-iroot limbs"),
        RotatedBlockWitness::new(aw.pre_limbs, aw.iroot).expect("178 pre-iroot limbs"),
        producer_cells_group,
    )
}

/// Read the eight `cells_root` group felts out of one rotated block of a trace row.
fn trace_cells_group(row: &[BabyBear], base: usize) -> Vec<BabyBear> {
    CELLS_ROOT_GROUP.iter().map(|&p| row[base + p]).collect()
}

/// **THE QUOTE CHECK.** The leaf construction this file reasons about IS the deployed
/// `rotation_witness::cells_root`: `entry(heap_addr(CELLS_COLLECTION, hash_bytes(id)), 1)` folded
/// by `CanonicalHeapTree8`. Also pins `CELLS_COLLECTION == 0` (the constant is private).
#[test]
fn executor_cells_leaf_construction_is_the_deployed_one() {
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell_from(AGENT_PK)).unwrap();
    ledger.insert_cell(cell_from(BORN_PK)).unwrap();

    let rebuilt = CanonicalHeapTree8::new(executor_cells_leaves(&ledger), HEAP_TREE_DEPTH).root8();
    assert_eq!(
        rw::cells_root(&ledger).limbs(),
        rebuilt,
        "the executor's cells tree is entry(heap_addr(CELLS_COLLECTION=0, hash_bytes(id)), 1) \
         folded by CanonicalHeapTree8 — if this fails the quote in this file's header is stale"
    );

    // And the same value through the raw-entries helper the producer actually calls.
    let entries: Vec<((BabyBear, BabyBear), BabyBear)> = ledger
        .iter()
        .map(|(id, _)| {
            (
                (BabyBear::new(CELLS_COLLECTION), hash_bytes(id.as_bytes())),
                BabyBear::ONE,
            )
        })
        .collect();
    assert_eq!(
        rw::cells_root(&ledger).limbs(),
        compute_canonical_heap_root_8_entries(&entries).limbs(),
        "cells_root == compute_canonical_heap_root_8_entries over the existence entries"
    );
}

/// **THE DIVERGENCE, EXHIBITED.** On a birth turn the trace OVERWRITES the `cells_root` group with
/// the circuit's own accounts-tree roots. Those felts are a function of `(before_accounts, cell_key)`
/// ONLY — so two ledgers whose `cells_root` differ produce IDENTICAL committed limb-0 groups, and
/// neither equals the producer's own committed `cells_root` group. The anchor and `STATE_COMMIT`
/// are describing different trees.
#[test]
fn circuit_accounts_limb_is_independent_of_the_executor_ledger() {
    let key = create_hash(&BORN_PK, &TOKEN, 0);
    let effects = vec![Effect::CreateCell { create_hash: key }];
    let st = CellState::new(40_000, 0);
    let caveat = empty_caveat_manifest();

    // LEDGER A: the agent alone. LEDGER B: the agent plus one unrelated filler cell.
    let mut ledger_a = Ledger::new();
    ledger_a.insert_cell(cell_from(AGENT_PK)).unwrap();
    let mut ledger_b = Ledger::new();
    ledger_b.insert_cell(cell_from(AGENT_PK)).unwrap();
    ledger_b.insert_cell(cell_from([3u8; 32])).unwrap();

    assert_ne!(
        rw::cells_root(&ledger_a).limbs(),
        rw::cells_root(&ledger_b).limbs(),
        "anti-vacuity: the two ledgers must have DIFFERENT executor cells roots"
    );

    let mut committed: Vec<(Vec<BabyBear>, Vec<BabyBear>, Vec<BabyBear>)> = Vec::new();
    for ledger in [&ledger_a, &ledger_b] {
        let (before_w, after_w, producer_group) = birth_witnesses(ledger);
        // The DEPLOYED shape: every live caller passes an EMPTY before-accounts set.
        let (trace, _dpis, _heaps) = generate_rotated_create_cell_trace_with_accounts_tree(
            &st,
            &effects,
            &before_w,
            &after_w,
            &caveat,
            &[],
        )
        .expect("deployed birth wiring must produce a trace");
        committed.push((
            trace_cells_group(&trace[0], BEFORE_BASE),
            trace_cells_group(&trace[trace.len() - 1], AFTER_BASE),
            producer_group,
        ));
    }

    assert_eq!(
        committed[0].0, committed[1].0,
        "the trace's BEFORE cells_root group is the SAME for two different ledgers — it is \
         root8(before_accounts = []), not a view of any ledger"
    );
    assert_eq!(
        committed[0].1, committed[1].1,
        "the trace's AFTER cells_root group is the SAME for two different ledgers — it is \
         AAFI-insert(empty, entry(create_hash[0], create_hash[0])), a function of the birth \
         EFFECT alone"
    );
    assert_ne!(
        committed[0].0, committed[0].2,
        "the trace CLOBBERS the producer's committed cells_root group: the value the consensus \
         anchor chip-chains is NOT the value STATE_COMMIT absorbs on a birth turn"
    );

    // And the circuit's own AFTER root is not the executor's post-birth cells_root either.
    let mut ledger_a_post = ledger_a.clone();
    ledger_a_post.insert_cell(cell_from(BORN_PK)).unwrap();
    assert_ne!(
        committed[0].1,
        rw::cells_root(&ledger_a_post).limbs().to_vec(),
        "the proof's AFTER accounts root is not the executor's post-birth cells_root"
    );
}

/// **THE TOOTH THAT DOES NOT BITE.** `cellsFreshOp .absent` is documented (Lean
/// `EffectVmEmitRotationV3`) as "a re-creation of an existing cell id has no bracketing witness and
/// is UNSAT (no account-id collision)". It admits exactly that birth — at the deployed
/// `before_accounts = &[]` AND with the executor's real cells-tree leaf set threaded, because the
/// key domains do not align. The correspondence cannot be repaired by passing the right leaves.
#[test]
fn freshness_gate_admits_the_birth_of_an_already_present_cell() {
    // The born cell is ALREADY in the ledger; the executor itself refuses a second creation.
    let born_id = CellId::derive_raw(&BORN_PK, &TOKEN);
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell_from(AGENT_PK)).unwrap();
    ledger.insert_cell(cell_from(BORN_PK)).unwrap();
    assert!(ledger.get(&born_id).is_some(), "the born id IS present");
    assert!(
        ledger.insert_cell(cell_from(BORN_PK)).is_err(),
        "the EXECUTOR refuses a re-creation (CellAlreadyExists) — this is the fact the in-circuit \
         `.absent` tooth claims to mirror"
    );

    let key = create_hash(&BORN_PK, &TOKEN, 0);
    let effects = vec![Effect::CreateCell { create_hash: key }];
    let st = CellState::new(40_000, 0);
    let caveat = empty_caveat_manifest();
    let (before_w, after_w, _producer_group) = birth_witnesses(&ledger);

    // (a) THE DEPLOYED SHAPE: `.absent` against the empty tree. Trivially satisfied.
    generate_rotated_create_cell_trace_with_accounts_tree(
        &st,
        &effects,
        &before_w,
        &after_w,
        &caveat,
        &[],
    )
    .expect(
        "the deployed birth wiring accepts a re-creation of a PRESENT cell: `.absent` is opened \
         against the EMPTY prover-chosen accounts tree, not the ledger",
    );

    // (b) THREADING THE REAL LEAF SET DOES NOT REPAIR IT. The executor's cells tree keys on
    //     `heap_addr(CELLS, hash_bytes(id))`; the gate's key is the raw `create_hash[0]` param
    //     felt. The present cell's leaf is invisible to `position_of(cell_key)`.
    let real_leaves = executor_cells_leaves(&ledger);
    let real_tree = CanonicalHeapTree8::new(real_leaves.clone(), HEAP_TREE_DEPTH);
    let executor_addr = heap_addr(
        BabyBear::new(CELLS_COLLECTION),
        hash_bytes(born_id.as_bytes()),
    );
    assert!(
        real_tree.position_of(executor_addr).is_some(),
        "anti-vacuity: the present cell IS a member of the executor's cells tree at its own addr"
    );
    assert!(
        real_tree.position_of(key[0]).is_none(),
        "the SAME cell is a NON-member at the circuit's key `create_hash[0]` — different key \
         domains, so the `.absent` bracket cannot see the collision"
    );
    generate_rotated_create_cell_trace_with_accounts_tree(
        &st,
        &effects,
        &before_w,
        &after_w,
        &caveat,
        &real_leaves,
    )
    .expect(
        "even with the executor's REAL cells-tree leaf set threaded, the birth of an ALREADY \
         PRESENT cell is accepted — the encodings do not align, so 'thread the real leaves' is \
         not the repair",
    );

    // (c) THE OPPOSITE POLARITY — the tooth IS live. Put the collision in the gate's OWN key
    //     domain and the generator refuses. So (a)/(b) are an ENCODING miss, not a dead gate:
    //     `.absent` bites exactly when the before-tree is keyed the way the gate keys.
    let same_domain_leaves = vec![HeapLeaf::entry(key[0], key[0])];
    let refused = generate_rotated_create_cell_trace_with_accounts_tree(
        &st,
        &effects,
        &before_w,
        &after_w,
        &caveat,
        &same_domain_leaves,
    );
    assert!(
        refused.is_err(),
        "ANTI-VACUITY (opposite polarity): a before-accounts set carrying the SAME key the gate \
         inserts MUST be refused — the `.absent` tooth is live, and (a)/(b) miss only because the \
         executor's tree is keyed in a different domain"
    );
}
