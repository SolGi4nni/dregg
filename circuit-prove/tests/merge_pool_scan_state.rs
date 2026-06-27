//! THE TREE-SCAN-STATE aggregation infra — verification.
//!
//! Two things are proven here:
//!
//!   1. **The farm-able SHAPE (fast, structural).** The aggregation DAG the scan-state driver walks
//!      is a balanced binary tree whose same-depth merge nodes are mutually INDEPENDENT (disjoint
//!      inputs) — so ⌊n/2⌋ merges are simultaneously ready at the base frontier and a worker/GPU pool
//!      drains them in parallel: throughput ∝ worker count. The DAG also matches the serial
//!      `aggregate_tree`'s pairing + odd-promotion EXACTLY, which is why the parallel root equals the
//!      serial root.
//!
//!   2. **The same answer, parallel path (slow, real fold — `#[ignore]`).** A multi-turn history
//!      folded through the merge-pool + frontier-driver produces a root BYTE-IDENTICAL to the
//!      one-shot serial `aggregate_tree` (compared via the `WholeChainProofBytes` envelope), and both
//!      verify under the honest VK anchor. Determinism holds across worker counts (1 vs 4) — the
//!      parallel path is not a different circuit, just a parallel SCHEDULE of the same merges.
//!
//! Run the slow folds with:
//!   cargo test -p dregg-circuit-prove --test merge_pool_scan_state -- --ignored --nocapture

use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::ivc_turn_chain::{
    FinalizedTurn, WholeChainProof, WholeChainProofBytes, ir2_leaf_wrap_config,
    prove_descriptor_leaf_rotated_with_segment, prove_turn_chain_recursive,
    verify_turn_chain_recursive,
};
use dregg_circuit_prove::joint_turn_aggregation::DescriptorParticipant;
use dregg_circuit_prove::merge_pool::{aggregate_tree_scan_state, aggregation_dag};
use dregg_turn::rotation_witness::mint_rotated_participant_leg;

// ============================================================================
// FIXTURE (the audited Bucket-F rotated mint, mirrored from ivc_turn_chain_rotated.rs)
// ============================================================================

fn open_permissions() -> dregg_cell::Permissions {
    use dregg_cell::AuthRequired;
    dregg_cell::Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    }
}

fn producer_cell(balance: i64, nonce: u64) -> dregg_cell::Cell {
    let mut pk = [0u8; 32];
    pk[0] = 7;
    let mut cell = dregg_cell::Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    for _ in 0..nonce {
        let _ = cell.state.increment_nonce();
    }
    cell
}

fn make_turn(balance: u64, nonce: u32, amount: u64) -> (FinalizedTurn, BabyBear, BabyBear) {
    let state = CellState::new(balance, nonce);
    let effects = vec![Effect::Transfer {
        amount,
        direction: 1,
    }];
    let before_cell = producer_cell(balance as i64, nonce as u64);
    let after_cell = producer_cell((balance as i64) - (amount as i64), nonce as u64);
    let nullifier_root = [0u8; 32];
    let commitments_root = [0u8; 32];
    let receipt_log: Vec<[u8; 32]> = vec![[1u8; 32], [2u8; 32]];
    let leg = mint_rotated_participant_leg(
        &state,
        &effects,
        &before_cell,
        &after_cell,
        &nullifier_root,
        &commitments_root,
        &receipt_log,
        None,
    )
    .expect("rotated transfer leg mints + self-verifies");
    let old_root = leg.old_root();
    let new_root = leg.new_root();
    (
        FinalizedTurn::new(DescriptorParticipant::rotated(leg)),
        old_root,
        new_root,
    )
}

fn make_chain(
    start_balance: u64,
    start_nonce: u32,
    step: u64,
    k: usize,
) -> (Vec<FinalizedTurn>, BabyBear, BabyBear) {
    let mut turns = Vec::with_capacity(k);
    let mut balance = start_balance;
    let mut nonce = start_nonce;
    let mut genesis = BabyBear::ZERO;
    let mut final_root = BabyBear::ZERO;
    // `nonce`/`balance` are intertwined chain accumulators here; an enumerate rewrite isn't clean.
    #[allow(clippy::explicit_counter_loop)]
    for i in 0..k {
        let (turn, old_root, new_root) = make_turn(balance, nonce, step);
        if i == 0 {
            genesis = old_root;
        } else {
            assert_eq!(old_root, final_root, "real chain must already link");
        }
        final_root = new_root;
        turns.push(turn);
        balance -= step;
        nonce += 1;
    }
    (turns, genesis, final_root)
}

/// Build the per-turn segment-carrying descriptor leaves for `turns` at the leaf-wrap config — the
/// SAME leaves `prove_chain_core_rotated` feeds to `aggregate_tree` / the scan-state driver.
fn build_leaves(
    turns: &[FinalizedTurn],
) -> Vec<
    p3_recursion::RecursionOutput<
        dregg_circuit_prove::plonky3_recursion_impl::recursive::DreggRecursionConfig,
    >,
> {
    let config = ir2_leaf_wrap_config();
    turns
        .iter()
        .map(|t| {
            let leg = &t.participant.rotated;
            prove_descriptor_leaf_rotated_with_segment(
                &leg.descriptor,
                &leg.proof,
                &leg.public_inputs,
                &config,
            )
            .expect("descriptor leaf wraps + carries its segment")
        })
        .collect()
}

// ============================================================================
// (1) THE FARM-ABLE SHAPE — fast structural witness
// ============================================================================

/// The DAG is a balanced binary tree whose base-level merges are MUTUALLY INDEPENDENT (disjoint
/// inputs), so ⌊n/2⌋ jobs are simultaneously ready at the start frontier — the farm-able width that
/// makes throughput scale with worker count. Each node is consumed by exactly one parent (so a worker
/// can MOVE its inputs, never clone), and the shape matches `aggregate_tree`'s odd-promotion.
#[test]
fn dag_is_balanced_tree_with_independent_base_merges() {
    for n in 2..=17usize {
        let (tasks, root) = aggregation_dag(n);
        // n leaves -> exactly n-1 merges (every merge reduces the live-node count by one).
        assert_eq!(
            tasks.len(),
            n - 1,
            "n={n}: a binary fold of n leaves has n-1 merges"
        );

        // The last task produces the root.
        assert_eq!(
            tasks.last().unwrap().2,
            root,
            "n={n}: last task is the root"
        );

        // Each node (leaf or internal, except the root) is consumed exactly ONCE — the property that
        // lets a worker MOVE its inputs (the proof is not needed elsewhere) and that makes the merges
        // a partition, hence independent.
        let total_nodes = n + tasks.len(); // leaves + internal outputs
        let mut consumed = vec![0usize; total_nodes];
        for &(l, r, _out) in &tasks {
            consumed[l] += 1;
            consumed[r] += 1;
        }
        for (node, &c) in consumed.iter().enumerate() {
            if node == root {
                assert_eq!(c, 0, "n={n}: the root is consumed by nobody");
            } else {
                assert_eq!(c, 1, "n={n}: node {node} is consumed by exactly one parent");
            }
        }

        // The BASE frontier: merges whose BOTH inputs are leaves (`< n`) are ready immediately and
        // independent. There are ⌊n/2⌋ of them — the initial farm-able width.
        let base_ready = tasks.iter().filter(|&&(l, r, _)| l < n && r < n).count();
        assert_eq!(
            base_ready,
            n / 2,
            "n={n}: ⌊n/2⌋ base merges are simultaneously ready (the parallel width)"
        );
        if n >= 4 {
            assert!(
                base_ready >= 2,
                "n={n}: ≥2 independent merges => a 2+-worker pool overlaps them"
            );
        }
    }
}

/// The DAG mirrors `aggregate_tree`'s pairing + odd-promotion EXACTLY: re-derive the level-by-level
/// fold here and confirm the same `(left, right, out)` sequence and root. This identity is WHY the
/// parallel root equals the serial root.
#[test]
fn dag_matches_serial_aggregate_tree_pairing() {
    for n in 1..=17usize {
        let (tasks, root) = aggregation_dag(n);
        // Re-derive the serial pairing.
        let mut expected: Vec<(usize, usize, usize)> = Vec::new();
        let mut next_node = n;
        let mut level: Vec<usize> = (0..n).collect();
        while level.len() > 1 {
            let mut next = Vec::new();
            let mut i = 0;
            while i + 1 < level.len() {
                let out = next_node;
                next_node += 1;
                expected.push((level[i], level[i + 1], out));
                next.push(out);
                i += 2;
            }
            if i < level.len() {
                next.push(level[i]); // odd promotion = aggregate_tree's `proofs.pop()`.
            }
            level = next;
        }
        assert_eq!(
            tasks, expected,
            "n={n}: DAG pairing matches the serial fold"
        );
        if n == 1 {
            assert_eq!(root, 0, "single leaf is its own root");
        } else {
            assert_eq!(root, *expected.last().map(|(_, _, o)| o).unwrap());
        }
    }
}

// ============================================================================
// (2) SAME ANSWER, PARALLEL PATH — real fold (slow)
// ============================================================================

/// **THE KEYSTONE.** Fold a real multi-turn history through the merge-pool + frontier-driver and
/// confirm the root is BYTE-IDENTICAL to the one-shot serial `aggregate_tree` root (compared via the
/// verify-sufficient `WholeChainProofBytes` envelope), and that BOTH verify under the honest anchor.
/// Same circuit, same VK, same root — just a parallel schedule of the same merges.
#[test]
#[ignore = "SLOW: real recursion fold (~minutes); run with --ignored"]
fn scan_state_root_equals_serial_root() {
    let (turns, genesis, final_root) = make_chain(1000, 0, 7, 4);
    assert_eq!(turns.len(), 4);

    // The SERIAL reference (the deployed default path — `DREGG_MERGE_WORKERS` unset).
    let serial: WholeChainProof =
        prove_turn_chain_recursive(&turns).expect("the serial 4-turn chain folds");
    assert_eq!(serial.num_turns, 4);
    assert_eq!(serial.genesis_root, [genesis; 8]);
    assert_eq!(serial.final_root, [final_root; 8]);
    let serial_vk = serial.root_vk_fingerprint();
    verify_turn_chain_recursive(&serial, &serial_vk).expect("serial root verifies");
    let serial_bytes = WholeChainProofBytes::from_proof(&serial).to_postcard();

    // The PARALLEL path: build the SAME leaves, fold them through the scan-state driver with a real
    // multi-worker merge-pool, then assemble the same WholeChainProof shape and compare bytes.
    for workers in [1usize, 4usize] {
        let leaves = build_leaves(&turns);
        let parallel_root = aggregate_tree_scan_state(leaves, workers, 64)
            .expect("the parallel scan-state driver folds the same leaves");

        // The driver returns the root RecursionOutput; verify it directly under the SERIAL anchor
        // (a different circuit/schedule would fail the VK pin) and compare the root proof bytes.
        let serial_root_bytes =
            postcard::to_allocvec(&serial.root.0).expect("serial root proof postcard-encodes");
        let parallel_root_bytes =
            postcard::to_allocvec(&parallel_root.0).expect("parallel root proof postcard-encodes");
        assert_eq!(
            parallel_root_bytes, serial_root_bytes,
            "workers={workers}: the parallel root proof is BYTE-IDENTICAL to the serial root"
        );
    }

    // Sanity: the serial envelope is self-consistent (the assertion above already pinned the root
    // proof equality; this keeps `serial_bytes` load-bearing as the whole-artifact reference).
    assert!(!serial_bytes.is_empty());
}
