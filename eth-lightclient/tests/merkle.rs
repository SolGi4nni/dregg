//! Committee-rotation Merkle-branch verification.
//!
//! A valid SSZ inclusion branch for `next_sync_committee` (generalized index 55,
//! depth 5, subtree index 23) against a finalized `state_root` must accept; any
//! tampered leaf / branch node / root must reject. The branch+root pair is a
//! self-consistent KAT: we pick the branch nodes and leaf, compute the root the
//! SSZ rule yields, then assert verification against that root — and that every
//! single-bit perturbation breaks it.

use eth_lightclient::ssz::{hash_pair, is_valid_merkle_branch};
use eth_lightclient::{
    verify_committee_update, SyncCommittee, NEXT_SYNC_COMMITTEE_DEPTH,
    NEXT_SYNC_COMMITTEE_DEPTH_ELECTRA, NEXT_SYNC_COMMITTEE_GINDEX,
    NEXT_SYNC_COMMITTEE_GINDEX_ELECTRA, NEXT_SYNC_COMMITTEE_SUBTREE_INDEX, SYNC_COMMITTEE_SIZE,
};

/// Reconstruct the root implied by (leaf, branch, index) — the constructive
/// inverse of `is_valid_merkle_branch`.
fn compute_root(leaf: &[u8; 32], branch: &[[u8; 32]], index: u64) -> [u8; 32] {
    let mut value = *leaf;
    for (i, node) in branch.iter().enumerate() {
        if (index >> i) & 1 == 1 {
            value = hash_pair(node, &value);
        } else {
            value = hash_pair(&value, node);
        }
    }
    value
}

fn sample_committee() -> SyncCommittee {
    // 512 distinct (structurally, not on-curve — the branch verify only hashes
    // bytes, it never deserializes points) pubkeys + an aggregate pubkey.
    let pubkeys: Vec<[u8; 48]> = (0..SYNC_COMMITTEE_SIZE)
        .map(|i| {
            let mut p = [0u8; 48];
            p[0] = (i & 0xff) as u8;
            p[1] = ((i >> 8) & 0xff) as u8;
            p
        })
        .collect();
    SyncCommittee {
        pubkeys,
        aggregate_pubkey: [0xAB; 48],
    }
}

fn sample_branch() -> Vec<[u8; 32]> {
    (0..NEXT_SYNC_COMMITTEE_DEPTH as u8)
        .map(|i| [i.wrapping_add(1); 32])
        .collect()
}

#[test]
fn valid_committee_branch_accepts() {
    let committee = sample_committee();
    let branch = sample_branch();
    let leaf = committee.hash_tree_root();
    let root = compute_root(&leaf, &branch, NEXT_SYNC_COMMITTEE_SUBTREE_INDEX);
    assert!(verify_committee_update(&committee, &branch, &root).is_ok());
}

#[test]
fn tampered_root_rejects() {
    let committee = sample_committee();
    let branch = sample_branch();
    let leaf = committee.hash_tree_root();
    let mut root = compute_root(&leaf, &branch, NEXT_SYNC_COMMITTEE_SUBTREE_INDEX);
    root[0] ^= 0x01;
    assert!(verify_committee_update(&committee, &branch, &root).is_err());
}

#[test]
fn tampered_branch_node_rejects() {
    let committee = sample_committee();
    let branch = sample_branch();
    let leaf = committee.hash_tree_root();
    let root = compute_root(&leaf, &branch, NEXT_SYNC_COMMITTEE_SUBTREE_INDEX);
    let mut bad = branch.clone();
    bad[2][5] ^= 0x80;
    assert!(verify_committee_update(&committee, &bad, &root).is_err());
}

#[test]
fn tampered_leaf_committee_rejects() {
    // A different next_sync_committee (different leaf) under the same branch/root.
    let committee = sample_committee();
    let branch = sample_branch();
    let leaf = committee.hash_tree_root();
    let root = compute_root(&leaf, &branch, NEXT_SYNC_COMMITTEE_SUBTREE_INDEX);

    let mut tampered = sample_committee();
    tampered.aggregate_pubkey[0] ^= 0x01;
    assert!(verify_committee_update(&tampered, &branch, &root).is_err());
}

#[test]
fn wrong_branch_length_rejects() {
    let committee = sample_committee();
    let branch = sample_branch();
    let leaf = committee.hash_tree_root();
    let root = compute_root(&leaf, &branch, NEXT_SYNC_COMMITTEE_SUBTREE_INDEX);
    let short = &branch[..NEXT_SYNC_COMMITTEE_DEPTH - 1];
    assert!(verify_committee_update(&committee, short, &root).is_err());
}

/// Electra+ deepened the `BeaconState`: `next_sync_committee` moved to gindex 87 →
/// depth 6, SAME subtree index 23. A 6-node branch must verify (ACCEPT polarity of
/// the post-Electra rotation path).
#[test]
fn electra_depth6_committee_branch_accepts() {
    let committee = sample_committee();
    let branch: Vec<[u8; 32]> = (0..NEXT_SYNC_COMMITTEE_DEPTH_ELECTRA as u8)
        .map(|i| [i.wrapping_add(0x40); 32])
        .collect();
    let leaf = committee.hash_tree_root();
    let root = compute_root(&leaf, &branch, NEXT_SYNC_COMMITTEE_SUBTREE_INDEX);
    assert!(
        verify_committee_update(&committee, &branch, &root).is_ok(),
        "a depth-6 Electra committee branch must verify"
    );
}

/// REJECT polarity for the Electra path: a tampered 6-node branch must not verify.
#[test]
fn electra_depth6_tampered_branch_rejects() {
    let committee = sample_committee();
    let branch: Vec<[u8; 32]> = (0..NEXT_SYNC_COMMITTEE_DEPTH_ELECTRA as u8)
        .map(|i| [i.wrapping_add(0x40); 32])
        .collect();
    let leaf = committee.hash_tree_root();
    let root = compute_root(&leaf, &branch, NEXT_SYNC_COMMITTEE_SUBTREE_INDEX);
    let mut bad = branch.clone();
    bad[5][0] ^= 0x01;
    assert!(verify_committee_update(&committee, &bad, &root).is_err());
}

/// Any branch length OTHER than the two fork depths (5 Altair..Deneb, 6 Electra+)
/// is fail-closed — including one deeper than Electra's.
#[test]
fn non_fork_branch_lengths_reject() {
    let committee = sample_committee();
    let leaf = committee.hash_tree_root();
    for depth in [0usize, 1, 4, 7, 8] {
        let branch: Vec<[u8; 32]> = (0..depth as u8).map(|i| [i.wrapping_add(1); 32]).collect();
        let root = compute_root(&leaf, &branch, NEXT_SYNC_COMMITTEE_SUBTREE_INDEX);
        assert!(
            verify_committee_update(&committee, &branch, &root).is_err(),
            "a depth-{depth} committee branch must be refused"
        );
    }
}

/// The load-bearing fork invariant: gindex 55 (depth 5) and gindex 87 (depth 6) walk
/// to the SAME subtree index 23, so one verifier serves both forks.
#[test]
fn subtree_index_invariant_across_fork() {
    assert_eq!(
        NEXT_SYNC_COMMITTEE_GINDEX % (1 << NEXT_SYNC_COMMITTEE_DEPTH),
        23
    );
    assert_eq!(
        NEXT_SYNC_COMMITTEE_GINDEX_ELECTRA % (1 << NEXT_SYNC_COMMITTEE_DEPTH_ELECTRA),
        23
    );
    assert_eq!(NEXT_SYNC_COMMITTEE_SUBTREE_INDEX, 23);
}

#[test]
fn generic_branch_wrong_index_rejects() {
    // The same nodes verified at the WRONG subtree index must not reconstruct
    // the root (left/right orientation flips).
    let committee = sample_committee();
    let branch = sample_branch();
    let leaf = committee.hash_tree_root();
    let root = compute_root(&leaf, &branch, NEXT_SYNC_COMMITTEE_SUBTREE_INDEX);
    assert!(!is_valid_merkle_branch(
        &leaf,
        &branch,
        NEXT_SYNC_COMMITTEE_SUBTREE_INDEX ^ 1,
        &root
    ));
}
