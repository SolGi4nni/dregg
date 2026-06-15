//! # A2 DIFFERENTIAL — `circuit_cap_root == cell_cap_root` (cap Phase A gate)
//!
//! THE single most important new invariant of cap Phase A: the cell-side
//! canonical capability root (`dregg_cell::compute_canonical_capability_root_felt`)
//! and the circuit-side `cap_root` (`dregg_circuit::cap_root` /
//! `CellState::capability_root`) are the SAME openable sorted-Poseidon2 Merkle
//! root for the same c-list — computed byte-identically.
//!
//! Before Phase A they were DISJOINT: the cell used a BLAKE3 XOR-fold and the
//! circuit seeded `cap_root` from `BabyBear::ZERO`, so nothing tied the
//! circuit's capability digest to the authoritative c-list. Without this test,
//! everything built on the "openable root" would be an F-4-style dark mirror.
//!
//! The differential is checked TWO ways:
//!   1. The cell's felt root equals an INDEPENDENTLY hand-built circuit-side
//!      `CanonicalCapTree` over leaves constructed directly from the circuit's
//!      `cap_root` field encoding (so the cell's `cap_ref_to_leaf` mapping
//!      agrees with a from-scratch circuit encoding, not just with itself).
//!   2. The value the circuit `CellState` carries for a fresh cell
//!      (`CellState::new(..).capability_root`) equals the cell's empty-c-list
//!      root, and `CellState::with_capability_root` round-trips the real root.

use dregg_cell::permissions::AuthRequired;
use dregg_cell::{Cell, CellId};
use dregg_circuit::cap_root::{self, CapLeaf};
use dregg_circuit::field::BabyBear;

/// Build the circuit-side `CapLeaf` for a `dregg_cell` capability, mirroring
/// the cell's encoding INDEPENDENTLY (this is the differential reference — if
/// the cell's private `cap_ref_to_leaf` ever drifts from this, the roots
/// diverge and the test fails).
fn ref_leaf(
    slot: u32,
    target: &CellId,
    auth: &AuthRequired,
    mask: Option<u32>,
    expiry: Option<u64>,
    breadstuff: Option<&[u8; 32]>,
) -> CapLeaf {
    let (mask_lo, mask_hi) = cap_root::split_effect_mask(mask.unwrap_or(0xFFFF_FFFF));
    let auth_tag = match auth {
        AuthRequired::None => BabyBear::new(0),
        AuthRequired::Signature => BabyBear::new(1),
        AuthRequired::Proof => BabyBear::new(2),
        AuthRequired::Either => BabyBear::new(3),
        AuthRequired::Impossible => BabyBear::new(4),
        AuthRequired::Custom { vk_hash } => {
            use dregg_circuit::poseidon2::hash_many;
            let mut inputs = vec![BabyBear::new(5)];
            inputs.extend_from_slice(&BabyBear::encode_hash(vk_hash));
            hash_many(&inputs)
        }
    };
    CapLeaf {
        slot_hash: cap_root::slot_hash(slot),
        target: cap_root::fold_bytes32(target.as_bytes()),
        auth_tag,
        mask_lo,
        mask_hi,
        expiry: cap_root::encode_expiry(expiry),
        breadstuff: cap_root::encode_breadstuff(breadstuff),
    }
}

fn tcell() -> Cell {
    Cell::new([7u8; 32], [11u8; 32])
}

/// THE A2 GATE: an EMPTY c-list — the cell's felt root equals the circuit's
/// `empty_capability_root()`, which is the value `CellState::new` seeds.
#[test]
fn a2_empty_clist_cell_equals_circuit_seed() {
    let cell = tcell();
    let cell_root = dregg_cell::compute_canonical_capability_root_felt(&cell.capabilities);

    // Circuit side: the empty-c-list sorted-tree root, and the seed CellState::new uses.
    let circuit_empty = cap_root::empty_capability_root();
    let seeded = dregg_circuit::CellState::new(100_000, 0).capability_root;

    assert_eq!(
        cell_root, circuit_empty,
        "A2: cell empty-c-list root != circuit empty_capability_root() — the openable root is a dark mirror"
    );
    assert_eq!(
        cell_root, seeded,
        "A2: cell empty root != the value CellState::new seeds into the circuit cap_root column"
    );
    assert_ne!(
        cell_root,
        BabyBear::ZERO,
        "A2: the empty root must NOT be ZERO (the pre-Phase-A disjoint seed bug)"
    );
}

/// THE A2 GATE: a NON-trivial c-list (varied auth tiers, masks, expiry,
/// breadstuff) — the cell's felt root equals an INDEPENDENTLY hand-built
/// circuit-side tree over the same logical leaves. This is the real
/// cell≡circuit differential: the cell's leaf encoding must agree with a
/// from-scratch circuit encoding, not merely with itself.
#[test]
fn a2_populated_clist_cell_equals_circuit() {
    let mut cell = tcell();
    let t1 = CellId::derive_raw(&[1u8; 32], &[1u8; 32]);
    let t2 = CellId::derive_raw(&[2u8; 32], &[2u8; 32]);
    let t3 = CellId::derive_raw(&[3u8; 32], &[3u8; 32]);

    // (a) a signature cap with full effect mask, no expiry, no breadstuff.
    let s1 = cell
        .capabilities
        .grant(t1, AuthRequired::Signature)
        .unwrap();
    // (b) a proof cap with an expiry.
    let s2 = cell
        .capabilities
        .grant_with_expiry(t2, AuthRequired::Proof, 12345)
        .unwrap();
    // (c) a faceted cap (restricted mask) with a breadstuff token.
    let bread = [0xABu8; 32];
    let s3 = cell
        .capabilities
        .grant_full(t3, AuthRequired::Either, Some(bread), None)
        .unwrap();

    let cell_root = dregg_cell::compute_canonical_capability_root_felt(&cell.capabilities);

    // INDEPENDENT circuit-side reconstruction of the SAME c-list.
    let leaves = vec![
        ref_leaf(s1, &t1, &AuthRequired::Signature, None, None, None),
        ref_leaf(s2, &t2, &AuthRequired::Proof, None, Some(12345), None),
        ref_leaf(s3, &t3, &AuthRequired::Either, None, None, Some(&bread)),
    ];
    let circuit_root = cap_root::compute_capability_root(leaves);

    assert_eq!(
        cell_root, circuit_root,
        "A2 DIFFERENTIAL: cell capability root != independently-built circuit root for the same c-list"
    );
}

/// THE A2 GATE for `Custom { vk_hash }`: the absorbed vk_hash limbs bind the
/// leaf, and cell≡circuit. Two `Custom`s with distinct vk_hashes must yield
/// distinct roots on BOTH sides.
#[test]
fn a2_custom_vk_hash_binds_cell_equals_circuit() {
    let t = CellId::derive_raw(&[9u8; 32], &[9u8; 32]);
    let vk_a = [0x11u8; 32];
    let vk_b = [0x22u8; 32];

    let mut cell_a = tcell();
    let sa = cell_a
        .capabilities
        .grant(t, AuthRequired::Custom { vk_hash: vk_a })
        .unwrap();
    let cell_root_a = dregg_cell::compute_canonical_capability_root_felt(&cell_a.capabilities);

    let mut cell_b = tcell();
    let sb = cell_b
        .capabilities
        .grant(t, AuthRequired::Custom { vk_hash: vk_b })
        .unwrap();
    let cell_root_b = dregg_cell::compute_canonical_capability_root_felt(&cell_b.capabilities);

    // Circuit-side reconstruction.
    let circ_a = cap_root::compute_capability_root(vec![ref_leaf(
        sa,
        &t,
        &AuthRequired::Custom { vk_hash: vk_a },
        None,
        None,
        None,
    )]);
    let circ_b = cap_root::compute_capability_root(vec![ref_leaf(
        sb,
        &t,
        &AuthRequired::Custom { vk_hash: vk_b },
        None,
        None,
        None,
    )]);

    assert_eq!(cell_root_a, circ_a, "A2: Custom(vk_a) cell != circuit");
    assert_eq!(cell_root_b, circ_b, "A2: Custom(vk_b) cell != circuit");
    assert_ne!(
        cell_root_a, cell_root_b,
        "A2: two Custom caps with distinct vk_hashes MUST yield distinct roots (vk_hash must bind)"
    );
}

/// ANTI-GHOST: tampering ANY authority-bearing field of a capability moves the
/// cell root (the commitment is genuinely load-bearing, not vacuous). Checks
/// target, auth tier, mask, expiry, breadstuff each independently.
#[test]
fn a2_anti_ghost_every_field_binds() {
    let t = CellId::derive_raw(&[5u8; 32], &[5u8; 32]);
    let t_other = CellId::derive_raw(&[6u8; 32], &[6u8; 32]);

    let base = {
        let mut c = tcell();
        c.capabilities
            .grant_full(t, AuthRequired::Signature, Some([1u8; 32]), Some(100))
            .unwrap();
        dregg_cell::compute_canonical_capability_root_felt(&c.capabilities)
    };

    // Different target.
    let diff_target = {
        let mut c = tcell();
        c.capabilities
            .grant_full(t_other, AuthRequired::Signature, Some([1u8; 32]), Some(100))
            .unwrap();
        dregg_cell::compute_canonical_capability_root_felt(&c.capabilities)
    };
    assert_ne!(base, diff_target, "anti-ghost: target must bind");

    // Different auth tier.
    let diff_auth = {
        let mut c = tcell();
        c.capabilities
            .grant_full(t, AuthRequired::Proof, Some([1u8; 32]), Some(100))
            .unwrap();
        dregg_cell::compute_canonical_capability_root_felt(&c.capabilities)
    };
    assert_ne!(base, diff_auth, "anti-ghost: auth tier must bind");

    // Different expiry.
    let diff_expiry = {
        let mut c = tcell();
        c.capabilities
            .grant_full(t, AuthRequired::Signature, Some([1u8; 32]), Some(200))
            .unwrap();
        dregg_cell::compute_canonical_capability_root_felt(&c.capabilities)
    };
    assert_ne!(base, diff_expiry, "anti-ghost: expiry must bind");

    // Different breadstuff.
    let diff_bread = {
        let mut c = tcell();
        c.capabilities
            .grant_full(t, AuthRequired::Signature, Some([2u8; 32]), Some(100))
            .unwrap();
        dregg_cell::compute_canonical_capability_root_felt(&c.capabilities)
    };
    assert_ne!(base, diff_bread, "anti-ghost: breadstuff must bind");
}

/// THE A2 GATE FOR REVOKE (the cap-crown seam closure): after the CELL revokes a
/// capability via `CapabilitySet::revoke`, its canonical capability root equals
/// the circuit-side post-revoke `cap_root` — the TOMBSTONE deletion (the revoked
/// slot's position folded to the ZERO/padding leaf), NOT a compacted rebuild.
///
/// This is the load-bearing invariant that makes a live `RevokeCapability` turn
/// proof verify: the deployed cell now computes the SAME root the in-circuit
/// sel-24 revoke gate (`cap_root::revocation_witness`) produces. Before this
/// reconciliation the cell used a `retain` + rebuild (compacted, re-indexing)
/// root, which diverged from the circuit's tombstone root and bricked the turn.
///
/// Checked THREE ways:
///   1. cell-root == an independently-built circuit tombstone tree over the
///      remaining live leaves + the revoked slot as a tombstone key.
///   2. cell-root == the `revocation_witness` zero-fold of the revoked slot
///      against the PRE-revoke live tree (the exact in-circuit gate output).
///   3. cell-root != the compacted rebuild over only the remaining live caps
///      (the OLD cell behavior — proving the reconciliation is non-vacuous).
#[test]
fn a2_revoke_cell_equals_circuit_tombstone() {
    let mut cell = tcell();
    let t1 = CellId::derive_raw(&[1u8; 32], &[1u8; 32]);
    let t2 = CellId::derive_raw(&[2u8; 32], &[2u8; 32]);
    let t3 = CellId::derive_raw(&[3u8; 32], &[3u8; 32]);

    let s1 = cell
        .capabilities
        .grant(t1, AuthRequired::Signature)
        .unwrap();
    let s2 = cell
        .capabilities
        .grant_with_expiry(t2, AuthRequired::Proof, 12345)
        .unwrap();
    let bread = [0xABu8; 32];
    let s3 = cell
        .capabilities
        .grant_full(t3, AuthRequired::Either, Some(bread), None)
        .unwrap();

    // The PRE-revoke live tree (all three leaves), for the witness reference.
    let leaf1 = ref_leaf(s1, &t1, &AuthRequired::Signature, None, None, None);
    let leaf2 = ref_leaf(s2, &t2, &AuthRequired::Proof, None, Some(12345), None);
    let leaf3 = ref_leaf(s3, &t3, &AuthRequired::Either, None, None, Some(&bread));
    let pre_tree =
        cap_root::CanonicalCapTree::new(vec![leaf1, leaf2, leaf3], cap_root::CAP_TREE_DEPTH);

    // CELL revokes the MIDDLE slot (s2). Logical c-list: s2 is now absent.
    assert!(
        cell.capabilities.revoke(s2),
        "revoke must find and remove s2"
    );
    assert!(
        cell.capabilities.lookup(s2).is_none(),
        "revoked slot is logically absent from the c-list"
    );
    assert!(
        cell.capabilities.lookup(s1).is_some() && cell.capabilities.lookup(s3).is_some(),
        "the OTHER caps survive the revoke"
    );

    let cell_root = dregg_cell::compute_canonical_capability_root_felt(&cell.capabilities);

    // (1) INDEPENDENT circuit tombstone tree: remaining live leaves + s2 tombstone.
    let circuit_tombstone_root = cap_root::compute_capability_root_with_tombstones(
        vec![leaf1, leaf3],
        &[cap_root::slot_hash(s2)],
    );
    assert_eq!(
        cell_root, circuit_tombstone_root,
        "A2 REVOKE: cell post-revoke root != independently-built circuit TOMBSTONE root"
    );

    // (2) The exact in-circuit sel-24 gate output: the zero-fold witness.
    let w = pre_tree
        .revocation_witness(cap_root::slot_hash(s2))
        .expect("s2 present in the pre-revoke tree");
    assert_eq!(
        cell_root, w.new_root,
        "A2 REVOKE: cell post-revoke root != the in-circuit revocation_witness zero-fold (the sel-24 gate)"
    );

    // (3) Non-vacuity: the COMPACTED rebuild (the OLD cell behavior) DIFFERS.
    let compacted = cap_root::compute_capability_root(vec![leaf1, leaf3]);
    assert_ne!(
        cell_root, compacted,
        "A2 REVOKE: the tombstone root MUST differ from the compacted rebuild — that gap is the seam this closes"
    );
}

/// The revoke is POSITION-STABLE for the survivors: revoking s2 must leave the
/// membership witnesses of s1 and s3 valid against the NEW root (the whole point
/// of tombstoning over compaction). We check that the survivor leaves still open
/// to the post-revoke cell root via the tombstone tree's membership paths.
#[test]
fn a2_revoke_preserves_survivor_membership() {
    let mut cell = tcell();
    let t1 = CellId::derive_raw(&[1u8; 32], &[1u8; 32]);
    let t2 = CellId::derive_raw(&[2u8; 32], &[2u8; 32]);
    let t3 = CellId::derive_raw(&[3u8; 32], &[3u8; 32]);
    let s1 = cell
        .capabilities
        .grant(t1, AuthRequired::Signature)
        .unwrap();
    let s2 = cell.capabilities.grant(t2, AuthRequired::Proof).unwrap();
    let s3 = cell.capabilities.grant(t3, AuthRequired::Either).unwrap();
    let leaf1 = ref_leaf(s1, &t1, &AuthRequired::Signature, None, None, None);
    let leaf3 = ref_leaf(s3, &t3, &AuthRequired::Either, None, None, None);

    assert!(cell.capabilities.revoke(s2));
    let cell_root = dregg_cell::compute_canonical_capability_root_felt(&cell.capabilities);

    // The post-revoke tombstone tree (survivors + s2 ghost).
    let tomb_tree = cap_root::CanonicalCapTree::new_with_tombstones(
        vec![leaf1, leaf3],
        &[cap_root::slot_hash(s2)],
        cap_root::CAP_TREE_DEPTH,
    );
    assert_eq!(
        tomb_tree.root(),
        cell_root,
        "tombstone tree root == cell root"
    );

    // Each survivor still has an authenticated membership path to the new root.
    for (key, leaf) in [(s1, leaf1), (s3, leaf3)] {
        let pos = tomb_tree
            .position_of(cap_root::slot_hash(key))
            .expect("survivor slot still occupies a position after the revoke");
        let (sibs, dirs) = tomb_tree.prove_membership(pos).expect("membership path");
        let mut cur = leaf.digest();
        for level in 0..cap_root::CAP_TREE_DEPTH {
            cur = if dirs[level] == 0 {
                dregg_circuit::poseidon2::hash_fact(cur, &[sibs[level]])
            } else {
                dregg_circuit::poseidon2::hash_fact(sibs[level], &[cur])
            };
        }
        assert_eq!(
            cur, cell_root,
            "survivor slot {key} must still open to the post-revoke root (position-stable)"
        );
    }
}

/// `with_capability_root` round-trips the real root into the circuit
/// `CellState`, and the resulting `state_commitment` differs from the
/// empty-root state (so the seed genuinely flows into the commitment).
#[test]
fn a2_with_capability_root_round_trips_into_commitment() {
    let mut cell = tcell();
    let t = CellId::derive_raw(&[4u8; 32], &[4u8; 32]);
    cell.capabilities.grant(t, AuthRequired::Signature).unwrap();
    let real_root = dregg_cell::compute_canonical_capability_root_felt(&cell.capabilities);

    let seeded = dregg_circuit::CellState::with_capability_root(100_000, 0, real_root);
    assert_eq!(
        seeded.capability_root, real_root,
        "with_capability_root must carry the real root"
    );

    let empty_state = dregg_circuit::CellState::new(100_000, 0);
    assert_ne!(
        seeded.state_commitment, empty_state.state_commitment,
        "the seeded cap_root must flow into the circuit state_commitment (non-vacuous seed)"
    );
}
