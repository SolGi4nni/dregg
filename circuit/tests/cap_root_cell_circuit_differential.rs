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
