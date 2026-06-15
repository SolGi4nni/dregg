#![cfg(not(feature = "recursion"))]
//! GRADUATED RevokeCapability (sel 24) — the cap-crown cap-REMOVAL leg.
//!
//! These tests are the PROOF that a verifying `RevokeCapability` proof through
//! the AUDITED p3 verifier (`effect_vm_p3_full_air`) IMPLIES the revoked
//! capability WAS HELD (its leaf is AUTHENTICATED against the actor's
//! `old_cap_root` — the seeded openable sorted-Poseidon2 capability tree,
//! `cap_root.rs`) AND the post `cap_root` is the GENUINE sorted-tree DELETION of
//! that slot (the ZERO/padding leaf folded up the SAME sibling path). Mirrors
//! `effect_vm_attenuate_non_amp.rs`: a CONTROL that proves+verifies, then two
//! FORGERIES each rejected by a SPECIFIC gate (flip-one-field non-vacuity).
//!
//!   * CONTROL          — honest revoke of a HELD slot PROVES + VERIFIES.
//!   * FORGERY 1 (held) — revoking a slot NOT in old_cap_root ⇒ REJECT (the
//!                        membership-open authentication: a fabricated held leaf
//!                        has no path to the seeded root).
//!   * FORGERY 2 (root) — a tampered `new_cap_root` (NOT the zero-fold deletion)
//!                        ⇒ REJECT (the zero-fold recompute gate).
//!
//! All decisions go through the FRI-free `p3_air_accepts_revocation` (the exact
//! predicate the audited verifier enforces); the CONTROL additionally does a
//! full real-Plonky3 prove+verify roundtrip via `prove_effect_vm_p3_revocation`
//! / `verify_effect_vm_p3`.

use dregg_cell::facet::{EFFECT_ALL, EFFECT_SET_FIELD, EFFECT_TRANSFER};
use dregg_circuit::cap_root::{
    CAP_TREE_DEPTH, CanonicalCapTree, CapLeaf, encode_breadstuff, encode_expiry, fold_bytes32,
    slot_hash, split_effect_mask,
};
use dregg_circuit::effect_vm::{CellState, Effect, RevokeWitness, generate_effect_vm_trace};
use dregg_circuit::effect_vm_p3_full_air::{
    p3_air_accepts_revocation, prove_effect_vm_p3_revocation, verify_effect_vm_p3,
};
use dregg_circuit::field::BabyBear;

/// Build a `CapLeaf` at `slot` for `target_byte`, with the given tier byte and
/// mask. Mirrors the attenuate gauntlet's `leaf`.
fn leaf(slot: u32, target_byte: u8, tier: u32, mask: u32) -> CapLeaf {
    let mut tgt = [0u8; 32];
    tgt[0] = target_byte;
    let (mask_lo, mask_hi) = split_effect_mask(mask);
    CapLeaf {
        slot_hash: slot_hash(slot),
        target: fold_bytes32(&tgt),
        auth_tag: BabyBear::new(tier),
        mask_lo,
        mask_hi,
        expiry: encode_expiry(None),
        breadstuff: encode_breadstuff(None),
    }
}

/// A representative actor c-list: the revoked leaf at `slot=7` plus a couple of
/// unrelated capabilities (so the membership path has non-trivial siblings).
fn tree_with_held(held: CapLeaf) -> CanonicalCapTree {
    let other_a = leaf(3, 0x22, 1, EFFECT_ALL);
    let other_b = leaf(42, 0x33, 2, EFFECT_TRANSFER);
    CanonicalCapTree::new(vec![held, other_a, other_b], CAP_TREE_DEPTH)
}

/// Build the base 186-col trace + PIs for a single Revoke turn carrying the
/// Phase-B witness, with the actor's `cap_root` seeded to `seed_root` (so GATE 1
/// authenticates against it).
fn base_trace_for(
    held: &CapLeaf,
    w: &RevokeWitness,
    seed_root: BabyBear,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>, Vec<Effect>) {
    // params[0] (CAP_ENTRY) anchors the revoked slot hash; the gate pins it to
    // the witnessed leaf's slot. The remaining 7 limbs are padding.
    let mut slot_limbs = [BabyBear::ZERO; 8];
    slot_limbs[0] = held.slot_hash;
    let eff = Effect::RevokeCapability {
        slot_hash: slot_limbs,
        phase_b: Some(Box::new(w.clone())),
    };
    let initial = CellState::with_capability_root(100_000, 0, seed_root);
    let effects = vec![eff];
    let (trace, pis) = generate_effect_vm_trace(&initial, &effects);
    (trace, pis, effects)
}

// ===========================================================================
// CONTROL — honest revoke of a held slot proves + verifies.
// ===========================================================================

#[test]
fn control_honest_revoke_proves_and_verifies() {
    // The actor holds a cap at slot 7 (among slots 3, 42). Revoking it removes
    // the slot: the cap_root moves to the tree with slot 7 zero-folded out.
    let held = leaf(7, 0x11, 1, EFFECT_SET_FIELD | EFFECT_TRANSFER);
    let tree = tree_with_held(held);

    let aw = tree
        .revocation_witness(held.slot_hash)
        .expect("held slot present in the actor's c-list tree");
    assert_eq!(aw.held, held, "membership opens the genuine held leaf");
    let w = RevokeWitness {
        held: aw.held,
        siblings: aw.siblings,
        directions: aw.directions,
    };
    let (trace, pis, effects) = base_trace_for(&held, &w, tree.root());

    assert!(
        p3_air_accepts_revocation(&trace, &pis, &effects),
        "CONTROL: honest revoke of a held slot must SATISFY the audited p3 AIR (both gates)"
    );
    let proof = prove_effect_vm_p3_revocation(&trace, &pis, &effects)
        .expect("CONTROL: honest revoke must PROVE through the audited p3 verifier");
    verify_effect_vm_p3(&proof, &pis)
        .expect("CONTROL: the honest revoke proof must independently VERIFY");
}

// ===========================================================================
// FORGERY 1 — fabricated held leaf NOT in old_cap_root ⇒ membership-open REJECTS.
// ===========================================================================

#[test]
fn forgery1_fabricated_held_rejected_by_membership_open() {
    // The actor's REAL c-list has caps at slots 3 and 42 — but NOT slot 7. The
    // adversary fabricates a "held" leaf at slot 7 and builds a membership path
    // for it in a DIFFERENT tree (internally consistent, but tops out at the
    // WRONG root). The actor's seeded cap_root is the REAL tree's root, so GATE 1
    // (rev_old_root == old_cap_root) fails.
    let real_a = leaf(3, 0x22, 1, EFFECT_ALL);
    let real_b = leaf(42, 0x33, 2, EFFECT_TRANSFER);
    let real_tree = CanonicalCapTree::new(vec![real_a, real_b], CAP_TREE_DEPTH);
    let real_root = real_tree.root();

    // Fabricated held leaf at a slot NOT in the real tree.
    let fake_held = leaf(7, 0x11, 0, EFFECT_ALL);
    let fake_tree = CanonicalCapTree::new(vec![fake_held], CAP_TREE_DEPTH);
    let aw = fake_tree
        .revocation_witness(fake_held.slot_hash)
        .expect("fake leaf present in the fake tree");
    assert_ne!(
        aw.old_root, real_root,
        "the fabricated leaf's path tops out at a DIFFERENT root than the actor's real cap_root"
    );
    let w = RevokeWitness {
        held: fake_held,
        siblings: aw.siblings,
        directions: aw.directions,
    };
    // Seed the actor's state with the REAL root (the genuine commitment).
    let (trace, pis, effects) = base_trace_for(&fake_held, &w, real_root);

    assert!(
        !p3_air_accepts_revocation(&trace, &pis, &effects),
        "FORGERY 1: a fabricated held leaf NOT in old_cap_root MUST be REJECTED by the membership-open gate"
    );
    assert!(
        prove_effect_vm_p3_revocation(&trace, &pis, &effects).is_err(),
        "FORGERY 1: the audited prover must REFUSE an unauthenticated revoked leaf"
    );
}

// ===========================================================================
// FORGERY 2 — tampered new_cap_root (NOT the zero-fold) ⇒ zero-fold gate REJECTS.
// ===========================================================================

#[test]
fn forgery2_tampered_new_root_rejected() {
    // Honest membership (the held leaf IS in the tree), but the prover forges the
    // post-state cap_root to something OTHER than the genuine zero-fold deletion.
    // The published revoke is REJECTED: the forged root is neither the zero-fold
    // GATE 2 forces NOR the value the GROUP-4 commitment chain re-derives — so a
    // prover cannot publish a revoke whose new_cap_root is not the genuine
    // sorted-tree slot deletion.
    let held = leaf(7, 0x11, 1, EFFECT_SET_FIELD);
    let tree = tree_with_held(held);
    let aw = tree
        .revocation_witness(held.slot_hash)
        .expect("held slot present");
    let w = RevokeWitness {
        held: aw.held,
        siblings: aw.siblings,
        directions: aw.directions,
    };
    let (mut trace, pis, effects) = base_trace_for(&held, &w, tree.root());

    // Non-vacuity: the untampered trace PASSES (so the rejection below is the
    // forgery, not a fixture error).
    assert!(
        p3_air_accepts_revocation(&trace, &pis, &effects),
        "control (genuine zero-fold) must PASS — the forgery's rejection is the tamper, not a fixture error"
    );

    // Forge state_after.cap_root on row 0 to a wrong value (the genuine zero-fold
    // root + 1): not the deletion of the slot.
    use dregg_circuit::effect_vm::columns::{STATE_AFTER_BASE, state};
    let honest_new = trace[0][STATE_AFTER_BASE + state::CAP_ROOT];
    trace[0][STATE_AFTER_BASE + state::CAP_ROOT] = honest_new + BabyBear::new(1);

    assert!(
        !p3_air_accepts_revocation(&trace, &pis, &effects),
        "FORGERY 2: a new_cap_root that is NOT the zero-fold deletion MUST be REJECTED"
    );
}
