#![cfg(not(feature = "recursion"))]
//! PHASE B — AttenuateCapability in-circuit NON-AMPLIFICATION (the reference).
//!
//! These tests are the PROOF that a verifying `AttenuateCapability` proof through
//! the AUDITED p3 verifier (`effect_vm_p3_full_air`) IMPLIES `granted ⊑ held` on
//! BOTH lattices + monotone expiry, with `held` AUTHENTICATED against the
//! actor's `old_cap_root` (the seeded openable sorted-Poseidon2 capability tree,
//! `cap_root.rs`). Mirrors `effect_vm_record_root_anti_ghost.rs` +
//! `dsl/revocation.rs`'s anti-forgery teeth: a CONTROL that proves+verifies, then
//! four FORGERIES each rejected by a SPECIFIC gate (flip-one-field non-vacuity).
//!
//!   * CONTROL          — honest attenuation (granted ⊑ held on both lattices,
//!                        granted_expiry ≤ held_expiry) PROVES + VERIFIES.
//!   * FORGERY 1 (mask) — granted_mask sets a bit absent from held_mask ⇒ REJECT
//!                        (the submask gate).
//!   * FORGERY 2 (auth) — held = Signature, granted = Proof (INCOMPARABLE) ⇒
//!                        REJECT (the AuthRequired LATTICE: a numeric ≤ would
//!                        wrongly admit this — THIS is the litmus that the gate is
//!                        a partial order, not a GTE).
//!   * FORGERY 3 (held) — a held leaf with inflated rights NOT in old_cap_root ⇒
//!                        REJECT (the membership-open authentication).
//!   * FORGERY 4 (vk)   — held = Custom{a}, granted = Custom{b}, a ≠ b ⇒ REJECT
//!                        (the vk-equality sub-gate).
//!
//! All five decisions go through the FRI-free `p3_air_accepts_attenuation` (the
//! exact predicate the audited verifier enforces); the CONTROL additionally does
//! a full real-Plonky3 prove+verify roundtrip via `prove_effect_vm_p3_attenuation`
//! / `verify_effect_vm_p3`.

use dregg_cell::facet::{EFFECT_ALL, EFFECT_EMIT_EVENT, EFFECT_SET_FIELD, EFFECT_TRANSFER};
use dregg_circuit::cap_root::{
    CAP_TREE_DEPTH, CanonicalCapTree, CapLeaf, encode_breadstuff, encode_expiry, fold_bytes32,
    slot_hash, split_effect_mask,
};
use dregg_circuit::effect_vm::{AttenuateWitness, CellState, Effect, generate_effect_vm_trace};
use dregg_circuit::effect_vm_p3_full_air::{
    p3_air_accepts_attenuation, prove_effect_vm_p3_attenuation, verify_effect_vm_p3,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::poseidon2::hash_many;

// Tier ordinals (cell/src/commitment.rs auth_byte): None=0…Custom=5.
const TIER_NONE: u8 = 0;
const TIER_SIGNATURE: u8 = 1;
const TIER_PROOF: u8 = 2;
const TIER_EITHER: u8 = 3;
#[allow(dead_code)]
const TIER_IMPOSSIBLE: u8 = 4;
const TIER_CUSTOM: u8 = 5;

/// The `auth_tag` felt for a built-in tier (= the tier byte) — mirrors the
/// cell-side `auth_required_to_tag` for non-Custom variants.
fn builtin_tag(tier: u8) -> BabyBear {
    BabyBear::new(tier as u32)
}

/// The `auth_tag` felt for `Custom { vk_hash }`: hash_many([5, vk_limbs..]) —
/// mirrors `auth_required_to_tag`'s Custom arm.
fn custom_tag(vk: &[u8; 32]) -> BabyBear {
    let mut inputs = Vec::with_capacity(9);
    inputs.push(BabyBear::new(TIER_CUSTOM as u32));
    inputs.extend_from_slice(&BabyBear::encode_hash(vk));
    hash_many(&inputs)
}

/// Build a `CapLeaf` at `slot` for `target_byte`, with the given auth tag, mask,
/// and optional expiry / breadstuff. Mirrors `cap_ref_to_leaf`.
fn leaf(
    slot: u32,
    target_byte: u8,
    auth_tag: BabyBear,
    mask: u32,
    expiry: Option<u64>,
    breadstuff: Option<[u8; 32]>,
) -> CapLeaf {
    let mut tgt = [0u8; 32];
    tgt[0] = target_byte;
    let (mask_lo, mask_hi) = split_effect_mask(mask);
    CapLeaf {
        slot_hash: slot_hash(slot),
        target: fold_bytes32(&tgt),
        auth_tag,
        mask_lo,
        mask_hi,
        expiry: encode_expiry(expiry),
        breadstuff: encode_breadstuff(breadstuff.as_ref()),
    }
}

/// One Attenuate scenario: the actor's c-list tree (carrying the held leaf among
/// some siblings) + the held/granted leaves and their tiers / raw expiries.
struct Scenario {
    tree: CanonicalCapTree,
    held: CapLeaf,
    granted: CapLeaf,
    held_tier: u8,
    granted_tier: u8,
    held_expiry: Option<u64>,
    granted_expiry: Option<u64>,
}

impl Scenario {
    /// Build the `AttenuateWitness` from the tree's authenticated membership path
    /// for the held slot, narrowed to `granted`.
    fn witness(&self) -> AttenuateWitness {
        let aw = self
            .tree
            .attenuation_witness(self.granted)
            .expect("held slot must be present in the actor's c-list tree");
        // Sanity: the witnessed held leaf is the real committed one.
        assert_eq!(aw.held, self.held, "membership opens the genuine held leaf");
        AttenuateWitness {
            held: aw.held,
            granted: aw.granted,
            siblings: aw.siblings,
            directions: aw.directions,
            held_tier: self.held_tier,
            granted_tier: self.granted_tier,
            held_expiry_height: self.held_expiry,
            granted_expiry_height: self.granted_expiry,
        }
    }

    /// The base 186-col trace + PIs for the single Attenuate turn, with the
    /// actor's `cap_root` seeded to the tree root (so GATE 1 authenticates).
    fn base_trace(&self, w: &AttenuateWitness) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>, Vec<Effect>) {
        // The params anchor the membership slot (params[0]) and the granted leaf
        // digest (params[1]); the gates pin both. The remaining 7 limbs are
        // padding (only limb[0] is load-bearing in-circuit; all 8 bind via
        // effects_hash, irrelevant to the gates).
        let mut slot_limbs = [BabyBear::ZERO; 8];
        slot_limbs[0] = self.held.slot_hash;
        let mut narrower_limbs = [BabyBear::ZERO; 8];
        narrower_limbs[0] = self.granted.digest();
        let eff = Effect::AttenuateCapability {
            cap_slot_hash: slot_limbs,
            narrower_commitment: narrower_limbs,
            phase_b: Some(Box::new(w.clone())),
        };
        let initial = CellState::with_capability_root(100_000, 0, self.tree.root());
        let effects = vec![eff];
        let (trace, pis) = generate_effect_vm_trace(&initial, &effects);
        (trace, pis, effects)
    }
}

/// A representative actor c-list: the held leaf at `slot=7` plus a couple of
/// unrelated capabilities (so the membership path has non-trivial siblings, not
/// just sentinels).
fn tree_with_held(held: CapLeaf) -> CanonicalCapTree {
    let other_a = leaf(3, 0x22, builtin_tag(TIER_SIGNATURE), EFFECT_ALL, None, None);
    let other_b = leaf(
        42,
        0x33,
        builtin_tag(TIER_PROOF),
        EFFECT_TRANSFER,
        Some(500),
        None,
    );
    CanonicalCapTree::new(vec![held, other_a, other_b], CAP_TREE_DEPTH)
}

// ===========================================================================
// CONTROL — honest attenuation proves + verifies.
// ===========================================================================

#[test]
fn control_honest_attenuation_proves_and_verifies() {
    // Held: Either auth, {SetField,Transfer,EmitEvent}, expiry 1000.
    // Granted: narrowed to Signature (⊑ Either), {SetField,EmitEvent} (⊆),
    //          expiry 500 (≤ 1000). Genuine narrowing on all three axes.
    let held = leaf(
        7,
        0x11,
        builtin_tag(TIER_EITHER),
        EFFECT_SET_FIELD | EFFECT_TRANSFER | EFFECT_EMIT_EVENT,
        Some(1000),
        None,
    );
    let granted = leaf(
        7,
        0x11,
        builtin_tag(TIER_SIGNATURE),
        EFFECT_SET_FIELD | EFFECT_EMIT_EVENT,
        Some(500),
        None,
    );
    let scn = Scenario {
        tree: tree_with_held(held),
        held,
        granted,
        held_tier: TIER_EITHER,
        granted_tier: TIER_SIGNATURE,
        held_expiry: Some(1000),
        granted_expiry: Some(500),
    };
    let w = scn.witness();
    let (trace, pis, effects) = scn.base_trace(&w);

    assert!(
        p3_air_accepts_attenuation(&trace, &pis, &effects),
        "CONTROL: honest attenuation must SATISFY the audited p3 AIR (all 5 gates)"
    );
    let proof = prove_effect_vm_p3_attenuation(&trace, &pis, &effects)
        .expect("CONTROL: honest attenuation must PROVE through the audited p3 verifier");
    verify_effect_vm_p3(&proof, &pis)
        .expect("CONTROL: the honest attenuation proof must independently VERIFY");
}

/// Control variant: narrowing an UNBOUNDED (None) expiry to a finite one is a
/// valid narrowing (None = ⊤). Also exercises the None→finite expiry path.
#[test]
fn control_unbounded_to_bounded_expiry_is_narrowing() {
    let held = leaf(7, 0x11, builtin_tag(TIER_EITHER), EFFECT_ALL, None, None);
    let granted = leaf(
        7,
        0x11,
        builtin_tag(TIER_EITHER),
        EFFECT_ALL,
        Some(900),
        None,
    );
    let scn = Scenario {
        tree: tree_with_held(held),
        held,
        granted,
        held_tier: TIER_EITHER,
        granted_tier: TIER_EITHER,
        held_expiry: None,
        granted_expiry: Some(900),
    };
    let w = scn.witness();
    let (trace, pis, effects) = scn.base_trace(&w);
    assert!(
        p3_air_accepts_attenuation(&trace, &pis, &effects),
        "narrowing an unbounded expiry to a finite one is a valid attenuation"
    );
}

// ===========================================================================
// FORGERY 1 — mask amplification ⇒ submask gate REJECTS.
// ===========================================================================

#[test]
fn forgery1_mask_amplification_rejected_by_submask_gate() {
    // Held mask = {SetField, EmitEvent}; granted sets TRANSFER (a bit ABSENT from
    // held) ⇒ amplification. Everything else is a valid narrowing, so ONLY the
    // submask gate can be the rejecter (non-vacuity).
    let held = leaf(
        7,
        0x11,
        builtin_tag(TIER_SIGNATURE),
        EFFECT_SET_FIELD | EFFECT_EMIT_EVENT,
        Some(1000),
        None,
    );
    // Honest control sibling: granted ⊆ held (drop EmitEvent) — must pass.
    let honest_granted = leaf(
        7,
        0x11,
        builtin_tag(TIER_SIGNATURE),
        EFFECT_SET_FIELD,
        Some(1000),
        None,
    );
    // Forged granted: adds TRANSFER (not in held).
    let forged_granted = leaf(
        7,
        0x11,
        builtin_tag(TIER_SIGNATURE),
        EFFECT_SET_FIELD | EFFECT_TRANSFER,
        Some(1000),
        None,
    );

    let mk = |granted: CapLeaf| Scenario {
        tree: tree_with_held(held),
        held,
        granted,
        held_tier: TIER_SIGNATURE,
        granted_tier: TIER_SIGNATURE,
        held_expiry: Some(1000),
        granted_expiry: Some(1000),
    };

    // Non-vacuity: the honest sibling (drop a bit) PASSES.
    let scn_ok = mk(honest_granted);
    let w_ok = scn_ok.witness();
    let (t_ok, p_ok, e_ok) = scn_ok.base_trace(&w_ok);
    assert!(
        p3_air_accepts_attenuation(&t_ok, &p_ok, &e_ok),
        "control sibling (granted ⊆ held) must PASS — so the forgery's rejection is the submask gate, not a fixture error"
    );

    // The forgery (add an absent bit) is REJECTED.
    let scn = mk(forged_granted);
    let w = scn.witness();
    let (t, p, e) = scn.base_trace(&w);
    assert!(
        !p3_air_accepts_attenuation(&t, &p, &e),
        "FORGERY 1: a granted mask bit ABSENT from held must be REJECTED by the submask gate"
    );
    assert!(
        prove_effect_vm_p3_attenuation(&t, &p, &e).is_err(),
        "FORGERY 1: the audited prover must REFUSE the mask-amplifying attenuation"
    );
}

// ===========================================================================
// FORGERY 2 — INCOMPARABLE AuthRequired ⇒ the LATTICE gate REJECTS.
// (held = Signature, granted = Proof: a numeric ≤ would wrongly admit this.)
// ===========================================================================

#[test]
fn forgery2_incomparable_auth_rejected_by_lattice_not_gte() {
    // Held = Signature(1); granted = Proof(2). {Signature} and {Proof} are
    // INCOMPARABLE in `is_narrower_or_equal` (neither narrower nor equal). A
    // GTE/numeric-≤ (2 ≤ 1 is false, or 1 ≤ 2 is true) would mis-decide; the
    // admissible-pair LATTICE has NO (2,1) entry and (2,1) is not the vk path ⇒
    // UNSAT. Mask + expiry are held FIXED so the lattice is the SOLE rejecter.
    let held = leaf(
        7,
        0x11,
        builtin_tag(TIER_SIGNATURE),
        EFFECT_ALL,
        Some(1000),
        None,
    );
    let forged_granted = leaf(
        7,
        0x11,
        builtin_tag(TIER_PROOF),
        EFFECT_ALL,
        Some(1000),
        None,
    );

    // Non-vacuity control: granted == held (Signature ⊑ Signature) PASSES.
    let honest_granted = leaf(
        7,
        0x11,
        builtin_tag(TIER_SIGNATURE),
        EFFECT_ALL,
        Some(1000),
        None,
    );
    let scn_ok = Scenario {
        tree: tree_with_held(held),
        held,
        granted: honest_granted,
        held_tier: TIER_SIGNATURE,
        granted_tier: TIER_SIGNATURE,
        held_expiry: Some(1000),
        granted_expiry: Some(1000),
    };
    let w_ok = scn_ok.witness();
    let (t_ok, p_ok, e_ok) = scn_ok.base_trace(&w_ok);
    assert!(
        p3_air_accepts_attenuation(&t_ok, &p_ok, &e_ok),
        "control (Signature ⊑ Signature) must PASS — isolates the lattice as the forgery's rejecter"
    );

    // The incomparable forgery is REJECTED.
    let scn = Scenario {
        tree: tree_with_held(held),
        held,
        granted: forged_granted,
        held_tier: TIER_SIGNATURE,
        granted_tier: TIER_PROOF,
        held_expiry: Some(1000),
        granted_expiry: Some(1000),
    };
    let w = scn.witness();
    let (t, p, e) = scn.base_trace(&w);
    assert!(
        !p3_air_accepts_attenuation(&t, &p, &e),
        "FORGERY 2 (LITMUS): Signature→Proof is INCOMPARABLE and MUST be REJECTED — \
         the AuthRequired gate is a PARTIAL ORDER, not a numeric ≤"
    );
    assert!(
        prove_effect_vm_p3_attenuation(&t, &p, &e).is_err(),
        "FORGERY 2: the audited prover must REFUSE the incomparable-auth attenuation"
    );

    // Belt: the OTHER incomparable direction (held=Proof, granted=Signature) is
    // ALSO rejected (the table omits BOTH (1,2) and (2,1)).
    let held2 = leaf(
        7,
        0x11,
        builtin_tag(TIER_PROOF),
        EFFECT_ALL,
        Some(1000),
        None,
    );
    let granted2 = leaf(
        7,
        0x11,
        builtin_tag(TIER_SIGNATURE),
        EFFECT_ALL,
        Some(1000),
        None,
    );
    let scn2 = Scenario {
        tree: tree_with_held(held2),
        held: held2,
        granted: granted2,
        held_tier: TIER_PROOF,
        granted_tier: TIER_SIGNATURE,
        held_expiry: Some(1000),
        granted_expiry: Some(1000),
    };
    let w2 = scn2.witness();
    let (t2, p2, e2) = scn2.base_trace(&w2);
    assert!(
        !p3_air_accepts_attenuation(&t2, &p2, &e2),
        "FORGERY 2 (dual): Proof→Signature is ALSO incomparable ⇒ REJECT"
    );
}

// ===========================================================================
// FORGERY 3 — fabricated held leaf NOT in old_cap_root ⇒ membership-open REJECTS.
// ===========================================================================

#[test]
fn forgery3_fabricated_held_rejected_by_membership_open() {
    // The actor's REAL c-list has the held cap with NARROW rights (Signature,
    // {SetField}). The adversary fabricates a held leaf with INFLATED rights
    // (None auth — the broadest — + EFFECT_ALL) so that the "narrowing" to a
    // genuine cap looks valid on the lattices, then attenuates from the inflated
    // fake. But the fake held leaf is NOT in old_cap_root, so its membership path
    // cannot reach the seeded root ⇒ GATE 1 fails.
    let real_held = leaf(
        7,
        0x11,
        builtin_tag(TIER_SIGNATURE),
        EFFECT_SET_FIELD,
        Some(1000),
        None,
    );
    let tree = tree_with_held(real_held);
    let real_root = tree.root();

    // Fabricated held: same slot/target, INFLATED rights.
    let fake_held = leaf(7, 0x11, builtin_tag(TIER_NONE), EFFECT_ALL, None, None);
    // Granted: looks like a valid narrowing OF THE FAKE (Signature ⊑ None,
    // {SetField} ⊆ ALL, finite ≤ None).
    let granted = leaf(
        7,
        0x11,
        builtin_tag(TIER_SIGNATURE),
        EFFECT_SET_FIELD,
        Some(1000),
        None,
    );

    // Build a membership path for the fake held leaf by inserting it into a
    // DIFFERENT tree (so the path is internally consistent but tops out at the
    // WRONG root). The actor's seeded cap_root is `real_root`, so GATE 1
    // (attn_old_root == old_cap_root) fails.
    let fake_tree = CanonicalCapTree::new(vec![fake_held], CAP_TREE_DEPTH);
    let aw = fake_tree
        .attenuation_witness(granted)
        .expect("fake leaf present in the fake tree");
    assert_ne!(
        aw.old_root, real_root,
        "the fabricated leaf's path tops out at a DIFFERENT root than the actor's real cap_root"
    );
    let w = AttenuateWitness {
        held: fake_held,
        granted,
        siblings: aw.siblings,
        directions: aw.directions,
        held_tier: TIER_NONE,
        granted_tier: TIER_SIGNATURE,
        held_expiry_height: None,
        granted_expiry_height: Some(1000),
    };
    // Seed the actor's state with the REAL root (the genuine commitment).
    let mut slot_limbs = [BabyBear::ZERO; 8];
    slot_limbs[0] = fake_held.slot_hash;
    let mut narrower_limbs = [BabyBear::ZERO; 8];
    narrower_limbs[0] = granted.digest();
    let eff = Effect::AttenuateCapability {
        cap_slot_hash: slot_limbs,
        narrower_commitment: narrower_limbs,
        phase_b: Some(Box::new(w)),
    };
    let initial = CellState::with_capability_root(100_000, 0, real_root);
    let effects = vec![eff];
    let (trace, pis) = generate_effect_vm_trace(&initial, &effects);

    assert!(
        !p3_air_accepts_attenuation(&trace, &pis, &effects),
        "FORGERY 3: a fabricated held leaf NOT in old_cap_root MUST be REJECTED by the membership-open gate"
    );
    assert!(
        prove_effect_vm_p3_attenuation(&trace, &pis, &effects).is_err(),
        "FORGERY 3: the audited prover must REFUSE an unauthenticated held leaf"
    );
}

// ===========================================================================
// FORGERY 4 — Custom vk mismatch ⇒ vk-equality sub-gate REJECTS.
// ===========================================================================

#[test]
fn forgery4_custom_vk_mismatch_rejected_by_vk_subgate() {
    // Held = Custom{a}; granted = Custom{b}, a ≠ b. `is_narrower_or_equal`
    // admits Custom→Custom ONLY when vk_hashes are equal. The lattice routes both
    // to the vk path (tiers 5,5); the vk sub-gate forces granted_tag == held_tag,
    // which FAILS for distinct vks (distinct absorbed-vk felts).
    let vk_a = [0xAA; 32];
    let vk_b = [0xBB; 32];
    let held = leaf(7, 0x11, custom_tag(&vk_a), EFFECT_ALL, Some(1000), None);

    // Non-vacuity control: granted = Custom{a} (SAME vk) PASSES.
    let honest_granted = leaf(7, 0x11, custom_tag(&vk_a), EFFECT_ALL, Some(1000), None);
    let scn_ok = Scenario {
        tree: tree_with_held(held),
        held,
        granted: honest_granted,
        held_tier: TIER_CUSTOM,
        granted_tier: TIER_CUSTOM,
        held_expiry: Some(1000),
        granted_expiry: Some(1000),
    };
    let w_ok = scn_ok.witness();
    let (t_ok, p_ok, e_ok) = scn_ok.base_trace(&w_ok);
    assert!(
        p3_air_accepts_attenuation(&t_ok, &p_ok, &e_ok),
        "control (Custom{{a}} ⊑ Custom{{a}}, equal vk) must PASS — isolates the vk sub-gate"
    );

    // The vk-mismatch forgery is REJECTED.
    let forged_granted = leaf(7, 0x11, custom_tag(&vk_b), EFFECT_ALL, Some(1000), None);
    let scn = Scenario {
        tree: tree_with_held(held),
        held,
        granted: forged_granted,
        held_tier: TIER_CUSTOM,
        granted_tier: TIER_CUSTOM,
        held_expiry: Some(1000),
        granted_expiry: Some(1000),
    };
    let w = scn.witness();
    let (t, p, e) = scn.base_trace(&w);
    assert!(
        !p3_air_accepts_attenuation(&t, &p, &e),
        "FORGERY 4: Custom{{a}} → Custom{{b}} with a ≠ b MUST be REJECTED by the vk-equality sub-gate"
    );
    assert!(
        prove_effect_vm_p3_attenuation(&t, &p, &e).is_err(),
        "FORGERY 4: the audited prover must REFUSE the Custom-vk-mismatch attenuation"
    );
}

// ===========================================================================
// FORGERY 5 (bonus) — expiry EXTENSION ⇒ monotone-expiry gate REJECTS.
// ===========================================================================

#[test]
fn forgery5_expiry_extension_rejected_by_monotone_gate() {
    // Held expiry 500; granted "narrows" to 900 (EXTENDS the bound — a widening).
    // Auth + mask are held FIXED, so the expiry gate is the SOLE rejecter.
    let held = leaf(
        7,
        0x11,
        builtin_tag(TIER_SIGNATURE),
        EFFECT_ALL,
        Some(500),
        None,
    );
    let forged_granted = leaf(
        7,
        0x11,
        builtin_tag(TIER_SIGNATURE),
        EFFECT_ALL,
        Some(900),
        None,
    );

    // Non-vacuity control: shrink 500 → 400 PASSES.
    let honest_granted = leaf(
        7,
        0x11,
        builtin_tag(TIER_SIGNATURE),
        EFFECT_ALL,
        Some(400),
        None,
    );
    let scn_ok = Scenario {
        tree: tree_with_held(held),
        held,
        granted: honest_granted,
        held_tier: TIER_SIGNATURE,
        granted_tier: TIER_SIGNATURE,
        held_expiry: Some(500),
        granted_expiry: Some(400),
    };
    let w_ok = scn_ok.witness();
    let (t_ok, p_ok, e_ok) = scn_ok.base_trace(&w_ok);
    assert!(
        p3_air_accepts_attenuation(&t_ok, &p_ok, &e_ok),
        "control (expiry 500 → 400 shrink) must PASS — isolates the expiry gate"
    );

    let scn = Scenario {
        tree: tree_with_held(held),
        held,
        granted: forged_granted,
        held_tier: TIER_SIGNATURE,
        granted_tier: TIER_SIGNATURE,
        held_expiry: Some(500),
        granted_expiry: Some(900),
    };
    let w = scn.witness();
    let (t, p, e) = scn.base_trace(&w);
    assert!(
        !p3_air_accepts_attenuation(&t, &p, &e),
        "FORGERY 5: EXTENDING a finite expiry (500 → 900) MUST be REJECTED by the monotone-expiry gate"
    );

    // And a finite→unbounded "narrowing" (granted None over a finite held) is a
    // widening ⇒ also rejected (granted None ⇒ held None gate).
    let granted_none = leaf(7, 0x11, builtin_tag(TIER_SIGNATURE), EFFECT_ALL, None, None);
    let scn_none = Scenario {
        tree: tree_with_held(held),
        held,
        granted: granted_none,
        held_tier: TIER_SIGNATURE,
        granted_tier: TIER_SIGNATURE,
        held_expiry: Some(500),
        granted_expiry: None,
    };
    let w_none = scn_none.witness();
    let (tn, pn, en) = scn_none.base_trace(&w_none);
    assert!(
        !p3_air_accepts_attenuation(&tn, &pn, &en),
        "FORGERY 5 (dual): granted None over a FINITE held is a widening ⇒ REJECT"
    );
}
