//! PHASE B2 — GrantCapability (sel 3) in-circuit NON-AMPLIFICATION: the
//! cross-cell delegation, on the granter-side delegation row.
//!
//! Mirrors `effect_vm_attenuate_non_amp.rs` (the Phase-B reference). These tests
//! are the PROOF that a verifying witnessed-Grant proof through the AUDITED p3
//! verifier (`effect_vm_p3_full_air`) IMPLIES `granted ⊑ held` on BOTH lattices
//! + monotone expiry, with `held` AUTHENTICATED against the GRANTER's
//! `old_cap_root` (the row covers the GRANTER cell; its `state_before.cap_root`
//! IS the tree holding the delegated-from cap). Grant's structural difference
//! from Attenuate — the granted leaf lands in the RECIPIENT's c-list at a NEW
//! slot — shows up as: the granted leaf carries its OWN `slot_hash` /
//! `breadstuff`, the granter's cap_root PASSES THROUGH (delegating does not
//! move the granter's tree), and the public `cap_entry` param (params[0]) is
//! pinned in-circuit to the granted CapLeaf's 7-field Poseidon2 digest — the
//! installed entry's ACTUAL rights fields, not an opaque digest.
//!
//!   * CONTROL          — honest cross-cell grant (granted ⊑ held on both
//!                        lattices, granted_expiry ≤ held_expiry, recipient-side
//!                        slot) PROVES + VERIFIES.
//!   * FORGERY 1 (mask) — granted_mask sets a bit absent from held_mask ⇒ REJECT
//!                        (the submask gate).
//!   * FORGERY 2 (auth) — held = Signature, granted = Proof (INCOMPARABLE) ⇒
//!                        REJECT (the AuthRequired LATTICE litmus a GTE would
//!                        wrongly admit).
//!   * FORGERY 3 (held) — a held leaf with inflated rights NOT in the GRANTER's
//!                        cap_root ⇒ REJECT (the membership-open authentication;
//!                        a free held is forbidden).
//!   * FORGERY 4 (vk)   — held = Custom{a}, granted = Custom{b}, a ≠ b ⇒ REJECT
//!                        (the vk-equality sub-gate).
//!   * FORGERY 5 (exp)  — granted extends the held expiry ⇒ REJECT (the
//!                        monotone-expiry gate); granted-None over finite held
//!                        ALSO rejected.
//!   * FORGERY 6 (bind) — cap_entry[0] ≠ the granted leaf's genuine digest ⇒
//!                        REJECT (the granted-leaf binding gate: the public
//!                        param must commit to the actual rights fields).
//!
//! Each forgery flips ONE field against a PASSING control (non-vacuity). All
//! decisions go through the FRI-free `p3_air_accepts_attenuation` (the exact
//! predicate the audited verifier enforces — shared with Attenuate, Phase B2
//! threads witnessed Grant rows through the same entry points); the CONTROL
//! additionally does a full real-Plonky3 prove+verify roundtrip.

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
const TIER_CUSTOM: u8 = 5;

/// The `auth_tag` felt for a built-in tier (= the tier byte).
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

/// The GRANTER's held slot in every scenario.
const HELD_SLOT: u32 = 7;
/// The RECIPIENT's new slot the granted leaf installs at — a DIFFERENT c-list,
/// so its slot is unrelated to the held slot (the structural difference from
/// Attenuate's narrow-in-place).
const RECIPIENT_SLOT: u32 = 0;

/// One Grant scenario: the GRANTER's c-list tree (carrying the held leaf among
/// some unrelated caps) + the held/granted leaves and their tiers / raw expiries.
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
    /// Build the delegation witness from the GRANTER tree's authenticated
    /// membership path for the held slot, delegating `granted` to the recipient.
    fn witness(&self) -> AttenuateWitness {
        let dw = self
            .tree
            .delegation_witness(self.held.slot_hash, self.granted)
            .expect("held slot must be present in the granter's c-list tree");
        // Sanity: the witnessed held leaf is the real committed one, and the
        // granter's tree is unchanged by the delegation.
        assert_eq!(dw.held, self.held, "membership opens the genuine held leaf");
        assert_eq!(
            dw.old_root, dw.new_root,
            "delegating must not move the granter's tree"
        );
        AttenuateWitness {
            held: dw.held,
            granted: dw.granted,
            siblings: dw.siblings,
            directions: dw.directions,
            held_tier: self.held_tier,
            granted_tier: self.granted_tier,
            held_expiry_height: self.held_expiry,
            granted_expiry_height: self.granted_expiry,
        }
    }

    /// The base trace + PIs for the single witnessed-Grant turn, with the
    /// GRANTER's `cap_root` seeded to the granter tree root (so GATE 1
    /// authenticates the held leaf against the genuine delegated-from rights).
    /// `cap_entry[0]` carries the granted leaf's digest — the AIR pins it.
    fn base_trace(&self, w: &AttenuateWitness) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>, Vec<Effect>) {
        self.base_trace_with_cap_entry(w, self.granted.digest())
    }

    /// Like [`Self::base_trace`] but with an explicit `cap_entry[0]` (FORGERY 6
    /// flips this against the genuine granted digest).
    fn base_trace_with_cap_entry(
        &self,
        w: &AttenuateWitness,
        cap_entry0: BabyBear,
    ) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>, Vec<Effect>) {
        let mut cap_entry = [BabyBear::ZERO; 8];
        cap_entry[0] = cap_entry0;
        let eff = Effect::GrantCapability {
            cap_entry,
            phase_b: Some(Box::new(w.clone())),
        };
        let initial = CellState::with_capability_root(100_000, 0, self.tree.root());
        let effects = vec![eff];
        let (trace, pis) = generate_effect_vm_trace(&initial, &effects);
        (trace, pis, effects)
    }
}

/// A representative GRANTER c-list: the held leaf at `HELD_SLOT` plus a couple
/// of unrelated capabilities (so the membership path has non-trivial siblings).
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
// CONTROL — honest cross-cell grant proves + verifies.
// ===========================================================================

#[test]
fn control_honest_grant_proves_and_verifies() {
    // Granter holds: Either auth, {SetField,Transfer,EmitEvent}, expiry 1000,
    // over target 0x11. Grants the recipient (new slot 0, SAME target): narrowed
    // to Signature (⊑ Either), {SetField,EmitEvent} (⊆), expiry 500 (≤ 1000).
    // Genuine narrowing on all three axes, across c-lists.
    let held = leaf(
        HELD_SLOT,
        0x11,
        builtin_tag(TIER_EITHER),
        EFFECT_SET_FIELD | EFFECT_TRANSFER | EFFECT_EMIT_EVENT,
        Some(1000),
        None,
    );
    let granted = leaf(
        RECIPIENT_SLOT,
        0x11,
        builtin_tag(TIER_SIGNATURE),
        EFFECT_SET_FIELD | EFFECT_EMIT_EVENT,
        Some(500),
        None,
    );
    // The structural difference from Attenuate is REAL in this fixture: the
    // granted leaf occupies a different slot key than the held leaf.
    assert_ne!(
        granted.slot_hash, held.slot_hash,
        "cross-c-list grant: different slot keys"
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
        "CONTROL: honest cross-cell grant must SATISFY the audited p3 AIR (membership + all 3 order gates + granted-leaf binding + cap_root passthrough)"
    );
    let proof = prove_effect_vm_p3_attenuation(&trace, &pis, &effects)
        .expect("CONTROL: honest grant must PROVE through the audited p3 verifier");
    verify_effect_vm_p3(&proof, &pis)
        .expect("CONTROL: the honest grant proof must independently VERIFY");
}

/// Control variant: delegating with a breadstuff'd granted cap (grant carries
/// the delegated cap's OWN breadstuff — unlike Attenuate, no equality with the
/// held leaf's breadstuff is required) and an unbounded→bounded expiry.
#[test]
fn control_grant_with_own_breadstuff_and_bounded_expiry() {
    let held = leaf(
        HELD_SLOT,
        0x11,
        builtin_tag(TIER_EITHER),
        EFFECT_ALL,
        None,
        None,
    );
    let granted = leaf(
        RECIPIENT_SLOT,
        0x11,
        builtin_tag(TIER_EITHER),
        EFFECT_ALL,
        Some(900),
        Some([0x77; 32]),
    );
    assert_ne!(
        granted.breadstuff, held.breadstuff,
        "granted carries its own breadstuff"
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
        "a granted leaf with its own breadstuff + a bounded expiry under an unbounded held is a valid delegation"
    );
}

// ===========================================================================
// FORGERY 1 — mask amplification ⇒ submask gate REJECTS.
// ===========================================================================

#[test]
fn forgery1_mask_amplification_rejected_by_submask_gate() {
    // Held mask = {SetField, EmitEvent}; granted sets TRANSFER (a bit ABSENT
    // from held) ⇒ amplification. Everything else is a valid narrowing, so ONLY
    // the submask gate can be the rejecter (non-vacuity).
    let held = leaf(
        HELD_SLOT,
        0x11,
        builtin_tag(TIER_SIGNATURE),
        EFFECT_SET_FIELD | EFFECT_EMIT_EVENT,
        Some(1000),
        None,
    );
    let honest_granted = leaf(
        RECIPIENT_SLOT,
        0x11,
        builtin_tag(TIER_SIGNATURE),
        EFFECT_SET_FIELD,
        Some(1000),
        None,
    );
    let forged_granted = leaf(
        RECIPIENT_SLOT,
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
        "FORGERY 1: a granted mask bit ABSENT from the granter's held mask must be REJECTED by the submask gate"
    );
    assert!(
        prove_effect_vm_p3_attenuation(&t, &p, &e).is_err(),
        "FORGERY 1: the audited prover must REFUSE the mask-amplifying grant"
    );
}

// ===========================================================================
// FORGERY 2 — INCOMPARABLE AuthRequired ⇒ the LATTICE gate REJECTS.
// ===========================================================================

#[test]
fn forgery2_incomparable_auth_rejected_by_lattice_not_gte() {
    // Held = Signature(1); granted = Proof(2). INCOMPARABLE in
    // `is_narrower_or_equal` — a numeric ≤ would mis-decide; the
    // admissible-pair LATTICE has NO (2,1) entry ⇒ UNSAT. Mask + expiry held
    // FIXED so the lattice is the SOLE rejecter. This is ALSO exactly the
    // check the runtime's `apply_grant_capability` does enforce
    // (`is_attenuation`, apply.rs:646) — the circuit now carries it in-proof.
    let held = leaf(
        HELD_SLOT,
        0x11,
        builtin_tag(TIER_SIGNATURE),
        EFFECT_ALL,
        Some(1000),
        None,
    );
    let forged_granted = leaf(
        RECIPIENT_SLOT,
        0x11,
        builtin_tag(TIER_PROOF),
        EFFECT_ALL,
        Some(1000),
        None,
    );

    // Non-vacuity control: granted == held tier (Signature ⊑ Signature) PASSES.
    let honest_granted = leaf(
        RECIPIENT_SLOT,
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
        "FORGERY 2 (LITMUS): granting Proof from a held Signature is INCOMPARABLE and MUST be REJECTED — \
         the AuthRequired gate is a PARTIAL ORDER, not a numeric ≤"
    );
    assert!(
        prove_effect_vm_p3_attenuation(&t, &p, &e).is_err(),
        "FORGERY 2: the audited prover must REFUSE the incomparable-auth grant"
    );

    // Belt: the OTHER incomparable direction (held=Proof, granted=Signature) is
    // ALSO rejected (the table omits BOTH (1,2) and (2,1)).
    let held2 = leaf(
        HELD_SLOT,
        0x11,
        builtin_tag(TIER_PROOF),
        EFFECT_ALL,
        Some(1000),
        None,
    );
    let granted2 = leaf(
        RECIPIENT_SLOT,
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
        "FORGERY 2 (dual): granting Signature from a held Proof is ALSO incomparable ⇒ REJECT"
    );
}

// ===========================================================================
// FORGERY 3 — fabricated held NOT in the GRANTER's cap_root ⇒ membership REJECTS.
// ===========================================================================

#[test]
fn forgery3_fabricated_held_rejected_by_membership_open() {
    // The granter's REAL c-list holds a NARROW cap (Signature, {SetField}).
    // The adversary fabricates a held leaf with INFLATED rights (None auth +
    // EFFECT_ALL) so the delegation looks like a valid narrowing OF THE FAKE,
    // then grants broad rights to an accomplice recipient. But the fake held
    // leaf is NOT in the granter's cap_root, so its membership path cannot
    // reach the seeded root ⇒ GATE 1 fails. A free held is forbidden.
    let real_held = leaf(
        HELD_SLOT,
        0x11,
        builtin_tag(TIER_SIGNATURE),
        EFFECT_SET_FIELD,
        Some(1000),
        None,
    );
    let tree = tree_with_held(real_held);
    let real_root = tree.root();

    // Fabricated held: same slot/target, INFLATED rights.
    let fake_held = leaf(
        HELD_SLOT,
        0x11,
        builtin_tag(TIER_NONE),
        EFFECT_ALL,
        None,
        None,
    );
    // Granted: a broad delegation that would be a valid narrowing OF THE FAKE
    // (Either ⊑ None, EFFECT_ALL ⊆ ALL, finite ≤ None) but is an AMPLIFICATION
    // of the real held rights.
    let granted = leaf(
        RECIPIENT_SLOT,
        0x11,
        builtin_tag(TIER_EITHER),
        EFFECT_ALL,
        Some(1000),
        None,
    );

    // Build a membership path for the fake held leaf from a DIFFERENT tree (so
    // the path is internally consistent but tops out at the WRONG root).
    let fake_tree = CanonicalCapTree::new(vec![fake_held], CAP_TREE_DEPTH);
    let dw = fake_tree
        .delegation_witness(fake_held.slot_hash, granted)
        .expect("fake leaf present in the fake tree");
    assert_ne!(
        dw.old_root, real_root,
        "the fabricated leaf's path tops out at a DIFFERENT root than the granter's real cap_root"
    );
    let w = AttenuateWitness {
        held: fake_held,
        granted,
        siblings: dw.siblings,
        directions: dw.directions,
        held_tier: TIER_NONE,
        granted_tier: TIER_EITHER,
        held_expiry_height: None,
        granted_expiry_height: Some(1000),
    };
    // Seed the granter's state with the REAL root (the genuine commitment).
    let mut cap_entry = [BabyBear::ZERO; 8];
    cap_entry[0] = granted.digest();
    let eff = Effect::GrantCapability {
        cap_entry,
        phase_b: Some(Box::new(w)),
    };
    let initial = CellState::with_capability_root(100_000, 0, real_root);
    let effects = vec![eff];
    let (trace, pis) = generate_effect_vm_trace(&initial, &effects);

    assert!(
        !p3_air_accepts_attenuation(&trace, &pis, &effects),
        "FORGERY 3: a fabricated held leaf NOT in the GRANTER's cap_root MUST be REJECTED by the membership-open gate"
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
    // admits Custom→Custom ONLY when vk_hashes are equal.
    let vk_a = [0xAA; 32];
    let vk_b = [0xBB; 32];
    let held = leaf(
        HELD_SLOT,
        0x11,
        custom_tag(&vk_a),
        EFFECT_ALL,
        Some(1000),
        None,
    );

    // Non-vacuity control: granted = Custom{a} (SAME vk) PASSES.
    let honest_granted = leaf(
        RECIPIENT_SLOT,
        0x11,
        custom_tag(&vk_a),
        EFFECT_ALL,
        Some(1000),
        None,
    );
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
    let forged_granted = leaf(
        RECIPIENT_SLOT,
        0x11,
        custom_tag(&vk_b),
        EFFECT_ALL,
        Some(1000),
        None,
    );
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
        "FORGERY 4: granting Custom{{b}} from a held Custom{{a}} with a ≠ b MUST be REJECTED by the vk-equality sub-gate"
    );
    assert!(
        prove_effect_vm_p3_attenuation(&t, &p, &e).is_err(),
        "FORGERY 4: the audited prover must REFUSE the Custom-vk-mismatch grant"
    );
}

// ===========================================================================
// FORGERY 5 — expiry EXTENSION ⇒ monotone-expiry gate REJECTS.
// ===========================================================================

#[test]
fn forgery5_expiry_extension_rejected_by_monotone_gate() {
    // Held expiry 500; granted "narrows" to 900 (EXTENDS the bound). Auth +
    // mask held FIXED, so the expiry gate is the SOLE rejecter. NOTE: the
    // runtime's `grant_with_breadstuff` currently installs `expires_at: None`
    // unconditionally — the circuit gate enforces the WORTHWHILE semantics.
    let held = leaf(
        HELD_SLOT,
        0x11,
        builtin_tag(TIER_SIGNATURE),
        EFFECT_ALL,
        Some(500),
        None,
    );
    let forged_granted = leaf(
        RECIPIENT_SLOT,
        0x11,
        builtin_tag(TIER_SIGNATURE),
        EFFECT_ALL,
        Some(900),
        None,
    );

    // Non-vacuity control: shrink 500 → 400 PASSES.
    let honest_granted = leaf(
        RECIPIENT_SLOT,
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
        "FORGERY 5: EXTENDING a finite held expiry (500 → 900) in a grant MUST be REJECTED by the monotone-expiry gate"
    );

    // And a finite→unbounded grant (granted None over a finite held) is a
    // widening ⇒ also rejected.
    let granted_none = leaf(
        RECIPIENT_SLOT,
        0x11,
        builtin_tag(TIER_SIGNATURE),
        EFFECT_ALL,
        None,
        None,
    );
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
        "FORGERY 5 (dual): granting an UNBOUNDED expiry from a finite held is a widening ⇒ REJECT"
    );
}

// ===========================================================================
// FORGERY 6 — cap_entry not the granted leaf's digest ⇒ binding gate REJECTS.
// ===========================================================================

#[test]
fn forgery6_cap_entry_digest_mismatch_rejected_by_binding_gate() {
    // An otherwise-honest delegation whose PUBLIC cap_entry param carries a
    // digest of DIFFERENT rights than the witnessed granted leaf: the public
    // attestation (what the recipient-side install consumes) would not match
    // the rights the order gates checked. The binding gate pins
    // params[0] == Poseidon2(granted leaf fields) ⇒ REJECT.
    let held = leaf(
        HELD_SLOT,
        0x11,
        builtin_tag(TIER_EITHER),
        EFFECT_ALL,
        Some(1000),
        None,
    );
    let granted = leaf(
        RECIPIENT_SLOT,
        0x11,
        builtin_tag(TIER_SIGNATURE),
        EFFECT_SET_FIELD,
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

    // Non-vacuity: the SAME witness with the genuine digest PASSES.
    let (t_ok, p_ok, e_ok) = scn.base_trace(&w);
    assert!(
        p3_air_accepts_attenuation(&t_ok, &p_ok, &e_ok),
        "control (genuine granted digest in cap_entry) must PASS — isolates the binding gate"
    );

    // Flip ONE field: cap_entry[0] = digest of an AMPLIFIED leaf (what a
    // dishonest granter would want the recipient install to consume).
    let amplified = leaf(
        RECIPIENT_SLOT,
        0x11,
        builtin_tag(TIER_NONE),
        EFFECT_ALL,
        None,
        None,
    );
    let (t, p, e) = scn.base_trace_with_cap_entry(&w, amplified.digest());
    assert!(
        !p3_air_accepts_attenuation(&t, &p, &e),
        "FORGERY 6: a cap_entry digest that does not match the witnessed granted leaf MUST be REJECTED by the granted-leaf binding gate"
    );
    assert!(
        prove_effect_vm_p3_attenuation(&t, &p, &e).is_err(),
        "FORGERY 6: the audited prover must REFUSE the mismatched public attestation"
    );
}
