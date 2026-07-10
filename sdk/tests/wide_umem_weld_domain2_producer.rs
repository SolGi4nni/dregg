//! # THE DOMAIN-2 CAP-OPEN UMEM **PRODUCER PLUMBING** LOUD PROBE (STAGED, VK-RISK-FREE) — the umem
//! flip's 12th-catch seam CLOSED.
//!
//! The sibling [`wide_umem_weld_domain2_gauntlet`] bites the welded cap-open PRODUCER in isolation
//! (`prove_cap_open_umem_welded_staged` directly). THIS probe bites the **routing seam** the 12th
//! catch found: the SHARED full-turn path ([`dregg_sdk::prove_full_turn`] →
//! `prove_cohort_run_chain`) — the exact path the deployed node
//! `prove_and_verify_finalized_turn_capability*` drives — now MINTS the WIDE cap-open+umem WELDED leg
//! for a domain-2 cap-gated turn WHEN the caller threads the turn's CAPS-domain universal-memory
//! projection diff via [`dregg_sdk::FullTurnWitness::umem_witness`].
//!
//! ## What this proves (the producer seam)
//!
//! 1. **THE WELDED ROUTE (the seam closed)** — a single-effect `AttenuateCapability` turn with a
//!    consumed-cap membership witness AND a threaded CAPS umem witness mints, through
//!    `prove_full_turn`, an `"effect-vm-rotated"` leg that verifies UNIQUELY through the deployed wire
//!    verifier under the Lean-emitted welded-twin `attenuateCapOpenEffVmDescriptor2R24` member of
//!    [`WIDE_UMEM_WELD_REGISTRY_TSV`]. The leg's vk_hash PINS the WELDED member (PANIC if it does not
//!    — a silent bare-fallback cannot hide).
//! 2. **THE ~124-BIT BINDING TOOTH** — tampering one of the welded leg's last-16 PIs (a forged 8-felt
//!    commit felt) makes the wire verifier REJECT.
//! 3. **THE BARE CONTROL (unaffected)** — the SAME turn with NO umem witness mints the BARE wide
//!    cap-open leg (verifies under the bare wide member, NOT the welded one) — so a cap turn that does
//!    not opt in is byte-for-byte the deployed default.
//!
//! Requires `prover`. Self-skips under `not(prover)`.

#![cfg(feature = "prover")]

use dregg_circuit::cap_root::CapLeaf;
use dregg_circuit::effect_vm::trace_rotated::{
    CapOpenWitness, FACET_MASK_HI, SIGNATURE_AUTH_TAG, WRITE_MASK_LO,
};
use dregg_circuit::effect_vm::{CellState, Effect as VmEffect};
use dregg_circuit::effect_vm_descriptors::{WIDE_REGISTRY_STAGED_TSV, WIDE_UMEM_WELD_REGISTRY_TSV};
use dregg_circuit::field::BabyBear;
use dregg_circuit::heap_root::HeapLeaf;
use dregg_sdk::full_turn_proof::{CapMembershipWitness, verify_effect_vm_rotated_with_cutover};
use dregg_sdk::{FullTurnWitness, RotationTurnWitness, UmemWeldWitness, prove_full_turn};
use dregg_turn::rotation_witness as rw;
use dregg_turn::umem::{UProjection, UVal, UmemOp, project_diff_ops, project_record_kernel_state};

const ATTENUATE_WELDED_KEY: &str = "attenuateCapOpenEffVmDescriptor2R24";

fn open_perms() -> dregg_cell::Permissions {
    dregg_cell::Permissions {
        send: dregg_cell::AuthRequired::None,
        receive: dregg_cell::AuthRequired::None,
        set_state: dregg_cell::AuthRequired::None,
        set_permissions: dregg_cell::AuthRequired::None,
        set_verification_key: dregg_cell::AuthRequired::None,
        increment_nonce: dregg_cell::AuthRequired::None,
        delegate: dregg_cell::AuthRequired::None,
        access: dregg_cell::AuthRequired::None,
    }
}

/// The shared attenuate fixture (mirrors `wide_umem_weld_domain2_gauntlet`): the circuit pre-state,
/// the single attenuate VM effect, the before/after rotation witnesses, the consumed-cap membership
/// witness, and the GENUINE caps-domain projection diff (a single `CapSlot` insert — caps-only).
#[allow(clippy::type_complexity)]
fn attenuate_fixture() -> (
    CellState,
    Vec<VmEffect>,
    RotationTurnWitness,
    CapMembershipWitness,
    UProjection,
    Vec<UmemOp>,
) {
    let chosen: [BabyBear; 7] = [
        BabyBear::new(0xA11CE),
        BabyBear::new(7_777),
        BabyBear::new(SIGNATURE_AUTH_TAG),
        BabyBear::new(WRITE_MASK_LO),
        BabyBear::new(FACET_MASK_HI),
        BabyBear::new(0x00FF_FFFF),
        BabyBear::new(42),
    ];
    let other: [BabyBear; 7] = [
        BabyBear::new(0xBEEF),
        BabyBear::new(123),
        BabyBear::new(1),
        BabyBear::new(1),
        BabyBear::new(0),
        BabyBear::new(9),
        BabyBear::new(0),
    ];
    let open = CapOpenWitness::build(&[other, chosen], 1).expect("cap-open witness builds");
    let held_mask = BabyBear::new(0xFF);
    let clist_leaves = vec![
        HeapLeaf {
            addr: chosen[0],
            value: held_mask,
        },
        HeapLeaf {
            addr: other[0],
            value: other[3],
        },
    ];
    let cap = CapMembershipWitness {
        leaf: CapLeaf {
            slot_hash: chosen[0],
            target: chosen[1],
            auth_tag: chosen[2],
            mask_lo: chosen[3],
            mask_hi: chosen[4],
            expiry: chosen[5],
            breadstuff: chosen[6],
        },
        siblings: open.siblings.to_vec(),
        directions: open.directions.to_vec(),
        clist_leaves,
        cap_leaves: Vec::new(),
        cap_tombstones: Vec::new(),
    };

    let before_balance: u64 = 100_000;
    let initial = CellState::new(before_balance, 0);
    let effects = vec![VmEffect::AttenuateCapability {
        cap_slot_hash: [BabyBear::new(0x51); 8],
        narrower_commitment: [BabyBear::new(0x52); 8],
        phase_b: None,
    }];

    let mut pk = [0u8; 32];
    pk[0] = 7;
    let mut before_cell = dregg_cell::Cell::with_balance(pk, [0u8; 32], before_balance as i64);
    before_cell.permissions = open_perms();
    let mut after_cell = before_cell.clone();
    let target = {
        let mut tpk = [0u8; 32];
        tpk[0] = 200;
        dregg_cell::Cell::with_balance(tpk, [0u8; 32], 0).id()
    };
    after_cell
        .capabilities
        .grant(target, dregg_cell::AuthRequired::None)
        .expect("grant a cap slot (the genuine caps-domain change the umem leg reconciles)");

    let mut ledger = dregg_cell::Ledger::new();
    ledger.insert_cell(after_cell.clone()).unwrap();
    let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32], [4u8; 32]];
    let before_w = rw::produce(
        &before_cell,
        &ledger,
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &receipt_log,
        &Default::default(),
    );
    let after_w = rw::produce(
        &after_cell,
        &ledger,
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &receipt_log,
        &Default::default(),
    );
    let rot = RotationTurnWitness::for_effects(before_w, after_w, &effects);

    let proj_pre = project_record_kernel_state(&before_cell);
    let proj_post = project_record_kernel_state(&after_cell);
    let ops = project_diff_ops(&proj_pre, &proj_post);
    assert_eq!(ops.len(), 1, "the attenuate caps diff is a single op");
    assert_eq!(
        ops[0].key.domain(),
        dregg_turn::umem::UDomain::Caps,
        "the welded leg reconciles the CAPS domain (domain 2)"
    );
    (initial, effects, rot, cap, proj_pre, ops)
}

fn witness(
    initial: &CellState,
    effects: &[VmEffect],
    rot: RotationTurnWitness,
    cap: CapMembershipWitness,
    umem_witness: Option<UmemWeldWitness>,
) -> FullTurnWitness {
    FullTurnWitness {
        initial_cell_state: initial.clone(),
        effects: effects.to_vec(),
        membership: None,
        conservation: None,
        non_revocation: None,
        cap_membership: Some(cap),
        turn_hash: [0xC2u8; 32],
        rotation: Some(rot),
        cap_turn_identity: None,
        umem_witness,
    }
}

fn member_json(registry: &'static str, key: &str) -> &'static str {
    registry
        .lines()
        .find_map(|l| {
            let mut it = l.splitn(3, '\t');
            if it.next() == Some(key) {
                let _name = it.next();
                it.next()
            } else {
                None
            }
        })
        .expect("registry member present")
}

/// The `"effect-vm-rotated"` leg of a composed full-turn proof: `(proof_bytes, pis, vk_hash)`.
fn rotated_leg(proof: &dregg_sdk::FullTurnProof) -> (Vec<u8>, Vec<BabyBear>, [u8; 32]) {
    let leg = proof
        .composed
        .sub_proofs
        .iter()
        .find(|sp| sp.label == "effect-vm-rotated")
        .expect("the composed proof carries the effect-vm-rotated leg");
    (
        leg.proof_bytes.clone(),
        leg.sub_public_inputs.clone(),
        leg.vk_hash,
    )
}

#[test]
fn domain2_producer_routes_welded_through_prove_full_turn() {
    let (initial, effects, rot, cap, proj_pre, ops) = attenuate_fixture();

    // THE WELDED ROUTE: thread the CAPS umem witness → `prove_full_turn` routes the cap-open run
    // through the WELDED producer. PANIC (`.expect`) if the welded mint fails — no silent fallback.
    let uw = UmemWeldWitness {
        pre: proj_pre.clone(),
        ops: ops.clone(),
    };
    let proof = prove_full_turn(&witness(&initial, &effects, rot, cap.clone(), Some(uw))).expect(
        "the DOMAIN-2 cap-gated turn MUST mint the WIDE cap-open+umem WELDED leg through the \
                 shared prove_full_turn path (the producer seam the 12th catch named)",
    );
    assert!(
        proof.components.has_cap_membership,
        "the cap-membership leg is composed alongside the welded cap-open leg"
    );

    let (leg_bytes, leg_pis, leg_vk) = rotated_leg(&proof);

    // THE LEG IS WELDED: it verifies through the deployed wire verifier UNDER the welded-twin member,
    // and its vk_hash PINS the welded member (a silent bare-fallback would pin the bare member instead
    // — this assertion makes that a LOUD failure).
    verify_effect_vm_rotated_with_cutover(&leg_bytes, &leg_pis, &leg_vk)
        .expect("the welded cap-open leg MUST verify through the deployed wire verifier");
    let welded_vk: [u8; 32] =
        *blake3::hash(member_json(WIDE_UMEM_WELD_REGISTRY_TSV, ATTENUATE_WELDED_KEY).as_bytes())
            .as_bytes();
    assert_eq!(
        leg_vk, welded_vk,
        "PRODUCER SEAM: the routed leg MUST be the WELDED cap-open member (its vk_hash pins the \
         welded twin) — a bare-fallback would silently downgrade the umem reconciliation"
    );

    // THE ~124-BIT BINDING TOOTH: a forged 8-felt commit felt is rejected by the wire verifier.
    let mut forged = leg_pis.clone();
    let n = forged.len();
    forged[n - 1] = forged[n - 1] + BabyBear::new(0x7777);
    assert!(
        verify_effect_vm_rotated_with_cutover(&leg_bytes, &forged, &leg_vk).is_err(),
        "a forged 8-felt commit felt MUST be rejected (the ~124-bit anchor binds on the welded form)"
    );
}

#[test]
fn domain2_producer_bare_control_is_unaffected() {
    let (initial, effects, rot, cap, _proj_pre, _ops) = attenuate_fixture();

    // BARE CONTROL: NO umem witness → the deployed-default BARE wide cap-open leg. It verifies under
    // the BARE wide member (NOT the welded one) — the cap turn that does not opt in is unchanged.
    let proof = prove_full_turn(&witness(&initial, &effects, rot, cap, None))
        .expect("the bare wide cap-open leg proves (the deployed default)");
    let (leg_bytes, leg_pis, leg_vk) = rotated_leg(&proof);
    verify_effect_vm_rotated_with_cutover(&leg_bytes, &leg_pis, &leg_vk)
        .expect("the bare wide cap-open leg verifies through the deployed wire verifier");
    let bare_vk: [u8; 32] =
        *blake3::hash(member_json(WIDE_REGISTRY_STAGED_TSV, ATTENUATE_WELDED_KEY).as_bytes())
            .as_bytes();
    assert_eq!(
        leg_vk, bare_vk,
        "the no-witness control MUST pin the BARE wide member (deployed default unaffected)"
    );
    let welded_vk: [u8; 32] =
        *blake3::hash(member_json(WIDE_UMEM_WELD_REGISTRY_TSV, ATTENUATE_WELDED_KEY).as_bytes())
            .as_bytes();
    assert_ne!(
        leg_vk, welded_vk,
        "the no-witness control must NOT have welded (the welded form is opt-in via the witness)"
    );
}

/// THE FORGE TOOTH (caps anti-forge): a threaded witness whose claimed committed `prev_val` disagrees
/// with the genuine pre-state projection makes the offline universal-memory multiset inconsistent, so
/// `prove_full_turn` REFUSES (the welded routing fails CLOSED — never silently bare).
#[test]
fn domain2_producer_forged_caps_prev_refuses() {
    let (initial, effects, rot, cap, proj_pre, ops) = attenuate_fixture();
    let mut forged = ops.clone();
    forged[0].prev_val = Some(UVal::Present);
    let uw = UmemWeldWitness {
        pre: proj_pre,
        ops: forged,
    };
    let r = prove_full_turn(&witness(&initial, &effects, rot, cap, Some(uw)));
    assert!(
        r.is_err(),
        "a forged committed caps prev-state MUST refuse on the welded routing (fail-closed, not a \
         silent bare downgrade)"
    );
}
