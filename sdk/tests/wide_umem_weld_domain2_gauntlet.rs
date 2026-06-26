//! # THE DOMAIN-2 (CAPABILITY) WIDE CAP-OPEN+UMEM WELD GAUNTLET (STAGED, VK-RISK-FREE) — the 7th
//! flip-refusal's wall CLOSED.
//!
//! The sibling [`wide_umem_weld_staged_gauntlet`] bites the VALUE-cohort weld (the umem leg welded
//! onto a PLAIN wide descriptor — transfer, domain-1 heap). THIS gauntlet bites the first DOMAIN-2
//! (capability) welded mint: a real `AttenuateCapability` turn proved through ONE descriptor that
//! carries BOTH the WIDE cap-open cohort proof (the rotated effect semantics + the **in-circuit
//! depth-16 cap-membership authority crown** the light-client wire DEMANDS + the 8-felt / ~124-bit
//! commit at the leg's tail) AND the universal-memory CAPS-domain reconciliation leg, via the staged
//! SDK entry [`dregg_sdk::full_turn_proof::prove_cap_open_umem_welded_staged`].
//!
//! ## Why the value-cohort weld could not do this (the 7th refusal's wall)
//!
//! The value-cohort weld ([`prove_wide_umem_welded_staged`]) resolves the PLAIN wide descriptor for a
//! cap effect (e.g. `attenuateVmDescriptor2R24`). The light-client wire verifier
//! ([`verify_effect_vm_rotated_with_cutover`]) FORBIDS those plain cap descriptors
//! (`is_forbidden_plain_cap_descriptor`): a cap effect proven WITHOUT the membership crown launders
//! host-trusted authority. So a welded grant under the plain descriptor self-verifies but the WIRE
//! REJECTS it (see [`domain2_plain_cap_weld_is_wire_forbidden`]). The 7th refusal's
//! `OodEvaluationMismatch` was a SEPARATE witness inconsistency (a spurious Heap-domain nonce op made
//! the projection diff multi-domain — the single-domain cohort fails closed). The genuine wall is the
//! forbidden-plain-cap wire tooth. This prover routes through the cap-open WIDE descriptor and welds
//! the caps leg onto THAT — the descriptor the welded registry carries a wire-accepted twin of
//! (`attenuateCapOpenEffVmDescriptor2R24`, domain 2 / caps).
//!
//! ## What this proves
//!
//! 1. **CONTROL** — the welded WIDE cap-open descriptor proves a real attenuate turn (the membership
//!    crown + the universal-memory CAPS reconciliation, one proof) and SELF-verifies.
//! 2. **THE WIRE LEG (the 7th wall closed)** — the welded proof verifies through the DEPLOYED wire
//!    verifier under the Lean-emitted welded-twin `attenuateCapOpenEffVmDescriptor2R24` member of
//!    [`WIDE_UMEM_WELD_REGISTRY_TSV`] — a domain-2 member accepted as a STAGED form beside the bare.
//! 3. **THE ~124-BIT BINDING TOOTH** — tampering one of the welded leg's last-16 PIs (a forged 8-felt
//!    commit felt) makes the wire verifier REJECT (the wide carrier PiBindings ride the weld).
//! 4. **THE vk_hash TOOTH** — a tampered welded-member vk_hash is rejected.
//! 5. **THE UMEM CAPS ANTI-FORGE TOOTH** — a forged caps umem op (its claimed committed `prev_val`
//!    disagrees with the genuine pre-state projection) makes the offline universal-memory multiset
//!    inconsistent at the boundary, so the prover REFUSES.
//! 6. **THE CAPS-DOMAIN GUARD** — a non-caps (heap) umem op is refused (a capability cap-open weld
//!    must reconcile the CAPS domain).
//!
//! ## VK-RISK-FREE
//!
//! Pure ADDITIVE: only the STAGED welded WIDE cap-open descriptor
//! ([`dregg_circuit::effect_vm_descriptors::weld_umem_into_wide_descriptor`]) + the opt-in welded
//! cap-open prover; it touches no deployed descriptor JSON / VK / default prover, and never arms
//! `umem_witness_enabled`.
//!
//! Requires `prover`. Self-skips under `not(prover)`.

#![cfg(feature = "prover")]

use dregg_circuit::cap_root::CapLeaf;
use dregg_circuit::effect_vm::trace_rotated::{
    CapOpenWitness, FACET_MASK_HI, SIGNATURE_AUTH_TAG, WRITE_MASK_LO,
};
use dregg_circuit::effect_vm::{CellState, Effect as VmEffect};
use dregg_circuit::effect_vm_descriptors::WIDE_UMEM_WELD_REGISTRY_TSV;
use dregg_circuit::field::BabyBear;
use dregg_circuit::heap_root::HeapLeaf;
use dregg_sdk::full_turn_proof::{
    CapMembershipWitness, prove_cap_open_umem_welded_staged, prove_wide_umem_welded_staged,
    verify_effect_vm_rotated_with_cutover,
};
use dregg_turn::rotation_witness as rw;
use dregg_turn::umem::{UKey, UVal, UmemKind, UmemOp, project_record_kernel_state};

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

/// The pre→post projection DIFF as a Blum WRITE op trace (the effect's universal-memory touch).
fn ops_from_diff(
    pre: &dregg_turn::umem::UProjection,
    post: &dregg_turn::umem::UProjection,
) -> Vec<UmemOp> {
    let mut keys: Vec<&UKey> = pre.keys().chain(post.keys()).collect();
    keys.sort();
    keys.dedup();
    let mut ops = Vec::new();
    for k in keys {
        let a = pre.get(k);
        let b = post.get(k);
        if a != b {
            ops.push(UmemOp {
                kind: UmemKind::Write,
                key: k.clone(),
                val: b.cloned(),
                prev_val: a.cloned(),
                prev_serial: 0,
            });
        }
    }
    ops
}

/// The shared attenuate fixture: the consumed-cap membership witness, the rotation witnesses, the
/// circuit pre-state, the effect, and the GENUINE caps-domain projection diff (a `CapSlot` insert; NO
/// cell nonce tick — the VM ticks internally, so the projection diff stays caps-only / single-domain).
#[allow(clippy::type_complexity)]
fn attenuate_fixture() -> (
    CellState,
    Vec<VmEffect>,
    rw::RotationWitness,
    rw::RotationWitness,
    CapMembershipWitness,
    dregg_turn::umem::UProjection,
    Vec<UmemOp>,
) {
    // A FAITHFUL transfer-conferring leaf: auth_tag == Signature, mask_lo == EFFECT_TRANSFER, mask_hi
    // == 0; target == src. (Mirrors `cap_open_attenuate_leg_proves_and_verifies_end_to_end`.)
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
    // The attenuate map_op is an in-place UPDATE-AT-KEY: the held key must be present, its held mask
    // BROAD enough that the narrowed KEEP_MASK (0x52) is a submask (0x52 ⊑ 0xFF).
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
    let before_w = rw::produce(&before_cell, &ledger, &[0u8; 32], &[0u8; 32], &receipt_log);
    let after_w = rw::produce(&after_cell, &ledger, &[0u8; 32], &[0u8; 32], &receipt_log);

    let proj_pre = project_record_kernel_state(&before_cell);
    let proj_post = project_record_kernel_state(&after_cell);
    let ops = ops_from_diff(&proj_pre, &proj_post);
    assert_eq!(
        ops.len(),
        1,
        "the attenuate fixture's caps diff is a single op"
    );
    assert_eq!(
        ops[0].key.domain(),
        dregg_turn::umem::UDomain::Caps,
        "the welded leg reconciles the CAPS domain (domain 2)"
    );
    (initial, effects, before_w, after_w, cap, proj_pre, ops)
}

fn welded_member_json(key: &str) -> &'static str {
    WIDE_UMEM_WELD_REGISTRY_TSV
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
        .expect("welded member present in the Lean-emitted welded registry")
}

#[test]
fn domain2_attenuate_cap_open_weld_proves_and_verifies_through_wire() {
    let (initial, effects, before_w, after_w, cap, proj_pre, ops) = attenuate_fixture();

    // CONTROL: the welded WIDE cap-open descriptor PROVES the real attenuate turn (the depth-16
    // cap-membership crown + the universal-memory CAPS reconciliation, one proof) and self-verifies.
    let (welded_proof, welded_dpis) = prove_cap_open_umem_welded_staged(
        &initial, &effects, &before_w, &after_w, &cap, &proj_pre, &ops,
    )
    .expect("the welded WIDE cap-open+umem descriptor proves the genuine attenuate turn");

    // 8-FELT PRESERVED: the welded cap-open leg carries the wide cap-open PI vector (the membership
    // crown adds no PIs; the wide carriers add the 16 commit PIs / 8-felt anchors).
    assert!(
        welded_dpis.len() >= 16 + 38,
        "the welded cap-open attenuate leg carries the 38 base PIs + 16 wide commit PIs (got {})",
        welded_dpis.len()
    );

    // THE WIRE LEG (the 7th wall closed): the welded proof verifies through the DEPLOYED wire verifier
    // under the Lean-emitted welded-twin `attenuateCapOpenEffVmDescriptor2R24` member — a wire-ACCEPTED
    // (NOT forbidden-plain) cap-open descriptor that carries the in-circuit membership crown.
    let proof_bytes = postcard::to_allocvec(&welded_proof).expect("serialize welded cap-open leg");
    let vk_hash: [u8; 32] =
        *blake3::hash(welded_member_json(ATTENUATE_WELDED_KEY).as_bytes()).as_bytes();
    verify_effect_vm_rotated_with_cutover(&proof_bytes, &welded_dpis, &vk_hash).expect(
        "the welded WIDE cap-open attenuate proof MUST verify through the deployed wire verifier under \
         the Lean-emitted welded-wide cap-open registry member (the staged DOMAIN-2 verifier leg)",
    );

    // THE ~124-BIT BINDING TOOTH on the WIRE: tampering a published 8-felt commit felt makes the wire
    // verifier REJECT (the welded member's wide PiBindings ride through the weld and bite on the wire).
    let mut forged_dpis = welded_dpis.clone();
    let n = forged_dpis.len();
    forged_dpis[n - 1] = forged_dpis[n - 1] + BabyBear::new(0x7777);
    assert!(
        verify_effect_vm_rotated_with_cutover(&proof_bytes, &forged_dpis, &vk_hash).is_err(),
        "a forged 8-felt commit felt MUST be rejected by the wire verifier (the ~124-bit anchor binds \
         on the welded cap-open form)"
    );

    // THE vk_hash TOOTH: a tampered welded-member vk_hash is rejected.
    let mut bad_vk = vk_hash;
    bad_vk[0] ^= 0xff;
    assert!(
        verify_effect_vm_rotated_with_cutover(&proof_bytes, &welded_dpis, &bad_vk).is_err(),
        "a tampered welded-member vk_hash MUST be rejected by the wire verifier"
    );
}

#[test]
fn domain2_attenuate_cap_open_weld_forged_caps_prev_refuses() {
    let (initial, effects, before_w, after_w, cap, proj_pre, ops) = attenuate_fixture();

    // THE UMEM CAPS ANTI-FORGE TOOTH: forge the caps op's claimed committed `prev_val` (the genuine
    // CapSlot insert has `prev_val: None`). The boundary init (derived from the genuine PRE) disagrees,
    // so the offline universal-memory multiset is inconsistent and the prover REFUSES.
    let mut forged = ops.clone();
    forged[0].prev_val = Some(UVal::Present);
    let r = prove_cap_open_umem_welded_staged(
        &initial, &effects, &before_w, &after_w, &cap, &proj_pre, &forged,
    );
    assert!(
        r.is_err(),
        "a forged committed caps prev-state must refuse on the welded WIDE cap-open+umem path"
    );
}

#[test]
fn domain2_cap_open_weld_non_caps_op_refuses() {
    let (initial, effects, before_w, after_w, cap, proj_pre, _ops) = attenuate_fixture();

    // THE CAPS-DOMAIN GUARD: a HEAP-domain op (a Balance change) is NOT a capability reconciliation —
    // the cap-open weld must reconcile the CAPS domain. Refused.
    let heap_op = UmemOp {
        kind: UmemKind::Write,
        key: UKey::Balance({
            let mut pk = [0u8; 32];
            pk[0] = 7;
            dregg_cell::Cell::with_balance(pk, [0u8; 32], 0).id()
        }),
        val: Some(UVal::Int(1)),
        prev_val: Some(UVal::Int(0)),
        prev_serial: 0,
    };
    let r = prove_cap_open_umem_welded_staged(
        &initial,
        &effects,
        &before_w,
        &after_w,
        &cap,
        &proj_pre,
        std::slice::from_ref(&heap_op),
    );
    assert!(
        r.is_err(),
        "a non-caps (heap) umem op must fail closed on the capability cap-open weld"
    );
}

/// **THE 7th REFUSAL'S WALL, DEMONSTRATED.** The PLAIN cap descriptor route (the value-cohort weld
/// `prove_wide_umem_welded_staged`) self-verifies BUT is REJECTED by the deployed wire verifier — a cap
/// effect proven without the in-circuit membership crown launders host-trusted authority. This is
/// exactly why the domain-2 welded mint MUST route through the cap-open descriptor (the test above).
#[test]
fn domain2_plain_cap_weld_is_wire_forbidden() {
    // A grant whose PLAIN wide base (`grantCapVmDescriptor2R24`) the value-cohort weld resolves. Its
    // caps projection diff is a genuine single-domain CapSlot insert. cap_entry ZERO keeps the plain
    // grant base's hash_2_to_1 cap_root model satisfiable (the point here is the WIRE rejection, not
    // the proof).
    let before_balance: u64 = 100_000;
    let initial = CellState::with_capability_root(
        before_balance,
        0,
        dregg_circuit::cap_root::empty_capability_root(),
    );
    let effects = vec![VmEffect::GrantCapability {
        cap_entry: [BabyBear::ZERO; 8],
        phase_b: None,
    }];

    let mut pk = [0u8; 32];
    pk[0] = 7;
    let mut before_cell = dregg_cell::Cell::with_balance(pk, [0u8; 32], before_balance as i64);
    before_cell.permissions = open_perms();
    let mut after_cell = before_cell.clone();
    let target = {
        let mut tpk = [0u8; 32];
        tpk[0] = 201;
        dregg_cell::Cell::with_balance(tpk, [0u8; 32], 0).id()
    };
    after_cell
        .capabilities
        .grant(target, dregg_cell::AuthRequired::None)
        .expect("grant a cap slot");

    let mut ledger = dregg_cell::Ledger::new();
    ledger.insert_cell(after_cell.clone()).unwrap();
    let before_w = rw::produce(&before_cell, &ledger, &[0u8; 32], &[0u8; 32], &[]);
    let after_w = rw::produce(&after_cell, &ledger, &[0u8; 32], &[0u8; 32], &[]);

    let proj_pre = project_record_kernel_state(&before_cell);
    let proj_post = project_record_kernel_state(&after_cell);
    let ops = ops_from_diff(&proj_pre, &proj_post);
    assert_eq!(ops[0].key.domain(), dregg_turn::umem::UDomain::Caps);

    let caveat = dregg_circuit::effect_vm::trace_rotated::empty_caveat_manifest();
    let (welded_proof, welded_dpis) = prove_wide_umem_welded_staged(
        &initial, &effects, &before_w, &after_w, &caveat, &proj_pre, &ops, None, None,
    )
    .expect("the PLAIN welded grant SELF-verifies (it carries no membership crown)");

    // The PLAIN grant welded twin exists in the registry — but the wire FORBIDS plain cap descriptors.
    let proof_bytes = postcard::to_allocvec(&welded_proof).expect("serialize plain welded grant");
    let vk_hash: [u8; 32] =
        *blake3::hash(welded_member_json("grantCapVmDescriptor2R24").as_bytes()).as_bytes();
    let r = verify_effect_vm_rotated_with_cutover(&proof_bytes, &welded_dpis, &vk_hash);
    assert!(
        r.is_err(),
        "the PLAIN welded grant MUST be REJECTED by the wire verifier (forbidden plain cap descriptor \
         — host-trusted authority is not light-client-verifiable); the cap-open route is required"
    );
    let msg = format!("{r:?}");
    assert!(
        msg.contains("cap") || msg.contains("forbidden") || msg.contains("membership"),
        "the rejection names the cap-open requirement, got: {msg}"
    );
}
