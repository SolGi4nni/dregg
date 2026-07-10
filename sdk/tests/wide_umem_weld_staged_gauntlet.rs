//! # THE WIDE+UMEM WELD GAUNTLET (STAGED, VK-RISK-FREE) — the genuine flip precursor the VK epoch
//! needs.
//!
//! The sibling [`rotated_umem_weld_staged_gauntlet`] bites the NARROW weld (the umem leg welded onto
//! the 1-felt / 46-PI rotated descriptor — a correct staging artifact, but flipping the deployed
//! WIDE wire onto it would NARROW the ~124-bit commitment to ~46-bit, the no-narrowing scar). THIS
//! gauntlet bites the WIDE weld: a REAL turn proved through ONE descriptor that carries BOTH the
//! whole WIDE rotated cohort proof (the 8-felt / ~124-bit faithful commit, the 16 wide commit PIs at
//! the leg's tail) AND the universal-memory reconciliation leg, via the staged SDK entry
//! [`dregg_sdk::full_turn_proof::prove_wide_umem_welded_staged`].
//!
//! ## What this proves (the WIDE weld, 8-felt preserved)
//!
//! 1. **CONTROL** — the welded WIDE descriptor proves a real transfer-out (rotated semantics + the
//!    universal-memory Balance reconciliation, one proof).
//! 2. **8-FELT PRESERVED (the no-narrowing property)** — the welded leg's published PI vector is
//!    BYTE-IDENTICAL to the wide-only leg's over the SAME transition (the weld appends 0 PIs), so the
//!    LAST 16 PIs — the 8-felt before/after commits `verify_full_turn_bound` binds — are UNCHANGED.
//!    The welded descriptor's `public_input_count` equals the wide descriptor's, and every wide
//!    `PiBinding` survives the weld. The welded leg's 8-felt commits equal the trusted
//!    `wide_commit_anchors` (the SAME ~124-bit anchor the light-client verifier binds).
//! 3. **THE ~124-BIT BINDING TOOTH** — tampering ONE of the welded leg's last-16 PIs (a forged
//!    8-felt commit felt) makes the welded proof FAIL `verify_vm_descriptor2`: the wide carrier
//!    `PiBinding`s ride through the additive weld and bite on the welded form exactly as on the wide
//!    form. So the welded form keeps the full ~124-bit commitment — no narrowing.
//! 4. **THE UMEM ANTI-FORGE TOOTH** — a forged umem op (its claimed committed `prev_val` disagrees
//!    with the genuine pre-state projection) makes the offline universal-memory multiset inconsistent
//!    at the boundary, so the prover REFUSES.
//! 5. **FAIL-CLOSED** — a non-rotated-cohort effect has no welded descriptor and refuses.
//!
//! ## VK-RISK-FREE
//!
//! Pure ADDITIVE: only the STAGED welded WIDE descriptor
//! ([`dregg_circuit::effect_vm_descriptors::weld_umem_into_wide_descriptor`]) + the opt-in welded
//! prover; it touches no deployed descriptor JSON / VK / default prover, and never arms
//! `umem_witness_enabled`. The deployed default stays its current path until the gated VK epoch.
//!
//! Requires `prover`. Self-skips under `not(prover)`.

#![cfg(feature = "prover")]

use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
use dregg_circuit::descriptor_ir2::{VmConstraint2, parse_vm_descriptor2, verify_vm_descriptor2};
use dregg_circuit::effect_vm::trace_rotated::{
    rotated_descriptor_name_for_effect, transfer_caveat_manifest,
};
use dregg_circuit::effect_vm::{CellState, Effect as VmEffect};
use dregg_circuit::effect_vm_descriptors::{
    WIDE_REGISTRY_STAGED_TSV, WIDE_UMEM_WELD_REGISTRY_TSV, weld_umem_into_wide_descriptor,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::VmConstraint;
use dregg_sdk::full_turn_proof::{
    RotationTurnWitness, prove_effect_vm_rotated_wide, prove_wide_umem_welded_staged,
    verify_effect_vm_rotated_with_cutover,
};
use dregg_turn::rotation_witness as rw;
use dregg_turn::umem::{
    UKey, UVal, UmemKind, UmemOp, project_record_kernel_state, record_kernel_boundary_agrees,
};

fn open_permissions() -> Permissions {
    Permissions {
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

fn producer_cell(balance: i64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = 7;
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    cell
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

/// Build the (before_w, after_w, proj_pre, ops, st, effects) for a real transfer-out.
#[allow(clippy::type_complexity)]
fn transfer_fixture(
    before_balance: i64,
    amount: u64,
) -> (
    rw::RotationWitness,
    rw::RotationWitness,
    dregg_turn::umem::UProjection,
    Vec<UmemOp>,
    CellState,
    Vec<VmEffect>,
) {
    let st = CellState::new(before_balance as u64, 0);
    let effects = vec![VmEffect::Transfer {
        amount,
        direction: 1,
    }];
    let before_cell = producer_cell(before_balance);
    let after_cell = producer_cell(before_balance - amount as i64);

    let mut ledger = Ledger::new();
    ledger.insert_cell(after_cell.clone()).unwrap();
    let receipt_log: Vec<[u8; 32]> = vec![[1u8; 32], [2u8; 32]];
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

    record_kernel_boundary_agrees(&before_cell)
        .unwrap_or_else(|e| panic!("PRE projection must agree with per-map roots: {e}"));
    let proj_pre = project_record_kernel_state(&before_cell);
    let proj_post = project_record_kernel_state(&after_cell);
    let ops = ops_from_diff(&proj_pre, &proj_post);
    assert!(
        !ops.is_empty(),
        "the transfer must touch the universal memory"
    );
    (before_w, after_w, proj_pre, ops, st, effects)
}

#[test]
fn wide_umem_welded_transfer_proves_and_preserves_8felt() {
    let (before_w, after_w, proj_pre, ops, st, effects) = transfer_fixture(100_000, 50);
    let caveat = transfer_caveat_manifest();

    // CONTROL: the welded WIDE descriptor PROVES the real turn (wide rotated semantics + the
    // universal-memory reconciliation, one proof). Returns (proof, wide_dpis).
    let (welded_proof, welded_dpis) = prove_wide_umem_welded_staged(
        &st, &effects, &before_w, &after_w, &caveat, &proj_pre, &ops, None, None,
    )
    .expect("the welded WIDE+umem descriptor proves the genuine transfer turn");

    // The wide-ONLY leg over the SAME transition (the deployed wide producer leg).
    let (_wide_proof, wide_dpis) =
        prove_effect_vm_rotated_wide(&st, &effects, &before_w, &after_w, &caveat, None, None)
            .expect("the deployed wide leg proves");

    // 8-FELT PRESERVED: the weld appends ZERO PIs — the welded leg's whole PI vector is
    // byte-identical to the wide-only leg's, so the LAST 16 PIs (the 8-felt before/after commits
    // `verify_full_turn_bound` binds) are UNCHANGED. NO narrowing.
    assert_eq!(
        welded_dpis, wide_dpis,
        "the WIDE+umem weld must publish the SAME PI vector as the wide-only leg (0 PIs appended) — \
         the 8-felt commit is preserved"
    );
    assert!(
        welded_dpis.len() >= 16 + 46,
        "the welded WIDE transfer leg carries the 46 base PIs + 16 wide commit PIs (got {})",
        welded_dpis.len()
    );

    // The trusted 8-felt anchors the light-client verifier binds, re-derived GENERATE-ONLY.
    let rot = RotationTurnWitness {
        before: before_w.clone(),
        after: after_w.clone(),
        caveat: caveat.clone(),
    };
    let (old8, new8) = rot
        .wide_commit_anchors(&st, &effects, None)
        .expect("wide_commit_anchors");
    let n = welded_dpis.len();
    let leg_before8: [BabyBear; 8] = welded_dpis[n - 16..n - 8].try_into().unwrap();
    let leg_after8: [BabyBear; 8] = welded_dpis[n - 8..n].try_into().unwrap();
    assert_eq!(
        leg_before8, old8,
        "the welded leg's published BEFORE 8-felt commit == the trusted wide_commit_anchors BEFORE"
    );
    assert_eq!(
        leg_after8, new8,
        "the welded leg's published AFTER 8-felt commit == the trusted wide_commit_anchors AFTER"
    );

    // STRUCTURAL: the welded descriptor preserves the wide descriptor's PI count + every PiBinding.
    let name = rotated_descriptor_name_for_effect(&effects[0]).unwrap();
    let wide_json = WIDE_REGISTRY_STAGED_TSV
        .lines()
        .find_map(|l| {
            let mut it = l.splitn(3, '\t');
            if it.next() == Some(name) {
                let _display = it.next();
                it.next()
            } else {
                None
            }
        })
        .expect("wide member present");
    let wide_desc = parse_vm_descriptor2(wide_json).unwrap();
    let welded_desc = weld_umem_into_wide_descriptor(&wide_desc, 1);
    assert_eq!(
        welded_desc.public_input_count, wide_desc.public_input_count,
        "the weld must NOT change public_input_count (the 8-felt PIs stay at the same offsets)"
    );
    let pibinds = |d: &dregg_circuit::descriptor_ir2::EffectVmDescriptor2| -> Vec<(usize, usize)> {
        d.constraints
            .iter()
            .filter_map(|c| match c {
                VmConstraint2::Base(VmConstraint::PiBinding { col, pi_index, .. }) => {
                    Some((*col, *pi_index))
                }
                _ => None,
            })
            .collect()
    };
    let wide_pibinds = pibinds(&wide_desc);
    let welded_pibinds = pibinds(&welded_desc);
    for pb in &wide_pibinds {
        assert!(
            welded_pibinds.contains(pb),
            "every wide PiBinding {pb:?} (incl. the 16 wide-commit anchors) must survive the weld"
        );
    }
    assert_eq!(
        wide_pibinds, welded_pibinds,
        "the weld appends NO PiBinding and drops none — the 8-felt commit binding is identical"
    );

    // THE ~124-BIT BINDING TOOTH: forge ONE of the welded leg's last-16 PIs (an 8-felt commit felt).
    // The wide carrier PiBinding rides through the weld, so the welded proof no longer verifies
    // against the tampered PI vector — the welded form binds the FULL ~124-bit commitment.
    let mut forged_dpis = welded_dpis.clone();
    let forge_at = n - 1; // the AFTER commit's last felt.
    forged_dpis[forge_at] = forged_dpis[forge_at] + BabyBear::new(0x7777);
    assert!(
        verify_vm_descriptor2(&welded_desc, &welded_proof, &forged_dpis).is_err(),
        "a forged 8-felt commit felt MUST make the welded WIDE proof UNSAT — the ~124-bit anchor \
         binds on the welded form (no narrowing)"
    );
    // (And the honest PI vector still verifies — sanity that the tooth is the forgery, not the weld.)
    verify_vm_descriptor2(&welded_desc, &welded_proof, &welded_dpis)
        .expect("the honest welded WIDE proof verifies against its true PI vector");
}

/// **THE VERIFIER LEG — RE-POINTED OFF SELF-VERIFY (the flip's last real precursor).** The welded
/// proof now verifies through the DEPLOYED WIRE VERIFIER `verify_effect_vm_rotated_with_cutover`
/// (the light-client rotated-leg path that iterates the registries), NOT against the descriptor it
/// just built. This is the missing verifier leg: a welded proof verifies under a DEPLOYED (Lean-
/// emitted, byte-pinned) descriptor — the `WIDE_UMEM_WELD_REGISTRY_TSV` member — as a STAGED accepted
/// form beside the bare wide registry. The 8-felt anchors stay bound (the tooth below), the deployed
/// bare default is untouched.
#[test]
fn wide_umem_welded_transfer_verifies_through_wire_verifier() {
    let (before_w, after_w, proj_pre, ops, st, effects) = transfer_fixture(100_000, 50);
    let caveat = transfer_caveat_manifest();

    let (welded_proof, welded_dpis) = prove_wide_umem_welded_staged(
        &st, &effects, &before_w, &after_w, &caveat, &proj_pre, &ops, None, None,
    )
    .expect("the welded WIDE+umem descriptor proves the genuine transfer turn");

    // The DEPLOYED wire verifier consumes the serialized proof + the published PI vector + the leg's
    // vk_hash. The vk_hash is the blake3 fingerprint of the accepting registry member's committed JSON
    // (the SAME fingerprint `verify_effect_vm_rotated_with_cutover` re-derives from the uniquely-
    // accepting descriptor). For the welded transfer that member is the welded twin of
    // `transferVmDescriptor2R24` in the Lean-emitted `WIDE_UMEM_WELD_REGISTRY_TSV`.
    let proof_bytes = postcard::to_allocvec(&welded_proof).expect("serialize welded leg");
    let welded_json = WIDE_UMEM_WELD_REGISTRY_TSV
        .lines()
        .find_map(|l| {
            let mut it = l.splitn(3, '\t');
            if it.next() == Some("transferVmDescriptor2R24") {
                let _name = it.next();
                it.next()
            } else {
                None
            }
        })
        .expect("the welded transfer member is in the Lean-emitted welded registry");
    let vk_hash: [u8; 32] = *blake3::hash(welded_json.as_bytes()).as_bytes();

    // THE RE-POINT: verifies through the REAL wire path (not self-verify).
    verify_effect_vm_rotated_with_cutover(&proof_bytes, &welded_dpis, &vk_hash).expect(
        "the welded WIDE transfer proof MUST verify through the deployed wire verifier under the \
         Lean-emitted welded-wide registry member (the staged verifier leg)",
    );

    // THE 8-FELT BINDING TOOTH on the WIRE: tampering a published 8-felt commit felt makes the wire
    // verifier REJECT (the welded member's wide PiBindings ride through the weld and bite on the wire).
    let mut forged_dpis = welded_dpis.clone();
    let n = forged_dpis.len();
    forged_dpis[n - 1] = forged_dpis[n - 1] + BabyBear::new(0x7777);
    assert!(
        verify_effect_vm_rotated_with_cutover(&proof_bytes, &forged_dpis, &vk_hash).is_err(),
        "a forged 8-felt commit felt MUST be rejected by the wire verifier (the ~124-bit anchor binds)"
    );

    // THE vk_hash TOOTH: a tampered vk_hash (descriptor-identity metadata) is rejected even though the
    // proof itself is selector-bound.
    let mut bad_vk = vk_hash;
    bad_vk[0] ^= 0xff;
    assert!(
        verify_effect_vm_rotated_with_cutover(&proof_bytes, &welded_dpis, &bad_vk).is_err(),
        "a tampered welded-member vk_hash MUST be rejected by the wire verifier"
    );
}

#[test]
fn wide_umem_welded_forged_pre_refuses() {
    let (before_w, after_w, proj_pre, ops, st, effects) = transfer_fixture(100_000, 50);
    let caveat = transfer_caveat_manifest();

    let mut forged = ops.clone();
    forged[0].prev_val = match &forged[0].prev_val {
        Some(UVal::Int(v)) => Some(UVal::Int(v + 1)),
        Some(_) => Some(UVal::Int(123_456)),
        None => Some(UVal::Int(1)),
    };
    let r = prove_wide_umem_welded_staged(
        &st, &effects, &before_w, &after_w, &caveat, &proj_pre, &forged, None, None,
    );
    assert!(
        r.is_err(),
        "a forged committed pre-state must refuse on the welded WIDE+umem path"
    );
}

#[test]
fn wide_umem_welded_non_cohort_refuses() {
    let before_balance: i64 = 100_000;
    let st = CellState::new(before_balance as u64, 0);
    let before_cell = producer_cell(before_balance);
    let mut ledger = Ledger::new();
    ledger.insert_cell(before_cell.clone()).unwrap();
    let before_w = rw::produce(
        &before_cell,
        &ledger,
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &[],
        &Default::default(),
    );
    let proj = project_record_kernel_state(&before_cell);
    let op = UmemOp {
        kind: UmemKind::Write,
        key: UKey::Balance(before_cell.id()),
        val: Some(UVal::Int(1)),
        prev_val: Some(UVal::Int(0)),
        prev_serial: 0,
    };
    let r = prove_wide_umem_welded_staged(
        &st,
        &[VmEffect::IncrementNonce],
        &before_w,
        &before_w,
        &transfer_caveat_manifest(),
        &proj,
        &[op],
        None,
        None,
    );
    assert!(
        r.is_err(),
        "a non-cohort effect must fail closed on the welded WIDE+umem path"
    );
}
