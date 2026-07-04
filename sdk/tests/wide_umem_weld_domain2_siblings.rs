//! # THE DOMAIN-2 CAP-EFFECT SIBLING GAUNTLET — every welded cap-open twin proven END-TO-END
//! (mint → wire-verify → executor-commit), EMPIRICALLY, not "shares the code path".
//!
//! [`executor_cap_open_welded_commit`] proved the FIRST domain-2 family (`AttenuateCapability`) through
//! all three surfaces (producer mint · deployed wire verifier · `TurnExecutor::execute` commit). The
//! remaining domain-2 cap families route — with the cell's full c-list threaded — to their WRITE-bearing
//! cap-open wrapper, whose welded twin now lives in
//! [`WIDE_UMEM_WELD_REGISTRY_TSV`](dregg_circuit::effect_vm_descriptors::WIDE_UMEM_WELD_REGISTRY_TSV):
//!
//!   * `GrantCapability` (delegate / grantCap)  → `delegateWriteCapOpenVmDescriptor2R24`
//!   * `Introduce`                              → `introduceWriteCapOpenVmDescriptor2R24`
//!   * `RefreshDelegation`                      → `refreshDelegationWriteCapOpenVmDescriptor2R24`
//!   * `RevokeCapability`                       → `revokeCapabilityWriteCapOpenVmDescriptor2R24`
//!   * `RevokeDelegation`                       → `revokeDelegationWriteCapOpenVmDescriptor2R24`
//!
//! were only ASSERTED mechanically-covered by the shared cap-open route. This gauntlet MINTS each one,
//! WIRE-VERIFIES it through `verify_effect_vm_rotated_with_cutover` under its Lean-emitted welded twin,
//! and COMMITS it through the DEPLOYED `TurnExecutor::execute`, with the ~124-bit anchor + vk_hash teeth
//! biting on each surface. (`SpawnWithDelegation` has no welded twin in the registry — its cap-open is a
//! live-only member — so it is naturally skipped.)
//!
//! ## The route these siblings take (vs attenuate)
//!
//! `AttenuateCapability` is special: its write-bearing wrapper IS its authority key
//! (`attenuateCapOpenEffVmDescriptor2R24`, position 43 of `v3RegistryCapOpenWide`), so the attenuate
//! fixture's non-empty c-list (the `Update` write route) resolves a key ALREADY in the 45 welded crown
//! members. The OTHER cap families' write wrappers (`delegateWriteCapOpen…`, `introduceWriteCapOpen…`,
//! `revokeDelegationWriteCapOpen…`, …) are the §10 WRITE-bearing tail (`v3RegistryCapOpenWriteWide`):
//! they DO carry proven WIDE twins (`cap_open_key_has_wide_twin` is true), but their WELDED twins were
//! the missing verifier leg — so a welded WIDE write-route mint verified under NO cohort descriptor.
//! This lane WELDS the §10 write tail into the Lean-emitted welded registry (the byte source
//! `EmitWideUMemWeldRegistryProbe.lean`, FP-pinned), so each sibling's genuine WRITE route — the
//! `…WriteCapOpen…` wrapper whose `map_op` binds the post-cap-root on-the-wire (the depth-16 membership
//! crown AND the cap-tree write both in-circuit, NOT host-trusted) — now resolves a welded twin and
//! verifies end-to-end.
//!
//! ## STAGED / VK-RISK-FREE
//! Purely additive: the welded WIDE cap-open descriptors + the opt-in welded prover; no deployed
//! descriptor / VK / default prover touched, `umem_witness_enabled` untouched.
//!
//! Requires `prover`; self-skips under `not(prover)`.

#![cfg(feature = "prover")]

use dregg_cell::CapabilityRef;
use dregg_cell::commitment::{compute_canonical_capability_root_felt, felt8_to_bytes32};
use dregg_cell::{Cell, CellId, CellMode, Ledger};
use dregg_circuit::cap_root::CapLeaf;
use dregg_circuit::effect_vm::Effect as VmEffect;
use dregg_circuit::effect_vm::trace_rotated::{CapOpenWitness, SIGNATURE_AUTH_TAG};
use dregg_circuit::effect_vm_descriptors::WIDE_UMEM_WELD_REGISTRY_TSV;
use dregg_circuit::field::BabyBear;
use dregg_circuit::heap_root::HeapLeaf;
use dregg_sdk::AgentCipherclerk;
use dregg_sdk::full_turn_proof::{
    CapMembershipWitness, prove_cap_open_umem_welded_staged, verify_effect_vm_rotated_with_cutover,
};
use dregg_turn::rotation_witness as rw;
use dregg_turn::umem::{UKey, UmemKind, UmemOp, project_record_kernel_state};
use dregg_turn::{ComputronCosts, Effect, Turn, TurnExecutor, TurnResult};

// ---- shared scaffolding (mirrors `executor_cap_open_welded_commit`) -------------------------------

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

fn proof_carrying_turn(
    cell_id: CellId,
    effects: Vec<Effect>,
    proof_bytes: Vec<u8>,
    new: [u8; 32],
) -> Turn {
    let mut forest = dregg_turn::forest::CallForest::new();
    forest.add_root(dregg_sdk::raw::unsigned_action_named(
        cell_id,
        "sovereign_execute_proven",
        effects,
    ));
    Turn {
        agent: cell_id,
        nonce: 0,
        call_forest: forest,
        fee: 0,
        memo: None,
        valid_until: None,
        previous_receipt_hash: None,
        depends_on: Vec::new(),
        conservation_proof: None,
        sovereign_witnesses: Default::default(),
        execution_proof: Some(proof_bytes),
        execution_proof_cell: Some(cell_id),
        execution_proof_new_commitment: Some(new),
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    }
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

/// A BROAD honest cap leaf (`EFFECT_ALL` mask: `mask_lo = mask_hi = 0xFFFF`) the authority-crown
/// `from_membership_for` submask-membership accepts for ANY effect-kind bit. The c-list is the
/// 2-leaf sparse tree the cap-open witness opens; the chosen leaf is `target = src` (the
/// `targetBindGate` holds). The crown `effBit` column is the DESCRIPTOR's constant (the route's
/// `eff_bit`), not the mask — so a broad mask permits every fan-out crown facet.
fn broad_cap_witness() -> CapMembershipWitness {
    use dregg_circuit::cap_root::{CAP_TREE_DEPTH, CanonicalCapTree};
    let chosen = CapLeaf {
        slot_hash: BabyBear::new(0xA11CE),
        target: BabyBear::new(7_777),
        auth_tag: BabyBear::new(SIGNATURE_AUTH_TAG),
        mask_lo: BabyBear::new(0xFFFF),
        mask_hi: BabyBear::new(0xFFFF),
        expiry: BabyBear::new(0x00FF_FFFF),
        breadstuff: BabyBear::new(42),
    };
    let other = CapLeaf {
        slot_hash: BabyBear::new(0xBEEF),
        target: BabyBear::new(123),
        auth_tag: BabyBear::new(1),
        mask_lo: BabyBear::new(0xFFFF),
        mask_hi: BabyBear::new(0xFFFF),
        expiry: BabyBear::new(9),
        breadstuff: BabyBear::new(0),
    };
    // The holder's BEFORE tree is a genuine CanonicalCapTree (the keystone INSERT wrappers rebuild
    // it to splice the fresh conferred edge — `insert_witness`), so the membership path opens
    // against ITS root and the FULL 7-field c-list is threaded (`cap_leaves`).
    let tree = CanonicalCapTree::new(vec![chosen, other], CAP_TREE_DEPTH);
    let mw = tree
        .membership_witness(chosen.slot_hash)
        .expect("the anchor is a member of the BEFORE tree");
    CapMembershipWitness {
        leaf: chosen,
        siblings: mw.siblings,
        directions: mw.directions,
        // NON-EMPTY c-list ⇒ the WRITE-bearing cap-open route (`…WriteCapOpenVmDescriptor2R24`), the
        // ONLY wire-accepted route for these write-bearing cap effects (the authority-only crown is
        // wire-FORBIDDEN — `is_forbidden_authority_only_cap_write_descriptor` — because it leaves the
        // post-cap-root host-trusted). The anchor leaf (`slot_hash`) must be PRESENT; a second filler
        // leaf makes the sorted c-list non-trivial. INSERT routes graft a fresh edge derived from the
        // effect (distinct + absent); REMOVE/UPDATE routes touch the anchor in place.
        cap_leaves: vec![chosen, other],
        cap_tombstones: Vec::new(),
        clist_leaves: vec![
            HeapLeaf {
                addr: chosen.slot_hash,
                value: BabyBear::new(0xFFFF),
            },
            HeapLeaf {
                addr: other.slot_hash,
                value: other.mask_lo,
            },
        ],
    }
}

/// The shared mint→wire→commit driver for ONE domain-2 cap family. `effects` is the kernel turn
/// (a single cap-authorized effect); `welded_key` its authority-crown welded twin; `expect_vm` an
/// assertion on the executor bridge's VM projection (the per-effect surprise guard — the projector
/// effect-KIND must be the one we mint over). Drives:
///   1. MINT through `prove_cap_open_umem_welded_staged` (self-verifies),
///   2. WIRE-VERIFY through the deployed `verify_effect_vm_rotated_with_cutover` under the welded twin,
///      + the ~124-bit 8-felt anchor tooth + the vk_hash tooth,
///   3. EXECUTOR-COMMIT through `TurnExecutor::execute` + the forged-NEW-commitment anchor tooth.
fn mint_wire_commit(
    family: &str,
    before_cell: Cell,
    cell_id: CellId,
    effects: Vec<Effect>,
    welded_key: &str,
    expect_vm: impl Fn(&[VmEffect]) -> bool,
    after_mut: impl Fn(&mut Cell),
) {
    // The executor's OWN bridge projection — mint over EXACTLY the VM-effect sequence the executor
    // reconstructs at verify time (the per-effect-kind surprise the SDK projector could hide).
    let projection_turn = proof_carrying_turn(cell_id, effects.clone(), Vec::new(), [0u8; 32]);
    let vm_effects = dregg_turn::executor::convert_turn_effects_to_vm(&cell_id, &projection_turn);
    assert!(
        expect_vm(&vm_effects),
        "[{family}] the executor bridge must project the expected VM cap effect, got {vm_effects:?}"
    );

    let cap = broad_cap_witness();

    let before_balance: u64 = 100_000;
    let initial = dregg_circuit::CellState::with_capability_root_and_record_digest(
        before_balance,
        before_cell.state.nonce() as u32,
        compute_canonical_capability_root_felt(&before_cell.capabilities),
        dregg_cell::compute_authority_digest_felt(&before_cell),
    );

    // After-cell = before + a per-family single-domain CAPS change the umem leg reconciles (the staged
    // weld reconciles a caps-domain projection diff, decoupled from the effect's own cap-tree write,
    // exactly as the proven attenuate fixture does). Most families grant a cap slot; RevokeDelegation
    // BUMPS the delegation epoch instead — that is BOTH its single caps op AND the faithful post-state
    // the wide `revokeDelegationWriteCapOpen` write wrapper's epoch-tick gate (constraint #70:
    // `after.epoch == before.epoch + 1`) demands.
    let mut after_cell = before_cell.clone();
    after_mut(&mut after_cell);

    let mut ctx_ledger = Ledger::new();
    let _ = ctx_ledger.insert_cell(after_cell.clone());
    let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32], [4u8; 32]];
    let before_w = rw::produce(
        &before_cell,
        &ctx_ledger,
        &[0u8; 32],
        &[0u8; 32],
        &receipt_log,
        &Default::default(),
    );
    let after_w = rw::produce(
        &after_cell,
        &ctx_ledger,
        &[0u8; 32],
        &[0u8; 32],
        &receipt_log,
        &Default::default(),
    );

    let proj_pre = project_record_kernel_state(&before_cell);
    let proj_post = project_record_kernel_state(&after_cell);
    let ops = ops_from_diff(&proj_pre, &proj_post);
    assert_eq!(ops.len(), 1, "[{family}] the caps diff is a single op");
    assert_eq!(
        ops[0].key.domain(),
        dregg_turn::umem::UDomain::Caps,
        "[{family}] the welded leg reconciles the CAPS domain (domain 2)"
    );

    // 1. MINT (self-verifies inside the prover).
    let (welded_proof, welded_dpis) = prove_cap_open_umem_welded_staged(
        &initial,
        &vm_effects,
        &before_w,
        &after_w,
        &cap,
        &proj_pre,
        &ops,
    )
    .unwrap_or_else(|e| panic!("[{family}] the welded WIDE cap-open+umem mint MUST prove: {e:?}"));
    assert!(
        welded_dpis.len() >= 16 + 38,
        "[{family}] the welded cap-open leg carries the base PIs + 16 wide commit PIs (got {})",
        welded_dpis.len()
    );

    let proof_bytes =
        postcard::to_allocvec(&welded_proof).expect("serialize welded cap-open proof");

    // 2. WIRE-VERIFY through the deployed verifier under the Lean-emitted welded twin.
    let vk_hash: [u8; 32] = *blake3::hash(welded_member_json(welded_key).as_bytes()).as_bytes();
    verify_effect_vm_rotated_with_cutover(&proof_bytes, &welded_dpis, &vk_hash).unwrap_or_else(|e| {
        panic!(
            "[{family}] the welded WIDE cap-open proof MUST verify through the deployed wire verifier \
             under {welded_key}: {e:?}"
        )
    });

    // THE ~124-BIT ANCHOR TOOTH (wire): a forged 8-felt commit felt is rejected.
    let mut forged_dpis = welded_dpis.clone();
    let nf = forged_dpis.len();
    forged_dpis[nf - 1] = forged_dpis[nf - 1] + BabyBear::new(0x7777);
    assert!(
        verify_effect_vm_rotated_with_cutover(&proof_bytes, &forged_dpis, &vk_hash).is_err(),
        "[{family}] a forged 8-felt commit felt MUST be rejected by the wire verifier"
    );
    // THE vk_hash TOOTH (wire): a tampered welded-member vk_hash is rejected.
    let mut bad_vk = vk_hash;
    bad_vk[0] ^= 0xff;
    assert!(
        verify_effect_vm_rotated_with_cutover(&proof_bytes, &welded_dpis, &bad_vk).is_err(),
        "[{family}] a tampered welded-member vk_hash MUST be rejected by the wire verifier"
    );

    // 3. EXECUTOR-COMMIT through `TurnExecutor::execute`.
    let n = welded_dpis.len();
    let before8: [BabyBear; 8] = welded_dpis[n - 16..n - 8].try_into().unwrap();
    let after8: [BabyBear; 8] = welded_dpis[n - 8..n].try_into().unwrap();
    let old_commitment = felt8_to_bytes32(&before8);
    let new_commitment = felt8_to_bytes32(&after8);

    let mut ledger = Ledger::new();
    ledger
        .register_sovereign_cell(cell_id, old_commitment)
        .unwrap();
    let _ = ledger.insert_cell(before_cell.clone());

    let turn = proof_carrying_turn(
        cell_id,
        effects.clone(),
        proof_bytes.clone(),
        new_commitment,
    );
    let executor = TurnExecutor::new(ComputronCosts::zero());
    match executor.execute(&turn, &mut ledger) {
        TurnResult::Committed { .. } => {}
        other => panic!(
            "[{family}] the welded cap-open proof MUST COMMIT through the executor, got {other:?}"
        ),
    }
    let committed = ledger
        .get_sovereign_commitment(&cell_id)
        .expect("sovereign commitment present after commit");
    assert_eq!(
        *committed, new_commitment,
        "[{family}] the welded cap-open turn advanced the stored sovereign commitment"
    );

    // THE 8-FELT ANCHOR TOOTH (executor): a forged NEW commitment is rejected.
    let mut ledger2 = Ledger::new();
    ledger2
        .register_sovereign_cell(cell_id, old_commitment)
        .unwrap();
    let _ = ledger2.insert_cell(before_cell);
    let tampered = proof_carrying_turn(cell_id, effects, proof_bytes, [0xABu8; 32]);
    let executor2 = TurnExecutor::new(ComputronCosts::zero());
    match executor2.execute(&tampered, &mut ledger2) {
        TurnResult::Rejected { reason, .. } => {
            let s = format!("{reason:?}");
            assert!(
                s.contains("ProofVerificationFailed")
                    || s.contains("rotated")
                    || s.contains("Proof"),
                "[{family}] expected a cap-open 8-felt-anchor rejection, got: {s}"
            );
        }
        other => panic!(
            "[{family}] a forged NEW commitment on the welded cap-open proof MUST be REJECTED, got {other:?}"
        ),
    }
}

/// Build a sovereign before-cell with open permissions, keyed to the cipherclerk's public key.
fn sovereign_before(seed: &[u8]) -> (Cell, CellId) {
    let cclerk = AgentCipherclerk::new();
    let pub_key = cclerk.public_key().0;
    let token_id = *blake3::hash(seed).as_bytes();
    let mut before_cell = Cell::with_balance(pub_key, token_id, 100_000i64);
    before_cell.mode = CellMode::Sovereign;
    before_cell.permissions = open_perms();
    let cell_id = before_cell.id();
    (before_cell, cell_id)
}

/// The default single-domain CAPS after-mutation: grant a fresh cap slot (one caps-domain projection
/// op the umem leg reconciles). Used by every INSERT/UPDATE/REMOVE-cap family whose write wrapper
/// freezes the nonce + delegation epoch (a frozen-epoch after-cell PROVES for them).
fn grant_cap_slot(c: &mut Cell) {
    let target = {
        let mut tpk = [0u8; 32];
        tpk[0] = 200;
        Cell::with_balance(tpk, [0u8; 32], 0).id()
    };
    c.capabilities
        .grant(target, dregg_cell::AuthRequired::None)
        .expect("grant a cap slot");
}

// ---- the per-family end-to-end gauntlet cells -----------------------------------------------------

#[test]
fn domain2_grant_capability_welded_end_to_end() {
    let (before_cell, cell_id) = sovereign_before(b"cap-open-grant-domain2");
    // delegate / grantCap: the actor grants a cap TO ITSELF (the bridge's `to == cell_id` arm),
    // projecting `VmEffect::GrantCapability { phase_b: None }` → the plain-delegate authority route
    // (`grantCapCapOpenVmDescriptor2R24`).
    let effects = vec![Effect::GrantCapability {
        from: cell_id,
        to: cell_id,
        cap: CapabilityRef {
            target: cell_id,
            slot: 3,
            permissions: dregg_cell::AuthRequired::None,
            breadstuff: None,
            expires_at: None,
            allowed_effects: None,
            stored_epoch: None,
        },
    }];
    // With a non-empty c-list the EFFECTIVE descriptor is the WRITE wrapper: a plain (non-attenuating)
    // grant/delegate routes to `delegateWriteCapOpenVmDescriptor2R24` (the INSERT wrapper binding the
    // DELEGATION_OPS facet), NOT the authority-only `grantCapCapOpen` crown.
    mint_wire_commit(
        "GrantCapability",
        before_cell,
        cell_id,
        effects,
        "delegateWriteCapOpenVmDescriptor2R24",
        |vm| matches!(vm, [VmEffect::GrantCapability { .. }]),
        grant_cap_slot,
    );
}

#[test]
fn domain2_introduce_welded_end_to_end() {
    let (before_cell, cell_id) = sovereign_before(b"cap-open-introduce-domain2");
    let recipient = {
        let mut pk = [0u8; 32];
        pk[0] = 11;
        Cell::with_balance(pk, [0u8; 32], 0).id()
    };
    let target = {
        let mut pk = [0u8; 32];
        pk[0] = 22;
        Cell::with_balance(pk, [0u8; 32], 0).id()
    };
    let effects = vec![Effect::Introduce {
        introducer: cell_id,
        recipient,
        target,
        permissions: dregg_cell::AuthRequired::None,
    }];
    mint_wire_commit(
        "Introduce",
        before_cell,
        cell_id,
        effects,
        "introduceWriteCapOpenVmDescriptor2R24",
        |vm| matches!(vm, [VmEffect::Introduce { .. }]),
        grant_cap_slot,
    );
}

#[test]
fn domain2_refresh_delegation_welded_end_to_end() {
    let (before_cell, cell_id) = sovereign_before(b"cap-open-refresh-domain2");
    let child = {
        let mut pk = [0u8; 32];
        pk[0] = 33;
        Cell::with_balance(pk, [0u8; 32], 0).id()
    };
    let effects = vec![Effect::RefreshDelegation {
        child,
        snapshot: [7u8; 32],
    }];
    mint_wire_commit(
        "RefreshDelegation",
        before_cell,
        cell_id,
        effects,
        "refreshDelegationWriteCapOpenVmDescriptor2R24",
        |vm| matches!(vm, [VmEffect::RefreshDelegation { .. }]),
        grant_cap_slot,
    );
}

#[test]
fn domain2_revoke_capability_welded_end_to_end() {
    let (before_cell, cell_id) = sovereign_before(b"cap-open-revokecap-domain2");
    let effects = vec![Effect::RevokeCapability {
        cell: cell_id,
        slot: 5,
    }];
    mint_wire_commit(
        "RevokeCapability",
        before_cell,
        cell_id,
        effects,
        "revokeCapabilityWriteCapOpenVmDescriptor2R24",
        |vm| matches!(vm, [VmEffect::RevokeCapability { .. }]),
        grant_cap_slot,
    );
}

#[test]
fn domain2_revoke_delegation_welded_end_to_end() {
    let (before_cell, cell_id) = sovereign_before(b"cap-open-revokedeleg-domain2");
    let child = {
        let mut pk = [0u8; 32];
        pk[0] = 44;
        Cell::with_balance(pk, [0u8; 32], 0).id()
    };
    let effects = vec![Effect::RevokeDelegation { child }];
    // RevokeDelegation routes to the REMOVE wrapper `revokeDelegationWriteCapOpenVmDescriptor2R24`,
    // whose epoch-tick gate (constraint #70) demands `after.epoch == before.epoch + 1`. So the faithful
    // single-domain CAPS after-state BUMPS the delegation epoch (epoch-based revocation — a cap stamped
    // at the prior epoch goes stale), mirroring the HEAD `cap_write_revoke_proves_and_verifies_light_client`
    // fix. That bump IS the single caps-domain projection op the umem leg reconciles.
    mint_wire_commit(
        "RevokeDelegation",
        before_cell,
        cell_id,
        effects,
        "revokeDelegationWriteCapOpenVmDescriptor2R24",
        |vm| matches!(vm, [VmEffect::RevokeDelegation { .. }]),
        |c| {
            assert!(
                c.state.bump_delegation_epoch(),
                "the genuine RevokeDelegation post-state advances the delegation epoch"
            );
        },
    );
}
