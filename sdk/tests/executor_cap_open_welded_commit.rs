//! # THE DOMAIN-2 (CAPABILITY) CAP-OPEN WELDED EXECUTOR-COMMIT (STAGED, VK-RISK-FREE) — the
//! domain-2 executor-commit gap CLOSED.
//!
//! The sibling [`executor_welded_commit`] drives a domain-1 (value) welded transfer proof through the
//! deployed `TurnExecutor::execute` path. THIS test drives the first DOMAIN-2 (capability) welded
//! mint: a real `AttenuateCapability` turn proved through the WIDE cap-open descriptor (the in-circuit
//! depth-16 cap-membership authority crown the light-client wire DEMANDS) + the universal-memory CAPS
//! reconciliation leg, via [`dregg_sdk::full_turn_proof::prove_cap_open_umem_welded_staged`].
//!
//! ## The gap this closes
//!
//! The deployed executor sovereign verify (`dregg_turn`'s `verify_and_commit_proof_rotated` →
//! `verify_one_cohort_run`) resolved a cap effect to its PLAIN cohort descriptor
//! (`attenuateVmDescriptor2R24`) — a DIFFERENT surface than the SDK wire verifier
//! (`verify_effect_vm_rotated_with_cutover`), which routes cap effects through the cap-open descriptor +
//! the depth-16 membership crown and FORBIDS the plain cap descriptor. So a welded cap-open proof could
//! not executor-commit (the executor expected plain). The executor now ADDITIVELY resolves the bare
//! cap-open + welded cap-open descriptors (`attenuateCapOpenEffVmDescriptor2R24` in
//! `WIDE_REGISTRY_STAGED_TSV` / `WIDE_UMEM_WELD_REGISTRY_TSV`) BESIDE the plain member and verifies the
//! proof against them with the SAME anchored dpis — the cap-open WIDE PI vector is PI-COUNT-IDENTICAL
//! (62) to the plain wide cap vector (the crown adds trace columns, not PIs), so the reconstructed 8-felt
//! anchors bind BYTE-IDENTICALLY. The executor's cap-effect verify surface now AGREES with the wire's.
//!
//! ## What this proves
//!
//! 1. **CONTROL** — a welded WIDE cap-open `AttenuateCapability` proof verifies through the DEPLOYED
//!    `TurnExecutor::execute` and COMMITS, advancing the stored v9 commitment to the proven post-state.
//! 2. **THE 8-FELT ANCHOR BITES** — a forged NEW commitment makes the executor's anchored AFTER-8 PIs
//!    disagree with the welded leg's bound carrier ⇒ rejected (the ~124-bit binding rides the cap-open
//!    weld).
//!
//! ## STAGED / VK-RISK-FREE
//! The executor now ADMITS the cap-open welded form on the wire; it does NOT flip the deployed default
//! prover (the cipherclerk still mints the PLAIN wide cap descriptor) nor `umem_witness_enabled`.
//!
//! Requires `prover`; self-skips under `not(prover)`.

#![cfg(feature = "prover")]

use dregg_cell::commitment::{compute_canonical_capability_root_felt, felt8_to_bytes32};
use dregg_cell::{Cell, CellId, CellMode, Ledger};
use dregg_circuit::cap_root::CapLeaf;
use dregg_circuit::effect_vm::Effect as VmEffect;
use dregg_circuit::effect_vm::trace_rotated::{
    CapOpenWitness, FACET_MASK_HI, SIGNATURE_AUTH_TAG, WRITE_MASK_LO,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::heap_root::HeapLeaf;
use dregg_sdk::AgentCipherclerk;
use dregg_sdk::full_turn_proof::{CapMembershipWitness, prove_cap_open_umem_welded_staged};
use dregg_turn::rotation_witness as rw;
use dregg_turn::umem::{UKey, UmemKind, UmemOp, project_record_kernel_state};
use dregg_turn::{ComputronCosts, Effect, Turn, TurnExecutor, TurnResult};

/// The pre→post projection DIFF as a Blum WRITE op trace (the SAME shape the gauntlets build).
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

/// Assemble the sovereign proof-carrying turn (the cipherclerk's `sovereign_execute_proven` shape) —
/// identical to the domain-1 `executor_welded_commit` harness.
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

/// Build the shared fixture: a sovereign before-cell, the kernel attenuate effect + its BRIDGE-derived
/// VM effect (so the executor reconstructs the SAME effects_hash), the crown cap-membership witness
/// (its clist anchor mask set to the bridged KEEP_MASK so the cap-tree Update's submask is reflexive),
/// the producer's circuit pre-state (mirroring the executor's reconstruction), the rotation witnesses,
/// the genuine caps projection-diff, and the welded WIDE cap-open proof + its published dpis.
#[allow(clippy::type_complexity)]
fn make_welded_cap_open_attenuate() -> (
    Cell,
    CellId,
    Vec<Effect>,
    dregg_circuit::descriptor_ir2::Ir2BatchProof<dregg_circuit::descriptor_ir2::DreggStarkConfig>,
    Vec<BabyBear>,
) {
    let cclerk = AgentCipherclerk::new();
    let pub_key = cclerk.public_key().0;
    let token_id = *blake3::hash(b"cap-open-exec-domain2").as_bytes();

    let before_balance: u64 = 100_000;
    let mut before_cell = Cell::with_balance(pub_key, token_id, before_balance as i64);
    before_cell.mode = CellMode::Sovereign;
    before_cell.permissions = open_perms();
    let cell_id = before_cell.id();

    // The kernel attenuate effect → its VM projection via the EXECUTOR's OWN bridge
    // (`convert_turn_effects_to_vm`), so the producer mints over the EXACT VM-effect sequence the
    // executor reconstructs at verify time (the SDK `AgentCipherclerk::convert_effects_to_vm` projector
    // maps attenuate to a RevokeCapability shape — a DIFFERENT effect-kind — so it cannot be used here;
    // the executor's bridge maps attenuate to `VmEffect::AttenuateCapability`, which routes the
    // `attenuateCapOpenEffVmDescriptor2R24` cap-open member).
    let effects = vec![Effect::AttenuateCapability {
        cell: cell_id,
        slot: 7,
        narrower_permissions: dregg_cell::AuthRequired::None,
        narrower_effects: None,
        narrower_expiry: None,
    }];
    let projection_turn = proof_carrying_turn(cell_id, effects.clone(), Vec::new(), [0u8; 32]);
    let vm_effects = dregg_turn::executor::convert_turn_effects_to_vm(&cell_id, &projection_turn);
    assert!(
        matches!(
            vm_effects.as_slice(),
            [VmEffect::AttenuateCapability { .. }]
        ),
        "the executor bridge must project the kernel attenuate to a VM AttenuateCapability, got {vm_effects:?}"
    );
    let keep_mask = match &vm_effects[0] {
        VmEffect::AttenuateCapability {
            narrower_commitment,
            ..
        } => narrower_commitment[1],
        other => panic!("expected a VM AttenuateCapability, got {other:?}"),
    };

    // The faithful transfer-conferring crown leaf (auth_tag == Signature, mask_lo == EFFECT_TRANSFER) —
    // the depth-16 membership crown the wire demands. (Mirrors the domain-2 gauntlet's chosen leaf.)
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
    // The attenuate Update reads the held key (chosen[0]) and writes KEEP_MASK; set the anchor's held
    // mask to KEEP_MASK so the narrowing submask is reflexive (KEEP ⊑ held) for ANY bridged KEEP_MASK.
    let clist_leaves = vec![
        HeapLeaf {
            addr: chosen[0],
            value: keep_mask,
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

    // The producer's circuit pre-state — derived from the before-cell EXACTLY as the executor
    // reconstructs it (`verify_and_commit_proof_rotated`: pre-fee balance, pre-nonce, canonical cap-root,
    // authority digest), so the witness-independent base PIs match byte-for-byte.
    let initial = dregg_circuit::CellState::with_capability_root_and_record_digest(
        before_balance,
        before_cell.state.nonce() as u32,
        compute_canonical_capability_root_felt(&before_cell.capabilities),
        dregg_cell::compute_authority_digest_felt(&before_cell),
    );

    // After-cell = before + a granted cap slot (the genuine single-domain CAPS change the umem leg
    // reconciles).
    let mut after_cell = before_cell.clone();
    let target = {
        let mut tpk = [0u8; 32];
        tpk[0] = 200;
        Cell::with_balance(tpk, [0u8; 32], 0).id()
    };
    after_cell
        .capabilities
        .grant(target, dregg_cell::AuthRequired::None)
        .expect("grant a cap slot");

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
    assert_eq!(ops.len(), 1, "the attenuate caps diff is a single op");
    assert_eq!(
        ops[0].key.domain(),
        dregg_turn::umem::UDomain::Caps,
        "the welded leg reconciles the CAPS domain (domain 2)"
    );

    let (welded_proof, welded_dpis) = prove_cap_open_umem_welded_staged(
        &initial,
        &vm_effects,
        &before_w,
        &after_w,
        &cap,
        &proj_pre,
        &ops,
    )
    .expect("the welded WIDE cap-open+umem descriptor proves the genuine attenuate turn");
    assert!(
        welded_dpis.len() >= 16 + 38,
        "the welded cap-open leg carries the base PIs + 16 wide commit PIs (got {})",
        welded_dpis.len()
    );

    (before_cell, cell_id, effects, welded_proof, welded_dpis)
}

/// CONTROL: a welded WIDE cap-open `AttenuateCapability` proof verifies through the DEPLOYED executor
/// path and COMMITS, advancing the stored v9 commitment to the proven post-state. (Before the cap-open
/// routing the executor resolved ONLY the plain `attenuateVmDescriptor2R24` and the cap-open proof — its
/// membership-crown trace — would verify under NO resolved descriptor and REJECT.)
#[test]
fn welded_cap_open_attenuate_commits_through_executor() {
    let (before_cell, cell_id, effects, welded_proof, welded_dpis) =
        make_welded_cap_open_attenuate();

    // Stored OLD / claimed NEW = the producer's published 8-felt BEFORE/AFTER wide commit (the LAST 16
    // PIs), so the executor's re-anchor of those 16 PIs is a no-op for the honest leg (mirroring the
    // domain-1 `executor_welded_commit` harness).
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

    let proof_bytes =
        postcard::to_allocvec(&welded_proof).expect("serialize welded cap-open proof");
    let turn = proof_carrying_turn(cell_id, effects.clone(), proof_bytes, new_commitment);

    let executor = TurnExecutor::new(ComputronCosts::zero());
    match executor.execute(&turn, &mut ledger) {
        TurnResult::Committed { .. } => {}
        other => panic!(
            "the welded cap-open attenuate proof must COMMIT through the executor, got {other:?}"
        ),
    }
    let committed = ledger
        .get_sovereign_commitment(&cell_id)
        .expect("sovereign commitment present after commit");
    assert_eq!(
        *committed, new_commitment,
        "the welded cap-open turn advanced the stored sovereign commitment to the proven post-state"
    );

    // THE 8-FELT ANCHOR BITES: a forged NEW commitment makes the executor's anchored AFTER-8 PIs
    // disagree with the welded leg's bound carrier ⇒ rejected (the ~124-bit binding rides the cap-open
    // weld). A FRESH executor (the prior receipt chain advanced past the committed turn).
    let mut ledger2 = Ledger::new();
    ledger2
        .register_sovereign_cell(cell_id, old_commitment)
        .unwrap();
    let _ = ledger2.insert_cell(before_cell);
    let proof_bytes2 =
        postcard::to_allocvec(&welded_proof).expect("serialize welded cap-open proof");
    let tampered = proof_carrying_turn(cell_id, effects, proof_bytes2, [0xABu8; 32]);
    let executor2 = TurnExecutor::new(ComputronCosts::zero());
    match executor2.execute(&tampered, &mut ledger2) {
        TurnResult::Rejected { reason, .. } => {
            let s = format!("{reason:?}");
            assert!(
                s.contains("ProofVerificationFailed") || s.contains("rotated"),
                "expected a cap-open 8-felt-anchor rejection, got: {s}"
            );
        }
        other => panic!(
            "a forged NEW commitment on the welded cap-open proof must be REJECTED, got {other:?}"
        ),
    }
}
