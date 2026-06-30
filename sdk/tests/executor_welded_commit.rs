//! # THE EXECUTOR WELDED-AWARE COMMIT (STAGED, VK-RISK-FREE) — the umem flip's HARD BLOCKER closed.
//!
//! The deployed executor verify path (`dregg_turn`'s `verify_and_commit_proof_rotated` →
//! `verify_one_cohort_run`) resolves a turn's cohort descriptor BY NAME and verifies the attached
//! `Ir2BatchProof` against it. Before this change it resolved ONLY the bare wide member
//! (`WIDE_REGISTRY_STAGED_TSV`), so a WELDED proof (the wide rotated cohort + the universal-memory
//! reconciliation leg, one descriptor — `prove_wide_umem_welded_staged{,_with_fee}`) would verify
//! under NO resolved descriptor and REJECT — the wire-breaking blocker that gated the umem flip.
//!
//! This test drives a GENUINE welded proof through the DEPLOYED `TurnExecutor::execute` path and
//! asserts it COMMITS: the executor now ALSO resolves the welded twin from
//! `WIDE_UMEM_WELD_REGISTRY_TSV` and accepts a welded proof against it (a UNIQUE-accept beside the
//! bare member). It also asserts the BARE path still commits (the welded twin is PRESENT for a
//! transfer key, yet a bare proof falls back to the bare member and the 8-felt anchors stay bound),
//! and that the welded twin's 8-felt anchors bite (a tampered NEW commitment rejects).
//!
//! ## STAGED / VK-RISK-FREE
//! The executor now ADMITS the welded form on the wire; it does NOT flip the deployed default prover
//! (the cipherclerk still mints bare) nor `umem_witness_enabled`. The weld is PI-COUNT-PRESERVING, so
//! the executor's existing 16-wide-commit-PI (8-felt) reconstruction is byte-identical for the welded
//! form — only the resolved descriptor + verify target change.
//!
//! Requires `prover`; self-skips under `not(prover)`.

#![cfg(feature = "prover")]

use dregg_cell::commitment::{
    V9RotationContext, compute_canonical_state_commitment_v9_8, felt8_to_bytes32,
};
use dregg_cell::{Cell, CellId, CellMode, Ledger};
use dregg_circuit::effect_vm::trace_rotated::transfer_caveat_manifest;
use dregg_sdk::AgentCipherclerk;
use dregg_sdk::full_turn_proof::prove_wide_umem_welded_staged_with_fee;
use dregg_turn::rotation_witness as rw;
use dregg_turn::umem::{UKey, UmemKind, UmemOp, project_record_kernel_state};
use dregg_turn::{ComputronCosts, Effect, Turn, TurnExecutor, TurnResult};

/// The pre→post projection DIFF as a Blum WRITE op trace (the effect's universal-memory touch) — the
/// SAME shape `wide_umem_weld_staged_gauntlet`'s `ops_from_diff` builds.
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

/// Build a sovereign before-cell + its single-cell v9 turn-context (cells_root over the lone cell,
/// empty nullifier/commitments roots, empty receipt-chain MMR) — the EXACT context the cipherclerk
/// sovereign producer (`prove_sovereign_turn_rotated`) and `setup_sovereign_cell` use.
fn setup(balance: u64) -> (Cell, CellId, V9RotationContext, [u8; 32]) {
    let cclerk = AgentCipherclerk::new();
    let pub_key = cclerk.public_key().0;
    let token_id = *blake3::hash(b"weld-exec-domain").as_bytes();

    let mut cell = Cell::with_balance(pub_key, token_id, i64::try_from(balance).unwrap());
    cell.mode = CellMode::Sovereign;
    let cell_id = cell.id();

    let mut ctx_ledger = Ledger::new();
    let _ = ctx_ledger.insert_cell(cell.clone());
    let ctx = V9RotationContext {
        cells_root: rw::cells_root(&ctx_ledger),
        nullifier_root: [0u8; 32],
        commitments_root: [0u8; 32],
        iroot: rw::iroot(&[]),
    };
    let old_commitment = compute_canonical_state_commitment_v9_8(&cell, &ctx);
    (cell, cell_id, ctx, old_commitment)
}

/// Assemble the sovereign proof-carrying turn (the cipherclerk's `sovereign_execute_proven` shape).
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

/// CONTROL: a WELDED sovereign transfer proof verifies through the DEPLOYED executor path and
/// COMMITS, advancing the stored v9 commitment to the proven post-state. (Without the welded-aware
/// resolution the executor would resolve only the bare `transferFeeVmDescriptor2R24` and the welded
/// proof — its extra umemOp / +7 columns — would verify under NO descriptor and REJECT.)
#[test]
fn welded_transfer_commits_through_executor() {
    let balance = 100_000u64;
    let amount = 250u64;
    let (before_cell, cell_id, ctx, old_commitment) = setup(balance);

    // The executor reconstructs `initial_vm_state` from the registered cell (pre-fee balance,
    // pre-nonce, cap-root, authority digest); produce the welded proof over the IDENTICAL state.
    let initial_vm_state = dregg_circuit::CellState::with_capability_root_and_record_digest(
        balance,
        before_cell.state.nonce() as u32,
        dregg_cell::compute_canonical_capability_root_felt(&before_cell.capabilities),
        dregg_cell::compute_authority_digest_felt(&before_cell),
    );

    let dest_cell = Cell::with_balance([9u8; 32], *blake3::hash(b"weld-exec-domain").as_bytes(), 0);
    let dest_id = dest_cell.id();
    let effects = vec![Effect::Transfer {
        from: cell_id,
        to: dest_id,
        amount,
    }];
    let vm_effects = AgentCipherclerk::convert_effects_to_vm(&cell_id, &effects);

    // After-cell = before debited by `amount` (fee 0, so no extra fee debit) — the SAME projection
    // the cipherclerk's `prove_sovereign_turn_rotated` derives.
    let mut after_cell = before_cell.clone();
    after_cell
        .state
        .set_balance(after_cell.state.balance().saturating_sub(amount as i64));

    let mut ctx_ledger = Ledger::new();
    let _ = ctx_ledger.insert_cell(before_cell.clone());
    let before_w = rw::produce(
        &before_cell,
        &ctx_ledger,
        &ctx.nullifier_root,
        &ctx.commitments_root,
        &[],
    );
    let after_w = rw::produce(
        &after_cell,
        &ctx_ledger,
        &ctx.nullifier_root,
        &ctx.commitments_root,
        &[],
    );

    let caveat = transfer_caveat_manifest();
    let proj_pre = project_record_kernel_state(&before_cell);
    let proj_post = project_record_kernel_state(&after_cell);
    let ops = ops_from_diff(&proj_pre, &proj_post);
    assert!(
        !ops.is_empty(),
        "the transfer must touch the universal memory"
    );

    // THE WELDED FEE PROOF (the deployed sovereign transfer routes the fee descriptor).
    let (welded_proof, welded_dpis) = prove_wide_umem_welded_staged_with_fee(
        &initial_vm_state,
        &vm_effects,
        &before_w,
        &after_w,
        &caveat,
        &proj_pre,
        &ops,
        0,
    )
    .expect("the welded WIDE+umem fee descriptor proves the genuine sovereign transfer");

    // The NEW commitment the executor anchors AFTER-8 to = the welded leg's published AFTER 8-felt
    // commit (the LAST 8 PIs). The executor re-anchors the 16 wide PIs to stored-OLD / claimed-NEW.
    let n = welded_dpis.len();
    let after8: [dregg_circuit::field::BabyBear; 8] = welded_dpis[n - 8..n].try_into().unwrap();
    let new_commitment = felt8_to_bytes32(&after8);

    let mut ledger = Ledger::new();
    ledger
        .register_sovereign_cell(cell_id, old_commitment)
        .unwrap();
    let _ = ledger.insert_cell(before_cell.clone());

    let proof_bytes = postcard::to_allocvec(&welded_proof).expect("serialize welded proof");
    let turn = proof_carrying_turn(cell_id, effects.clone(), proof_bytes, new_commitment);

    let executor = TurnExecutor::new(ComputronCosts::zero());
    match executor.execute(&turn, &mut ledger) {
        TurnResult::Committed { .. } => {}
        other => {
            panic!("the welded transfer proof must COMMIT through the executor, got {other:?}")
        }
    }
    let committed = ledger
        .get_sovereign_commitment(&cell_id)
        .expect("sovereign commitment present after commit");
    assert_eq!(
        *committed, new_commitment,
        "the welded turn advanced the stored sovereign commitment to the proven post-state"
    );

    // THE 8-FELT ANCHOR BITES: a forged NEW commitment makes the executor's anchored AFTER-8 PIs
    // disagree with the welded leg's bound carrier ⇒ rejected (the ~124-bit binding rides the weld).
    let mut ledger2 = Ledger::new();
    ledger2
        .register_sovereign_cell(cell_id, old_commitment)
        .unwrap();
    let _ = ledger2.insert_cell(before_cell.clone());
    let proof_bytes2 = postcard::to_allocvec(&welded_proof).expect("serialize welded proof");
    let tampered = proof_carrying_turn(cell_id, effects, proof_bytes2, [0xABu8; 32]);
    // A FRESH executor (the prior one's receipt chain advanced past the committed turn, which would
    // reject the tampered turn at the receipt-chain stage before reaching proof verification).
    let executor2 = TurnExecutor::new(ComputronCosts::zero());
    match executor2.execute(&tampered, &mut ledger2) {
        TurnResult::Rejected { reason, .. } => {
            let s = format!("{reason:?}");
            assert!(
                s.contains("ProofVerificationFailed") || s.contains("rotated"),
                "expected a welded 8-felt-anchor rejection, got: {s}"
            );
        }
        other => {
            panic!("a forged NEW commitment on the welded proof must be REJECTED, got {other:?}")
        }
    }
}

/// THE FLIP (G4): a deployed BARE sovereign transfer is now REJECTED by the welded-requiring
/// executor. The transfer key HAS a welded twin present and is NOT one of the 3 producer-bare wide
/// members, so `verify_one_cohort_run`'s `require_welded` DROPS the bare member from the accept set:
/// a welded leg is the SOLE accepted form. Disarming the producer alone (without reverting the
/// verifier) is a HALF-rollback that fails closed — the bare proof binds no admitted descriptor. (A
/// genuine rollback reverts BOTH the producer toggle AND this verifier narrowing; the bare TSV stays
/// in-tree as that rollback target.)
#[test]
fn bare_transfer_rejected_by_welded_requiring_executor() {
    let (mut cclerk, cell_id, mut ledger) = setup_bare(1000);
    // DISARM the domain-1 producer (the G4 default is ARMED) so it mints the BARE wide leg — the
    // half-rollback the welded-requiring executor must REJECT.
    cclerk.set_umem_weld_staged_enabled(false);

    let dest_cell =
        Cell::with_balance([42u8; 32], *blake3::hash(b"weld-exec-domain").as_bytes(), 0);
    let dest_id = dest_cell.id();
    let _ = ledger.insert_cell(dest_cell);

    let effects = vec![Effect::Transfer {
        from: cell_id,
        to: dest_id,
        amount: 100,
    }];
    let turn = cclerk
        .execute_sovereign_turn_with_proof(&cell_id, effects, 0, 0)
        .expect("bare rotated sovereign turn should prove");

    let executor = TurnExecutor::new(ComputronCosts::zero());
    match executor.execute(&turn, &mut ledger) {
        TurnResult::Rejected { reason, .. } => {
            let s = format!("{reason:?}");
            assert!(
                s.contains("bound NO descriptor")
                    || s.contains("welded required")
                    || s.contains("ProofVerificationFailed"),
                "expected a welded-required rejection of the bare transfer, got: {s}"
            );
        }
        other => panic!(
            "the bare transfer must be REJECTED by the welded-requiring executor (G4 flip), got \
             {other:?}"
        ),
    }
    // The stored commitment did NOT advance (no commit happened).
    assert!(
        ledger.get_sovereign_commitment(&cell_id).is_some(),
        "the sovereign registration is intact (the rejected turn did not commit)"
    );
}

/// Cipherclerk-driven sovereign-cell setup (the c1 `setup_sovereign_cell` shape) for the bare path.
fn setup_bare(balance: u64) -> (AgentCipherclerk, CellId, Ledger) {
    let cclerk = AgentCipherclerk::new();
    let pub_key = cclerk.public_key().0;
    let token_id = *blake3::hash(b"weld-exec-domain").as_bytes();

    let mut cell = Cell::with_balance(pub_key, token_id, i64::try_from(balance).unwrap());
    cell.mode = CellMode::Sovereign;
    let cell_id = cell.id();

    let mut ctx_ledger = Ledger::new();
    let _ = ctx_ledger.insert_cell(cell.clone());
    let ctx = V9RotationContext {
        cells_root: rw::cells_root(&ctx_ledger),
        nullifier_root: [0u8; 32],
        commitments_root: [0u8; 32],
        iroot: rw::iroot(&[]),
    };
    let commitment = compute_canonical_state_commitment_v9_8(&cell, &ctx);

    let mut cclerk = cclerk;
    cclerk.store_sovereign_state(cell.clone());

    let mut ledger = Ledger::new();
    ledger.register_sovereign_cell(cell_id, commitment).unwrap();
    let _ = ledger.insert_cell(cell);

    (cclerk, cell_id, ledger)
}

/// **THE DOMAIN-1 CIPHERCLERK WELD PRODUCER (STAGED, VK-RISK-FREE) — the deployed sovereign producer
/// mints welded when armed.** Arm the cipherclerk's domain-1 weld toggle
/// (`set_umem_weld_staged_enabled(true)`) and drive a sovereign transfer through the SAME deployed
/// entry the live producer uses (`execute_sovereign_turn_with_proof` → `prove_sovereign_turn_rotated`).
/// The resulting `execution_proof` is the WIDE+UMEM WELDED form (the value-domain reconciliation leg
/// folded BESIDE the 8-felt commit), and it COMMITS through the deployed welded-aware executor — the
/// domain-1 half of "both domains mint welded on the deployed path."
///
/// CONTROL is the sibling `bare_transfer_still_commits_through_welded_aware_executor` (toggle OFF ⇒
/// the byte-identical bare leg). STAGED: the toggle defaults OFF, so the live fleet is unaffected
/// until the gated VK epoch flips it on.
#[test]
fn domain1_armed_cipherclerk_mints_welded_and_commits() {
    let (mut cclerk, cell_id, mut ledger) = setup_bare(1000);
    // ARM the domain-1 weld producer (the opt-in the gated VK epoch will flip on by default).
    cclerk.set_umem_weld_staged_enabled(true);
    assert!(cclerk.umem_weld_staged_enabled());

    let dest_cell =
        Cell::with_balance([43u8; 32], *blake3::hash(b"weld-exec-domain").as_bytes(), 0);
    let dest_id = dest_cell.id();
    let _ = ledger.insert_cell(dest_cell);

    let effects = vec![Effect::Transfer {
        from: cell_id,
        to: dest_id,
        amount: 100,
    }];
    let turn = cclerk
        .execute_sovereign_turn_with_proof(&cell_id, effects, 0, 0)
        .expect("the ARMED cipherclerk MUST mint the welded sovereign transfer proof");

    let executor = TurnExecutor::new(ComputronCosts::zero());
    match executor.execute(&turn, &mut ledger) {
        TurnResult::Committed { .. } => {}
        other => panic!(
            "the DOMAIN-1 welded sovereign transfer MUST commit through the welded-aware executor, \
             got {other:?}"
        ),
    }
    let committed = ledger
        .get_sovereign_commitment(&cell_id)
        .expect("commitment present after commit");
    assert_eq!(
        *committed,
        turn.execution_proof_new_commitment.unwrap(),
        "the welded leg's 8-felt commit anchors are PI-count-preserving — the committed commitment \
         matches the deployed-default (bare) one"
    );
}
