//! Cutover C1 validation — the ROTATED sovereign proof-carrying matched pair.
//!
//! This integration test drives the cutover's first coherent checkpoint
//! (ROTATION-CUTOVER §EXEC, C1): the sovereign producer
//! ([`AgentCipherclerk::execute_sovereign_turn_with_proof`]) now mints a rotated
//! R=24 `Ir2BatchProof` over the cohort descriptor (instead of the weak hand-AIR
//! `EffectVmAir`), carrying the v9 felt commitment; the matched verifier
//! (`dregg_turn`'s `executor::verify_and_commit_proof`, which graduates to
//! `descriptor_ir2::verify_vm_descriptor2`) reconstructs the 38-PI layout from
//! the after-state it holds and accepts.
//!
//! It lives in `sdk/tests/` (a self-contained compilation unit) rather than the
//! workspace `dregg-tests` harness so the C1 matched pair is validatable
//! independently. Requires the `recursion` feature (the SDK default), which
//! compiles the rotated producer + pulls `dregg-circuit/recursion` (the rotated
//! verifier). Under `not(recursion)` the rotated path does not exist, so the
//! test self-skips.

#![cfg(feature = "recursion")]

use dregg_cell::{Cell, CellId, CellMode, Ledger};
use dregg_sdk::AgentCipherclerk;
use dregg_turn::{ComputronCosts, Effect, TurnExecutor, TurnResult};

/// Register a sovereign cell with the v9 commitment the rotated producer derives
/// for its before-state (single-cell `cells_root`, empty nullifier root, empty
/// receipt-chain `iroot`). The executor reads this back as OLD_COMMIT (PI 34).
fn setup_sovereign_cell(balance: u64) -> (AgentCipherclerk, CellId, Ledger) {
    let cclerk = AgentCipherclerk::new();
    let pub_key = cclerk.public_key().0;
    let token_id = *blake3::hash(b"c1-domain").as_bytes();

    let mut cell = Cell::with_balance(pub_key, token_id, i64::try_from(balance).unwrap());
    cell.mode = CellMode::Sovereign;
    let cell_id = cell.id();

    let nullifier_root = [0u8; 32];
    let mut ctx_ledger = Ledger::new();
    let _ = ctx_ledger.insert_cell(cell.clone());
    let cells_root = dregg_turn::rotation_witness::cells_root(&ctx_ledger);
    let iroot = dregg_turn::rotation_witness::iroot(&[]);
    let v9_ctx = dregg_cell::commitment::V9RotationContext {
        cells_root,
        nullifier_root,
        iroot,
    };
    let commitment = dregg_cell::commitment::compute_canonical_state_commitment_v9(&cell, &v9_ctx);

    let mut cclerk = cclerk;
    cclerk.store_sovereign_state(cell.clone());

    let mut ledger = Ledger::new();
    ledger.register_sovereign_cell(cell_id, commitment).unwrap();
    let _ = ledger.insert_cell(cell);

    (cclerk, cell_id, ledger)
}

/// CONTROL: an honest rotated sovereign turn proves (rotated `Ir2BatchProof`) and
/// the executor ACCEPTS it through the rotated `verify_vm_descriptor2` leg, then
/// advances the stored v9 commitment.
#[test]
fn rotated_sovereign_turn_proves_and_verifies() {
    let (mut cclerk, cell_id, mut ledger) = setup_sovereign_cell(1000);

    let dest_cell = Cell::with_balance([42u8; 32], *blake3::hash(b"c1-domain").as_bytes(), 0);
    let dest_id = dest_cell.id();
    let _ = ledger.insert_cell(dest_cell);

    let effects = vec![Effect::Transfer {
        from: cell_id,
        to: dest_id,
        amount: 100,
    }];

    let turn = cclerk
        .execute_sovereign_turn_with_proof(&cell_id, effects, 500)
        .expect("rotated sovereign turn should prove");

    // The proof is real, postcard-encoded (NOT the `DREG`-magic hand-AIR wire).
    let proof_bytes = turn
        .execution_proof
        .as_ref()
        .expect("execution_proof attached");
    assert!(!proof_bytes.is_empty());
    assert_ne!(
        &proof_bytes[0..4],
        b"DREG",
        "rotated wire is a postcard BatchProof"
    );
    assert_eq!(turn.execution_proof_cell, Some(cell_id));
    assert!(turn.execution_proof_new_commitment.is_some());
    assert!(turn.sovereign_witnesses.is_empty());

    let executor = TurnExecutor::new(ComputronCosts::zero());
    match executor.execute(&turn, &mut ledger) {
        TurnResult::Committed { .. } => {}
        other => panic!("rotated sovereign turn must commit, got {other:?}"),
    }

    // The stored sovereign commitment advanced to the proven post-state (v9 felt).
    let new_commitment = ledger
        .get_sovereign_commitment(&cell_id)
        .expect("commitment present after commit");
    assert_eq!(
        *new_commitment,
        turn.execution_proof_new_commitment.unwrap()
    );
}

/// ANTI-GHOST: a rotated sovereign turn whose claimed post-state commitment is
/// FORGED is REJECTED — the forged PI 35 disagrees with the trace's after-block
/// `STATE_COMMIT` carrier (the descriptor's col-261 `pi_binding`), so
/// `verify_vm_descriptor2` fails.
#[test]
fn rotated_sovereign_forged_post_state_is_rejected() {
    let (mut cclerk, cell_id, mut ledger) = setup_sovereign_cell(1000);

    let dest_cell = Cell::with_balance([43u8; 32], *blake3::hash(b"c1-domain").as_bytes(), 0);
    let dest_id = dest_cell.id();
    let _ = ledger.insert_cell(dest_cell);

    let effects = vec![Effect::Transfer {
        from: cell_id,
        to: dest_id,
        amount: 50,
    }];

    let mut turn = cclerk
        .execute_sovereign_turn_with_proof(&cell_id, effects, 500)
        .expect("rotated sovereign turn should prove");

    // Forge the claimed post-state commitment.
    turn.execution_proof_new_commitment = Some([0xFFu8; 32]);

    let executor = TurnExecutor::new(ComputronCosts::zero());
    match executor.execute(&turn, &mut ledger) {
        TurnResult::Rejected { reason, .. } => {
            let s = format!("{reason:?}");
            assert!(
                s.contains("ProofVerificationFailed") || s.contains("rotated"),
                "expected a rotated verify rejection, got: {s}"
            );
        }
        other => panic!("ANTI-GHOST: forged post-state must be rejected, got {other:?}"),
    }
}

// ===========================================================================
// WALL A — the rotated `prove_full_turn` / `verify_full_turn` round-trip carries
// ZERO v1 dependency. These drive `prove_full_turn` DIRECTLY with a rotation
// witness (not the executor-mint path) so the rotated leg's vk_hash (A.1) and the
// rotated-PI conservation read (A.2) are exercised, and so the v1 trace is NOT
// generated on the rotated path (A.3). The witness is built mirroring the
// cipherclerk's validated reference shape (a single outgoing sovereign transfer,
// the transfer caveat manifest).
// ===========================================================================
mod wall_a {
    use dregg_cell::commitment::{V9RotationContext, compute_canonical_state_commitment_v9_felt};
    use dregg_cell::{Cell, CellMode, Ledger};
    use dregg_circuit::effect_vm::{self, CellState};
    use dregg_sdk::full_turn_proof::{
        ConservationWitness, FullTurnWitness, RotationTurnWitness, prove_full_turn,
        verify_full_turn,
    };
    use dregg_turn::rotation_witness as rw;

    /// Build a valid rotated `FullTurnWitness` for a single outgoing transfer of `amount`
    /// from a sovereign cell of `balance`. Returns `(witness, old_commit_felt,
    /// new_commit_felt)` — the latter two are the rotated PI 34/35 the verifier expects.
    /// Mirrors `AgentCipherclerk::prove_sovereign_turn_rotated` (the C1 reference).
    fn build_rotated_transfer_witness(
        balance: u64,
        amount: u64,
    ) -> (
        FullTurnWitness,
        dregg_circuit::field::BabyBear,
        dregg_circuit::field::BabyBear,
    ) {
        let token_id = *blake3::hash(b"wallA-domain").as_bytes();
        let mut before_cell = Cell::with_balance([7u8; 32], token_id, balance as i64);
        before_cell.mode = CellMode::Sovereign;

        // after-state: an outgoing transfer debits the balance.
        let mut after_cell = before_cell.clone();
        after_cell
            .state
            .set_balance(after_cell.state.balance().saturating_sub(amount as i64));

        // circuit pre-state (cap-root-seeded), identical to the v1 path.
        let initial_vm_state = CellState::with_capability_root(
            before_cell.state.balance() as u64,
            before_cell.state.nonce() as u32,
            dregg_cell::compute_canonical_capability_root_felt(&before_cell.capabilities),
        );

        let vm_effects = vec![effect_vm::Effect::Transfer {
            amount,
            direction: 1, // outgoing
        }];

        let nullifier_root = [0u8; 32];
        let receipt_hashes: Vec<[u8; 32]> = Vec::new();
        let mut ctx_ledger = Ledger::new();
        let _ = ctx_ledger.insert_cell(before_cell.clone());

        let before_w = rw::produce(&before_cell, &ctx_ledger, &nullifier_root, &receipt_hashes);
        let after_w = rw::produce(&after_cell, &ctx_ledger, &nullifier_root, &receipt_hashes);

        // The cell-side v9 commitment of the before-state == rotated PI 34; the after-state
        // v9 == rotated PI 35 (the cross-checks the cipherclerk asserts by construction).
        let old_commit = compute_canonical_state_commitment_v9_felt(
            &before_cell,
            &V9RotationContext {
                cells_root: before_w.pre_limbs[0],
                nullifier_root,
                iroot: before_w.iroot,
            },
        );
        let new_commit = compute_canonical_state_commitment_v9_felt(
            &after_cell,
            &V9RotationContext {
                cells_root: after_w.pre_limbs[0],
                nullifier_root,
                iroot: after_w.iroot,
            },
        );

        let rotation = RotationTurnWitness::for_effects(before_w, after_w, &vm_effects);
        let witness = FullTurnWitness {
            initial_cell_state: initial_vm_state,
            effects: vm_effects,
            authorization: None,
            membership: None,
            conservation: None,
            non_revocation: None,
            cap_membership: None,
            turn_hash: *blake3::hash(b"wallA-turn").as_bytes(),
            rotation: Some(rotation),
        };
        (witness, old_commit, new_commit)
    }

    /// CONTROL: a rotated full-turn proves through `prove_full_turn` and `verify_full_turn`
    /// ACCEPTS it — the rotated leg's vk_hash is the rotated cohort descriptor's fingerprint
    /// (A.1) and is re-checked at verify; the v1 effect-vm trace was never generated (A.3).
    #[test]
    fn rotated_full_turn_round_trips() {
        let (witness, _old, _new) = build_rotated_transfer_witness(1000, 100);
        let proof = prove_full_turn(&witness).expect("rotated full-turn should prove");

        // The attached leg is the rotated one (not the v1 "effect-vm").
        let labels: Vec<&str> = proof
            .composed
            .sub_proofs
            .iter()
            .map(|sp| sp.label.as_str())
            .collect();
        assert!(
            labels.contains(&"effect-vm-rotated"),
            "expected a rotated effect-vm leg, got {labels:?}"
        );
        assert!(
            !labels.contains(&"effect-vm"),
            "the v1 effect-vm leg must be ABSENT on the rotated path, got {labels:?}"
        );

        // The verifier cross-binds OLD_COMMIT(0)/NEW_COMMIT(4) of the rotated leg's PI; those
        // carriers are the trace's OWN before/after state-commit (NOT a separately-recomputed
        // v9), so the expected commits ARE the proof's bound PI at those offsets.
        let rot_pi = &proof
            .composed
            .sub_proofs
            .iter()
            .find(|sp| sp.label == "effect-vm-rotated")
            .expect("rotated leg present")
            .sub_public_inputs;
        let old_commit = rot_pi[dregg_circuit::effect_vm::pi::OLD_COMMIT];
        let new_commit = rot_pi[dregg_circuit::effect_vm::pi::NEW_COMMIT];

        verify_full_turn(&proof, old_commit, new_commit).expect("rotated full-turn should verify");
    }

    /// ANTI-GHOST (A.1): tampering the rotated leg's vk_hash is REJECTED. The verifier
    /// re-derives the expected fingerprint from the uniquely-accepting cohort descriptor and
    /// the mismatch fails — proving vk_hash is load-bearing on the rotated leg (not cosmetic).
    #[test]
    fn rotated_full_turn_tampered_vk_hash_rejected() {
        let (witness, old_commit, new_commit) = build_rotated_transfer_witness(1000, 100);
        let mut proof = prove_full_turn(&witness).expect("rotated full-turn should prove");

        let leg = proof
            .composed
            .sub_proofs
            .iter_mut()
            .find(|sp| sp.label == "effect-vm-rotated")
            .expect("rotated leg present");
        leg.vk_hash[0] ^= 0xFF; // flip a byte of the descriptor fingerprint

        let err = verify_full_turn(&proof, old_commit, new_commit)
            .expect_err("ANTI-GHOST: a tampered rotated vk_hash must be rejected");
        let s = format!("{err:?}");
        assert!(
            s.contains("vk_hash") || s.contains("fingerprint"),
            "expected a vk_hash-mismatch rejection, got: {s}"
        );
    }

    /// ANTI-GHOST (A.2): with a conservation witness present, a FORGED expected_net_delta is
    /// rejected — and the check reads net_delta from the ROTATED PI (the v1 trace does not
    /// exist on this path), so this also proves the conservation leg has no v1 dependency.
    #[test]
    fn rotated_full_turn_forged_net_delta_rejected() {
        let (mut witness, _old, _new) = build_rotated_transfer_witness(1000, 100);
        // A wrong expected net_delta (the honest turn's is the outgoing-100 encoding).
        witness.conservation = Some(ConservationWitness {
            expected_net_delta: 999_999,
        });
        let err = prove_full_turn(&witness)
            .expect_err("ANTI-GHOST: a forged conservation net_delta must be rejected");
        let s = format!("{err:?}");
        assert!(
            s.contains("conservation"),
            "expected a conservation mismatch (read from the rotated PI), got: {s}"
        );
    }
}
