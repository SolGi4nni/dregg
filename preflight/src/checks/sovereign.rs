//! Factory and Sovereign checks: deploy, peer exchange, multi-party atomic, IVC history.
//!
//! The IVC-history check runs the REAL whole-chain recursive prover
//! (`dregg_circuit_prove::ivc_turn_chain`) over genuinely minted rotated turns —
//! NOT the simulated IVC in `circuit/src/ivc.rs` (a hash-chain a forger can mint
//! at will; see `circuit-prove/tests/mock_proof_purge_gate.rs`).

use dregg_cell::{
    AuthRequired, Cell, CellId, CellMode, ChildVkStrategy, FactoryDescriptor, FactoryRegistry,
    FieldConstraint, Ledger, Permissions,
};
use dregg_circuit_prove::ivc_turn_chain::{
    FinalizedTurn, RecursionVk, WholeChainProofBytes, prove_turn_chain_recursive,
    verify_whole_chain_proof_bytes,
};
use dregg_circuit_prove::joint_turn_aggregation::DescriptorParticipant;
use dregg_turn::builder::ActionBuilder;
use dregg_turn::rotation_witness::mint_rotated_participant_leg;
use dregg_turn::{ComputronCosts, DelegationMode, Effect, TurnBuilder, TurnExecutor, TurnResult};

use crate::report::{CheckResult, run_check};

fn test_key(name: &str) -> [u8; 32] {
    *blake3::hash(format!("preflight-sovereign:{name}").as_bytes()).as_bytes()
}

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

pub fn run() -> Vec<CheckResult> {
    vec![
        run_check("deploy", check_factory_deploy),
        run_check("peer_exchange", check_sovereign_peer_exchange),
        run_check("atomic", check_multi_party_atomic),
        run_check("ivc", check_ivc_history_compression),
    ]
}

fn check_factory_deploy() -> Result<(), String> {
    let mut registry = FactoryRegistry::new();

    let factory_vk = test_key("factory-deploy");
    let descriptor = FactoryDescriptor {
        factory_vk,
        child_program_vk: None,
        child_vk_strategy: Some(ChildVkStrategy::Derived {
            base_vk: factory_vk,
        }),
        allowed_cap_templates: vec![],
        field_constraints: vec![
            FieldConstraint::NonZero { field_index: 0 },
            FieldConstraint::Range {
                field_index: 1,
                min: 1,
                max: 100,
            },
        ],
        state_constraints: vec![],
        default_mode: CellMode::Hosted,
        creation_budget: Some(1000),
    };

    registry.deploy(descriptor);

    // Verify factory is registered
    let retrieved = registry.get(&factory_vk).ok_or("factory not in registry")?;
    if retrieved.factory_vk != factory_vk {
        return Err("factory VK mismatch".into());
    }

    // Verify VK derivation for child
    let params_hash = *blake3::hash(b"nft-params-1").as_bytes();
    let child_vk = ChildVkStrategy::derive_child_vk(&factory_vk, &params_hash);

    // Verify VK derivation is deterministic
    let child_vk2 = ChildVkStrategy::derive_child_vk(&factory_vk, &params_hash);
    if child_vk != child_vk2 {
        return Err("VK derivation should be deterministic".into());
    }

    // Verify different params produce different VKs
    let other_params = *blake3::hash(b"nft-params-2").as_bytes();
    let other_vk = ChildVkStrategy::derive_child_vk(&factory_vk, &other_params);
    if child_vk == other_vk {
        return Err("different params should produce different VKs".into());
    }

    // Record creation in registry
    registry
        .record_creation(&factory_vk)
        .map_err(|e| format!("{e:?}"))?;

    Ok(())
}

fn check_sovereign_peer_exchange() -> Result<(), String> {
    // The sovereign-commitment STORE (register / get / update on the Ledger).
    // NB this half is CRUD, not protocol: `update_sovereign_commitment` writes
    // the store directly, bypassing every `PeerExchange::verify_transition`
    // guard. Until 2026-07-16 this CRUD was the ENTIRE `peer_exchange` check —
    // a gate named for a security protocol that exercised none of it, and which
    // stayed GREEN no matter what the protocol's guards did. The real
    // peer-exchange leg is below.
    let mut ledger = Ledger::new();

    let cell_a_key = test_key("sovereign-a");
    let token_id = test_key("sovereign-token");
    let cell_a_id = CellId::derive_raw(&cell_a_key, &token_id);

    // Register as sovereign cell with a commitment
    let state_commitment = *blake3::hash(b"cell-a-state-v1").as_bytes();
    ledger
        .register_sovereign_cell(cell_a_id, state_commitment)
        .map_err(|e| format!("{e:?}"))?;

    // Verify commitment is retrievable
    let stored = ledger
        .get_sovereign_commitment(&cell_a_id)
        .ok_or("no sovereign commitment for cell A")?;
    if *stored != state_commitment {
        return Err("commitment mismatch in sovereign store".into());
    }

    // Verify cell is recognized as sovereign
    if !ledger.is_sovereign(&cell_a_id) {
        return Err("cell A should be sovereign".into());
    }

    // Update commitment (simulates peer exchange after state transition)
    let new_commitment = *blake3::hash(b"cell-a-state-v2").as_bytes();
    ledger
        .update_sovereign_commitment(&cell_a_id, new_commitment)
        .map_err(|e| format!("{e:?}"))?;

    let updated = ledger
        .get_sovereign_commitment(&cell_a_id)
        .ok_or("commitment lost after update")?;
    if *updated != new_commitment {
        return Err("commitment should be updated".into());
    }

    // ---------------------------------------------------------------------
    // The ACTUAL peer-exchange protocol: two `PeerExchange` sessions, a real
    // signed transition, and the adversarial legs. Each leg below asserts a
    // guard REJECTS — a happy path alone would certify nothing.
    // ---------------------------------------------------------------------
    check_peer_exchange_protocol()
}

/// Drive `dregg_cell_crypto::peer_exchange::PeerExchange` end-to-end: one legal
/// transition must be ACCEPTED, and each of the protocol's fail-closed guards
/// must REJECT. This is the leg that actually binds the preflight gate to the
/// peer-exchange security claims.
fn check_peer_exchange_protocol() -> Result<(), String> {
    use dregg_cell_crypto::peer_exchange::{PeerExchange, PeerExchangeError};

    let alice_cell = CellId::derive_raw(&test_key("px-alice"), &test_key("px-token"));
    let bob_cell = CellId::derive_raw(&test_key("px-bob"), &test_key("px-token"));

    let mut alice = PeerExchange::new(alice_cell, test_key("px-alice-sk"));
    let mut bob = PeerExchange::new(bob_cell, test_key("px-bob-sk"));

    let c0 = *blake3::hash(b"px-state-0").as_bytes();
    let c1 = *blake3::hash(b"px-state-1").as_bytes();
    let effects = *blake3::hash(b"px-effects-1").as_bytes();
    bob.register_peer(alice_cell, c0);
    let alice_pk = alice.public_key();

    // 1. HAPPY PATH: a legitimately signed transition is accepted and advances
    //    Bob's view.
    let t1 = alice.create_transition(c0, c1, effects);
    bob.verify_transition(&t1, &alice_pk)
        .map_err(|e| format!("legal peer transition must verify, got: {e}"))?;
    if bob.peer_commitment(&alice_cell) != Some(c1) {
        return Err("accepted peer transition must advance Bob's view to c1".into());
    }

    // 2. UNKNOWN PEER: a cell Bob never registered is refused.
    let carol_cell = CellId::derive_raw(&test_key("px-carol"), &test_key("px-token"));
    let mut carol = PeerExchange::new(carol_cell, test_key("px-carol-sk"));
    let t_carol = carol.create_transition(c0, c1, effects);
    match bob.verify_transition(&t_carol, &carol.public_key()) {
        Err(PeerExchangeError::UnknownPeer(_)) => {}
        other => return Err(format!("unregistered peer must be refused, got: {other:?}")),
    }

    // 3. REPLAY: re-submitting the already-accepted transition is refused
    //    (its old_commitment no longer matches Bob's advanced view).
    match bob.verify_transition(&t1, &alice_pk) {
        Err(PeerExchangeError::CommitmentMismatch { .. }) => {}
        other => {
            return Err(format!(
                "replayed transition must be refused, got: {other:?}"
            ));
        }
    }

    // 4. RETIRED v1 STARK PROOF fails closed. The canonical signing message does
    //    NOT cover `transition_proof`, so this transition carries a VALID
    //    signature — only the fail-closed guard stops it. Mirrors the executor's
    //    sovereign-witness rule 8.
    //
    //    ORDER MATTERS: `verify_transition` checks signature -> commitment ->
    //    sequence -> timestamp -> proof. `create_transition` bumps Alice's
    //    sequence counter on every call, so this leg must be minted BEFORE any
    //    other transition that Bob rejects, or it arrives with a gapped sequence
    //    and trips `SequenceGap` first — asserting a guard we did not mean to
    //    test. Bob's `last_sequence` is 1 here, so this is sequence 2.
    let c2 = *blake3::hash(b"px-state-2").as_bytes();
    let mut proof_bearing = alice.create_transition(c1, c2, effects);
    proof_bearing.transition_proof = Some(vec![0u8; 256]);
    match bob.verify_transition(&proof_bearing, &alice_pk) {
        Err(PeerExchangeError::InvalidTransitionProof(_)) => {}
        other => {
            return Err(format!(
                "a v1 transition_proof-bearing transition must fail closed, got: {other:?}"
            ));
        }
    }

    // 5. FORGED SIGNATURE: a transition Bob's peer did not sign is refused.
    //    Safe to mint last: the signature check runs FIRST, so this leg's
    //    (now gapped) sequence never gets reached.
    let mut forged = alice.create_transition(c1, c2, effects);
    forged.signature[0] ^= 0xFF;
    match bob.verify_transition(&forged, &alice_pk) {
        Err(PeerExchangeError::InvalidSignature) => {}
        other => return Err(format!("forged signature must be refused, got: {other:?}")),
    }

    // Every rejection above must have left Bob's view untouched at c1.
    if bob.peer_commitment(&alice_cell) != Some(c1) {
        return Err("rejected peer transitions must not mutate Bob's view".into());
    }

    Ok(())
}

fn check_multi_party_atomic() -> Result<(), String> {
    // Multi-party atomic: 2 cells swap value atomically.
    // Both transfers must succeed or both must fail (conservation).
    let token_id = test_key("atomic-token");
    let mut ledger = Ledger::new();

    let alice_key = test_key("atomic-alice");
    let mut alice = Cell::with_balance(alice_key, token_id, 50_000);
    alice.permissions = open_permissions();
    let alice_id = alice.id();
    ledger.insert_cell(alice).map_err(|e| format!("{e:?}"))?;

    let bob_key = test_key("atomic-bob");
    let mut bob = Cell::with_balance(bob_key, token_id, 50_000);
    bob.permissions = open_permissions();
    let bob_id = bob.id();
    ledger.insert_cell(bob).map_err(|e| format!("{e:?}"))?;

    // Grant mutual capabilities
    {
        let a = ledger.get_mut(&alice_id).unwrap();
        a.capabilities.grant(bob_id, AuthRequired::None);
    }
    {
        let b = ledger.get_mut(&bob_id).unwrap();
        b.capabilities.grant(alice_id, AuthRequired::None);
    }

    // Use zero costs so fee doesn't interfere with the test logic.
    let executor = TurnExecutor::new(ComputronCosts::zero());

    // Atomic turn: alice sends 100 to bob
    let mut tb = TurnBuilder::new(alice_id, 0);
    tb.set_fee(1000);
    let action = ActionBuilder::new_unchecked_for_tests(bob_id, "atomic-swap", alice_id)
        .delegation(DelegationMode::None)
        .effect(Effect::Transfer {
            from: alice_id,
            to: bob_id,
            amount: 100,
        })
        .build();
    tb.add_action(action);
    let turn = tb.build();

    let total_before = {
        let a = ledger.get(&alice_id).unwrap();
        let b = ledger.get(&bob_id).unwrap();
        a.state.balance() + b.state.balance()
    };

    match executor.execute(&turn, &mut ledger) {
        TurnResult::Committed { .. } => {}
        TurnResult::Rejected { reason, .. } => {
            return Err(format!("atomic turn rejected: {reason}"));
        }
        _ => return Err("unexpected result".into()),
    }

    // Verify conservation: total value minus fee is preserved.
    // Fee is deducted from alice's balance in Phase 1 (never rolled back).
    let total_after = {
        let a = ledger.get(&alice_id).unwrap();
        let b = ledger.get(&bob_id).unwrap();
        a.state.balance() + b.state.balance()
    };

    // THE EPOCH: balances are SIGNED (i64); totals are i64 sums.
    let fee = 1000i64;
    if total_after != total_before - fee {
        return Err(format!(
            "conservation violated: before={total_before}, after={total_after}, fee={fee}"
        ));
    }

    Ok(())
}

/// The transfer actor cell at `(balance, nonce)` with open permissions — the
/// before/after `Cell` the rotated producer-witness path runs over (the same
/// producer shape `lightclient/src/bin/produce_history_envelope.rs` ships).
fn ivc_producer_cell(balance: i64, nonce: u64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = 7;
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    for _ in 0..nonce {
        let _ = cell.state.increment_nonce();
    }
    cell
}

/// Mint ONE REAL finalized turn on the production descriptor path: the rotated
/// multi-table batch proof from `dregg_turn::rotation_witness`, self-verified at
/// mint. This is the SAME producer recipe the light-client history envelope uses
/// — no fabricated fold deltas, no synthetic chain.
fn mint_real_turn(balance: u64, nonce: u32, amount: u64) -> Result<FinalizedTurn, String> {
    use dregg_circuit::effect_vm::{CellState, Effect as VmEffect};

    let state = CellState::new(balance, nonce);
    let effects = vec![VmEffect::Transfer {
        amount,
        direction: 1,
    }];
    // The rotated transfer DEBIT: balance decreases by `amount`; the rotated
    // trace welds the nonce bump from the v1 sub-trace.
    let before_cell = ivc_producer_cell(balance as i64, nonce as u64);
    let after_cell = ivc_producer_cell((balance as i64) - (amount as i64), nonce as u64);
    let nullifier_root = dregg_circuit::heap_root::empty_heap_root_8();
    let commitments_root = dregg_circuit::heap_root::empty_heap_root_8();
    let receipt_log: Vec<[u8; 32]> = vec![[1u8; 32], [2u8; 32]];
    let leg = mint_rotated_participant_leg(
        &state,
        &effects,
        &before_cell,
        &after_cell,
        &nullifier_root,
        &commitments_root,
        &receipt_log,
        None,
    )
    .map_err(|e| format!("rotated turn leg failed to mint: {e}"))?;
    Ok(FinalizedTurn::new(DescriptorParticipant::rotated(leg)))
}

/// IVC history compression through the REAL whole-chain recursive prover.
///
/// Mints a continuous 2-turn chain of production rotated turn proofs, folds it
/// with `prove_turn_chain_recursive` (per-turn execution re-proven IN-CIRCUIT,
/// temporal continuity bound at the 8-felt anchors), and verifies the wire byte
/// envelope with `verify_whole_chain_proof_bytes` against the fold's own VK
/// fingerprint (the honest-setup anchor extraction).
///
/// Then three ADVERSARIAL teeth — a gate that only shows honest-accept cannot
/// tell a real verifier from `Ok(())`:
///   1. a FORGED chain (turn 2 does not continue turn 1's post-state) must be
///      REFUSED by the fold;
///   2. TAMPERED publics (the envelope's claimed final root bumped) must be
///      REFUSED by the byte verifier;
///   3. a WRONG trust anchor must be REFUSED (VK-pin tooth).
fn check_ivc_history_compression() -> Result<(), String> {
    // A continuous 2-turn chain: turn 1 = (1000, nonce 0) -7-> 993; turn 2
    // starts exactly at (993, nonce 1) — the rotated trace bumps the nonce by 1
    // per Transfer row, so both balance and nonce advance per turn and the
    // rotated state-commit anchors chain (new_root[0] == old_root[1]).
    let step = 7u64;
    let turn1 = mint_real_turn(1_000, 0, step)?;
    let turn2 = mint_real_turn(1_000 - step, 1, step)?;
    let mut turns = vec![turn1, turn2];

    // THE REAL FOLD: one recursive whole-chain proof over both turns.
    let proof = prove_turn_chain_recursive(&turns)
        .map_err(|e| format!("real whole-chain recursive fold failed: {e}"))?;
    if proof.num_turns != 2 {
        return Err(format!("expected 2 folded turns, got {}", proof.num_turns));
    }

    // Honest-setup anchor extraction: the VK fingerprint of OUR OWN fold.
    let vk = proof.root_vk_fingerprint();

    // Wire round-trip + REAL verification of the byte envelope.
    let bytes = proof.to_bytes();
    verify_whole_chain_proof_bytes(&bytes, &vk)
        .map_err(|e| format!("verifier rejected an HONEST whole-chain proof: {e}"))?;

    // ── TOOTH 2 (verify side): tampered claimed publics must be refused. ──
    let mut tampered = WholeChainProofBytes::from_postcard(&bytes)
        .map_err(|e| format!("envelope re-decode failed: {e}"))?;
    tampered.final_root[0] ^= 1; // claim a different final state anchor
    if verify_whole_chain_proof_bytes(&tampered.to_postcard(), &vk).is_ok() {
        return Err(
            "MOCK-GRADE verifier: a whole-chain envelope with a TAMPERED final root was \
             ACCEPTED — the claimed publics are not bound to the proof"
                .into(),
        );
    }

    // ── TOOTH 3 (trust anchor): a wrong VK pin must be refused. ──
    let mut wrong = vk.0;
    wrong[0] ^= 0xFF;
    if verify_whole_chain_proof_bytes(&bytes, &RecursionVk(wrong)).is_ok() {
        return Err(
            "MOCK-GRADE verifier: a whole-chain proof verified against the WRONG trust \
             anchor — the VK pin does not bite"
                .into(),
        );
    }

    // ── TOOTH 1 (prove side): a FORGED chain must be refused by the fold. ──
    // An alien turn whose pre-state anchor is NOT turn 1's post-state anchor
    // (different balance/nonce ⇒ different rotated state commitments): a
    // reordered/spliced history.
    let alien = mint_real_turn(500_000, 9, step)?;
    let forged = vec![turns.remove(0), alien];
    match prove_turn_chain_recursive(&forged) {
        Err(_) => Ok(()), // the temporal tooth bit: the forged chain is refused
        Ok(_) => Err(
            "MOCK-GRADE prover: a FORGED (discontinuous) turn chain folded to a root — \
             the temporal continuity tooth does not bite"
                .into(),
        ),
    }
}
