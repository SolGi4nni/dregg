//! # THE UMEM BOUNDARY PRODUCER — a REAL turn → a REAL `UMemBoundaryWitness`, accepted in
//! # isolation by the deployed universal-memory prover.
//!
//! The flag-day audit (`ae90b6a5`) found the `UmemTurnWitness → UMemBoundaryWitness` producer
//! (`dregg_turn::umem::umem_proving_inputs`) was the missing deployed-plumbing piece: the
//! lowering existed only as test-local helpers, so the SDK/IVC prover could only ever be handed
//! `UMemBoundaryWitness::default()`. This test exercises the LIBRARY producer end-to-end:
//!
//!   1. a real multi-verb turn (two transfers + a set-field + a capability attenuation) executes
//!      through the production `TurnExecutor` with the umem witness lane armed;
//!   2. `umem_proving_inputs` derives the umem-form descriptor + per-op trace + a REAL
//!      (non-`default`) `UMemBoundaryWitness` carrying the turn's genuine touched `(domain, key)`
//!      addresses (under the deployed `heap_addr`/`slot_hash` codecs) with their pre-state image;
//!   3. the deployed `prove_vm_descriptor2_umem` proves the ONE Blum balance over that REAL
//!      boundary through the production `ir2_config`, and the independent verifier accepts;
//!   4. TEETH: a tampered installed value REFUSES (the boundary no longer balances).
//!
//! VK-RISK-FREE: this touches no registry/VK/deployed-prover routing. The deployed rotated prover
//! (`prove_effect_vm_rotated_ir2_with_caveat` / `mint_from_block_witnesses`) still passes
//! `::default()` — the prover-switch is the next sequenced, gated step.

use std::sync::atomic::Ordering;

use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
use dregg_circuit::descriptor_ir2::{
    MemBoundaryWitness, prove_vm_descriptor2_umem, verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_turn::umem::{disciplined, fold, receipt_op, umem_proving_inputs_from};
use dregg_turn::{
    Action, Authorization, CallForest, ComputronCosts, DelegationMode, Effect, TurnExecutor,
    turn::Turn,
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

fn make_open_cell(seed: u8, balance: i64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(37);
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    cell
}

/// Execute the real multi-verb turn on the production executor; return its emitted umem witness
/// (pre projection + Blum op trace) and the turn's receipt hash.
fn real_turn() -> (dregg_turn::umem::UmemTurnWitness, [u8; 32]) {
    let agent = make_open_cell(11, 1000);
    let target = make_open_cell(12, 10);
    let (agent_id, target_id) = (agent.id(), target.id());

    let mut agent_with_cap = agent;
    let slot = agent_with_cap
        .capabilities
        .grant(target_id, AuthRequired::Either)
        .unwrap();
    let mut ledger = Ledger::new();
    ledger.insert_cell(agent_with_cap).unwrap();
    ledger.insert_cell(target).unwrap();

    let executor = TurnExecutor::new(ComputronCosts::zero());
    executor.umem_witness_enabled.store(true, Ordering::Relaxed);

    let mut forest = CallForest::new();
    forest.add_root(Action {
        target: agent_id,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![
            Effect::Transfer {
                from: agent_id,
                to: target_id,
                amount: 7,
            },
            Effect::Transfer {
                from: agent_id,
                to: target_id,
                amount: 5,
            },
            Effect::SetField {
                cell: agent_id,
                index: 2,
                value: [42u8; 32],
            },
            Effect::AttenuateCapability {
                cell: agent_id,
                slot,
                narrower_permissions: AuthRequired::Signature,
                narrower_effects: None,
                narrower_expiry: None,
            },
        ],
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    });
    let turn = Turn {
        agent: agent_id,
        nonce: 0,
        call_forest: forest,
        fee: 0,
        memo: None,
        valid_until: None,
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    };

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed(), "real turn must commit: {result:?}");
    let (_, receipt, _) = result.unwrap_committed();

    let witness = executor
        .last_umem_witness
        .lock()
        .unwrap()
        .take()
        .expect("witness produced")
        .expect("witness emission succeeded");
    // the bridge square holds on the Rust side before anything goes near the prover.
    assert_eq!(fold(&witness.pre, &witness.ops), witness.post);
    assert!(disciplined(&witness.ops));
    assert_eq!(witness.synthesized, 0);

    (witness, receipt.receipt_hash())
}

#[test]
fn producer_yields_real_boundary_the_umem_prover_accepts() {
    let (witness, receipt_hash) = real_turn();

    // The real Blum trace exercises the serial chain (the two transfers debit the SAME balance
    // address twice — the second touch claims the first's installed value, not the init).
    assert!(
        witness.ops.iter().any(|op| op.prev_serial != 0),
        "the real trace must exercise the serial chain (an address touched twice)"
    );

    // Append the caller-owned index-domain receipt write (the turn's log append at position 0),
    // so the produced boundary spans a fourth domain.
    let mut ops = witness.ops.clone();
    ops.push(receipt_op(0, receipt_hash));

    let inputs = umem_proving_inputs_from(&witness.pre, &ops)
        .expect("the producer derives umem proving inputs from the real witness");

    // The produced boundary is REAL — non-`default`, spanning the turn's touched domains.
    assert!(
        !inputs.boundary.addrs.is_empty(),
        "the produced boundary must be non-empty (non-default)"
    );
    assert_eq!(
        inputs.boundary.addrs.len(),
        inputs.boundary.init_vals.len(),
        "boundary addrs and init image are parallel"
    );
    // strictly increasing by (domain, key) — the umem boundary's load-bearing invariant.
    assert!(
        inputs
            .boundary
            .addrs
            .windows(2)
            .all(|w| (w[0].0, w[0].1.as_u32()) < (w[1].0, w[1].1.as_u32())),
        "the produced boundary addresses must be strictly increasing"
    );
    // the turn touched heap (balance/field), caps (the attenuated slot), and index (receipt) —
    // at least three distinct domains in the boundary.
    let mut domains: Vec<u32> = inputs.boundary.addrs.iter().map(|(d, _)| *d).collect();
    domains.dedup();
    assert!(
        domains.len() >= 3,
        "the produced boundary must span the turn's touched domains, got {domains:?}"
    );

    // The deployed universal-memory prover consumes the REAL boundary and proves the ONE Blum
    // balance; the independent verifier accepts.
    let proof = prove_vm_descriptor2_umem(
        &inputs.descriptor,
        &inputs.rows,
        &[],
        &MemBoundaryWitness::default(),
        &[],
        &inputs.boundary,
    )
    .expect("the real turn's memory leg proves against the produced boundary");
    verify_vm_descriptor2(&inputs.descriptor, &proof, &[])
        .expect("the produced-boundary memory leg verifies independently");
}

#[test]
fn producer_boundary_tampered_write_refuses() {
    let (witness, receipt_hash) = real_turn();
    let mut ops = witness.ops.clone();
    ops.push(receipt_op(0, receipt_hash));
    let mut inputs = umem_proving_inputs_from(&witness.pre, &ops).expect("producer derives inputs");

    // Tamper the FIRST guarded row's installed value: the multiset balance must refuse (the
    // read/boundary entries no longer cancel). Column 2 is the installed `value`.
    inputs.rows[0][2] = inputs.rows[0][2] + BabyBear::ONE;
    let r = prove_vm_descriptor2_umem(
        &inputs.descriptor,
        &inputs.rows,
        &[],
        &MemBoundaryWitness::default(),
        &[],
        &inputs.boundary,
    );
    assert!(r.is_err(), "a tampered installed value must refuse");
}
