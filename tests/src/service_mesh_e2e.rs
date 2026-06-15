#![cfg(not(feature = "recursion"))]
//! End-to-end service mesh integration tests.
//!
//! Entirely v1: both live tests prove the CAS effects through the bespoke
//! `EffectVmAir` (recursion-absent) and assert the STARK verifies, so the whole
//! module is gated `not(recursion)`.
//!
//! Tests the full service mesh pipeline:
//! 1. ContentStore: nameless write -> verify hash = address (CAS)
//! 2. Splice: modify blob -> verify new hash, old hash nullified
//! 3. Mount service entry: CAS -> resolve -> get back sturdy ref
//! 4. Governance vote -> route table changes -> verify new commitment
//!
//! All operations are proven via the Effect VM STARK. No mocks.

use dregg_circuit::effect_vm::{
    self as effect_vm, CellState, Effect, EffectVmAir, EffectVmContext, generate_effect_vm_trace,
    generate_effect_vm_trace_ext,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::poseidon2::{hash_2_to_1, hash_4_to_1, hash_many};
use dregg_circuit::stark::{self, StarkProof};

// =============================================================================
// Content-Addressable Store (CAS) Primitives
// =============================================================================

/// Compute the content address (hash) of a blob.
/// In the circuit, content is represented as a sequence of BabyBear elements.
fn content_address(data: &[BabyBear]) -> BabyBear {
    hash_many(data)
}

/// Compute a nullifier for a content address (proves the old content was consumed/replaced).
fn content_nullifier(address: BabyBear, owner_key: BabyBear) -> BabyBear {
    hash_2_to_1(address, owner_key)
}

/// Compute a service entry commitment: hash(service_name, content_address, version).
fn service_entry_commitment(
    service_name: BabyBear,
    content_address: BabyBear,
    version: u32,
) -> BabyBear {
    hash_4_to_1(&[
        service_name,
        content_address,
        BabyBear::new(version),
        BabyBear::ZERO,
    ])
}

/// Compute a governance vote commitment: hash(voter, proposal_hash, vote_weight).
fn vote_commitment(voter: BabyBear, proposal: BabyBear, weight: u32) -> BabyBear {
    hash_4_to_1(&[voter, proposal, BabyBear::new(weight), BabyBear::ZERO])
}

// =============================================================================
// Helper
// =============================================================================

/// Prove effects and return the STARK proof.
fn prove_effects(initial_state: &CellState, effects: &[Effect]) -> StarkProof {
    let mut ctx = EffectVmContext::default();
    ctx.actor_nonce = initial_state.nonce as u64;
    prove_effects_ext(initial_state, effects, ctx)
}

/// Prove effects with an explicit context and return the STARK proof.
fn prove_effects_ext(
    initial_state: &CellState,
    effects: &[Effect],
    ctx: EffectVmContext,
) -> StarkProof {
    let (trace, public_inputs) = generate_effect_vm_trace_ext(initial_state, effects, ctx);
    let air = EffectVmAir::new(trace.len());
    let proof = stark::prove(&air, &trace, &public_inputs);
    let result = stark::verify(&air, &proof, &public_inputs);
    assert!(
        result.is_ok(),
        "STARK verification failed: {:?}",
        result.err()
    );
    proof
}

// =============================================================================
// Test 1: ContentStore — nameless write -> verify hash = address
// =============================================================================

/// Write content to the store (content-addressed). The "address" is the
/// Poseidon2 hash of the content. Prove via STARK that the stored commitment
/// matches the content hash.
#[test]
fn test_content_store_nameless_write() {
    // Simulate writing a blob: content = [0x48, 0x65, 0x6C, 0x6C, 0x6F] ("Hello" as field elements)
    let content: Vec<BabyBear> = vec![
        BabyBear::new(0x48),
        BabyBear::new(0x65),
        BabyBear::new(0x6C),
        BabyBear::new(0x6C),
        BabyBear::new(0x6F),
    ];
    let address = content_address(&content);

    // The content store records: field[0] = content_address (the CAS key).
    // We prove this write via a SetField effect.
    let initial_state = CellState::new(1000, 0);

    let effects = vec![Effect::SetField {
        field_idx: 0,
        value: address,
    }];

    let (trace, _public_inputs) = generate_effect_vm_trace(&initial_state, &effects);

    // Verify the content address is correctly stored.
    let row = &trace[0];
    let stored_value = row[effect_vm::STATE_AFTER_BASE + effect_vm::state::FIELD_BASE + 0];
    assert_eq!(
        stored_value, address,
        "Stored value should equal content hash (CAS property)"
    );

    // Verify content-addressability: same content always produces same address.
    let content2 = content.clone();
    let address2 = content_address(&content2);
    assert_eq!(address, address2, "CAS: same content -> same address");

    // Different content -> different address.
    let different_content = vec![
        BabyBear::new(0x42),
        BabyBear::new(0x79),
        BabyBear::new(0x65),
    ];
    let different_address = content_address(&different_content);
    assert_ne!(
        address, different_address,
        "CAS: different content -> different address"
    );

    // Prove and verify via STARK.
    let proof = prove_effects(&initial_state, &effects);
    assert!(proof.trace_len >= 2);
    assert!(!proof.query_proofs.is_empty());
}

// =============================================================================
// Test 2: Splice — modify blob -> verify new hash, old hash nullified
// =============================================================================

/// Splice a content blob: write new content, nullify old content address.
/// Proves:
///   - New content address is correctly computed
///   - Old content address is nullified (via nullifier derivation)
///   - Both operations happen atomically in one STARK proof
#[test]
fn test_content_splice_nullifies_old() {
    let owner_key = BabyBear::new(0xCAFE_BABE);

    // Original content and its address.
    let old_content = vec![BabyBear::new(1), BabyBear::new(2), BabyBear::new(3)];
    let old_address = content_address(&old_content);

    // New content (spliced) and its address.
    let new_content = vec![
        BabyBear::new(1),
        BabyBear::new(2),
        BabyBear::new(99), // changed byte
    ];
    let new_address = content_address(&new_content);
    assert_ne!(old_address, new_address, "splice should change address");

    // Compute nullifier for the old content (proves old was consumed).
    let nullifier = content_nullifier(old_address, owner_key);

    // Initial state: field[0] = old_address (content store), field[1] = 0 (no nullifier yet).
    let mut initial_state = CellState::new(5000, 0);
    initial_state.fields[0] = old_address;
    initial_state.refresh_commitment();

    // Splice = two effects:
    //   1. SetField[0] = new_address (update content)
    //   2. SetField[1] = nullifier (record that old was consumed)
    let effects = vec![
        Effect::SetField {
            field_idx: 0,
            value: new_address,
        },
        Effect::SetField {
            field_idx: 1,
            value: nullifier,
        },
    ];

    let (trace, public_inputs) = generate_effect_vm_trace(&initial_state, &effects);

    // After effect 1 (row 0): field[0] = new_address.
    let row0 = &trace[0];
    let after_splice_field0 = row0[effect_vm::STATE_AFTER_BASE + effect_vm::state::FIELD_BASE + 0];
    assert_eq!(
        after_splice_field0, new_address,
        "field[0] should be updated to new content address"
    );

    // After effect 2 (row 1): field[1] = nullifier.
    let row1 = &trace[1];
    let after_nullify_field1 = row1[effect_vm::STATE_AFTER_BASE + effect_vm::state::FIELD_BASE + 1];
    assert_eq!(
        after_nullify_field1, nullifier,
        "field[1] should contain the nullifier of old content"
    );

    // Verify nullifier binds to old_address: nullifier = hash(old_address, owner_key).
    let recomputed_nullifier = hash_2_to_1(old_address, owner_key);
    assert_eq!(
        nullifier, recomputed_nullifier,
        "nullifier should be deterministically derived from old address + owner"
    );

    // Prove atomically with single STARK.
    let proof = prove_effects(&initial_state, &effects);
    assert!(proof.trace_len >= 2);

    // The old_commitment != new_commitment (state changed).
    assert_ne!(
        public_inputs[0], public_inputs[1],
        "state commitment should change after splice"
    );
}

// RETIRED (dregg3): Test 3 (test_mount_service_entry_and_export) and Test 4
// (test_governance_vote_updates_route_table) drove the CapTP sturdyref family
// — ExportSturdyRef and ValidateHandoff — which the dregg3 reduction dissolved
// from the circuit Effect enum. The CAS content-store tests above (Test 1/2)
// are unaffected and remain live. The two handoff/sturdyref tests are deleted
// because there is no surviving effect to mount/validate against.
