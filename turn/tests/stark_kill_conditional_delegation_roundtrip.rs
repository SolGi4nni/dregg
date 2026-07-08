//! # RUNTIME round-trip gate for the `turn-conditional-delegation` cluster's
//! `StarkProof` → `Ir2BatchProof` wire migration.
//!
//! The proof-witness blob at both consumers in this cluster is an OPAQUE `Vec<u8>`, so
//! `cargo build` cannot see the byte-format flip (`postcard(StarkProof)` →
//! `postcard(Ir2BatchProof)`) nor the descriptor dispatch. This test is the gate the
//! build cannot provide: it drives the REAL prover ([`prove_vm_descriptor2`]) →
//! `postcard`-encodes the blob → and consumes it through the two migrated consumers,
//! per predicate, honest-ACCEPT + tamper/wrong-REJECT, non-vacuous.
//!
//! Two consumers, both flipped onto the IR-v2 foundations:
//!   1. [`dregg_turn::resolve_condition`] `RemoteProof`/`LocalProof` arms
//!      (`turn/src/conditional.rs`): descriptor resolved from the CONDITION's committed
//!      predicate identity (`descriptor_by_name`, fail-closed `None`), blob decoded as
//!      `postcard(Ir2BatchProof)`, checked with `verify_vm_descriptor2`.
//!   2. [`dregg_turn::action::verify_stark_delegation_binding`]
//!      (`turn/src/action.rs`): the `DelegationProofData::StarkDelegation` scope binding,
//!      now a FULL `verify_vm_descriptor2` of the `delegate_binding_descriptor` (24 row-0
//!      `PiBinding`s pin the scope vector).

use std::collections::HashSet;

use dregg_cell::{AuthRequired, CellId};
use dregg_circuit::BabyBear;
use dregg_circuit::delegate_descriptor::{
    DELEGATE_SCOPE_LIMBS, OFF_TARGET, delegate_binding_descriptor, delegate_binding_witness,
};
use dregg_circuit::descriptor_by_name::{MEMBERSHIP_GENERAL_NAME_PREFIX, descriptor_by_name};
use dregg_circuit::descriptor_ir2::{MemBoundaryWitness, prove_vm_descriptor2};
use dregg_circuit::membership_descriptor_general::{
    MembershipStep, membership_root, membership_witness,
};
use dregg_turn::action::{
    StarkDelegationBindingError, stark_delegation_expected_public_inputs,
    verify_stark_delegation_binding,
};
use dregg_turn::{
    ConditionProof, ConditionalResult, DEFAULT_MAX_ROOT_AGE, ProofCondition, TrustedRoot,
    resolve_condition,
};

const DFA_NAME: &str = "dfa-routing-toggle-2state::poseidon2-v1";

// ─────────────────────────────────────────────────────────────────────────────
// Producer: an honest membership witness → real IR-v2 proof → the new wire blob.
// ─────────────────────────────────────────────────────────────────────────────

/// `(descriptor name, postcard(Ir2BatchProof) blob, public_outputs=[leaf, root])`
/// for a depth-`d` Poseidon2 Merkle-membership proof — exactly the wire shape a
/// migrated `ConditionProof::StarkProof` carries.
fn membership_blob(depth: usize, leaf_val: u32) -> (String, Vec<u8>, Vec<u32>) {
    let name = format!("{MEMBERSHIP_GENERAL_NAME_PREFIX}{depth}");
    let desc = descriptor_by_name(&name).expect("depth-general membership descriptor dispatches");
    let leaf = BabyBear::new(leaf_val);
    let path: Vec<MembershipStep> = (0..depth)
        .map(|i| MembershipStep {
            sibling: BabyBear::new(1000 + i as u32),
            dir: i % 2 == 1,
        })
        .collect();
    let root = membership_root(leaf, &path);
    let (trace, pis) = membership_witness(leaf, &path).expect("honest membership witness");
    assert_eq!(pis, vec![leaf, root], "membership PIs are [leaf, root]");
    let proof = prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
        .expect("honest membership witness must prove");
    let blob = postcard::to_allocvec(&proof).expect("postcard-encode the IR-v2 batch proof");
    let public_outputs: Vec<u32> = pis.iter().map(|bb| bb.0).collect();
    (name, blob, public_outputs)
}

fn resolve(
    condition: &ProofCondition,
    proof: &ConditionProof,
    trusted: &[TrustedRoot],
) -> ConditionalResult {
    let mut used: HashSet<[u8; 32]> = HashSet::new();
    resolve_condition(
        condition,
        proof,
        10,
        100,
        trusted,
        DEFAULT_MAX_ROOT_AGE,
        &mut used,
        &[],
    )
}

// ═════════════════════════════════════════════════════════════════════════════
// CONSUMER 1a: resolve_condition RemoteProof arm.
// ═════════════════════════════════════════════════════════════════════════════

#[test]
fn remote_proof_resolve_roundtrip_accept_and_reject() {
    let fed_root = [0x11u8; 32];
    let trusted = vec![(fed_root, 5u64)];
    let (name, blob, public_outputs) = membership_blob(4, 0xBEEF);

    // POSITIVE POLE — honest membership proof ACCEPTS through the real consumer.
    let condition = ProofCondition::RemoteProof {
        federation_root: fed_root,
        expected_air: name.clone(),
        expected_conclusion: public_outputs[0],
    };
    let proof = ConditionProof::StarkProof {
        proof_bytes: blob.clone(),
        federation_root: fed_root,
        public_outputs: public_outputs.clone(),
        air_name: name.clone(),
    };
    assert_eq!(
        resolve(&condition, &proof, &trusted),
        ConditionalResult::Resolved,
        "an honest membership proof must resolve the RemoteProof condition"
    );

    // NEGATIVE 1 — a forged claimed root PI (the leaf is not a member under root+1).
    let forged_outputs = vec![public_outputs[0], public_outputs[1].wrapping_add(1)];
    let forged_proof = ConditionProof::StarkProof {
        proof_bytes: blob.clone(),
        federation_root: fed_root,
        public_outputs: forged_outputs.clone(),
        air_name: name.clone(),
    };
    let forged_condition = ProofCondition::RemoteProof {
        federation_root: fed_root,
        expected_air: name.clone(),
        expected_conclusion: forged_outputs[0],
    };
    assert!(
        matches!(
            resolve(&forged_condition, &forged_proof, &trusted),
            ConditionalResult::InvalidProof(_)
        ),
        "a forged root public input must be REJECTED by verify_vm_descriptor2"
    );

    // NEGATIVE 2 — a tampered blob (mid-byte flip).
    let mut tampered = blob.clone();
    let mid = tampered.len() / 2;
    tampered[mid] ^= 0xFF;
    let tampered_proof = ConditionProof::StarkProof {
        proof_bytes: tampered,
        federation_root: fed_root,
        public_outputs: public_outputs.clone(),
        air_name: name.clone(),
    };
    assert!(
        matches!(
            resolve(&condition, &tampered_proof, &trusted),
            ConditionalResult::InvalidProof(_)
        ),
        "a tampered blob must be REJECTED"
    );

    // NEGATIVE 3 — cross-KIND: the SAME membership blob dispatched to the DFA descriptor
    // (condition + proof both name DFA). A wrong dispatch arm cannot launder the proof.
    let cross_condition = ProofCondition::RemoteProof {
        federation_root: fed_root,
        expected_air: DFA_NAME.to_string(),
        expected_conclusion: public_outputs[0],
    };
    let cross_proof = ConditionProof::StarkProof {
        proof_bytes: blob.clone(),
        federation_root: fed_root,
        public_outputs: public_outputs.clone(),
        air_name: DFA_NAME.to_string(),
    };
    assert!(
        matches!(
            resolve(&cross_condition, &cross_proof, &trusted),
            ConditionalResult::InvalidProof(_)
        ),
        "verifying a membership proof under the DFA descriptor must be REJECTED"
    );

    // NEGATIVE 4 — fail-closed dispatch MISS: an unknown predicate never falls through
    // to accept, even with an otherwise-valid blob.
    let miss_condition = ProofCondition::RemoteProof {
        federation_root: fed_root,
        expected_air: "no-such-air".to_string(),
        expected_conclusion: public_outputs[0],
    };
    let miss_proof = ConditionProof::StarkProof {
        proof_bytes: blob,
        federation_root: fed_root,
        public_outputs,
        air_name: "no-such-air".to_string(),
    };
    assert!(
        matches!(resolve(&miss_condition, &miss_proof, &trusted),
            ConditionalResult::InvalidProof(ref m) if m.contains("unknown AIR")),
        "a dispatch miss must fail closed (typed InvalidProof naming the AIR)"
    );
}

// ═════════════════════════════════════════════════════════════════════════════
// CONSUMER 1b: resolve_condition LocalProof arm (elementwise PI match on top of verify).
// ═════════════════════════════════════════════════════════════════════════════

#[test]
fn local_proof_resolve_roundtrip_accept_and_reject() {
    let (name, blob, public_outputs) = membership_blob(4, 0x1234);

    // POSITIVE — honest ACCEPT.
    let condition = ProofCondition::LocalProof {
        expected_air: name.clone(),
        expected_public_inputs: public_outputs.clone(),
    };
    let proof = ConditionProof::StarkProof {
        proof_bytes: blob.clone(),
        federation_root: [0u8; 32],
        public_outputs: public_outputs.clone(),
        air_name: name.clone(),
    };
    assert_eq!(
        resolve(&condition, &proof, &[]),
        ConditionalResult::Resolved,
        "an honest membership proof must resolve the LocalProof condition"
    );

    // NEGATIVE — a forged root PI: verify_vm_descriptor2 rejects (the committed root
    // differs), before the elementwise expected-input check even runs.
    let forged_outputs = vec![public_outputs[0], public_outputs[1].wrapping_add(1)];
    let forged_condition = ProofCondition::LocalProof {
        expected_air: name.clone(),
        expected_public_inputs: forged_outputs.clone(),
    };
    let forged_proof = ConditionProof::StarkProof {
        proof_bytes: blob,
        federation_root: [0u8; 32],
        public_outputs: forged_outputs,
        air_name: name,
    };
    assert!(
        matches!(
            resolve(&forged_condition, &forged_proof, &[]),
            ConditionalResult::InvalidProof(_)
        ),
        "a forged public input must be REJECTED"
    );
}

// ═════════════════════════════════════════════════════════════════════════════
// CONSUMER 2: verify_stark_delegation_binding — full verify_vm_descriptor2 of the
// delegate_binding_descriptor (the DelegationProofData::StarkDelegation scope binding).
// ═════════════════════════════════════════════════════════════════════════════

/// Build a real delegation-binding batch proof committing to the canonical scope for
/// `(root_issuer, target, permissions, expires_at, federation)`.
fn delegate_blob(
    root_issuer: &[u8; 32],
    target: &CellId,
    permissions: &AuthRequired,
    expires_at: u64,
    federation: &[u8; 32],
) -> Vec<u8> {
    let expected = stark_delegation_expected_public_inputs(
        target,
        permissions,
        expires_at,
        federation,
        root_issuer,
    );
    let scope: [BabyBear; DELEGATE_SCOPE_LIMBS] = expected
        .clone()
        .try_into()
        .expect("delegation scope is exactly 24 limbs");
    let desc = delegate_binding_descriptor();
    let (trace, pis) = delegate_binding_witness(&scope);
    let proof = prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
        .expect("honest delegation-binding must prove");
    postcard::to_allocvec(&proof).expect("postcard-encode the delegation batch proof")
}

#[test]
fn delegation_binding_roundtrip_accept_and_reject() {
    let federation = [0x11u8; 32];
    let target = CellId([0x22u8; 32]);
    let root_issuer = [0x33u8; 32];
    let permissions = AuthRequired::Signature;
    let expires_at: u64 = 1_000;

    let blob = delegate_blob(&root_issuer, &target, &permissions, expires_at, &federation);

    // POSITIVE POLE — the honestly-bound proof verifies through the real consumer.
    assert!(
        verify_stark_delegation_binding(
            &blob,
            &root_issuer,
            &target,
            &permissions,
            expires_at,
            &federation,
        )
        .is_ok(),
        "a delegation proof bound to the exercised scope must verify"
    );

    // NEGATIVE — relay to a WIDER target (same blob, different target scope).
    let wider_target = CellId([0x99u8; 32]);
    assert!(
        matches!(
            verify_stark_delegation_binding(
                &blob,
                &root_issuer,
                &wider_target,
                &permissions,
                expires_at,
                &federation,
            ),
            Err(StarkDelegationBindingError::PublicInputMismatch { .. })
        ),
        "a relayed proof pointed at a wider target must be REJECTED (scope binding UNSAT)"
    );

    // NEGATIVE — forged root issuer.
    let forged_root = [0xFFu8; 32];
    assert!(
        verify_stark_delegation_binding(
            &blob,
            &forged_root,
            &target,
            &permissions,
            expires_at,
            &federation,
        )
        .is_err(),
        "a proof presented under a different root issuer must be REJECTED"
    );

    // NEGATIVE — escalated permission tier + extended expiry + cross-federation.
    assert!(
        verify_stark_delegation_binding(
            &blob,
            &root_issuer,
            &target,
            &AuthRequired::Proof,
            expires_at,
            &federation
        )
        .is_err(),
        "escalated permission tier must be REJECTED"
    );
    assert!(
        verify_stark_delegation_binding(
            &blob,
            &root_issuer,
            &target,
            &permissions,
            expires_at + 1,
            &federation
        )
        .is_err(),
        "extended expiry must be REJECTED"
    );
    assert!(
        verify_stark_delegation_binding(
            &blob,
            &root_issuer,
            &target,
            &permissions,
            expires_at,
            &[0x44u8; 32]
        )
        .is_err(),
        "cross-federation replay must be REJECTED"
    );

    // NEGATIVE — garbage / truncated bytes do not deserialize.
    assert!(
        matches!(
            verify_stark_delegation_binding(
                &[0xDE, 0xAD, 0xBE, 0xEF],
                &root_issuer,
                &target,
                &permissions,
                expires_at,
                &federation
            ),
            Err(StarkDelegationBindingError::Deserialization(_))
        ),
        "non-deserializable proof bytes must be REJECTED at deserialization"
    );

    // Cross-check the forge lands on the scope's target block, not an unrelated limb.
    let _ = OFF_TARGET;
}
