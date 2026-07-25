//! The shared proving recipe behind [`dregg_turn::ProvenReceipt`] — one real wide
//! rotated EffectVM STARK, minted for a Transfer debit and bound to a turn hash.
//!
//! `dregg_turn::conditional` keeps the whole `TurnProven` RESOLVER (the verify
//! floor: `resolve_condition` + `verify_effect_vm_condition_proof`) and the
//! `ProvenReceipt` type. Only the MINT — which drives
//! `dregg_circuit::descriptor_ir2::prove_vm_descriptor2` over the wide rotated
//! producer — lives here, because it is proof PRODUCTION.
//!
//! This is the single place the downstream proof-carrying features
//! (`service_promise`, `shared_fork`, the cross-fed atomic demos,
//! `full_pipeline`) obtain a genuine `EffectVmProof` for tests/demos, instead of
//! each re-implementing the proving. The PRODUCTION producer is the node commit
//! pipeline extracting the `"effect-vm-rotated"` leg from
//! `dregg_sdk::FullTurnProof`.

use dregg_circuit::BabyBear;
use dregg_circuit::descriptor_ir2::verify_vm_descriptor2;
use dregg_turn::conditional::ProvenReceipt;
use dregg_turn::turn::TurnReceipt;

/// Mint a GENUINE [`ProvenReceipt`] for a Transfer DEBIT of `amount` bound to `turn_hash`
/// — a real (non-recursive, DEFAULT-config) wide rotated EffectVM STARK the resolver
/// accepts, NOT a mock. The `PI[TURN_HASH]` slot is filled with the canonical projection
/// of `turn_hash` (the honest producer's job — the AIR does not constrain that slot), and
/// the wide 8-felt endpoints are packed to the condition's 32-byte commitment form.
///
/// This is the SAME proving recipe [`crate::rotation_witness::mint_rotated_participant_leg`] runs,
/// proved under the deployed non-recursive `prove_vm_descriptor2` (the verify floor) so the
/// resolver's self-detecting `verify_vm_descriptor2` accepts it. It is the single place the
/// downstream proof-carrying features (`service_promise`, `shared_fork`, the cross-fed atomic
/// demos, `full_pipeline`) obtain a genuine `EffectVmProof` for tests/demos, instead of each
/// re-implementing the proving. (The PRODUCTION producer is the node commit pipeline extracting
/// the `"effect-vm-rotated"` leg from `dregg_sdk::FullTurnProof` — see [`ProvenReceipt`].)
///
/// Lives in `dregg-turn-prover` (the wide rotated PRODUCER); the resolver's verify floor is
/// unconditional in core `dregg-turn`. Heavy: mints one real wide rotated proof.
pub fn mint_transfer_proven_receipt(turn_hash: [u8; 32], amount: u64) -> ProvenReceipt {
    use dregg_cell::commitment::RotationCarrierMaterial;
    use dregg_cell::{AuthRequired, Ledger, Permissions};
    use dregg_circuit::descriptor_ir2::prove_vm_descriptor2;
    use dregg_circuit::effect_vm::pi as p;
    use dregg_circuit::effect_vm::trace_rotated::{
        RotatedBlockWitness, generate_rotated_effect_vm_descriptor_and_trace_wide,
        transfer_caveat_manifest,
    };
    use dregg_circuit::effect_vm::{CellState, Effect};
    use dregg_commit::typed::canonical_32_to_felts_4;
    use dregg_turn::rotation_witness::{empty_revoked_root_8, produce, sender_membership_teeth};

    // A producer cell that admits the actor without auth gating (the rotated producer recipe).
    let open = Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    };
    let mut pk = [0u8; 32];
    pk[0] = 7;
    let balance = 1000i64;
    let make_cell = |bal: i64| {
        let mut cell = dregg_cell::Cell::with_balance(pk, [0u8; 32], bal);
        cell.permissions = open.clone();
        cell
    };
    let before_cell = make_cell(balance);
    let after_cell = make_cell(balance - amount as i64);

    let state = CellState::new(balance as u64, 0);
    let effects = vec![Effect::Transfer {
        amount,
        direction: 1,
    }];
    let nullifier_root = dregg_circuit::heap_root::empty_heap_root_8();
    let commitments_root = dregg_circuit::heap_root::empty_heap_root_8();
    let receipt_log: Vec<[u8; 32]> = vec![[1u8; 32], [2u8; 32]];

    let mut ledger = Ledger::new();
    ledger
        .insert_cell(after_cell.clone())
        .expect("seed ledger for the proven-receipt mint");
    let carrier = RotationCarrierMaterial::default();
    let before_w = produce(
        &before_cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &empty_revoked_root_8(),
        &receipt_log,
        &carrier,
    );
    let after_w = produce(
        &after_cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &empty_revoked_root_8(),
        &receipt_log,
        &carrier,
    );
    let before_block = RotatedBlockWitness::new(before_w.pre_limbs.clone(), before_w.iroot)
        .expect("before block witness");
    let after_block = RotatedBlockWitness::new(after_w.pre_limbs.clone(), after_w.iroot)
        .expect("after block witness");
    let caveat = transfer_caveat_manifest();
    let (desc, trace, mut dpis, map_heaps, mem_boundary) =
        generate_rotated_effect_vm_descriptor_and_trace_wide(
            &state,
            &effects,
            &before_block,
            &after_block,
            &caveat,
            None,
            None,
            None,
            Some(sender_membership_teeth(&before_cell)),
        )
        .expect("wide rotated transfer producer");

    // Honest producer: fill the (AIR-unconstrained) TURN_HASH slot with the canonical
    // projection of the turn identity, so the proof binds THIS turn.
    let th = canonical_32_to_felts_4(&turn_hash);
    dpis[p::TURN_HASH_BASE..p::TURN_HASH_BASE + p::TURN_HASH_LEN].copy_from_slice(&th);

    let proof = prove_vm_descriptor2(&desc, &trace, &dpis, &mem_boundary, &map_heaps)
        .expect("default-config wide effect-vm prove");
    verify_vm_descriptor2(&desc, &proof, &dpis).expect("minted proof self-verifies");

    let effect_vm_proof_bytes =
        postcard::to_allocvec(&proof).expect("postcard-encode the rotated Ir2BatchProof");
    let effect_vm_public_inputs: Vec<u32> = dpis.iter().map(|f| f.as_u32()).collect();
    let n = dpis.len();
    let wide_old: [BabyBear; 8] = dpis[n - 16..n - 8].try_into().unwrap();
    let wide_new: [BabyBear; 8] = dpis[n - 8..n].try_into().unwrap();
    let pre_commitment = dregg_turn::executor::TurnExecutor::commitment_8bb_to_bytes(wide_old);
    let post_commitment = dregg_turn::executor::TurnExecutor::commitment_8bb_to_bytes(wide_new);

    let receipt = TurnReceipt {
        turn_hash,
        ..Default::default()
    };
    ProvenReceipt {
        receipt,
        effect_vm_proof_bytes,
        effect_vm_public_inputs,
        pre_commitment,
        post_commitment,
    }
}
