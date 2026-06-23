//! The Effect VM AIR: shape descriptor (`AIR_DESCRIPTOR`), `EffectVmAir`
//! struct, and the `StarkAir::eval_constraints` body that pins every row
//! to its selector-gated effect semantics.

use super::{EFFECT_VM_WIDTH, NUM_EFFECTS, pi};

// The v1 hand-AIR (`EffectVmAir` + its `StarkAir` impl) is RETIRED; the rotated
// IR-v2 multi-table descriptor (`crate::descriptor_ir2`) is the sole effect-VM
// circuit. Only the shape descriptor `AIR_DESCRIPTOR` (which needs `EFFECT_VM_WIDTH`/
// `NUM_EFFECTS`/`pi`) remains here.

/// The Effect VM AIR's shape descriptor (VK v2; see
/// `circuit::air_descriptor`). Captures the externally visible shape
/// of [`EffectVmAir`] so callers can fingerprint it into VK v2's
/// layered hash.
///
/// `public_input_layout` enumerates the frozen v2 prefix (`pi::BASE_COUNT`)
/// PI surface (commitments, balance limbs, bilateral aggregation roots,
/// sovereign-witness teeth, 30-bit-trunc value limbs). The PI v3 tail
/// (`COMMITTED_HEIGHT`, `RATE_BOUND_TAG`, `CHALLENGE_WINDOW_TAG`) and the
/// CUSTOM_PROOFS region beyond `pi::ACTIVE_BASE_COUNT` are variable/staged
/// and are *not* listed here — their presence is implicit.
pub const AIR_DESCRIPTOR: crate::air_descriptor::AirDescriptor =
    crate::air_descriptor::AirDescriptor {
        air_id: "effect_vm_air_v1",
        column_count: EFFECT_VM_WIDTH,
        public_input_layout: &[
            crate::air_descriptor::PiSlot {
                name: "old_commit",
                offset: pi::OLD_COMMIT_BASE,
                length_in_felts: pi::OLD_COMMIT_LEN,
            },
            crate::air_descriptor::PiSlot {
                name: "new_commit",
                offset: pi::NEW_COMMIT_BASE,
                length_in_felts: pi::NEW_COMMIT_LEN,
            },
            crate::air_descriptor::PiSlot {
                name: "effects_hash",
                offset: pi::EFFECTS_HASH_BASE,
                length_in_felts: pi::EFFECTS_HASH_LEN,
            },
            crate::air_descriptor::PiSlot {
                name: "init_bal_lo",
                offset: pi::INIT_BAL_LO,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "init_bal_hi",
                offset: pi::INIT_BAL_HI,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "final_bal_lo",
                offset: pi::FINAL_BAL_LO,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "final_bal_hi",
                offset: pi::FINAL_BAL_HI,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "net_delta_mag",
                offset: pi::NET_DELTA_MAG,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "net_delta_sign",
                offset: pi::NET_DELTA_SIGN,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "current_block_height",
                offset: pi::CURRENT_BLOCK_HEIGHT,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "max_custom_effects",
                offset: pi::MAX_CUSTOM_EFFECTS,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "custom_effect_count",
                offset: pi::CUSTOM_EFFECT_COUNT,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "approved_handoffs",
                offset: pi::APPROVED_HANDOFFS_BASE,
                length_in_felts: pi::APPROVED_HANDOFFS_LEN,
            },
            crate::air_descriptor::PiSlot {
                name: "turn_hash",
                offset: pi::TURN_HASH_BASE,
                length_in_felts: pi::TURN_HASH_LEN,
            },
            crate::air_descriptor::PiSlot {
                name: "effects_hash_global",
                offset: pi::EFFECTS_HASH_GLOBAL_BASE,
                length_in_felts: pi::EFFECTS_HASH_GLOBAL_LEN,
            },
            crate::air_descriptor::PiSlot {
                name: "actor_nonce",
                offset: pi::ACTOR_NONCE,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "previous_receipt_hash",
                offset: pi::PREVIOUS_RECEIPT_HASH_BASE,
                length_in_felts: pi::PREVIOUS_RECEIPT_HASH_LEN,
            },
            crate::air_descriptor::PiSlot {
                name: "outbound_transfer_count",
                offset: pi::OUTBOUND_TRANSFER_COUNT,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "inbound_transfer_count",
                offset: pi::INBOUND_TRANSFER_COUNT,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "outbound_grant_count",
                offset: pi::OUTBOUND_GRANT_COUNT,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "inbound_grant_count",
                offset: pi::INBOUND_GRANT_COUNT,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "intro_as_introducer_count",
                offset: pi::INTRO_AS_INTRODUCER_COUNT,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "intro_as_recipient_count",
                offset: pi::INTRO_AS_RECIPIENT_COUNT,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "intro_as_target_count",
                offset: pi::INTRO_AS_TARGET_COUNT,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "outgoing_transfer_root",
                offset: pi::OUTGOING_TRANSFER_ROOT_BASE,
                length_in_felts: pi::OUTGOING_TRANSFER_ROOT_LEN,
            },
            crate::air_descriptor::PiSlot {
                name: "incoming_transfer_root",
                offset: pi::INCOMING_TRANSFER_ROOT_BASE,
                length_in_felts: pi::INCOMING_TRANSFER_ROOT_LEN,
            },
            crate::air_descriptor::PiSlot {
                name: "outgoing_grant_root",
                offset: pi::OUTGOING_GRANT_ROOT_BASE,
                length_in_felts: pi::OUTGOING_GRANT_ROOT_LEN,
            },
            crate::air_descriptor::PiSlot {
                name: "incoming_grant_root",
                offset: pi::INCOMING_GRANT_ROOT_BASE,
                length_in_felts: pi::INCOMING_GRANT_ROOT_LEN,
            },
            crate::air_descriptor::PiSlot {
                name: "intro_as_introducer_root",
                offset: pi::INTRO_AS_INTRODUCER_ROOT_BASE,
                length_in_felts: pi::INTRO_AS_INTRODUCER_ROOT_LEN,
            },
            crate::air_descriptor::PiSlot {
                name: "intro_as_recipient_root",
                offset: pi::INTRO_AS_RECIPIENT_ROOT_BASE,
                length_in_felts: pi::INTRO_AS_RECIPIENT_ROOT_LEN,
            },
            crate::air_descriptor::PiSlot {
                name: "intro_as_target_root",
                offset: pi::INTRO_AS_TARGET_ROOT_BASE,
                length_in_felts: pi::INTRO_AS_TARGET_ROOT_LEN,
            },
            crate::air_descriptor::PiSlot {
                name: "is_agent_cell",
                offset: pi::IS_AGENT_CELL,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "sovereign_witness_key_commit",
                offset: pi::SOVEREIGN_WITNESS_KEY_COMMIT_BASE,
                length_in_felts: pi::SOVEREIGN_WITNESS_KEY_COMMIT_LEN,
            },
            crate::air_descriptor::PiSlot {
                name: "sovereign_witness_sequence",
                offset: pi::SOVEREIGN_WITNESS_SEQUENCE,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "is_sovereign_cell",
                offset: pi::IS_SOVEREIGN_CELL,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "sovereign_transition_proof_vk_hash",
                offset: pi::SOVEREIGN_TRANSITION_PROOF_VK_HASH_BASE,
                length_in_felts: pi::SOVEREIGN_TRANSITION_PROOF_VK_HASH_LEN,
            },
            crate::air_descriptor::PiSlot {
                name: "sovereign_transition_proof_commitment",
                offset: pi::SOVEREIGN_TRANSITION_PROOF_COMMITMENT_BASE,
                length_in_felts: pi::SOVEREIGN_TRANSITION_PROOF_COMMITMENT_LEN,
            },
            crate::air_descriptor::PiSlot {
                name: "has_transition_proof",
                offset: pi::HAS_TRANSITION_PROOF,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "bridge_mint_value_limbs",
                offset: pi::BRIDGE_MINT_VALUE_LIMBS_BASE,
                length_in_felts: pi::BRIDGE_MINT_VALUE_LIMBS_LEN,
            },
            crate::air_descriptor::PiSlot {
                name: "bridge_lock_value_limbs",
                offset: pi::BRIDGE_LOCK_VALUE_LIMBS_BASE,
                length_in_felts: pi::BRIDGE_LOCK_VALUE_LIMBS_LEN,
            },
            crate::air_descriptor::PiSlot {
                name: "create_escrow_amount_limbs",
                offset: pi::CREATE_ESCROW_AMOUNT_LIMBS_BASE,
                length_in_felts: pi::CREATE_ESCROW_AMOUNT_LIMBS_LEN,
            },
            // Stage 7-γ.2 unilateral binding (1-arity sibling of bilateral).
            crate::air_descriptor::PiSlot {
                name: "unilateral_attestations_count",
                offset: pi::UNILATERAL_ATTESTATIONS_COUNT,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "unilateral_attestations_root",
                offset: pi::UNILATERAL_ATTESTATIONS_ROOT_BASE,
                length_in_felts: pi::UNILATERAL_ATTESTATIONS_ROOT_LEN,
            },
            // EmitEvent binding (closes #110).
            crate::air_descriptor::PiSlot {
                name: "emit_event_count",
                offset: pi::EMIT_EVENT_COUNT,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "emit_event_topic_hash",
                offset: pi::EMIT_EVENT_TOPIC_HASH_BASE,
                length_in_felts: pi::EMIT_EVENT_TOPIC_HASH_LEN,
            },
            crate::air_descriptor::PiSlot {
                name: "emit_event_payload_hash",
                offset: pi::EMIT_EVENT_PAYLOAD_HASH_BASE,
                length_in_felts: pi::EMIT_EVENT_PAYLOAD_HASH_LEN,
            },
            // γ.2 follow-up (#131/#132): per-cell federation + owner binding.
            crate::air_descriptor::PiSlot {
                name: "federation_id",
                offset: pi::FEDERATION_ID_BASE,
                length_in_felts: pi::FEDERATION_ID_LEN,
            },
            crate::air_descriptor::PiSlot {
                name: "owner_cell_id",
                offset: pi::OWNER_CELL_ID_BASE,
                length_in_felts: pi::OWNER_CELL_ID_LEN,
            },
            // D5: NoteSpend nullifier cross-binding (approach A). Single felt
            // carrying fold_bytes32_to_bb(nullifier); pinned to every
            // sel::NOTE_SPEND row's param0 by the per-row gated constraint.
            crate::air_descriptor::PiSlot {
                name: "notespend_nullifier",
                offset: pi::NOTESPEND_NULLIFIER,
                length_in_felts: 1,
            },
            // D5b: NoteCreate commitment cross-binding (approach A). Single felt
            // carrying fold_bytes32_to_bb(commitment); pinned to every
            // sel::NOTE_CREATE row's param0 by the per-row gated constraint.
            crate::air_descriptor::PiSlot {
                name: "notecreate_commitment",
                offset: pi::NOTECREATE_COMMITMENT,
                length_in_felts: 1,
            },
            // D5c: Burn target cross-binding (approach A). Single felt carrying
            // fold_bytes32_to_bb(target); pinned to every sel::BURN row's
            // param0 (BURN_TARGET) by the per-row gated constraint.
            crate::air_descriptor::PiSlot {
                name: "burn_target",
                offset: pi::BURN_TARGET_PI,
                length_in_felts: 1,
            },
            // Light-client conservation: per-cell ASSET CLASS (PI v3). Single
            // felt (the folded committed token_id); row-0-pinned to the
            // aux_off::ASSET_CLASS column so the per-asset conservation gate
            // partitions each proof's NET_DELTA by the PI-bound class.
            crate::air_descriptor::PiSlot {
                name: "asset_class",
                offset: pi::v3::ASSET_CLASS,
                length_in_felts: 1,
            },
        ],
        // Constraint groups: selector validity (NUM_EFFECTS+1), per-effect
        // gated constraints (~NUM_EFFECTS large groups), boundary bindings
        // for commitments / balance limbs / sovereign teeth, bilateral
        // aggregation accumulators. Number is a stable property of the AIR
        // shape — when constraints are added/removed, this bumps.
        //
        // W9-RANGECHECK adds CONSTRAINT GROUP 2a: an in-circuit balance-limb
        // range / underflow proof contributing
        //   2 * BAL_LIMB_BITS booleanity + 2 recomposition
        // unconditional constraints. We fold its presence into the descriptor
        // count (+1 for the group) so the VK-v2 fingerprint binds the new AIR
        // shape; the per-bit constraints are an internal property of the group.
        // + 1 (D5: NoteSpend nullifier cross-binding — one per-row gated
        //   equality `s_notespend * (param0 - PI[NOTESPEND_NULLIFIER])`).
        // + 1 (D5b: NoteCreate commitment cross-binding — one per-row gated
        //   equality `s_notecreate * (param0 - PI[NOTECREATE_COMMITMENT])`).
        // + 1 (D5c: Burn target cross-binding — one per-row gated equality
        //   `s_burn * (param0 - PI[BURN_TARGET_PI])`).
        constraint_polynomial_count: NUM_EFFECTS + 1 + NUM_EFFECTS + 1 + 1 + 1 + 1,
        // 32 prior + 8 (γ.2 #131/#132: 4 FEDERATION_ID + 4 OWNER_CELL_ID
        // row-0 boundary bindings) + 1 (light-client conservation: ASSET_CLASS
        // row-0 boundary binding to PI[v3::ASSET_CLASS]).
        boundary_constraint_count: 41,
        max_degree: 9,
        source_hash: None,
    };

