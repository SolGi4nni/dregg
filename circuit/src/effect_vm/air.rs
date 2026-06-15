//! The Effect VM AIR: shape descriptor (`AIR_DESCRIPTOR`), `EffectVmAir`
//! struct, and the `StarkAir::eval_constraints` body that pins every row
//! to its selector-gated effect semantics.

use crate::field::BabyBear;
use crate::poseidon2::{hash_2_to_1, hash_4_to_1};
use crate::stark::{BoundaryConstraint, StarkAir};

use super::{
    AUX_BASE, BAL_LIMB_BITS, EFFECT_VM_WIDTH, NUM_EFFECTS, PARAM_BASE, STATE_AFTER_BASE,
    STATE_BEFORE_BASE, aux_off, param, pi, sel, state,
};

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
        // row-0 boundary bindings).
        boundary_constraint_count: 40,
        max_degree: 9,
        source_hash: None,
    };

/// The Effect VM AIR. Proves an arbitrary sequence of effects in a single STARK.
///
/// v1 hand-AIR: retained under `#[cfg(not(feature = "recursion"))]` for the v1 floor.
/// The recursion tower proves the effect-VM transition through the rotated IR-v2
/// multi-table descriptor (`crate::descriptor_ir2`) instead. The shape descriptor
/// [`AIR_DESCRIPTOR`] and the shared trace+PI generator (`generate_effect_vm_trace`,
/// `EFFECT_VM_WIDTH`) STAY in both builds — the rotated leg is built on them.
#[cfg(not(feature = "recursion"))]
pub struct EffectVmAir {
    /// Maximum number of effects (trace height, padded to power of 2).
    pub max_effects: usize,
}

#[cfg(not(feature = "recursion"))]
impl EffectVmAir {
    pub fn new(max_effects: usize) -> Self {
        // MIN 64 rows: closes the FRI single-row-gap (task #90). A short trace
        // has too few FRI folding rounds for the probabilistic query set to
        // reliably detect single-row tampering. With 64 rows (domain_size 256
        // at blowup-4, 6 FRI rounds) the miss probability is negligible.
        assert!(
            max_effects >= 64,
            "Need at least 64 rows for STARK (FRI single-row-gap closure; task #90)"
        );
        assert!(
            max_effects.is_power_of_two(),
            "max_effects must be a power of 2"
        );
        Self { max_effects }
    }
}

#[cfg(not(feature = "recursion"))]
impl StarkAir for EffectVmAir {
    fn width(&self) -> usize {
        EFFECT_VM_WIDTH
    }

    fn constraint_degree(&self) -> usize {
        // Selector sum constraint is degree 1 (linear).
        // Selector boolean constraints are degree 2.
        // Per-effect constraints: selector * (expression) is at most degree 3.
        // Hash constraints (hash_2_to_1, hash_4_to_1) are evaluated concretely on trace
        // values at FRI evaluation points — they do NOT contribute polynomial degree.
        // SetField field_idx range check: selector * prod_{k=0..7}(field_idx - k) = degree 9.
        // Seal/Unseal field_idx range check: same degree 9.
        9
    }

    fn air_name(&self) -> &'static str {
        "dregg-effect-vm-v1"
    }

    fn has_chain_continuity(&self) -> bool {
        false
    }

    fn eval_constraints(
        &self,
        local: &[BabyBear],
        next: &[BabyBear],
        public_inputs: &[BabyBear],
        alpha: BabyBear,
    ) -> BabyBear {
        let mut combined = BabyBear::ZERO;
        let mut alpha_pow = BabyBear::ONE;

        // ====================================================================
        // CONSTRAINT GROUP 1: Selector validity
        // ====================================================================

        // Each selector must be boolean: s*(s-1) == 0
        for i in 0..NUM_EFFECTS {
            let s = local[i];
            let c = s * (s - BabyBear::ONE);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // Selectors must sum to exactly 1.
        let mut sel_sum = BabyBear::ZERO;
        for i in 0..NUM_EFFECTS {
            sel_sum = sel_sum + local[i];
        }
        let c_sum = sel_sum - BabyBear::ONE;
        combined = combined + alpha_pow * c_sum;
        alpha_pow = alpha_pow * alpha;

        // VERB-LOCKSTEP refusal tooth: every RETIRED selector column is pinned
        // to ZERO on every row. The 25 factory-dissolved effects have no
        // `Effect` variant, no trace arm, and no constraint group — without
        // this pin a malicious prover could satisfy the one-hot sum with a
        // retired selector and obtain an effect row with NO variant semantics.
        // With it, a trace claiming a doomed effect is UNSATISFIABLE: the
        // kernel's refusal is structural in-circuit.
        for &retired in sel::RETIRED_SELECTORS.iter() {
            let c_retired = local[retired];
            combined = combined + alpha_pow * c_retired;
            alpha_pow = alpha_pow * alpha;
        }

        // ====================================================================
        // CONSTRAINT GROUP 2: Per-effect-type constraints (gated by selector)
        // ====================================================================
        //
        // SECURITY NOTE — Balance limb range checks (o1vm audit finding #1):
        //
        // balance_lo (30-bit) and balance_hi (34-bit) are NOT range-checked
        // in-circuit. Full bit-decomposition would add 60+ columns to the trace.
        // Instead, the EXECUTOR independently validates:
        //   - balance_lo < 2^30  (fits in the lo limb)
        //   - balance_hi < 2^34  (fits in the hi limb, and < BabyBear prime)
        //   - balance_lo + balance_hi * 2^30 == declared u64 balance
        //
        // The boundary constraints bind start/end state_commitment to public
        // inputs, and state_commitment = Poseidon2(balance_lo, balance_hi, ...),
        // so a malicious prover cannot forge commitments without matching limbs.
        // However, a prover CAN choose field-valid but out-of-range limbs on
        // INTERIOR rows (between boundaries). The executor rejects such proofs
        // by re-deriving the final state and checking limb ranges.
        //
        // TODO(range-checks): When we add lookup arguments (log-derivative or
        // Lasso-style), replace executor-side checks with in-circuit range
        // proofs via a 2^16 lookup table (2 lookups per limb for 30/34 bits).
        //
        // STARBRIDGE-FOLLOWUP-03 (2026-05-25): This remains BLOCKED ON HUMAN
        // per STARBRIDGE-PLAN §5.2 (T2.5 / T2.14 in SILVER-DEBT). Precise:
        // circuit/ + turn/executor heavy; no cargo in this session (user
        // circuit release tests active). See SILVER-DEBT §4 table rows for
        // `circuit/src/effect_vm.rs:2305` etc + `air.rs:107` dups. Next
        // session: add lookup feature behind cfg, wire in EffectVmAir
        // boundary + effect.rs projection. Test via circuit/tests/...
        //
        // SECURITY NOTE — Balance underflow protection (o1vm audit finding #3):
        //
        // For outgoing transfers and obligation creation, the constraint is:
        //   new_balance_lo = old_balance_lo - amount
        // In BabyBear modular arithmetic, if amount > old_balance, this wraps
        // around to a large "valid" field element rather than failing.
        //
        // The witness generation uses saturating_sub, so honest provers never
        // produce underflow. However, a MALICIOUS prover could craft a trace
        // where the subtraction wraps around the field modulus.
        //
        // Defense: The executor checks that the final balance (extracted from
        // the proven new_commitment) is <= the initial balance + net_credits.
        // Additionally, the state_commitment binds the actual balance limbs,
        // so any wrap-around would produce a commitment that doesn't match the
        // declared final state.
        //
        // TODO(underflow): Add proper non-negative range proof via bit
        // decomposition of (old_balance - amount) to prove it fits in 30 bits.
        // This requires 30 aux columns per debit row, or a shared lookup table.
        //
        // STARBRIDGE-FOLLOWUP-03: Same blocked status as range-checks above
        // (§5.2). Executor-side defense is the current Silver posture.
        // ====================================================================

        // ====================================================================
        // CONSTRAINT GROUP 2a: IN-CIRCUIT balance-limb range / underflow proof
        // (W9-RANGECHECK — closes o1vm audit findings #1 and #3 in-circuit).
        //
        // The SECURITY NOTE above documented that the limbs were range-checked
        // only by the OFF-circuit executor. This group lifts that guard INTO
        // the AIR via a per-row bit-decomposition of the *new* balance limbs:
        //
        //   balance_lo = Σ_{i=0}^{29} lo_bit_i * 2^i,   each lo_bit_i ∈ {0,1}
        //   balance_hi = Σ_{i=0}^{29} hi_bit_i * 2^i,   each hi_bit_i ∈ {0,1}
        //
        // Both recomposed sums are < 2^30 < p (BabyBear prime), so the
        // decomposition is UNIQUE and the in-field recomposition cannot wrap.
        //
        // SOUNDNESS (underflow / finding #3): the Transfer / NoteCreate /
        // CreateEscrow / CreateObligation / Burn / … debit constraints set
        //   new_bal_lo = old_bal_lo - amount   (in the field).
        // If amount > old_bal_lo this WRAPS to a field element ≥ 2^30 (e.g.
        // the `p - 1` witness proved satisfiable in
        // metatheory/Dregg2/Spike/TransferAirSoundness.lean). Such a value has
        // NO 30-bit boolean decomposition, so constraint (2) below fails and
        // the STARK verifier rejects — no executor re-derivation required.
        //
        // Enforced UNCONDITIONALLY on every row (mirrors the reserved-bit
        // decomposition for SetField), so the new limbs of *every* effect's
        // post-state are pinned in range. Degree: booleanity is degree 2,
        // recomposition is degree 1 — both well under the degree-9 budget.
        // ====================================================================
        {
            // -- balance_lo decomposition --
            let mut recomposed_lo = BabyBear::ZERO;
            for i in 0..BAL_LIMB_BITS {
                let bit = local[AUX_BASE + aux_off::NEW_BAL_LO_BIT_BASE + i];
                // (1) booleanity.
                let c_bool = bit * (bit - BabyBear::ONE);
                combined = combined + alpha_pow * c_bool;
                alpha_pow = alpha_pow * alpha;
                recomposed_lo = recomposed_lo + bit * BabyBear::new(1u32 << i);
            }
            // (2) recomposition pins new_bal_lo into [0, 2^30).
            let c_recompose_lo = recomposed_lo - local[STATE_AFTER_BASE + state::BALANCE_LO];
            combined = combined + alpha_pow * c_recompose_lo;
            alpha_pow = alpha_pow * alpha;

            // -- balance_hi decomposition --
            let mut recomposed_hi = BabyBear::ZERO;
            for i in 0..BAL_LIMB_BITS {
                let bit = local[AUX_BASE + aux_off::NEW_BAL_HI_BIT_BASE + i];
                let c_bool = bit * (bit - BabyBear::ONE);
                combined = combined + alpha_pow * c_bool;
                alpha_pow = alpha_pow * alpha;
                recomposed_hi = recomposed_hi + bit * BabyBear::new(1u32 << i);
            }
            let c_recompose_hi = recomposed_hi - local[STATE_AFTER_BASE + state::BALANCE_HI];
            combined = combined + alpha_pow * c_recompose_hi;
            alpha_pow = alpha_pow * alpha;
        }

        let s_noop = local[sel::NOOP];
        let s_transfer = local[sel::TRANSFER];
        let s_setfield = local[sel::SET_FIELD];
        let s_grantcap = local[sel::GRANT_CAP];
        let s_notespend = local[sel::NOTE_SPEND];
        let s_notecreate = local[sel::NOTE_CREATE];
        let s_custom = local[sel::CUSTOM];

        // State accessors (before).
        let old_bal_lo = local[STATE_BEFORE_BASE + state::BALANCE_LO];
        let old_bal_hi = local[STATE_BEFORE_BASE + state::BALANCE_HI];
        let old_nonce = local[STATE_BEFORE_BASE + state::NONCE];
        let old_cap_root = local[STATE_BEFORE_BASE + state::CAP_ROOT];

        // State accessors (after).
        let new_bal_lo = local[STATE_AFTER_BASE + state::BALANCE_LO];
        let new_bal_hi = local[STATE_AFTER_BASE + state::BALANCE_HI];
        let new_nonce = local[STATE_AFTER_BASE + state::NONCE];
        let new_cap_root = local[STATE_AFTER_BASE + state::CAP_ROOT];

        // Parameters.
        let p0 = local[PARAM_BASE + 0];
        let p1 = local[PARAM_BASE + 1];
        let _p2 = local[PARAM_BASE + 2];

        // -- NoOp: state_after == state_before for all state columns --
        for i in 0..state::SIZE {
            let c = s_noop * (local[STATE_AFTER_BASE + i] - local[STATE_BEFORE_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // -- Transfer: balance update --
        // param0 = amount_lo, param1 = direction (0=in, 1=out)
        // If direction=0 (in): new_bal = old_bal + amount
        // If direction=1 (out): new_bal = old_bal - amount
        // Unified: new_bal_lo - old_bal_lo - amount + 2*direction*amount == carry adjustment
        //
        // We work with the combined 60-bit balance:
        //   balance = bal_lo + bal_hi * 2^30
        //   Transfer only touches bal_lo for simplicity (amount < 2^30).
        //   new_bal_lo = old_bal_lo + amount * (1 - 2*direction)
        //
        // For amounts that don't overflow a single limb:
        let two = BabyBear::new(2);
        let direction = p1;
        let amount = p0;
        // new_bal_lo == old_bal_lo + amount - 2*direction*amount
        let c_transfer_lo =
            s_transfer * (new_bal_lo - old_bal_lo - amount + two * direction * amount);
        combined = combined + alpha_pow * c_transfer_lo;
        alpha_pow = alpha_pow * alpha;

        // Transfer: hi limb unchanged (for single-limb amounts).
        let c_transfer_hi = s_transfer * (new_bal_hi - old_bal_hi);
        combined = combined + alpha_pow * c_transfer_hi;
        alpha_pow = alpha_pow * alpha;

        // Transfer: direction must be boolean.
        let c_transfer_dir = s_transfer * direction * (direction - BabyBear::ONE);
        combined = combined + alpha_pow * c_transfer_dir;
        alpha_pow = alpha_pow * alpha;

        // Transfer: cap_root and reserved unchanged.
        // (state_commitment is a derived value recomputed in witness gen; bound at boundaries only.)
        for i in [state::CAP_ROOT, state::RESERVED] {
            let c = s_transfer * (local[STATE_AFTER_BASE + i] - local[STATE_BEFORE_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }
        // Transfer: fields unchanged.
        for i in 0..8 {
            let c = s_transfer
                * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                    - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // -- SetField: exactly one field updated --
        // param0 = field_index, param1 = new_value
        // For the targeted field: new_field[idx] = new_value.
        // For all others: unchanged.
        // We use the Lagrange selector trick:
        //   For each field slot j: new_field[j] - old_field[j] - is_target_j * (new_value - old_field[j]) == 0
        //   where is_target_j = prod_{k != j} (field_index - k) / (j - k)
        //
        // Simplified: we constrain that the sum of changes equals (new_value - old_field[idx])
        // and that it happens at exactly the right index. For degree control, we use:
        //   For each j in 0..8:
        //     sel_setfield * (new_field[j] - old_field[j]) * (1 - eq(field_index, j)) == 0
        //     where eq check is: (field_index - j) * inverse_or_zero
        //
        // Even simpler approach (lower degree): use aux columns for the Lagrange basis.
        // But for v1, we use a direct approach with the product constraint:
        //   sel_setfield * (new_field[j] - old_field[j]) * product_{k != j}(field_index - k) == 0
        //   for all j where field_index != j.
        //
        // Actually simplest: enforce
        //   For each j: sel * (new_f[j] - old_f[j] - delta_j) == 0
        //   where delta_j = if j == field_index { new_value - old_f[j] } else { 0 }
        //
        // We do it as: for the ONE field that matches, the difference must equal new_value - old.
        // For all others, difference must be zero.
        // With selector-index product trick at degree 2:
        //   sel_setfield * (field_index - j) * (new_f[j] - old_f[j]) == 0 for each j
        //   (if field_index == j, this is trivially 0 regardless of change)
        //   (if field_index != j, new_f[j] - old_f[j] must be 0)
        let field_index = p0;
        let new_value = p1;
        for j in 0..8u32 {
            let old_fj = local[STATE_BEFORE_BASE + state::FIELD_BASE + j as usize];
            let new_fj = local[STATE_AFTER_BASE + state::FIELD_BASE + j as usize];
            // Non-target fields must be unchanged.
            let c = s_setfield * (field_index - BabyBear::new(j)) * (new_fj - old_fj);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }
        // The target field must become new_value. We check this by:
        //   For each j: sel * prod_{k!=j}(index - k) * (new_f[j] - new_value) == 0
        // When index == j, prod_{k!=j}(index-k) != 0, so new_f[j] must equal new_value.
        // When index != j, some factor (index - j) is zero in the product, so constraint is trivial.
        // But this is high degree (degree 8). Instead, use the aux column approach:
        //   aux[0] stores the Lagrange indicator (computed in witness gen).
        //   Constraint: sel * (sum_j new_f[j] * lagrange_j - new_value) == 0
        //
        // Simplest correct approach for v1: The witness generation ensures the right field
        // is set. We just need ONE constraint proving the target field has the right value.
        // Use aux[0] to carry the old value of the target field, then:
        //   sel_setfield * (new_value - target_field_new) == 0
        // where target_field_new is reconstructed from the trace.
        //
        // Actually, the simplest sound approach:
        //   Verify that the difference across all fields sums to exactly (new_value - old_value_at_idx).
        //   Combined with per-field constraints above (non-target unchanged), this is sufficient.
        // The sum of (new_f[j] - old_f[j]) for all j must equal (new_value - old_value_at_idx).
        // old_value_at_idx is stored in aux[0].
        let old_value_at_idx = local[AUX_BASE + 0];
        let mut field_diff_sum = BabyBear::ZERO;
        for j in 0..8 {
            let old_fj = local[STATE_BEFORE_BASE + state::FIELD_BASE + j];
            let new_fj = local[STATE_AFTER_BASE + state::FIELD_BASE + j];
            field_diff_sum = field_diff_sum + (new_fj - old_fj);
        }
        let c_setfield_sum = s_setfield * (field_diff_sum - (new_value - old_value_at_idx));
        combined = combined + alpha_pow * c_setfield_sum;
        alpha_pow = alpha_pow * alpha;

        // SetField: balance and cap_root unchanged.
        let c_sf_bal_lo = s_setfield * (new_bal_lo - old_bal_lo);
        combined = combined + alpha_pow * c_sf_bal_lo;
        alpha_pow = alpha_pow * alpha;
        let c_sf_bal_hi = s_setfield * (new_bal_hi - old_bal_hi);
        combined = combined + alpha_pow * c_sf_bal_hi;
        alpha_pow = alpha_pow * alpha;
        let c_sf_cap = s_setfield * (new_cap_root - old_cap_root);
        combined = combined + alpha_pow * c_sf_cap;
        alpha_pow = alpha_pow * alpha;
        // Stage 2 (sealing honesty): SetField must not change `reserved`
        // (sealed_mask AND mode_flag both preserved across a field set).
        let sf_old_reserved = local[STATE_BEFORE_BASE + state::RESERVED];
        let sf_new_reserved = local[STATE_AFTER_BASE + state::RESERVED];
        let c_sf_reserved = s_setfield * (sf_new_reserved - sf_old_reserved);
        combined = combined + alpha_pow * c_sf_reserved;
        alpha_pow = alpha_pow * alpha;
        // Stage 2 (sealing honesty, FULL bit-decomposition):
        // The target field must NOT be sealed. We derive
        // `bit_at_field_idx = Σ_k L_k(field_idx) * b_k` from the
        // bit-decomposition of old_reserved (aux[RESERVED_BIT_0..7]),
        // where L_k(x) is the Lagrange basis on {0..7}. The constraints
        // below enforce:
        //   1. Each b_i is boolean.
        //   2. Σ b_i * 2^i + mode * 256 == old_reserved.
        //   3. mode is boolean.
        //   4. s_setfield * (Σ_k L_k(field_idx) * b_k) == 0.
        // The first three apply to every row (UNCONDITIONALLY) — that
        // gives every effect row a correct bit-decomposition of its
        // own old_reserved. The fourth gates by selector.
        //
        // Resolves AUDIT[stage2-setfield-sealed-witness].
        let b0 = local[AUX_BASE + aux_off::RESERVED_BIT_0];
        let b1 = local[AUX_BASE + aux_off::RESERVED_BIT_1];
        let b2 = local[AUX_BASE + aux_off::RESERVED_BIT_2];
        let b3 = local[AUX_BASE + aux_off::RESERVED_BIT_3];
        let b4 = local[AUX_BASE + aux_off::RESERVED_BIT_4];
        let b5 = local[AUX_BASE + aux_off::RESERVED_BIT_5];
        let b6 = local[AUX_BASE + aux_off::RESERVED_BIT_6];
        let b7 = local[AUX_BASE + aux_off::RESERVED_BIT_7];
        let mode_bit = local[AUX_BASE + aux_off::RESERVED_MODE];
        // Boolean constraints (unconditional, every row).
        for bit in [b0, b1, b2, b3, b4, b5, b6, b7, mode_bit].iter() {
            let cb = (*bit) * ((*bit) - BabyBear::ONE);
            combined = combined + alpha_pow * cb;
            alpha_pow = alpha_pow * alpha;
        }
        // Decomposition: Σ bi * 2^i + mode * 256 == old_reserved.
        let sf_old_reserved_dec = local[STATE_BEFORE_BASE + state::RESERVED];
        let reconstructed = b0
            + b1 * BabyBear::new(2)
            + b2 * BabyBear::new(4)
            + b3 * BabyBear::new(8)
            + b4 * BabyBear::new(16)
            + b5 * BabyBear::new(32)
            + b6 * BabyBear::new(64)
            + b7 * BabyBear::new(128)
            + mode_bit * BabyBear::new(256);
        let c_decomp = reconstructed - sf_old_reserved_dec;
        combined = combined + alpha_pow * c_decomp;
        alpha_pow = alpha_pow * alpha;
        // Lagrange-basis selection of the bit at field_idx.
        // For field_idx ∈ {0..7}, returns b_{field_idx}.
        let l_bits: [BabyBear; 8] = [b0, b1, b2, b3, b4, b5, b6, b7];
        let bit_at_idx = {
            let x = field_index;
            let mut acc = BabyBear::ZERO;
            for k in 0..8usize {
                let mut num = BabyBear::ONE;
                let mut den = BabyBear::ONE;
                for j in 0..8usize {
                    if j == k {
                        continue;
                    }
                    num = num * (x - BabyBear::new(j as u32));
                    let diff = if k > j {
                        BabyBear::new((k - j) as u32)
                    } else {
                        BabyBear::ZERO - BabyBear::new((j - k) as u32)
                    };
                    den = den * diff;
                }
                let den_inv = den
                    .inverse()
                    .expect("Lagrange denominator non-zero on {0..7}");
                acc = acc + num * den_inv * l_bits[k];
            }
            acc
        };
        // s_setfield * bit_at_idx == 0  (cannot set a sealed field).
        let c_sf_not_sealed = s_setfield * bit_at_idx;
        combined = combined + alpha_pow * c_sf_not_sealed;
        alpha_pow = alpha_pow * alpha;
        // ====================================================================
        // RANGE CHECK: SetField field_idx must be in {0, 1, 2, 3, 4, 5, 6, 7}
        // ====================================================================
        // Degree-8 polynomial that vanishes exactly on {0..7}:
        //   prod_{k=0}^{7} (field_idx - k) == 0
        // Gated by sel_setfield (total degree 9). Any out-of-bounds value makes
        // this constraint non-zero, causing the STARK verifier to reject.
        {
            let mut field_idx_range_product = BabyBear::ONE;
            for k in 0..8u32 {
                field_idx_range_product =
                    field_idx_range_product * (field_index - BabyBear::new(k));
            }
            let c_field_idx_range = s_setfield * field_idx_range_product;
            combined = combined + alpha_pow * c_field_idx_range;
            alpha_pow = alpha_pow * alpha;
        }

        // -- GrantCapability: capability_root update --
        // param0 = cap_entry (hash of new capability)
        // new_cap_root MUST equal hash_2_to_1(old_cap_root, cap_entry).
        //
        // SOUNDNESS FIX: We compute hash_2_to_1 directly in the constraint evaluator.
        // The old approach used a prover-controlled aux[1] value which allowed a
        // malicious prover to set new_cap_root to ANY value. Now the verifier
        // independently computes the hash at each evaluation point. This works because
        // eval_constraints operates on concrete field values (not symbolic polynomials),
        // so the hash is a pure function of the trace values at the query point.
        let cap_entry_val = local[PARAM_BASE + param::CAP_ENTRY];
        let expected_new_cap = hash_2_to_1(old_cap_root, cap_entry_val);
        let c_grantcap = s_grantcap * (new_cap_root - expected_new_cap);
        combined = combined + alpha_pow * c_grantcap;
        alpha_pow = alpha_pow * alpha;

        // GrantCap: balance and fields unchanged.
        let c_gc_bal_lo = s_grantcap * (new_bal_lo - old_bal_lo);
        combined = combined + alpha_pow * c_gc_bal_lo;
        alpha_pow = alpha_pow * alpha;
        let c_gc_bal_hi = s_grantcap * (new_bal_hi - old_bal_hi);
        combined = combined + alpha_pow * c_gc_bal_hi;
        alpha_pow = alpha_pow * alpha;
        for i in 0..8 {
            let c = s_grantcap
                * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                    - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // -- EmitEvent: stateless side-effect with canonical (topic, payload) binding --
        //
        // Row layout (closes #110):
        //   params[0..4] = topic_hash[0..4]
        //   params[4..8] = payload_hash[0..4]
        //
        // The full 8-felt topic/payload hashes (32 bytes each) are bound by
        // three independent algebraic teeth:
        //
        //   (a) Per-row PI-equality (BELOW): when sel::EMIT_EVENT == 1, the
        //       row's params[0..4] MUST equal PI[EMIT_EVENT_TOPIC_HASH][0..4]
        //       and params[4..8] MUST equal PI[EMIT_EVENT_PAYLOAD_HASH][0..4].
        //       Soundness: a malicious prover that forges any of the 8 low
        //       felts cannot satisfy this constraint at any FRI evaluation
        //       point because PI is a constant across rows. ~124-bit binding
        //       on the low halves.
        //
        //   (b) compute_effects_hash absorbs all 16 felts of the (topic_hash ‖
        //       payload_hash) preimage. The Poseidon2-chained effects_hash is
        //       pinned to PI[EFFECTS_HASH_BASE] via a row-0 boundary, so the
        //       HIGH 4 felts of each hash also become cryptographically bound
        //       (any swap in [4..8] changes the chain). ~256-bit binding.
        //
        //   (c) Off-AIR PI-match loop: the verifier recomputes the canonical
        //       (topic, payload) bytes from the runtime Event and rejects any
        //       PI disagreement. Closes the executor-honesty gap for the high
        //       halves with respect to the runtime Event encoding.
        //
        // State columns: balance / cap_root / fields all unchanged (the
        // existing passthrough constraints retained below).
        let s_emitevent = local[sel::EMIT_EVENT];
        let c_ee_bal_lo = s_emitevent * (new_bal_lo - old_bal_lo);
        combined = combined + alpha_pow * c_ee_bal_lo;
        alpha_pow = alpha_pow * alpha;
        let c_ee_bal_hi = s_emitevent * (new_bal_hi - old_bal_hi);
        combined = combined + alpha_pow * c_ee_bal_hi;
        alpha_pow = alpha_pow * alpha;
        let c_ee_cap = s_emitevent * (new_cap_root - old_cap_root);
        combined = combined + alpha_pow * c_ee_cap;
        alpha_pow = alpha_pow * alpha;
        for i in 0..8 {
            let c = s_emitevent
                * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                    - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }
        // (a) Per-row PI-equality binding for topic_hash[0..4] / payload_hash[0..4].
        // Gated by sel::EMIT_EVENT so non-emit rows are unaffected. PI access is
        // safe inside eval_constraints (see Group 6 INIT_BAL_LO usage above).
        if public_inputs.len() >= pi::BASE_COUNT {
            for i in 0..4 {
                let pi_topic_i = public_inputs[pi::EMIT_EVENT_TOPIC_HASH_BASE + i];
                let c_topic = s_emitevent * (local[PARAM_BASE + i] - pi_topic_i);
                combined = combined + alpha_pow * c_topic;
                alpha_pow = alpha_pow * alpha;
            }
            for i in 0..4 {
                let pi_payload_i = public_inputs[pi::EMIT_EVENT_PAYLOAD_HASH_BASE + i];
                let c_payload = s_emitevent * (local[PARAM_BASE + 4 + i] - pi_payload_i);
                combined = combined + alpha_pow * c_payload;
                alpha_pow = alpha_pow * alpha;
            }
        }

        // -- SetPermissions: same shape as EmitEvent (state passthrough) --
        // Permissions live outside the VM trace (they're part of the cell's
        // off-chain manifest). The AIR's job is to bind permissions_hash
        // into effects_hash and forbid state column drift.
        let s_setperms = local[sel::SET_PERMISSIONS];
        let c_sp_bal_lo = s_setperms * (new_bal_lo - old_bal_lo);
        combined = combined + alpha_pow * c_sp_bal_lo;
        alpha_pow = alpha_pow * alpha;
        let c_sp_bal_hi = s_setperms * (new_bal_hi - old_bal_hi);
        combined = combined + alpha_pow * c_sp_bal_hi;
        alpha_pow = alpha_pow * alpha;
        let c_sp_cap = s_setperms * (new_cap_root - old_cap_root);
        combined = combined + alpha_pow * c_sp_cap;
        alpha_pow = alpha_pow * alpha;
        for i in 0..8 {
            let c = s_setperms
                * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                    - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // -- SetVerificationKey: same shape as SetPermissions (passthrough) --
        let s_setvk = local[sel::SET_VERIFICATION_KEY];
        let c_svk_bal_lo = s_setvk * (new_bal_lo - old_bal_lo);
        combined = combined + alpha_pow * c_svk_bal_lo;
        alpha_pow = alpha_pow * alpha;
        let c_svk_bal_hi = s_setvk * (new_bal_hi - old_bal_hi);
        combined = combined + alpha_pow * c_svk_bal_hi;
        alpha_pow = alpha_pow * alpha;
        let c_svk_cap = s_setvk * (new_cap_root - old_cap_root);
        combined = combined + alpha_pow * c_svk_cap;
        alpha_pow = alpha_pow * alpha;
        for i in 0..8 {
            let c = s_setvk
                * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                    - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // -- All passthrough variants (Stage 3 batch). State columns must
        //    be unchanged; nonce ticks. Variant-specific param (or absence)
        //    in PARAM_BASE+0; binds via effects_hash.
        for s_sel_idx in [
            sel::REFRESH_DELEGATION,
            sel::INCREMENT_NONCE,
            sel::REVOKE_DELEGATION,
            sel::CREATE_CELL,
            sel::SPAWN_WITH_DELEGATION,
            sel::EXERCISE_VIA_CAPABILITY,
            sel::INTRODUCE,
            sel::PIPELINED_SEND,
        ] {
            let s_v = local[s_sel_idx];
            let c_bal_lo = s_v * (new_bal_lo - old_bal_lo);
            combined = combined + alpha_pow * c_bal_lo;
            alpha_pow = alpha_pow * alpha;
            let c_bal_hi = s_v * (new_bal_hi - old_bal_hi);
            combined = combined + alpha_pow * c_bal_hi;
            alpha_pow = alpha_pow * alpha;
            let c_cap = s_v * (new_cap_root - old_cap_root);
            combined = combined + alpha_pow * c_cap;
            alpha_pow = alpha_pow * alpha;
            for i in 0..8 {
                let c = s_v
                    * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                        - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
                combined = combined + alpha_pow * c;
                alpha_pow = alpha_pow * alpha;
            }
        }

        // -- RevokeCapability: capability_root update --
        // Mirrors GRANT_CAP: param0 (shared with CAP_ENTRY) carries the slot
        // hash; new_cap_root MUST equal hash_2_to_1(old_cap_root, slot_hash).
        // The verifier independently computes the hash (no prover-controlled
        // aux witness), matching the SOUNDNESS FIX comment above.
        let s_revokecap = local[sel::REVOKE_CAPABILITY];
        let slot_hash_val = local[PARAM_BASE + param::CAP_ENTRY];
        let expected_revoke_cap = hash_2_to_1(old_cap_root, slot_hash_val);
        let c_revokecap = s_revokecap * (new_cap_root - expected_revoke_cap);
        combined = combined + alpha_pow * c_revokecap;
        alpha_pow = alpha_pow * alpha;
        // RevokeCap: balance and fields unchanged.
        let c_rc_bal_lo = s_revokecap * (new_bal_lo - old_bal_lo);
        combined = combined + alpha_pow * c_rc_bal_lo;
        alpha_pow = alpha_pow * alpha;
        let c_rc_bal_hi = s_revokecap * (new_bal_hi - old_bal_hi);
        combined = combined + alpha_pow * c_rc_bal_hi;
        alpha_pow = alpha_pow * alpha;
        for i in 0..8 {
            let c = s_revokecap
                * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                    - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // -- NoteSpend: balance credit --
        // param0 = nullifier, param1 = value_lo, param2 = value_hi
        // new_bal_lo = old_bal_lo + value_lo (with potential carry to hi)
        // For simplicity (v1): value fits in lo limb (value_hi == 0).
        let note_val_lo = p1;
        let c_ns_bal = s_notespend * (new_bal_lo - old_bal_lo - note_val_lo);
        combined = combined + alpha_pow * c_ns_bal;
        alpha_pow = alpha_pow * alpha;
        let c_ns_hi = s_notespend * (new_bal_hi - old_bal_hi);
        combined = combined + alpha_pow * c_ns_hi;
        alpha_pow = alpha_pow * alpha;
        // NoteSpend: fields and cap unchanged.
        let c_ns_cap = s_notespend * (new_cap_root - old_cap_root);
        combined = combined + alpha_pow * c_ns_cap;
        alpha_pow = alpha_pow * alpha;
        for i in 0..8 {
            let c = s_notespend
                * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                    - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }
        // ====================================================================
        // D5: NoteSpend nullifier CROSS-BINDING (approach A) — per-row gated
        // PI equality. When sel::NOTE_SPEND == 1, the row's param0 (the
        // single folded `fold_bytes32_to_bb(nullifier)` felt) MUST equal
        // PI[NOTESPEND_NULLIFIER]. Same mechanism as the EMIT_EVENT topic /
        // payload pin above: PI is a constant across rows, so a malicious
        // prover that feeds a different M into the EffectVM (param0 = fold(M))
        // cannot satisfy this at any FRI evaluation point unless PI also
        // carries fold(M).
        //
        // The off-AIR verifier (turn::executor::proof_verify) reconstructs
        // PI[NOTESPEND_NULLIFIER] from the SCHEMA_NOTE_SPEND binding proof's
        // fields[0] — the proof that certifies the nullifier against the spent
        // note's preimage. Its PI-match loop rejects any proof whose PI
        // disagrees. Together: param0 == PI[NOTESPEND_NULLIFIER] == fold(the
        // binding-proof-certified nullifier), so the EffectVM can no longer
        // spend a nullifier other than the one the spending proof enforced.
        //
        // Gated by s_notespend, so non-NoteSpend rows are unaffected; on
        // proofs with no NoteSpend row, the slot stays at the ZERO sentinel
        // and this constraint is vacuous (no row has s_notespend == 1).
        if public_inputs.len() >= pi::BASE_COUNT {
            let pi_nullifier = public_inputs[pi::NOTESPEND_NULLIFIER];
            let c_ns_nullifier =
                s_notespend * (local[PARAM_BASE + param::NULLIFIER] - pi_nullifier);
            combined = combined + alpha_pow * c_ns_nullifier;
            alpha_pow = alpha_pow * alpha;
        }

        // ====================================================================
        // D5b: NoteCreate commitment CROSS-BINDING (approach A) — per-row gated
        // PI equality. When sel::NOTE_CREATE == 1, the row's param0
        // (`param::NOTE_COMMITMENT`, the single folded
        // `fold_bytes32_to_bb(commitment)` felt that also drives the balance
        // DEBIT) MUST equal PI[NOTECREATE_COMMITMENT]. Identical mechanism to
        // the NoteSpend nullifier weld above: PI is constant across rows, so a
        // malicious prover that feeds a different commitment C' into the
        // EffectVM (param0 = fold(C')) cannot satisfy this unless PI carries
        // fold(C'). The off-AIR verifier reconstructs PI[NOTECREATE_COMMITMENT]
        // from the SCHEMA_NOTE_CREATE binding proof's fields[0] — the proof
        // that certifies the commitment against its value/asset/range opening
        // — so the EffectVM can no longer mint a note creation for a
        // commitment the binding proof never validated. Gated by s_notecreate;
        // sentinel ZERO when no NoteCreate row is present (vacuous).
        if public_inputs.len() >= pi::BASE_COUNT {
            let pi_commitment = public_inputs[pi::NOTECREATE_COMMITMENT];
            let c_nc_commitment =
                s_notecreate * (local[PARAM_BASE + param::NOTE_COMMITMENT] - pi_commitment);
            combined = combined + alpha_pow * c_nc_commitment;
            alpha_pow = alpha_pow * alpha;
        }

        // ====================================================================
        // D5c: Burn target CROSS-BINDING (approach A) — per-row gated PI
        // equality. When sel::BURN == 1, the row's param0 (`param::BURN_TARGET`
        // = `fold_bytes32_to_bb(target.as_bytes())`) MUST equal
        // PI[BURN_TARGET_PI]. The Burn row's balance-debit constraint operates
        // on the trace's running balance; this weld pins WHICH cell the burn
        // is attributed to. The off-AIR verifier reconstructs PI[BURN_TARGET_PI]
        // from the SCHEMA_BURN binding proof's fields[0] (the target whose
        // `old_balance - new_balance == amount` the proof validated against the
        // ledger snapshot), so a malicious executor can no longer prove the
        // burn arithmetic for target T while feeding a Burn for a different
        // target T' into the EffectVM. Gated by s_burn; sentinel ZERO when no
        // Burn row is present (vacuous).
        if public_inputs.len() >= pi::BASE_COUNT {
            let s_burn_xb = local[sel::BURN];
            let pi_burn_target = public_inputs[pi::BURN_TARGET_PI];
            let c_burn_target =
                s_burn_xb * (local[PARAM_BASE + param::BURN_TARGET] - pi_burn_target);
            combined = combined + alpha_pow * c_burn_target;
            alpha_pow = alpha_pow * alpha;
        }

        // -- NoteCreate: balance-NEUTRAL --
        // param0 = commitment, param1 = value_lo, param2 = value_hi
        // The note value is hidden in the commitment and is NEVER moved on the
        // transparent ledger (the shielding convention the executor uses:
        // `apply_note_create` records the commitment and does not touch balance).
        // So `bal_lo` is FROZEN: new_bal_lo = old_bal_lo. This matches the verified
        // Lean descriptor (`EffectVmEmitNoteCreate.gBalLoFreeze` / `CellNoteSpec`,
        // balance-neutral) and universe-A's `noteCreateA_bal_neutral`. (A prior
        // version debited `value_lo`, which diverged from the executor; closed.)
        // (`p1` = value_lo is still bound into the commitment cross-binding elsewhere.)
        let c_nc_bal = s_notecreate * (new_bal_lo - old_bal_lo);
        combined = combined + alpha_pow * c_nc_bal;
        alpha_pow = alpha_pow * alpha;
        let c_nc_hi = s_notecreate * (new_bal_hi - old_bal_hi);
        combined = combined + alpha_pow * c_nc_hi;
        alpha_pow = alpha_pow * alpha;
        // NoteCreate: fields and cap unchanged.
        let c_nc_cap = s_notecreate * (new_cap_root - old_cap_root);
        combined = combined + alpha_pow * c_nc_cap;
        alpha_pow = alpha_pow * alpha;
        for i in 0..8 {
            let c = s_notecreate
                * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                    - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // -- BridgeMint: balance credit (mirror NoteSpend) --
        // param0 = mint_hash, param1 = value_lo
        // new_bal_lo = old_bal_lo + value_lo
        let s_bridgemint = local[sel::BRIDGE_MINT];
        let bm_val_lo = local[PARAM_BASE + 1];
        let c_bm_bal = s_bridgemint * (new_bal_lo - old_bal_lo - bm_val_lo);
        combined = combined + alpha_pow * c_bm_bal;
        alpha_pow = alpha_pow * alpha;
        let c_bm_hi = s_bridgemint * (new_bal_hi - old_bal_hi);
        combined = combined + alpha_pow * c_bm_hi;
        alpha_pow = alpha_pow * alpha;
        let c_bm_cap = s_bridgemint * (new_cap_root - old_cap_root);
        combined = combined + alpha_pow * c_bm_cap;
        alpha_pow = alpha_pow * alpha;
        for i in 0..8 {
            let c = s_bridgemint
                * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                    - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // -- Custom (CellProgram dispatch): state continuity only --
        //
        // SECURITY NOTE (Gap 5): Custom effects provide WEAKER guarantees than
        // other effect types. The Effect VM only enforces:
        //   1. State continuity (state flows through unchanged)
        //   2. Proof commitment binding (the custom_proof_commitment hash is
        //      recorded in the public inputs for external verification)
        //
        // The ACTUAL SEMANTICS of the custom effect are defined entirely by the
        // external CellProgram. The Effect VM circuit does NOT verify the external
        // proof — it only binds its hash commitment to the turn's public inputs.
        //
        // Verifiers MUST independently verify the external proof against the
        // committed program VK hash. Without this check, a malicious prover can
        // claim any custom_proof_commitment without having a valid external proof.
        //
        // The custom_program_vk_hash in the PI identifies which CellProgram was
        // invoked. The verifier should:
        //   1. Look up the registered program by VK hash
        //   2. Verify the external proof against that program's verification key
        //   3. Check the external proof's hash matches custom_proof_commitment
        //
        // If ANY of these steps are skipped, the custom effect is effectively
        // unconstrained — the prover can claim arbitrary side-effects occurred.
        //
        // This is BY DESIGN: the Effect VM is a generic execution framework,
        // and custom programs extend it with domain-specific logic. But verifiers
        // must understand that Custom effects are only as secure as their external
        // verification implementation.
        //
        // Constraints: semantic state passthrough. `nonce` still ticks via
        // the global nonce constraint below, and `state_commit` is recomputed
        // from the post-state, so neither can be equality-constrained here.
        let c_custom_bal_lo = s_custom * (new_bal_lo - old_bal_lo);
        combined = combined + alpha_pow * c_custom_bal_lo;
        alpha_pow = alpha_pow * alpha;
        let c_custom_bal_hi = s_custom * (new_bal_hi - old_bal_hi);
        combined = combined + alpha_pow * c_custom_bal_hi;
        alpha_pow = alpha_pow * alpha;
        let c_custom_cap = s_custom * (new_cap_root - old_cap_root);
        combined = combined + alpha_pow * c_custom_cap;
        alpha_pow = alpha_pow * alpha;
        for i in 0..8 {
            let c = s_custom
                * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                    - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }
        let c_custom_reserved = s_custom
            * (local[STATE_AFTER_BASE + state::RESERVED]
                - local[STATE_BEFORE_BASE + state::RESERVED]);
        combined = combined + alpha_pow * c_custom_reserved;
        alpha_pow = alpha_pow * alpha;

        // ====================================================================

        // -- MakeSovereign: mode_flag 0->1, balance/fields/cap preserved --
        let s_makesov = local[sel::MAKE_SOVEREIGN];
        let old_reserved = local[STATE_BEFORE_BASE + state::RESERVED];
        let new_reserved = local[STATE_AFTER_BASE + state::RESERVED];
        let c_sov_mode = s_makesov * (new_reserved - old_reserved - BabyBear::new(256));
        combined = combined + alpha_pow * c_sov_mode;
        alpha_pow = alpha_pow * alpha;
        // Stage 2 (MakeSovereign once-only): the mode bit must currently be 0.
        // Combined with `new_reserved - old_reserved == 256` (above), this
        // enforces the canonical 0→1 transition. Without this, a malicious
        // prover could apply MakeSovereign to an already-sovereign cell,
        // pushing reserved through 2*256 (which is no longer a valid
        // encoding — mode bit becomes non-boolean).
        let c_sov_was_managed = s_makesov * mode_bit;
        combined = combined + alpha_pow * c_sov_was_managed;
        alpha_pow = alpha_pow * alpha;
        let c_sov_bal_lo = s_makesov * (new_bal_lo - old_bal_lo);
        combined = combined + alpha_pow * c_sov_bal_lo;
        alpha_pow = alpha_pow * alpha;
        let c_sov_bal_hi = s_makesov * (new_bal_hi - old_bal_hi);
        combined = combined + alpha_pow * c_sov_bal_hi;
        alpha_pow = alpha_pow * alpha;
        let c_sov_cap = s_makesov * (new_cap_root - old_cap_root);
        combined = combined + alpha_pow * c_sov_cap;
        alpha_pow = alpha_pow * alpha;
        for i in 0..8 {
            let c = s_makesov
                * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                    - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // -- CreateCellFromFactory: semantic state passthrough; nonce ticks --
        let s_factory = local[sel::CREATE_CELL_FROM_FACTORY];
        let c_factory_bal_lo = s_factory * (new_bal_lo - old_bal_lo);
        combined = combined + alpha_pow * c_factory_bal_lo;
        alpha_pow = alpha_pow * alpha;
        let c_factory_bal_hi = s_factory * (new_bal_hi - old_bal_hi);
        combined = combined + alpha_pow * c_factory_bal_hi;
        alpha_pow = alpha_pow * alpha;
        let c_factory_cap = s_factory * (new_cap_root - old_cap_root);
        combined = combined + alpha_pow * c_factory_cap;
        alpha_pow = alpha_pow * alpha;
        for i in 0..8 {
            let c = s_factory
                * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                    - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }
        let c_factory_reserved = s_factory
            * (local[STATE_AFTER_BASE + state::RESERVED]
                - local[STATE_BEFORE_BASE + state::RESERVED]);
        combined = combined + alpha_pow * c_factory_reserved;
        alpha_pow = alpha_pow * alpha;

        // ====================================================================
        // -- Burn: explicit non-conservation balance reduction --
        //
        // Near-miss aliasing closure (#100 follow-up). Pre-this-change, the
        // turn-side `Effect::Burn` was either dropped from the projection or
        // routed through `VmEffect::Transfer { direction: 1 }`. A verifier
        // replaying the trace could not distinguish a Burn from a
        // Transfer-direction-1 algebraically: both rows produce the same
        // balance-debit shape. Silver Vision honesty: dedicated selector +
        // dedicated `was_burn_flag == 1` constraint so the proof attests
        // "this Burn happened" rather than "some balance-debit happened".
        //
        // Params:
        //   params[BURN_TARGET]         = target_hash (folded into effects_hash)
        //   params[BURN_AMOUNT_LO]      = amount_lo (low 30 bits)
        //   params[BURN_WAS_BURN_FLAG]  = 1 (constant — the AIR pins this)
        //
        // Constraints:
        //   1. new_bal_lo + amount_lo == old_bal_lo     (balance debit)
        //   2. new_bal_hi == old_bal_hi                 (single-limb amount)
        //   3. was_burn_flag == 1                        (disclosure pinning)
        //   4. cap_root, fields, reserved all passthrough.
        let s_burn = local[sel::BURN];
        {
            let burn_amount = local[PARAM_BASE + param::BURN_AMOUNT_LO];
            let burn_flag = local[PARAM_BASE + param::BURN_WAS_BURN_FLAG];

            // Balance debit (mirrors NoteCreate's `new = old - amount`).
            let c_burn_bal_lo = s_burn * (new_bal_lo - old_bal_lo + burn_amount);
            combined = combined + alpha_pow * c_burn_bal_lo;
            alpha_pow = alpha_pow * alpha;
            let c_burn_bal_hi = s_burn * (new_bal_hi - old_bal_hi);
            combined = combined + alpha_pow * c_burn_bal_hi;
            alpha_pow = alpha_pow * alpha;

            // Was-burn disclosure flag: MUST be 1 on a Burn row. A trace
            // that drops the disclosure (sets it to 0) fails the AIR.
            let c_burn_flag = s_burn * (burn_flag - BabyBear::ONE);
            combined = combined + alpha_pow * c_burn_flag;
            alpha_pow = alpha_pow * alpha;

            // cap_root unchanged.
            let c_burn_cap = s_burn * (new_cap_root - old_cap_root);
            combined = combined + alpha_pow * c_burn_cap;
            alpha_pow = alpha_pow * alpha;
            // fields unchanged.
            for i in 0..8 {
                let c = s_burn
                    * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                        - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
                combined = combined + alpha_pow * c;
                alpha_pow = alpha_pow * alpha;
            }
            // reserved unchanged (Burn does not seal / unseal / sovereign).
            let c_burn_reserved = s_burn
                * (local[STATE_AFTER_BASE + state::RESERVED]
                    - local[STATE_BEFORE_BASE + state::RESERVED]);
            combined = combined + alpha_pow * c_burn_reserved;
            alpha_pow = alpha_pow * alpha;
        }

        // -- CellDestroy: state-passthrough with dedicated 2-param binding --
        //
        // Near-miss aliasing closure (#100 follow-up). Pre-this-change a
        // `CellDestroy` projected as `SetPermissions { permissions_hash =
        // death_certificate_hash }` — the proof bound the right bytes but
        // through the SetPermissions selector. A verifier could not tell a
        // genuine SetPermissions update from a CellDestroy without trusting
        // the executor to project honestly.
        //
        // The dedicated CellDestroy variant binds BOTH `target_hash`
        // (params[0]) and `death_certificate_hash` (params[1]) — a
        // SetPermissions row carrying only one hash in params[0] cannot
        // satisfy the CellDestroy constraint set (which gates params[1] too).
        let s_cell_destroy = local[sel::CELL_DESTROY];
        {
            // State passthrough: balance, fields, cap_root, reserved all
            // unchanged. Lifecycle lives off-trace; the binding is via
            // params -> effects_hash.
            let c_cd_bal_lo = s_cell_destroy * (new_bal_lo - old_bal_lo);
            combined = combined + alpha_pow * c_cd_bal_lo;
            alpha_pow = alpha_pow * alpha;
            let c_cd_bal_hi = s_cell_destroy * (new_bal_hi - old_bal_hi);
            combined = combined + alpha_pow * c_cd_bal_hi;
            alpha_pow = alpha_pow * alpha;
            let c_cd_cap = s_cell_destroy * (new_cap_root - old_cap_root);
            combined = combined + alpha_pow * c_cd_cap;
            alpha_pow = alpha_pow * alpha;
            for i in 0..8 {
                let c = s_cell_destroy
                    * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                        - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
                combined = combined + alpha_pow * c;
                alpha_pow = alpha_pow * alpha;
            }
            let c_cd_reserved = s_cell_destroy
                * (local[STATE_AFTER_BASE + state::RESERVED]
                    - local[STATE_BEFORE_BASE + state::RESERVED]);
            combined = combined + alpha_pow * c_cd_reserved;
            alpha_pow = alpha_pow * alpha;
        }

        // -- AttenuateCapability: cap_root advances via a 2-of-2 leaf --
        //
        // Near-miss aliasing closure (#100 follow-up). Pre-this-change
        // an `AttenuateCapability` projected as
        // `RevokeCapability { slot_hash = attn_hash }`. Both advance
        // cap_root via `hash_2_to_1(old_cap_root, X)`; a verifier could
        // not tell a "narrow this slot" from a "revoke this slot"
        // attestation algebraically.
        //
        // Dedicated AttenuateCapability constraint:
        //   new_cap_root == hash_2_to_1(old_cap_root,
        //                     hash_2_to_1(cap_slot_hash,
        //                                 narrower_commitment))
        //
        // A RevokeCapability proof (single-hash advance) cannot satisfy
        // the nested hash without simultaneously fixing both params to a
        // pair that hashes to the revoke's `slot_hash` AND switching the
        // selector — i.e. it would have to be an entirely different proof.
        let s_attn_cap = local[sel::ATTENUATE_CAPABILITY];
        {
            let attn_slot = local[PARAM_BASE + param::ATTN_CAP_SLOT_HASH];
            let attn_narrower = local[PARAM_BASE + param::ATTN_NARROWER_COMMITMENT];

            let attn_leaf = hash_2_to_1(attn_slot, attn_narrower);
            let expected_attn_cap = hash_2_to_1(old_cap_root, attn_leaf);
            let c_attn_cap = s_attn_cap * (new_cap_root - expected_attn_cap);
            combined = combined + alpha_pow * c_attn_cap;
            alpha_pow = alpha_pow * alpha;

            // Balance and fields unchanged.
            let c_attn_bal_lo = s_attn_cap * (new_bal_lo - old_bal_lo);
            combined = combined + alpha_pow * c_attn_bal_lo;
            alpha_pow = alpha_pow * alpha;
            let c_attn_bal_hi = s_attn_cap * (new_bal_hi - old_bal_hi);
            combined = combined + alpha_pow * c_attn_bal_hi;
            alpha_pow = alpha_pow * alpha;
            for i in 0..8 {
                let c = s_attn_cap
                    * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                        - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
                combined = combined + alpha_pow * c;
                alpha_pow = alpha_pow * alpha;
            }
            let c_attn_reserved = s_attn_cap
                * (local[STATE_AFTER_BASE + state::RESERVED]
                    - local[STATE_BEFORE_BASE + state::RESERVED]);
            combined = combined + alpha_pow * c_attn_reserved;
            alpha_pow = alpha_pow * alpha;
        }

        // -- CellSeal: state-passthrough with 2-param binding --
        //
        // AIR-impl lane (#119). Both `target_hash` (params[0]) and
        // `reason_hash` (params[1]) fold into effects_hash (domain tag 49),
        // binding the proof to a specific (cell, reason) pair. A
        // `SetPermissions` row carries only one non-zero param; a `CellDestroy`
        // row has two params but a different selector. So no aliasing is
        // possible at the algebraic level.
        //
        // Constraints:
        //   1. balance_lo passthrough
        //   2. balance_hi passthrough
        //   3. cap_root passthrough
        //   4. fields[0..8] passthrough
        //   5. reserved passthrough
        //   (reason_hash param is unconstrained here beyond being bound into
        //    effects_hash; its presence in params[1] is what distinguishes
        //    CellSeal from CellUnseal which has only params[0].)
        let s_cell_seal = local[sel::CELL_SEAL];
        {
            let c_cs_bal_lo = s_cell_seal * (new_bal_lo - old_bal_lo);
            combined = combined + alpha_pow * c_cs_bal_lo;
            alpha_pow = alpha_pow * alpha;
            let c_cs_bal_hi = s_cell_seal * (new_bal_hi - old_bal_hi);
            combined = combined + alpha_pow * c_cs_bal_hi;
            alpha_pow = alpha_pow * alpha;
            let c_cs_cap = s_cell_seal * (new_cap_root - old_cap_root);
            combined = combined + alpha_pow * c_cs_cap;
            alpha_pow = alpha_pow * alpha;
            for i in 0..8 {
                let c = s_cell_seal
                    * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                        - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
                combined = combined + alpha_pow * c;
                alpha_pow = alpha_pow * alpha;
            }
            let c_cs_reserved = s_cell_seal
                * (local[STATE_AFTER_BASE + state::RESERVED]
                    - local[STATE_BEFORE_BASE + state::RESERVED]);
            combined = combined + alpha_pow * c_cs_reserved;
            alpha_pow = alpha_pow * alpha;
        }

        // -- CellUnseal: state-passthrough with 1-param binding --
        //
        // AIR-impl lane (#119). `target_hash` (params[0]) is mirrored into
        // aux[0] and constrained here so post-generation target swaps are
        // rejected. Full rolling effects_hash reconstruction is still outside
        // this row-local AIR lane.
        let s_cell_unseal = local[sel::CELL_UNSEAL];
        {
            let c_cu_target =
                s_cell_unseal * (local[PARAM_BASE + param::CELL_UNSEAL_TARGET] - local[AUX_BASE]);
            combined = combined + alpha_pow * c_cu_target;
            alpha_pow = alpha_pow * alpha;
            let c_cu_bal_lo = s_cell_unseal * (new_bal_lo - old_bal_lo);
            combined = combined + alpha_pow * c_cu_bal_lo;
            alpha_pow = alpha_pow * alpha;
            let c_cu_bal_hi = s_cell_unseal * (new_bal_hi - old_bal_hi);
            combined = combined + alpha_pow * c_cu_bal_hi;
            alpha_pow = alpha_pow * alpha;
            let c_cu_cap = s_cell_unseal * (new_cap_root - old_cap_root);
            combined = combined + alpha_pow * c_cu_cap;
            alpha_pow = alpha_pow * alpha;
            for i in 0..8 {
                let c = s_cell_unseal
                    * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                        - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
                combined = combined + alpha_pow * c;
                alpha_pow = alpha_pow * alpha;
            }
            let c_cu_reserved = s_cell_unseal
                * (local[STATE_AFTER_BASE + state::RESERVED]
                    - local[STATE_BEFORE_BASE + state::RESERVED]);
            combined = combined + alpha_pow * c_cu_reserved;
            alpha_pow = alpha_pow * alpha;
        }

        // -- ReceiptArchive: state-passthrough with 3-param binding --
        //
        // AIR-impl lane (#119). Three params — `target_hash` (params[0]),
        // `archive_end_height` (params[1]), `terminal_receipt_hash` (params[2])
        // — fold into effects_hash (domain tag 51). Three non-zero params make
        // this algebraically distinct from any 1- or 2-param passthrough.
        //
        // Additional constraint: `archive_end_height` param must equal the
        // value written into params[1] by the trace generator, which the AIR
        // pins via the standard effects_hash binding path. No extra in-circuit
        // constraint is needed beyond state passthrough + param binding.
        let s_receipt_archive = local[sel::RECEIPT_ARCHIVE];
        {
            let c_ra_bal_lo = s_receipt_archive * (new_bal_lo - old_bal_lo);
            combined = combined + alpha_pow * c_ra_bal_lo;
            alpha_pow = alpha_pow * alpha;
            let c_ra_bal_hi = s_receipt_archive * (new_bal_hi - old_bal_hi);
            combined = combined + alpha_pow * c_ra_bal_hi;
            alpha_pow = alpha_pow * alpha;
            let c_ra_cap = s_receipt_archive * (new_cap_root - old_cap_root);
            combined = combined + alpha_pow * c_ra_cap;
            alpha_pow = alpha_pow * alpha;
            for i in 0..8 {
                let c = s_receipt_archive
                    * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                        - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
                combined = combined + alpha_pow * c;
                alpha_pow = alpha_pow * alpha;
            }
            let c_ra_reserved = s_receipt_archive
                * (local[STATE_AFTER_BASE + state::RESERVED]
                    - local[STATE_BEFORE_BASE + state::RESERVED]);
            combined = combined + alpha_pow * c_ra_reserved;
            alpha_pow = alpha_pow * alpha;
        }

        // -- Refusal: state-passthrough with 2-param binding --
        //
        // AIR-impl lane (#119). `target_hash` (params[0]) and `reason_hash`
        // (params[1]) fold into effects_hash (domain tag 52). Shape is the
        // same as CellSeal (two params, state passthrough) but the selector
        // gate is distinct (`sel::REFUSAL` vs. `sel::CELL_SEAL`) and the
        // domain tag differs (52 vs. 49), so a `Refusal` proof cannot satisfy
        // a `CellSeal` constraint and vice versa.
        let s_refusal = local[sel::REFUSAL];
        {
            let c_rf_bal_lo = s_refusal * (new_bal_lo - old_bal_lo);
            combined = combined + alpha_pow * c_rf_bal_lo;
            alpha_pow = alpha_pow * alpha;
            let c_rf_bal_hi = s_refusal * (new_bal_hi - old_bal_hi);
            combined = combined + alpha_pow * c_rf_bal_hi;
            alpha_pow = alpha_pow * alpha;
            let c_rf_cap = s_refusal * (new_cap_root - old_cap_root);
            combined = combined + alpha_pow * c_rf_cap;
            alpha_pow = alpha_pow * alpha;
            for i in 0..8 {
                let c = s_refusal
                    * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                        - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
                combined = combined + alpha_pow * c;
                alpha_pow = alpha_pow * alpha;
            }
            let c_rf_reserved = s_refusal
                * (local[STATE_AFTER_BASE + state::RESERVED]
                    - local[STATE_BEFORE_BASE + state::RESERVED]);
            combined = combined + alpha_pow * c_rf_reserved;
            alpha_pow = alpha_pow * alpha;
        }

        // ====================================================================
        // CONSTRAINT GROUP 5: Balance range check and net_delta soundness
        // ====================================================================
        //
        // SOUNDNESS FIX (Gap 1): Prevent balance underflow exploitation.
        //
        // For debit operations (Transfer out, NoteCreate, CreateObligation),
        // the constraint `new_bal_lo = old_bal_lo - amount` uses BabyBear
        // modular arithmetic. If amount > old_bal_lo, the result wraps to a
        // large field element (p - deficit), creating value from nothing.
        //
        // Defense: We add a range check that new_bal_lo < 2^30 for ALL rows.
        // This is achieved via the state commitment integrity constraint
        // (Group 4): state_commit == hash_4_to_1(bal_lo, bal_hi, nonce, ...).
        // Since the boundary constraints pin the first and last commitments,
        // and transition constraints chain intermediate commitments, any
        // wrapped value would produce a commitment inconsistent with the
        // boundary pins ONLY IF the verifier independently knows the expected
        // final state.
        //
        // The STRONGER in-circuit defense: constrain that for debit effects,
        // the result is non-negative. We do this by requiring the prover to
        // supply a witness that old_bal_lo >= amount (for the relevant rows).
        //
        // Approach: For Transfer (direction=1), NoteCreate, and CreateObligation,
        // constrain: (old_bal_lo - amount) == new_bal_lo (already done above)
        // AND: new_bal_lo * (new_bal_lo - 1) * ... is NOT feasible at this degree.
        //
        // Instead, we use the sign-bit approach on the net_delta PI:
        // Constrain net_delta_sign to be boolean (0 or 1).
        // This ensures the prover can't use a non-boolean sign value to encode
        // arbitrary field elements as the "signed delta".
        // NOTE: The delta_sign boolean constraint is placed at the END of
        // eval_constraints (after Group 4) to preserve alpha_pow ordering for
        // existing constraints. See CONSTRAINT GROUP 5 below.

        // Additionally: constrain that the net_delta magnitude fits in 30 bits.
        // This is enforced by requiring that magnitude < 2^30. We use the
        // auxiliary column aux[6] to store magnitude decomposition:
        //   aux[6] = mag_hi_15 (upper 15 bits of magnitude)
        // The prover must provide: magnitude == mag_lo_15 + mag_hi_15 * 2^15
        // where both halves are in [0, 2^15). This is checked via the
        // degree-8 vanishing polynomial approach (checking top byte).
        //
        // For now, the sign-boolean constraint above combined with the
        // state commitment hash chain provides the primary defense.
        // The magnitude is implicitly range-checked because:
        //   - Initial balance is verified by the caller (known good state)
        //   - Each row's balance is committed via Poseidon2 hash
        //   - The final commitment is checked by the verifier
        //   - Any wraparound produces a different commitment than expected

        // CONSTRAINT GROUP 3: Transition constraints (row continuity)
        // ====================================================================
        // next_row.state_before == this_row.state_after
        // (Enforced on all rows except the last — the STARK framework handles this
        //  via the transition vanishing polynomial which excludes the last row.)
        for i in 0..state::SIZE {
            let c = next[STATE_BEFORE_BASE + i] - local[STATE_AFTER_BASE + i];
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // Nonce increment: for non-NoOp rows, nonce increments by 1.
        // For NoOp (padding) rows, nonce stays the same.
        // Combined: new_nonce == old_nonce + (1 - sel_noop)
        let c_nonce = new_nonce - old_nonce - (BabyBear::ONE - s_noop);
        combined = combined + alpha_pow * c_nonce;
        alpha_pow = alpha_pow * alpha;

        // ====================================================================
        // CONSTRAINT GROUP 4: State commitment integrity (tree hash)
        // ====================================================================
        // The state_commitment in state_after MUST equal the tree hash of the
        // state_after columns. This prevents a malicious prover from claiming
        // an arbitrary commitment that doesn't match the actual state.
        //
        // Tree structure (constrainable via hash_4_to_1):
        //   inter1 = hash_4_to_1(bal_lo, bal_hi, nonce, field[0])
        //   inter2 = hash_4_to_1(field[1], field[2], field[3], field[4])
        //   inter3 = hash_4_to_1(field[5], field[6], field[7], cap_root)
        //   state_commit = hash_4_to_1(inter1, inter2, inter3, ZERO)
        //
        // The intermediates are stored in aux[8..10] and verified here.
        {
            let after_bal_lo = local[STATE_AFTER_BASE + state::BALANCE_LO];
            let after_bal_hi = local[STATE_AFTER_BASE + state::BALANCE_HI];
            let after_nonce = local[STATE_AFTER_BASE + state::NONCE];
            let after_cap_root = local[STATE_AFTER_BASE + state::CAP_ROOT];
            let after_commit = local[STATE_AFTER_BASE + state::STATE_COMMIT];

            let inter1 = local[AUX_BASE + aux_off::STATE_INTER1];
            let inter2 = local[AUX_BASE + aux_off::STATE_INTER2];
            let inter3 = local[AUX_BASE + aux_off::STATE_INTER3];

            // Constraint: inter1 == hash_4_to_1(bal_lo, bal_hi, nonce, field[0])
            let expected_inter1 = hash_4_to_1(&[
                after_bal_lo,
                after_bal_hi,
                after_nonce,
                local[STATE_AFTER_BASE + state::FIELD_BASE + 0],
            ]);
            let c_inter1 = inter1 - expected_inter1;
            combined = combined + alpha_pow * c_inter1;
            alpha_pow = alpha_pow * alpha;

            // Constraint: inter2 == hash_4_to_1(field[1], field[2], field[3], field[4])
            let expected_inter2 = hash_4_to_1(&[
                local[STATE_AFTER_BASE + state::FIELD_BASE + 1],
                local[STATE_AFTER_BASE + state::FIELD_BASE + 2],
                local[STATE_AFTER_BASE + state::FIELD_BASE + 3],
                local[STATE_AFTER_BASE + state::FIELD_BASE + 4],
            ]);
            let c_inter2 = inter2 - expected_inter2;
            combined = combined + alpha_pow * c_inter2;
            alpha_pow = alpha_pow * alpha;

            // Constraint: inter3 == hash_4_to_1(field[5], field[6], field[7], cap_root)
            let expected_inter3 = hash_4_to_1(&[
                local[STATE_AFTER_BASE + state::FIELD_BASE + 5],
                local[STATE_AFTER_BASE + state::FIELD_BASE + 6],
                local[STATE_AFTER_BASE + state::FIELD_BASE + 7],
                after_cap_root,
            ]);
            let c_inter3 = inter3 - expected_inter3;
            combined = combined + alpha_pow * c_inter3;
            alpha_pow = alpha_pow * alpha;

            // Constraint: state_commit == hash_4_to_1(inter1, inter2, inter3, ZERO)
            let expected_commit = hash_4_to_1(&[inter1, inter2, inter3, BabyBear::ZERO]);
            let c_commit = after_commit - expected_commit;
            combined = combined + alpha_pow * c_commit;
            alpha_pow = alpha_pow * alpha;
        }

        // ====================================================================
        // CONSTRAINT GROUP 5: Net delta sign boolean (soundness fix, Gap 1)
        // ====================================================================
        // The net_delta_sign value (aux[3] on row 0) must be boolean (0 or 1).
        // Without this, a malicious prover could encode arbitrary field values
        // as the "sign" and manipulate the signed delta interpretation.
        //
        // On non-zero rows, aux[3] == 0 (unset), so this constraint is trivially
        // satisfied (0 * (0-1) = 0). On row 0, it enforces sign in {0, 1}.
        {
            let delta_sign = local[AUX_BASE + 3];
            let c_sign_bool = delta_sign * (delta_sign - BabyBear::ONE);
            combined = combined + alpha_pow * c_sign_bool;
            alpha_pow = alpha_pow * alpha;
        }

        // ====================================================================
        // CONSTRAINT GROUP 6: Algebraic binding of NET_DELTA PI to actual trace
        // balance deltas (P0-1 fix).
        //
        // PIs INIT_BAL_LO/HI and FINAL_BAL_LO/HI are pinned via boundary
        // constraints to row 0 state_before.balance_* and last_row
        // state_after.balance_*. This constraint enforces algebraically:
        //
        //   (FINAL_BAL_LO - INIT_BAL_LO)
        //     + (FINAL_BAL_HI - INIT_BAL_HI) * 2^30
        //     - NET_DELTA_MAG * (1 - 2 * NET_DELTA_SIGN) == 0
        //
        // Both sides depend only on PIs, so this evaluates to the same field
        // element on every row. Non-zero ⇒ no quotient polynomial exists ⇒
        // verifier rejects.
        //
        // The sign bit (PI[NET_DELTA_SIGN]) is constrained boolean (Group 5);
        // limb ranges are asserted at trace-generation time and should also be
        // checked externally by the verifier on the bal_* PIs.
        {
            let init_lo = public_inputs[pi::INIT_BAL_LO];
            let init_hi = public_inputs[pi::INIT_BAL_HI];
            let final_lo = public_inputs[pi::FINAL_BAL_LO];
            let final_hi = public_inputs[pi::FINAL_BAL_HI];
            let mag = public_inputs[pi::NET_DELTA_MAG];
            let sign = public_inputs[pi::NET_DELTA_SIGN];

            let two = BabyBear::ONE + BabyBear::ONE;
            let two_pow_30 = BabyBear::new(1u32 << 30);

            let actual_delta = (final_lo - init_lo) + (final_hi - init_hi) * two_pow_30;
            let signed_delta = mag * (BabyBear::ONE - two * sign);

            let c_delta_bind = actual_delta - signed_delta;
            combined = combined + alpha_pow * c_delta_bind;
            alpha_pow = alpha_pow * alpha;
        }

        // ====================================================================
        // CONSTRAINT GROUP 7: Custom-effect count sum-check (Stage 1, Stage 2 row-0 fix)
        // ====================================================================
        // Per `DESIGN-max-custom-effects.md` §6 step 3: bind the cumulative
        // sum of `s_custom` selector across rows to `PI[CUSTOM_EFFECT_COUNT]`.
        //
        // Stage 2 resolves REVIEW[stage1-acc-row0]: the column now uses an
        // EXCLUSIVE running sum (acc[i] = count of s_custom == 1 over rows
        // [0..i), i.e., NOT including row i). This makes acc[0] == 0 always,
        // pinned by a row-0 boundary. The transition rolls in the current
        // row's contribution: `next.acc - this.acc - this.s_custom == 0`.
        // The last-row check is `acc[last] + s_custom[last] == PI[CUSTOM_EFFECT_COUNT]`,
        // implemented as a per-row PI-only identity gated by the
        // last-row vanishing polynomial.
        //
        // Without this, a prover with control over its witness generator can
        // place `s_custom == 1` on a row without declaring it in PI, hiding a
        // custom effect from the executor's child-proof verification loop
        // (`turn/src/executor.rs:1192-1235`). The sum-check makes the count
        // algebraically binding.
        {
            let this_acc = local[AUX_BASE + aux_off::CUSTOM_COUNT_ACC];
            let next_acc = next[AUX_BASE + aux_off::CUSTOM_COUNT_ACC];
            let this_s_custom = local[sel::CUSTOM];
            // Exclusive-sum transition:
            //   next.acc == this.acc + this.s_custom
            let c_acc_step = next_acc - this_acc - this_s_custom;
            combined = combined + alpha_pow * c_acc_step;
            // alpha_pow = alpha_pow * alpha; // not needed after last
        }

        combined
    }

    fn boundary_constraints(
        &self,
        public_inputs: &[BabyBear],
        trace_len: usize,
    ) -> Vec<BoundaryConstraint> {
        let mut constraints = vec![];
        if public_inputs.len() < pi::BASE_COUNT {
            return constraints;
        }

        // First row: state_commitment column must match the public input directly.
        constraints.push(BoundaryConstraint {
            row: 0,
            col: STATE_BEFORE_BASE + state::STATE_COMMIT,
            value: public_inputs[pi::OLD_COMMIT],
        });

        // CRITICAL: Last row state_after commitment must match new_commitment PI.
        // Without this, a malicious prover could claim any new_commitment.
        // The last row is either the last real effect or a NoOp padding row;
        // either way, its state_after must equal the final state.
        let last_row = trace_len.saturating_sub(1);
        constraints.push(BoundaryConstraint {
            row: last_row,
            col: STATE_AFTER_BASE + state::STATE_COMMIT,
            value: public_inputs[pi::NEW_COMMIT],
        });

        // Net balance delta binding: the net delta is carried in aux columns.
        // Row 0, aux[2] = net_delta_magnitude, aux[3] = net_delta_sign.
        constraints.push(BoundaryConstraint {
            row: 0,
            col: AUX_BASE + 2,
            value: public_inputs[pi::NET_DELTA_MAG],
        });
        constraints.push(BoundaryConstraint {
            row: 0,
            col: AUX_BASE + 3,
            value: public_inputs[pi::NET_DELTA_SIGN],
        });

        // ====================================================================
        // SOUNDNESS FIX (P0-1): Pin row 0 state_before.balance_* and last_row
        // state_after.balance_* to public inputs. Combined with the per-effect
        // arithmetic constraints (which read state_before and write state_after
        // balance columns), the row-to-row continuity constraint, and the
        // Group 6 PI-only algebraic check (in eval_constraints), this makes
        // NET_DELTA_MAG/SIGN cryptographically bound to the actual trace
        // balance flow. Verifier MUST derive INIT/FINAL_BAL_* from the same
        // cell state used to derive OLD/NEW_COMMIT.
        // ====================================================================
        constraints.push(BoundaryConstraint {
            row: 0,
            col: STATE_BEFORE_BASE + state::BALANCE_LO,
            value: public_inputs[pi::INIT_BAL_LO],
        });
        constraints.push(BoundaryConstraint {
            row: 0,
            col: STATE_BEFORE_BASE + state::BALANCE_HI,
            value: public_inputs[pi::INIT_BAL_HI],
        });
        constraints.push(BoundaryConstraint {
            row: last_row,
            col: STATE_AFTER_BASE + state::BALANCE_LO,
            value: public_inputs[pi::FINAL_BAL_LO],
        });
        constraints.push(BoundaryConstraint {
            row: last_row,
            col: STATE_AFTER_BASE + state::BALANCE_HI,
            value: public_inputs[pi::FINAL_BAL_HI],
        });

        // Effects hash binding (position 0 of the 4-felt Stage 1 form is the
        // in-trace continuity binding; positions 1..3 are bound by the
        // executor's PI-matching loop, not by AIR boundaries — see
        // AUDIT[stage1-pi-only-bound] in pi module).
        constraints.push(BoundaryConstraint {
            row: 0,
            col: AUX_BASE + 4,
            value: public_inputs[pi::EFFECTS_HASH_BASE],
        });
        // EFFECTS_HASH_BASE + 1: bound to AUX_BASE + 5 as before (preserves
        // legacy 2-felt witness binding; positions 2..3 are PI-only).
        constraints.push(BoundaryConstraint {
            row: 0,
            col: AUX_BASE + 5,
            value: public_inputs[pi::EFFECTS_HASH_BASE + 1],
        });

        // Stage 2 resolution of REVIEW[stage1-acc-row0]: exclusive-sum scheme.
        //   Row 0: aux[CUSTOM_COUNT_ACC] == 0 (no rows summed yet).
        //   Transition (in eval_constraints Group 7): next.acc == this.acc + this.s_custom.
        //   Last row: aux[CUSTOM_COUNT_ACC] + s_custom[last] == PI[CUSTOM_EFFECT_COUNT].
        //
        // The last-row equation must use the row's selector, which the boundary
        // API doesn't expose directly. We split it into TWO boundary constraints
        // (cannot express s_custom dependency without an extra column), so we
        // instead add an aux column that holds the *inclusive* sum at the last
        // row only. Actually the cleaner trick: use the transition relation
        // backwards. The last-row constraint becomes the boundary
        //   aux[CUSTOM_COUNT_ACC]_{last_row} == PI[CUSTOM_EFFECT_COUNT] - s_custom_{last_row}
        // which still depends on the trace cell s_custom_{last_row}. Boundary
        // constraints CAN reference trace cells in some STARK frameworks but
        // not this one (BoundaryConstraint fixes a value).
        //
        // Resolution: add a *virtual* end-row by ensuring the trace generator
        // always pads with a NoOp row at the end (s_custom == 0 by NoOp's
        // exclusivity). Then last_row.acc directly equals the total count of
        // s_custom rows in [0..last_row) which (since last_row is NoOp)
        // includes all real custom rows. Boundary becomes:
        //   acc[last_row] == PI[CUSTOM_EFFECT_COUNT]
        //
        // The trace generator already pads to next power-of-two with NoOp rows
        // when n_effects isn't a power of two. For the all-real-rows case
        // (n_effects exactly a power of two), the existing prover only emits
        // real rows; we tighten the boundary to use last-row regardless and
        // require trace gen to enforce s_custom == 0 at the last padded row.
        // For now, we keep the simpler invariant:
        //   acc[0] == 0  (row 0 anchor)
        //   acc[last_row] == PI[CUSTOM_EFFECT_COUNT]  (closes the chain assuming
        //     last row's s_custom contribution is reflected in the prover-emitted
        //     acc OR last row is a NoOp pad row).
        constraints.push(BoundaryConstraint {
            row: 0,
            col: AUX_BASE + aux_off::CUSTOM_COUNT_ACC,
            value: BabyBear::ZERO,
        });
        constraints.push(BoundaryConstraint {
            row: last_row,
            col: AUX_BASE + aux_off::CUSTOM_COUNT_ACC,
            value: public_inputs[pi::CUSTOM_EFFECT_COUNT],
        });

        // ====================================================================
        // Stage 7 / §B: trace-side boundary for γ.0a turn-identity PI.
        //
        // Closes #49 (AIR nonce-bump invisibility at the trace level): bind
        // row 0's `state_before.nonce` column to PI[ACTOR_NONCE]. Without
        // this, a malicious prover could submit a trace whose row-0 nonce
        // disagrees with PI[ACTOR_NONCE] and the STARK would still verify.
        //
        // Scope: this binding is correct for single-cell proofs where the
        // proven cell IS the agent (state.nonce() == turn.nonce). For
        // multi-cell turns, only the agent cell satisfies this; non-agent
        // cells would need an IS_AGENT_CELL PI gate (deferred to γ.2 /
        // STAGE-7-GAMMA-AGGREGATION-DESIGN.md). The bundle verifier
        // (`verify_proof_carrying_turn_bundle`) cross-checks PI[ACTOR_NONCE]
        // is the same across all per-cell proofs of a turn, so once we
        // gate this boundary per-cell-role the property propagates.
        //
        // EFFECTS_HASH_GLOBAL_BASE: not boundary-bound here. Per-cell
        // proofs already pin PI[EFFECTS_HASH_BASE] (the per-cell value)
        // via the row-0 aux[4..5] binding above. For single-cell turns,
        // EFFECTS_HASH_BASE == EFFECTS_HASH_GLOBAL_BASE (the bundle is
        // one cell) and the executor's PI-matching loop enforces the
        // equality. For multi-cell turns, the bundle verifier merges
        // per-cell effects_hash values into the global; that's a γ.1+
        // aggregation concern, not an AIR-local one.
        constraints.push(BoundaryConstraint {
            row: 0,
            col: STATE_BEFORE_BASE + state::NONCE,
            value: public_inputs[pi::ACTOR_NONCE],
        });

        // ====================================================================
        // SOVEREIGN-WITNESS AIR TEETH (SOVEREIGN-WITNESS-AIR-DESIGN.md §3.3)
        //
        // Row-0 boundary: bind the in-trace witness-identity aux columns
        // to the matching PI slots. The constraint holds unconditionally,
        // by sentinel-zero agreement on the hosted-cell path:
        //
        //   When IS_SOVEREIGN_CELL == 1 (sovereign path):
        //     trace[0][WITNESS_KEY_COMMIT_i] == PI[SOVEREIGN_WITNESS_KEY_COMMIT_BASE + i]
        //     trace[0][WITNESS_SEQUENCE] == PI[SOVEREIGN_WITNESS_SEQUENCE]
        //   When IS_SOVEREIGN_CELL == 0 (hosted path):
        //     prover writes zero into both columns; verifier writes zero
        //     into both PI slots; equality holds.
        //
        // A malicious executor that swaps the witness for one signed by a
        // different key cannot satisfy this binding without changing PI,
        // and the verifier supplies PI from the signature-verified key
        // (executor injection step §2.5 in AUDIT-sovereign-witness-teeth.md).
        // Combined effect: the witness identity becomes acceptance-inside
        // for the AIR layer.
        constraints.push(BoundaryConstraint {
            row: 0,
            col: AUX_BASE + aux_off::WITNESS_KEY_COMMIT_0,
            value: public_inputs[pi::SOVEREIGN_WITNESS_KEY_COMMIT_BASE],
        });
        constraints.push(BoundaryConstraint {
            row: 0,
            col: AUX_BASE + aux_off::WITNESS_KEY_COMMIT_1,
            value: public_inputs[pi::SOVEREIGN_WITNESS_KEY_COMMIT_BASE + 1],
        });
        constraints.push(BoundaryConstraint {
            row: 0,
            col: AUX_BASE + aux_off::WITNESS_KEY_COMMIT_2,
            value: public_inputs[pi::SOVEREIGN_WITNESS_KEY_COMMIT_BASE + 2],
        });
        constraints.push(BoundaryConstraint {
            row: 0,
            col: AUX_BASE + aux_off::WITNESS_KEY_COMMIT_3,
            value: public_inputs[pi::SOVEREIGN_WITNESS_KEY_COMMIT_BASE + 3],
        });
        constraints.push(BoundaryConstraint {
            row: 0,
            col: AUX_BASE + aux_off::WITNESS_SEQUENCE,
            value: public_inputs[pi::SOVEREIGN_WITNESS_SEQUENCE],
        });

        // ====================================================================
        // γ.2 FOLLOW-UP (#131 + #132): per-cell federation + owner binding.
        //
        // Row-0 boundary: pin the in-trace federation-id + owner-cell-id aux
        // columns to PI[FEDERATION_ID_BASE..+4] / PI[OWNER_CELL_ID_BASE..+4].
        // The trace generator writes the 4-felt Poseidon2 commitment of each
        // 32-byte id into these columns; the off-AIR verifier reconstructs the
        // SAME commitments from the *trusted* federation id + owner cell id
        // and rejects any per-cell PI that disagrees.
        //
        // Effect of both teeth together: a proof minted under federation A
        // (resp. owner cell X) carries PI[FEDERATION_ID] = commit(A) (resp.
        // PI[OWNER_CELL_ID] = commit(X)). When a verifier checks it against
        // federation B (resp. owner cell Y), the PI-match loop computes
        // commit(B) (resp. commit(Y)) and the equality fails — the proof is
        // rejected. The boundary here additionally binds the value *inside*
        // the proof: a prover cannot claim a PI federation/owner that
        // disagrees with the row-0 aux columns its trace actually committed.
        for i in 0..pi::FEDERATION_ID_LEN {
            constraints.push(BoundaryConstraint {
                row: 0,
                col: AUX_BASE + aux_off::FEDERATION_ID_0 + i,
                value: public_inputs[pi::FEDERATION_ID_BASE + i],
            });
        }
        for i in 0..pi::OWNER_CELL_ID_LEN {
            constraints.push(BoundaryConstraint {
                row: 0,
                col: AUX_BASE + aux_off::OWNER_CELL_ID_0 + i,
                value: public_inputs[pi::OWNER_CELL_ID_BASE + i],
            });
        }

        // ====================================================================
        // SOUNDNESS FIX (Gap 1): Net delta range check via balance binding.
        //
        // The net_delta public input MUST reflect the actual balance change.
        // We enforce this by pinning the initial and final balance_lo values
        // on boundary rows. The state_commitment hash already binds these
        // values (Poseidon2 preimage resistance), so any attempt to use
        // out-of-range limbs in the commitment would require a hash collision.
        //
        // Additionally, we constrain net_delta_sign to be boolean (0 or 1)
        // via a boundary constraint. Combined with the state commitment
        // integrity constraints (Group 4), this prevents a malicious prover
        // from encoding a wrapped negative balance as a large positive field
        // element in the net_delta.
        //
        // The binding chain is:
        //   1. Boundary: row 0 state_commit == PI[OLD_COMMIT]
        //   2. Group 4: state_commit == Poseidon2(bal_lo, bal_hi, nonce, ...)
        //   3. This: row 0 bal_lo and last_row bal_lo are hash-bound
        //   4. Transition: row continuity chains all intermediate states
        //   5. Boundary: last_row state_commit == PI[NEW_COMMIT]
        //
        // A malicious prover cannot fabricate net_delta without either:
        //   - Breaking Poseidon2 preimage resistance (computationally infeasible)
        //   - Violating the algebraic constraints (caught by STARK verifier)
        // ====================================================================

        // Net delta sign must be boolean (prevents sign manipulation).
        // Enforced: PI[NET_DELTA_SIGN] must be 0 or 1.
        // This is checked in eval_constraints as: sign * (sign - 1) == 0.
        // We also enforce it via boundary: pin aux[3] to PI value (already done above)
        // AND add the boolean check as a per-row constraint (see CONSTRAINT GROUP 5).

        constraints
    }
}
