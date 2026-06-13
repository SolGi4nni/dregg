//! Witness/trace generation for the Effect VM AIR.
//!
//! Builds the trace matrix and PI vector for each variant of `Effect`,
//! including the widened `EffectVmContext` carrying turn-identity,
//! slot-caveat manifests, and per-effect commitment witnesses.

use crate::field::BabyBear;
use crate::poseidon2::{hash_2_to_1, hash_4_to_1, hash_fact};

use super::{
    AUX_BASE, CellState, EFFECT_VM_WIDTH, Effect, PARAM_BASE, STATE_AFTER_BASE, STATE_BEFORE_BASE,
    aux_off, compute_effects_hash, compute_effects_hash_4, fill_balance_limb_bits,
    fill_reserved_bits, param, pi, sel, split_u64, u64_to_4_limbs_16,
};

/// Compress a 32-byte canonical id (federation id or cell id) into 4 BabyBear
/// felts (γ.2 #131/#132 per-cell federation + owner binding).
///
/// This is bit-identical to `dregg_commit::typed::canonical_32_to_felts_4`
/// (30-bit-per-limb packing folded through four `hash_4_to_1` compressions),
/// re-implemented here so the `dregg-circuit` crate stays free of a
/// `dregg-commit` dependency while still producing the same felts the
/// off-AIR verifier (`turn::executor::proof_verify`) reconstructs. Any drift
/// between the two would show up immediately as a PI-match rejection in the
/// `federation_owner_binding_round_trip` test and the executor PI loop.
pub fn canonical_id_to_felts_4(canonical: &[u8; 32]) -> [BabyBear; 4] {
    let mut eight = [BabyBear::ZERO; 8];
    for i in 0..8 {
        let lo = canonical[i * 4] as u32;
        let mid1 = canonical[i * 4 + 1] as u32;
        let mid2 = canonical[i * 4 + 2] as u32;
        let hi = canonical[i * 4 + 3] as u32;
        // Pack 30 bits: 8 + 8 + 8 + 6 = 30.
        eight[i] = BabyBear::new(lo | (mid1 << 8) | (mid2 << 16) | ((hi & 0x3F) << 24));
    }
    let a = hash_4_to_1(&[eight[0], eight[1], eight[2], eight[3]]);
    let b = hash_4_to_1(&[eight[4], eight[5], eight[6], eight[7]]);
    let c = hash_4_to_1(&[eight[0], eight[4], eight[2], eight[6]]);
    let d = hash_4_to_1(&[eight[1], eight[5], eight[3], eight[7]]);
    [a, b, c, d]
}

/// Generate the execution trace and public inputs for an effect VM proof.
///
/// # Arguments
/// * `initial_state` - The cell state before executing effects.
/// * `effects` - The sequence of effects to prove.
///
/// # Returns
/// (trace, public_inputs) suitable for `stark::prove`.
pub fn generate_effect_vm_trace(
    initial_state: &CellState,
    effects: &[Effect],
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    // Stage 7 / §B: for the default-context wrapper, set actor_nonce
    // from the initial cell nonce. This is the natural invariant for
    // single-cell proofs (the cell IS the agent), and it preserves
    // backwards-compat with the dozens of tests that pass a non-zero
    // initial nonce to CellState::new and rely on the row-0 boundary
    // (state_before.nonce == PI[ACTOR_NONCE]) holding.
    let mut ctx = EffectVmContext::default();
    ctx.actor_nonce = initial_state.nonce as u64;
    generate_effect_vm_trace_ext(initial_state, effects, ctx)
}

/// Extra context that goes into the widened PI layout (Stage 1 + 7-γ.0a).
///
/// All fields have safe defaults for backwards-compat: zero block height,
/// default `max_custom_effects`, empty approved-handoffs root, and
/// all-zero Stage 7-γ.0a turn-identity fields. Callers that produce
/// real per-cell proofs in the executor populate the γ.0a fields from
/// the live `Turn` and call_forest.
#[derive(Clone, Copy, Debug)]
pub struct EffectVmContext {
    /// Federation block height at turn-commit time. Used by timeout-bearing
    /// effects in later stages.
    pub current_block_height: u64,
    /// Per-cell maximum custom effects (from cell program manifest).
    pub max_custom_effects: u8,
    /// Federation-scoped approved-handoffs Merkle root (4-felt Poseidon2 form).
    /// RETIRED (VERB-LOCKSTEP): `ValidateHandoff` is gone; always the empty
    /// sentinel until the PI-layout compaction lane.
    pub approved_handoffs_root: [BabyBear; 4],
    /// Stage 7-γ.0a: Poseidon2 of canonical `Turn::hash()` (v3). Shared
    /// across all per-cell proofs of one turn.
    pub turn_hash: [BabyBear; 4],
    /// Stage 7-γ.0a: Poseidon2 over the canonical-DFS-order traversal
    /// of the entire call_forest's effects. Shared across the bundle.
    pub effects_hash_global: [BabyBear; 4],
    /// Stage 7-γ.0a: outer `Turn::nonce` promoted to PI; closes the
    /// differential-test gap from task #49 (AIR did not witness the
    /// agent's outer nonce bump). Shared across the bundle.
    pub actor_nonce: u64,
    /// Stage 7-γ.0a: Poseidon2 of `previous_receipt_hash` (or zero
    /// sentinel when None). Shared across the bundle.
    pub previous_receipt_hash: [BabyBear; 4],
    /// Sovereign-witness teeth (Phase 1): when this proof attests to a
    /// sovereign-witnessed effect, the 4-felt Poseidon2 hash of the
    /// witness's owning pubkey. Bound to the row-0 aux column and to
    /// PI[SOVEREIGN_WITNESS_KEY_COMMIT_BASE..+4]. Zero sentinel for
    /// hosted-cell proofs.
    pub sovereign_witness_key_commit: [BabyBear; 4],
    /// Sovereign-witness teeth (Phase 1): per-cell monotonic sequence
    /// from the witness. Bound to the row-0 aux column and to
    /// PI[SOVEREIGN_WITNESS_SEQUENCE]. Zero sentinel for hosted-cell
    /// proofs.
    pub sovereign_witness_sequence: u64,
    /// Sovereign-witness teeth (Phase 1): 1 iff this is a sovereign
    /// witnessed proof; 0 otherwise. Drives the (a)-style sentinel
    /// agreement between prover and verifier (no actual gating in the
    /// AIR — sentinel zeros on both sides make the boundary trivial
    /// when off).
    pub is_sovereign_cell: bool,
    /// Sovereign-witness teeth (Phase 2): 4-felt VK hash of the AIR the
    /// inner transition_proof was generated under. Zero sentinel when
    /// no transition_proof is supplied.
    pub sovereign_transition_proof_vk_hash: [BabyBear; 4],
    /// Sovereign-witness teeth (Phase 2): 4-felt Poseidon2 hash of the
    /// canonical inner-proof bytes. Zero sentinel when no transition_proof
    /// is supplied.
    pub sovereign_transition_proof_commitment: [BabyBear; 4],
    /// Sovereign-witness teeth (Phase 2): 1 iff a transition_proof
    /// was supplied AND `is_sovereign_cell` is true.
    pub has_transition_proof: bool,

    /// 30-bit-truncation fix (CAVEAT-LAYER-COVERAGE.md §6.5): 4×16-bit
    /// little-endian limbs of the full u64 `BridgeMint.value`. Position 0
    /// is the low 16 bits; position 3 is the high. Each limb < 2^16.
    /// Zero sentinel when no BridgeMint effect is in the trace.
    pub bridge_mint_value_limbs: [BabyBear; 4],
    /// RETIRED (VERB-LOCKSTEP): `BridgeLock` is gone; always zero.
    pub bridge_lock_value_limbs: [BabyBear; 4],
    /// RETIRED (VERB-LOCKSTEP): `CreateEscrow` is gone; always zero.
    pub create_escrow_amount_limbs: [BabyBear; 4],

    /// Slot-caveat manifest (Cav-Codex Block 3). Cell-program-declared
    /// `StateConstraint` set, projected into a fixed-size table for
    /// row-boundary AIR enforcement. `slot_caveat_count` ∈ [0,
    /// `pi::MAX_SLOT_CAVEATS`]; `slot_caveat_manifest[..count]`
    /// carries the entries.
    pub slot_caveat_count: u32,
    pub slot_caveat_manifest: [SlotCaveatEntry; pi::MAX_SLOT_CAVEATS],

    /// γ.2 follow-up (#131): the 32-byte federation id under which this proof
    /// is minted. Compressed to 4 felts via [`canonical_id_to_felts_4`] and
    /// pinned to PI[FEDERATION_ID_BASE..+4] + the row-0 aux columns. Zero by
    /// default (a fresh federation id of all-zeros is the local-federation
    /// sentinel, matching `TurnExecutor::local_federation_id`'s default).
    pub federation_id: [u8; 32],
    /// γ.2 follow-up (#132): the 32-byte owner cell id whose state transition
    /// this proof attests. Compressed to 4 felts via
    /// [`canonical_id_to_felts_4`] and pinned to PI[OWNER_CELL_ID_BASE..+4] +
    /// the row-0 aux columns. Zero by default (back-compat for callers that
    /// do not yet thread the owner id through; the off-AIR verifier supplies
    /// the same sentinel so the binding holds trivially).
    pub owner_cell_id: [u8; 32],

    /// PI v3 (THE ROTATION): the block height at which this cell's state was
    /// last committed. Bound to the canonical commitment as a commitment limb,
    /// so the PI face cannot be prover-chosen. Zero default (legacy / fresh
    /// cells) is a valid committed height.
    pub committed_height: u64,
    /// PI v3: rate-bound caveat tag. Semantics are staged: today this is the
    /// zero sentinel; the optimistic-proving mode (#169) will populate it.
    pub rate_bound_tag: u32,
    /// PI v3: challenge-window caveat tag. Semantics are staged: today this is
    /// the zero sentinel; the dispute/slashing mode (#169) will populate it.
    pub challenge_window_tag: u32,
}

/// A single entry in the slot-caveat manifest (Cav-Codex Block 3).
///
/// `type_tag` is one of `pi::SLOT_CAVEAT_TAG_*` (zero means "no
/// caveat"); `slot_index` is the cell-state field index; `params` are
/// up to 4 numeric parameters or a 4-felt commitment (the variant
/// determines the encoding — see `populate_slot_caveat_manifest`).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct SlotCaveatEntry {
    pub type_tag: u32,
    pub slot_index: u8,
    pub params: [BabyBear; 4],
}

impl SlotCaveatEntry {
    pub const fn zero() -> Self {
        Self {
            type_tag: 0,
            slot_index: 0,
            params: [BabyBear::ZERO; 4],
        }
    }

    /// Encode this entry into `out[..SLOT_CAVEAT_ENTRY_SIZE]` as
    /// (type_tag, slot_index, p0, p1, p2, p3).
    pub fn write_to(&self, out: &mut [BabyBear]) {
        debug_assert!(out.len() >= pi::SLOT_CAVEAT_ENTRY_SIZE);
        out[0] = BabyBear::new(self.type_tag);
        out[1] = BabyBear::new(self.slot_index as u32);
        for i in 0..4 {
            out[2 + i] = self.params[i];
        }
    }
}

/// STAGED (THE ROTATION — the widened caveat operand,
/// `docs/ROTATION-CUTOVER.md` §3 pre-gate). NOTHING live reads this type:
/// the live `SlotCaveatEntry` manifest at PI 101..126 is untouched; the
/// staged probe + tamper teeth ride the recursion-gated IR-v2 path
/// (`descriptor_ir2.rs`).
///
/// The rotated caveat entry widens `SlotCaveatEntry`'s `slot_index: u8` into
/// a DOMAIN-TAGGED operand `(domain_tag, key)` on the universal-memory
/// `UDomain` wire codes (registers 0 · heap 1 — `turn/src/umem.rs`): the
/// heap is the app-state lane, so capability attenuation must scope to heap
/// keys, and heap keys are FELTS (no u8 can carry them). A register (slot)
/// operand can NEVER alias a heap operand — domain separation is a THEOREM
/// (`caveat_operand_no_aliasing`,
/// `metatheory/Dregg2/Circuit/Emit/EffectVmEmitRotationCaveat.lean`), the
/// same discipline as the umem `Domain` tags. 7-felt packing:
/// `[type_tag, domain_tag, key, p0, p1, p2, p3]`
/// (`columns::rotation::caveat::ENTRY_SIZE`).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct RotCaveatEntry {
    /// One of `pi::SLOT_CAVEAT_TAG_*` (the slot and heap planes share ONE
    /// tag space); zero means "no caveat".
    pub type_tag: u32,
    /// `caveat::DOMAIN_REGISTERS` (0) or `caveat::DOMAIN_HEAP` (1). Decode
    /// REFUSES anything else (fail closed — there is no default plane).
    pub domain_tag: u32,
    /// The in-domain key: a register index (`< caveat::R`) in the registers
    /// domain; an arbitrary heap-key felt in the heap domain.
    pub key: BabyBear,
    pub params: [BabyBear; 4],
}

impl RotCaveatEntry {
    pub const SIZE: usize = super::columns::rotation::caveat::ENTRY_SIZE;

    pub const fn zero() -> Self {
        Self {
            type_tag: 0,
            domain_tag: 0,
            key: BabyBear::ZERO,
            params: [BabyBear::ZERO; 4],
        }
    }

    /// Encode this entry into `out[..SIZE]` as
    /// `(type_tag, domain_tag, key, p0, p1, p2, p3)`.
    pub fn write_to(&self, out: &mut [BabyBear]) {
        debug_assert!(out.len() >= Self::SIZE);
        out[0] = BabyBear::new(self.type_tag);
        out[1] = BabyBear::new(self.domain_tag);
        out[2] = self.key;
        for i in 0..4 {
            out[3 + i] = self.params[i];
        }
    }

    /// Decode an entry from its 7-felt packing — FAIL CLOSED:
    ///   * a forged/unknown domain tag REFUSES (only registers/heap are
    ///     caveat-scopable; caps/nullifiers/index are kernel planes);
    ///   * a registers-domain key outside the rotated register file
    ///     (`>= caveat::R`, the CONFIRMED R=24) REFUSES;
    ///   * a heap-domain key is any felt (heap keys are felts — the point).
    /// The zero entry (`type_tag == 0`) decodes as "no caveat" with no
    /// further checks (the all-zero padding rows).
    pub fn from_felts(f: &[BabyBear]) -> Result<Self, String> {
        use super::columns::rotation::caveat;
        if f.len() < Self::SIZE {
            return Err(format!(
                "RotCaveatEntry: need {} felts, got {}",
                Self::SIZE,
                f.len()
            ));
        }
        let entry = Self {
            type_tag: f[0].0,
            domain_tag: f[1].0,
            key: f[2],
            params: [f[3], f[4], f[5], f[6]],
        };
        if entry.type_tag == 0 {
            return Ok(entry);
        }
        match entry.domain_tag {
            caveat::DOMAIN_REGISTERS => {
                if (entry.key.0 as usize) >= caveat::R {
                    return Err(format!(
                        "RotCaveatEntry: registers-domain key {} outside the \
                         R={} register file (refused)",
                        entry.key.0,
                        caveat::R
                    ));
                }
            }
            caveat::DOMAIN_HEAP => {}
            other => {
                return Err(format!(
                    "RotCaveatEntry: unknown domain tag {other} (refused — \
                     only registers 0 / heap 1 are caveat-scopable)"
                ));
            }
        }
        Ok(entry)
    }
}

impl Default for EffectVmContext {
    fn default() -> Self {
        Self {
            current_block_height: 0,
            max_custom_effects: pi::MAX_CUSTOM_EFFECTS_DEFAULT,
            approved_handoffs_root: [BabyBear::ZERO; 4],
            turn_hash: [BabyBear::ZERO; 4],
            effects_hash_global: [BabyBear::ZERO; 4],
            actor_nonce: 0,
            previous_receipt_hash: [BabyBear::ZERO; 4],
            sovereign_witness_key_commit: [BabyBear::ZERO; 4],
            sovereign_witness_sequence: 0,
            is_sovereign_cell: false,
            sovereign_transition_proof_vk_hash: [BabyBear::ZERO; 4],
            sovereign_transition_proof_commitment: [BabyBear::ZERO; 4],
            has_transition_proof: false,
            bridge_mint_value_limbs: [BabyBear::ZERO; 4],
            bridge_lock_value_limbs: [BabyBear::ZERO; 4],
            create_escrow_amount_limbs: [BabyBear::ZERO; 4],
            slot_caveat_count: 0,
            slot_caveat_manifest: [SlotCaveatEntry::zero(); pi::MAX_SLOT_CAVEATS],
            federation_id: [0u8; 32],
            owner_cell_id: [0u8; 32],
            committed_height: 0,
            rate_bound_tag: 0,
            challenge_window_tag: 0,
        }
    }
}

/// Stage 1 trace generator. Same as [`generate_effect_vm_trace`] but accepts
/// the widened PI inputs ([`EffectVmContext`]).
pub fn generate_effect_vm_trace_ext(
    initial_state: &CellState,
    effects: &[Effect],
    context: EffectVmContext,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    assert!(!effects.is_empty(), "Need at least one effect");

    // ====================================================================
    // EXECUTOR-SIDE RANGE VALIDATION (o1vm audit mitigations)
    // ====================================================================
    // These checks run at proof generation time. They do NOT add constraints
    // to the STARK, but they prevent the executor from producing a trace with
    // out-of-range values that could exploit modular arithmetic.
    //
    // A verifier receiving a proof from an untrusted prover must additionally
    // verify that the final state (decoded from new_commitment PI) has valid
    // limb ranges. See `verify_balance_limb_ranges` below.
    // ====================================================================

    // Validate initial balance limbs are in range.
    let (init_lo, init_hi) = split_u64(initial_state.balance);
    assert!(
        init_lo.0 < (1 << 30),
        "Initial balance_lo out of range: {} >= 2^30",
        init_lo.0
    );
    assert!(
        init_hi.0 < (1 << 31),
        "Initial balance_hi out of range: {} >= 2^31 (exceeds BabyBear)",
        init_hi.0
    );

    // Validate field_idx bounds and balance underflow for all effects.
    // We track a running balance to catch underflow across multi-effect turns.
    {
        let mut running_balance = initial_state.balance;
        for effect in effects {
            match effect {
                Effect::SetField { field_idx, .. } => {
                    assert!(
                        *field_idx < 8,
                        "SetField field_idx out of bounds: {} (must be 0..7)",
                        field_idx
                    );
                }

                Effect::Transfer {
                    amount, direction, ..
                } => {
                    if *direction == 1 {
                        // Outgoing: validate no underflow.
                        assert!(
                            *amount <= running_balance,
                            "Transfer underflow: amount {} > running balance {} \
                             (executor rejects; STARK constraint would wrap in BabyBear)",
                            amount,
                            running_balance
                        );
                        running_balance -= amount;
                    } else {
                        running_balance = running_balance.saturating_add(*amount);
                    }
                }
                Effect::NoteCreate { .. } => {
                    // BALANCE-NEUTRAL: a NoteCreate moves NO transparent value (the
                    // note value lives in the commitment, never on the ledger), so it
                    // cannot underflow the running balance and does not decrement it.
                    // Matches the verified executor (`apply_note_create`) + Lean
                    // descriptor (`EffectVmEmitNoteCreate`, balance-neutral).
                }

                Effect::NoteSpend { value, .. } => {
                    running_balance = running_balance.saturating_add(*value);
                }

                Effect::Burn {
                    amount_lo,
                    amount_full,
                    ..
                } => {
                    // Burn debits balance by the low-30-bit amount the AIR
                    // constraint uses (mirrors NoteCreate / CreateEscrow).
                    // `amount_full` binds via effects_hash but doesn't drive
                    // the per-row balance arithmetic.
                    let _ = amount_full;
                    let amt = amount_lo.as_u32() as u64;
                    assert!(
                        amt <= running_balance,
                        "Burn underflow: amount_lo {} > running balance {}",
                        amt,
                        running_balance,
                    );
                    running_balance -= amt;
                }
                _ => {}
            }
        }
    }

    // Determine trace height (pad to power of 2, minimum MIN_TRACE_HEIGHT).
    //
    // MIN_TRACE_HEIGHT = 64 closes the FRI single-row-gap (task #90 /
    // TEST-REALITY-AUDIT A1). With a 2-row trace the FRI folding tree has only
    // one round and a single-row tamper can slip through probabilistically.
    // With 64 rows (domain_size = 256 at blowup-4, 6 FRI rounds) the quotient
    // polynomial deviation from low-degree is detectable with overwhelming
    // probability for any single-row tamper: the high-degree quotient is at
    // Hamming distance ≥ 3/4 · domain_size from any valid codeword, so
    // P(miss with 80 queries) ≤ (1/4)^80 ≈ 10^-48. Tradeoff: proofs for
    // short effect sequences use 64 NoOp padding rows instead of 2; the Merkle
    // tree and FRI layers are correspondingly larger but still fast.
    //
    // Stage 2 (REVIEW[stage1-acc-row0]): if the last real effect is a Custom,
    // we need at least one trailing NoOp row so the exclusive-sum boundary
    // `acc[last] == PI[CUSTOM_EFFECT_COUNT]` holds. Reserve a slot.
    const MIN_TRACE_HEIGHT: usize = 64;
    let n_effects = effects.len();
    let need_extra_pad = matches!(effects.last(), Some(Effect::Custom { .. }));
    let trace_height = if need_extra_pad {
        (n_effects + 1).next_power_of_two().max(MIN_TRACE_HEIGHT)
    } else {
        n_effects.next_power_of_two().max(MIN_TRACE_HEIGHT)
    };

    let mut trace = Vec::with_capacity(trace_height);
    let mut current_state = initial_state.clone();

    // Track net balance delta.
    let mut net_delta: i64 = 0;

    for effect in effects {
        let mut row = vec![BabyBear::ZERO; EFFECT_VM_WIDTH];

        // Set selector.
        let sel_idx = match effect {
            Effect::NoOp => sel::NOOP,
            Effect::Transfer { .. } => sel::TRANSFER,
            Effect::SetField { .. } => sel::SET_FIELD,
            Effect::GrantCapability { .. } => sel::GRANT_CAP,
            Effect::NoteSpend { .. } => sel::NOTE_SPEND,
            Effect::NoteCreate { .. } => sel::NOTE_CREATE,

            Effect::Custom { .. } => sel::CUSTOM,

            Effect::MakeSovereign => sel::MAKE_SOVEREIGN,
            Effect::CreateCellFromFactory { .. } => sel::CREATE_CELL_FROM_FACTORY,

            Effect::RevokeCapability { .. } => sel::REVOKE_CAPABILITY,
            Effect::EmitEvent { .. } => sel::EMIT_EVENT,
            Effect::SetPermissions { .. } => sel::SET_PERMISSIONS,
            Effect::SetVerificationKey { .. } => sel::SET_VERIFICATION_KEY,

            Effect::RefreshDelegation => sel::REFRESH_DELEGATION,
            Effect::IncrementNonce => sel::INCREMENT_NONCE,
            Effect::RevokeDelegation { .. } => sel::REVOKE_DELEGATION,
            Effect::CreateCell { .. } => sel::CREATE_CELL,
            Effect::SpawnWithDelegation { .. } => sel::SPAWN_WITH_DELEGATION,

            Effect::ExerciseViaCapability { .. } => sel::EXERCISE_VIA_CAPABILITY,
            Effect::Introduce { .. } => sel::INTRODUCE,
            Effect::PipelinedSend { .. } => sel::PIPELINED_SEND,

            Effect::BridgeMint { .. } => sel::BRIDGE_MINT,

            Effect::Burn { .. } => sel::BURN,
            Effect::CellDestroy { .. } => sel::CELL_DESTROY,
            Effect::AttenuateCapability { .. } => sel::ATTENUATE_CAPABILITY,
            Effect::CellSeal { .. } => sel::CELL_SEAL,
            Effect::CellUnseal { .. } => sel::CELL_UNSEAL,
            Effect::ReceiptArchive { .. } => sel::RECEIPT_ARCHIVE,
            Effect::Refusal { .. } => sel::REFUSAL,
        };
        row[sel_idx] = BabyBear::ONE;

        // Write state_before.
        let state_before_cols = current_state.to_trace_cols();
        for (i, &val) in state_before_cols.iter().enumerate() {
            row[STATE_BEFORE_BASE + i] = val;
        }

        // Apply effect and compute state_after + params.
        let mut new_state = current_state.clone();
        match effect {
            Effect::NoOp => {
                // No state change, no nonce increment for padding.
            }
            Effect::Transfer { amount, direction } => {
                let (lo, _hi) = split_u64(*amount);
                row[PARAM_BASE + param::AMOUNT] = lo;
                row[PARAM_BASE + param::DIRECTION] = BabyBear::new(*direction);

                if *direction == 1 {
                    // Outgoing.
                    new_state.balance = new_state.balance.saturating_sub(*amount);
                    net_delta -= *amount as i64;
                } else {
                    // Incoming.
                    new_state.balance = new_state.balance.saturating_add(*amount);
                    net_delta += *amount as i64;
                }
                new_state.nonce += 1;
            }
            Effect::SetField { field_idx, value } => {
                row[PARAM_BASE + param::FIELD_INDEX] = BabyBear::new(*field_idx);
                row[PARAM_BASE + param::NEW_VALUE] = *value;

                // Store old value at target index in aux[0] for the constraint.
                let idx = *field_idx as usize;
                row[AUX_BASE + 0] = current_state.fields[idx.min(7)];

                new_state.fields[idx.min(7)] = *value;
                new_state.nonce += 1;
            }
            Effect::GrantCapability { cap_entry, phase_b } => {
                // 32-byte widening: anchor limb[0] into params[0]; the AIR's
                // cap_root advance uses limb[0]. The full 8 limbs bind via
                // compute_effects_hash → PI[EFFECTS_HASH].
                row[PARAM_BASE + param::CAP_ENTRY] = cap_entry[0];

                match phase_b {
                    // ---- Phase B2: GRANTER-side delegation row ----
                    // The row covers the GRANTER, whose seeded cap_root holds
                    // the delegated-from cap; the p3 AIR's gates membership-open
                    // the held leaf against state_before.cap_root, enforce
                    // granted ⊑ held (submask + AuthRequired lattice + expiry),
                    // and pin params[0] to the granted leaf's in-circuit
                    // 7-field digest. Delegating does NOT move the granter's
                    // own tree (the install lands in the RECIPIENT's c-list),
                    // so cap_root passes through unchanged.
                    Some(w) => {
                        row[PARAM_BASE + param::GRANT_DIRECTION] = BabyBear::ONE;
                        row[PARAM_BASE + param::GRANT_HELD_SLOT_HASH] = w.held.slot_hash;
                        // capability_root: passthrough (no mutation).
                    }
                    // ---- Legacy: RECIPIENT install (direction 0) ----
                    None => {
                        let new_cap = hash_2_to_1(current_state.capability_root, cap_entry[0]);
                        new_state.capability_root = new_cap;
                    }
                }
                new_state.nonce += 1;
            }
            Effect::RevokeCapability { slot_hash } => {
                // The slot_hash limb[0] shares param slot 0 with cap_entry.
                row[PARAM_BASE + param::CAP_ENTRY] = slot_hash[0];

                // Mirror GrantCapability: cap_root deterministically updates
                // by hashing limb[0] of slot_hash with the previous root.
                let new_cap = hash_2_to_1(current_state.capability_root, slot_hash[0]);
                new_state.capability_root = new_cap;
                new_state.nonce += 1;
            }
            Effect::EmitEvent {
                topic_hash,
                payload_hash,
            } => {
                // Park the low 4 felts of topic_hash into params[0..4] and the
                // low 4 felts of payload_hash into params[4..8]. The AIR's
                // per-row PI-equality constraint pins these to
                // `PI[EMIT_EVENT_TOPIC_HASH][0..4]` and
                // `PI[EMIT_EVENT_PAYLOAD_HASH][0..4]`. The high 4 felts of
                // each hash are bound via `compute_effects_hash` (which
                // absorbs all 16 felts) and via the off-AIR verifier's
                // PI-match loop (which recomputes the full canonical
                // (topic, payload) hashes from the runtime Event). No state
                // column changes — pure side-effect.
                for i in 0..4 {
                    row[PARAM_BASE + i] = topic_hash[i];
                    row[PARAM_BASE + 4 + i] = payload_hash[i];
                }
                new_state.nonce += 1;
            }
            Effect::SetPermissions { permissions_hash } => {
                // 32-byte widening: anchor limb[0] into params[0]; AIR forbids
                // any state column change; nonce ticks. Full 8 limbs bind via
                // compute_effects_hash.
                row[PARAM_BASE + 0] = permissions_hash[0];
                new_state.nonce += 1;
            }
            Effect::SetVerificationKey { vk_hash } => {
                // Same shape as SetPermissions: VK lives off-trace. Anchor limb[0].
                row[PARAM_BASE + 0] = vk_hash[0];
                new_state.nonce += 1;
            }

            Effect::RefreshDelegation => {
                // No params; selector alone records the intent.
                new_state.nonce += 1;
            }
            Effect::IncrementNonce => {
                // Explicit nonce-only runtime effect. The selector distinguishes
                // it from delegation refresh and other passthrough siblings.
                new_state.nonce += 1;
            }
            Effect::RevokeDelegation { child_hash } => {
                // 32-byte widening: anchor limb[0]; full 8 limbs bind via effects_hash.
                row[PARAM_BASE + 0] = child_hash[0];
                new_state.nonce += 1;
            }
            Effect::CreateCell { create_hash } => {
                row[PARAM_BASE + 0] = create_hash[0];
                new_state.nonce += 1;
            }
            Effect::SpawnWithDelegation { spawn_hash } => {
                row[PARAM_BASE + 0] = spawn_hash[0];
                new_state.nonce += 1;
            }

            Effect::ExerciseViaCapability { exercise_hash } => {
                row[PARAM_BASE + 0] = exercise_hash[0];
                new_state.nonce += 1;
            }
            Effect::Introduce { intro_hash } => {
                row[PARAM_BASE + 0] = intro_hash[0];
                new_state.nonce += 1;
            }
            Effect::PipelinedSend { send_hash } => {
                row[PARAM_BASE + 0] = send_hash[0];
                new_state.nonce += 1;
            }

            Effect::BridgeMint {
                value_lo,
                mint_hash,
                value_full: _,
            } => {
                // Mirror NoteSpend: balance credit by value_lo.
                row[PARAM_BASE + 0] = *mint_hash;
                row[PARAM_BASE + 1] = *value_lo;
                let value_u64 = value_lo.as_u32() as u64;
                new_state.balance = new_state.balance.saturating_add(value_u64);
                net_delta += value_u64 as i64;
                new_state.nonce += 1;
            }

            Effect::NoteSpend { nullifier, value } => {
                let (val_lo, val_hi) = split_u64(*value);
                row[PARAM_BASE + param::NULLIFIER] = *nullifier;
                row[PARAM_BASE + param::NOTE_VALUE_LO] = val_lo;
                row[PARAM_BASE + param::NOTE_VALUE_HI] = val_hi;

                new_state.balance = new_state.balance.saturating_add(*value);
                net_delta += *value as i64;
                new_state.nonce += 1;
            }
            Effect::NoteCreate { commitment, value } => {
                let (val_lo, val_hi) = split_u64(*value);
                row[PARAM_BASE + param::NOTE_COMMITMENT] = *commitment;
                row[PARAM_BASE + param::NOTE_VALUE_LO] = val_lo;
                row[PARAM_BASE + param::NOTE_VALUE_HI] = val_hi;

                // BALANCE-NEUTRAL: the note value is hidden in the commitment and is
                // NEVER moved on the transparent ledger (the shielding convention; the
                // executor `apply_note_create` records the commitment and does not touch
                // balance). So the balance is FROZEN and `net_delta` is unchanged. This
                // matches the verified Lean descriptor (`EffectVmEmitNoteCreate`,
                // balance-neutral `gBalLoFreeze`/`CellNoteSpec`). (A prior version
                // subtracted `value`, which diverged from the executor; closed.)
                new_state.nonce += 1;
            }

            Effect::Custom {
                program_vk_hash,
                proof_commitment,
            } => {
                // Write VK hash into params[0..4]: the trace row carries the
                // low 4 felts of the 8-felt VK hash for continuity. The full
                // 8-felt vk_hash is bound through PI[CUSTOM_PROOFS_BASE..+8]
                // (pi v2 widening, `pi::VK_PI_LAYOUT_VERSION == 2`). The
                // executor's PI matching loop enforces equality between the
                // full 32-byte registry key and the PI bytes — the trace's
                // 4-felt slot is metadata only; binding is in PI.
                for i in 0..4 {
                    row[PARAM_BASE + param::CUSTOM_VK_HASH_BASE + i] = program_vk_hash[i];
                }
                // Write proof commitment into params[4..8].
                for i in 0..4 {
                    row[PARAM_BASE + param::CUSTOM_PROOF_COMMIT_BASE + i] = proof_commitment[i];
                }
                // Custom effects do NOT change state (state flows through unchanged).
                // The nonce still increments (it's a real effect, not padding).
                new_state.nonce += 1;
                // No balance change from the Effect VM perspective.
            }

            Effect::MakeSovereign => {
                // Mode flag transitions from 0 to 1.
                new_state.mode_flag = 1;
                new_state.nonce += 1;
            }
            Effect::CreateCellFromFactory {
                factory_vk,
                child_vk_derived,
            } => {
                row[PARAM_BASE + param::FACTORY_VK_HASH] = *factory_vk;
                row[PARAM_BASE + param::CHILD_VK_DERIVED] = *child_vk_derived;
                // Store in aux columns for constraint verification.
                row[AUX_BASE + 6] = *factory_vk;
                row[AUX_BASE + 7] = *child_vk_derived;
                new_state.nonce += 1;
            }

            Effect::Burn {
                target_hash,
                amount_lo,
                amount_full: _,
            } => {
                // Near-miss aliasing closure (#100 follow-up): a dedicated
                // Burn variant. Mirrors NoteCreate's balance-debit shape but
                // (a) uses its own selector (so a verifier can distinguish
                //     Burn from Transfer-dir-1 at the algebraic level), and
                // (b) pins `was_burn_flag == 1` into params[2] so a forged
                //     trace that drops the disclosure flag fails the AIR.
                row[PARAM_BASE + param::BURN_TARGET] = *target_hash;
                row[PARAM_BASE + param::BURN_AMOUNT_LO] = *amount_lo;
                row[PARAM_BASE + param::BURN_WAS_BURN_FLAG] = BabyBear::ONE;

                let amt = amount_lo.as_u32() as u64;
                new_state.balance = new_state.balance.saturating_sub(amt);
                net_delta -= amt as i64;
                new_state.nonce += 1;
            }
            Effect::CellDestroy {
                target_hash,
                death_certificate_hash,
            } => {
                // State passthrough (lifecycle lives off-trace), but the
                // two params bind the cell + death certificate. Distinct
                // from `SetPermissions` (which only binds a single hash)
                // both by selector and by a second-PARAM constraint that
                // a SetPermissions row can't satisfy.
                // 32-byte widening: anchor limb[0] of each into params; the
                // full 8 limbs of both bind via compute_effects_hash.
                row[PARAM_BASE + param::CELL_DESTROY_TARGET] = target_hash[0];
                row[PARAM_BASE + param::CELL_DESTROY_CERT_HASH] = death_certificate_hash[0];
                new_state.nonce += 1;
            }
            Effect::AttenuateCapability {
                cap_slot_hash,
                narrower_commitment,
                phase_b,
            } => {
                row[PARAM_BASE + param::ATTN_CAP_SLOT_HASH] = cap_slot_hash[0];
                row[PARAM_BASE + param::ATTN_NARROWER_COMMITMENT] = narrower_commitment[0];

                match phase_b {
                    // ---- Phase B: GENUINE sorted-tree leaf-update ----
                    // The cap_root advances from the held leaf's authenticated
                    // position to the narrowed leaf, recomputed over the real
                    // Merkle path. `state_before.cap_root` MUST already equal the
                    // witness's `old_root` (the caller seeds the actor's tree
                    // root), and `state_after.cap_root` becomes the recomputed
                    // `new_root`. The p3 AIR's Phase-B gates (membership-open +
                    // submask + AuthRequired lattice + expiry) prove
                    // granted ⊑ held over THIS move. The params[1] narrower
                    // commitment is pinned in-circuit to the granted leaf digest.
                    Some(w) => {
                        // Recompute the new root over the witnessed sibling path.
                        let mut cur = w.granted.digest();
                        for level in 0..w.siblings.len() {
                            let sib = w.siblings[level];
                            cur = if w.directions[level] == 0 {
                                hash_fact(cur, &[sib])
                            } else {
                                hash_fact(sib, &[cur])
                            };
                        }
                        new_state.capability_root = cur;
                    }
                    // ---- Legacy (pre-Phase-B): opaque 2-of-2 fold ----
                    // Algebraically distinct from RevokeCapability's single-hash
                    // advance, but NOT a genuine sorted-tree update and NOT
                    // provable through the audited p3 Phase-B gates.
                    None => {
                        let leaf = hash_2_to_1(cap_slot_hash[0], narrower_commitment[0]);
                        new_state.capability_root = hash_2_to_1(new_state.capability_root, leaf);
                    }
                }
                new_state.nonce += 1;
            }

            // ---- AIR-impl lane #119 ----
            Effect::CellSeal {
                target,
                reason_hash,
            } => {
                // State passthrough: balance/fields/cap_root/reserved unchanged.
                // Both params bind so the proof cannot alias SetPermissions
                // (which only carries one non-zero param).
                // 32-byte widening: anchor limb[0] of each into params; the
                // full 8 limbs of both bind via compute_effects_hash.
                row[PARAM_BASE + param::CELL_SEAL_TARGET] = target[0];
                row[PARAM_BASE + param::CELL_SEAL_REASON_HASH] = reason_hash[0];
                new_state.nonce += 1;
            }
            Effect::CellUnseal { target } => {
                // State passthrough; mirror the single target param (limb[0])
                // into aux so AIR rejects post-generation param swaps. All 8
                // limbs bind via compute_effects_hash.
                row[PARAM_BASE + param::CELL_UNSEAL_TARGET] = target[0];
                row[AUX_BASE] = target[0];
                new_state.nonce += 1;
            }
            Effect::ReceiptArchive {
                target,
                archive_end_height,
                terminal_receipt_hash,
            } => {
                // State passthrough; three params make this algebraically
                // distinct from any 1- or 2-param passthrough sibling. 32-byte
                // widening: anchor limb[0] of target / terminal_receipt_hash;
                // archive_end_height is a scalar height (single felt).
                row[PARAM_BASE + param::RECEIPT_ARCHIVE_TARGET] = target[0];
                row[PARAM_BASE + param::RECEIPT_ARCHIVE_END_HEIGHT] = *archive_end_height;
                row[PARAM_BASE + param::RECEIPT_ARCHIVE_TERMINAL_HASH] = terminal_receipt_hash[0];
                new_state.nonce += 1;
            }
            Effect::Refusal {
                target,
                reason_hash,
            } => {
                // State passthrough; two params — same count as CellSeal —
                // but algebraically distinct because the selector gate is
                // different (`sel::REFUSAL` vs. `sel::CELL_SEAL`). 32-byte
                // widening: anchor limb[0]; full 8 limbs bind via effects_hash.
                row[PARAM_BASE + param::REFUSAL_TARGET] = target[0];
                row[PARAM_BASE + param::REFUSAL_REASON_HASH] = reason_hash[0];
                new_state.nonce += 1;
            }
        }

        // Refresh state commitment.
        new_state.refresh_commitment();

        // Fill state commitment tree intermediate columns (aux[8..10]).
        // These are constrained by the evaluator to match hash_4_to_1 computations
        // on the state_after columns.
        let (inter1, inter2, inter3) = CellState::compute_commitment_intermediates(
            new_state.balance,
            new_state.nonce,
            &new_state.fields,
            new_state.capability_root,
        );
        row[AUX_BASE + aux_off::STATE_INTER1] = inter1;
        row[AUX_BASE + aux_off::STATE_INTER2] = inter2;
        row[AUX_BASE + aux_off::STATE_INTER3] = inter3;

        // Stage 2 (sealing honesty): bit-decompose OLD reserved on every row.
        // The constraint in eval_constraints requires that
        //   Σ b_i * 2^i + mode * 256 == old_reserved
        // hold unconditionally for every row.
        fill_reserved_bits(
            &mut row,
            current_state.sealed_field_mask,
            current_state.mode_flag,
        );

        // W9-RANGECHECK: bit-decompose the new (state_after) balance limbs so
        // the per-row in-circuit range / underflow constraint is satisfied.
        fill_balance_limb_bits(&mut row, new_state.balance);

        // Write state_after.
        let state_after_cols = new_state.to_trace_cols();
        for (i, &val) in state_after_cols.iter().enumerate() {
            row[STATE_AFTER_BASE + i] = val;
        }

        trace.push(row);
        current_state = new_state;
    }

    // Compute effects hash and net delta for public inputs.
    let (effects_hash_lo, effects_hash_hi) = compute_effects_hash(effects);
    let (delta_mag, delta_sign) = if net_delta < 0 {
        ((-net_delta) as u32, 1u32)
    } else {
        (net_delta as u32, 0u32)
    };

    // Fill aux columns on the first row with public-input-bound values.
    // Stage 1: effects_hash is widened to 4 felts; positions 0..1 are bound
    // to AUX[4..5] via boundary constraints (preserves the legacy 2-felt
    // witness binding), positions 2..3 are PI-only (see AUDIT[stage1-pi-only-bound]).
    let effects_hash_4_witness = compute_effects_hash_4(effects);
    if !trace.is_empty() {
        trace[0][AUX_BASE + 2] = BabyBear::new(delta_mag);
        trace[0][AUX_BASE + 3] = BabyBear::new(delta_sign);
        trace[0][AUX_BASE + 4] = effects_hash_4_witness[0];
        trace[0][AUX_BASE + 5] = effects_hash_4_witness[1];

        // Sovereign-witness teeth (SOVEREIGN-WITNESS-AIR-DESIGN.md §3.1):
        // bind the witness's key-commit + sequence into row-0 aux columns.
        // The boundary constraints pin these to the matching PI slots.
        // When IS_SOVEREIGN_CELL == 0, the prover writes zero sentinels
        // and the verifier supplies zero sentinels — the boundary holds
        // trivially.
        trace[0][AUX_BASE + aux_off::WITNESS_KEY_COMMIT_0] =
            context.sovereign_witness_key_commit[0];
        trace[0][AUX_BASE + aux_off::WITNESS_KEY_COMMIT_1] =
            context.sovereign_witness_key_commit[1];
        trace[0][AUX_BASE + aux_off::WITNESS_KEY_COMMIT_2] =
            context.sovereign_witness_key_commit[2];
        trace[0][AUX_BASE + aux_off::WITNESS_KEY_COMMIT_3] =
            context.sovereign_witness_key_commit[3];
        trace[0][AUX_BASE + aux_off::WITNESS_SEQUENCE] =
            BabyBear::new((context.sovereign_witness_sequence & 0x7FFF_FFFF) as u32);

        // γ.2 follow-up (#131/#132): bind the federation id + owner cell id
        // into row-0 aux columns. The boundary constraints pin these to
        // PI[FEDERATION_ID_BASE..+4] / PI[OWNER_CELL_ID_BASE..+4]. The
        // off-AIR verifier recomputes both 4-felt commitments from the
        // trusted federation id + owner cell id, so a proof minted under a
        // different federation (or for a different owner cell) cannot satisfy
        // both the boundary (vs. its own PI) AND the verifier's PI-match loop
        // (vs. the expected federation/owner).
        let fed_id_4 = canonical_id_to_felts_4(&context.federation_id);
        let owner_id_4 = canonical_id_to_felts_4(&context.owner_cell_id);
        trace[0][AUX_BASE + aux_off::FEDERATION_ID_0] = fed_id_4[0];
        trace[0][AUX_BASE + aux_off::FEDERATION_ID_1] = fed_id_4[1];
        trace[0][AUX_BASE + aux_off::FEDERATION_ID_2] = fed_id_4[2];
        trace[0][AUX_BASE + aux_off::FEDERATION_ID_3] = fed_id_4[3];
        trace[0][AUX_BASE + aux_off::OWNER_CELL_ID_0] = owner_id_4[0];
        trace[0][AUX_BASE + aux_off::OWNER_CELL_ID_1] = owner_id_4[1];
        trace[0][AUX_BASE + aux_off::OWNER_CELL_ID_2] = owner_id_4[2];
        trace[0][AUX_BASE + aux_off::OWNER_CELL_ID_3] = owner_id_4[3];
    }
    // Silence unused warnings on the legacy 2-felt return values.
    let _ = (effects_hash_lo, effects_hash_hi);

    // Pad with NoOp rows.
    for _ in n_effects..trace_height {
        let mut row = vec![BabyBear::ZERO; EFFECT_VM_WIDTH];
        row[sel::NOOP] = BabyBear::ONE; // NoOp selector

        // State before = current state (carried from last real row).
        let state_cols = current_state.to_trace_cols();
        for (i, &val) in state_cols.iter().enumerate() {
            row[STATE_BEFORE_BASE + i] = val;
        }
        // State after = same (NoOp doesn't change state).
        for (i, &val) in state_cols.iter().enumerate() {
            row[STATE_AFTER_BASE + i] = val;
        }

        // Fill state commitment tree intermediates for padding rows too.
        let (inter1, inter2, inter3) = CellState::compute_commitment_intermediates(
            current_state.balance,
            current_state.nonce,
            &current_state.fields,
            current_state.capability_root,
        );
        row[AUX_BASE + aux_off::STATE_INTER1] = inter1;
        row[AUX_BASE + aux_off::STATE_INTER2] = inter2;
        row[AUX_BASE + aux_off::STATE_INTER3] = inter3;

        // Stage 2 (sealing honesty): bit-decompose OLD reserved.
        fill_reserved_bits(
            &mut row,
            current_state.sealed_field_mask,
            current_state.mode_flag,
        );

        // W9-RANGECHECK: NoOp pad rows pass balance through unchanged, so
        // state_after.balance == current_state.balance — decompose it.
        fill_balance_limb_bits(&mut row, current_state.balance);

        trace.push(row);
        // current_state stays the same for padding.
    }

    // Stage 2 sum-check (REVIEW[stage1-acc-row0] resolution): populate
    // aux[CUSTOM_COUNT_ACC] as the EXCLUSIVE running sum of `s_custom`
    // indicators. Convention: acc[i] = count of s_custom rows in [0..i)
    // (NOT including row i). With this convention:
    //   - acc[0] == 0 always (pinned by row-0 boundary)
    //   - Transition: next.acc == this.acc + this.s_custom (Group 7)
    //   - acc[last] == total count, pinned to PI[CUSTOM_EFFECT_COUNT] by
    //     the last-row boundary.
    //
    // For the last-row boundary to equal the total custom count, the last
    // row must contribute 0 to the running sum — i.e., the last row must
    // be a NoOp pad row. The pad loop above already pads with NoOp; the
    // `need_extra_pad` check at trace_height computation guarantees a NoOp
    // slot exists when the last real effect is Custom.
    {
        let mut acc: u32 = 0;
        for i in 0..trace.len() {
            // Exclusive sum: record acc BEFORE adding this row's contribution.
            trace[i][AUX_BASE + aux_off::CUSTOM_COUNT_ACC] = BabyBear::new(acc);
            if trace[i][sel::CUSTOM] == BabyBear::ONE {
                acc = acc.saturating_add(1);
            }
        }
    }

    // Collect custom effect entries for public inputs.
    let custom_entries: Vec<_> = effects
        .iter()
        .filter_map(|e| {
            if let Effect::Custom {
                program_vk_hash,
                proof_commitment,
            } = e
            {
                Some((*program_vk_hash, *proof_commitment))
            } else {
                None
            }
        })
        .collect();
    let custom_count = custom_entries.len();
    assert!(
        custom_count <= context.max_custom_effects as usize,
        "Too many custom effects: {} (max {})",
        custom_count,
        context.max_custom_effects
    );
    assert!(
        context.max_custom_effects <= pi::MAX_CUSTOM_EFFECTS_HARD_CAP,
        "max_custom_effects {} exceeds hard cap {}",
        context.max_custom_effects,
        pi::MAX_CUSTOM_EFFECTS_HARD_CAP,
    );

    // Build public inputs in the PI v3 layout (see `pi` module).
    let pi_len = pi::ACTIVE_BASE_COUNT + custom_count * pi::CUSTOM_ENTRY_SIZE;
    let mut public_inputs = vec![BabyBear::ZERO; pi_len];

    // ---- Commitments (4 felts each) ----
    let old_commit_4 = CellState::compute_commitment_4(
        initial_state.balance,
        initial_state.nonce,
        &initial_state.fields,
        initial_state.capability_root,
    );
    let new_commit_4 = CellState::compute_commitment_4(
        current_state.balance,
        current_state.nonce,
        &current_state.fields,
        current_state.capability_root,
    );
    for i in 0..pi::OLD_COMMIT_LEN {
        public_inputs[pi::OLD_COMMIT_BASE + i] = old_commit_4[i];
    }
    for i in 0..pi::NEW_COMMIT_LEN {
        public_inputs[pi::NEW_COMMIT_BASE + i] = new_commit_4[i];
    }

    // ---- Effects hash (4 felts) ----
    let effects_hash_4 = compute_effects_hash_4(effects);
    for i in 0..pi::EFFECTS_HASH_LEN {
        public_inputs[pi::EFFECTS_HASH_BASE + i] = effects_hash_4[i];
    }
    // Suppress unused-variable warning for the legacy 2-felt form.
    let _ = (effects_hash_lo, effects_hash_hi);

    // ---- Balance limbs (P0-1) ----
    let (i_lo, i_hi) = split_u64(initial_state.balance);
    let (f_lo, f_hi) = split_u64(current_state.balance);
    public_inputs[pi::INIT_BAL_LO] = i_lo;
    public_inputs[pi::INIT_BAL_HI] = i_hi;
    public_inputs[pi::FINAL_BAL_LO] = f_lo;
    public_inputs[pi::FINAL_BAL_HI] = f_hi;

    // ---- Net delta (P0-1) ----
    public_inputs[pi::NET_DELTA_MAG] = BabyBear::new(delta_mag);
    public_inputs[pi::NET_DELTA_SIGN] = BabyBear::new(delta_sign);

    // ---- Stage 1 additions ----
    public_inputs[pi::CURRENT_BLOCK_HEIGHT] =
        BabyBear::new((context.current_block_height & 0x7FFF_FFFF) as u32);
    public_inputs[pi::MAX_CUSTOM_EFFECTS] = BabyBear::new(context.max_custom_effects as u32);
    public_inputs[pi::CUSTOM_EFFECT_COUNT] = BabyBear::new(custom_count as u32);
    // RETIRED slot (VERB-LOCKSTEP): ValidateHandoff is gone; the approved-
    // handoffs root stays the context-supplied sentinel until the PI compaction.
    for i in 0..pi::APPROVED_HANDOFFS_LEN {
        public_inputs[pi::APPROVED_HANDOFFS_BASE + i] = context.approved_handoffs_root[i];
    }

    // ---- Stage 7-γ.0a turn-identity bindings ----
    // These four fields are *shared across all per-cell proofs of one turn*.
    // The verifier's cross-proof PI matching loop enforces equality across
    // the bundle; per-proof binding to the canonical Turn::hash and
    // call_forest projection is executor-trusted at γ.0 and becomes
    // algebraic at γ.1.
    for i in 0..pi::TURN_HASH_LEN {
        public_inputs[pi::TURN_HASH_BASE + i] = context.turn_hash[i];
    }
    for i in 0..pi::EFFECTS_HASH_GLOBAL_LEN {
        public_inputs[pi::EFFECTS_HASH_GLOBAL_BASE + i] = context.effects_hash_global[i];
    }
    public_inputs[pi::ACTOR_NONCE] = BabyBear::new((context.actor_nonce & 0x7FFF_FFFF) as u32);
    for i in 0..pi::PREVIOUS_RECEIPT_HASH_LEN {
        public_inputs[pi::PREVIOUS_RECEIPT_HASH_BASE + i] = context.previous_receipt_hash[i];
    }

    // ---- Sovereign-witness teeth (SOVEREIGN-WITNESS-AIR-DESIGN.md) ----
    //
    // Phase 1: PI carries the witness's owning-key commitment, monotonic
    // sequence, and a flag indicating sovereign vs. hosted. The boundary
    // constraint binds the in-trace aux columns to these PI values at
    // row 0. When IS_SOVEREIGN_CELL == 0, the sentinel-zero on both
    // sides makes the constraint trivially satisfied.
    //
    // Phase 2: PI additionally carries the inner transition_proof's
    // VK hash + 4-felt commitment + a presence flag. The off-AIR
    // verifier reads these and recursively verifies the inner STARK.
    for i in 0..pi::SOVEREIGN_WITNESS_KEY_COMMIT_LEN {
        public_inputs[pi::SOVEREIGN_WITNESS_KEY_COMMIT_BASE + i] =
            context.sovereign_witness_key_commit[i];
    }
    public_inputs[pi::SOVEREIGN_WITNESS_SEQUENCE] =
        BabyBear::new((context.sovereign_witness_sequence & 0x7FFF_FFFF) as u32);
    public_inputs[pi::IS_SOVEREIGN_CELL] = if context.is_sovereign_cell {
        BabyBear::ONE
    } else {
        BabyBear::ZERO
    };
    for i in 0..pi::SOVEREIGN_TRANSITION_PROOF_VK_HASH_LEN {
        public_inputs[pi::SOVEREIGN_TRANSITION_PROOF_VK_HASH_BASE + i] =
            context.sovereign_transition_proof_vk_hash[i];
    }
    for i in 0..pi::SOVEREIGN_TRANSITION_PROOF_COMMITMENT_LEN {
        public_inputs[pi::SOVEREIGN_TRANSITION_PROOF_COMMITMENT_BASE + i] =
            context.sovereign_transition_proof_commitment[i];
    }
    public_inputs[pi::HAS_TRANSITION_PROOF] = if context.has_transition_proof {
        BabyBear::ONE
    } else {
        BabyBear::ZERO
    };

    // ---- 30-bit-truncation fix (CAVEAT-LAYER-COVERAGE.md §6.5) ----
    //
    // Each of the three affected effects gets its own 4×16-bit limb slot.
    // We aggregate per-turn: each BridgeMint/BridgeLock/CreateEscrow in
    // the trace contributes its full u64 value via wrap-add (the AIR's
    // per-row balance arithmetic uses the legacy 30-bit-truncated
    // `value_lo`; the new limb slots independently attest to the FULL
    // u64 the executor saw, summed across the trace). A future
    // refinement (per-row limb columns) sits behind a separate
    // PI/aux-column widening.
    //
    // Each limb is < 2^16 by construction (`u64_to_4_limbs_16` masks).
    // The verifier's PI match loop catches any out-of-range limb a
    // malicious prover supplies, and the on-trace effects also bind to
    // the same 4-limb form via the absorbed-into-effects-hash path
    // (see `compute_effects_hash` arms for BridgeMint/BridgeLock/
    // CreateEscrow). Together the two paths give the bit-injective
    // u64 binding that closes §6.5.
    let mint_sum = {
        let mut m: u64 = 0;
        for eff in effects {
            if let Effect::BridgeMint { value_full, .. } = eff {
                m = m.wrapping_add(*value_full);
            }
        }
        m
    };
    let mint_limbs = u64_to_4_limbs_16(mint_sum);
    for i in 0..pi::BRIDGE_MINT_VALUE_LIMBS_LEN {
        public_inputs[pi::BRIDGE_MINT_VALUE_LIMBS_BASE + i] = mint_limbs[i];
    }
    // RETIRED slots (VERB-LOCKSTEP): BridgeLock / CreateEscrow no longer exist,
    // so their limb slots are pinned to the zero sentinel (PI layout unchanged
    // until the descriptor-regeneration lane compacts it).
    for i in 0..pi::BRIDGE_LOCK_VALUE_LIMBS_LEN {
        public_inputs[pi::BRIDGE_LOCK_VALUE_LIMBS_BASE + i] = BabyBear::ZERO;
    }
    for i in 0..pi::CREATE_ESCROW_AMOUNT_LIMBS_LEN {
        public_inputs[pi::CREATE_ESCROW_AMOUNT_LIMBS_BASE + i] = BabyBear::ZERO;
    }
    // Unused context-field shadows (the context-supplied limbs remain in
    // EffectVmContext for forward-compat with a per-effect-instance
    // refinement; today they're recomputed from `effects`).
    let _ = (
        context.bridge_mint_value_limbs,
        context.bridge_lock_value_limbs,
        context.create_escrow_amount_limbs,
    );

    // ---- EmitEvent binding (closes #110) ----
    //
    // Project the canonical (topic_hash, payload_hash) of the first
    // EmitEvent row into PI[EMIT_EVENT_TOPIC_HASH] / PI[EMIT_EVENT_PAYLOAD_HASH]
    // and pin the count. The AIR's per-row PI-equality constraint (gated by
    // `sel::EMIT_EVENT`) pins each emit-event row's params[0..8] to the low
    // 4 felts of each hash; the high 4 felts are bound via
    // `compute_effects_hash` absorption and the off-AIR PI-match loop.
    //
    // Sentinel: when no EmitEvent rows are present, both 8-felt slots stay
    // at the zero default. When multiple emit-event rows are present, the
    // per-row equality constraint forces them all to share the same
    // (topic, payload); the off-AIR verifier rejects bundles whose
    // EMIT_EVENT_COUNT > 1 disagree on hashes (out-of-scope for this lane;
    // documented in the EmitEvent variant docstring).
    let mut emit_event_count: u32 = 0;
    let mut first_emit_topic: Option<[BabyBear; 8]> = None;
    let mut first_emit_payload: Option<[BabyBear; 8]> = None;
    for eff in effects {
        if let Effect::EmitEvent {
            topic_hash,
            payload_hash,
        } = eff
        {
            emit_event_count += 1;
            if first_emit_topic.is_none() {
                first_emit_topic = Some(*topic_hash);
                first_emit_payload = Some(*payload_hash);
            }
        }
    }
    public_inputs[pi::EMIT_EVENT_COUNT] = BabyBear::new(emit_event_count);
    if let (Some(t), Some(p)) = (first_emit_topic, first_emit_payload) {
        for i in 0..pi::EMIT_EVENT_TOPIC_HASH_LEN {
            public_inputs[pi::EMIT_EVENT_TOPIC_HASH_BASE + i] = t[i];
        }
        for i in 0..pi::EMIT_EVENT_PAYLOAD_HASH_LEN {
            public_inputs[pi::EMIT_EVENT_PAYLOAD_HASH_BASE + i] = p[i];
        }
    }

    // ---- D5: NoteSpend nullifier cross-binding (approach A) ----
    //
    // Surface the first NoteSpend row's folded nullifier (param0) into
    // PI[NOTESPEND_NULLIFIER]. The AIR's per-row gated constraint pins every
    // sel::NOTE_SPEND row's param0 to this slot, and the off-AIR verifier
    // reconstructs the same value from the SCHEMA_NOTE_SPEND binding proof's
    // fields[0]. Sentinel: ZERO when no NoteSpend row is present. Multiple
    // NoteSpend rows must share the same folded nullifier (the per-row
    // constraint forces it) — multi-distinct-nullifier proofs need PI
    // extension (deferred, same as EmitEvent's EMIT_EVENT_COUNT > 1 note).
    let first_notespend_nullifier: Option<BabyBear> = effects.iter().find_map(|eff| {
        if let Effect::NoteSpend { nullifier, .. } = eff {
            Some(*nullifier)
        } else {
            None
        }
    });
    if let Some(n) = first_notespend_nullifier {
        public_inputs[pi::NOTESPEND_NULLIFIER] = n;
    }

    // ---- D5b: NoteCreate commitment cross-binding (approach A) ----
    //
    // Surface the first NoteCreate row's folded commitment (param0,
    // NOTE_COMMITMENT) into PI[NOTECREATE_COMMITMENT]. The AIR's per-row gated
    // constraint pins every sel::NOTE_CREATE row's param0 to this slot, and the
    // off-AIR verifier reconstructs the same value from the SCHEMA_NOTE_CREATE
    // binding proof's fields[0]. Sentinel: ZERO when no NoteCreate row is
    // present. Multi-distinct-commitment proofs need PI extension (deferred,
    // same posture as NoteSpend).
    let first_notecreate_commitment: Option<BabyBear> = effects.iter().find_map(|eff| {
        if let Effect::NoteCreate { commitment, .. } = eff {
            Some(*commitment)
        } else {
            None
        }
    });
    if let Some(c) = first_notecreate_commitment {
        public_inputs[pi::NOTECREATE_COMMITMENT] = c;
    }

    // ---- D5c: Burn target cross-binding (approach A) ----
    //
    // Surface the first Burn row's folded target (param0, BURN_TARGET) into
    // PI[BURN_TARGET_PI]. The AIR's per-row gated constraint pins every
    // sel::BURN row's param0 to this slot, and the off-AIR verifier
    // reconstructs the same value from the SCHEMA_BURN binding proof's
    // fields[0] (the ledger-validated burn target). Sentinel: ZERO when no
    // Burn row is present.
    let first_burn_target: Option<BabyBear> = effects.iter().find_map(|eff| {
        if let Effect::Burn { target_hash, .. } = eff {
            Some(*target_hash)
        } else {
            None
        }
    });
    if let Some(t) = first_burn_target {
        public_inputs[pi::BURN_TARGET_PI] = t;
    }

    // ---- γ.2 follow-up (#131/#132): per-cell federation + owner binding ----
    //
    // Surface the 4-felt commitments to the federation id + owner cell id.
    // The row-0 boundary constraints (air.rs) pin these to the matching aux
    // columns, and the off-AIR verifier reconstructs the expected values from
    // the trusted federation id + owner cell id and rejects any disagreement.
    let fed_id_4 = canonical_id_to_felts_4(&context.federation_id);
    let owner_id_4 = canonical_id_to_felts_4(&context.owner_cell_id);
    for i in 0..pi::FEDERATION_ID_LEN {
        public_inputs[pi::FEDERATION_ID_BASE + i] = fed_id_4[i];
    }
    for i in 0..pi::OWNER_CELL_ID_LEN {
        public_inputs[pi::OWNER_CELL_ID_BASE + i] = owner_id_4[i];
    }

    // ---- Slot-caveat manifest (Cav-Codex Block 3) ----
    //
    // Project the cell-program-declared `StateConstraint` set into a
    // fixed-size PI table. The verifier extracts the table and
    // re-evaluates each entry against the state_before / state_after
    // columns; the *executor* is responsible for honestly populating
    // the manifest from `CellProgram::Predicate(...)`. Any tampering
    // with an entry shows up as a PI-match mismatch at receipt
    // verification time (the receipt re-computes the expected PI from
    // the cell's program).
    let cav_count = context.slot_caveat_count.min(pi::MAX_SLOT_CAVEATS as u32);
    public_inputs[pi::SLOT_CAVEAT_COUNT] = BabyBear::new(cav_count);
    for i in 0..(cav_count as usize) {
        let base = pi::SLOT_CAVEAT_MANIFEST_BASE + i * pi::SLOT_CAVEAT_ENTRY_SIZE;
        context.slot_caveat_manifest[i]
            .write_to(&mut public_inputs[base..base + pi::SLOT_CAVEAT_ENTRY_SIZE]);
    }

    // ---- PI v3 tail (THE ROTATION) ----
    //
    // Surface the committed-height commitment limb and the staged caveat
    // tags. The committed-height slot closes the temporal-gate anti-ghost
    // tooth: the prover cannot choose a height because the canonical
    // commitment already absorbed it. The tag slots are staged zero
    // sentinels today; the optimistic-proving / dispute modes (#169) will
    // populate them later.
    public_inputs[pi::v3::COMMITTED_HEIGHT] =
        BabyBear::new((context.committed_height & 0x7FFF_FFFF) as u32);
    public_inputs[pi::v3::RATE_BOUND_TAG] = BabyBear::new(context.rate_bound_tag);
    public_inputs[pi::v3::CHALLENGE_WINDOW_TAG] = BabyBear::new(context.challenge_window_tag);

    // ---- Custom proof entries (PI layout v3: 8 vk + 4 commit per entry) ----
    for (i, (vk_hash, proof_commit)) in custom_entries.iter().enumerate() {
        let base = pi::CUSTOM_PROOFS_BASE + i * pi::CUSTOM_ENTRY_SIZE;
        for j in 0..8 {
            public_inputs[base + j] = vk_hash[j];
        }
        for j in 0..4 {
            public_inputs[base + 8 + j] = proof_commit[j];
        }
    }

    assert_eq!(public_inputs.len(), pi_len);
    (trace, public_inputs)
}

/// Encode a signed balance delta as (magnitude, sign_bit) for public inputs.
pub fn encode_net_delta(delta: i64) -> (BabyBear, BabyBear) {
    if delta < 0 {
        (BabyBear::new((-delta) as u32), BabyBear::ONE)
    } else {
        (BabyBear::new(delta as u32), BabyBear::ZERO)
    }
}

/// Extract the net balance delta from public inputs.
pub fn extract_net_delta(public_inputs: &[BabyBear]) -> Option<i64> {
    if public_inputs.len() < pi::BASE_COUNT {
        return None;
    }
    let magnitude = public_inputs[pi::NET_DELTA_MAG].0 as i64;
    let sign_bit = public_inputs[pi::NET_DELTA_SIGN].0;
    if sign_bit == 1 {
        Some(-magnitude)
    } else {
        Some(magnitude)
    }
}

/// Extract the custom proof commitments from public inputs.
/// Returns a vec of (program_vk_hash, proof_commitment) tuples.
/// Cav-Codex Block 3: extract the (count, entries) slot-caveat
/// manifest from a public-inputs vector. Returns up to
/// `pi::MAX_SLOT_CAVEATS` entries; trailing entries past `count` are
/// dropped. Use [`verify_slot_caveat_manifest`] to re-evaluate each
/// against state_before / state_after.
pub fn extract_slot_caveat_manifest(public_inputs: &[BabyBear]) -> Vec<SlotCaveatEntry> {
    if public_inputs.len() < pi::BASE_COUNT {
        return Vec::new();
    }
    let count = (public_inputs[pi::SLOT_CAVEAT_COUNT].0 as usize).min(pi::MAX_SLOT_CAVEATS);
    let mut result = Vec::with_capacity(count);
    for i in 0..count {
        let base = pi::SLOT_CAVEAT_MANIFEST_BASE + i * pi::SLOT_CAVEAT_ENTRY_SIZE;
        result.push(SlotCaveatEntry {
            type_tag: public_inputs[base].0,
            slot_index: (public_inputs[base + 1].0 & 0xFF) as u8,
            params: [
                public_inputs[base + 2],
                public_inputs[base + 3],
                public_inputs[base + 4],
                public_inputs[base + 5],
            ],
        });
    }
    result
}

pub fn extract_custom_proof_commitments(
    public_inputs: &[BabyBear],
) -> Vec<([BabyBear; 8], [BabyBear; 4])> {
    if public_inputs.len() < pi::BASE_COUNT {
        return Vec::new();
    }
    let custom_count = public_inputs[pi::CUSTOM_EFFECT_COUNT].0 as usize;
    let mut result = Vec::with_capacity(custom_count);
    for i in 0..custom_count {
        let base = pi::CUSTOM_PROOFS_BASE + i * pi::CUSTOM_ENTRY_SIZE;
        if base + pi::CUSTOM_ENTRY_SIZE > public_inputs.len() {
            break;
        }
        // PI layout v2: 8 vk_hash felts + 4 proof_commit felts per entry.
        let vk_hash = [
            public_inputs[base],
            public_inputs[base + 1],
            public_inputs[base + 2],
            public_inputs[base + 3],
            public_inputs[base + 4],
            public_inputs[base + 5],
            public_inputs[base + 6],
            public_inputs[base + 7],
        ];
        let proof_commit = [
            public_inputs[base + 8],
            public_inputs[base + 9],
            public_inputs[base + 10],
            public_inputs[base + 11],
        ];
        result.push((vk_hash, proof_commit));
    }
    result
}
