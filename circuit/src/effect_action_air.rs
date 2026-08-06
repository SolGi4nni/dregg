//! Generalized effect-action binding **schemas + layout constants** (`EffectActionSchema`, `HASH_LIMBS`,
//! `AMOUNT_LIMBS`) — NOT an AIR (the name is historical; 2026-07-16 sweep).
//!
//! ⚠ The line this header used to carry — "This file authors NO constraints in any of the three
//! dialects" — was FALSE. `effect_action_to_descriptor2` (below) BUILDS the constraint list in Rust:
//! it pushes `VmConstraint::PiBinding` and `WindowGateSpec` values directly. Those two families are
//! byte-pinned to their Lean author (`Dregg2.Circuit.Emit.EffectActionBindingEmit.effectActionDesc`,
//! via `EffectActionBindingRefine`), so they do not currently DISAGREE with Lean — but they are
//! Rust-authored, which is the standing law's subject, and the pin is what keeps them honest, not
//! the construction. See the ⚑ on `effect_action_to_descriptor2` for the one place the Rust
//! construction is genuinely WEAKER than its Lean author.
//!
//! Sibling AIR to `bridge_action_witness`. The bridge AIR established the pattern:
//! a 32-byte field becomes 8 BabyBear limbs (4 bytes each), a u64 amount
//! becomes 4 BabyBear limbs of 16 bits each, and each limb is pinned to a
//! trace-row-0 column via a boundary constraint. Transition constraints force
//! every row to equal row 0, so a malicious prover cannot put one set of
//! parameters in row 0 and another in row 1 to slip past the boundary check.
//!
//! `bridge_action_witness` ships a *fixed* schema (nullifier + recipient +
//! destination_federation + amount). This module generalizes the same shape to
//! an arbitrary list of named 32-byte fields and named u64 amounts, so each
//! `Effect` variant can have its parameters bound at full fidelity without
//! authoring a new AIR per variant.
//!
//! # Layout
//!
//! Given a schema with `N` 32-byte fields and `M` u64 amounts, the column /
//! PI layout is:
//!
//! ```text
//! col / PI 0..8           field[0] limbs        (8 × 4-byte BabyBear)
//! col / PI 8..16          field[1] limbs
//! ...
//! col / PI 8N             amount[0] limb 0  (bits  0..16)
//! col / PI 8N + 1         amount[0] limb 1  (bits 16..32)
//! col / PI 8N + 2         amount[0] limb 2  (bits 32..48)
//! col / PI 8N + 3         amount[0] limb 3  (bits 48..64)
//! col / PI 8N + 4         amount[1] limb 0
//! ...
//! ```
//!
//! Total trace width = 8N + 4M. Total PI count = 8N + 4M. Each PI slot
//! corresponds 1:1 with a row-0 boundary constraint on the same column.
//!
//! # ⚑ WHY 16-BIT LIMBS AND NOT 32 (flag day 2026-08-06)
//!
//! A 32-bit limb HAS NO BABYBEAR FELT: `p = 2013265921 < 2^32`, so
//! `BabyBear::new(lo)` reduces and `lo = 0` collides with `lo = p`. A
//! "full-fidelity binding" that collides on the amount is not full
//! fidelity. The same arithmetic showed up as a hard refusal on the
//! descriptor side: the Lean author's Burn borrow gate carried the
//! coefficient `2^32 = 4294967296` and `parse_vm_descriptor2` REFUSED the
//! emitted descriptor — *"constant at byte 3619 does not fit a BabyBear
//! felt"* — so `dregg-effect-burn-v1` could not be read by its own parser.
//!
//! 16 bits is the felt-sized width: a u64 is EXACTLY four limbs (no
//! truncation, no wasted capacity), the borrow weight `2^16 = 65536` is a
//! felt, and every chain gate body is bounded by `2^18` — far inside `p` —
//! so the prover's mod-`p` reading and the ℤ reading of Lean's forcing
//! lemmas COINCIDE. The authority is
//! `Dregg2.Circuit.Emit.EffectActionBindingEmit` (`LIMB_BITS = 16`,
//! `AMOUNT_LIMBS = 4`, `burn_chain_exact_of_modEq`); this file follows it.
//!
//! # Why a generalized AIR rather than one-per-effect?
//!
//! The bridge-action AIR is its own module for historical / dispatch reasons
//! (the bridge wire format references the proof shape by name). For
//! subsequent effects we factor: one AIR with a per-effect *schema*, and
//! per-effect *witness builders* in this same module. Each effect's
//! `prove_X_binding` / `verify_X_binding` pair uses the same AIR with a
//! different schema. The AIR's `air_name` mixes in the effect kind so the
//! Fiat-Shamir transcript domain-separates different effect kinds (a proof
//! generated for effect A cannot replay as effect B even with the same
//! parameter bytes).
//!
//! # What this AIR does and does NOT do
//!
//! Does: full-fidelity binding of typed parameters into the proof's PI.
//! Tampering on any byte of any 32-byte field, or any bit of any u64 amount,
//! produces a different limb encoding which mismatches the boundary
//! constraint, which fails STARK verification.
//!
//! Does NOT: replay protection, ledger-state consistency, cross-effect
//! ordering, or anything specific to an effect's *semantics*. Those live one
//! layer up (executor / Effect-VM / per-effect side proofs).

use crate::field::BabyBear;

/// Number of BabyBear limbs used to represent a 32-byte field.
pub const HASH_LIMBS: usize = 8;

/// Bits per amount limb. 16, because a 32-bit limb has no BabyBear felt
/// (`p = 2013265921 < 2^32`) — see the module header. Lean:
/// `EffectActionBindingEmit.LIMB_BITS`.
pub const AMOUNT_LIMB_BITS: u32 = 16;

/// Number of BabyBear limbs used to represent a u64 amount. `4 * 16 = 64`,
/// exact. Lean: `EffectActionBindingEmit.AMOUNT_LIMBS`.
pub const AMOUNT_LIMBS: usize = 4;

/// Optional schema-specific algebraic-constraint tag. Most schemas are
/// pure binding (no extra arithmetic over the bound limbs). Schemas that
/// need additional algebraic relations declare a tag here and the AIR's
/// `eval_constraints` branches on it.
///
/// Today only `Burn` carries a non-trivial tag — it constrains
/// `old_balance - new_balance == amount` and `old_balance >= amount` on
/// the bound amount columns (AIR-SOUNDNESS-AUDIT.md #75). Adding another
/// algebraic kind is one new variant here plus its eval branch.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AlgebraicConstraint {
    /// No algebraic constraints beyond per-limb boundary pinning.
    None,
    /// `Burn` invariant — see `SCHEMA_BURN`. Amount layout (after the
    /// schema's 32-byte fields):
    ///   amounts[0] = old_balance  (u64 → 4 × 16-bit limbs)
    ///   amounts[1] = new_balance  (u64 → 4 × 16-bit limbs)
    ///   amounts[2] = amount       (u64 → 4 × 16-bit limbs)
    ///   amounts[3] = was_burn_flag (u64; constrained to 1)
    ///
    /// ⚠ NOT ENFORCED BY THE DEPLOYED DESCRIPTOR. This doc used to read
    /// "Constraints enforced on row 0 / row continuity" and list four
    /// gates. `effect_action_to_descriptor2` never reads `schema.algebraic`,
    /// so NONE of them is emitted. The gates below exist and are PROVEN in
    /// Lean (`EffectActionBindingEmit.burnDesc`, five Base gates with
    /// `cLo_zero_iff` / `cHi_zero_iff` / `cBorrowBool_zero_iff` /
    /// `cWasBurnLo_zero_iff`), but nothing routes them into Rust:
    ///   1..3.  new_i + amt_i + b_{i-1} == old_i + b_i * 2^16   (i = 0,1,2)
    ///   4.     new_3 + amt_3 + b_2 == old_3   (NO outgoing borrow — this is
    ///          the `amount <= old_balance` availability tooth)
    ///   5..7.  b_i * (b_i - 1) == 0   (boolean borrow bits)
    ///   8..11. was_burn_flag limb 0 == 1, limbs 1..3 == 0
    ///
    /// What this tag ACTUALLY does today is reserve three aux columns
    /// (`aux_count() == 3`) for the borrow bits that `generate_trace` fills
    /// and NO constraint reads.
    ///
    /// Why that is not (currently) a soundness hole: the deployed verifier
    /// `TurnExecutor::verify_effect_binding_proofs_with_ledger` reconstructs
    /// ALL FOUR amounts from its own authoritative state — `old_balance`
    /// from the ledger snapshot, `new_balance = old_balance - amount`
    /// computed by the executor, `amount` from the runtime `Effect::Burn`,
    /// `was_burn_flag` hard-coded to 1 — rejects any wire PI that disagrees,
    /// and then STARK-verifies against ITS OWN PI vector. The prover has no
    /// freedom over the values these gates would relate. The residual is
    /// that the conservation relation is enforced by executor arithmetic
    /// rather than in-circuit, so any FUTURE consumer that trusts a burn
    /// binding proof WITHOUT that reconstruction inherits nothing.
    Burn,
}

/// A static schema describing what an effect-binding proof commits to.
///
/// Schemas are normally defined as `pub const` values, one per Effect kind,
/// with a unique `kind_name` (used for domain separation in the Fiat-Shamir
/// transcript) and a fixed list of named 32-byte fields and u64 amounts.
#[derive(Clone, Copy, Debug)]
pub struct EffectActionSchema {
    /// Unique name used in `air_name()` for Fiat-Shamir domain separation.
    /// MUST be distinct for each effect kind to prevent cross-effect proof
    /// confusion.
    pub kind_name: &'static str,
    /// Number of 32-byte fields the schema binds.
    pub field_count: usize,
    /// Number of u64 amounts the schema binds.
    pub amount_count: usize,
    /// Optional schema-specific algebraic constraints. Defaults to `None`
    /// for pure-binding schemas; set to `Burn` for the Burn invariant.
    pub algebraic: AlgebraicConstraint,
}

impl EffectActionSchema {
    /// Total trace width / PI count for this schema.
    ///
    /// Schemas with algebraic constraints may reserve additional aux
    /// columns (e.g., `Burn` needs 3 borrow bits). Aux columns are tracked
    /// past the PI surface — the PI count is still `field_count * 8 +
    /// amount_count * AMOUNT_LIMBS`; the trace width is `pi_count + aux_count`.
    pub const fn width(&self) -> usize {
        self.pi_count() + self.aux_count()
    }
    /// PI count (no aux columns).
    pub const fn pi_count(&self) -> usize {
        self.field_count * HASH_LIMBS + self.amount_count * AMOUNT_LIMBS
    }
    /// Schema-specific aux column count (algebraic constraints only).
    pub const fn aux_count(&self) -> usize {
        match self.algebraic {
            AlgebraicConstraint::None => 0,
            // Three borrow bits for the four-limb u64 subtraction chain
            // (the borrow OUT of limb 3 does not exist: the top chain gate
            // carries no outgoing borrow, which IS the `amount <= old` tooth).
            AlgebraicConstraint::Burn => 3,
        }
    }
}

/// Encode a u64 amount as `AMOUNT_LIMBS` BabyBear limbs of `AMOUNT_LIMB_BITS`
/// bits, least-significant first.
///
/// ⚑ INJECTIVE, unlike the 32-bit split this replaced: every limb is
/// `< 2^16 << p`, so `BabyBear::new` never reduces and two distinct u64s
/// never share a limb vector. `encode_amount_is_injective` is the tooth.
///
/// ⚠ NO LONGER the same encoding as `bridge_action_witness::encode_amount`,
/// which is still the 2x32-bit split and carries the same defect. That AIR
/// is a separate family with its own witness/PI surface; it is named here so
/// the divergence is visible rather than discovered.
pub fn encode_amount(amount: u64) -> [BabyBear; AMOUNT_LIMBS] {
    let mut out = [BabyBear::ZERO; AMOUNT_LIMBS];
    for (i, slot) in out.iter_mut().enumerate() {
        *slot = BabyBear::new(((amount >> (i as u32 * AMOUNT_LIMB_BITS)) & 0xFFFF) as u32);
    }
    out
}

/// The borrow bits of the four-limb subtraction `old - amount`: `out[i]` is
/// the borrow OUT of limb `i` into limb `i+1`. Only three exist as witness
/// columns; a borrow out of limb 3 would be an underflow, which the top
/// chain gate structurally forbids (it carries no outgoing borrow term).
fn subtraction_borrows(old: u64, amount: u64) -> [BabyBear; 3] {
    let mask = (1u64 << AMOUNT_LIMB_BITS) - 1;
    let mut borrow = 0u64;
    let mut out = [BabyBear::ZERO; 3];
    for (i, slot) in out.iter_mut().enumerate() {
        let o = (old >> (i as u32 * AMOUNT_LIMB_BITS)) & mask;
        let a = ((amount >> (i as u32 * AMOUNT_LIMB_BITS)) & mask) + borrow;
        borrow = u64::from(o < a);
        *slot = BabyBear::new(borrow as u32);
    }
    out
}

/// A typed witness for one instance of an `EffectActionSchema`.
///
/// The `fields` and `amounts` vectors are in schema order: `fields[i]` is
/// pinned to PI slots `[i * 8, (i + 1) * 8)`; `amounts[j]` is pinned to PI
/// slots `[8 * field_count + j * 4, 8 * field_count + (j + 1) * 4)`.
#[derive(Clone, Debug)]
pub struct EffectActionWitness {
    /// Schema describing the binding.
    pub schema: EffectActionSchema,
    /// 32-byte fields in schema order.
    pub fields: Vec<[u8; 32]>,
    /// u64 amounts in schema order.
    pub amounts: Vec<u64>,
}

impl EffectActionWitness {
    /// Compute the canonical public-input vector this witness commits to.
    pub fn public_inputs(&self) -> Vec<BabyBear> {
        let mut pi = Vec::with_capacity(self.schema.width());
        for f in &self.fields {
            pi.extend_from_slice(&crate::effect_vm::bytes32_to_8_limbs(f));
        }
        for a in &self.amounts {
            pi.extend_from_slice(&encode_amount(*a));
        }
        pi
    }
}

/// The generalized effect-action binding AIR.
///
/// Stateless modulo the `schema`. One real row of typed data, padded to 4 to
/// satisfy STARK power-of-2 trace-length requirements.
pub struct EffectActionAir {
    /// The schema this AIR instance binds to. Carried by value so each
    /// effect kind gets its own (statically declared) schema and the
    /// `air_name()` returns the kind's unique name for Fiat-Shamir.
    pub schema: EffectActionSchema,
}

impl EffectActionAir {
    /// Generate the execution trace and public inputs from a witness.
    pub fn generate_trace(witness: &EffectActionWitness) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
        assert_eq!(
            witness.fields.len(),
            witness.schema.field_count,
            "field count mismatch"
        );
        assert_eq!(
            witness.amounts.len(),
            witness.schema.amount_count,
            "amount count mismatch"
        );
        let width = witness.schema.width();

        // Row 0: the full typed binding.
        let mut row0 = vec![BabyBear::ZERO; width];
        let mut col = 0;
        for f in &witness.fields {
            let limbs = crate::effect_vm::bytes32_to_8_limbs(f);
            for limb in limbs {
                row0[col] = limb;
                col += 1;
            }
        }
        for a in &witness.amounts {
            for limb in encode_amount(*a) {
                row0[col] = limb;
                col += 1;
            }
        }

        // Aux columns (schema-specific algebraic-constraint witnesses).
        match witness.schema.algebraic {
            AlgebraicConstraint::None => {}
            AlgebraicConstraint::Burn => {
                // amounts layout: [old_balance, new_balance, amount, was_burn_flag]
                let borrows = subtraction_borrows(witness.amounts[0], witness.amounts[2]);
                let base = witness.schema.pi_count();
                for (i, b) in borrows.into_iter().enumerate() {
                    row0[base + i] = b;
                }
            }
        }

        // Pad to length 4 (smallest power of 2 ≥ 1).
        let mut trace = Vec::with_capacity(4);
        for _ in 0..4 {
            trace.push(row0.clone());
        }

        let public_inputs = witness.public_inputs();
        (trace, public_inputs)
    }
}

/// Lower an [`EffectActionSchema`] to the IR-v2 [`EffectVmDescriptor2`] so an
/// effect-binding proof can prove/verify through the general descriptor prover
/// (`prove_vm_descriptor2` / `verify_vm_descriptor2`), the same route the deleted
/// hand `EffectActionAir` used to.
///
/// The mapping mirrors [`crate::descriptor_ir2`]'s bridge-action lowering exactly,
/// because [`EffectActionAir::generate_trace`] has the identical shape: ONE typed
/// row (fields → 8-limb, amounts → 2-limb, plus any schema aux columns) repeated
/// to a power-of-two height. So:
///
///   * the `pi_count()` typed slots pin `row0[col c] == pi[c]`
///     (`PiBinding{First}`) — the term-for-term binding of the typed parameters to
///     the public inputs (the same 8/8/2-limb layout `public_inputs` lays down),
///     and
///   * every one of the `width()` columns is held constant across rows
///     (`WindowGate{Nxt(c) − Loc(c), on_transition}`), the continuity glue the
///     "repeat row0" trace satisfies.
///
/// The public inputs the caller supplies are `EffectActionWitness::public_inputs`;
/// the executor reconstructs them from its own view of the effect's typed
/// parameters (and, for `Burn`, the authoritative pre/post ledger balances) and
/// binds them here, so a proof committed to different typed bytes is UNSAT.
///
/// ⚑ **THE LEAN DIVERGENCE — this function never reads `schema.algebraic`.**
/// The Lean author of this same descriptor
/// (`Dregg2.Circuit.Emit.EffectActionBindingEmit.burnDesc`) is
/// `contGates 17 ++ piGates 16 ++ burnGates` = 38 constraints, byte-pinned by
/// `#guard emitVmJson2 burnDesc == …` and carrying five PROVEN Base gates
/// (the two limb equations, borrow booleanity, and the two disclosure pins).
/// The two families below are 33. So for `SCHEMA_BURN` the Rust construction is
/// STRICTLY WEAKER than the Lean object it is supposed to be: the borrow aux
/// column at `pi_count()` rides completely free — no constraint reads it, and it
/// is past the PI surface so nothing compares it either. The house law says these
/// constraints are AUTHORED IN LEAN and Rust only calls the emitted artifact; the
/// standing repair is to route Burn through the Lean-emitted JSON the way
/// `descriptor_by_name` already routes every predicate descriptor
/// (`EmitByName.lean` + `scripts/emit-descriptors.sh`), NOT to hand-write five
/// more Rust gates here.
///
/// Not currently exploitable — see `AlgebraicConstraint::Burn` for why (the
/// executor computes all four amounts itself and verifies against its own PI
/// vector, pinned by `burn_conservation_is_enforced_by_pi_reconstruction`) — but
/// the enforcement lives in executor arithmetic, not in the circuit.
///
/// The mapping is total (no effect-action constraint kind to refuse), so this
/// always returns `Ok`.
pub fn effect_action_to_descriptor2(
    schema: &EffectActionSchema,
) -> Result<crate::descriptor_ir2::EffectVmDescriptor2, String> {
    use crate::descriptor_ir2::{VmConstraint2, WindowExpr, WindowGateSpec};
    use crate::lean_descriptor_air::{VmConstraint, VmRow};

    let width = schema.width();
    let pi_count = schema.pi_count();
    let mut constraints: Vec<VmConstraint2> = Vec::with_capacity(pi_count + width);

    // Family 1 — the `pi_count` typed boundary pins: `row0[col c] == pi[c]`.
    for c in 0..pi_count {
        constraints.push(VmConstraint2::Base(VmConstraint::PiBinding {
            row: VmRow::First,
            col: c,
            pi_index: c,
        }));
    }

    // Family 2 — the `width` continuity pins: `next[c] − local[c] == 0` on the
    // transition domain (every column constant across rows).
    for c in 0..width {
        constraints.push(VmConstraint2::WindowGate(WindowGateSpec {
            body: WindowExpr::Add(
                Box::new(WindowExpr::Nxt(c)),
                Box::new(WindowExpr::Mul(
                    Box::new(WindowExpr::Const(-1)),
                    Box::new(WindowExpr::Loc(c)),
                )),
            ),
            on_transition: true,
        }));
    }

    Ok(crate::descriptor_ir2::EffectVmDescriptor2 {
        name: format!("effect-action-leaf::{}", schema.kind_name),
        trace_width: width,
        public_input_count: pi_count,
        challenges: 0,
        tables: vec![],
        constraints,
        hash_sites: vec![],
        ranges: vec![],
    })
}

// ============================================================================
// Per-Effect schemas
// ============================================================================
//
// Each schema is a `pub const` so the Fiat-Shamir `air_name` is statically
// distinct per effect kind. Adding a new effect's binding is one new const
// here plus a `prove_X_binding` / `verify_X_binding` convenience pair (see
// below) and the executor's projection update.

/// Schema for `GrantCapability` binding:
/// fields = [cap_target_cell (32B), cap_permissions_hash (32B),
///           cap_allowed_effects_hash (32B)]
/// amounts = [cap_slot (u32 → u64)]
pub const SCHEMA_GRANT_CAPABILITY: EffectActionSchema = EffectActionSchema {
    kind_name: "dregg-effect-grant-capability-v1",
    field_count: 3,
    amount_count: 1,
    algebraic: AlgebraicConstraint::None,
};

/// Schema for `RevokeCapability` binding:
/// fields = [cell_id (32B)]
/// amounts = [slot (u32 → u64)]
pub const SCHEMA_REVOKE_CAPABILITY: EffectActionSchema = EffectActionSchema {
    kind_name: "dregg-effect-revoke-capability-v1",
    field_count: 1,
    amount_count: 1,
    algebraic: AlgebraicConstraint::None,
};

/// Schema for `EmitEvent` binding:
/// fields = [topic (32B), data_hash (32B = BLAKE3 of full event.data)]
/// amounts = [data_len (u64)]
pub const SCHEMA_EMIT_EVENT: EffectActionSchema = EffectActionSchema {
    kind_name: "dregg-effect-emit-event-v1",
    field_count: 2,
    amount_count: 1,
    algebraic: AlgebraicConstraint::None,
};

/// Schema for `CreateCell` binding:
/// fields = [public_key (32B), token_id (32B)]
/// amounts = [balance (u64)]
pub const SCHEMA_CREATE_CELL: EffectActionSchema = EffectActionSchema {
    kind_name: "dregg-effect-create-cell-v1",
    field_count: 2,
    amount_count: 1,
    algebraic: AlgebraicConstraint::None,
};

/// Schema for `SetPermissions` binding:
/// fields = [cell_id (32B), permissions_hash (32B = BLAKE3 of postcard(perm))]
/// amounts = []
pub const SCHEMA_SET_PERMISSIONS: EffectActionSchema = EffectActionSchema {
    kind_name: "dregg-effect-set-permissions-v1",
    field_count: 2,
    amount_count: 0,
    algebraic: AlgebraicConstraint::None,
};

/// Schema for `SetVerificationKey` binding:
/// fields = [cell_id (32B), vk_hash (32B; all-zero for None)]
/// amounts = []
pub const SCHEMA_SET_VERIFICATION_KEY: EffectActionSchema = EffectActionSchema {
    kind_name: "dregg-effect-set-verification-key-v1",
    field_count: 2,
    amount_count: 0,
    algebraic: AlgebraicConstraint::None,
};

/// Schema for `Introduce` binding:
/// fields = [introducer (32B), recipient (32B), target (32B),
///           permissions_vk_hash (32B; zero for non-Custom)]
/// amounts = [permissions_discriminant (u64; 0..=5)]
pub const SCHEMA_INTRODUCE: EffectActionSchema = EffectActionSchema {
    kind_name: "dregg-effect-introduce-v1",
    field_count: 4,
    amount_count: 1,
    algebraic: AlgebraicConstraint::None,
};

/// Schema for `RevokeDelegation` binding:
/// fields = [child (32B)]
/// amounts = []
pub const SCHEMA_REVOKE_DELEGATION: EffectActionSchema = EffectActionSchema {
    kind_name: "dregg-effect-revoke-delegation-v1",
    field_count: 1,
    amount_count: 0,
    algebraic: AlgebraicConstraint::None,
};

/// Schema for `SpawnWithDelegation` binding:
/// fields = [child_public_key (32B), child_token_id (32B)]
/// amounts = [max_staleness (u64)]
pub const SCHEMA_SPAWN_WITH_DELEGATION: EffectActionSchema = EffectActionSchema {
    kind_name: "dregg-effect-spawn-with-delegation-v1",
    field_count: 2,
    amount_count: 1,
    algebraic: AlgebraicConstraint::None,
};

/// Schema for `ExerciseViaCapability` binding:
/// fields = [inner_effects_hash (32B = BLAKE3 of inner_effects[*].hash() chain)]
/// amounts = [cap_slot (u32 → u64), inner_effects_len (u64)]
///
/// Note: inner_effects_len is bound explicitly so a prover cannot
/// substitute a different-length effect chain with a collision-prefix
/// hash. Combined with the chained hash, this gives full integrity over
/// the inner effects list.
pub const SCHEMA_EXERCISE_VIA_CAPABILITY: EffectActionSchema = EffectActionSchema {
    kind_name: "dregg-effect-exercise-via-capability-v1",
    field_count: 1,
    amount_count: 2,
    algebraic: AlgebraicConstraint::None,
};

/// Schema for `PipelinedSend` binding:
/// fields = [source_turn (32B), action_hash (32B)]
/// amounts = [output_slot (u64)]
pub const SCHEMA_PIPELINED_SEND: EffectActionSchema = EffectActionSchema {
    kind_name: "dregg-effect-pipelined-send-v1",
    field_count: 2,
    amount_count: 1,
    algebraic: AlgebraicConstraint::None,
};

/// Schema for `CreateCellFromFactory` binding:
/// fields = [factory_vk (32B), owner_pubkey (32B), token_id (32B),
///           params_hash (32B = BLAKE3 of postcard(params))]
/// amounts = []
pub const SCHEMA_CREATE_CELL_FROM_FACTORY: EffectActionSchema = EffectActionSchema {
    kind_name: "dregg-effect-create-cell-from-factory-v1",
    field_count: 4,
    amount_count: 0,
    algebraic: AlgebraicConstraint::None,
};

/// Schema for `NoteSpend` binding (full-fidelity proof-to-action binding):
///
/// fields = [nullifier (32B), note_tree_root (32B),
///           asset_type_commitment (32B; BLAKE3 of asset_type.to_le_bytes()
///                                  for backward compat — see note below),
///           value_commitment (32B; Pedersen 32B if Some, ZERO if None)]
/// amounts = [value (u64), asset_type (u64)]
///
/// # Relationship with the deprecated `note_spending_witness`
///
/// `circuit/src/note_spending_witness.rs` is the legacy AIR that proves
/// knowledge of the spending key, Merkle membership of the note, and
/// pins `nullifier`/`merkle_root`/`value`/`asset_type` as **single
/// BabyBear felts each** (Poseidon2-compressed). That AIR's PIs are
/// one-way digests — a verifier cannot algebraically attribute a spend
/// to a specific 32-byte nullifier; it can only check a felt-sized digest.
///
/// `SCHEMA_NOTE_SPEND` here is the **canonical full-fidelity binding**:
/// each 32-byte field is 8 × 4-byte BabyBear limbs (~248-bit binding),
/// each u64 amount is 2 × 32-bit limbs (full 64-bit binding). The
/// `value_commitment` slot is ZERO when the runtime variant carries
/// `None` (cleartext-value path) and the Pedersen point's compressed
/// 32 bytes when the runtime variant carries `Some` (committed path).
///
/// **Recommendation:** deprecate `note_spending_witness` in favor of the
/// schema-based generalized AIR. The schema-based binding gives every
/// callsite 248-bit-strength on every 32-byte field plus full 64-bit
/// amount binding, replacing the felt-sized PIs of the legacy AIR.
/// The Merkle / spending-key half of the legacy AIR continues to live
/// in the spend proof (or its replacement); only the binding role
/// migrates here.
pub const SCHEMA_NOTE_SPEND: EffectActionSchema = EffectActionSchema {
    kind_name: "dregg-effect-note-spend-v1",
    field_count: 4,
    amount_count: 2,
    algebraic: AlgebraicConstraint::None,
};

/// Schema for `NoteCreate` binding (full-fidelity proof-to-action binding):
///
/// fields = [note_commitment (32B),
///           asset_type_commitment (32B; see NoteSpend note),
///           value_commitment (32B; Pedersen 32B if Some, ZERO if None),
///           range_proof_hash (32B; BLAKE3 of range_proof bytes if Some,
///                             ZERO if None)]
/// amounts = [value (u64), asset_type (u64)]
///
/// # Relationship with the deprecated `note_spending_witness`
///
/// Same story as `SCHEMA_NOTE_SPEND` — the legacy `note_spending_witness`
/// proves spend-side semantics with felt-sized PIs; this schema is the
/// **canonical full-fidelity binding** for the create-side action
/// parameters. Recommend deprecating the legacy AIR in favor of the
/// schema-based generalized AIR.
pub const SCHEMA_NOTE_CREATE: EffectActionSchema = EffectActionSchema {
    kind_name: "dregg-effect-note-create-v1",
    field_count: 4,
    amount_count: 2,
    algebraic: AlgebraicConstraint::None,
};

/// Schema for `Burn` binding (AIR-SOUNDNESS-AUDIT.md #75).
///
/// Pre-#75 the Burn effect was structural-only: the executor enforced
/// `old_balance >= amount` and decremented the balance in
/// `executor/apply.rs::Effect::Burn`, but no AIR algebraic constraint
/// witnessed the arithmetic. A malicious executor producing a forged
/// receipt could claim any `(old, new, amount)` triple consistent with
/// the recorded balance commitments, since the proof did not pin the
/// arithmetic relation.
///
/// fields = [target_cell_id (32B)]
/// amounts = [old_balance (u64), new_balance (u64), amount (u64),
///            was_burn_flag (u64; constrained to 1)]
///
/// ⚠ Algebraic constraints: DECLARED HERE, NOT EMITTED. This doc used to
/// assert that the AIR enforces `new_balance == old_balance - amount`, the
/// disclosure pin `was_burn_flag == 1`, and borrow booleanity. It does not —
/// `effect_action_to_descriptor2` ignores `algebraic` entirely, so the
/// deployed burn descriptor is 33 constraints (16 PI pins + 17 continuity)
/// against the Lean author's 38. See `AlgebraicConstraint::Burn` for the
/// full statement, including why this is not currently exploitable (the
/// executor reconstructs every one of these amounts itself and verifies
/// against its own PI vector) and what the residual actually is.
///
/// The `old_balance >= amount` predicate is enforced by the executor's
/// `InsufficientBalance` runtime check.
///
/// `slot` is not bound here because Silver-Vision rejects any slot other
/// than the canonical balance slot (`0`); see the executor's apply check.
/// Once Burn is extended to multi-slot, add a `slot (u64)` amount to the
/// schema.
pub const SCHEMA_BURN: EffectActionSchema = EffectActionSchema {
    kind_name: "dregg-effect-burn-v1",
    field_count: 1,
    amount_count: 4,
    algebraic: AlgebraicConstraint::Burn,
};

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn hash_limbs_deterministic() {
        let a = crate::effect_vm::bytes32_to_8_limbs(&[0x42; 32]);
        let b = crate::effect_vm::bytes32_to_8_limbs(&[0x42; 32]);
        assert_eq!(a, b);
    }

    #[test]
    fn hash_limbs_distinguish_distinct_bytes() {
        let a = crate::effect_vm::bytes32_to_8_limbs(&[0x42; 32]);
        let mut bytes = [0x42u8; 32];
        bytes[0] = 0x43;
        let b = crate::effect_vm::bytes32_to_8_limbs(&bytes);
        assert_ne!(a, b);
    }

    #[test]
    fn encode_amount_full_64_bits() {
        let l = encode_amount(0xDEAD_BEEF_CAFE_F00D);
        assert_eq!(l[0], BabyBear::new(0xF00D));
        assert_eq!(l[1], BabyBear::new(0xCAFE));
        assert_eq!(l[2], BabyBear::new(0xBEEF));
        assert_eq!(l[3], BabyBear::new(0xDEAD));
    }

    /// ⚑ THE TOOTH THE 32-BIT SPLIT COULD NOT PASS. Every 16-bit limb is
    /// `< 2^16 < p`, so `BabyBear::new` never reduces and the encoding is
    /// injective on u64. Under the retired 2x32-bit split, `lo = 0` and
    /// `lo = p = 2013265921` were the SAME cell — this names that pair.
    #[test]
    fn encode_amount_is_injective() {
        assert_ne!(encode_amount(0), encode_amount(2_013_265_921));
        for a in [
            0u64,
            1,
            0xFFFF,
            0x1_0000,
            2_013_265_921,
            u64::MAX,
            0xDEAD_BEEF_CAFE_F00D,
        ] {
            for (i, limb) in encode_amount(a).into_iter().enumerate() {
                let raw = ((a >> (i as u32 * AMOUNT_LIMB_BITS)) & 0xFFFF) as u32;
                assert_eq!(limb.as_u32(), raw, "limb {i} of {a:#x} was reduced mod p");
            }
        }
    }

    /// The borrow chain the Lean gates read.
    #[test]
    fn subtraction_borrows_match_the_chain() {
        let bits = |b: [BabyBear; 3]| [b[0].as_u32(), b[1].as_u32(), b[2].as_u32()];
        // 65536 - 1: the low limb underflows, so b_0 = 1 and the rest are 0.
        assert_eq!(bits(subtraction_borrows(65_536, 1)), [1, 0, 0]);
        // 1000 - 400: no limb underflows.
        assert_eq!(bits(subtraction_borrows(1000, 400)), [0, 0, 0]);
        // 2^48 - 1: the borrow propagates through all three bits.
        assert_eq!(bits(subtraction_borrows(1u64 << 48, 1)), [1, 1, 1]);
    }

    #[test]
    fn schema_width_arithmetic() {
        assert_eq!(SCHEMA_GRANT_CAPABILITY.width(), 3 * 8 + 1 * 4);
        assert_eq!(SCHEMA_REVOKE_CAPABILITY.width(), 8 + 4);
        assert_eq!(SCHEMA_EMIT_EVENT.width(), 16 + 4);
        assert_eq!(SCHEMA_CREATE_CELL.width(), 16 + 4);
        assert_eq!(SCHEMA_SET_PERMISSIONS.width(), 16);
        assert_eq!(SCHEMA_SET_VERIFICATION_KEY.width(), 16);
        assert_eq!(SCHEMA_INTRODUCE.width(), 32 + 4);
    }

    #[test]
    fn burn_schema_shape_v1() {
        // Schema shape sanity: 1 field × 8 + 4 amounts × 4 = 24 PI felts.
        assert_eq!(SCHEMA_BURN.field_count, 1);
        assert_eq!(SCHEMA_BURN.amount_count, 4);
        assert_eq!(SCHEMA_BURN.pi_count(), 8 + 16);
        // Three aux columns for the four-limb borrow chain.
        assert_eq!(SCHEMA_BURN.aux_count(), 3);
        assert_eq!(SCHEMA_BURN.width(), 27);
        assert_eq!(SCHEMA_BURN.algebraic, AlgebraicConstraint::Burn);
    }
}
