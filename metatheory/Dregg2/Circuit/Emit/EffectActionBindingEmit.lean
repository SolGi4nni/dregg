/-
# Dregg2.Circuit.Emit.EffectActionBindingEmit — the emit-from-Lean twin of the generalized
effect-action binding AIR (`circuit/src/effect_action_air.rs :: EffectActionAir`).

## What this file IS (the family: `effect_action`)

The hand AIR `EffectActionAir` binds an effect's typed parameters into a STARK proof's public
inputs at full fidelity: a 32-byte field becomes 8 BabyBear limbs (4 bytes each), a u64 amount
becomes 2 limbs (low/high 32 bits), and each such limb is pinned to a row-0 trace column via a
boundary constraint. A transition constraint forces every row to equal row 0, so a malicious
prover cannot stash a different parameter set in a later row. One schema (`Burn`) additionally
witnesses the two-limb u64 subtraction `new_balance == old_balance - amount` with a boolean
borrow, and pins the `was_burn` disclosure flag to `1`.

This file EMITS that AIR's semantics as an `EffectVmDescriptor2` in the IR-v2 grammar, byte-pins
the wire string (`#guard emitVmJson2`), and its Rust gate
(`circuit-prove/tests/effect_action_emit_gate.rs`) decodes the exact string, asserts it equals an
independently hand-built descriptor, and proves+verifies an honest witness through the REAL
`prove_vm_descriptor2` / `verify_vm_descriptor2` — with mutation canaries that each bite a NAMED
constraint (a forged PI limb → the `pi_binding`; a broken subtraction → a Burn `gate`; a stashed
later row → the continuity `window_gate`).

## The constraint → IR2 map (audited against `effect_action_air.rs`)

  * Row-continuity `next[c] - local[c] == 0` for every column `c ∈ [0, width)`
    (`eval_constraints` :301-305, the RLC over all `width` columns)
    ↦ `VmConstraint2.windowGate ⟨Nxt c - Loc c, onTransition := true⟩`, one per column.
  * PI binding `local[c] == public_inputs[c]` on row 0 for every `c ∈ [0, pi_count)`
    (`boundary_constraints` :408-416)
    ↦ `VmConstraint2.base (VmConstraint.piBinding .first c c)`.
  * Domain separation (`air_name() == kind_name`, :278-283) ↦ the descriptor `name` string
    (the exact `kind_name` per schema), so a proof for kind A cannot Fiat-Shamir-replay as B.
  * Wrong-PI-length guard (:402-407) ↦ structural: the descriptor's fixed `piCount`; the IR2
    prover rejects a mismatched public-input vector before constraint eval.
  * Burn low-limb subtraction `new_lo + amt_lo - borrow*2^32 - old_lo == 0` (:349) ↦ a Base gate.
  * Burn high-limb subtraction `new_hi + amt_hi + borrow - old_hi == 0` (:354) ↦ a Base gate.
  * Burn borrow-boolean `borrow*(borrow-1) == 0` (:358) ↦ a Base gate.
  * Burn disclosure pins `was_burn_lo - 1 == 0` (:362) and `was_burn_hi == 0` (:365) ↦ two Base gates.

The borrow witness lives in the prover-supplied AUX column at index `pi_count` (NOT bound to any
PI), exactly as the hand AIR declares (`aux_count = 1`, :132-138). Faithful to the documented
scope, NO bit-decomposition / canonical-u32 range check is emitted on the Burn limbs — the hand
AIR enforces `old_balance >= amount` OFF-AIR in the executor (:368-385); adding a range lookup
here would DIVERGE from the hand AIR, so it is deliberately absent.

## Axiom hygiene
Definitional descriptors + byte-pinned `#guard`s on their wire strings + genuinely-proven,
non-vacuous semantic lemmas (each TRUE and FALSE witnessed). `#assert_axioms` on the lemmas is
`⊆ {}` (pure `omega` / `mul_eq_zero`). NEW file; imports read-only.
-/
import Dregg2.Circuit.DescriptorIR2

namespace Dregg2.Circuit.Emit.EffectActionBindingEmit

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 WindowExpr WindowConstraint emitVmJson2)

set_option autoImplicit false

/-! ## §1 — The generic binding constraints (parametric over every schema).

The family is uniform: a schema of `fieldCount` 32-byte fields and `amountCount` u64 amounts has
`pi_count = fieldCount*8 + amountCount*2` public-input slots, each pinned 1:1 to a row-0 trace
column, over a trace of `width = pi_count + aux` columns tied row-to-row by continuity. -/

/-- The continuity `window_gate` body for column `c`: `Nxt c - Loc c` (the next row equals this
row on that column — the faithful twin of `eval_constraints`' `diff = next[c] - local[c]`). -/
def contWindowBody (c : Nat) : WindowExpr :=
  .add (.nxt c) (.mul (.const (-1)) (.loc c))

/-- The per-column continuity constraint (asserted on the transition domain, as the Rust
`when_transition().assert_zero(next[c] - local[c])`). -/
def contGate (c : Nat) : VmConstraint2 :=
  .windowGate { body := contWindowBody c, onTransition := true }

/-- Row-continuity over ALL `width` columns (incl. the Burn borrow aux). -/
def contGates (width : Nat) : List VmConstraint2 :=
  (List.range width).map contGate

/-- The per-slot PI binding: row-0 column `c` equals public input `c`. -/
def piGate (c : Nat) : VmConstraint2 :=
  .base (.piBinding .first c c)

/-- The full PI-binding boundary (one pin per public-input slot). -/
def piGates (piCount : Nat) : List VmConstraint2 :=
  (List.range piCount).map piGate

/-- **`effectActionDesc name fieldCount amountCount`** — a PURE-BINDING schema descriptor
(`AlgebraicConstraint::None`): `pi_count = fieldCount*8 + amountCount*2` columns, continuity over
all of them, one PI pin per slot, no aux, no extra tables. The `name` is the schema's exact
`kind_name` (Fiat-Shamir domain separation). -/
def effectActionDesc (name : String) (fieldCount amountCount : Nat) : EffectVmDescriptor2 :=
  let pi := fieldCount * 8 + amountCount * 2
  { name        := name
  , traceWidth  := pi
  , piCount     := pi
  , tables      := []
  , constraints := contGates pi ++ piGates pi
  , hashSites   := []
  , ranges      := [] }

/-! ## §2 — The `Burn` schema's algebraic gates (`AlgebraicConstraint::Burn`).

Burn layout (`SCHEMA_BURN`: 1 field, 4 amounts): field limbs 0..8, then
`old_balance` (8,9), `new_balance` (10,11), `amount` (12,13), `was_burn_flag` (14,15); the
prover-supplied borrow aux is column 16 = `pi_count`. -/

def B_OLD_LO : Nat := 8
def B_OLD_HI : Nat := 9
def B_NEW_LO : Nat := 10
def B_NEW_HI : Nat := 11
def B_AMT_LO : Nat := 12
def B_AMT_HI : Nat := 13
def B_WASBURN_LO : Nat := 14
def B_WASBURN_HI : Nat := 15
def B_BORROW : Nat := 16

/-- `2^32` as a field constant (the low-limb borrow weight; reduces mod p at eval — the hand AIR's
`BabyBear::new(0xFFFF_FFFF) + 1`). -/
def TWO_POW_32 : Int := 4294967296

/-- Low-limb subtraction: `new_lo + amt_lo - borrow*2^32 - old_lo == 0`. -/
def cLoBody : EmittedExpr :=
  .add (.add (.var B_NEW_LO) (.var B_AMT_LO))
       (.add (.mul (.const (-TWO_POW_32)) (.var B_BORROW))
             (.mul (.const (-1)) (.var B_OLD_LO)))

/-- High-limb subtraction: `new_hi + amt_hi + borrow - old_hi == 0`. -/
def cHiBody : EmittedExpr :=
  .add (.add (.var B_NEW_HI) (.var B_AMT_HI))
       (.add (.var B_BORROW) (.mul (.const (-1)) (.var B_OLD_HI)))

/-- Boolean borrow: `borrow*(borrow-1) == 0`. -/
def cBorrowBoolBody : EmittedExpr :=
  .mul (.var B_BORROW) (.add (.var B_BORROW) (.const (-1)))

/-- Disclosure pin, low limb: `was_burn_lo - 1 == 0`. -/
def cWasBurnLoBody : EmittedExpr :=
  .add (.var B_WASBURN_LO) (.const (-1))

/-- Disclosure pin, high limb: `was_burn_hi == 0`. -/
def cWasBurnHiBody : EmittedExpr :=
  .var B_WASBURN_HI

/-- The five Burn algebraic Base gates, in `eval_constraints` order. -/
def burnGates : List VmConstraint2 :=
  [ .base (.gate cLoBody)
  , .base (.gate cHiBody)
  , .base (.gate cBorrowBoolBody)
  , .base (.gate cWasBurnLoBody)
  , .base (.gate cWasBurnHiBody) ]

/-! ## §3 — Two concrete descriptors: a pure-binding schema and the algebraic Burn schema. -/

/-- **`revokeCapabilityDesc`** — `SCHEMA_REVOKE_CAPABILITY` (1 field, 1 amount): pure binding,
`pi_count = 10`, width 10. -/
def revokeCapabilityDesc : EffectVmDescriptor2 :=
  effectActionDesc "dregg-effect-revoke-capability-v1" 1 1

/-- **`burnDesc`** — `SCHEMA_BURN` (1 field, 4 amounts + borrow aux): `pi_count = 16`, width 17,
with the five algebraic gates appended past the continuity + PI-binding block. -/
def burnDesc : EffectVmDescriptor2 :=
  { name        := "dregg-effect-burn-v1"
  , traceWidth  := 17
  , piCount     := 16
  , tables      := []
  , constraints := contGates 17 ++ piGates 16 ++ burnGates
  , hashSites   := []
  , ranges      := [] }

/-! ## §4 — The byte-pinned wire goldens (the Rust decoder ingests THESE strings). -/

#guard emitVmJson2 revokeCapabilityDesc == "{\"name\":\"dregg-effect-revoke-capability-v1\",\"ir\":2,\"trace_width\":10,\"public_input_count\":10,\"tables\":[],\"constraints\":[{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":0}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":1}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":2}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":3}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":4},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":4}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":5},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":5}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":6},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":6}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":7},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":7}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":8},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":8}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":9},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":9}}}},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":0,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":1,\"pi_index\":1},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":2,\"pi_index\":2},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":3,\"pi_index\":3},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":4,\"pi_index\":4},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":5,\"pi_index\":5},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":6,\"pi_index\":6},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":7,\"pi_index\":7},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":8,\"pi_index\":8},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":9,\"pi_index\":9}],\"hash_sites\":[],\"ranges\":[]}"

#guard emitVmJson2 burnDesc == "{\"name\":\"dregg-effect-burn-v1\",\"ir\":2,\"trace_width\":17,\"public_input_count\":16,\"tables\":[],\"constraints\":[{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":0}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":1}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":2}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":3}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":4},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":4}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":5},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":5}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":6},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":6}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":7},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":7}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":8},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":8}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":9},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":9}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":10},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":10}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":11},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":11}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":12},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":12}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":13},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":13}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":14},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":14}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":15},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":15}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":16},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":16}}}},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":0,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":1,\"pi_index\":1},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":2,\"pi_index\":2},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":3,\"pi_index\":3},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":4,\"pi_index\":4},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":5,\"pi_index\":5},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":6,\"pi_index\":6},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":7,\"pi_index\":7},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":8,\"pi_index\":8},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":9,\"pi_index\":9},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":10,\"pi_index\":10},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":11,\"pi_index\":11},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":12,\"pi_index\":12},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":13,\"pi_index\":13},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":14,\"pi_index\":14},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":15,\"pi_index\":15},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"var\",\"v\":12}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4294967296},\"r\":{\"t\":\"var\",\"v\":16}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":8}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":11},\"r\":{\"t\":\"var\",\"v\":13}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":9}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":14},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"var\",\"v\":15}}],\"hash_sites\":[],\"ranges\":[]}"

/-! ## §5 — Genuinely-proven, non-vacuous semantic lemmas (the constraint teeth). -/

/-- The continuity body is zero EXACTLY when the two rows agree on column `c` — TRUE when they
chain, FALSE otherwise. The Lean face of the `window_gate` the emit enforces row-for-row. -/
theorem cont_zero_iff (env : VmRowEnv) (c : Nat) :
    (contWindowBody c).eval env = 0 ↔ env.nxt c = env.loc c := by
  simp only [contWindowBody, WindowExpr.eval]
  constructor <;> intro h <;> omega

/-- The low-limb Burn gate is zero EXACTLY when `new_lo + amt_lo = old_lo + borrow*2^32` — the
faithful u64 low-limb subtraction relation the emitted `gate` pins. -/
theorem cLo_zero_iff (a : Assignment) :
    cLoBody.eval a = 0 ↔
      a B_NEW_LO + a B_AMT_LO = a B_OLD_LO + TWO_POW_32 * a B_BORROW := by
  simp only [cLoBody, EmittedExpr.eval, TWO_POW_32]
  constructor <;> intro h <;> omega

/-- The high-limb Burn gate is zero EXACTLY when `new_hi + amt_hi + borrow = old_hi`. -/
theorem cHi_zero_iff (a : Assignment) :
    cHiBody.eval a = 0 ↔
      a B_NEW_HI + a B_AMT_HI + a B_BORROW = a B_OLD_HI := by
  simp only [cHiBody, EmittedExpr.eval]
  constructor <;> intro h <;> omega

/-- The borrow-boolean gate is zero EXACTLY when the borrow is a bit. -/
theorem cBorrowBool_zero_iff (a : Assignment) :
    cBorrowBoolBody.eval a = 0 ↔ a B_BORROW = 0 ∨ a B_BORROW = 1 := by
  simp only [cBorrowBoolBody, EmittedExpr.eval]
  rw [mul_eq_zero]; omega

/-- The disclosure pin is zero EXACTLY when the burn flag is `1`. -/
theorem cWasBurnLo_zero_iff (a : Assignment) :
    cWasBurnLoBody.eval a = 0 ↔ a B_WASBURN_LO = 1 := by
  simp only [cWasBurnLoBody, EmittedExpr.eval]
  constructor <;> intro h <;> omega

/-! Non-vacuity witnesses (each gate ACCEPTS a satisfying row and REJECTS a violating one). -/

-- continuity: agrees ⇒ 0; differs ⇒ ≠ 0.
#guard decide ((contWindowBody 3).eval ⟨fun _ => 5, fun _ => 5, fun _ => 0⟩ = 0)
#guard decide (¬ ((contWindowBody 3).eval ⟨fun _ => 5, fun i => if i = 3 then 9 else 5, fun _ => 0⟩ = 0))

-- low-limb: 600 + 400 = 1000 + 0*2^32 ⇒ 0; 601 + 400 ≠ 1000 ⇒ ≠ 0.
#guard decide (cLoBody.eval (fun i =>
  if i = B_NEW_LO then 600 else if i = B_AMT_LO then 400 else if i = B_OLD_LO then 1000 else 0) = 0)
#guard decide (¬ (cLoBody.eval (fun i =>
  if i = B_NEW_LO then 601 else if i = B_AMT_LO then 400 else if i = B_OLD_LO then 1000 else 0) = 0))

-- borrow-boolean: 1 ⇒ 0; 2 ⇒ ≠ 0.
#guard decide (cBorrowBoolBody.eval (fun i => if i = B_BORROW then 1 else 0) = 0)
#guard decide (¬ (cBorrowBoolBody.eval (fun i => if i = B_BORROW then 2 else 0) = 0))

-- disclosure: flag 1 ⇒ 0; flag 0 ⇒ ≠ 0.
#guard decide (cWasBurnLoBody.eval (fun i => if i = B_WASBURN_LO then 1 else 0) = 0)
#guard decide (¬ (cWasBurnLoBody.eval (fun _ => 0) = 0))

/-! ## §6 — Shape pins. -/

#guard revokeCapabilityDesc.traceWidth == 10
#guard revokeCapabilityDesc.piCount == 10
#guard revokeCapabilityDesc.constraints.length == 20
#guard burnDesc.traceWidth == 17
#guard burnDesc.piCount == 16
#guard burnDesc.constraints.length == 38

#assert_axioms cont_zero_iff
#assert_axioms cLo_zero_iff
#assert_axioms cHi_zero_iff
#assert_axioms cBorrowBool_zero_iff
#assert_axioms cWasBurnLo_zero_iff

end Dregg2.Circuit.Emit.EffectActionBindingEmit
