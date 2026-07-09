/-
# Dregg2.Circuit.Emit.PredicatesLeEmit — the emitted `LessThanOrEqual(value, threshold)`
arithmetic-predicate descriptor (`dregg-predicate-arith-le::threshold-v1`).

## What this file IS

The `≤` sibling of `PredicatesArithmeticEmit.predicateGeDesc`. The hand-STARK deletion left the
comparison ops `Lte`/`Gt`/`Lt`/`Neq`/`InRange` with NO emitted descriptor (fail-closed); only `Gte`
was emitted. This file emits the `≤` case by the SAME one-tooth mechanism as `≥`, with the DIFF
subtraction swapped:

  * `≥` (`predicateGeDesc`):  `DIFF = value − threshold ∈ [0, 2^29)`  (`value ≥ threshold`);
  * `≤` (here):              `DIFF = threshold − value ∈ [0, 2^29)`  (`value ≤ threshold`).

The five teeth are the arithmetic-comparison core, carried one-for-one from the `≥` template:

| tooth | constraint                                                    |
|-------|---------------------------------------------------------------|
| C1    | `.piBinding first THRESHOLD PI_THRESHOLD`  (public threshold)  |
| C2    | `.piBinding first FACT_COMMITMENT PI_FACT_COMMITMENT`          |
| C3    | `.gate (SLOT_A − INPUT)`  (bare-Input slot identity)          |
| C5    | `.gate (DIFF − THRESHOLD + SLOT_A)`  (`DIFF = threshold−value`) |
| C6    | `.lookup ⟨range, [DIFF]⟩`  (`DIFF ∈ [0, 2^29)`)               |

The range lookup is the LOAD-BEARING tooth: `DIFF = threshold − value ∈ [0, 2^29)` iff
`value ≤ threshold` with a bounded gap (a `value > threshold` wraps `DIFF` to
`p − (value − threshold)`, far outside the interval — UNSAT). The Poseidon2 value↔fact weld the
`≥` descriptor also carries is an ORTHOGONAL hardening (held-forgery #2); it is a uniform follow-up
across the whole comparison family and is NOT part of the comparison mechanism, so this leaner
descriptor pins `fact_commitment` as the hand-AIR pass-through public input (C2) exactly as the
pre-weld `≥` AIR did.

## Axiom hygiene
Definitional descriptor + byte-pinned `#guard` + non-vacuous per-gate lemmas (`omega`).
`#assert_axioms` ⊆ {} on the gate lemmas. NEW file; imports read-only.
-/
import Dregg2.Circuit.DescriptorIR2

namespace Dregg2.Circuit.Emit.PredicatesLeEmit

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Lookup TableId rangeTableDef emitVmJson2 rangeRows
   range_row_mem_iff)

set_option autoImplicit false

/-! ## §1 — trace column layout (one logical row). -/

/-- The private input value being compared. -/
def INPUT : Nat := 0
/-- The compiled expression-A result slot; C3 forces `SLOT_A = INPUT`. -/
def SLOT_A : Nat := 1
/-- The public comparison target, PI-bound to `PI_THRESHOLD`. -/
def THRESHOLD : Nat := 2
/-- The comparison difference `threshold − value`; range-proved into `[0, 2^29)`. -/
def DIFF : Nat := 3
/-- The public fact commitment, PI-bound to `PI_FACT_COMMITMENT`. -/
def FACT_COMMITMENT : Nat := 4

/-- Base-trace width (the diff limbs are appended by the assembler, not counted here). -/
def PRED_WIDTH : Nat := 5

/-- Public-input slot for the threshold. -/
def PI_THRESHOLD : Nat := 0
/-- Public-input slot for the fact commitment. -/
def PI_FACT_COMMITMENT : Nat := 1

/-- The effective diff range width (`[0, 2^29)`). -/
def DIFF_BITS : Nat := 29

/-! ## §2 — the constraint list. -/

/-- **C1** — `threshold` matches the public input. -/
def c1ThresholdPin : VmConstraint2 := .base (.piBinding VmRow.first THRESHOLD PI_THRESHOLD)

/-- **C2** — `fact_commitment` matches the public input. -/
def c2FactPin : VmConstraint2 := .base (.piBinding VmRow.first FACT_COMMITMENT PI_FACT_COMMITMENT)

/-- The C3 slot-identity body `SLOT_A − INPUT`. -/
def c3Body : EmittedExpr := .add (.var SLOT_A) (.mul (.const (-1)) (.var INPUT))

/-- **C3** — the slot-identity gate. -/
def c3SlotGate : VmConstraint2 := .base (.gate c3Body)

/-- The C5 diff-computation body `DIFF − THRESHOLD + SLOT_A` (`DIFF = THRESHOLD − SLOT_A`, i.e.
`DIFF = threshold − value` — the `≤` swap of the `≥` template's `DIFF = value − threshold`). -/
def c5Body : EmittedExpr :=
  .add (.add (.var DIFF) (.mul (.const (-1)) (.var THRESHOLD))) (.var SLOT_A)

/-- **C5** — the diff-computation gate. -/
def c5DiffGate : VmConstraint2 := .base (.gate c5Body)

/-- **C6** — the diff range proof: `DIFF ∈ [0, 2^29)`. -/
def c6RangeLookup : VmConstraint2 := .lookup ⟨TableId.range, [.var DIFF]⟩

/-- **`predicateLeDesc`** — the arithmetic `LessThanOrEqual(value, threshold)` descriptor. -/
def predicateLeDesc : EffectVmDescriptor2 :=
  { name        := "dregg-predicate-arith-le::threshold-v1"
  , traceWidth  := PRED_WIDTH
  , piCount     := 2
  , tables      := [rangeTableDef DIFF_BITS]
  , constraints := [c1ThresholdPin, c2FactPin, c3SlotGate, c5DiffGate, c6RangeLookup]
  , hashSites   := []
  , ranges      := [] }

/-! ## §3 — the byte-pinned wire golden. -/

#guard emitVmJson2 predicateLeDesc ==
  "{\"name\":\"dregg-predicate-arith-le::threshold-v1\",\"ir\":2,\"trace_width\":5,\"public_input_count\":2,\"tables\":[{\"id\":2,\"name\":\"range\",\"arity\":1,\"sem\":\"range\",\"bits\":29}],\"constraints\":[{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":2,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":4,\"pi_index\":1},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":0}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":2}}},\"r\":{\"t\":\"var\",\"v\":1}}},{\"t\":\"lookup\",\"table\":2,\"tuple\":[{\"t\":\"var\",\"v\":3}]}],\"hash_sites\":[],\"ranges\":[]}"

/-! ## §4 — non-vacuous per-gate lemmas. -/

/-- The C3 gate body is zero iff `SLOT_A = INPUT`. -/
theorem c3_body_zero_iff (a : Assignment) :
    c3Body.eval a = 0 ↔ a SLOT_A = a INPUT := by
  simp only [c3Body, EmittedExpr.eval]
  constructor <;> intro h <;> omega

/-- The C5 gate body is zero iff `DIFF = THRESHOLD − SLOT_A` (the `≤` diff identity). -/
theorem c5_body_zero_iff (a : Assignment) :
    c5Body.eval a = 0 ↔ a DIFF = a THRESHOLD - a SLOT_A := by
  simp only [c5Body, EmittedExpr.eval]
  constructor <;> intro h <;> omega

-- Non-vacuity witnesses.
#guard decide (c3Body.eval (fun i => if i = SLOT_A ∨ i = INPUT then 7 else 0) = 0)
#guard decide (¬ (c3Body.eval (fun i => if i = SLOT_A then 7 else 0) = 0))
#guard decide (c5Body.eval (fun i => if i = DIFF then 60 else if i = THRESHOLD then 100 else if i = SLOT_A then 40 else 0) = 0)
#guard decide (¬ (c5Body.eval (fun i => if i = DIFF then 59 else if i = THRESHOLD then 100 else if i = SLOT_A then 40 else 0) = 0))

-- The range tooth, in Lean (via `range_row_mem_iff`, NEVER `decide` over the table).
example : ([60] : List ℤ) ∈ rangeRows DIFF_BITS := by
  rw [range_row_mem_iff]; norm_num [DIFF_BITS]
example : ¬ (([2 ^ 29] : List ℤ) ∈ rangeRows DIFF_BITS) := by
  rw [range_row_mem_iff]; norm_num [DIFF_BITS]

-- Shape pins.
#guard predicateLeDesc.traceWidth == PRED_WIDTH
#guard predicateLeDesc.piCount == 2
#guard predicateLeDesc.constraints.length == 5
#guard predicateLeDesc.tables.length == 1

#assert_axioms c3_body_zero_iff
#assert_axioms c5_body_zero_iff

end Dregg2.Circuit.Emit.PredicatesLeEmit
