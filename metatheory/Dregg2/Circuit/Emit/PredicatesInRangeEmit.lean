/-
# Dregg2.Circuit.Emit.PredicatesInRangeEmit — the emitted `InRange(lo ≤ value ≤ hi)`
arithmetic-predicate descriptor (`dregg-predicate-arith-inrange::bounds-v1`).

## What this file IS

The two-sided membership case: `lo ≤ value ≤ hi`, carried by TWO range checks — one for each side.
Public inputs are `[lo, hi, fact_commitment]` (three PIs, vs the one-sided ops' two):

  * `DIFF_LO = value − lo ∈ [0, 2^29)`  (`value ≥ lo`);
  * `DIFF_HI = hi − value ∈ [0, 2^29)`  (`value ≤ hi`).

| tooth  | constraint                                                       |
|--------|------------------------------------------------------------------|
| C1lo   | `.piBinding first LO PI_LO`                                       |
| C1hi   | `.piBinding first HI PI_HI`                                       |
| C2     | `.piBinding first FACT_COMMITMENT PI_FACT_COMMITMENT`             |
| C3     | `.gate (SLOT_A − INPUT)`  (bare-Input slot identity)             |
| C5lo   | `.gate (DIFF_LO − SLOT_A + LO)`  (`DIFF_LO = value − lo`)        |
| C5hi   | `.gate (DIFF_HI − HI + SLOT_A)`  (`DIFF_HI = hi − value`)        |
| C6lo   | `.lookup ⟨range, [DIFF_LO]⟩`                                      |
| C6hi   | `.lookup ⟨range, [DIFF_HI]⟩`                                      |

Both range lookups are load-bearing: a `value < lo` wraps `DIFF_LO` below zero, a `value > hi` wraps
`DIFF_HI` below zero — either UNSAT. Fact-commitment is the pass-through PI (C2).

`#assert_axioms` ⊆ {} on the gate lemmas. NEW file; imports read-only.
-/
import Dregg2.Circuit.DescriptorIR2

namespace Dregg2.Circuit.Emit.PredicatesInRangeEmit

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Lookup TableId rangeTableDef emitVmJson2 rangeRows
   range_row_mem_iff)

set_option autoImplicit false

def INPUT : Nat := 0
def SLOT_A : Nat := 1
def LO : Nat := 2
def HI : Nat := 3
def DIFF_LO : Nat := 4
def DIFF_HI : Nat := 5
def FACT_COMMITMENT : Nat := 6
def PRED_WIDTH : Nat := 7
def PI_LO : Nat := 0
def PI_HI : Nat := 1
def PI_FACT_COMMITMENT : Nat := 2
def DIFF_BITS : Nat := 29

def c1LoPin : VmConstraint2 := .base (.piBinding VmRow.first LO PI_LO)
def c1HiPin : VmConstraint2 := .base (.piBinding VmRow.first HI PI_HI)
def c2FactPin : VmConstraint2 := .base (.piBinding VmRow.first FACT_COMMITMENT PI_FACT_COMMITMENT)

def c3Body : EmittedExpr := .add (.var SLOT_A) (.mul (.const (-1)) (.var INPUT))
def c3SlotGate : VmConstraint2 := .base (.gate c3Body)

/-- `DIFF_LO = SLOT_A − LO` (`value − lo`). Body `DIFF_LO − SLOT_A + LO`. -/
def c5LoBody : EmittedExpr :=
  .add (.add (.var DIFF_LO) (.mul (.const (-1)) (.var SLOT_A))) (.var LO)
def c5LoGate : VmConstraint2 := .base (.gate c5LoBody)

/-- `DIFF_HI = HI − SLOT_A` (`hi − value`). Body `DIFF_HI − HI + SLOT_A`. -/
def c5HiBody : EmittedExpr :=
  .add (.add (.var DIFF_HI) (.mul (.const (-1)) (.var HI))) (.var SLOT_A)
def c5HiGate : VmConstraint2 := .base (.gate c5HiBody)

def c6LoRange : VmConstraint2 := .lookup ⟨TableId.range, [.var DIFF_LO]⟩
def c6HiRange : VmConstraint2 := .lookup ⟨TableId.range, [.var DIFF_HI]⟩

/-- **`predicateInRangeDesc`** — the arithmetic `InRange(lo ≤ value ≤ hi)` descriptor. 3 PIs. -/
def predicateInRangeDesc : EffectVmDescriptor2 :=
  { name        := "dregg-predicate-arith-inrange::bounds-v1"
  , traceWidth  := PRED_WIDTH
  , piCount     := 3
  , tables      := [rangeTableDef DIFF_BITS]
  , constraints := [c1LoPin, c1HiPin, c2FactPin, c3SlotGate, c5LoGate, c5HiGate, c6LoRange, c6HiRange]
  , hashSites   := []
  , ranges      := [] }

#guard emitVmJson2 predicateInRangeDesc ==
  "{\"name\":\"dregg-predicate-arith-inrange::bounds-v1\",\"ir\":2,\"trace_width\":7,\"public_input_count\":3,\"tables\":[{\"id\":2,\"name\":\"range\",\"arity\":1,\"sem\":\"range\",\"bits\":29}],\"constraints\":[{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":2,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":3,\"pi_index\":1},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":6,\"pi_index\":2},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":0}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":1}}},\"r\":{\"t\":\"var\",\"v\":2}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":3}}},\"r\":{\"t\":\"var\",\"v\":1}}},{\"t\":\"lookup\",\"table\":2,\"tuple\":[{\"t\":\"var\",\"v\":4}]},{\"t\":\"lookup\",\"table\":2,\"tuple\":[{\"t\":\"var\",\"v\":5}]}],\"hash_sites\":[],\"ranges\":[]}"

theorem c3_body_zero_iff (a : Assignment) :
    c3Body.eval a = 0 ↔ a SLOT_A = a INPUT := by
  simp only [c3Body, EmittedExpr.eval]
  constructor <;> intro h <;> omega

theorem c5Lo_body_zero_iff (a : Assignment) :
    c5LoBody.eval a = 0 ↔ a DIFF_LO = a SLOT_A - a LO := by
  simp only [c5LoBody, EmittedExpr.eval]
  constructor <;> intro h <;> omega

theorem c5Hi_body_zero_iff (a : Assignment) :
    c5HiBody.eval a = 0 ↔ a DIFF_HI = a HI - a SLOT_A := by
  simp only [c5HiBody, EmittedExpr.eval]
  constructor <;> intro h <;> omega

#guard decide (c3Body.eval (fun i => if i = SLOT_A ∨ i = INPUT then 7 else 0) = 0)
#guard decide (c5LoBody.eval (fun i => if i = DIFF_LO then 30 else if i = SLOT_A then 40 else if i = LO then 10 else 0) = 0)
#guard decide (¬ (c5LoBody.eval (fun i => if i = DIFF_LO then 29 else if i = SLOT_A then 40 else if i = LO then 10 else 0) = 0))
#guard decide (c5HiBody.eval (fun i => if i = DIFF_HI then 60 else if i = HI then 100 else if i = SLOT_A then 40 else 0) = 0)
#guard decide (¬ (c5HiBody.eval (fun i => if i = DIFF_HI then 59 else if i = HI then 100 else if i = SLOT_A then 40 else 0) = 0))

example : ([30] : List ℤ) ∈ rangeRows DIFF_BITS := by
  rw [range_row_mem_iff]; norm_num [DIFF_BITS]
example : ¬ (([2 ^ 29] : List ℤ) ∈ rangeRows DIFF_BITS) := by
  rw [range_row_mem_iff]; norm_num [DIFF_BITS]

#guard predicateInRangeDesc.traceWidth == PRED_WIDTH
#guard predicateInRangeDesc.piCount == 3
#guard predicateInRangeDesc.constraints.length == 8
#guard predicateInRangeDesc.tables.length == 1

#assert_axioms c3_body_zero_iff
#assert_axioms c5Lo_body_zero_iff
#assert_axioms c5Hi_body_zero_iff

end Dregg2.Circuit.Emit.PredicatesInRangeEmit
