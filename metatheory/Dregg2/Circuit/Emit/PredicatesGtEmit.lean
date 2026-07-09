/-
# Dregg2.Circuit.Emit.PredicatesGtEmit — the emitted `GreaterThan(value, threshold)`
arithmetic-predicate descriptor (`dregg-predicate-arith-gt::threshold-v1`).

The strict `>` sibling of `PredicatesArithmeticEmit.predicateGeDesc`. Strict comparison is `≥` with a
`+1`: `value > threshold ↔ value ≥ threshold + 1 ↔ value − threshold − 1 ≥ 0`. So the DIFF is the
`≥` DIFF minus one:

  * `≥`:  `DIFF = value − threshold ∈ [0, 2^29)`;
  * `>`:  `DIFF = value − threshold − 1 ∈ [0, 2^29)`.

The five teeth are the arithmetic-comparison core (C1/C2 PI pins, C3 slot identity, C5 diff gate,
C6 range lookup); the C6 range lookup is the load-bearing tooth (a `value ≤ threshold` wraps
`DIFF = value − threshold − 1` below zero — UNSAT). Fact-commitment is the hand-AIR pass-through PI
(C2); the Poseidon2 value↔fact weld is an orthogonal family-wide follow-up.

`#assert_axioms` ⊆ {} on the gate lemmas. NEW file; imports read-only.
-/
import Dregg2.Circuit.DescriptorIR2

namespace Dregg2.Circuit.Emit.PredicatesGtEmit

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Lookup TableId rangeTableDef emitVmJson2 rangeRows
   range_row_mem_iff)

set_option autoImplicit false

def INPUT : Nat := 0
def SLOT_A : Nat := 1
def THRESHOLD : Nat := 2
def DIFF : Nat := 3
def FACT_COMMITMENT : Nat := 4
def PRED_WIDTH : Nat := 5
def PI_THRESHOLD : Nat := 0
def PI_FACT_COMMITMENT : Nat := 1
def DIFF_BITS : Nat := 29

def c1ThresholdPin : VmConstraint2 := .base (.piBinding VmRow.first THRESHOLD PI_THRESHOLD)
def c2FactPin : VmConstraint2 := .base (.piBinding VmRow.first FACT_COMMITMENT PI_FACT_COMMITMENT)

def c3Body : EmittedExpr := .add (.var SLOT_A) (.mul (.const (-1)) (.var INPUT))
def c3SlotGate : VmConstraint2 := .base (.gate c3Body)

/-- The C5 diff-computation body `DIFF − SLOT_A + THRESHOLD + 1` (`DIFF = SLOT_A − THRESHOLD − 1`,
i.e. `DIFF = value − threshold − 1` — the strict `>` shift of the `≥` template). -/
def c5Body : EmittedExpr :=
  .add (.add (.add (.var DIFF) (.mul (.const (-1)) (.var SLOT_A))) (.var THRESHOLD)) (.const 1)
def c5DiffGate : VmConstraint2 := .base (.gate c5Body)

def c6RangeLookup : VmConstraint2 := .lookup ⟨TableId.range, [.var DIFF]⟩

/-- **`predicateGtDesc`** — the arithmetic `GreaterThan(value, threshold)` descriptor. -/
def predicateGtDesc : EffectVmDescriptor2 :=
  { name        := "dregg-predicate-arith-gt::threshold-v1"
  , traceWidth  := PRED_WIDTH
  , piCount     := 2
  , tables      := [rangeTableDef DIFF_BITS]
  , constraints := [c1ThresholdPin, c2FactPin, c3SlotGate, c5DiffGate, c6RangeLookup]
  , hashSites   := []
  , ranges      := [] }

#guard emitVmJson2 predicateGtDesc ==
  "{\"name\":\"dregg-predicate-arith-gt::threshold-v1\",\"ir\":2,\"trace_width\":5,\"public_input_count\":2,\"tables\":[{\"id\":2,\"name\":\"range\",\"arity\":1,\"sem\":\"range\",\"bits\":29}],\"constraints\":[{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":2,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":4,\"pi_index\":1},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":0}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":1}}},\"r\":{\"t\":\"var\",\"v\":2}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"lookup\",\"table\":2,\"tuple\":[{\"t\":\"var\",\"v\":3}]}],\"hash_sites\":[],\"ranges\":[]}"

theorem c3_body_zero_iff (a : Assignment) :
    c3Body.eval a = 0 ↔ a SLOT_A = a INPUT := by
  simp only [c3Body, EmittedExpr.eval]
  constructor <;> intro h <;> omega

/-- The C5 gate body is zero iff `DIFF = SLOT_A − THRESHOLD − 1` (the strict `>` diff identity). -/
theorem c5_body_zero_iff (a : Assignment) :
    c5Body.eval a = 0 ↔ a DIFF = a SLOT_A - a THRESHOLD - 1 := by
  simp only [c5Body, EmittedExpr.eval]
  constructor <;> intro h <;> omega

#guard decide (c3Body.eval (fun i => if i = SLOT_A ∨ i = INPUT then 7 else 0) = 0)
#guard decide (¬ (c3Body.eval (fun i => if i = SLOT_A then 7 else 0) = 0))
#guard decide (c5Body.eval (fun i => if i = DIFF then 59 else if i = SLOT_A then 100 else if i = THRESHOLD then 40 else 0) = 0)
#guard decide (¬ (c5Body.eval (fun i => if i = DIFF then 60 else if i = SLOT_A then 100 else if i = THRESHOLD then 40 else 0) = 0))

example : ([59] : List ℤ) ∈ rangeRows DIFF_BITS := by
  rw [range_row_mem_iff]; norm_num [DIFF_BITS]
example : ¬ (([2 ^ 29] : List ℤ) ∈ rangeRows DIFF_BITS) := by
  rw [range_row_mem_iff]; norm_num [DIFF_BITS]

#guard predicateGtDesc.traceWidth == PRED_WIDTH
#guard predicateGtDesc.piCount == 2
#guard predicateGtDesc.constraints.length == 5
#guard predicateGtDesc.tables.length == 1

#assert_axioms c3_body_zero_iff
#assert_axioms c5_body_zero_iff

end Dregg2.Circuit.Emit.PredicatesGtEmit
