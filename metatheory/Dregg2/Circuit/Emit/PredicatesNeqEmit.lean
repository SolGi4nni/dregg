/-
# Dregg2.Circuit.Emit.PredicatesNeqEmit — the emitted `NotEqual(value, threshold)`
arithmetic-predicate descriptor (`dregg-predicate-arith-neq::threshold-v1`).

## What this file IS

The `≠` case does NOT use a range proof: it uses the standard **nonzero-inverse gadget**. Let
`DIFF = value − threshold`. A witness column `DIFF_INV` and the degree-2 gate `DIFF · DIFF_INV = 1`
prove `DIFF` is INVERTIBLE — hence nonzero — hence `value ≠ threshold`. (Over the ℤ denotation the
gate forces `DIFF ∈ {1, −1}`, a fortiori `DIFF ≠ 0`; over the deployed BabyBear field the SAME gate
is satisfiable for ANY nonzero `DIFF`, which is exactly the field `≠` gadget. Either way the
soundness direction `DIFF·DIFF_INV = 1 ⟹ DIFF ≠ 0 ⟹ value ≠ threshold` holds.)

| tooth | constraint                                                    |
|-------|---------------------------------------------------------------|
| C1    | `.piBinding first THRESHOLD PI_THRESHOLD`                      |
| C2    | `.piBinding first FACT_COMMITMENT PI_FACT_COMMITMENT`          |
| C3    | `.gate (SLOT_A − INPUT)`  (bare-Input slot identity)          |
| C5    | `.gate (DIFF − SLOT_A + THRESHOLD)`  (`DIFF = value − threshold`) |
| CNZ   | `.gate (DIFF · DIFF_INV − 1)`  (`DIFF` invertible ⟹ `DIFF ≠ 0`) |

No range table, no lookups — a `value = threshold` forces `DIFF = 0`, and `0 · DIFF_INV = 0 ≠ 1`
has NO witness (UNSAT): the nonzero tooth BITES. Fact-commitment is the pass-through PI (C2).

`#assert_axioms` ⊆ {} on the gate lemmas. NEW file; imports read-only.
-/
import Dregg2.Circuit.DescriptorIR2

namespace Dregg2.Circuit.Emit.PredicatesNeqEmit

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 TableId emitVmJson2)

set_option autoImplicit false

def INPUT : Nat := 0
def SLOT_A : Nat := 1
def THRESHOLD : Nat := 2
def DIFF : Nat := 3
/-- The claimed inverse of `DIFF`; the degree-2 gate `DIFF · DIFF_INV = 1` forces `DIFF ≠ 0`. -/
def DIFF_INV : Nat := 4
def FACT_COMMITMENT : Nat := 5
def PRED_WIDTH : Nat := 6
def PI_THRESHOLD : Nat := 0
def PI_FACT_COMMITMENT : Nat := 1

def c1ThresholdPin : VmConstraint2 := .base (.piBinding VmRow.first THRESHOLD PI_THRESHOLD)
def c2FactPin : VmConstraint2 := .base (.piBinding VmRow.first FACT_COMMITMENT PI_FACT_COMMITMENT)

def c3Body : EmittedExpr := .add (.var SLOT_A) (.mul (.const (-1)) (.var INPUT))
def c3SlotGate : VmConstraint2 := .base (.gate c3Body)

/-- The C5 diff-computation body `DIFF − SLOT_A + THRESHOLD` (`DIFF = SLOT_A − THRESHOLD`, i.e.
`DIFF = value − threshold`). -/
def c5Body : EmittedExpr :=
  .add (.add (.var DIFF) (.mul (.const (-1)) (.var SLOT_A))) (.var THRESHOLD)
def c5DiffGate : VmConstraint2 := .base (.gate c5Body)

/-- The CNZ nonzero-inverse body `DIFF · DIFF_INV − 1` (degree 2). Zero iff `DIFF · DIFF_INV = 1`,
which forces `DIFF ≠ 0`. -/
def cNzBody : EmittedExpr := .add (.mul (.var DIFF) (.var DIFF_INV)) (.const (-1))
def cNzGate : VmConstraint2 := .base (.gate cNzBody)

/-- **`predicateNeqDesc`** — the arithmetic `NotEqual(value, threshold)` descriptor. No tables. -/
def predicateNeqDesc : EffectVmDescriptor2 :=
  { name        := "dregg-predicate-arith-neq::threshold-v1"
  , traceWidth  := PRED_WIDTH
  , piCount     := 2
  , tables      := []
  , constraints := [c1ThresholdPin, c2FactPin, c3SlotGate, c5DiffGate, cNzGate]
  , hashSites   := []
  , ranges      := [] }

#guard emitVmJson2 predicateNeqDesc ==
  "{\"name\":\"dregg-predicate-arith-neq::threshold-v1\",\"ir\":2,\"trace_width\":6,\"public_input_count\":2,\"tables\":[],\"constraints\":[{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":2,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":5,\"pi_index\":1},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":0}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":1}}},\"r\":{\"t\":\"var\",\"v\":2}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"var\",\"v\":4}},\"r\":{\"t\":\"const\",\"v\":-1}}}],\"hash_sites\":[],\"ranges\":[]}"

theorem c3_body_zero_iff (a : Assignment) :
    c3Body.eval a = 0 ↔ a SLOT_A = a INPUT := by
  simp only [c3Body, EmittedExpr.eval]
  constructor <;> intro h <;> omega

theorem c5_body_zero_iff (a : Assignment) :
    c5Body.eval a = 0 ↔ a DIFF = a SLOT_A - a THRESHOLD := by
  simp only [c5Body, EmittedExpr.eval]
  constructor <;> intro h <;> omega

/-- The CNZ gate body is zero iff `DIFF · DIFF_INV = 1`; this IMPLIES `DIFF ≠ 0`. -/
theorem cNz_body_zero_imp_ne (a : Assignment) :
    cNzBody.eval a = 0 → a DIFF ≠ 0 := by
  simp only [cNzBody, EmittedExpr.eval]
  intro h hz
  rw [hz] at h
  simp at h

#guard decide (c3Body.eval (fun i => if i = SLOT_A ∨ i = INPUT then 7 else 0) = 0)
#guard decide (¬ (c3Body.eval (fun i => if i = SLOT_A then 7 else 0) = 0))
#guard decide (c5Body.eval (fun i => if i = DIFF then 1 else if i = SLOT_A then 41 else if i = THRESHOLD then 40 else 0) = 0)
-- CNZ accepts a genuine inverse (DIFF = 1, DIFF_INV = 1) and rejects DIFF = 0.
#guard decide (cNzBody.eval (fun i => if i = DIFF then 1 else if i = DIFF_INV then 1 else 0) = 0)
#guard decide (¬ (cNzBody.eval (fun i => if i = DIFF then 0 else if i = DIFF_INV then 5 else 0) = 0))

#guard predicateNeqDesc.traceWidth == PRED_WIDTH
#guard predicateNeqDesc.piCount == 2
#guard predicateNeqDesc.constraints.length == 5
#guard predicateNeqDesc.tables.length == 0

#assert_axioms c3_body_zero_iff
#assert_axioms c5_body_zero_iff
#assert_axioms cNz_body_zero_imp_ne

end Dregg2.Circuit.Emit.PredicatesNeqEmit
