/-
# FieldDeltaRangeEmit — Lean-authored result-range circuit

The modular transition `new = old + delta` is retained, while a 30-bit
decomposition prevents an underflow wrap (`p-k`) from being committed as a new
game-economy value.  Rust includes and interprets the emitted IR2 bytes.
-/
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Circuit.DecideSatisfied2
import Dregg2.Circuit.GateExpr

namespace Dregg2.Circuit.Emit.FieldDeltaRangeEmit

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2

set_option autoImplicit false

def RESULT_BITS : Nat := 30
def OLD_COL : Nat := 0
def DELTA_COL : Nat := 1
def NEW_COL : Nat := 2
def BIT_BASE : Nat := 3
def WIDTH : Nat := BIT_BASE + RESULT_BITS
def PI_COUNT : Nat := 3
def bitCol (j : Nat) : Nat := BIT_BASE + j

def esub (x y : EmittedExpr) : EmittedExpr := .add x (.mul (.const (-1)) y)
def gate (body : EmittedExpr) : VmConstraint2 := .base (.gate body)
def boolBody (j : Nat) : EmittedExpr :=
  Dregg2.Circuit.GateExpr.render Dregg2.Circuit.GateExpr.toEmitted
    (Dregg2.Circuit.GateExpr.gBoolEnc2 (.leaf (bitCol j)))

theorem boolBody_eq (j : Nat) :
    boolBody j = let b := EmittedExpr.var (bitCol j); .mul b (esub b (.const 1)) := rfl
def recomposeBody : EmittedExpr :=
  (List.range RESULT_BITS).foldl
    (fun acc j => esub acc (.mul (.const ((2 : Int) ^ j)) (.var (bitCol j))))
    (.var NEW_COL)

def transitionGate : VmConstraint2 :=
  gate (esub (.var NEW_COL) (.add (.var OLD_COL) (.var DELTA_COL)))
def booleanGates : List VmConstraint2 :=
  (List.range RESULT_BITS).map (fun j => gate (boolBody j))
def recomposeGate : VmConstraint2 := gate recomposeBody
def piPins : List VmConstraint2 :=
  [.base (.piBinding VmRow.first OLD_COL 0),
   .base (.piBinding VmRow.first DELTA_COL 1),
   .base (.piBinding VmRow.first NEW_COL 2)]

def fieldDeltaRangeConstraints : List VmConstraint2 :=
  transitionGate :: booleanGates ++ [recomposeGate] ++ piPins

def fieldDeltaRangeDescriptor : EffectVmDescriptor2 :=
  { name := "field-delta-result-range"
  , traceWidth := WIDTH
  , piCount := PI_COUNT
  , tables := []
  , constraints := fieldDeltaRangeConstraints
  , hashSites := []
  , ranges := [] }

#guard fieldDeltaRangeDescriptor.traceWidth == 33
#guard fieldDeltaRangeDescriptor.piCount == 3
#guard fieldDeltaRangeDescriptor.constraints.length == 35
#guard (2 : Int) ^ RESULT_BITS < 2013265921

/-- Exact emitted-wire golden included verbatim by circuit-prove. -/
def FIELD_DELTA_RANGE_GOLDEN : String :=
  "{\"name\":\"field-delta-result-range\",\"ir\":2,\"trace_width\":33,\"public_input_count\":3,\"challenges\":0,\"tables\":[],\"constraints\":[{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"var\",\"v\":1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"const\",\"v\":1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"const\",\"v\":1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"const\",\"v\":1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"const\",\"v\":1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"const\",\"v\":1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"const\",\"v\":1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":9},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":9},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"const\",\"v\":1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"const\",\"v\":1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":11},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":11},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"const\",\"v\":1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":12},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":12},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"const\",\"v\":1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":13},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":13},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"const\",\"v\":1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":14},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":14},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"const\",\"v\":1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":15},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":15},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"const\",\"v\":1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"const\",\"v\":1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":17},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":17},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"const\",\"v\":1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":18},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":18},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"const\",\"v\":1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"const\",\"v\":1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"const\",\"v\":1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"const\",\"v\":1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":22},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":22},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"const\",\"v\":1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":23},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":23},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"const\",\"v\":1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":24},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":24},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"const\",\"v\":1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":25},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":25},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"const\",\"v\":1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":26},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":26},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"const\",\"v\":1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":27},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":27},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"const\",\"v\":1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":28},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":28},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"const\",\"v\":1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":29},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":29},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"const\",\"v\":1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":30},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":30},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"const\",\"v\":1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":31},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":31},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"const\",\"v\":1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"const\",\"v\":1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":3}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"var\",\"v\":4}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":4},\"r\":{\"t\":\"var\",\"v\":5}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":8},\"r\":{\"t\":\"var\",\"v\":6}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":16},\"r\":{\"t\":\"var\",\"v\":7}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":8}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":64},\"r\":{\"t\":\"var\",\"v\":9}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":128},\"r\":{\"t\":\"var\",\"v\":10}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":256},\"r\":{\"t\":\"var\",\"v\":11}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":512},\"r\":{\"t\":\"var\",\"v\":12}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1024},\"r\":{\"t\":\"var\",\"v\":13}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2048},\"r\":{\"t\":\"var\",\"v\":14}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":4096},\"r\":{\"t\":\"var\",\"v\":15}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":8192},\"r\":{\"t\":\"var\",\"v\":16}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":16384},\"r\":{\"t\":\"var\",\"v\":17}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":32768},\"r\":{\"t\":\"var\",\"v\":18}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":65536},\"r\":{\"t\":\"var\",\"v\":19}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":131072},\"r\":{\"t\":\"var\",\"v\":20}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":262144},\"r\":{\"t\":\"var\",\"v\":21}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":524288},\"r\":{\"t\":\"var\",\"v\":22}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1048576},\"r\":{\"t\":\"var\",\"v\":23}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2097152},\"r\":{\"t\":\"var\",\"v\":24}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":4194304},\"r\":{\"t\":\"var\",\"v\":25}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":8388608},\"r\":{\"t\":\"var\",\"v\":26}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":16777216},\"r\":{\"t\":\"var\",\"v\":27}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":33554432},\"r\":{\"t\":\"var\",\"v\":28}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":67108864},\"r\":{\"t\":\"var\",\"v\":29}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":134217728},\"r\":{\"t\":\"var\",\"v\":30}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":268435456},\"r\":{\"t\":\"var\",\"v\":31}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":536870912},\"r\":{\"t\":\"var\",\"v\":32}}}}},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":0,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":1,\"pi_index\":1},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":2,\"pi_index\":2}],\"hash_sites\":[],\"ranges\":[]}"

#guard emitVmJson2 fieldDeltaRangeDescriptor == FIELD_DELTA_RANGE_GOLDEN

/-! ## Semantic soundness of the range tooth. -/

def Canon (x : ℤ) : Prop := 0 ≤ x ∧ x < 2013265921

theorem esub_eval (x y : EmittedExpr) (a : Assignment) :
    (esub x y).eval a = x.eval a - y.eval a := by
  simp [esub, EmittedExpr.eval]; ring

theorem binary_of_boolBody {a : Assignment} {j : Nat}
    (h : (boolBody j).eval a ≡ 0 [ZMOD 2013265921])
    (hc : Canon (a (bitCol j))) :
    a (bitCol j) = 0 ∨ a (bitCol j) = 1 := by
  obtain ⟨h0, h1⟩ := hc
  have hev : (boolBody j).eval a = a (bitCol j) * (a (bitCol j) - 1) := by
    simp only [boolBody_eq, esub, EmittedExpr.eval]; ring
  rw [hev] at h
  have hd : (2013265921 : ℤ) ∣ a (bitCol j) * (a (bitCol j) - 1) :=
    Int.modEq_zero_iff_dvd.mp h
  rcases Dregg2.Circuit.Emit.EffectVmEmitTransfer.pPrimeInt.dvd_mul.mp hd with hx | hx
  · obtain ⟨k, hk⟩ := hx; left; omega
  · obtain ⟨k, hk⟩ := hx; right; omega

theorem recompose_foldl_eval (a : Assignment) :
    ∀ (l : List Nat) (e0 : EmittedExpr),
      (l.foldl (fun acc j => esub acc (.mul (.const ((2 : Int) ^ j)) (.var (bitCol j)))) e0).eval a
        = e0.eval a - (l.map (fun j => (2 : Int) ^ j * a (bitCol j))).sum := by
  intro l
  induction l with
  | nil => intro e0; simp
  | cons x xs ih =>
    intro e0
    rw [List.foldl_cons, ih]
    simp only [List.map_cons, List.sum_cons, esub, EmittedExpr.eval]
    ring

theorem recomposeBody_eval (a : Assignment) :
    recomposeBody.eval a = a NEW_COL -
      ((List.range RESULT_BITS).map (fun j => (2 : Int) ^ j * a (bitCol j))).sum := by
  simpa [recomposeBody, EmittedExpr.eval] using
    recompose_foldl_eval a (List.range RESULT_BITS) (.var NEW_COL)

theorem bitsum_bounds (a : Assignment) :
    ∀ n, (∀ j < n, a (bitCol j) = 0 ∨ a (bitCol j) = 1) →
      0 ≤ ((List.range n).map (fun j => (2 : Int) ^ j * a (bitCol j))).sum ∧
      ((List.range n).map (fun j => (2 : Int) ^ j * a (bitCol j))).sum < 2 ^ n := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ k ih =>
    intro hbit
    obtain ⟨ih0, ih1⟩ := ih (fun j hj => hbit j (by omega))
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    have h2k : (0 : ℤ) ≤ 2 ^ k := by positivity
    have hpow : (2 : ℤ) ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
    rcases hbit k (by omega) with h | h <;> rw [h] <;> constructor <;>
      nlinarith [ih0, ih1, h2k]

theorem eq_of_modEq_canon {a b : ℤ} (h : a ≡ b [ZMOD 2013265921])
    (ha : Canon a) (hb : Canon b) : a = b := by
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hb0, hb1⟩ := hb
  obtain ⟨k, hk⟩ := h.dvd
  omega

/-- The emitted 30-bit decomposition forces the exact integer range. -/
theorem range_forces_result (a : Assignment)
    (hbool : ∀ j < RESULT_BITS, (boolBody j).eval a ≡ 0 [ZMOD 2013265921])
    (hrec : recomposeBody.eval a ≡ 0 [ZMOD 2013265921])
    (hnew : Canon (a NEW_COL))
    (hbits : ∀ j < RESULT_BITS, Canon (a (bitCol j))) :
    0 ≤ a NEW_COL ∧ a NEW_COL < 2 ^ RESULT_BITS := by
  set S := ((List.range RESULT_BITS).map
    (fun j => (2 : Int) ^ j * a (bitCol j))).sum with hS
  have hbit : ∀ j < RESULT_BITS, a (bitCol j) = 0 ∨ a (bitCol j) = 1 :=
    fun j hj => binary_of_boolBody (hbool j hj) (hbits j hj)
  have hnewS : a NEW_COL ≡ S [ZMOD 2013265921] := by
    have h : (a NEW_COL - S) ≡ 0 [ZMOD 2013265921] := by
      rw [← recomposeBody_eval]
      exact hrec
    obtain ⟨k, hk⟩ := Int.modEq_zero_iff_dvd.mp h
    exact Int.modEq_iff_dvd.mpr ⟨-k, by linear_combination -hk⟩
  obtain ⟨hS0, hS1⟩ := bitsum_bounds a RESULT_BITS hbit
  have heq : a NEW_COL = S := eq_of_modEq_canon hnewS hnew
    ⟨hS0, lt_trans hS1 (by norm_num [RESULT_BITS])⟩
  exact ⟨by rw [heq]; exact hS0, by rw [heq]; exact hS1⟩

def constTrace (a pub : Assignment) : VmTrace :=
  { rows := List.replicate 8 a, pub := pub, tf := fun _ => [] }

@[simp] theorem constTrace_loc0 (a pub : Assignment) :
    (envAt (constTrace a pub) 0).loc = a := by
  funext k
  simp [envAt, constTrace, List.getD]

theorem gate_vanishes {hash : List ℤ → ℤ} {a pub : Assignment}
    (hsat : Satisfied2 hash fieldDeltaRangeDescriptor (fun _ => 0) (fun _ => (0, 0)) []
      (constTrace a pub))
    {body : EmittedExpr} (hmem : gate body ∈ fieldDeltaRangeConstraints) :
    body.eval a ≡ 0 [ZMOD 2013265921] := by
  have h := hsat.rowConstraints 0 (by simp [constTrace]) _ hmem
  simp only [VmConstraint2.holdsAt, gate, VmConstraint.holdsVm, constTrace_loc0] at h
  exact h

/-- Whole-descriptor soundness: a satisfying constant transition obeys the
modular delta equation and its result is an integer in `[0,2^30)`. -/
theorem fieldDeltaRange_emit_sound {hash : List ℤ → ℤ} {a pub : Assignment}
    (hcanon : ∀ c, Canon (a c))
    (hsat : Satisfied2 hash fieldDeltaRangeDescriptor (fun _ => 0) (fun _ => (0, 0)) []
      (constTrace a pub)) :
    (a NEW_COL - (a OLD_COL + a DELTA_COL) ≡ 0 [ZMOD 2013265921]) ∧
    (0 ≤ a NEW_COL ∧ a NEW_COL < 2 ^ RESULT_BITS) := by
  constructor
  · have h := gate_vanishes (body :=
        esub (.var NEW_COL) (.add (.var OLD_COL) (.var DELTA_COL))) hsat (by
      show transitionGate ∈ fieldDeltaRangeConstraints
      simp [fieldDeltaRangeConstraints])
    have heq : a NEW_COL - (a OLD_COL + a DELTA_COL) =
        a NEW_COL + (-a DELTA_COL + -a OLD_COL) := by ring
    rw [heq]
    simpa [esub, EmittedExpr.eval] using h
  · apply range_forces_result a
    · intro j hj
      apply gate_vanishes (body := boolBody j) hsat
      show gate (boolBody j) ∈ fieldDeltaRangeConstraints
      simp only [fieldDeltaRangeConstraints, List.mem_append]
      refine Or.inl (Or.inl (List.mem_cons.mpr (Or.inr ?_)))
      show gate (boolBody j) ∈ booleanGates
      simp only [booleanGates, List.mem_map, List.mem_range]
      exact ⟨j, hj, rfl⟩
    · apply gate_vanishes (body := recomposeBody) hsat
      show recomposeGate ∈ fieldDeltaRangeConstraints
      simp only [fieldDeltaRangeConstraints, List.mem_append]
      exact Or.inl (Or.inr (by simp))
    · exact hcanon NEW_COL
    · intro j _; exact hcanon (bitCol j)

-- Closed teeth: 70 has a 30-bit representation; p-20 is outside it.
#guard decide ((70 : Int) < 2 ^ RESULT_BITS)
#guard decide (¬ ((2013265921 - 20 : Int) < 2 ^ RESULT_BITS))

#assert_all_clean [Dregg2.Circuit.Emit.FieldDeltaRangeEmit.esub_eval,
  Dregg2.Circuit.Emit.FieldDeltaRangeEmit.binary_of_boolBody,
  Dregg2.Circuit.Emit.FieldDeltaRangeEmit.recompose_foldl_eval,
  Dregg2.Circuit.Emit.FieldDeltaRangeEmit.recomposeBody_eval,
  Dregg2.Circuit.Emit.FieldDeltaRangeEmit.bitsum_bounds,
  Dregg2.Circuit.Emit.FieldDeltaRangeEmit.eq_of_modEq_canon,
  Dregg2.Circuit.Emit.FieldDeltaRangeEmit.range_forces_result,
  Dregg2.Circuit.Emit.FieldDeltaRangeEmit.gate_vanishes,
  Dregg2.Circuit.Emit.FieldDeltaRangeEmit.fieldDeltaRange_emit_sound]

end Dregg2.Circuit.Emit.FieldDeltaRangeEmit
