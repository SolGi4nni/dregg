/-
# A certified Gabbay matrix instance in the live descriptor IR-v2

This module connects the rational matrix semantics and its finite-field
projection certificate to the descriptor relation used by the running dregg
proof stack.  The compiled source schema is a three-entry graph of a unary
Skolem function.  Its two matrix rows are interpolated at the one-based nodes
`1,2,3`, and the source formula requires every output to equal its input plus
one.

The trace carries denominator-cleared coefficients for `2 * P(X)`.  For row
values `y1,y2,y3` those coefficients are

* `6*y1 - 6*y2 + 2*y3`,
* `-5*y1 + 8*y2 - 3*y3`,
* `y1 - 2*y2 + y3`.

Thus interpolation needs no witness-authored division and every evaluation
gate is an exact integer identity before reduction modulo BabyBear.  Three
separate squared residual gates feed an exact numerator column, and the final
always-on gate requires that numerator to vanish.

The main theorem is an exact live relation, not an analogy: for every concrete
three-entry table carrying the proved no-wrap projection certificate, its
constructed IR-v2 trace satisfies the emitted descriptor iff the ordinary
`Holds` semantics satisfies the original bounded formula.  The final examples
construct the successor trace and refuse both a tampered entry and the known
unchecked modulus-five projection.

This is deliberately the largest faithful fixed-arity fragment established
here.  A symbolic compiler for arbitrary matrix length would additionally need
an emitted interpolation algorithm and certified denominator/no-wrap cost;
IR-v2 itself is fixed to BabyBear and cannot soundly select a witness-authored
modulus.
-/
import Dregg2.Metatheory.GabbayFiniteFieldProjection
import Dregg2.Circuit.DescriptorIR2

namespace Dregg2.Metatheory.GabbayDescriptorIR2

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)
open GabbayMatrixSemantics
open GabbayFiniteFieldProjection

set_option autoImplicit false

/-! ## 1. Source tables and their ordinary semantics -/

/-- A concrete two-row, three-column graph table. -/
structure ThreeEntryTable where
  input : Fin 3 -> Int
  output : Fin 3 -> Int

/-- Turn the graph into the intrinsically sized matrix expected by the source
semantics. -/
def sourceMatrix (table : ThreeEntryTable) : IntMatrix 2 where
  length := 3
  length_pos := by decide
  cell row col := if row.1 = 0 then table.input col else table.output col

@[simp] theorem sourceMatrix_input (table : ThreeEntryTable) (j : Fin 3) :
    (sourceMatrix table).cell inputRow j = table.input j := by
  simp [sourceMatrix, inputRow]

@[simp] theorem sourceMatrix_output (table : ThreeEntryTable) (j : Fin 3) :
    (sourceMatrix table).cell outputRow j = table.output j := by
  simp [sourceMatrix, outputRow]

/-- The source valuation determined by a concrete table. -/
def sourceValuation (table : ThreeEntryTable) : Valuation skolemSignature
  | .table => sourceMatrix table

/-- Ordinary source truth is pointwise successor truth at the three declared
columns. -/
theorem holds_iff_entries (table : ThreeEntryTable) :
    Holds (sourceValuation table) 0 successorSkolemFormula <->
      forall j : Fin 3, table.output j = table.input j + 1 := by
  simp only [successorSkolemFormula, Holds]
  constructor
  · intro h j
    have hj := h j
    rw [eval_lookup_index_at_node, evalTerm_add, eval_lookup_index_at_node,
      evalTerm_rational] at hj
    exact_mod_cast hj
  · intro h j
    rw [eval_lookup_index_at_node, evalTerm_add, eval_lookup_index_at_node,
      evalTerm_rational]
    exact_mod_cast h j

/-- The exact integer numerator implemented by the live circuit. -/
def residualNumerator (table : ThreeEntryTable) : Int :=
  (table.output 0 - table.input 0 - 1) ^ 2 +
  (table.output 1 - table.input 1 - 1) ^ 2 +
  (table.output 2 - table.input 2 - 1) ^ 2

/-- The projection obligation for the integer residual actually emitted by
the fixed-schema descriptor.  Unlike a witness-authored field modulus, this
certificate is checked outside the circuit and names BabyBear explicitly. -/
structure LiveProjectionCertificate (table : ThreeEntryTable) : Prop where
  prime : Nat.Prime 2013265921
  numeratorNoWrap : (residualNumerator table).natAbs < 2013265921

/-! ## 2. Denominator-cleared row interpolation -/

/-- Integral coefficients of `2 * P(X)` for the unique degree-below-three
interpolant through `y(1),y(2),y(3)`. -/
def twiceCoefficients (y : Fin 3 -> Int) : Fin 3 -> Int
  | 0 => 6 * y 0 - 6 * y 1 + 2 * y 2
  | 1 => -5 * y 0 + 8 * y 1 - 3 * y 2
  | 2 => y 0 - 2 * y 1 + y 2

/-- Evaluation of the cleared coefficient witness recovers twice the exact
entry at every interpolation node. -/
theorem twiceCoefficients_eval (y : Fin 3 -> Int) (j : Fin 3) :
    twiceCoefficients y 0 + twiceCoefficients y 1 * (j.1 + 1) +
        twiceCoefficients y 2 * (j.1 + 1) ^ 2 = 2 * y j := by
  fin_cases j <;> simp [twiceCoefficients] <;> ring

/-! ## 3. Concrete live descriptor -/

def inputCol (j : Fin 3) : Nat := j.1
def outputCol (j : Fin 3) : Nat := 3 + j.1
def inputCoeffCol (k : Fin 3) : Nat := 6 + k.1
def outputCoeffCol (k : Fin 3) : Nat := 9 + k.1
def residualCol (j : Fin 3) : Nat := 12 + j.1
def numeratorCol : Nat := 15
def denominatorCol : Nat := 16
def TRACE_WIDTH : Nat := 17

def negW (x : WindowExpr) : WindowExpr := .mul (.const (-1)) x
def subW (x y : WindowExpr) : WindowExpr := .add x (negW y)
def scaleW (n : Int) (x : WindowExpr) : WindowExpr := .mul (.const n) x
def squareW (x : WindowExpr) : WindowExpr := .mul x x

/-- Evaluate a denominator-cleared quadratic coefficient row at one of the
three declared one-based nodes, then bind it to twice the entry column. -/
def interpolationBody (coeffCol : Fin 3 -> Nat) (entry : Nat)
    (node : Nat) : WindowExpr :=
  subW
    (.add (.add (.loc (coeffCol 0))
      (scaleW node (.loc (coeffCol 1))))
      (scaleW (node ^ 2) (.loc (coeffCol 2))))
    (scaleW 2 (.loc entry))

/-- One squared atomic residual, materialized in its own column. -/
def residualBody (j : Fin 3) : WindowExpr :=
  subW (.loc (residualCol j))
    (squareW (subW (subW (.loc (outputCol j)) (.loc (inputCol j))) (.const 1)))

def numeratorBody : WindowExpr :=
  subW (.loc numeratorCol)
    (.add (.add (.loc (residualCol 0)) (.loc (residualCol 1)))
      (.loc (residualCol 2)))

def acceptBody : WindowExpr := .loc numeratorCol
def denominatorBody : WindowExpr := subW (.loc denominatorCol) (.const 1)

def always (body : WindowExpr) : VmConstraint2 :=
  .windowGate { body := body, onTransition := false }

/-- Explicit entry, interpolation, residual, numerator, denominator, and
acceptance constraints.  Every gate is always-on, including the final row. -/
def gabbayConstraints : List VmConstraint2 :=
  [ always (interpolationBody inputCoeffCol (inputCol 0) 1)
  , always (interpolationBody inputCoeffCol (inputCol 1) 2)
  , always (interpolationBody inputCoeffCol (inputCol 2) 3)
  , always (interpolationBody outputCoeffCol (outputCol 0) 1)
  , always (interpolationBody outputCoeffCol (outputCol 1) 2)
  , always (interpolationBody outputCoeffCol (outputCol 2) 3)
  , always (residualBody 0)
  , always (residualBody 1)
  , always (residualBody 2)
  , always numeratorBody
  , always denominatorBody
  , always acceptBody ]

/-- The fixed-schema compiler target in the live v2 grammar. -/
def compileDescriptor : EffectVmDescriptor2 :=
  { name := "dregg-gabbay-three-entry-skolem-v2"
  , traceWidth := TRACE_WIDTH
  , piCount := 0
  , tables := [mainTableDef TRACE_WIDTH]
  , constraints := gabbayConstraints
  , hashSites := []
  , ranges := [] }

theorem accept_constraint_mem : always acceptBody ∈ compileDescriptor.constraints := by
  simp [compileDescriptor, gabbayConstraints]

/-! ## 4. Constructive trace -/

def rowOf (table : ThreeEntryTable) : Assignment
  | 0 => table.input 0
  | 1 => table.input 1
  | 2 => table.input 2
  | 3 => table.output 0
  | 4 => table.output 1
  | 5 => table.output 2
  | 6 => twiceCoefficients table.input 0
  | 7 => twiceCoefficients table.input 1
  | 8 => twiceCoefficients table.input 2
  | 9 => twiceCoefficients table.output 0
  | 10 => twiceCoefficients table.output 1
  | 11 => twiceCoefficients table.output 2
  | 12 => (table.output 0 - table.input 0 - 1) ^ 2
  | 13 => (table.output 1 - table.input 1 - 1) ^ 2
  | 14 => (table.output 2 - table.input 2 - 1) ^ 2
  | 15 => residualNumerator table
  | 16 => 1
  | _ => 0

def traceOf (table : ThreeEntryTable) : VmTrace :=
  { rows := [rowOf table], pub := zeroAsg, tf := fun _ => [] }

@[simp] theorem traceOf_loc (table : ThreeEntryTable) :
    (envAt (traceOf table) 0).loc = rowOf table := by
  simp [envAt, traceOf]

@[simp] theorem rowOf_input (table : ThreeEntryTable) (j : Fin 3) :
    rowOf table (inputCol j) = table.input j := by
  fin_cases j <;> rfl

@[simp] theorem rowOf_output (table : ThreeEntryTable) (j : Fin 3) :
    rowOf table (outputCol j) = table.output j := by
  fin_cases j <;> rfl

@[simp] theorem rowOf_inputCoefficient (table : ThreeEntryTable) (k : Fin 3) :
    rowOf table (inputCoeffCol k) = twiceCoefficients table.input k := by
  fin_cases k <;> rfl

@[simp] theorem rowOf_outputCoefficient (table : ThreeEntryTable) (k : Fin 3) :
    rowOf table (outputCoeffCol k) = twiceCoefficients table.output k := by
  fin_cases k <;> rfl

@[simp] theorem rowOf_residual (table : ThreeEntryTable) (j : Fin 3) :
    rowOf table (residualCol j) =
      (table.output j - table.input j - 1) ^ 2 := by
  fin_cases j <;> rfl

@[simp] theorem rowOf_numerator (table : ThreeEntryTable) :
    rowOf table numeratorCol = residualNumerator table := rfl

@[simp] theorem rowOf_denominator (table : ThreeEntryTable) :
    rowOf table denominatorCol = 1 := rfl

theorem memLog_compileDescriptor (table : ThreeEntryTable) :
    memLog compileDescriptor (traceOf table) = [] := by
  simp [memLog, memOpsOf, compileDescriptor, gabbayConstraints, always]

theorem mapLog_compileDescriptor (table : ThreeEntryTable) :
    mapLog compileDescriptor (traceOf table) = [] := by
  simp [mapLog, mapOpsOf, compileDescriptor, gabbayConstraints, always]

/-- All non-acceptance gates of the constructed trace are exact integer
identities.  Consequently source truth constructs a full live `Satisfied2`
witness. -/
theorem trace_complete (hash : List Int -> Int) (table : ThreeEntryTable)
    (hholds : Holds (sourceValuation table) 0 successorSkolemFormula) :
    Satisfied2 hash compileDescriptor (fun _ => 0)
      (fun _ => ((0 : Int), 0)) [] (traceOf table) := by
  have hentries := (holds_iff_entries table).1 hholds
  refine ⟨?_, ?_, ?_, List.nodup_nil, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi c hc
    have hi0 : i = 0 := by simp [traceOf] at hi; omega
    subst i
    simp only [compileDescriptor] at hc
    simp only [gabbayConstraints, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl
    all_goals
      simp only [always, VmConstraint2.holdsAt, WindowConstraint.holdsAt,
        Bool.false_eq_true, if_false]
    · change (interpolationBody inputCoeffCol (inputCol 0) 1).eval
          (envAt (traceOf table) 0) ≡ 0 [ZMOD 2013265921]
      simp [interpolationBody, subW, negW, scaleW, WindowExpr.eval,
        traceOf_loc, twiceCoefficients]
      ring_nf
      exact Int.ModEq.refl 0
    · change (interpolationBody inputCoeffCol (inputCol 1) 2).eval
          (envAt (traceOf table) 0) ≡ 0 [ZMOD 2013265921]
      simp [interpolationBody, subW, negW, scaleW, WindowExpr.eval,
        traceOf_loc, twiceCoefficients]
      ring_nf
      exact Int.ModEq.refl 0
    · change (interpolationBody inputCoeffCol (inputCol 2) 3).eval
          (envAt (traceOf table) 0) ≡ 0 [ZMOD 2013265921]
      simp [interpolationBody, subW, negW, scaleW, WindowExpr.eval,
        traceOf_loc, twiceCoefficients]
      ring_nf
      exact Int.ModEq.refl 0
    · change (interpolationBody outputCoeffCol (outputCol 0) 1).eval
          (envAt (traceOf table) 0) ≡ 0 [ZMOD 2013265921]
      simp [interpolationBody, subW, negW, scaleW, WindowExpr.eval,
        traceOf_loc, twiceCoefficients]
      ring_nf
      exact Int.ModEq.refl 0
    · change (interpolationBody outputCoeffCol (outputCol 1) 2).eval
          (envAt (traceOf table) 0) ≡ 0 [ZMOD 2013265921]
      simp [interpolationBody, subW, negW, scaleW, WindowExpr.eval,
        traceOf_loc, twiceCoefficients]
      ring_nf
      exact Int.ModEq.refl 0
    · change (interpolationBody outputCoeffCol (outputCol 2) 3).eval
          (envAt (traceOf table) 0) ≡ 0 [ZMOD 2013265921]
      simp [interpolationBody, subW, negW, scaleW, WindowExpr.eval,
        traceOf_loc, twiceCoefficients]
      ring_nf
      exact Int.ModEq.refl 0
    · simp [residualBody, subW, negW, squareW, WindowExpr.eval, traceOf_loc]
      ring_nf
      exact Int.ModEq.refl 0
    · simp [residualBody, subW, negW, squareW, WindowExpr.eval, traceOf_loc]
      ring_nf
      exact Int.ModEq.refl 0
    · simp [residualBody, subW, negW, squareW, WindowExpr.eval, traceOf_loc]
      ring_nf
      exact Int.ModEq.refl 0
    · simp [numeratorBody, subW, negW, WindowExpr.eval, traceOf_loc,
        residualNumerator]
    · simp [denominatorBody, subW, negW, WindowExpr.eval, traceOf_loc]
    · change residualNumerator table ≡ 0 [ZMOD 2013265921]
      have h0 : residualNumerator table = 0 := by
        simp [residualNumerator, hentries 0, hentries 1, hentries 2]
      rw [h0]
  · intro i hi
    trivial
  · intro i hi r hr
    simp [compileDescriptor] at hr
  · intro op hop
    rw [memLog_compileDescriptor table] at hop
    cases hop
  · rw [memLog_compileDescriptor table]
    trivial
  · rw [memLog_compileDescriptor table]
    exact memCheck_nil _ _
  · rw [memLog_compileDescriptor table]
    rfl
  · rw [mapLog_compileDescriptor table]
    rfl

/-! ## 5. Certified soundness and the exact live relation -/

/-- Any accepting constructed trace has a BabyBear-zero exact numerator. -/
theorem accepting_trace_modEq_zero {hash : List Int -> Int}
    {table : ThreeEntryTable}
    (hsat : Satisfied2 hash compileDescriptor (fun _ => 0)
      (fun _ => ((0 : Int), 0)) [] (traceOf table)) :
    residualNumerator table ≡ 0 [ZMOD 2013265921] := by
  have hgate := hsat.rowConstraints 0 (by simp [traceOf])
    (always acceptBody) accept_constraint_mem
  simpa [always, VmConstraint2.holdsAt, WindowConstraint.holdsAt,
    acceptBody, WindowExpr.eval, traceOf, envAt] using hgate

/-- Certified soundness of the live BabyBear acceptance gate. -/
theorem trace_sound (hash : List Int -> Int) (table : ThreeEntryTable)
    (cert : LiveProjectionCertificate table)
    (hsat : Satisfied2 hash compileDescriptor (fun _ => 0)
      (fun _ => ((0 : Int), 0)) [] (traceOf table)) :
    Holds (sourceValuation table) 0 successorSkolemFormula := by
  have hmod := accepting_trace_modEq_zero hsat
  rw [Int.modEq_zero_iff_dvd] at hmod
  have hnum : residualNumerator table = 0 := by
    apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hmod
    simpa using cert.numeratorNoWrap
  rw [holds_iff_entries]
  intro j
  have hs0 : 0 <= (table.output 0 - table.input 0 - 1) ^ 2 := sq_nonneg _
  have hs1 : 0 <= (table.output 1 - table.input 1 - 1) ^ 2 := sq_nonneg _
  have hs2 : 0 <= (table.output 2 - table.input 2 - 1) ^ 2 := sq_nonneg _
  simp only [residualNumerator] at hnum
  have hz0 : (table.output 0 - table.input 0 - 1) ^ 2 = 0 := by omega
  have hz1 : (table.output 1 - table.input 1 - 1) ^ 2 = 0 := by omega
  have hz2 : (table.output 2 - table.input 2 - 1) ^ 2 = 0 := by omega
  have hd0 := sq_eq_zero_iff.mp hz0
  have hd1 := sq_eq_zero_iff.mp hz1
  have hd2 := sq_eq_zero_iff.mp hz2
  fin_cases j
  · change table.output 0 = table.input 0 + 1
    omega
  · change table.output 1 = table.input 1 + 1
    omega
  · change table.output 2 = table.input 2 + 1
    omega

/-- **Exact live compiler theorem.**  Under the exported no-wrap projection
certificate, the constructive IR-v2 trace accepts iff the ordinary bounded
matrix formula holds. -/
theorem trace_satisfied_iff_holds (hash : List Int -> Int)
    (table : ThreeEntryTable)
    (cert : LiveProjectionCertificate table) :
    Satisfied2 hash compileDescriptor (fun _ => 0)
        (fun _ => ((0 : Int), 0)) [] (traceOf table) <->
      Holds (sourceValuation table) 0 successorSkolemFormula := by
  exact ⟨trace_sound hash table cert, trace_complete hash table⟩

/-! ## 6. Successor witness and refusal cases -/

def successorEntries : ThreeEntryTable where
  input j := j.1
  output j := j.1 + 1

theorem successorEntries_cell (row : Fin 2) (col : Fin 3) :
    (sourceMatrix successorEntries).cell row col =
      successorTable.cell row col := by
  fin_cases row <;> fin_cases col <;> rfl

theorem successorEntries_holds :
    Holds (sourceValuation successorEntries) 0 successorSkolemFormula := by
  rw [holds_iff_entries]
  intro j
  rfl

def successorLiveCertificate : LiveProjectionCertificate successorEntries := by
  refine ⟨babyBear_prime, ?_⟩
  norm_num [residualNumerator, successorEntries]

/-- Constructive live witness for the canonical successor table. -/
theorem successor_trace_satisfies (hash : List Int -> Int) :
    Satisfied2 hash compileDescriptor (fun _ => 0)
      (fun _ => ((0 : Int), 0)) [] (traceOf successorEntries) :=
  trace_complete hash successorEntries successorEntries_holds

/-- One altered output entry. -/
def tamperedEntries : ThreeEntryTable where
  input
    | 0 => 0
    | 1 => 1
    | 2 => 2
  output
    | 0 => 2
    | 1 => 2
    | 2 => 3

theorem tamperedEntries_not_holds :
    ¬ Holds (sourceValuation tamperedEntries) 0 successorSkolemFormula := by
  rw [holds_iff_entries]
  intro h
  have h0 := h 0
  norm_num [tamperedEntries] at h0

def tamperedLiveCertificate : LiveProjectionCertificate tamperedEntries := by
  refine ⟨babyBear_prime, ?_⟩
  norm_num [residualNumerator, tamperedEntries]

/-- The live relation refuses the one-cell tamper. -/
theorem tampered_trace_refused (hash : List Int -> Int) :
    ¬ Satisfied2 hash compileDescriptor (fun _ => 0)
      (fun _ => ((0 : Int), 0)) [] (traceOf tamperedEntries) := by
  intro hsat
  exact tamperedEntries_not_holds
    (trace_sound hash tamperedEntries tamperedLiveCertificate hsat)

/-- The unchecked modulus-five counterexample cannot enter this compiler: its
projection certificate is uninhabited.  Live IR-v2 is BabyBear-fixed. -/
theorem bad_prime_projection_refused :
    ¬ FormulaProjectionCertificate successorValuation 0 badPrimeFormula 5 :=
  badPrime_certificate_rejected

/-- The bad modulus is not the live descriptor field. -/
theorem modulus_five_is_not_live : (5 : Nat) ≠ 2013265921 := by decide

#assert_all_clean [sourceMatrix_input, sourceMatrix_output, holds_iff_entries,
  twiceCoefficients_eval, accept_constraint_mem, traceOf_loc, rowOf_input,
  rowOf_output, rowOf_inputCoefficient, rowOf_outputCoefficient,
  rowOf_residual, rowOf_numerator, rowOf_denominator,
  memLog_compileDescriptor, mapLog_compileDescriptor, trace_complete,
  accepting_trace_modEq_zero, trace_sound, trace_satisfied_iff_holds,
  successorEntries_cell, successorEntries_holds,
  successor_trace_satisfies, tamperedEntries_not_holds,
  tampered_trace_refused, bad_prime_projection_refused,
  modulus_five_is_not_live]

end Dregg2.Metatheory.GabbayDescriptorIR2
