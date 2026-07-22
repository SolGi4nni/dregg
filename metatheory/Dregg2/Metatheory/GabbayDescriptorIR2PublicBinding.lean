/-
# A public-statement-bound Gabbay table relation in live descriptor IR-v2

`GabbayDescriptorIR2` constructs a sound witness for a fixed two-by-three
table, but its descriptor has no public inputs.  This module closes that
statement boundary with the smallest honest construction: all six claimed
table cells are direct public inputs, pinned to the first trace row, and one
always-on polynomial checks the three successor equations.

This is deliberately a *direct-table* construction.  It makes no interpolation
performance claim: there are no coefficient columns and interpolation is not
part of logical acceptance.  The benefit is instead exact and auditable:

* six public cells, six trace columns, seven constraints;
* three nonlinear multiplications (the three squares);
* no hash site, commitment assumption, coefficient witness, or denominator;
* the whole table is public, so this variant provides integrity but no table
  privacy.

The main theorem is statement-level rather than witness-specific.  Under the
same explicit BabyBear no-wrap certificate as the source compiler, an
arbitrary nonempty canonical trace satisfies the public descriptor for a
claimed table iff that external table satisfies the source `Holds` semantics.
The canonical-representative premise is necessary because `Satisfied2` models
field equality by integer congruence; deployed field serialization supplies
exactly this boundary condition.
-/

import Dregg2.Metatheory.GabbayDescriptorIR2PublicBoundary

namespace Dregg2.Metatheory.GabbayDescriptorIR2PublicBinding

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)
open Dregg2.Metatheory.GabbayMatrixSemantics
open Dregg2.Metatheory.GabbayDescriptorIR2

set_option autoImplicit false

/-! ## 1. Direct public layout -/

def BABYBEAR_MODULUS : Int := 2013265921

def inputPi (j : Fin 3) : Nat := j.1
def outputPi (j : Fin 3) : Nat := 3 + j.1

def PUBLIC_INPUT_COUNT : Nat := 6
def TRACE_WIDTH : Nat := 6

/-- Stable public layout: the input row first, then the output row. -/
def publicLayout : List (Nat × Nat) :=
  [(inputCol 0, inputPi 0), (inputCol 1, inputPi 1),
   (inputCol 2, inputPi 2), (outputCol 0, outputPi 0),
   (outputCol 1, outputPi 1), (outputCol 2, outputPi 2)]

#guard publicLayout == [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5)]

/-- The six field elements sent to the verifier. -/
def publicOf (table : ThreeEntryTable) : Assignment
  | 0 => table.input 0
  | 1 => table.input 1
  | 2 => table.input 2
  | 3 => table.output 0
  | 4 => table.output 1
  | 5 => table.output 2
  | _ => 0

@[simp] theorem publicOf_input (table : ThreeEntryTable) (j : Fin 3) :
    publicOf table (inputPi j) = table.input j := by
  fin_cases j <;> rfl

@[simp] theorem publicOf_output (table : ThreeEntryTable) (j : Fin 3) :
    publicOf table (outputPi j) = table.output j := by
  fin_cases j <;> rfl

/-- The public vector decodes back to exactly the externally claimed table. -/
def tableOfPublic (pub : Assignment) : ThreeEntryTable where
  input j := pub (inputPi j)
  output j := pub (outputPi j)

@[simp] theorem tableOfPublic_publicOf (table : ThreeEntryTable) :
    tableOfPublic (publicOf table) = table := by
  cases table with
  | mk input output =>
      simp only [tableOfPublic]
      congr
      · funext j
        exact publicOf_input { input := input, output := output } j
      · funext j
        exact publicOf_output { input := input, output := output } j

/-! ## 2. One direct logical polynomial -/

/-- One direct residual square.  No interpolation coefficient appears here. -/
def directResidual (j : Fin 3) : WindowExpr :=
  squareW (subW (subW (.loc (outputCol j)) (.loc (inputCol j))) (.const 1))

/-- The acceptance polynomial is exactly the sum of the three residual
squares.  This is the logical use of the public table. -/
def directAcceptBody : WindowExpr :=
  .add (.add (directResidual 0) (directResidual 1)) (directResidual 2)

def publicPins : List VmConstraint2 :=
  [ .base (.piBinding .first (inputCol 0) (inputPi 0))
  , .base (.piBinding .first (inputCol 1) (inputPi 1))
  , .base (.piBinding .first (inputCol 2) (inputPi 2))
  , .base (.piBinding .first (outputCol 0) (outputPi 0))
  , .base (.piBinding .first (outputCol 1) (outputPi 1))
  , .base (.piBinding .first (outputCol 2) (outputPi 2)) ]

def publicConstraints : List VmConstraint2 :=
  publicPins ++ [always directAcceptBody]

/-- Live IR-v2 descriptor for the public two-by-three table statement. -/
def publicDescriptor : EffectVmDescriptor2 :=
  { name := "dregg-gabbay-public-three-entry-direct-v2"
  , traceWidth := TRACE_WIDTH
  , piCount := PUBLIC_INPUT_COUNT
  , tables := [mainTableDef TRACE_WIDTH]
  , constraints := publicConstraints
  , hashSites := []
  , ranges := [] }

theorem public_pin_mem {pin : VmConstraint2} (hpin : pin ∈ publicPins) :
    pin ∈ publicDescriptor.constraints := by
  simp [publicDescriptor, publicConstraints, hpin]

theorem direct_accept_mem :
    always directAcceptBody ∈ publicDescriptor.constraints := by
  simp [publicDescriptor, publicConstraints]

/-- Exact public surface: six direct PIs and no commitment or range carrier. -/
theorem descriptor_public_surface_exact :
    publicDescriptor.piCount = 6 /\
      publicDescriptor.hashSites = [] /\
      publicDescriptor.ranges = [] /\
      publicDescriptor.traceWidth = 6 /\
      publicDescriptor.constraints.length = 7 := by
  decide

/-! ## 3. Exact cost and privacy accounting -/

def totalMulNodes : WindowExpr -> Nat
  | .loc _ | .nxt _ | .const _ => 0
  | .add a b => totalMulNodes a + totalMulNodes b
  | .mul a b => 1 + totalMulNodes a + totalMulNodes b

/-- Count only multiplications where neither top-level operand is a constant.
The three residual squares are the only nonlinear products. -/
def nonlinearMulNodes : WindowExpr -> Nat
  | .loc _ | .nxt _ | .const _ => 0
  | .add a b => nonlinearMulNodes a + nonlinearMulNodes b
  | .mul (.const _) b => nonlinearMulNodes b
  | .mul a (.const _) => nonlinearMulNodes a
  | .mul a b => 1 + nonlinearMulNodes a + nonlinearMulNodes b

structure DirectPublicCost where
  publicInputs : Nat
  traceColumns : Nat
  constraints : Nat
  totalMulNodes : Nat
  nonlinearMulNodes : Nat
  privateTableCells : Nat
  interpolationCoefficients : Nat
  deriving Repr, DecidableEq

def directPublicCost : DirectPublicCost :=
  { publicInputs := publicDescriptor.piCount
  , traceColumns := publicDescriptor.traceWidth
  , constraints := publicDescriptor.constraints.length
  , totalMulNodes := totalMulNodes directAcceptBody
  , nonlinearMulNodes := nonlinearMulNodes directAcceptBody
  , privateTableCells := 0
  , interpolationCoefficients := 0 }

theorem direct_public_cost_exact :
    directPublicCost =
      { publicInputs := 6, traceColumns := 6, constraints := 7,
        totalMulNodes := 15, nonlinearMulNodes := 3,
        privateTableCells := 0, interpolationCoefficients := 0 } := by
  decide

/-- Privacy accounting is exact: observing the public inputs determines every
table cell, so this integrity construction hides no part of the model. -/
theorem public_statement_reveals_whole_table (left right : ThreeEntryTable)
    (hpub : publicOf left = publicOf right) : left = right := by
  rw [<- tableOfPublic_publicOf left, <- tableOfPublic_publicOf right, hpub]

/-! ## 4. Constructive witness -/

def directRowOf (table : ThreeEntryTable) : Assignment
  | 0 => table.input 0
  | 1 => table.input 1
  | 2 => table.input 2
  | 3 => table.output 0
  | 4 => table.output 1
  | 5 => table.output 2
  | _ => 0

def directTraceOf (table : ThreeEntryTable) : VmTrace :=
  { rows := [directRowOf table], pub := publicOf table, tf := fun _ => [] }

@[simp] theorem directTraceOf_loc (table : ThreeEntryTable) :
    (envAt (directTraceOf table) 0).loc = directRowOf table := by
  simp [envAt, directTraceOf]

@[simp] theorem directRowOf_input (table : ThreeEntryTable) (j : Fin 3) :
    directRowOf table (inputCol j) = table.input j := by
  fin_cases j <;> rfl

@[simp] theorem directRowOf_output (table : ThreeEntryTable) (j : Fin 3) :
    directRowOf table (outputCol j) = table.output j := by
  fin_cases j <;> rfl

theorem directAcceptBody_eval (table : ThreeEntryTable) :
    directAcceptBody.eval (envAt (directTraceOf table) 0) =
      residualNumerator table := by
  simp [directAcceptBody, directResidual, squareW, subW, negW,
    WindowExpr.eval, directTraceOf_loc, residualNumerator, pow_two]
  ring

theorem memLog_publicDescriptor (trace : VmTrace) :
    memLog publicDescriptor trace = [] := by
  simp [memLog, memOpsOf, publicDescriptor, publicConstraints, publicPins, always]

theorem mapLog_publicDescriptor (trace : VmTrace) :
    mapLog publicDescriptor trace = [] := by
  simp [mapLog, mapOpsOf, publicDescriptor, publicConstraints, publicPins, always]

/-- Source truth constructs the complete public-input-bound live trace. -/
theorem direct_trace_complete (hash : List Int -> Int) (table : ThreeEntryTable)
    (hholds : Holds (sourceValuation table) 0 successorSkolemFormula) :
    Satisfied2 hash publicDescriptor (fun _ => 0)
      (fun _ => ((0 : Int), 0)) [] (directTraceOf table) := by
  have hentries := (holds_iff_entries table).1 hholds
  have hres : residualNumerator table = 0 := by
    simp [residualNumerator, hentries 0, hentries 1, hentries 2]
  refine ⟨?_, ?_, ?_, List.nodup_nil, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi c hc
    have hi0 : i = 0 := by simp [directTraceOf] at hi; omega
    subst i
    simp only [publicDescriptor] at hc
    simp only [publicConstraints, publicPins, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    · simp [VmConstraint2.holdsAt, directTraceOf, envAt, publicOf,
        directRowOf, inputCol, inputPi]
    · simp [VmConstraint2.holdsAt, directTraceOf, envAt, publicOf,
        directRowOf, inputCol, inputPi]
    · simp [VmConstraint2.holdsAt, directTraceOf, envAt, publicOf,
        directRowOf, inputCol, inputPi]
    · simp [VmConstraint2.holdsAt, directTraceOf, envAt, publicOf,
        directRowOf, outputCol, outputPi]
    · simp [VmConstraint2.holdsAt, directTraceOf, envAt, publicOf,
        directRowOf, outputCol, outputPi]
    · simp [VmConstraint2.holdsAt, directTraceOf, envAt, publicOf,
        directRowOf, outputCol, outputPi]
    · simp only [VmConstraint2.holdsAt, always, WindowConstraint.holdsAt,
        Bool.false_eq_true, if_false]
      rw [directAcceptBody_eval, hres]
  · intro i hi
    trivial
  · intro i hi r hr
    simp [publicDescriptor] at hr
  · intro op hop
    rw [memLog_publicDescriptor] at hop
    cases hop
  · rw [memLog_publicDescriptor]
    trivial
  · rw [memLog_publicDescriptor]
    exact memCheck_nil _ _
  · rw [memLog_publicDescriptor]
    rfl
  · rw [mapLog_publicDescriptor]
    rfl

/-! ## 5. Public binding for arbitrary traces -/

/-- Canonical integer representatives for the six externally claimed cells. -/
def CanonicalTable (table : ThreeEntryTable) : Prop :=
  (∀ j, 0 <= table.input j /\ table.input j < BABYBEAR_MODULUS) /\
  (∀ j, 0 <= table.output j /\ table.output j < BABYBEAR_MODULUS)

/-- Canonical integer representatives for the six bound columns of row zero. -/
def CanonicalFirstRow (trace : VmTrace) : Prop :=
  (∀ j, 0 <= (envAt trace 0).loc (inputCol j) /\
    (envAt trace 0).loc (inputCol j) < BABYBEAR_MODULUS) /\
  (∀ j, 0 <= (envAt trace 0).loc (outputCol j) /\
    (envAt trace 0).loc (outputCol j) < BABYBEAR_MODULUS)

/-- Replace only the verifier-visible statement; the prover's rows and tables
remain arbitrary. -/
def withPublic (claim : ThreeEntryTable) (trace : VmTrace) : VmTrace :=
  { trace with pub := publicOf claim }

/-- The exact statement relation used below.  Nonemptiness is explicit because
the abstract `Satisfied2` carrier permits an empty list, whereas an AIR trace
has at least one row. -/
def StatementSatisfied (hash : List Int -> Int) (claim : ThreeEntryTable)
    (trace : VmTrace) : Prop :=
  trace.rows ≠ [] /\ CanonicalFirstRow trace /\
    Satisfied2 hash publicDescriptor (fun _ => 0)
      (fun _ => ((0 : Int), 0)) [] (withPublic claim trace)

/-- Two canonical representatives of one BabyBear residue are equal. -/
theorem eq_of_modEq_of_canonical {x y : Int}
    (hmod : x ≡ y [ZMOD 2013265921])
    (hx : 0 <= x /\ x < BABYBEAR_MODULUS)
    (hy : 0 <= y /\ y < BABYBEAR_MODULUS) : x = y := by
  obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp hmod
  simp only [BABYBEAR_MODULUS] at hk hx hy
  omega

theorem input_pin_field_binding {hash : List Int -> Int}
    {claim : ThreeEntryTable} {trace : VmTrace}
    (hne : trace.rows ≠ [])
    (hsat : Satisfied2 hash publicDescriptor (fun _ => 0)
      (fun _ => ((0 : Int), 0)) [] (withPublic claim trace))
    (j : Fin 3) :
    (envAt trace 0).loc (inputCol j) ≡ claim.input j [ZMOD 2013265921] := by
  have hpos : 0 < (withPublic claim trace).rows.length := by
    simp [withPublic]
    exact List.length_pos_iff.mpr hne
  have h := hsat.rowConstraints 0 hpos
    (.base (.piBinding .first (inputCol j) (inputPi j)))
    (public_pin_mem (by fin_cases j <;> simp [publicPins]))
  simpa [VmConstraint2.holdsAt, withPublic, envAt] using h

theorem output_pin_field_binding {hash : List Int -> Int}
    {claim : ThreeEntryTable} {trace : VmTrace}
    (hne : trace.rows ≠ [])
    (hsat : Satisfied2 hash publicDescriptor (fun _ => 0)
      (fun _ => ((0 : Int), 0)) [] (withPublic claim trace))
    (j : Fin 3) :
    (envAt trace 0).loc (outputCol j) ≡ claim.output j [ZMOD 2013265921] := by
  have hpos : 0 < (withPublic claim trace).rows.length := by
    simp [withPublic]
    exact List.length_pos_iff.mpr hne
  have h := hsat.rowConstraints 0 hpos
    (.base (.piBinding .first (outputCol j) (outputPi j)))
    (public_pin_mem (by fin_cases j <;> simp [publicPins]))
  simpa [VmConstraint2.holdsAt, withPublic, envAt] using h

theorem input_pin_exact {hash : List Int -> Int}
    {claim : ThreeEntryTable} {trace : VmTrace}
    (hclaim : CanonicalTable claim) (hrow : CanonicalFirstRow trace)
    (hne : trace.rows ≠ [])
    (hsat : Satisfied2 hash publicDescriptor (fun _ => 0)
      (fun _ => ((0 : Int), 0)) [] (withPublic claim trace))
    (j : Fin 3) :
    (envAt trace 0).loc (inputCol j) = claim.input j :=
  eq_of_modEq_of_canonical (input_pin_field_binding hne hsat j)
    (hrow.1 j) (hclaim.1 j)

theorem output_pin_exact {hash : List Int -> Int}
    {claim : ThreeEntryTable} {trace : VmTrace}
    (hclaim : CanonicalTable claim) (hrow : CanonicalFirstRow trace)
    (hne : trace.rows ≠ [])
    (hsat : Satisfied2 hash publicDescriptor (fun _ => 0)
      (fun _ => ((0 : Int), 0)) [] (withPublic claim trace))
    (j : Fin 3) :
    (envAt trace 0).loc (outputCol j) = claim.output j :=
  eq_of_modEq_of_canonical (output_pin_field_binding hne hsat j)
    (hrow.2 j) (hclaim.2 j)

/-- The direct acceptance gate of any nonempty satisfying trace reduces to the
claimed table's exact residual, once the six field pins are canonically decoded. -/
theorem claimed_residual_modEq_zero {hash : List Int -> Int}
    {claim : ThreeEntryTable} {trace : VmTrace}
    (hclaim : CanonicalTable claim) (hrow : CanonicalFirstRow trace)
    (hne : trace.rows ≠ [])
    (hsat : Satisfied2 hash publicDescriptor (fun _ => 0)
      (fun _ => ((0 : Int), 0)) [] (withPublic claim trace)) :
    residualNumerator claim ≡ 0 [ZMOD 2013265921] := by
  have hpos : 0 < (withPublic claim trace).rows.length := by
    simp [withPublic]
    exact List.length_pos_iff.mpr hne
  have hgate := hsat.rowConstraints 0 hpos
    (always directAcceptBody) direct_accept_mem
  have hi0 := input_pin_exact hclaim hrow hne hsat (0 : Fin 3)
  have hi1 := input_pin_exact hclaim hrow hne hsat (1 : Fin 3)
  have hi2 := input_pin_exact hclaim hrow hne hsat (2 : Fin 3)
  have ho0 := output_pin_exact hclaim hrow hne hsat (0 : Fin 3)
  have ho1 := output_pin_exact hclaim hrow hne hsat (1 : Fin 3)
  have ho2 := output_pin_exact hclaim hrow hne hsat (2 : Fin 3)
  simp only [withPublic, envAt] at hi0 hi1 hi2 ho0 ho1 ho2 hgate
  simpa [always, VmConstraint2.holdsAt, WindowConstraint.holdsAt,
    directAcceptBody, directResidual, squareW, subW, negW, WindowExpr.eval,
    residualNumerator, pow_two, hi0, hi1, hi2, ho0, ho1, ho2] using hgate

theorem holds_of_residual_zero (table : ThreeEntryTable)
    (hzero : residualNumerator table = 0) :
    Holds (sourceValuation table) 0 successorSkolemFormula := by
  rw [holds_iff_entries]
  intro j
  have hs0 : 0 <= (table.output 0 - table.input 0 - 1) ^ 2 := sq_nonneg _
  have hs1 : 0 <= (table.output 1 - table.input 1 - 1) ^ 2 := sq_nonneg _
  have hs2 : 0 <= (table.output 2 - table.input 2 - 1) ^ 2 := sq_nonneg _
  simp only [residualNumerator] at hzero
  have hz0 : (table.output 0 - table.input 0 - 1) ^ 2 = 0 := by omega
  have hz1 : (table.output 1 - table.input 1 - 1) ^ 2 = 0 := by omega
  have hz2 : (table.output 2 - table.input 2 - 1) ^ 2 = 0 := by omega
  have he0 : table.output 0 = table.input 0 + 1 := by
    have hd := sq_eq_zero_iff.mp hz0
    omega
  have he1 : table.output 1 = table.input 1 + 1 := by
    have hd := sq_eq_zero_iff.mp hz1
    omega
  have he2 : table.output 2 = table.input 2 + 1 := by
    have hd := sq_eq_zero_iff.mp hz2
    omega
  fin_cases j
  · exact he0
  · exact he1
  · exact he2

/-- Soundness for an arbitrary satisfying witness: the public statement, not a
prover-selected hidden table, is what `Holds`. -/
theorem statement_sound (hash : List Int -> Int) (claim : ThreeEntryTable)
    (cert : LiveProjectionCertificate claim) (hclaim : CanonicalTable claim)
    (trace : VmTrace) (hs : StatementSatisfied hash claim trace) :
    Holds (sourceValuation claim) 0 successorSkolemFormula := by
  rcases hs with ⟨hne, hrow, hsat⟩
  have hmod := claimed_residual_modEq_zero hclaim hrow hne hsat
  rw [Int.modEq_zero_iff_dvd] at hmod
  have hzero : residualNumerator claim = 0 := by
    apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hmod
    simpa using cert.numeratorNoWrap
  exact holds_of_residual_zero claim hzero

/-- A canonical true public statement has a constructive live witness. -/
theorem statement_complete (hash : List Int -> Int) (claim : ThreeEntryTable)
    (hclaim : CanonicalTable claim)
    (hholds : Holds (sourceValuation claim) 0 successorSkolemFormula) :
    StatementSatisfied hash claim (directTraceOf claim) := by
  refine ⟨by simp [directTraceOf], ?_, ?_⟩
  · constructor <;> intro j
    · simpa [directTraceOf, envAt] using hclaim.1 j
    · simpa [directTraceOf, envAt] using hclaim.2 j
  · simpa [withPublic, directTraceOf] using direct_trace_complete hash claim hholds

/-- **Exact external statement theorem.**  Existence of an arbitrary canonical
satisfying trace is equivalent to truth of the named public table. -/
theorem public_statement_satisfied_iff_holds (hash : List Int -> Int)
    (claim : ThreeEntryTable) (cert : LiveProjectionCertificate claim)
    (hclaim : CanonicalTable claim) :
    (∃ trace, StatementSatisfied hash claim trace) <->
      Holds (sourceValuation claim) 0 successorSkolemFormula := by
  constructor
  · rintro ⟨trace, hs⟩
    exact statement_sound hash claim cert hclaim trace hs
  · intro hholds
    exact ⟨directTraceOf claim, statement_complete hash claim hclaim hholds⟩

/-! ## 6. Concrete positive and tamper polarities -/

theorem successorEntries_canonical : CanonicalTable successorEntries := by
  constructor <;> intro j <;> fin_cases j <;> norm_num [successorEntries,
    BABYBEAR_MODULUS]

theorem successor_public_statement_has_witness (hash : List Int -> Int) :
    ∃ trace, StatementSatisfied hash successorEntries trace :=
  (public_statement_satisfied_iff_holds hash successorEntries
    successorLiveCertificate successorEntries_canonical).2 successorEntries_holds

theorem tamperedEntries_canonical : CanonicalTable tamperedEntries := by
  constructor <;> intro j <;> fin_cases j <;> norm_num [tamperedEntries,
    BABYBEAR_MODULUS]

/-- A one-cell change to the public statement has no satisfying canonical
witness.  This rejects the external tamper, not merely a preselected trace. -/
theorem tampered_public_statement_refused (hash : List Int -> Int) :
    ¬ (∃ trace, StatementSatisfied hash tamperedEntries trace) := by
  intro hex
  exact tamperedEntries_not_holds
    ((public_statement_satisfied_iff_holds hash tamperedEntries
      tamperedLiveCertificate tamperedEntries_canonical).1 hex)

/-! ## 7. Exact wire bytes -/

/-- The canonical byte string is pinned below after the definition, so changing
the PI order, field count, gate expression, or descriptor name is a proof-visible
wire change. -/
def publicDescriptorBytes : String := emitVmJson2 publicDescriptor

#guard publicDescriptorBytes ==
  "{\"name\":\"dregg-gabbay-public-three-entry-direct-v2\",\"ir\":2,\"trace_width\":6,\"public_input_count\":6,\"tables\":[{\"id\":0,\"name\":\"main\",\"arity\":6,\"sem\":\"main\"}],\"constraints\":[{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":0,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":1,\"pi_index\":1},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":2,\"pi_index\":2},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":3,\"pi_index\":3},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":4,\"pi_index\":4},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":5,\"pi_index\":5},{\"t\":\"window_gate\",\"on_transition\":false,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":0}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"const\",\"v\":1}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":0}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"const\",\"v\":1}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":4},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":1}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"const\",\"v\":1}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":4},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":1}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"const\",\"v\":1}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":5},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":2}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"const\",\"v\":1}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":5},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":2}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"const\",\"v\":1}}}}}}],\"hash_sites\":[],\"ranges\":[]}"

#assert_all_clean [
  publicOf_input, publicOf_output, tableOfPublic_publicOf,
  public_pin_mem, direct_accept_mem, descriptor_public_surface_exact,
  direct_public_cost_exact, public_statement_reveals_whole_table,
  directTraceOf_loc, directRowOf_input, directRowOf_output,
  directAcceptBody_eval, memLog_publicDescriptor, mapLog_publicDescriptor,
  direct_trace_complete, eq_of_modEq_of_canonical,
  input_pin_field_binding, output_pin_field_binding,
  input_pin_exact, output_pin_exact, claimed_residual_modEq_zero,
  holds_of_residual_zero, statement_sound, statement_complete,
  public_statement_satisfied_iff_holds, successorEntries_canonical,
  successor_public_statement_has_witness, tamperedEntries_canonical,
  tampered_public_statement_refused
]

end Dregg2.Metatheory.GabbayDescriptorIR2PublicBinding
