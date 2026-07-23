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

* six public cells, six trace columns, fifteen constraints — six PI pins,
  three acceptance atoms, six graduated range teeth;
* ZERO nonlinear multiplications — acceptance is three linear atoms;
* no hash site, commitment assumption, coefficient witness, or denominator;
* the whole table is public, so this variant provides integrity but no table
  privacy.

Acceptance used to be the single polynomial `sum of three squared residuals`,
sound only under a Lean-side `LiveProjectionCertificate` bounding the integer
numerator.  That premise was never serialized, so the emitted bytes did not
enforce what made them sound, and a fully canonical FALSE table was accepted:
`284861408 ^ 2 = -1` in BabyBear, so `1 ^ 2 + 284861408 ^ 2 + 0 ^ 2 = 0` in
the field.  Acceptance is now three LINEAR atoms plus a 30-bit range LOOKUP on
each of the six bound columns, both of which ARE serialized — and the lookup
form is the one the deployed assembly actually realizes (byte-limb
decomposition at the width pinned by the committed table id), not the v1
`ranges` carrier it refuses outright.  The teeth also discharge the old
`CanonicalFirstRow` trace premise: an accepting first row is 30-bit, hence
canonical, by the descriptor's own check.
`Dregg2.Verify.DirectLogicAdversarialFalsifierV2` keeps the cancellation table
as a live regression canary and now proves it REJECTED.

The main theorem is statement-level rather than witness-specific: an arbitrary
nonempty trace satisfies the public descriptor for a claimed table iff that
external table satisfies the source `Holds` semantics.  Two boundary
conditions remain, both named exactly.  (1) The claimed cells are canonical
integer representatives — `Satisfied2` models field equality by integer
congruence, and deployed field serialization supplies exactly this decoding
convention; it is a statement about how the six public field elements are
READ, not an arithmetic side condition on the witness.  (2) The witness is
structural: a nonempty row list (the abstract `Satisfied2` carrier admits an
empty one, on which every row-indexed obligation is vacuous, whereas a deployed
AIR trace always has at least one row) carrying the honest range table (what a
range lookup is a lookup INTO; the deployed assembly builds it rather than
reading it from the prover).  Neither is expressible as a gate: no descriptor
byte can constrain a row that does not exist, and a lookup cannot bootstrap the
table it looks into.
-/

import Dregg2.Metatheory.GabbayDescriptorIR2PublicBoundary

namespace Dregg2.Metatheory.GabbayDescriptorIR2PublicBinding

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv VmRange)
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

/-! ## 2. Three direct logical atoms -/

/-- One direct successor atom, as a LINEAR gate.  No interpolation coefficient
and no square appears here: a field sum of squares is not a conjunction, so
each equation gets its own gate. -/
def directAtom (j : Fin 3) : WindowExpr :=
  subW (subW (.loc (outputCol j)) (.loc (inputCol j))) (.const 1)

def publicPins : List VmConstraint2 :=
  [ .base (.piBinding .first (inputCol 0) (inputPi 0))
  , .base (.piBinding .first (inputCol 1) (inputPi 1))
  , .base (.piBinding .first (inputCol 2) (inputPi 2))
  , .base (.piBinding .first (outputCol 0) (outputPi 0))
  , .base (.piBinding .first (outputCol 1) (outputPi 1))
  , .base (.piBinding .first (outputCol 2) (outputPi 2)) ]

def publicAtoms : List VmConstraint2 :=
  [always (directAtom 0), always (directAtom 1), always (directAtom 2)]

/-- The emitted no-wrap teeth, in the GRADUATED v2 form: a 30-bit range LOOKUP
on each of the six bound columns, against the declared shared range table.
This is the serialized form of what the retired `LiveProjectionCertificate`
and the retired `CanonicalFirstRow` trace premise merely asserted in Lean.

Graduated rather than the v1 `ranges` carrier because the deployed assembly
refuses a v2 descriptor that carries the v1 form at all, while a range lookup
it lowers to a real byte-limb decomposition at the width pinned by the
committed table id. -/
def publicRangeLookups : List VmConstraint2 :=
  [ rangeLookup (inputCol 0), rangeLookup (inputCol 1), rangeLookup (inputCol 2)
  , rangeLookup (outputCol 0), rangeLookup (outputCol 1)
  , rangeLookup (outputCol 2) ]

def publicConstraints : List VmConstraint2 :=
  publicPins ++ publicAtoms ++ publicRangeLookups

/-- Live IR-v2 descriptor for the public two-by-three table statement. -/
def publicDescriptor : EffectVmDescriptor2 :=
  { name := "dregg-gabbay-public-three-entry-direct-v2"
  , traceWidth := TRACE_WIDTH
  , piCount := PUBLIC_INPUT_COUNT
  , tables := [mainTableDef TRACE_WIDTH, rangeTableDef WIRE_BITS]
  , constraints := publicConstraints
  , hashSites := []
  , ranges := [] }

theorem public_pin_mem {pin : VmConstraint2} (hpin : pin ∈ publicPins) :
    pin ∈ publicDescriptor.constraints := by
  simp [publicDescriptor, publicConstraints, hpin]

theorem direct_atom_mem (j : Fin 3) :
    always (directAtom j) ∈ publicDescriptor.constraints := by
  fin_cases j <;> simp [publicDescriptor, publicConstraints, publicAtoms]

theorem public_input_range_mem (j : Fin 3) :
    rangeLookup (inputCol j) ∈ publicDescriptor.constraints := by
  fin_cases j <;>
    simp [publicDescriptor, publicConstraints, publicRangeLookups, rangeLookup]

theorem public_output_range_mem (j : Fin 3) :
    rangeLookup (outputCol j) ∈ publicDescriptor.constraints := by
  fin_cases j <;>
    simp [publicDescriptor, publicConstraints, publicRangeLookups, rangeLookup]

/-- Exact public surface: six direct PIs, no commitment carrier, no v1 range
carrier, and fifteen constraints — six pins, three linear atoms, and the six
graduated 30-bit teeth that carry the no-wrap condition on the wire. -/
theorem descriptor_public_surface_exact :
    publicDescriptor.piCount = 6 /\
      publicDescriptor.hashSites = [] /\
      publicDescriptor.ranges = [] /\
      publicDescriptor.tables.length = 2 /\
      publicDescriptor.traceWidth = 6 /\
      publicDescriptor.constraints.length = 15 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## 3. Exact cost and privacy accounting -/

def totalMulNodes : WindowExpr -> Nat
  | .loc _ | .nxt _ | .const _ => 0
  | .add a b => totalMulNodes a + totalMulNodes b
  | .mul a b => 1 + totalMulNodes a + totalMulNodes b

/-- Count only multiplications where neither top-level operand is a constant.
The live acceptance block has NONE: `directAtom` is
`out - in - 1`, whose only multiplications are the `-1` scalings introduced by
`subW`/`negW`, and both have a constant operand.  The retired sum-of-squares
gate is where the nonlinear products used to live: each squared residual was a
`.mul` of two non-constant operands, three in all
(`direct_public_cost_exact` records the repaired ledger `totalMulNodes = 6`,
`nonlinearMulNodes = 0`; the retired one was `15` and `3`). -/
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
  rangeTeeth : Nat
  totalMulNodes : Nat
  nonlinearMulNodes : Nat
  privateTableCells : Nat
  interpolationCoefficients : Nat
  deriving Repr, DecidableEq

/-- Multiplication cost of the whole acceptance block (all three atoms), not of
one polynomial: the retired single sum-of-squares gate hid its cost in one
body. -/
def acceptanceMulNodes : Nat :=
  totalMulNodes (directAtom 0) + totalMulNodes (directAtom 1) +
    totalMulNodes (directAtom 2)

def acceptanceNonlinearMulNodes : Nat :=
  nonlinearMulNodes (directAtom 0) + nonlinearMulNodes (directAtom 1) +
    nonlinearMulNodes (directAtom 2)

def directPublicCost : DirectPublicCost :=
  { publicInputs := publicDescriptor.piCount
  , traceColumns := publicDescriptor.traceWidth
  , constraints := publicDescriptor.constraints.length
  , rangeTeeth := publicRangeLookups.length
  , totalMulNodes := acceptanceMulNodes
  , nonlinearMulNodes := acceptanceNonlinearMulNodes
  , privateTableCells := 0
  , interpolationCoefficients := 0 }

/-- The linear repair is also the cheaper circuit: the three squared residuals
(15 multiplication nodes, 3 of them nonlinear) become 6 constant-scaling nodes
and NO nonlinear product, at the price of two extra gates and six graduated
range teeth (whose deployed byte-limb realization is the real added cost). -/
theorem direct_public_cost_exact :
    directPublicCost =
      { publicInputs := 6, traceColumns := 6, constraints := 15,
        rangeTeeth := 6, totalMulNodes := 6, nonlinearMulNodes := 0,
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
  { rows := [directRowOf table], pub := publicOf table, tf := traceTables }

theorem directTraceOf_honest_range (table : ThreeEntryTable) :
    HonestRangeTable (directTraceOf table) := by
  simp only [HonestRangeTable, directTraceOf, traceTables]

@[simp] theorem directTraceOf_loc (table : ThreeEntryTable) :
    (envAt (directTraceOf table) 0).loc = directRowOf table := by
  simp [envAt, directTraceOf]

@[simp] theorem directRowOf_input (table : ThreeEntryTable) (j : Fin 3) :
    directRowOf table (inputCol j) = table.input j := by
  fin_cases j <;> rfl

@[simp] theorem directRowOf_output (table : ThreeEntryTable) (j : Fin 3) :
    directRowOf table (outputCol j) = table.output j := by
  fin_cases j <;> rfl

/-- The acceptance atom of an arbitrary trace reads exactly the two bound
columns of its first row. -/
theorem directAtom_eval (trace : VmTrace) (j : Fin 3) :
    (directAtom j).eval (envAt trace 0) =
      (envAt trace 0).loc (outputCol j) - (envAt trace 0).loc (inputCol j) - 1 := by
  simp [directAtom, subW, negW, WindowExpr.eval]
  ring

theorem memLog_publicDescriptor (trace : VmTrace) :
    memLog publicDescriptor trace = [] := by
  simp [memLog, memOpsOf, publicDescriptor, publicConstraints, publicPins,
    publicAtoms, publicRangeLookups, rangeLookup, always]

theorem mapLog_publicDescriptor (trace : VmTrace) :
    mapLog publicDescriptor trace = [] := by
  simp [mapLog, mapOpsOf, publicDescriptor, publicConstraints, publicPins,
    publicAtoms, publicRangeLookups, rangeLookup, always]

/-- A wire-bounded public column really is a row of the honest range table. -/
theorem directInputRangeLookup_holds (table : ThreeEntryTable)
    (hbound : WireBoundedTable table) (j : Fin 3) :
    Lookup.holdsAt (directTraceOf table).tf (envAt (directTraceOf table) 0)
      ⟨.range, [.var (inputCol j)]⟩ :=
  lookup_range_complete WIRE_BITS _ (directTraceOf_honest_range table) _ _
    (by simpa [rangeHolds_def, directTraceOf_loc] using hbound.1 j)

theorem directOutputRangeLookup_holds (table : ThreeEntryTable)
    (hbound : WireBoundedTable table) (j : Fin 3) :
    Lookup.holdsAt (directTraceOf table).tf (envAt (directTraceOf table) 0)
      ⟨.range, [.var (outputCol j)]⟩ :=
  lookup_range_complete WIRE_BITS _ (directTraceOf_honest_range table) _ _
    (by simpa [rangeHolds_def, directTraceOf_loc] using hbound.2 j)

/-- Source truth on the wire-checked domain constructs the complete
public-input-bound live trace. -/
theorem direct_trace_complete (hash : List Int -> Int) (table : ThreeEntryTable)
    (hbound : WireBoundedTable table)
    (hholds : Holds (sourceValuation table) 0 successorSkolemFormula) :
    Satisfied2 hash publicDescriptor (fun _ => 0)
      (fun _ => ((0 : Int), 0)) [] (directTraceOf table) := by
  have hentries := (holds_iff_entries table).1 hholds
  refine ⟨?_, ?_, ?_, List.nodup_nil, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi c hc
    have hi0 : i = 0 := by simp [directTraceOf] at hi; omega
    subst i
    simp only [publicDescriptor] at hc
    simp only [publicConstraints, publicPins, publicAtoms, publicRangeLookups,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with ((rfl | rfl | rfl | rfl | rfl | rfl) |
      (rfl | rfl | rfl)) | (rfl | rfl | rfl | rfl | rfl | rfl)
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
      rw [directAtom_eval]
      simp only [directTraceOf_loc, directRowOf_input, directRowOf_output]
      rw [hentries 0]; simp
    · simp only [VmConstraint2.holdsAt, always, WindowConstraint.holdsAt,
        Bool.false_eq_true, if_false]
      rw [directAtom_eval]
      simp only [directTraceOf_loc, directRowOf_input, directRowOf_output]
      rw [hentries 1]; simp
    · simp only [VmConstraint2.holdsAt, always, WindowConstraint.holdsAt,
        Bool.false_eq_true, if_false]
      rw [directAtom_eval]
      simp only [directTraceOf_loc, directRowOf_input, directRowOf_output]
      rw [hentries 2]; simp
    · exact directInputRangeLookup_holds table hbound 0
    · exact directInputRangeLookup_holds table hbound 1
    · exact directInputRangeLookup_holds table hbound 2
    · exact directOutputRangeLookup_holds table hbound 0
    · exact directOutputRangeLookup_holds table hbound 1
    · exact directOutputRangeLookup_holds table hbound 2
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

/-- A 30-bit wire value is a canonical BabyBear representative. -/
theorem canonical_of_wire_bounded {x : Int}
    (h : 0 <= x /\ x < 2 ^ WIRE_BITS) : 0 <= x /\ x < BABYBEAR_MODULUS := by
  refine ⟨h.1, ?_⟩
  have := h.2
  simp only [WIRE_BITS] at this
  norm_num [BABYBEAR_MODULUS] at this ⊢
  omega

/-- The wire-checked domain implies canonicality of the claim. -/
theorem canonicalTable_of_wireBounded {claim : ThreeEntryTable}
    (h : WireBoundedTable claim) : CanonicalTable claim :=
  ⟨fun j => canonical_of_wire_bounded (h.1 j),
   fun j => canonical_of_wire_bounded (h.2 j)⟩

/-- Replace only the verifier-visible statement; the prover's rows and tables
remain arbitrary. -/
def withPublic (claim : ThreeEntryTable) (trace : VmTrace) : VmTrace :=
  { trace with pub := publicOf claim }

/-- The exact statement relation used below.  Two structural conjuncts remain,
and both are conditions on the WITNESS, not side conditions on the claim.

* Nonemptiness: the abstract `Satisfied2` carrier permits an empty row list,
  whereas an AIR trace has at least one row.  No descriptor byte can constrain
  a row that does not exist.
* `HonestRangeTable`: a range lookup is a membership in the trace family's
  range table, so the table has to be the real one.  The deployed assembly
  discharges this by BUILDING the byte-limb decomposition itself at the width
  pinned by the committed table id, rather than reading a prover-supplied
  table.

The former `CanonicalFirstRow` conjunct is gone: the descriptor's own teeth now
force it (`first_row_input_bounded` / `first_row_output_bounded`). -/
def StatementSatisfied (hash : List Int -> Int) (claim : ThreeEntryTable)
    (trace : VmTrace) : Prop :=
  trace.rows ≠ [] /\ HonestRangeTable trace /\
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

/-- **The retired `CanonicalFirstRow` premise, now a theorem.**  The
descriptor's own range teeth bound row zero's six bound columns to 30 bits. -/
theorem withPublic_honest_range {claim : ThreeEntryTable} {trace : VmTrace}
    (hrange : HonestRangeTable trace) :
    HonestRangeTable (withPublic claim trace) := by
  simpa [HonestRangeTable, withPublic] using hrange

theorem first_row_input_bounded {hash : List Int -> Int}
    {claim : ThreeEntryTable} {trace : VmTrace}
    (hne : trace.rows ≠ []) (hrange : HonestRangeTable trace)
    (hsat : Satisfied2 hash publicDescriptor (fun _ => 0)
      (fun _ => ((0 : Int), 0)) [] (withPublic claim trace))
    (j : Fin 3) :
    0 <= (envAt trace 0).loc (inputCol j) /\
      (envAt trace 0).loc (inputCol j) < 2 ^ WIRE_BITS := by
  have hpos : 0 < (withPublic claim trace).rows.length := by
    simp [withPublic]
    exact List.length_pos_iff.mpr hne
  have h := hsat.rowConstraints 0 hpos _ (public_input_range_mem j)
  have hb := lookup_replaces_range WIRE_BITS _
    (withPublic_honest_range hrange) _ _ h
  simpa [rangeHolds_def, withPublic, envAt] using hb

theorem first_row_output_bounded {hash : List Int -> Int}
    {claim : ThreeEntryTable} {trace : VmTrace}
    (hne : trace.rows ≠ []) (hrange : HonestRangeTable trace)
    (hsat : Satisfied2 hash publicDescriptor (fun _ => 0)
      (fun _ => ((0 : Int), 0)) [] (withPublic claim trace))
    (j : Fin 3) :
    0 <= (envAt trace 0).loc (outputCol j) /\
      (envAt trace 0).loc (outputCol j) < 2 ^ WIRE_BITS := by
  have hpos : 0 < (withPublic claim trace).rows.length := by
    simp [withPublic]
    exact List.length_pos_iff.mpr hne
  have h := hsat.rowConstraints 0 hpos _ (public_output_range_mem j)
  have hb := lookup_replaces_range WIRE_BITS _
    (withPublic_honest_range hrange) _ _ h
  simpa [rangeHolds_def, withPublic, envAt] using hb

theorem input_pin_exact {hash : List Int -> Int}
    {claim : ThreeEntryTable} {trace : VmTrace}
    (hclaim : CanonicalTable claim)
    (hne : trace.rows ≠ []) (hrange : HonestRangeTable trace)
    (hsat : Satisfied2 hash publicDescriptor (fun _ => 0)
      (fun _ => ((0 : Int), 0)) [] (withPublic claim trace))
    (j : Fin 3) :
    (envAt trace 0).loc (inputCol j) = claim.input j :=
  eq_of_modEq_of_canonical (input_pin_field_binding hne hsat j)
    (canonical_of_wire_bounded (first_row_input_bounded hne hrange hsat j))
    (hclaim.1 j)

theorem output_pin_exact {hash : List Int -> Int}
    {claim : ThreeEntryTable} {trace : VmTrace}
    (hclaim : CanonicalTable claim)
    (hne : trace.rows ≠ []) (hrange : HonestRangeTable trace)
    (hsat : Satisfied2 hash publicDescriptor (fun _ => 0)
      (fun _ => ((0 : Int), 0)) [] (withPublic claim trace))
    (j : Fin 3) :
    (envAt trace 0).loc (outputCol j) = claim.output j :=
  eq_of_modEq_of_canonical (output_pin_field_binding hne hsat j)
    (canonical_of_wire_bounded (first_row_output_bounded hne hrange hsat j))
    (hclaim.2 j)

/-- **The retired `LiveProjectionCertificate`, now a theorem.**  Every
canonically decoded claim of a satisfying trace lies in the wire-checked
30-bit domain, because the emitted teeth say so. -/
theorem statement_forces_wire_bounded {hash : List Int -> Int}
    {claim : ThreeEntryTable} {trace : VmTrace}
    (hclaim : CanonicalTable claim) (hne : trace.rows ≠ [])
    (hrange : HonestRangeTable trace)
    (hsat : Satisfied2 hash publicDescriptor (fun _ => 0)
      (fun _ => ((0 : Int), 0)) [] (withPublic claim trace)) :
    WireBoundedTable claim := by
  constructor
  · intro j
    have hb := first_row_input_bounded hne hrange hsat j
    rwa [input_pin_exact hclaim hne hrange hsat j] at hb
  · intro j
    have hb := first_row_output_bounded hne hrange hsat j
    rwa [output_pin_exact hclaim hne hrange hsat j] at hb

/-- Each acceptance atom of any nonempty satisfying trace reduces to the
claimed table's own successor equation, once the six field pins are
canonically decoded. -/
theorem claimed_atom_modEq_zero {hash : List Int -> Int}
    {claim : ThreeEntryTable} {trace : VmTrace}
    (hclaim : CanonicalTable claim)
    (hne : trace.rows ≠ []) (hrange : HonestRangeTable trace)
    (hsat : Satisfied2 hash publicDescriptor (fun _ => 0)
      (fun _ => ((0 : Int), 0)) [] (withPublic claim trace))
    (j : Fin 3) :
    claim.output j - claim.input j - 1 ≡ 0 [ZMOD 2013265921] := by
  have hpos : 0 < (withPublic claim trace).rows.length := by
    simp [withPublic]
    exact List.length_pos_iff.mpr hne
  have hgate := hsat.rowConstraints 0 hpos
    (always (directAtom j)) (direct_atom_mem j)
  have hi := input_pin_exact hclaim hne hrange hsat j
  have ho := output_pin_exact hclaim hne hrange hsat j
  simp only [always, VmConstraint2.holdsAt, WindowConstraint.holdsAt,
    Bool.false_eq_true, if_false] at hgate
  rw [directAtom_eval] at hgate
  simp only [withPublic, envAt] at hi ho hgate
  rwa [hi, ho] at hgate

/-- **Soundness for an arbitrary satisfying witness, with NO arithmetic side
condition.**  The public statement, not a prover-selected hidden table, is what
`Holds`; the no-wrap premise that used to be assumed is now read off the
descriptor's own range teeth.  The only remaining hypothesis is the decoding
convention that the six claimed field elements are given by their canonical
integer representatives. -/
theorem statement_sound (hash : List Int -> Int) (claim : ThreeEntryTable)
    (hclaim : CanonicalTable claim)
    (trace : VmTrace) (hs : StatementSatisfied hash claim trace) :
    Holds (sourceValuation claim) 0 successorSkolemFormula := by
  rcases hs with ⟨hne, hrange, hsat⟩
  have hbound := statement_forces_wire_bounded hclaim hne hrange hsat
  rw [holds_iff_entries]
  intro j
  exact entry_eq_of_modEq_of_bounded (hbound.1 j) (hbound.2 j)
    (claimed_atom_modEq_zero hclaim hne hrange hsat j)

/-- A wire-bounded true public statement has a constructive live witness. -/
theorem statement_complete (hash : List Int -> Int) (claim : ThreeEntryTable)
    (hbound : WireBoundedTable claim)
    (hholds : Holds (sourceValuation claim) 0 successorSkolemFormula) :
    StatementSatisfied hash claim (directTraceOf claim) := by
  refine ⟨by simp [directTraceOf], directTraceOf_honest_range claim, ?_⟩
  simpa [withPublic, directTraceOf] using
    direct_trace_complete hash claim hbound hholds

/-- **Exact external statement theorem.**  On the descriptor's wire-checked
30-bit domain, existence of an arbitrary nonempty satisfying trace is
equivalent to truth of the named public table.  The bound is a premise only
because COMPLETENESS needs it — it names which statements this descriptor can
express; soundness derives it, so a claim outside the domain is REFUSED rather
than silently accepted. -/
theorem public_statement_satisfied_iff_holds (hash : List Int -> Int)
    (claim : ThreeEntryTable) (hbound : WireBoundedTable claim) :
    (∃ trace, StatementSatisfied hash claim trace) <->
      Holds (sourceValuation claim) 0 successorSkolemFormula := by
  constructor
  · rintro ⟨trace, hs⟩
    exact statement_sound hash claim (canonicalTable_of_wireBounded hbound)
      trace hs
  · intro hholds
    exact ⟨directTraceOf claim, statement_complete hash claim hbound hholds⟩

/-! ## 6. Concrete positive and tamper polarities -/

theorem successorEntries_canonical : CanonicalTable successorEntries := by
  constructor <;> intro j <;> fin_cases j <;> norm_num [successorEntries,
    BABYBEAR_MODULUS]

theorem successor_public_statement_has_witness (hash : List Int -> Int) :
    ∃ trace, StatementSatisfied hash successorEntries trace :=
  (public_statement_satisfied_iff_holds hash successorEntries
    successorEntries_wireBounded).2 successorEntries_holds

theorem tamperedEntries_canonical : CanonicalTable tamperedEntries := by
  constructor <;> intro j <;> fin_cases j <;> norm_num [tamperedEntries,
    BABYBEAR_MODULUS]

/-- A one-cell change to the public statement has no satisfying canonical
witness.  This rejects the external tamper, not merely a preselected trace. -/
theorem tampered_public_statement_refused (hash : List Int -> Int) :
    ¬ (∃ trace, StatementSatisfied hash tamperedEntries trace) := by
  intro hex
  exact tamperedEntries_not_holds
    (statement_sound hash tamperedEntries tamperedEntries_canonical
      hex.choose hex.choose_spec)

/-! ## 7. Exact wire bytes -/

/-- The canonical byte string is pinned below after the definition, so changing
the PI order, field count, gate expression, or descriptor name is a proof-visible
wire change. -/
def publicDescriptorBytes : String := emitVmJson2 publicDescriptor

#guard publicDescriptorBytes ==
  "{\"name\":\"dregg-gabbay-public-three-entry-direct-v2\",\"ir\":2,\"trace_width\":6,\"public_input_count\":6,\"tables\":[{\"id\":0,\"name\":\"main\",\"arity\":6,\"sem\":\"main\"},{\"id\":2,\"name\":\"range\",\"arity\":1,\"sem\":\"range\",\"bits\":30}],\"constraints\":[{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":0,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":1,\"pi_index\":1},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":2,\"pi_index\":2},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":3,\"pi_index\":3},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":4,\"pi_index\":4},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":5,\"pi_index\":5},{\"t\":\"window_gate\",\"on_transition\":false,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":0}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"const\",\"v\":1}}}},{\"t\":\"window_gate\",\"on_transition\":false,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":4},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":1}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"const\",\"v\":1}}}},{\"t\":\"window_gate\",\"on_transition\":false,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":5},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":2}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"const\",\"v\":1}}}},{\"t\":\"lookup\",\"table\":2,\"tuple\":[{\"t\":\"var\",\"v\":0}]},{\"t\":\"lookup\",\"table\":2,\"tuple\":[{\"t\":\"var\",\"v\":1}]},{\"t\":\"lookup\",\"table\":2,\"tuple\":[{\"t\":\"var\",\"v\":2}]},{\"t\":\"lookup\",\"table\":2,\"tuple\":[{\"t\":\"var\",\"v\":3}]},{\"t\":\"lookup\",\"table\":2,\"tuple\":[{\"t\":\"var\",\"v\":4}]},{\"t\":\"lookup\",\"table\":2,\"tuple\":[{\"t\":\"var\",\"v\":5}]}],\"hash_sites\":[],\"ranges\":[]}"

#assert_all_clean [
  publicOf_input, publicOf_output, tableOfPublic_publicOf,
  public_pin_mem, direct_atom_mem, public_input_range_mem,
  public_output_range_mem, descriptor_public_surface_exact,
  direct_public_cost_exact, public_statement_reveals_whole_table,
  directTraceOf_loc, directRowOf_input, directRowOf_output,
  directAtom_eval, directInputRangeLookup_holds, directOutputRangeLookup_holds,
  memLog_publicDescriptor, mapLog_publicDescriptor,
  direct_trace_complete, eq_of_modEq_of_canonical,
  canonical_of_wire_bounded, canonicalTable_of_wireBounded,
  input_pin_field_binding, output_pin_field_binding,
  withPublic_honest_range, directTraceOf_honest_range,
  first_row_input_bounded, first_row_output_bounded,
  input_pin_exact, output_pin_exact, statement_forces_wire_bounded,
  claimed_atom_modEq_zero,
  statement_sound, statement_complete,
  public_statement_satisfied_iff_holds, successorEntries_canonical,
  successor_public_statement_has_witness, tamperedEntries_canonical,
  tampered_public_statement_refused
]

end Dregg2.Metatheory.GabbayDescriptorIR2PublicBinding
