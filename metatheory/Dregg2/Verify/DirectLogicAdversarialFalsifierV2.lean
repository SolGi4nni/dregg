/-
# Direct-logic adversarial falsifiers (audit V2)

This file IS imported by the trusted umbrella (`Dregg2.lean`), so every theorem
below is built and gated by CI like any other.  That is the intended direction:
these are refusal canaries, and a canary that is not built is not a canary.  It
carries adversarial witnesses against the live direct-logic descriptors — two
CLOSED holes kept as regression canaries, one still-open carrier hole, and one
named residual premise the refusals ride on.

1. **CLOSED (regression canary).**  The public Gabbay direct-table descriptor
   used to ACCEPT a fully canonical FALSE table.  Its acceptance polynomial was
   the sum of three squared residuals, and `284861408 ^ 2 = -1` in BabyBear, so
   `1 ^ 2 + 284861408 ^ 2 + 0 ^ 2` vanishes in the field while the first two
   successor equations fail.  The gap was made up by a Lean-side
   `LiveProjectionCertificate` bounding the integer numerator — a premise that
   was NEVER serialized into the descriptor, so the emitted bytes did not
   enforce what made them sound.  The repair is on the wire: acceptance is now
   three LINEAR atoms and each of the six bound columns carries a 30-bit range
   LOOKUP against the declared range table `2` (the descriptor's `ranges` field
   is `[]`; the lookups are the enforcing instrument), both of which are
   emitted and both of which `Satisfied2` evaluates on every row.  The
   theorems below now prove the same table REFUSED — as a preselected trace and
   as an external statement — while the true successor table still has a
   witness, so the repair rejects the counterexample rather than everything.
   The wrap facts are retained to document exactly what the retired gate fell
   to.  §1b carries a SECOND wrap witness whose only refuting gate is a range
   tooth, so both halves of the repair are pinned load-bearing rather than one
   half masking the other.

2. **OPEN (named).**  The abstract finite-FOL `FOLSatisfied2` carrier accepts a
   false sentence on an EMPTY trace, because its row-wise conclusion and every
   row-local constraint are then vacuous.  No descriptor byte can close this:
   nothing can constrain a row that does not exist, so it is a property of the
   carrier (a deployed AIR trace has at least one row).  The public Gabbay
   statement relation keeps `trace.rows ≠ []` as an explicit premise for exactly
   this reason.

3. **NAMED RESIDUAL — the premise every range-tooth refusal here rides on.**
   Read §0 before reading any refusal theorem below.  The range half of the
   repair is enforced by lookups, and a lookup only bounds anything against an
   HONEST range table.  `StatementSatisfied` therefore carries
   `HonestRangeTable trace` (`t.tf .range = rangeRows 30`) as an explicit
   premise, and `Satisfied2` does NOT enforce it.  So the refusals below are
   CONDITIONAL on that premise, and the conditionality is carrier-level, not
   specific to this descriptor.

All theorems below are expected to compile.
-/

import Dregg2.Metatheory.GabbayDescriptorIR2PublicBinding
import Dregg2.Logic.FiniteSignatureFOLDescriptorIR2

namespace Dregg2.Verify.DirectLogicAdversarialFalsifierV2

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Metatheory.GabbayMatrixSemantics
open Dregg2.Metatheory.GabbayDescriptorIR2
open Dregg2.Metatheory.GabbayDescriptorIR2PublicBinding

set_option autoImplicit false

/-! ## 0. NAMED RESIDUAL — the refusals below are conditional on an HONEST RANGE TABLE

Read this before reading any refusal theorem in this file.  Nothing below is
weakened by it; it names what the refusals actually quantify over.

**The premise.**  `StatementSatisfied hash claim trace` is
`trace.rows ≠ [] /\ HonestRangeTable trace /\ Satisfied2 …`, where
`HonestRangeTable trace` is `trace.tf .range = rangeRows WIRE_BITS` — the
trace's `.range` table IS the genuine 30-bit interval table.  Every
statement-level refusal here (`wrapClaim_public_statement_refused`,
`borderWrap_public_statement_refused`) is a refutation of
`∃ trace, StatementSatisfied …`, i.e. it refutes only traces satisfying that
premise.  The two are not equally exposed: `wrapClaim` is refused by the
LINEAR ATOMS, which read no table at all, so its refusal survives an arbitrary
`tf .range` (`wrapClaim_direct_trace_refused` is stated on bare `Satisfied2`
and is table-free; only its statement-level restatement routes through the
shared `statement_sound`, which takes the premise).  `borderWrapClaim` is
refused by the RANGE TOOTH ALONE, and that refusal genuinely needs the
premise.

**Why the premise is not free.**  A range LOOKUP bounds a column only against
the table it looks INTO.  `Satisfied2` fixes the trace's auxiliary tables for
memory and map ops — it has `memTableFaithful : t.tf .memory = …` and
`mapTableFaithful : t.tf .mapOps = …` as structural conjuncts — but it has NO
corresponding field for `.range`.  The abstract carrier therefore lets the
prover choose `tf .range` freely.  Concretely: take `directTraceOf
borderWrapClaim` and replace ONLY its `tf .range` with a FORGED table — any
table whose rows include `[2013265920]` alongside the honest ones.  The rows
are untouched, so all six PI bindings still hold and all three linear
acceptance atoms still hold (`borderWrap_atom_gates_all_pass`); the six
lookups now hold too, because the forged table contains every looked-up cell.
Nothing else in `Satisfied2` bites (`hashSites` and `ranges` are empty, the
mem/map logs are empty).  So that trace satisfies the emitted descriptor for a
FALSE canonical table.  What refuses it is `HonestRangeTable`, a Lean-side
premise, not a descriptor byte.  `borderWrap_range_tooth_fires` shows the
dependence explicitly: it consumes `directTraceOf_honest_range` to turn the
lookup into a bound.

**What is and is not repaired.**  The Gabbay repair CLOSED the descriptor-side
hole: the retired design's `LiveProjectionCertificate` was a premise on the
CLAIM that no emitted byte checked, and it is gone.  The premise that remains
is of a different kind — a premise on the TRACE FAMILY, discharged by
construction for every trace this development builds (`traceOf`,
`directTraceOf`; see `traceOf_honest_range`, `directTraceOf_honest_range`) and
discharged in deployment by the assembly, which CONSTRUCTS the limb
decomposition for a range lookup rather than reading a prover-supplied table
(`circuit/src/descriptor_ir2.rs`).  Neither of those discharges is a theorem
about `Satisfied2`.

**It is carrier-level and uniform, not specific to this descriptor.**  Every
range lookup in the codebase reads against `t.tf .range`, so every soundness
argument through a range tooth carries the same `hrange`-shaped premise; the
deployed transfer path names it the same way (`graduateV1_sound`'s `hrange`).
The general-purpose fix already exists in shape: `Dregg2.Circuit.Satisfied2Faithful`
extends `Satisfied2` with `rangeTableFaithful : t.tf .range = rangeRows
BAL_LIMB_BITS` as a STRUCTURAL conjunct rather than a lever.  Note that the
OTHER extension, `Satisfied2Public`, does NOT close it: its
`PublicTablesFaithful` leg is `TableDef.publicContentsFaithful`, which is
`True` at a `.range`-sem table (only `.exactPublicRows` tables are pinned, and
a 30-bit range table cannot be carried as descriptor-literal rows).  This descriptor's
`StatementSatisfied` has NOT been ported to it, and porting it would move the
premise, not delete it — the honest-table obligation ultimately discharges at
the Rust assembly, which is outside the Lean carrier.  That is the residual:
same CLASS as the other Lean-side premises the abstract carrier does not
enforce, one level up from this descriptor. -/

/-! ## 1. Canonical BabyBear cancellation — the RETIRED gate, and its refusal now -/

/-- `284861408^2 = -1 (mod BabyBear)`.  The first two nonzero successor
residuals are therefore `1` and `284861408`; their squares cancel in the field. -/
def wrapClaim : ThreeEntryTable where
  input _ := 0
  output j := match j.val with
    | 0 => 2
    | 1 => 284861409
    | _ => 1

theorem wrapClaim_canonical : CanonicalTable wrapClaim := by
  constructor <;> intro j <;> fin_cases j <;>
    norm_num [wrapClaim, BABYBEAR_MODULUS]

theorem wrapClaim_not_holds :
    ¬ Holds (sourceValuation wrapClaim) 0 successorSkolemFormula := by
  rw [holds_iff_entries]
  push Not
  exact ⟨0, by norm_num [wrapClaim]⟩

theorem wrapClaim_residual_exact :
    residualNumerator wrapClaim = 81146021767742465 := by
  norm_num [residualNumerator, wrapClaim]

theorem wrapClaim_residual_wraps :
    residualNumerator wrapClaim = 2013265921 * 40305665 := by
  norm_num [wrapClaim_residual_exact]

theorem wrapClaim_residual_modEq_zero :
    residualNumerator wrapClaim ≡ 0 [ZMOD 2013265921] := by
  rw [Int.modEq_zero_iff_dvd, wrapClaim_residual_wraps]
  exact dvd_mul_right _ _

/-- The retired `LiveProjectionCertificate` demanded exactly this bound, and it
FAILS here — which is why the old sum-of-squares gate had to assume it. -/
theorem wrapClaim_numerator_exceeds_modulus :
    2013265921 <= (residualNumerator wrapClaim).natAbs := by
  rw [wrapClaim_residual_exact]
  norm_num

/-! ### The repair, on the wire

The wrap table is INSIDE the descriptor's checked 30-bit domain, so it is not
refused by being out of range — it is refused because acceptance is now a
conjunction of linear atoms instead of one field sum of squares. -/

theorem wrapClaim_wireBounded : WireBoundedTable wrapClaim := by
  constructor <;> intro j <;> fin_cases j <;>
    norm_num [wrapClaim, WIRE_BITS]

/-- The second successor equation fails in BabyBear itself: `284861408` is not a
multiple of the modulus.  Only its SQUARE cancelled. -/
theorem wrapClaim_atom_one_not_modEq_zero :
    ¬ (wrapClaim.output 1 - wrapClaim.input 1 - 1 ≡ 0 [ZMOD 2013265921]) := by
  intro h
  rw [Int.modEq_zero_iff_dvd] at h
  norm_num [wrapClaim] at h

/-- **Regression canary, preselected-trace polarity.**  The exact trace that the
old descriptor accepted is now REFUSED by the emitted gates. -/
theorem wrapClaim_direct_trace_refused (hash : List Int -> Int) :
    ¬ Satisfied2 hash publicDescriptor (fun _ => 0)
      (fun _ => ((0 : Int), 0)) [] (directTraceOf wrapClaim) := by
  intro hsat
  have hgate := hsat.rowConstraints 0 (by simp [directTraceOf])
    (always (directAtom 1)) (direct_atom_mem 1)
  simp only [always, VmConstraint2.holdsAt, WindowConstraint.holdsAt,
    Bool.false_eq_true, if_false] at hgate
  rw [directAtom_eval] at hgate
  simp only [directTraceOf_loc, directRowOf_input, directRowOf_output] at hgate
  exact wrapClaim_atom_one_not_modEq_zero hgate

/-- **Regression canary, external-statement polarity.**  No trace whatsoever
proves the false canonical table any more — the strongest form of the fix. -/
theorem wrapClaim_public_statement_refused (hash : List Int -> Int) :
    ¬ (∃ trace, StatementSatisfied hash wrapClaim trace) := by
  intro hex
  exact wrapClaim_not_holds
    (statement_sound hash wrapClaim wrapClaim_canonical
      hex.choose hex.choose_spec)

/-- The repair is not vacuous rejection: the true successor statement still has
a live witness under the same descriptor. -/
theorem repaired_descriptor_still_accepts_truth (hash : List Int -> Int) :
    ∃ trace, StatementSatisfied hash successorEntries trace :=
  successor_public_statement_has_witness hash

/-! ## 1b. The wrap the ATOMS alone admit — the range teeth are LOAD-BEARING

`wrapClaim` above lies INSIDE the descriptor's 30-bit domain
(`wrapClaim_wireBounded`), so it is refused by the linear atoms and the range
teeth do no work on it.  Read alone it would leave the teeth looking decorative.
This second witness is the one that shows they are not.

Over BabyBear, with both cells canonical in `[0, p)`, the residual
`out - inp - 1` lies in `(-p-1, p-1)`, so the ONLY nonzero multiple of the
modulus it can reach is `-p` — forced at `inp = p - 1`, `out = 0`.  That table
is fully canonical, FALSE, and every one of the three LINEAR acceptance atoms
passes on it in the field.  The single emitted gate that refuses it is the
30-bit range tooth on column 0.

So the repair needs BOTH halves on the wire, and each kills a counterexample the
other admits: conjunctive atoms kill the sum-of-squares cancellation
(`wrapClaim`), and the range teeth kill the residual canonical wrap the atoms
accept (`borderWrapClaim`).  Deleting either re-opens the hole, and these two
theorems are what would go red if someone did. -/

def borderWrapClaim : ThreeEntryTable where
  input j := match j.val with
    | 0 => 2013265920
    | _ => 0
  output j := match j.val with
    | 0 => 0
    | _ => 1

theorem borderWrapClaim_input_zero : borderWrapClaim.input 0 = 2013265920 := rfl

theorem borderWrapClaim_output_zero : borderWrapClaim.output 0 = 0 := rfl

theorem borderWrapClaim_canonical : CanonicalTable borderWrapClaim := by
  constructor <;> intro j <;> fin_cases j <;>
    norm_num [borderWrapClaim, BABYBEAR_MODULUS]

theorem borderWrapClaim_not_holds :
    ¬ Holds (sourceValuation borderWrapClaim) 0 successorSkolemFormula := by
  rw [holds_iff_entries]
  push Not
  refine ⟨0, ?_⟩
  rw [borderWrapClaim_output_zero, borderWrapClaim_input_zero]
  norm_num

/-- **Every LINEAR acceptance atom passes.**  The first residual is exactly
`-2013265921`, a genuine multiple of the modulus — this is a real field wrap of
the successor equation itself, not a sum-of-squares cancellation. -/
theorem borderWrapClaim_atoms_modEq_zero (j : Fin 3) :
    borderWrapClaim.output j - borderWrapClaim.input j - 1 ≡ 0
      [ZMOD 2013265921] := by
  rw [Int.modEq_zero_iff_dvd]
  fin_cases j <;> norm_num [borderWrapClaim]

/-- The same fact at the emitted gate: all three acceptance gates of the exact
trace evaluate to a BabyBear zero.  Acceptance atoms alone would ACCEPT. -/
theorem borderWrap_atom_gates_all_pass (j : Fin 3) :
    (directAtom j).eval (envAt (directTraceOf borderWrapClaim) 0) ≡ 0
      [ZMOD 2013265921] := by
  rw [directAtom_eval]
  simp only [directTraceOf_loc, directRowOf_input, directRowOf_output]
  exact borderWrapClaim_atoms_modEq_zero j

theorem borderWrapClaim_not_wireBounded : ¬ WireBoundedTable borderWrapClaim := by
  intro h
  have hb := (h.1 0).2
  rw [borderWrapClaim_input_zero] at hb
  norm_num [WIRE_BITS] at hb

/-- **The range tooth fires.**  Column 0 carries `2013265920 >= 2 ^ 30`, so the
emitted 30-bit lookup on it FAILS.  This one gate is the whole reason the table
is refused. -/
theorem borderWrap_range_tooth_fires :
    ¬ Lookup.holdsAt (directTraceOf borderWrapClaim).tf
        (envAt (directTraceOf borderWrapClaim) 0)
        ⟨.range, [.var (inputCol 0)]⟩ := by
  intro h
  have hb := lookup_replaces_range WIRE_BITS _
    (directTraceOf_honest_range borderWrapClaim) _ _ h
  rw [rangeHolds_def] at hb
  simp only [directTraceOf_loc, directRowOf_input,
    borderWrapClaim_input_zero] at hb
  norm_num [WIRE_BITS] at hb

/-- **Regression canary, preselected-trace polarity.**  The trace is refused,
and the refutation goes through the RANGE tooth — the atoms all passed. -/
theorem borderWrap_direct_trace_refused (hash : List Int -> Int) :
    ¬ Satisfied2 hash publicDescriptor (fun _ => 0)
      (fun _ => ((0 : Int), 0)) [] (directTraceOf borderWrapClaim) := by
  intro hsat
  exact borderWrap_range_tooth_fires
    (hsat.rowConstraints 0 (by simp [directTraceOf]) _
      (public_input_range_mem 0))

/-- **Regression canary, external-statement polarity.**  No trace whatsoever
proves this false canonical table, so the wrap is closed at the statement level
and not merely for one preselected witness. -/
theorem borderWrap_public_statement_refused (hash : List Int -> Int) :
    ¬ (∃ trace, StatementSatisfied hash borderWrapClaim trace) := by
  intro hex
  exact borderWrapClaim_not_holds
    (statement_sound hash borderWrapClaim borderWrapClaim_canonical
      hex.choose hex.choose_spec)

/-! ## 2. Empty-trace vacuity in the finite-signature FOL carrier -/

open Dregg2.Logic.FiniteLogicDescriptorIR2
open Dregg2.Logic.FiniteSignatureFOLDescriptorIR2

def falseSentence : Formula demoSignature 0 := .bottom

def emptyTrace : VmTrace :=
  { rows := [], pub := zeroAsg, tf := fun _ => [] }

theorem falseSentence_rejects_every_model (model : Model demoSignature) :
    falseSentence.eval model emptyBound = false := rfl

/-- `FOLSatisfied2` itself has no nonempty-trace premise.  With no rows, every
constraint and canonicality obligation is vacuous, even for `bottom`. -/
theorem empty_trace_satisfies_false_fol (hash : List Int -> Int) :
    FOLSatisfied2 hash falseSentence (fun _ => 0)
      (fun _ => ((0 : Int), 0)) [] emptyTrace := by
  refine ⟨⟨?_, ?_, ?_, List.nodup_nil, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i hi
    simp [emptyTrace] at hi
  · intro i hi
    simp [emptyTrace] at hi
  · intro i hi
    simp [emptyTrace] at hi
  · intro op hop
    rw [Dregg2.Logic.FiniteLogicDescriptorIR2.memLog_compileDescriptor] at hop
    cases hop
  · rw [Dregg2.Logic.FiniteLogicDescriptorIR2.memLog_compileDescriptor]
    trivial
  · rw [Dregg2.Logic.FiniteLogicDescriptorIR2.memLog_compileDescriptor]
    exact memCheck_nil _ _
  · rw [Dregg2.Logic.FiniteLogicDescriptorIR2.memLog_compileDescriptor]
    rfl
  · rw [Dregg2.Logic.FiniteLogicDescriptorIR2.mapLog_compileDescriptor]
    rfl
  · intro i hi
    simp [emptyTrace] at hi

#assert_all_clean [
  wrapClaim_canonical,
  wrapClaim_not_holds,
  wrapClaim_residual_exact,
  wrapClaim_residual_wraps,
  wrapClaim_residual_modEq_zero,
  wrapClaim_numerator_exceeds_modulus,
  wrapClaim_wireBounded,
  wrapClaim_atom_one_not_modEq_zero,
  wrapClaim_direct_trace_refused,
  wrapClaim_public_statement_refused,
  borderWrapClaim_canonical,
  borderWrapClaim_not_holds,
  borderWrapClaim_atoms_modEq_zero,
  borderWrap_atom_gates_all_pass,
  borderWrapClaim_not_wireBounded,
  borderWrap_range_tooth_fires,
  borderWrap_direct_trace_refused,
  borderWrap_public_statement_refused,
  repaired_descriptor_still_accepts_truth,
  falseSentence_rejects_every_model,
  empty_trace_satisfies_false_fol
]

end Dregg2.Verify.DirectLogicAdversarialFalsifierV2
