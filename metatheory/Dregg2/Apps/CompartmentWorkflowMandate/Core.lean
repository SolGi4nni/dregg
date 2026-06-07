/-
# Dregg2.Apps.CompartmentWorkflowMandate.Core — workflow mandate + DAG admissibility (Phase A).

A compartment-aware workflow mandate: each step names a clearance compartment and DAG
prerequisites; execution order must respect the DAG; step completion is tracked via dedicated
tracker cells in `KernelState.accounts`.

Pure, computable, `#eval`-able.
-/
import Dregg2.Authority.ClearanceGraph
import Dregg2.Exec.Kernel
import Dregg2.Exec.Value
import Dregg2.Tactics

namespace Dregg2.Apps.CompartmentWorkflowMandate

open Dregg2.Authority.ClearanceGraph
open Dregg2.Exec

/-! ## Workflow types. -/

/-- One workflow step: numeric id, DAG prerequisites, and its compartment label. -/
structure WorkflowStep where
  id          : Nat
  needs       : List Nat
  compartment : Label
  deriving Repr, DecidableEq

/-- A workflow mandate carried by the compartment app. -/
structure WorkflowMandate where
  steps           : List WorkflowStep
  charterNul      : Nat
  spendPolicy     : Nat
  actorLabels     : List Label
  clearanceGraph  : ClearanceGraph
  /-- Anchor cell id; step `s` completion is tracked at cell `tracker + s + 1`. -/
  tracker         : CellId := 0
  deriving Repr, DecidableEq

/-! ## Step lookup + completion tracking. -/

/-- The dedicated tracker cell for workflow step `stepId`. -/
def stepTrackerCell (tracker : CellId) (stepId : Nat) : CellId :=
  tracker + stepId + 1

/-- **`stepCompleted`** — step `stepId` is done when its tracker cell is live in the kernel. -/
def stepCompleted (k : KernelState) (stepId : Nat) : Bool :=
  stepTrackerCell 0 stepId ∈ k.accounts

/-- Variant keyed by an explicit tracker anchor (mandate-scoped). -/
def stepCompletedAt (tracker : CellId) (k : KernelState) (stepId : Nat) : Bool :=
  stepTrackerCell tracker stepId ∈ k.accounts

def stepCompletedM (m : WorkflowMandate) (k : KernelState) (stepId : Nat) : Bool :=
  stepCompletedAt m.tracker k stepId

def findStep (steps : List WorkflowStep) (stepId : Nat) : Option WorkflowStep :=
  steps.find? (fun s => s.id == stepId)

/-- Collect the ids of completed steps from kernel tracker cells. -/
def completedSteps (tracker : CellId) (k : KernelState) (candidates : List Nat) : List Nat :=
  candidates.filter (stepCompletedAt tracker k)

/-! ## Admissibility + DAG legality. -/

/-- **`stepAdmissible`** — all prerequisites are in `completed`, and the target is not yet done. -/
def stepAdmissible (m : WorkflowMandate) (stepId : Nat) (completed : List Nat) : Bool :=
  match findStep m.steps stepId with
  | none => false
  | some s =>
    (s.needs.all fun x => decide (x ∈ completed)) && !(decide (stepId ∈ completed))

def dagLegalAux (remaining done : List Nat) (m : WorkflowMandate) : Bool :=
  match remaining with
  | [] => true
  | stepId :: rest =>
    if stepAdmissible m stepId done then
      dagLegalAux rest (stepId :: done) m
    else
      false

/-- **`dagLegal`** — an execution order respects every step's prerequisite DAG. -/
def dagLegal (order : List Nat) (m : WorkflowMandate) : Bool :=
  dagLegalAux order [] m

/-- Whether the actor labels clear every compartment required by the step. -/
def stepClearanceOK (m : WorkflowMandate) (stepId : Nat) : Bool :=
  match findStep m.steps stepId with
  | none => false
  | some s =>
    needsAll m.clearanceGraph m.actorLabels [s.compartment]

/-! ## Basic lemmas. -/

theorem stepAdmissible_false_of_unknown (m : WorkflowMandate) (stepId : Nat)
    (completed : List Nat) (h : findStep m.steps stepId = none) :
    stepAdmissible m stepId completed = false := by
  simp [stepAdmissible, h]

theorem stepAdmissible_false_of_incomplete (m : WorkflowMandate) (stepId : Nat)
    (completed : List Nat) (s : WorkflowStep) (hs : findStep m.steps stepId = some s)
    (need : Nat) (hneed : need ∈ s.needs) (hmiss : need ∉ completed) :
    stepAdmissible m stepId completed = false := by
  unfold stepAdmissible
  simp only [hs]
  apply Bool.eq_false_of_not_eq_true
  intro htrue
  rcases Bool.and_eq_true_iff.mp htrue with ⟨hall, _⟩
  have ht := List.all_eq_true.mp hall need hneed
  exact hmiss (decide_eq_true_iff.mp ht)

theorem stepAdmissible_false_of_already_done (m : WorkflowMandate) (stepId : Nat)
    (completed : List Nat) (h : stepId ∈ completed) :
    stepAdmissible m stepId completed = false := by
  cases hstep : findStep m.steps stepId with
  | none => simp [stepAdmissible, hstep]
  | some s =>
      have hdec : decide (stepId ∈ completed) = true := decide_eq_true_iff.mpr h
      simp [stepAdmissible, hstep, hdec, Bool.and_false]

theorem dagLegal_nil (m : WorkflowMandate) : dagLegal [] m = true := by
  simp [dagLegal, dagLegalAux]

theorem dagLegal_singleton (m : WorkflowMandate) (stepId : Nat)
    (h : stepAdmissible m stepId [] = true) :
    dagLegal [stepId] m = true := by
  simp [dagLegal, dagLegalAux, h]

theorem stepCompleted_true_of_mem (k : KernelState) (stepId : Nat)
    (h : stepTrackerCell 0 stepId ∈ k.accounts) :
    stepCompleted k stepId = true := by
  simpa [stepCompleted] using h

theorem stepCompleted_false_of_not_mem (k : KernelState) (stepId : Nat)
    (h : stepTrackerCell 0 stepId ∉ k.accounts) :
    stepCompleted k stepId = false := by
  simpa [stepCompleted] using h

/-! ## Demo mandate + guards. -/

def demoSteps : List WorkflowStep :=
  [ { id := 0, needs := [], compartment := Label.named "draft" }
  , { id := 1, needs := [0], compartment := Label.named "review" }
  , { id := 2, needs := [1], compartment := Label.named "release" } ]

def demoGraph : ClearanceGraph :=
  { edges :=
      [ (Label.named "officer", Label.named "review")
      , (Label.named "officer", Label.named "release")
      , (Label.named "clerk", Label.named "draft") ] }

def demoMandate : WorkflowMandate :=
  { steps := demoSteps
  , charterNul := 42
  , spendPolicy := 7
  , actorLabels := [Label.named "officer", Label.named "clerk"]
  , clearanceGraph := demoGraph
  , tracker := 100 }

/-! ## RecordKernel charter slots (review → redact → sign). -/

abbrev stepCursorSlot : FieldName := "step_cursor"
abbrev commitmentAnchorSlot : FieldName := "commitment_anchor"
abbrev mandateCell : CellId := 0

/-- The canonical 3-step charter DAG: review → redact → sign. -/
def charterSteps3 : List WorkflowStep :=
  [ { id := 0, needs := [], compartment := Label.named "review" }
  , { id := 1, needs := [0], compartment := Label.named "redact" }
  , { id := 2, needs := [1], compartment := Label.named "sign" } ]

def charterGraph3 : ClearanceGraph :=
  { edges :=
      [ (Label.named "officer", Label.named "review")
      , (Label.named "officer", Label.named "redact")
      , (Label.named "officer", Label.named "sign")
      , (Label.named "clerk", Label.named "review") ] }

/-- Officer may run all three phases; clerk may only review. -/
def charterMandate3 : WorkflowMandate :=
  { steps := charterSteps3
  , charterNul := 42
  , spendPolicy := 5
  , actorLabels := [Label.named "officer"]
  , clearanceGraph := charterGraph3
  , tracker := 0 }

def clerkMandate3 : WorkflowMandate :=
  { charterMandate3 with actorLabels := [Label.named "clerk"] }

/-- Completed step ids implied by the monotonic cursor (`cursor = # completed prefix`). -/
def completedOf (cursor : Nat) : List Nat :=
  List.range cursor

/-- **Runtime mandate state** on the charter cell: step cursor + commitment anchor. -/
structure CwmRuntime where
  cursor : Nat
  anchor : Nat
  deriving Repr, DecidableEq

def CwmRuntime.WF (s : CwmRuntime) (m : WorkflowMandate) : Prop := s.cursor ≤ m.steps.length

def CwmRuntime.WF3 (s : CwmRuntime) : Prop := s.cursor ≤ 3

instance (s : CwmRuntime) (m : WorkflowMandate) : Decidable (s.WF m) := by
  unfold CwmRuntime.WF; infer_instance

/-- Predicate-level step completion: DAG prerequisites ∧ clearance. -/
def cwmAdvanceM (m : WorkflowMandate) (s : CwmRuntime) : Option CwmRuntime :=
  if s.cursor < m.steps.length then
    match stepAdmissible m s.cursor (completedOf s.cursor) && stepClearanceOK m s.cursor with
    | true  => some { s with cursor := s.cursor + 1 }
    | false => none
  else
    none

/-! ## The EXECUTOR ADMIT TABLE — `cwmAdvanceM` baked into a decision table the executor checks.

`cwmAdvanceM` decides DAG-prerequisites ∧ per-step-clearance off the cursor, but the executor only
sees a scalar `(old, new)` field write on `step_cursor`. We bake `cwmAdvanceM`'s decision into a
finite `(old, new)` decision table: for every cursor value `c` the charter admits an advance at, the
table holds `(c, c+1)`. The cell's program carries an `.admitTable stepCursorSlot` with THIS table, so
the executor admits a `c → c+1` write iff `cwmAdvanceM` admits at cursor `c` — and a no-clearance /
out-of-DAG advance (NOT in the table) is rejected BY THE EXECUTOR. -/

/-- Whether the charter admits an advance at cursor `c` (the predicate `cwmAdvanceM` decides). -/
def cwmAdvanceAdmits (m : WorkflowMandate) (c : Nat) : Bool :=
  decide (c < m.steps.length) && stepAdmissible m c (completedOf c) && stepClearanceOK m c

/-- The `(old, new)` decision table baked from `cwmAdvanceM`: `(c, c+1)` for every admitted cursor `c`
in `0..steps.length`. The executor admits a cursor write iff its `(old, new)` is in this list. -/
def cwmAdmitTable (m : WorkflowMandate) : List (Int × Int) :=
  (List.range (m.steps.length + 1)).filterMap fun c =>
    if cwmAdvanceAdmits m c then some ((c : Int), ((c + 1 : Nat) : Int)) else none

/-- **`cwmAdvanceAdmits_iff` — PROVED.** The baked predicate is EXACTLY `cwmAdvanceM`'s success at
cursor `c` (the off-line predicate and the table-source decision agree). -/
theorem cwmAdvanceAdmits_iff (m : WorkflowMandate) (s : CwmRuntime) :
    cwmAdvanceAdmits m s.cursor = true ↔ (cwmAdvanceM m s).isSome = true := by
  unfold cwmAdvanceAdmits cwmAdvanceM
  by_cases hlen : s.cursor < m.steps.length
  · simp only [hlen, decide_true, Bool.true_and, ↓reduceIte]
    cases hadm : stepAdmissible m s.cursor (completedOf s.cursor) <;>
      cases hcl : stepClearanceOK m s.cursor <;> simp
  · simp only [hlen, decide_false, Bool.false_and, ↓reduceIte, Option.isSome_none]

/-- **`cwmAdmitTable_mem_iff` — PROVED.** The table contains `(c, c+1)` (as `Int`s) iff the charter
admits an advance at cursor `c`. The bridge from table membership to the predicate decision. -/
theorem cwmAdmitTable_mem_iff (m : WorkflowMandate) (c : Nat) (hc : c < m.steps.length) :
    ((c : Int), ((c + 1 : Nat) : Int)) ∈ cwmAdmitTable m ↔ cwmAdvanceAdmits m c = true := by
  unfold cwmAdmitTable
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨a, _, ha⟩
    by_cases had : cwmAdvanceAdmits m a
    · rw [if_pos had] at ha
      simp only [Option.some.injEq, Prod.mk.injEq] at ha
      obtain ⟨hac, _⟩ := ha
      have : a = c := by exact_mod_cast hac
      subst this; exact had
    · rw [if_neg had] at ha; exact absurd ha (by simp)
  · intro had
    exact ⟨c, by simp only [List.mem_range]; omega, by rw [if_pos had]⟩

inductive CwmPhase | review | redact | sign
  deriving Repr, DecidableEq

def CwmPhase.toStepId : CwmPhase → Nat
  | .review => 0 | .redact => 1 | .sign => 2

def demoKernel : KernelState :=
  { accounts := { 101 }
  , bal := fun _ => 0
  , caps := fun _ => [] }

#guard stepAdmissible demoMandate 0 []
#guard stepAdmissible demoMandate 1 [0]
#guard stepAdmissible demoMandate 1 [] == false
#guard dagLegal [0, 1, 2] demoMandate
#guard dagLegal [1, 0, 2] demoMandate == false
#guard stepCompletedM demoMandate demoKernel 0
#guard stepClearanceOK demoMandate 1
#guard needsAll demoGraph [Label.named "clerk"] [Label.named "draft"]
#guard stepAdmissible charterMandate3 1 [0]
#guard stepClearanceOK charterMandate3 0
#guard stepClearanceOK clerkMandate3 1 == false
#guard (cwmAdvanceM charterMandate3 { cursor := 0, anchor := 42 }).map (·.cursor) == some 1

/-! ## DIFFERENTIAL CORPUS (mirror-drift tooth for `starbridge-compartment-workflow-mandate`).

`starbridge-apps/compartment-workflow-mandate/src/lib.rs::cwm_advance_admits` is a HAND-PORT of
`cwmAdvanceM` (DAG-prerequisite ∧ per-step clearance ∧ cursor < terminal). A hand port can
SILENTLY DRIFT — drop the clearance leg (letting a clerk sign), or admit past the terminal — and
the proven `cwmAdvanceM` / `cwmAdvanceAdmits_iff` theorems would never notice.

`cwmDiffCorpus` enumerates `(mandate, cursor)` and emits the advance DECISION as
`(admitted, newCursor)` (`newCursor = 0` on reject). The Rust test
`compartment-workflow-mandate/tests/cwm_lean_differential.rs` enumerates the IDENTICAL grid
through `cwm_advance_admits` and asserts the SAME vector. Drift on either side fails.

Grid: mandates = [charterMandate3 (officer: clears all 3), clerkMandate3 (clerk: clears only
review/step 0)]; cursors = [0, 1, 2, 3] (terminal = 3). -/

def cwmDiffMandates : List WorkflowMandate := [charterMandate3, clerkMandate3]
def cwmDiffCursors : List Nat := [0, 1, 2, 3]

/-- Per-row `(admitted, newCursor)`; `newCursor = 0` on reject. Row-major over mandates × cursors. -/
def cwmDiffCorpus : List (Bool × Nat) :=
  cwmDiffMandates.flatMap fun m =>
    cwmDiffCursors.map fun c =>
      match cwmAdvanceM m { cursor := c, anchor := 42 } with
      | some s' => (true, s'.cursor)
      | none    => (false, 0)

-- PINNED: the 8-row decision vector. The Rust differential test pins the identical literal.
#guard cwmDiffCorpus ==
  [ -- charterMandate3 (officer clears review/redact/sign): linear DAG advances 0→1→2→3, then stops
    (true, 1), (true, 2), (true, 3), (false, 0),
    -- clerkMandate3 (clerk clears ONLY review): step 0 admits; step 1 (redact) lacks clearance → stop
    (true, 1), (false, 0), (false, 0), (false, 0) ]

#assert_axioms stepAdmissible_false_of_incomplete
#assert_axioms dagLegal_nil
#assert_axioms stepCompleted_true_of_mem
#assert_axioms cwmAdvanceAdmits_iff
#assert_axioms cwmAdmitTable_mem_iff

end Dregg2.Apps.CompartmentWorkflowMandate