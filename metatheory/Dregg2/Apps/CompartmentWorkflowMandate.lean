/-
# Dregg2.Apps.CompartmentWorkflowMandate — compartment workflow mandate as a verified cell-program (ungated).

A **charter/mandate** workflow on the REAL `RecordKernelState`: the mandate cell carries a
`step_cursor` (`MonotonicSequence` — replay-safe `+1` advances) and an immutable
`commitment_anchor`. The static charter (`Core.charterMandate3`: review → redact → sign) couples
DAG prerequisite checks (`stepAdmissible`) with compartment clearance (`stepClearanceOK` over
`Authority/ClearanceGraph`).

Load-bearing guarantees (ungated crown):

  * **STEP LEGALITY** — along any adversarial schedule of admitted advances, the cursor stays within
    the charter (`cwm_step_legal_forever` via step-tracking induction).
  * **REJECTION TEETH** — illegal DAG steps and clearance violations fail-closed at the predicate
    layer (`cwm_illegal_dag_rejected`, `cwm_clearance_violation_rejected`); illegal cursor jumps are
    rejected by the executor's `MonotonicSequence` caveat (`cwm_illegal_dag_rejected_exec`).
  * **CONSERVATION** — mandate metadata writes are balance-neutral (`cwm_pay_supply_forever` via
    `livingCellA_carries` / `cellObsA_next`).
  * **SPEND POLICY DEMO** — Stingray `Slice` models per-step fee debits (`charterMandate3.spendPolicy`).

Templates: `Apps/ComputeExchange.lean`, `Apps/Subscription.lean`, `Apps/Identity.lean`.
-/
import Dregg2.Exec.CellCarry
import Dregg2.Exec.TurnExecutorFull
import Dregg2.Exec.FullForest
import Dregg2.Authority.ClearanceGraph
import Dregg2.Apps.CompartmentWorkflowMandate.Core
import Dregg2.Apps.StorageGatewayMandate
import Dregg2.Proof.Stingray

namespace Dregg2.Apps.CompartmentWorkflowMandate

open Dregg2.Exec
open Dregg2.Exec (cellObsA)
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.FullForest
open Dregg2.Exec.EffectsState (caveatsAdmit fieldOf writeField stateStepGuarded_eq stateStepGuarded_admits
  stateStepGuarded_caveat_violation_fails stateStepDev_caveat_violation_fails
  stateStep_factors guarded_state_field_written setField_fieldOf)
open Dregg2.Authority.ClearanceGraph
open Dregg2.Proof.Stingray

/-! ## §1 — Charter domain on RecordKernel (step cursor + commitment anchor). -/

abbrev mandateActor : CellId := 0
abbrev payAsset : AssetId := 0

/-- **The mandate's published per-slot program — NOW with the admission table baked in.** The
`commitment_anchor` stays immutable; the `step_cursor` slot now carries the `.admitTable` of
`cwmAdvanceM`'s admitted `(cursor, cursor+1)` transitions (`cwmAdmitTable charterMandate3`) — so the
executor enforces the FULL DAG-prerequisite ∧ per-step-clearance admission inline, not just the
weaker monotonic-`+1`/bounded shape. A no-clearance / out-of-DAG advance is simply absent from the
table and the executor rejects it. The admit-table SUBSUMES the old `.monotonicSeq`/`.boundedBy`
caveats for this charter (the table holds only consecutive in-bounds `+1` pairs). -/
def mandateCaveats : List SlotCaveat :=
  [ .immutable commitmentAnchorSlot,
    .admitTable stepCursorSlot (cwmAdmitTable charterMandate3) ]

/-- Advance the mandate step cursor on the REAL executor (`setFieldA`). -/
def cwmExecAdvance (actor : CellId) (target : Int) : FullForestA :=
  ⟨ .setFieldA actor mandateCell stepCursorSlot target, [] ⟩

/-- One charter phase as a `+1` cursor bump (review → redact → sign). -/
def cwmPhaseForest (actor : CellId) (cur : Nat) : FullForestA :=
  cwmExecAdvance actor (cur + 1)

/-! ## §A — Predicate-level one-step lemmas (DAG + clearance). -/

/-- **`cwm_illegal_dag_rejected`** — completing a step before its prerequisites is
rejected (`none`). -/
theorem cwm_illegal_dag_rejected (m : WorkflowMandate) (s : CwmRuntime) (stepId : Nat)
    (hdag : stepAdmissible m stepId (completedOf s.cursor) = false) :
    cwmAdvanceM m s = none ∨ s.cursor ≠ stepId := by
  unfold cwmAdvanceM
  by_cases hlen : s.cursor < m.steps.length
  · simp only [hlen, ↓reduceIte]
    by_cases heq : s.cursor = stepId
    · subst heq
      apply Or.inl
      simp [hdag, Bool.false_and]
    · exact Or.inr heq
  · simp only [hlen, ↓reduceIte]
    exact Or.inl trivial

/-- **`cwm_clearance_violation_rejected`** — insufficient compartment clearance is
rejected (`none`). -/
theorem cwm_clearance_violation_rejected (m : WorkflowMandate) (s : CwmRuntime)
    (hadm : stepAdmissible m s.cursor (completedOf s.cursor) = true)
    (hcl : stepClearanceOK m s.cursor = false)
    (hlen : s.cursor < m.steps.length) :
    cwmAdvanceM m s = none := by
  unfold cwmAdvanceM
  simp only [hlen, ↓reduceIte, hadm, hcl, Bool.and_false]

/-- A committed advance leaves the cursor within the charter terminal. -/
theorem cwmAdvanceM_preserves_WF (m : WorkflowMandate) (s s' : CwmRuntime)
    (hwf : s.WF m) (h : cwmAdvanceM m s = some s') : s'.WF m := by
  unfold cwmAdvanceM at h
  by_cases hlen : s.cursor < m.steps.length
  · simp only [hlen, ↓reduceIte] at h
    by_cases hadm : stepAdmissible m s.cursor (completedOf s.cursor) && stepClearanceOK m s.cursor
    · simp only [hadm, ↓reduceIte] at h
      rcases Option.some.inj h with rfl
      simp only [CwmRuntime.WF]; omega
    · simp only [hadm, ↓reduceIte] at h; cases h
  · simp only [hlen, ↓reduceIte] at h; cases h

/-! ### §A.forever — step legality carried along ANY admitted-advance stream. -/

inductive CwmOp where
  | tick
  deriving Repr, DecidableEq

def CwmSched : Type := Nat → CwmOp

def cwmStep (m : WorkflowMandate) (s : CwmRuntime) : CwmOp → CwmRuntime
  | .tick => (cwmAdvanceM m s).getD s

def cwmTraj (m : WorkflowMandate) (s : CwmRuntime) (sched : CwmSched) : Nat → CwmRuntime
  | 0     => s
  | n + 1 => cwmStep m (cwmTraj m s sched n) (sched n)

theorem cwmStep_preserves_WF (m : WorkflowMandate) (s : CwmRuntime) (op : CwmOp) (hwf : s.WF m) :
    (cwmStep m s op).WF m := by
  rcases op with ⟨⟩
  show (cwmAdvanceM m s).getD s |>.WF m
  cases hp : cwmAdvanceM m s with
  | some s' => simp only [Option.getD_some]; exact cwmAdvanceM_preserves_WF m s s' hwf hp
  | none    => simp only [Option.getD_none]; exact hwf

/-- **`cwm_step_legal_forever` — THE HEADLINE:** from any well-formed start, along the
ENTIRE unbounded stream of admitted charter ticks — under EVERY adversarial schedule — the mandate
cursor stays within the charter. Step-tracking induction (abstract face of `livingCellA_carries`). -/
theorem cwm_step_legal_forever (m : WorkflowMandate) (s : CwmRuntime) (hinit : s.WF m) (sched : CwmSched) :
    ∀ n, (cwmTraj m s sched n).WF m := by
  intro n
  induction n with
  | zero => exact hinit
  | succ k ih =>
      show (cwmStep m (cwmTraj m s sched k) (sched k)).WF m
      exact cwmStep_preserves_WF m (cwmTraj m s sched k) (sched k) ih

/-! ## §B — REAL executor teeth + conservation crown. -/

/-- **`cwm_illegal_dag_rejected_exec`** — an illegal cursor jump is rejected by the
`MonotonicSequence` caveat on `step_cursor`. -/
theorem cwm_illegal_dag_rejected_exec (s : RecChainedState) (actor : CellId) (target : Int)
    (hseq : caveatsAdmit s.kernel stepCursorSlot actor mandateCell target = false) :
    execFullForestA s (cwmExecAdvance actor target) = none := by
  have hnone := stateStepDev_caveat_violation_fails s stepCursorSlot actor mandateCell target hseq
  rw [execFullForestA_eq_execFullTurnA]
  simp only [cwmExecAdvance, lowerForestA, lowerChildrenA, execFullTurnA, execFullA, hnone]

/-! ### §B.admit — the EXECUTOR's `caveatsAdmit` over the strengthened program IS `cwmAdvanceM`.

With `mandateCaveats` now carrying `.admitTable stepCursorSlot (cwmAdmitTable charterMandate3)`, the
executor's `caveatsAdmit` on a `step_cursor` write reduces EXACTLY to table membership, which is
EXACTLY `cwmAdvanceM`'s admission at the committed cursor. This is the inline internalization: the
running admission and the off-line predicate decide the SAME thing. -/

/-- The committed cursor read off the mandate cell, as a `Nat`. -/
def cwmCursorNat (k : RecordKernelState) : Nat := (fieldOf stepCursorSlot (k.cell mandateCell)).toNat

/-- **`cwm_caveatsAdmit_eq_table`.** On a cell carrying `mandateCaveats`, the executor's
`caveatsAdmit` on a `step_cursor` write is exactly `cwmAdmitTable`-membership of `(old, new)`. -/
theorem cwm_caveatsAdmit_eq_table (k : RecordKernelState)
    (hprog : k.slotCaveats mandateCell = mandateCaveats) (actor : CellId) (new : Int) :
    caveatsAdmit k stepCursorSlot actor mandateCell new
      = (cwmAdmitTable charterMandate3).contains (fieldOf stepCursorSlot (k.cell mandateCell), new) := by
  unfold caveatsAdmit
  rw [hprog]
  have hf : (mandateCaveats.filter (fun cav => cav.field == stepCursorSlot))
      = [.admitTable stepCursorSlot (cwmAdmitTable charterMandate3)] := by decide
  rw [hf]
  simp only [List.all_cons, List.all_nil, Bool.and_true, SlotCaveat.eval]

/-- **`cwm_commit_iff_admit` (the COMMIT-IFF-ADMIT value frame, predicate↔executor).** On a
mandate cell whose committed cursor is `c` (`< steps.length`), the executor's caveat gate on a
`c → c+1` write COMMITS (admits) IFF `cwmAdvanceM` admits at cursor `c`. The off-line admission
predicate and the running executor decide the SAME transitions. -/
theorem cwm_commit_iff_admit (k : RecordKernelState)
    (hprog : k.slotCaveats mandateCell = mandateCaveats) (actor : CellId) (c : Nat)
    (hcur : fieldOf stepCursorSlot (k.cell mandateCell) = (c : Int)) (hc : c < charterMandate3.steps.length) :
    caveatsAdmit k stepCursorSlot actor mandateCell ((c + 1 : Nat) : Int) = true
      ↔ (cwmAdvanceM charterMandate3 { cursor := c, anchor := 0 }).isSome = true := by
  rw [cwm_caveatsAdmit_eq_table k hprog, hcur, List.contains_iff_mem,
      cwmAdmitTable_mem_iff charterMandate3 c hc]
  exact cwmAdvanceAdmits_iff charterMandate3 { cursor := c, anchor := 0 }

theorem cwmExecAdvance_delta_zero (actor : CellId) (target : Int) (b : AssetId) :
    turnLedgerDeltaAsset (lowerForestA (cwmExecAdvance actor target)) b = 0 := by
  simp [cwmExecAdvance, lowerForestA, lowerChildrenA, turnLedgerDeltaAsset, ledgerDeltaAsset]

theorem cwm_advance_conserves {s s' : RecChainedState} (actor : CellId) (target : Int) (b : AssetId)
    (h : execFullForestA s (cwmExecAdvance actor target) = some s') :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b :=
  execFullForestA_conserves_per_asset s s' (cwmExecAdvance actor target) b h
    (cwmExecAdvance_delta_zero actor target b)

/-- **`cwm_pay_supply_forever` — APP SEMANTICS (ungated crown).** Along EVERY adversarial
schedule on the real living cell, payment asset combined supply never drifts. -/
theorem cwm_pay_supply_forever (s0 : RecChainedState) (sched : SchedA) :
    ∀ n, recTotalAsset (trajA s0 sched n).kernel payAsset =
          recTotalAsset s0.kernel payAsset := by
  intro n
  simpa [cellObsA] using congrFun (livingCellA_obs_invariant' s0 sched n) payAsset



/-! ## §B′ — `cwmWF` kernel predicates (Phase B: real cursor bound + anchor compartment). -/

abbrev cwmCompartmentTag : Int := 42

/-- Read the mandate step cursor from the charter cell. -/
def cwmCursor (k : RecordKernelState) : Int :=
  fieldOf stepCursorSlot (k.cell mandateCell)

/-- Read the mandate commitment anchor from the charter cell. -/
def cwmAnchor (k : RecordKernelState) : Int :=
  fieldOf commitmentAnchorSlot (k.cell mandateCell)

/-- Decidable cursor bound check (used in `#guard` witnesses). -/
def cwmCursorBound (k : RecordKernelState) : Bool :=
  decide ((0 : Int) ≤ cwmCursor k ∧ cwmCursor k ≤ (charterMandate3.steps.length : Int))

def cwmAnchorIs (k : RecordKernelState) (comp : Int) : Bool :=
  decide (cwmAnchor k = comp)

/-- **Strong step-legal invariant (Phase B)** — cursor stays within the charter terminal. -/
def cwmWFStrong (k : RecordKernelState) : Prop :=
  (0 : Int) ≤ cwmCursor k ∧ cwmCursor k ≤ (charterMandate3.steps.length : Int)

/-- **Strong compartment invariant (Phase B)** — commitment anchor matches the expected tag. -/
def cwmInCompartmentStrong (k : RecordKernelState) (comp : Int) : Prop :=
  cwmAnchor k = comp

instance cwmWFStrongDecidable (k : RecordKernelState) : Decidable (cwmWFStrong k) := by
  unfold cwmWFStrong; infer_instance

instance cwmInCompartmentStrongDecidable (k : RecordKernelState) (comp : Int) :
    Decidable (cwmInCompartmentStrong k comp) := by
  unfold cwmInCompartmentStrong; infer_instance

/-- Mandate cell carries the published caveat program (immutable anchor + monotonic-seq/bounded cursor). -/
def cwmMandateProgramOK (k : RecordKernelState) : Prop :=
  k.slotCaveats mandateCell = mandateCaveats

/-- **`cwmWF` — NON-VACUOUS Hatchery contract invariant.** The mandate cell stays a LIVE account AND its
published per-slot caveat program (immutable anchor + monotonic-seq/bounded step cursor) remains
installed — so the executor's per-slot teeth (`cwm_illegal_dag_rejected_exec`, immutable-anchor rewrite
rejection) are enforced on the cell for its WHOLE life, along EVERY adversarial `trajG`. Carried by the
generic `StorageGatewayMandate.execFullForestA_progLive_preserved` frame (no `True` filler). -/
def cwmWF (k : RecordKernelState) : Prop :=
  mandateCell ∈ k.accounts ∧ cwmMandateProgramOK k

/-- **`cwmInCompartment` — NON-VACUOUS compartment-binding invariant (GENUINELY TAG-BINDING).**
Holds iff the mandate cell is a live account, its published per-slot caveat program is installed, AND its
commitment anchor is EXACTLY `comp` (`cwmAnchor k = comp`). This last conjunct is the genuine binding: a
state whose anchor drifts to a different compartment is REJECTED (the predicate is value-dependent on
`comp`, not constant in it). The binding is ENFORCED for life by the persisted
`.immutable commitmentAnchorSlot` caveat in `mandateCaveats` (any later anchor rewrite is rejected); the
sole residual is `makeSovereign` aimed at the cell, which is why the carry is along anchor-safe schedules
(`cwmCompartment_traj_carries`). -/
def cwmInCompartment (k : RecordKernelState) (comp : Int) : Prop :=
  mandateCell ∈ k.accounts ∧ cwmMandateProgramOK k ∧ cwmAnchor k = comp

instance cwmMandateProgramOKDecidable (k : RecordKernelState) : Decidable (cwmMandateProgramOK k) := by
  unfold cwmMandateProgramOK; infer_instance

instance cwmInCompartmentDecidable (k : RecordKernelState) (comp : Int) :
    Decidable (cwmInCompartment k comp) := by
  unfold cwmInCompartment; infer_instance

/-- Clearance at the current cursor (predicate-layer; gated demos exercise via `cwmAdvanceM`). -/
def cwmClearanceOK (k : RecordKernelState) : Bool :=
  let cur := (cwmCursor k).toNat
  if h : cwmCursor k = cur then
    stepClearanceOK charterMandate3 cur
  else
    false

/-- **`cwmWF_traj_carries` — NON-VACUOUS carry.** A committed forest keeps the mandate cell live
AND its published caveat program installed. The generic frame
`StorageGatewayMandate.execFullForestA_progLive_preserved` instantiated at `mandateCell`/`mandateCaveats`. -/
theorem cwmWF_traj_carries (s s' : RecChainedState) (cf : FullForestA)
    (h : execFullForestA s cf = some s') (hwf : cwmWF s.kernel) : cwmWF s'.kernel := by
  obtain ⟨hlive, hprog⟩ := hwf
  exact Dregg2.Apps.StorageGatewayMandate.execFullForestA_progLive_preserved
    s s' cf mandateCell mandateCaveats h hlive hprog

/-- The CWM mandate program installs the `.immutable commitmentAnchorSlot` caveat. -/
theorem cwm_mandateCaveats_has_immutable_anchor :
    (.immutable commitmentAnchorSlot : SlotCaveat) ∈ mandateCaveats := by
  simp [mandateCaveats]

/-- **`cwmCompartmentStrong_traj_carries` — the VALUE-PINNING carry.** A committed forest that
is anchor-safe for the mandate cell (no `makeSovereign` aimed at it) preserves the LITERAL compartment
binding `cwmAnchor = comp`, not merely program-liveness — via the shared
`StorageGatewayMandate.execFullForestA_anchorOf_preserved` frame. Requires the program installed (to
witness the immutable-anchor caveat) and the cell live; both are crown invariants. -/
theorem cwmCompartmentStrong_traj_carries (s s' : RecChainedState) (cf : FullForestA) (comp : Int)
    (h : execFullForestA s cf = some s') (hcomp : cwmInCompartmentStrong s.kernel comp)
    (hprog : cwmMandateProgramOK s.kernel)
    (hok : Dregg2.Apps.StorageGatewayMandate.anchorForestOK mandateCell cf)
    (hlive : mandateCell ∈ s.kernel.accounts) :
    cwmInCompartmentStrong s'.kernel comp := by
  have himm : .immutable commitmentAnchorSlot ∈ s.kernel.slotCaveats mandateCell := by
    rw [show s.kernel.slotCaveats mandateCell = mandateCaveats from hprog]
    exact cwm_mandateCaveats_has_immutable_anchor
  have hanchorEq : fieldOf commitmentAnchorSlot (s'.kernel.cell mandateCell)
      = fieldOf commitmentAnchorSlot (s.kernel.cell mandateCell) :=
    Dregg2.Apps.StorageGatewayMandate.execFullForestA_anchorOf_preserved
      s s' cf mandateCell h hlive himm hok
  unfold cwmInCompartmentStrong cwmAnchor at hcomp ⊢
  rw [hanchorEq]; exact hcomp

/-- **`cwmCompartment_traj_carries` — NON-VACUOUS carry of the GENUINE binding.** An anchor-safe
committed forest preserves all three conjuncts: live cell + installed immutable-anchor caveat program +
the LITERAL anchor value `cwmAnchor = comp`. The program-live legs use the generic
`execFullForestA_progLive_preserved` frame; the anchor-value leg uses
`execFullForestA_anchorOf_preserved` (gated by the installed `.immutable commitmentAnchorSlot` caveat,
excluding only the un-caveat-gated `makeSovereign` rebind, whence `anchorForestOK`). -/
theorem cwmCompartment_traj_carries (s s' : RecChainedState) (cf : FullForestA) (comp : Int)
    (h : execFullForestA s cf = some s')
    (hok : Dregg2.Apps.StorageGatewayMandate.anchorForestOK mandateCell cf)
    (hcomp : cwmInCompartment s.kernel comp) :
    cwmInCompartment s'.kernel comp := by
  obtain ⟨hlive, hprog, hanchor⟩ := hcomp
  obtain ⟨hlive', hprog'⟩ := Dregg2.Apps.StorageGatewayMandate.execFullForestA_progLive_preserved
    s s' cf mandateCell mandateCaveats h hlive hprog
  have hstrong' : cwmInCompartmentStrong s'.kernel comp :=
    cwmCompartmentStrong_traj_carries s s' cf comp h hanchor hprog hok hlive
  exact ⟨hlive', hprog', hstrong'⟩

theorem cwmWFStrong_of_cursor_unchanged {k k' : RecordKernelState}
    (hcur : cwmCursor k' = cwmCursor k) (hwf : cwmWFStrong k) : cwmWFStrong k' := by
  unfold cwmWFStrong at *
  simpa [hcur] using hwf

theorem cwmInCompartmentStrong_of_anchor_unchanged {k k' : RecordKernelState} (comp : Int)
    (ha : cwmAnchor k' = cwmAnchor k) (h : cwmInCompartmentStrong k comp) :
    cwmInCompartmentStrong k' comp := by
  unfold cwmInCompartmentStrong at *
  simpa [ha] using h

/-! ## §C — Stingray spend-policy demo (per-step fee against a silo slice). -/

def demoBudget : Slice := { ceiling := 10, spent := 0 }

theorem cwm_step_fee_fits_slice :
    (demoBudget.tryDebit charterMandate3.spendPolicy).isSome = true := by
  rw [tryDebit_isSome_iff]
  simp [demoBudget, charterMandate3, Slice.remaining]

theorem cwm_double_step_fee_exhausts_slice :
    ((demoBudget.tryDebit charterMandate3.spendPolicy).bind
      (fun s' => s'.tryDebit charterMandate3.spendPolicy)).isSome = true := by
  have h1 : demoBudget.tryDebit charterMandate3.spendPolicy = some { ceiling := 10, spent := 5 } := by
    unfold Slice.tryDebit; simp [demoBudget, charterMandate3, Slice.remaining]
  have h2 : ({ ceiling := 10, spent := 5 } : Slice).tryDebit charterMandate3.spendPolicy =
      some { ceiling := 10, spent := 10 } := by
    unfold Slice.tryDebit; simp [charterMandate3, Slice.remaining]
  simpa [h1, h2]

/-! ## §D — NON-VACUITY: review → redact → sign on `cwm0`. -/

def cwm0 : RecChainedState :=
  { kernel :=
      { accounts := {0}
        cell := fun c =>
          if c = mandateCell then
            .record [("balance", .int 0), (stepCursorSlot, .int 0),
                     (commitmentAnchorSlot, .int 42)]
          else .record [("balance", .int 0)]
        caps := fun _ => []
        bal := fun c a => if c = 0 then (if a = 0 then 100 else if a = 1 then 7 else 0) else 0
        slotCaveats := fun c => if c = mandateCell then mandateCaveats else [] }
    log := [] }

def cwmReviewed : Option RecChainedState :=
  execFullForestA cwm0 (cwmPhaseForest mandateActor 0)

def cwmRedacted : Option RecChainedState :=
  cwmReviewed.bind (fun s => execFullForestA s (cwmPhaseForest mandateActor 1))

def cwmSigned : Option RecChainedState :=
  cwmRedacted.bind (fun s => execFullForestA s (cwmPhaseForest mandateActor 2))

#guard ({ cursor := 0, anchor := 42 } : CwmRuntime).WF charterMandate3  --  true
#guard (cwmAdvanceM charterMandate3 { cursor := 0, anchor := 42 }).map (·.cursor) == some 1  --  some 1
#guard (cwmAdvanceM charterMandate3 { cursor := 1, anchor := 42 }).map (·.cursor) == some 2  --  some 2
#guard (cwmAdvanceM charterMandate3 { cursor := 2, anchor := 42 }).map (·.cursor) == some 3  --  some 3
#guard (cwmAdvanceM clerkMandate3 { cursor := 1, anchor := 42 }).isSome == false  --  false (clearance)
#guard stepAdmissible charterMandate3 1 [0]  --  true
#guard stepAdmissible charterMandate3 1 [] == false  --  false (illegal DAG)

#guard (cwmReviewed.isSome)  --  true
#guard (cwmReviewed.map (fun s => fieldOf stepCursorSlot (s.kernel.cell mandateCell))) == some 1  --  some 1
#guard (cwmRedacted.map (fun s => fieldOf stepCursorSlot (s.kernel.cell mandateCell))) == some 2  --  some 2
#guard (cwmSigned.map (fun s => fieldOf stepCursorSlot (s.kernel.cell mandateCell))) == some 3  --  some 3
#guard (cwmSigned.map (fun s => fieldOf commitmentAnchorSlot (s.kernel.cell mandateCell))) == some 42  --  some 42

#guard (caveatsAdmit cwm0.kernel stepCursorSlot mandateActor mandateCell 2) == false  --  false (skip)
#guard ((execFullForestA cwm0 (cwmExecAdvance mandateActor 2)).isSome) == false  --  false

#guard (demoBudget.tryDebit charterMandate3.spendPolicy).isSome  --  true
#guard ((demoBudget.tryDebit charterMandate3.spendPolicy).bind
        (fun s' => s'.tryDebit charterMandate3.spendPolicy)).isSome  --  true
#guard (((demoBudget.tryDebit charterMandate3.spendPolicy).bind
          (fun s' => s'.tryDebit charterMandate3.spendPolicy)).bind
         (fun s'' => s''.tryDebit charterMandate3.spendPolicy)).isSome == false  --  false

#guard ((cwmSigned.map (fun s => recTotalAsset s.kernel payAsset)).getD 0) == 100  --  100

-- NON-VACUITY of the carried invariant: the program-live invariant HOLDS at genesis (mandate cell live
-- + caveat program installed), so the safety crown is non-trivially applicable.
#guard (decide (mandateCell ∈ cwm0.kernel.accounts) && (cwm0.kernel.slotCaveats mandateCell == mandateCaveats))

/-! ## Axiom hygiene — every keystone pinned. -/

#assert_axioms cwm_illegal_dag_rejected
#assert_axioms cwm_clearance_violation_rejected
#assert_axioms cwm_caveatsAdmit_eq_table
#assert_axioms cwm_commit_iff_admit
#assert_axioms cwmAdvanceM_preserves_WF
#assert_axioms cwmStep_preserves_WF
#assert_axioms cwm_step_legal_forever
#assert_axioms cwm_illegal_dag_rejected_exec
#assert_axioms cwmExecAdvance_delta_zero
#assert_axioms cwm_advance_conserves
#assert_axioms cwm_pay_supply_forever
#assert_axioms cwm_step_fee_fits_slice
#assert_axioms cwm_double_step_fee_exhausts_slice
#assert_axioms cwmWFStrong_of_cursor_unchanged
#assert_axioms cwmWF_traj_carries
#assert_axioms cwmCompartment_traj_carries

end Dregg2.Apps.CompartmentWorkflowMandate