/-
# Dregg2.Apps.ColonistJob — a COLONIST'S JOB as a verified workflow-mandate (ORGAN 2 of the room).

The world read as a place: an inhabitant acts ONLY through a MANDATE proven safe-forever. A
workflow-mandate IS a colonist's JOB — a DAG of steps with prerequisites, a per-step clearance, AND a
spend budget it provably can't exceed. This file instantiates ONE concrete job —

    gather → make → hand-off

— and REUSES the proven crown rather than rebuilding it:

  * the DAG-prerequisite ∧ per-step-clearance admission is exactly `CompartmentWorkflowMandate`'s
    `cwmAdvanceAdmits` over a 3-step charter (`jobCharter`: the gather/make/handoff steps with their
    compartments and the colonist's clearance graph);
  * the executor↔predicate COMMIT-IFF-ADMIT plumbing + the anti-ghost rejection tooth + the kernel
    keystones (conservation / non-amplification / authority) are obtained by INSTANTIATING
    `VerificationToolkit.AppSpec` (`jobSpec`) — `app_commit_iff_admit` / `app_violation_rejected`
    drop out, NO re-proof of the executor plumbing;
  * the genuinely-NEW leg is the SPEND BUDGET woven into admission: a step is admitted only when the
    cumulative cost of the completed prefix PLUS this step's cost stays within the colonist's budget
    (`jobInBudget`). `jobAdvanceAdmits` folds DAG ∧ clearance ∧ in-budget into the scalar cursor
    boundary, and `jobSpec.admit` re-exposes it through the toolkit. Overspend is therefore a REAL
    table-absence rejection (the tooth bites), exactly as a skipped prerequisite or an
    out-of-clearance step is.

Both polarities are pinned by `#guard` (§NON-VACUITY): the colonist advances gather→make→hand-off iff
needs⊆completed ∧ clearance ∧ in-budget (genuine ✓); a skip-a-prerequisite, an out-of-clearance step
(a hauler attempting the crafting step), and an overspend are each REJECTED (cheat ✗) — absent from
the baked admit table, so the executor refuses them in-band.

Pure, computable, `#eval`-able. `#assert_axioms`-clean, no `sorry`, no `:= True`.
-/
import Dregg2.Apps.VerificationToolkit

namespace Dregg2.Apps.ColonistJob

open Dregg2.Exec
open Dregg2.Authority.ClearanceGraph
open Dregg2.Apps.CompartmentWorkflowMandate
  (WorkflowStep WorkflowMandate stepAdmissible stepClearanceOK completedOf
   cwmAdvanceAdmits cwmAdvanceM CwmRuntime stepCursorSlot)
open Dregg2.Apps.VerificationToolkit (AppSpec)

/-! ## §1 — The concrete job DAG: gather → make → hand-off.

Three steps in a linear DAG. Each names a clearance compartment (the verb the colonist must be
cleared for) and carries a spend cost (the budget the job draws against). The colonist's clearance
graph clears a `crafter` for all three verbs and a `hauler` for only `gather`/`handoff` (a hauler may
fetch and deliver but may NOT do the crafting step). -/

/-- Job step compartments — the colonist's VERBS. -/
abbrev gatherLabel  : Label := Label.named "gather"
abbrev makeLabel    : Label := Label.named "make"
abbrev handoffLabel : Label := Label.named "handoff"

/-- The acting-role labels. -/
abbrev crafterLabel : Label := Label.named "crafter"
abbrev haulerLabel  : Label := Label.named "hauler"

/-- The linear job DAG: `gather` (no prereq) → `make` (needs gather) → `hand-off` (needs make). -/
def jobSteps : List WorkflowStep :=
  [ { id := 0, needs := [],  compartment := gatherLabel }
  , { id := 1, needs := [0], compartment := makeLabel }
  , { id := 2, needs := [1], compartment := handoffLabel } ]

/-- The clearance graph: a crafter clears all three verbs; a hauler clears only gather + hand-off. -/
def jobGraph : ClearanceGraph :=
  { edges :=
      [ (crafterLabel, gatherLabel)
      , (crafterLabel, makeLabel)
      , (crafterLabel, handoffLabel)
      , (haulerLabel,  gatherLabel)
      , (haulerLabel,  handoffLabel) ] }

/-- **The CRAFTER's job mandate** — clears every verb (may run the whole DAG). -/
def crafterJob : WorkflowMandate :=
  { steps := jobSteps
  , charterNul := 7
  , spendPolicy := 0
  , actorLabels := [crafterLabel]
  , clearanceGraph := jobGraph
  , tracker := 0 }

/-- **The HAULER's job mandate** — clears only gather + hand-off (REFUSED at the `make` step). -/
def haulerJob : WorkflowMandate :=
  { crafterJob with actorLabels := [haulerLabel] }

/-! ## §2 — The SPEND BUDGET leg (the genuinely-new admission tooth).

Each step costs fuel; the job carries a total budget. A step is in-budget when the cumulative cost of
the completed prefix PLUS this step's cost stays within the budget. This folds the budget into the
scalar cursor admission so an overspend is rejected exactly like a skipped prerequisite. -/

/-- Per-step cost (fuel) of the job: gather=3, make=4, hand-off=2. -/
def stepCost : Nat → Nat
  | 0 => 3
  | 1 => 4
  | 2 => 2
  | _ => 0

/-- Cumulative cost of the completed prefix `0..cursor` (the fuel already spent). -/
def spentThrough (cursor : Nat) : Nat :=
  (completedOf cursor).foldl (fun acc s => acc + stepCost s) 0

/-- **`jobInBudget budget cursor`** — entering the step AT `cursor` keeps the spend within `budget`:
the prefix already spent PLUS this step's cost is `≤ budget`. -/
def jobInBudget (budget : Nat) (cursor : Nat) : Bool :=
  decide (spentThrough cursor + stepCost cursor ≤ budget)

/-! ## §3 — The folded admission: DAG ∧ clearance ∧ in-budget.

`cwmAdvanceAdmits m c` already folds DAG-prerequisite ∧ per-step-clearance ∧ in-bounds (proven in
`CompartmentWorkflowMandate.Core`); we AND the budget leg onto it. This is the colonist's complete
one-step admission — the predicate the executor's caveat table will decide. -/

/-- **`jobAdvanceAdmits m budget c`** — the colonist may advance at cursor `c` iff the charter
admits the step (DAG ∧ clearance ∧ in-bounds) AND the step keeps the job within `budget`. -/
def jobAdvanceAdmits (m : WorkflowMandate) (budget : Nat) (c : Nat) : Bool :=
  cwmAdvanceAdmits m c && jobInBudget budget c

/-- The full-budget that admits the whole job (gather+make+handoff = 3+4+2 = 9). -/
abbrev fullBudget : Nat := 9
/-- A LEAN budget that admits gather (3) but NOT make (3+4=7 > 6): the overspend witness. -/
abbrev tightBudget : Nat := 6

/-! ## §4 — The job as a `VerificationToolkit.AppSpec` (REUSE — no re-proof).

The colonist's job state, at the executor boundary, is the scalar `step_cursor` write `c → c+1`. We
present it as an `AppSpec` whose `admit` folds DAG ∧ clearance ∧ in-budget. Instantiating the toolkit
gives `app_commit_iff_admit`, `app_violation_rejected`, and the kernel keystones FREE — proven ONCE
generically, never re-derived here. -/

/-- **`jobSpec budget m`** — the colonist job over the `step_cursor` slot. The admit predicate folds
the verb-clearance (via `m`) AND the budget into the scalar `(c → c+1)` boundary. Grid `0..3` (3
steps; cursor ranges over `{0,1,2,3}`). -/
def jobSpec (budget : Nat) (m : WorkflowMandate) : AppSpec where
  slot     := stepCursorSlot
  cell     := 0
  admit    := fun old new =>
    decide (new = old + 1) && decide (0 ≤ old) && jobAdvanceAdmits m budget old.toNat
  oldRange := [0, 1, 2, 3]
  newRange := [1, 2, 3, 4]

/-- The crafter's job on the full budget — the happy path (the whole DAG admits). -/
abbrev crafterFullSpec : AppSpec := jobSpec fullBudget crafterJob
/-- The hauler's job on the full budget — clearance bites at `make`. -/
abbrev haulerFullSpec : AppSpec := jobSpec fullBudget haulerJob
/-- The crafter's job on a tight budget — the budget bites at `make`. -/
abbrev crafterTightSpec : AppSpec := jobSpec tightBudget crafterJob

/-- The toolkit-baked job program is exactly an `.admitTable` on the cursor slot — so a job cell
carrying `(jobSpec _).caveats` gets the executor's caveat-gate commit-iff-admit + tooth verbatim. -/
theorem jobSpec_caveats (budget : Nat) (m : WorkflowMandate) :
    (jobSpec budget m).caveats = [ .admitTable stepCursorSlot (jobSpec budget m).admitTable ] := rfl

/-! ## §5 — The crown, INSTANTIATED (commit-iff-admit + tooth + keystones, for free). -/

/-- **`job_commit_iff_admit` — THE COLONIST-JOB COMMIT-IFF-ADMIT.** On a job cell carrying
`(jobSpec budget m).caveats`, the executor's caveat gate on a `c → c+1` cursor write COMMITS iff the
job admits at cursor `c` (DAG ∧ clearance ∧ in-budget) AND the underlying authority gate fires. This
is `app_commit_iff_admit` INSTANTIATED — the executor plumbing is NOT re-proved. -/
theorem job_commit_iff_admit (budget : Nat) (m : WorkflowMandate) (s : RecChainedState)
    (hprog : s.kernel.slotCaveats (0 : CellId) = (jobSpec budget m).caveats) (actor : CellId) (c : Int)
    (hcur : (jobSpec budget m).committed s.kernel = c)
    (hold : c ∈ (jobSpec budget m).oldRange) (hnew : (c + 1) ∈ (jobSpec budget m).newRange) :
    (EffectsState.stateStepGuarded s stepCursorSlot actor (0 : CellId) (c + 1)).isSome = true
      ↔ ((jobSpec budget m).admit c (c + 1) = true
          ∧ (EffectsState.stateStep s stepCursorSlot actor (0 : CellId) (.int (c + 1))).isSome = true) := by
  have h := VerificationToolkit.app_commit_iff_admit (jobSpec budget m) s hprog actor (c + 1)
    (by rw [hcur]; exact hold) hnew
  rw [hcur] at h
  exact h

/-- **`job_illegal_step_rejected` — THE TOOTH.** A step the job FORBIDS — a skipped prerequisite, an
out-of-clearance verb (a hauler attempting `make`), OR an OVERSPEND — is rejected by the executor:
`stateStepGuarded = none`. `app_violation_rejected` INSTANTIATED; the colonist cannot sneak any of
the three violations past the executor. -/
theorem job_illegal_step_rejected (budget : Nat) (m : WorkflowMandate) (s : RecChainedState)
    (hprog : s.kernel.slotCaveats (0 : CellId) = (jobSpec budget m).caveats) (actor : CellId) (c : Int)
    (hcur : (jobSpec budget m).committed s.kernel = c)
    (hold : c ∈ (jobSpec budget m).oldRange) (hnew : (c + 1) ∈ (jobSpec budget m).newRange)
    (hbad : (jobSpec budget m).admit c (c + 1) = false) :
    EffectsState.stateStepGuarded s stepCursorSlot actor (0 : CellId) (c + 1) = none :=
  VerificationToolkit.app_violation_rejected (jobSpec budget m) s hprog actor (c + 1)
    (by rw [hcur]; exact hold) hnew (by rw [hcur]; exact hbad)

/-- The job cell's scalar slot is `step_cursor`, never the reserved `balance` field — definitionally,
for any budget/mandate. The hypothesis the conservation keystone needs. -/
theorem jobSpec_slot_ne_balance (budget : Nat) (m : WorkflowMandate) :
    (jobSpec budget m).slot ≠ balanceField := by
  show stepCursorSlot ≠ balanceField
  decide

/-- **`job_advance_conserves` — the ECONOMY conserves.** A committed job advance is balance-neutral
(the cursor slot is not `balance`). `app_commit_conserves` instantiated — the colonist's job moving
forward never mints or burns the world's substance. -/
theorem job_advance_conserves (budget : Nat) (m : WorkflowMandate)
    (s s' : RecChainedState) (actor : CellId) (new : Int)
    (h : EffectsState.stateStepGuarded s stepCursorSlot actor (0 : CellId) new = some s') :
    recTotal s'.kernel = recTotal s.kernel :=
  VerificationToolkit.app_commit_conserves (jobSpec budget m) s s' actor new
    (jobSpec_slot_ne_balance budget m) h

/-- **`job_advance_no_amplify` — no smuggled authority.** A committed job advance leaves the
authority graph fixed — advancing a colonist's task never mints a capability. `app_commit_no_amplify`
instantiated. -/
theorem job_advance_no_amplify (budget : Nat) (m : WorkflowMandate)
    (s s' : RecChainedState) (actor : CellId) (new : Int)
    (h : EffectsState.stateStepGuarded s stepCursorSlot actor (0 : CellId) new = some s') :
    Dregg2.Spec.execGraph s'.kernel.caps = Dregg2.Spec.execGraph s.kernel.caps :=
  VerificationToolkit.app_commit_no_amplify (jobSpec budget m) s s' actor new h

/-- **`job_advance_authorized` — only the cleared actor advances.** A committed job advance implies
the actor held authority over the job cell. `app_commit_authorized` instantiated. -/
theorem job_advance_authorized (budget : Nat) (m : WorkflowMandate)
    (s s' : RecChainedState) (actor : CellId) (new : Int)
    (h : EffectsState.stateStepGuarded s stepCursorSlot actor (0 : CellId) new = some s') :
    EffectsState.stateAuthB s.kernel.caps actor (0 : CellId) = true :=
  VerificationToolkit.app_commit_authorized (jobSpec budget m) s s' actor new h

/-! ## §6 — BOTH-POLARITY non-vacuity (the job advances IFF legal; cheats are rejected). -/

-- §6.a GENUINE ✓ — the crafter, on the full budget, advances gather→make→hand-off (the whole DAG):
#guard crafterFullSpec.admit 0 1   --  gather admits  (no prereq, crafter clears gather, 3 ≤ 9)
#guard crafterFullSpec.admit 1 2   --  make admits    (needs gather, crafter clears make, 3+4 ≤ 9)
#guard crafterFullSpec.admit 2 3   --  hand-off admits (needs make, crafter clears handoff, 7+2 ≤ 9)

-- the baked admit-table holds exactly the 3 legal +1 advances (non-vacuous: NON-EMPTY):
#guard crafterFullSpec.admitTable.contains (0, 1)            --  true
#guard crafterFullSpec.admitTable.contains (1, 2)            --  true
#guard crafterFullSpec.admitTable.contains (2, 3)            --  true
#guard crafterFullSpec.admitTable.length == 3               --  exactly the 3 legal advances

-- §6.b CHEAT ✗ — SKIP A PREREQUISITE: gather→hand-off (cursor 0 → 2) is NOT a +1, table-absent:
#guard crafterFullSpec.admit 0 2 == false                   --  skip rejected (not +1)
#guard crafterFullSpec.admitTable.contains (0, 2) == false  --  skip absent from table (TOOTH)
-- and advancing PAST the terminal (cursor 3 → 4) is rejected (out of DAG bounds):
#guard crafterFullSpec.admit 3 4 == false                   --  past-terminal rejected
#guard crafterFullSpec.admitTable.contains (3, 4) == false  --  terminal absent (TOOTH)

-- §6.c CHEAT ✗ — OUT-OF-CLEARANCE: a HAULER may gather + hand-off but is REFUSED at `make` (the
--      crafting verb). Admission is per-cursor (the prefix is cursor-derived), so the clearance leg
--      bites EXACTLY at the make step — the verb a hauler is not cleared for:
#guard haulerFullSpec.admit 0 1                              --  hauler clears gather (admits)
#guard haulerFullSpec.admit 1 2 == false                    --  hauler does NOT clear make (REJECT)
#guard haulerFullSpec.admit 2 3                              --  hauler clears hand-off (admits)
#guard haulerFullSpec.admitTable.contains (1, 2) == false   --  no-clearance make absent (TOOTH)
#guard haulerFullSpec.admitTable.contains (0, 1)            --  gather present
#guard haulerFullSpec.admitTable.contains (2, 3)            --  hand-off present (hauler clears it)

-- §6.d CHEAT ✗ — OVERSPEND: the crafter on a TIGHT budget (6) gathers (3 ≤ 6) but make OVERRUNS
--      (3+4 = 7 > 6) and is REJECTED — the budget leg BITES, distinct from clearance (crafter clears make):
#guard crafterTightSpec.admit 0 1                           --  gather in budget (3 ≤ 6)
#guard crafterTightSpec.admit 1 2 == false                  --  make OVERSPENDS (7 > 6) — REJECT
#guard crafterTightSpec.admitTable.contains (1, 2) == false --  overspend make absent (TOOTH)
-- the same step (1→2) the crafter on the FULL budget admits — isolating the budget leg as load-bearing:
#guard crafterFullSpec.admit 1 2                            --  make admits when budget allows (7 ≤ 9)

-- §6.e the budget arithmetic itself (the new leg is real, not decorative):
#guard spentThrough 0 == 0                                  --  nothing spent before gather
#guard spentThrough 1 == 3                                  --  gather cost 3 spent before make
#guard spentThrough 2 == 7                                  --  gather+make = 7 spent before hand-off
#guard jobInBudget fullBudget 2                            --  7+2 = 9 ≤ 9 (hand-off fits full budget)
#guard jobInBudget tightBudget 1 == false                  --  3+4 = 7 > 6 (make overruns tight budget)

/-! ## §7 — The DIFFERENTIAL CORPUS (Rust-mirror drift tooth).

The Rust mirror (`starbridge-apps/.../colonist_job.rs::job_advance_admits`) is a HAND-PORT of
`jobAdvanceAdmits`. It can silently DRIFT (drop the budget leg, drop the clearance leg). The corpus
enumerates `(spec, cursor)` over the three specs × `{0,1,2,3}` and emits the admit decision; the Rust
differential test pins the IDENTICAL vector. Drift on either side fails. -/

def jobDiffSpecs : List AppSpec := [crafterFullSpec, haulerFullSpec, crafterTightSpec]
def jobDiffCursors : List Int := [0, 1, 2, 3]

/-- Per-row admit decision (`spec.admit c (c+1)`), row-major over specs × cursors. -/
def jobDiffCorpus : List Bool :=
  jobDiffSpecs.flatMap fun sp =>
    jobDiffCursors.map fun c => sp.admit c (c + 1)

-- PINNED: the 12-row decision vector (3 specs × 4 cursors). The Rust differential test pins the
-- identical literal. Non-vacuous: it contains BOTH `true` and `false` (the clearance + budget cheats
-- are the false witnesses).
#guard jobDiffCorpus ==
  [ -- crafterFull: gather✓ make✓ handoff✓ then terminal✗
    true,  true,  true,  false,
    -- haulerFull: gather✓ make✗(no make-clearance) handoff✓(hauler clears it) terminal✗
    true,  false, true,  false,
    -- crafterTight(6): gather✓ make✗(overspend 7>6) handoff✗(overspend, cumulative 9>6) terminal✗
    true,  false, false, false ]

-- The diagonal corpus is BOTH-polarity (it contains `true` AND `false`) — the drift pin is not a
-- tautology the Rust mirror can satisfy with any vector.
#guard jobDiffCorpus.contains true && jobDiffCorpus.contains false  --  non-vacuous corpus
#guard jobDiffCorpus.length == 12                                   --  3 specs × 4 cursors

/-! ## §8 — Axiom hygiene. -/

#assert_axioms jobSpec_caveats
#assert_axioms jobSpec_slot_ne_balance
#assert_axioms job_commit_iff_admit
#assert_axioms job_illegal_step_rejected
#assert_axioms job_advance_conserves
#assert_axioms job_advance_no_amplify
#assert_axioms job_advance_authorized

end Dregg2.Apps.ColonistJob
