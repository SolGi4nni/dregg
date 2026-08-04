/-
# Shipworks — recurring maintenance as a finite PoA game

Shipworks is the ordinary work of keeping an inhabited pocket of the Khovokhi
comfortable.  It is one coherent, short game with four scheduled jobs rather
than four reskinned score buttons:

* power reroute rewards output while its switching faults pulse on even turns;
* atmosphere scrub starts dirtier and rewards deliberate fault removal;
* coolant repair has the sharpest late-session pressure curve;
* ration synthesis needs the largest output and makes reserve use consequential.

The player chooses two distinct single-use tools, then spends a bounded sequence
of scans, advances, stabilizations, improvisations and tool uses before asking
the station to certify the result.  Every ordinary turn advances the mission's
authored pressure schedule.  Certification is possible only after the station
has been scanned, the job target has been reached, and faults are within the
job-specific limit.

Daily recurrence is not a streak.  A finalized mission epoch selects both the
job and its pressure variant.  Browser UTC is retained only as unauthoritative
telemetry and is proved irrelevant to settlement.  Missing any number of epochs
does not change a later reward.  Persistent state remembers only the last
claimed mission epoch and the canonical u64 player counter, so one epoch cannot
be claimed twice and counter exhaustion refuses.

Most importantly, a submission contains actions, not a reward.  Settlement
replays those actions in Lean and derives the exact `Contribution` here.  There
is no caller-authored reward field and no clipping or saturation path.
-/
import Dregg2.Games.PathOfAngels.Core
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.Shipworks

open Dregg2.Games.PathOfAngels

set_option autoImplicit false

/-! ## Authored dispatch rotation -/

abbrev MAX_TURNS : Nat := 7
abbrev MAX_OUTPUT : Nat := 32
abbrev MAX_STORED_FAULT : Nat := 12
abbrev FAILURE_FAULT : Nat := 9
abbrev MAX_RESERVES : Nat := 4

inductive Job where
  | powerReroute
  | atmosphereScrub
  | coolantRepair
  | rationSynthesis
deriving Repr, DecidableEq

def jobAt (epoch : EpochId) : Job :=
  match epoch.value % 4 with
  | 0 => .powerReroute
  | 1 => .atmosphereScrub
  | 2 => .coolantRepair
  | _ => .rationSynthesis

/-- Three pressure arrangements rotate behind each of the four job families.
The quotient means epochs 0..3 share variant zero, 4..7 variant one, and so on. -/
def variantAt (epoch : EpochId) : Nat := (epoch.value / 4) % 3

/-- A dispatch can be issued only by the finalized-epoch selector in this
module.  The network adapter must supply that finalized epoch; no wall clock is
part of the constructor. -/
structure Dispatch where
  private mk ::
  epoch : EpochId
  job : Job
  variant : Nat
  job_scheduled : job = jobAt epoch
  variant_scheduled : variant = variantAt epoch
deriving Repr, DecidableEq

def dispatchForFinalizedEpoch (epoch : EpochId) : Dispatch where
  epoch
  job := jobAt epoch
  variant := variantAt epoch
  job_scheduled := rfl
  variant_scheduled := rfl

theorem dispatch_job_is_epoch_owned (epoch : EpochId) :
    (dispatchForFinalizedEpoch epoch).job = jobAt epoch := rfl

theorem dispatch_variant_is_epoch_owned (epoch : EpochId) :
    (dispatchForFinalizedEpoch epoch).variant = variantAt epoch := rfl

/-! ## Loadout and state -/

inductive Tool where
  | diagnosticArray
  | busCoupler
  | scrubberMesh
  | cryoPatch
  | cultureCatalyst
  | spareCartridge
deriving Repr, DecidableEq

structure Loadout where
  primary : Tool
  secondary : Tool
deriving Repr, DecidableEq

def Loadout.valid (loadout : Loadout) : Bool :=
  decide (loadout.primary != loadout.secondary)

inductive Status where
  | active
  | complete
  | failed
deriving Repr, DecidableEq

/-- The entire state projected to a future browser.  `turn`, `output`, `fault`
and `reserves` remain naturals on the projection boundary, while `Valid` below
is the admission wall for every transition. -/
structure State where
  dispatch : Dispatch
  loadout : Loadout
  status : Status
  turn : Nat
  output : Nat
  fault : Nat
  reserves : Nat
  scanned : Bool
  primaryUsed : Bool
  secondaryUsed : Bool
deriving Repr, DecidableEq

def State.Valid (state : State) : Bool :=
  state.loadout.valid &&
  decide (state.turn <= MAX_TURNS) &&
  decide (state.output <= MAX_OUTPUT) &&
  decide (state.fault <= MAX_STORED_FAULT) &&
  decide (state.reserves <= MAX_RESERVES) &&
  match state.status with
  | .active => decide (state.turn < MAX_TURNS && state.fault < FAILURE_FAULT)
  | .complete => true
  | .failed => true

def targetOutput : Job -> Nat
  | .powerReroute => 8
  | .atmosphereScrub => 7
  | .coolantRepair => 8
  | .rationSynthesis => 10

def safeFault : Job -> Nat
  | .powerReroute => 5
  | .atmosphereScrub => 3
  | .coolantRepair => 4
  | .rationSynthesis => 5

def baseFault : Job -> Nat
  | .powerReroute => 2
  | .atmosphereScrub => 3
  | .coolantRepair => 3
  | .rationSynthesis => 1

def advanceGain : Job -> Nat
  | .powerReroute => 3
  | .atmosphereScrub => 2
  | .coolantRepair => 3
  | .rationSynthesis => 2

def advanceFault : Job -> Nat
  | .powerReroute => 1
  | .atmosphereScrub => 1
  | .coolantRepair => 1
  | .rationSynthesis => 1

def stabilizeAmount : Job -> Nat
  | .powerReroute => 2
  | .atmosphereScrub => 3
  | .coolantRepair => 2
  | .rationSynthesis => 1

def improviseGain : Job -> Nat
  | .powerReroute => 2
  | .atmosphereScrub => 3
  | .coolantRepair => 2
  | .rationSynthesis => 3

def improviseFault : Job -> Nat
  | .powerReroute => 2
  | .atmosphereScrub => 2
  | .coolantRepair => 1
  | .rationSynthesis => 2

def specialist : Job -> Tool
  | .powerReroute => .busCoupler
  | .atmosphereScrub => .scrubberMesh
  | .coolantRepair => .cryoPatch
  | .rationSynthesis => .cultureCatalyst

/-- The base pulse is job-specific.  Variant one adds pressure at turn three;
variant two advances that extra pulse to turn two.  The schedule is derived
from the finalized epoch and therefore cannot be rerolled by submitting a new
browser timestamp. -/
def pressurePulse (dispatch : Dispatch) (nextTurn : Nat) : Nat :=
  let base := match dispatch.job with
    | .powerReroute => if nextTurn % 2 = 0 then 1 else 0
    | .atmosphereScrub => if nextTurn % 3 = 0 then 1 else 0
    | .coolantRepair => if nextTurn = 3 || nextTurn = 5 then 1 else 0
    | .rationSynthesis => if nextTurn = 4 || nextTurn = 7 then 1 else 0
  let variant :=
    if dispatch.variant = 1 && nextTurn = 3 then 1
    else if dispatch.variant = 2 && nextTurn = 2 then 1
    else 0
  base + variant

def initialState (dispatch : Dispatch) (loadout : Loadout) : Option State :=
  let state : State := {
    dispatch
    loadout
    status := .active
    turn := 0
    output := 0
    fault := baseFault dispatch.job
    reserves := 2
    scanned := false
    primaryUsed := false
    secondaryUsed := false
  }
  if state.Valid then some state else none

inductive Action where
  | scan
  | advance
  | stabilize
  | improvise
  | usePrimary
  | useSecondary
  | certify
deriving Repr, DecidableEq

/-! ## The one transition function -/

private structure Patch where
  status : Status := .active
  output : Nat
  fault : Nat
  reserves : Nat
  scanned : Bool
  primaryUsed : Bool
  secondaryUsed : Bool

private def specialistPatch (state : State) (tool : Tool)
    (usePrimary : Bool) : Patch :=
  let matched := tool = specialist state.dispatch.job
  let output := state.output + (if matched then 3 else 1)
  let fault := if matched then state.fault - 1 else state.fault + 1
  {
    output
    fault
    reserves := state.reserves
    scanned := state.scanned
    primaryUsed := state.primaryUsed || usePrimary
    secondaryUsed := state.secondaryUsed || !usePrimary
  }

private def toolPatch (state : State) (tool : Tool) (usePrimary : Bool) : Patch :=
  match tool with
  | .diagnosticArray => {
      output := state.output
      fault := state.fault - 2
      reserves := state.reserves
      scanned := true
      primaryUsed := state.primaryUsed || usePrimary
      secondaryUsed := state.secondaryUsed || !usePrimary
    }
  | .spareCartridge => {
      output := state.output + 1
      fault := state.fault
      reserves := state.reserves + 2
      scanned := state.scanned
      primaryUsed := state.primaryUsed || usePrimary
      secondaryUsed := state.secondaryUsed || !usePrimary
    }
  | other => specialistPatch state other usePrimary

private def proposal (state : State) : Action -> Option Patch
  | .scan =>
      if state.scanned then none else some {
        output := state.output
        fault := state.fault - 1
        reserves := state.reserves
        scanned := true
        primaryUsed := state.primaryUsed
        secondaryUsed := state.secondaryUsed
      }
  | .advance => some {
      output := state.output + advanceGain state.dispatch.job
      fault := state.fault + advanceFault state.dispatch.job
      reserves := state.reserves
      scanned := state.scanned
      primaryUsed := state.primaryUsed
      secondaryUsed := state.secondaryUsed
    }
  | .stabilize =>
      if state.reserves = 0 then none else some {
        output := state.output
        fault := state.fault - stabilizeAmount state.dispatch.job
        reserves := state.reserves - 1
        scanned := state.scanned
        primaryUsed := state.primaryUsed
        secondaryUsed := state.secondaryUsed
      }
  | .improvise =>
      if state.reserves = 0 then none else some {
        output := state.output + improviseGain state.dispatch.job
        fault := state.fault + improviseFault state.dispatch.job
        reserves := state.reserves - 1
        scanned := state.scanned
        primaryUsed := state.primaryUsed
        secondaryUsed := state.secondaryUsed
      }
  | .usePrimary =>
      if state.primaryUsed then none
      else some (toolPatch state state.loadout.primary true)
  | .useSecondary =>
      if state.secondaryUsed then none
      else some (toolPatch state state.loadout.secondary false)
  | .certify =>
      if state.scanned &&
          decide (targetOutput state.dispatch.job <= state.output) &&
          decide (state.fault <= safeFault state.dispatch.job) then
        some {
          status := .complete
          output := state.output
          fault := state.fault
          reserves := state.reserves
          scanned := state.scanned
          primaryUsed := state.primaryUsed
          secondaryUsed := state.secondaryUsed
        }
      else none

private def applyPatch (state : State) (patch : Patch) : State :=
  let nextTurn := state.turn + 1
  let pressuredFault :=
    if patch.status = .active then
      patch.fault + pressurePulse state.dispatch nextTurn
    else patch.fault
  let nextStatus :=
    if patch.status = .complete then .complete
    else if FAILURE_FAULT <= pressuredFault || MAX_TURNS <= nextTurn then .failed
    else .active
  {
    dispatch := state.dispatch
    loadout := state.loadout
    status := nextStatus
    turn := nextTurn
    output := patch.output
    fault := pressuredFault
    reserves := patch.reserves
    scanned := patch.scanned
    primaryUsed := patch.primaryUsed
    secondaryUsed := patch.secondaryUsed
  }

private def admitState (state : State) : Option State :=
  if state.Valid then some state else none

/-- One semantic entry point.  Invalid starting projections, terminal states,
illegal verbs, over-capacity spare cartridges, and out-of-range results all
refuse. -/
def step (state : State) (action : Action) : Option State :=
  if state.Valid then
    if state.status = .active then
      match proposal state action with
      | none => none
      | some patch => admitState (applyPatch state patch)
    else none
  else none

def replayFrom : State -> List Action -> Option State
  | state, [] => some state
  | state, action :: rest =>
      match step state action with
      | none => none
      | some next => replayFrom next rest

def replay (dispatch : Dispatch) (loadout : Loadout)
    (actions : List Action) : Option State :=
  match initialState dispatch loadout with
  | none => none
  | some start => replayFrom start actions

/-! ## Derived, fixed rewards -/

def quality (state : State) : Nat :=
  (MAX_TURNS - state.turn) +
  (safeFault state.dispatch.job - state.fault) +
  state.reserves

def usedTool (state : State) (tool : Tool) : Bool :=
  (state.primaryUsed && state.loadout.primary = tool) ||
  (state.secondaryUsed && state.loadout.secondary = tool)

/-- No mission or submission supplies this table.  It is the complete v1 reward
authority.  The differing meter shapes make the four jobs useful to different
ship conditions without creating four new currencies. -/
def rawContribution (state : State) : RawContribution :=
  let q := quality state
  match state.dispatch.job with
  | .powerReroute => {
      intel := if usedTool state .diagnosticArray then 2 else 0
      supplies := 10 + q
      cohesion := if usedTool state .spareCartridge then 4 else 2
      influence := 0
      score := 100 + 10 * q
      relics := []
    }
  | .atmosphereScrub => {
      intel := 1
      supplies := 3
      cohesion := 9 + q
      influence := 0
      score := 110 + 10 * q
      relics := []
    }
  | .coolantRepair => {
      intel := 1
      supplies := 8 + q
      cohesion := 5
      influence := 0
      score := 120 + 10 * q
      relics := []
    }
  | .rationSynthesis => {
      intel := 0
      supplies := 12 + q
      cohesion := 4
      influence := 0
      score := 130 + 10 * q
      relics := []
    }

def contributionFor (state : State) : Option Contribution :=
  if state.Valid && state.status = .complete then
    validateContribution (rawContribution state)
  else none

/-! ## Epoch/counter settlement -/

/-- The only persistent care state.  There is deliberately no streak, missed-day
penalty, hunger meter or decaying multiplier. -/
structure CareRecord where
  lastClaimedEpoch : Option EpochId
  lastCounter : PlayerCounter
deriving DecidableEq

def CareRecord.empty : CareRecord where
  lastClaimedEpoch := none
  lastCounter := 0

def CareRecord.epochFresh (record : CareRecord) (epoch : EpochId) : Bool :=
  match record.lastClaimedEpoch with
  | none => true
  | some prior => decide (prior.value < epoch.value)

/-- `browserUtcDay` is retained so the future surface may explain a local clock
mismatch.  It is intentionally absent from every branch of `settle`. -/
structure Submission where
  dispatch : Dispatch
  presentedMissionEpoch : EpochId
  browserUtcDay : Nat
  claimCounter : PlayerCounter
  loadout : Loadout
  actions : List Action
deriving DecidableEq

structure Settlement where
  private mk ::
  finalState : State
  contribution : Contribution
  nextRecord : CareRecord
  missionEpoch : EpochId
  job : Job
  claimCounter : PlayerCounter
deriving DecidableEq

/-- Settle by replay.  The caller supplies no final state and no contribution.
The counter must be exactly the checked u64 successor, and epoch freshness is
strict. -/
def settle (record : CareRecord) (submission : Submission) : Option Settlement := do
  if submission.presentedMissionEpoch = submission.dispatch.epoch then
    if record.epochFresh submission.dispatch.epoch then
      match record.lastCounter.next with
      | none => none
      | some expectedCounter =>
          if submission.claimCounter = expectedCounter then
            match replay submission.dispatch submission.loadout submission.actions with
            | none => none
            | some finalState =>
                match contributionFor finalState with
                | none => none
                | some contribution => some {
                    finalState
                    contribution
                    nextRecord := {
                      lastClaimedEpoch := some submission.dispatch.epoch
                      lastCounter := submission.claimCounter
                    }
                    missionEpoch := submission.dispatch.epoch
                    job := submission.dispatch.job
                    claimCounter := submission.claimCounter
                  }
          else none
    else none
  else none

/-! ## General laws -/

theorem initialState_valid {dispatch : Dispatch} {loadout : Loadout} {state : State}
    (h : initialState dispatch loadout = some state) : state.Valid = true := by
  simp only [initialState] at h
  split at h <;> try contradiction
  rename_i hv
  cases h
  exact hv

private theorem admitState_valid {candidate accepted : State}
    (h : admitState candidate = some accepted) : accepted.Valid = true := by
  simp only [admitState] at h
  split at h <;> try contradiction
  rename_i hv
  injection h with heq
  rw [← heq]
  exact hv

theorem step_preserves_valid {state next : State} {action : Action}
    (h : step state action = some next) : next.Valid = true := by
  simp only [step] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  exact admitState_valid h

theorem step_deterministic {state first second : State} {action : Action}
    (hfirst : step state action = some first)
    (hsecond : step state action = some second) : first = second := by
  rw [hfirst] at hsecond
  exact Option.some.inj hsecond

theorem step_refuses_terminal (state : State) (action : Action)
    (hvalid : state.Valid = true) (hterminal : state.status != .active) :
    step state action = none := by
  have hstatus : state.status != .active := hterminal
  have hne : state.status ≠ .active := by
    intro heq
    simp [heq] at hstatus
  simp [step, hvalid, hne]

private theorem applyPatch_increments_turn (state : State) (patch : Patch) :
    (applyPatch state patch).turn = state.turn + 1 := rfl

theorem step_increments_turn {state next : State} {action : Action}
    (h : step state action = some next) : next.turn = state.turn + 1 := by
  simp only [step] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  rename_i patch hproposal
  simp only [admitState] at h
  split at h <;> try contradiction
  injection h with heq
  rw [← heq]
  exact applyPatch_increments_turn state patch

theorem successful_step_turn_bounded {state next : State} {action : Action}
    (h : step state action = some next) : next.turn <= MAX_TURNS := by
  have hv := step_preserves_valid h
  simp only [State.Valid, Bool.and_eq_true, decide_eq_true_eq] at hv
  exact hv.1.1.1.1.2

theorem replayFrom_deterministic {state first second : State} {actions : List Action}
    (hfirst : replayFrom state actions = some first)
    (hsecond : replayFrom state actions = some second) : first = second := by
  rw [hfirst] at hsecond
  exact Option.some.inj hsecond

theorem replayFrom_turn_count {state final : State} {actions : List Action}
    (h : replayFrom state actions = some final) :
    final.turn = state.turn + actions.length := by
  induction actions generalizing state with
  | nil =>
      simp only [replayFrom, Option.some.injEq] at h
      subst final
      simp
  | cons action rest ih =>
      simp only [replayFrom] at h
      split at h <;> try contradiction
      rename_i next hstep
      have htail := ih h
      have hone := step_increments_turn hstep
      simp only [List.length_cons]
      omega

theorem replayFrom_preserves_valid {state final : State} {actions : List Action}
    (hstate : state.Valid = true)
    (h : replayFrom state actions = some final) : final.Valid = true := by
  induction actions generalizing state with
  | nil =>
      simp only [replayFrom, Option.some.injEq] at h
      subst final
      exact hstate
  | cons action rest ih =>
      simp only [replayFrom] at h
      split at h <;> try contradiction
      rename_i next hstep
      exact ih (step_preserves_valid hstep) h

theorem replay_action_bound {dispatch : Dispatch} {loadout : Loadout}
    {actions : List Action} {final : State}
    (h : replay dispatch loadout actions = some final) :
    actions.length <= MAX_TURNS := by
  simp only [replay] at h
  split at h <;> try contradiction
  rename_i start hstart
  have hturn := replayFrom_turn_count h
  have hstartTurn : start.turn = 0 := by
    simp only [initialState] at hstart
    split at hstart <;> try contradiction
    injection hstart with heq
    rw [← heq]
  have hfinalValid := replayFrom_preserves_valid (initialState_valid hstart) h
  simp only [State.Valid, Bool.and_eq_true, decide_eq_true_eq] at hfinalValid
  have hbound := hfinalValid.1.1.1.1.2
  omega

theorem settle_browser_clock_irrelevant (record : CareRecord) (submission : Submission)
    (firstDay secondDay : Nat) :
    settle record { submission with browserUtcDay := firstDay } =
      settle record { submission with browserUtcDay := secondDay } := by
  rfl

theorem settle_history_irrelevant_when_admission_matches
    (first second : CareRecord) (submission : Submission)
    (hcounter : first.lastCounter = second.lastCounter)
    (hfresh : first.epochFresh submission.dispatch.epoch =
      second.epochFresh submission.dispatch.epoch) :
    settle first submission = settle second submission := by
  unfold settle
  rw [hfresh, hcounter]

theorem settle_deterministic {record : CareRecord} {submission : Submission}
    {first second : Settlement}
    (hfirst : settle record submission = some first)
    (hsecond : settle record submission = some second) : first = second := by
  rw [hfirst] at hsecond
  exact Option.some.inj hsecond

theorem settle_derives_contribution {record : CareRecord} {submission : Submission}
    {result : Settlement} (h : settle record submission = some result) :
    contributionFor result.finalState = some result.contribution := by
  simp only [settle] at h
  repeat' first | split at h <;> try contradiction
  cases h
  assumption

theorem settle_binds_dispatch_epoch {record : CareRecord} {submission : Submission}
    {result : Settlement} (h : settle record submission = some result) :
    result.missionEpoch = submission.dispatch.epoch := by
  simp only [settle] at h
  repeat' first | split at h <;> try contradiction
  cases h
  rfl

theorem settle_counter_is_successor {record : CareRecord} {submission : Submission}
    {result : Settlement} (h : settle record submission = some result) :
    record.lastCounter.next = some result.claimCounter := by
  simp only [settle] at h
  repeat' first | split at h <;> try contradiction
  cases h
  simp_all

theorem settle_advances_exact_counter {record : CareRecord} {submission : Submission}
    {result : Settlement} (h : settle record submission = some result) :
    result.claimCounter.val = record.lastCounter.val + 1 := by
  exact PlayerCounter.next_value (settle_counter_is_successor h)

theorem settle_records_claimed_epoch {record : CareRecord} {submission : Submission}
    {result : Settlement} (h : settle record submission = some result) :
    result.nextRecord.lastClaimedEpoch = some submission.dispatch.epoch := by
  simp only [settle] at h
  repeat' first | split at h <;> try contradiction
  cases h
  rfl

theorem settle_refuses_stale_epoch (record : CareRecord) (submission : Submission)
    (prior : EpochId) (hrecord : record.lastClaimedEpoch = some prior)
    (hstale : submission.dispatch.epoch.value <= prior.value) :
    settle record submission = none := by
  simp [settle, CareRecord.epochFresh, hrecord, Nat.not_lt.mpr hstale]

theorem settle_refuses_wrong_presented_epoch (record : CareRecord) (submission : Submission)
    (hwrong : submission.presentedMissionEpoch != submission.dispatch.epoch) :
    settle record submission = none := by
  have hne : submission.presentedMissionEpoch ≠ submission.dispatch.epoch := by
    intro heq
    simp [heq] at hwrong
  simp [settle, hne]

theorem settle_refuses_counter_exhaustion (record : CareRecord) (submission : Submission)
    (hmax : record.lastCounter.val + 1 = PLAYER_COUNTER_MODULUS) :
    settle record submission = none := by
  have hnext := PlayerCounter.max_refuses_next record.lastCounter hmax
  simp only [settle]
  split <;> try rfl
  split <;> try rfl
  rw [hnext]

/-! ## Strategy and hostile examples -/

def powerDispatch : Dispatch := dispatchForFinalizedEpoch ⟨0⟩
def atmosphereDispatch : Dispatch := dispatchForFinalizedEpoch ⟨1⟩
def coolantDispatch : Dispatch := dispatchForFinalizedEpoch ⟨2⟩
def rationDispatch : Dispatch := dispatchForFinalizedEpoch ⟨3⟩

def carefulPowerLoadout : Loadout := ⟨.diagnosticArray, .busCoupler⟩
def reservePowerLoadout : Loadout := ⟨.busCoupler, .spareCartridge⟩
def atmosphereLoadout : Loadout := ⟨.diagnosticArray, .scrubberMesh⟩
def coolantLoadout : Loadout := ⟨.diagnosticArray, .cryoPatch⟩
def rationLoadout : Loadout := ⟨.diagnosticArray, .cultureCatalyst⟩

def carefulPowerPlan : List Action :=
  [.usePrimary, .advance, .useSecondary, .advance, .certify]

def reservePowerPlan : List Action :=
  [.scan, .usePrimary, .useSecondary, .advance, .improvise, .certify]

def atmospherePlan : List Action :=
  [.usePrimary, .advance, .useSecondary, .advance, .certify]

def coolantPlan : List Action :=
  [.usePrimary, .advance, .useSecondary, .advance, .certify]

def rationPlan : List Action :=
  [.usePrimary, .advance, .useSecondary, .advance, .improvise, .certify]

theorem careful_power_completes :
    (replay powerDispatch carefulPowerLoadout carefulPowerPlan).map State.status =
      some .complete := by native_decide

theorem reserve_power_completes :
    (replay powerDispatch reservePowerLoadout reservePowerPlan).map State.status =
      some .complete := by native_decide

theorem careful_power_preserves_more_quality :
    (replay powerDispatch carefulPowerLoadout carefulPowerPlan).map quality = some 6 :=
  by native_decide

theorem reserve_power_trades_quality_for_cohesion :
    (replay powerDispatch reservePowerLoadout reservePowerPlan).map quality = some 4 :=
  by native_decide

theorem power_strategies_have_distinct_exact_contributions :
    (replay powerDispatch carefulPowerLoadout carefulPowerPlan >>= contributionFor).map
        (fun c => (c.intel.val, c.supplies.val, c.cohesion.val, c.score.val)) =
      some (2, 16, 2, 160) /\
    (replay powerDispatch reservePowerLoadout reservePowerPlan >>= contributionFor).map
        (fun c => (c.intel.val, c.supplies.val, c.cohesion.val, c.score.val)) =
      some (0, 14, 4, 140) := by native_decide

theorem authored_epoch_variant_changes_pressure_exactly :
    (replay powerDispatch carefulPowerLoadout carefulPowerPlan).map
        (fun state => (state.fault, quality state)) = some (3, 6) /\
    (replay (dispatchForFinalizedEpoch ⟨4⟩) carefulPowerLoadout carefulPowerPlan).map
        (fun state => (state.fault, quality state)) = some (4, 5) := by
  native_decide

theorem atmosphere_scrub_completes :
    (replay atmosphereDispatch atmosphereLoadout atmospherePlan).map State.status =
      some .complete := by native_decide

theorem coolant_repair_completes :
    (replay coolantDispatch coolantLoadout coolantPlan).map State.status =
      some .complete := by native_decide

theorem ration_synthesis_completes :
    (replay rationDispatch rationLoadout rationPlan).map State.status =
      some .complete := by native_decide

theorem three_other_jobs_have_distinct_exact_contributions :
    (replay atmosphereDispatch atmosphereLoadout atmospherePlan >>= contributionFor).map
        (fun c => (c.intel.val, c.supplies.val, c.cohesion.val, c.score.val)) =
      some (1, 3, 13, 150) /\
    (replay coolantDispatch coolantLoadout coolantPlan >>= contributionFor).map
        (fun c => (c.intel.val, c.supplies.val, c.cohesion.val, c.score.val)) =
      some (1, 13, 5, 170) /\
    (replay rationDispatch rationLoadout rationPlan >>= contributionFor).map
        (fun c => (c.intel.val, c.supplies.val, c.cohesion.val, c.score.val)) =
      some (0, 15, 4, 160) := by native_decide

theorem duplicate_tools_refuse :
    initialState powerDispatch ⟨.busCoupler, .busCoupler⟩ = none := by native_decide

theorem early_certification_refuses :
    (initialState powerDispatch carefulPowerLoadout >>= fun state => step state .certify) = none :=
  by native_decide

theorem duplicate_scan_refuses :
    replay powerDispatch carefulPowerLoadout [.scan, .scan] = none := by native_decide

theorem duplicate_tool_use_refuses :
    replay powerDispatch carefulPowerLoadout [.usePrimary, .usePrimary] = none :=
  by native_decide

theorem reserve_exhaustion_refuses :
    replay powerDispatch carefulPowerLoadout [.stabilize, .stabilize, .stabilize] = none :=
  by native_decide

theorem second_spare_cartridge_use_refuses :
    replay powerDispatch reservePowerLoadout [.useSecondary, .useSecondary] = none :=
  by native_decide

def nearFullSpareState : State := {
  dispatch := powerDispatch
  loadout := ⟨.spareCartridge, .busCoupler⟩
  status := .active
  turn := 0
  output := 0
  fault := 2
  reserves := 3
  scanned := false
  primaryUsed := false
  secondaryUsed := false
}

theorem near_full_spare_state_is_valid : nearFullSpareState.Valid = true := by
  native_decide

theorem over_capacity_spare_cartridge_refuses :
    step nearFullSpareState .usePrimary = none := by native_decide

def powerSubmission (browserUtcDay : Nat) : Submission := {
  dispatch := powerDispatch
  presentedMissionEpoch := powerDispatch.epoch
  browserUtcDay
  claimCounter := ⟨1, by norm_num [PLAYER_COUNTER_MODULUS]⟩
  loadout := carefulPowerLoadout
  actions := carefulPowerPlan
}

theorem first_power_claim_succeeds :
    (settle CareRecord.empty (powerSubmission 20_000)).isSome = true := by native_decide

theorem power_claim_ignores_browser_calendar :
    settle CareRecord.empty (powerSubmission 0) =
      settle CareRecord.empty (powerSubmission 4_294_967_295) := by native_decide

def replayedPowerSubmission : Submission := {
  powerSubmission 20_001 with
  claimCounter := ⟨2, by decide⟩
}

theorem same_epoch_second_claim_refuses :
    (settle CareRecord.empty (powerSubmission 20_000)).bind
      (fun first => settle first.nextRecord replayedPowerSubmission) = none := by
  native_decide

def gapRecord : CareRecord := {
  lastClaimedEpoch := some ⟨0⟩
  lastCounter := ⟨1, by decide⟩
}

def noHistoryAtCounterOne : CareRecord := {
  lastClaimedEpoch := none
  lastCounter := ⟨1, by decide⟩
}

def epochFourSubmission : Submission := {
  dispatch := dispatchForFinalizedEpoch ⟨4⟩
  presentedMissionEpoch := ⟨4⟩
  browserUtcDay := 20_004
  claimCounter := ⟨2, by decide⟩
  loadout := carefulPowerLoadout
  actions := carefulPowerPlan
}

/-- Four missed rotations do not lower the reward.  Both records have the same
counter; one records an old visit and one records no earlier visit at all. -/
theorem missed_epochs_do_not_change_reward :
    (settle gapRecord epochFourSubmission).map Settlement.contribution =
      (settle noHistoryAtCounterOne epochFourSubmission).map Settlement.contribution :=
  by native_decide

#assert_axioms dispatch_job_is_epoch_owned
#assert_axioms dispatch_variant_is_epoch_owned
#assert_axioms initialState_valid
#assert_axioms step_preserves_valid
#assert_axioms step_deterministic
#assert_axioms step_refuses_terminal
#assert_axioms step_increments_turn
#assert_axioms successful_step_turn_bounded
#assert_axioms replayFrom_deterministic
#assert_axioms replayFrom_turn_count
#assert_axioms replayFrom_preserves_valid
#assert_axioms replay_action_bound
#assert_axioms settle_browser_clock_irrelevant
#assert_axioms settle_history_irrelevant_when_admission_matches
#assert_axioms settle_deterministic
#assert_axioms settle_derives_contribution
#assert_axioms settle_binds_dispatch_epoch
#assert_axioms settle_counter_is_successor
#assert_axioms settle_advances_exact_counter
#assert_axioms settle_records_claimed_epoch
#assert_axioms settle_refuses_stale_epoch
#assert_axioms settle_refuses_wrong_presented_epoch
#assert_axioms settle_refuses_counter_exhaustion

#assert_compiled careful_power_completes
#assert_compiled reserve_power_completes
#assert_compiled careful_power_preserves_more_quality
#assert_compiled reserve_power_trades_quality_for_cohesion
#assert_compiled power_strategies_have_distinct_exact_contributions
#assert_compiled authored_epoch_variant_changes_pressure_exactly
#assert_compiled atmosphere_scrub_completes
#assert_compiled coolant_repair_completes
#assert_compiled ration_synthesis_completes
#assert_compiled three_other_jobs_have_distinct_exact_contributions
#assert_compiled duplicate_tools_refuse
#assert_compiled early_certification_refuses
#assert_compiled duplicate_scan_refuses
#assert_compiled duplicate_tool_use_refuses
#assert_compiled reserve_exhaustion_refuses
#assert_compiled second_spare_cartridge_use_refuses
#assert_compiled near_full_spare_state_is_valid
#assert_compiled over_capacity_spare_cartridge_refuses
#assert_compiled first_power_claim_succeeds
#assert_compiled power_claim_ignores_browser_calendar
#assert_compiled same_epoch_second_claim_refuses
#assert_compiled missed_epochs_do_not_change_reward

end Dregg2.Games.PathOfAngels.Shipworks
