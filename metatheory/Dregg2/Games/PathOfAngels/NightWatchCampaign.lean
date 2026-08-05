/-
# NightWatchCampaign — a Lean-authored shift aboard the Khovokhi

The player chooses an officer, station, and authored task.  The activated policy
and current state derive everything else: hazard roll, success, evidence,
resource movement, wounds/recovery, contribution, mastery, and beta discovery.
No action contains reward bytes.

The campaign emits exact logbook/event intents.  An intent deliberately lacks
an `EventBatch.FinalizedTurnCoordinate`, event digest, batch digest, and durable
append receipt.  The existing EventBatch authority must supply those later.
Holder presentation is accepted only as UI metadata and is erased before the
semantic command; it cannot affect score, resources, safety, mastery, or canon.
-/
import Dregg2.Games.PathOfAngels.ShipLifeProgression
import Dregg2.Games.PathOfAngels.OfficerLogbook
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.NightWatchCampaign

open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.CrewRelayExpedition

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

abbrev MAX_RULES : Nat := 32
abbrev MAX_HAZARD_CYCLE : Nat := 64
abbrev MAX_SHIFTS : Nat := 4096
abbrev MAX_HISTORY : Nat := 4096
abbrev MAX_RESOURCE : Nat := 1000000
abbrev MAX_EVIDENCE : Nat := 1000000
abbrev MAX_WOUNDS : Nat := 100
abbrev MAX_STRAIN : Nat := 100
abbrev MASTERY_LEVEL_SIZE : Nat := 10

/-! ## Authored campaign vocabulary -/

inductive Station where
  | bridge
  | engineSpine
  | signalGallery
  | containment
  | galley
  | infirmary
deriving DecidableEq, Repr

inductive Task where
  | plotDrift
  | coolantBalance
  | traceSignal
  | inspectSeal
  | rationAudit
  | recoveryRound
deriving DecidableEq, Repr

def Station.tag : Station → Nat
  | .bridge => 1
  | .engineSpine => 2
  | .signalGallery => 3
  | .containment => 4
  | .galley => 5
  | .infirmary => 6

def Task.tag : Task → Nat
  | .plotDrift => 1
  | .coolantBalance => 2
  | .traceSignal => 3
  | .inspectSeal => 4
  | .rationAudit => 5
  | .recoveryRound => 6

structure ContributionDelta where
  intel : Nat
  supplies : Nat
  cohesion : Nat
  influence : Nat
  score : Nat
deriving DecidableEq, Repr

def ContributionDelta.zero : ContributionDelta := ⟨0, 0, 0, 0, 0⟩

structure ShipResources where
  propellant : Nat
  munitions : Nat
  supplies : Nat
  morale : Nat
deriving DecidableEq, Repr

def ShipResources.boundedB (resources : ShipResources) : Bool :=
  decide (resources.propellant ≤ MAX_RESOURCE) &&
    decide (resources.munitions ≤ MAX_RESOURCE) &&
    decide (resources.supplies ≤ MAX_RESOURCE) &&
    decide (resources.morale ≤ MAX_RESOURCE)

/-- Explicit spends and gains make conservation/audit visible. -/
structure WorldEffects where
  spendPropellant : Nat := 0
  spendMunitions : Nat := 0
  spendSupplies : Nat := 0
  spendMorale : Nat := 0
  gainPropellant : Nat := 0
  gainMunitions : Nat := 0
  gainSupplies : Nat := 0
  gainMorale : Nat := 0
deriving DecidableEq, Repr

def WorldEffects.boundedB (effect : WorldEffects) : Bool :=
  [effect.spendPropellant, effect.spendMunitions, effect.spendSupplies,
    effect.spendMorale, effect.gainPropellant, effect.gainMunitions,
    effect.gainSupplies, effect.gainMorale].all fun value =>
      decide (value ≤ MAX_RESOURCE)

def WorldEffects.apply? (effect : WorldEffects)
    (before : ShipResources) : Option ShipResources := do
  if before.propellant < effect.spendPropellant then none
  if before.munitions < effect.spendMunitions then none
  if before.supplies < effect.spendSupplies then none
  if before.morale < effect.spendMorale then none
  let after : ShipResources := {
    propellant := before.propellant - effect.spendPropellant + effect.gainPropellant
    munitions := before.munitions - effect.spendMunitions + effect.gainMunitions
    supplies := before.supplies - effect.spendSupplies + effect.gainSupplies
    morale := before.morale - effect.spendMorale + effect.gainMorale
  }
  if !after.boundedB then none else some after

structure HealthEffect where
  woundsAdded : Nat := 0
  strainAdded : Nat := 0
  woundsRecovered : Nat := 0
  strainRecovered : Nat := 0
deriving DecidableEq, Repr

def HealthEffect.boundedB (effect : HealthEffect) : Bool :=
  decide (effect.woundsAdded ≤ MAX_WOUNDS) &&
    decide (effect.strainAdded ≤ MAX_STRAIN) &&
    decide (effect.woundsRecovered ≤ MAX_WOUNDS) &&
    decide (effect.strainRecovered ≤ MAX_STRAIN)

structure OfficerHealth where
  seat : SeatId
  wounds : Nat
  strain : Nat
  recoveryObserved : Nat
deriving DecidableEq, Repr

def OfficerHealth.apply (before : OfficerHealth) (effect : HealthEffect) :
    OfficerHealth :=
  let wounds := min MAX_WOUNDS
    (before.wounds + effect.woundsAdded - effect.woundsRecovered)
  let strain := min MAX_STRAIN
    (before.strain + effect.strainAdded - effect.strainRecovered)
  { before with
    wounds
    strain
    recoveryObserved := before.recoveryObserved +
      if effect.woundsRecovered + effect.strainRecovered > 0 then 1 else 0 }

def OfficerHealth.progressionView (health : OfficerHealth) :
    ShipLifeProgression.DerivedHealthView where
  wounds := health.wounds
  strain := health.strain
  inRecovery := decide (0 < health.wounds + health.strain)
  training := 0

structure TaskRule where
  station : Station
  task : Task
  role : CrewRole
  riskThreshold : Nat
  successContribution : ContributionDelta
  failureContribution : ContributionDelta
  successEffects : WorldEffects
  failureEffects : WorldEffects
  successHealth : HealthEffect
  failureHealth : HealthEffect
  successEvidence : Nat
  failureEvidence : Nat
  localService : Fin (GalleyMaintenanceDailyRuntime.MAX_LOCAL_SERVICE + 1)
  betaDiscovery : Option ContentContract.ArtifactId
  discoveryEvidenceRequired : Nat
  taskContentId : Digest32
  successContentId : Digest32
  failureContentId : Digest32
deriving DecidableEq

def TaskRule.key (rule : TaskRule) : Station × Task := (rule.station, rule.task)

def contributionBoundedB (value : ContributionDelta) : Bool :=
  [value.intel, value.supplies, value.cohesion, value.influence,
    value.score].all fun amount => decide (amount ≤ METRIC_LIMIT)

def taskRuleValidB (rule : TaskRule) : Bool :=
  decide (rule.riskThreshold ≤ 100) &&
    contributionBoundedB rule.successContribution &&
    contributionBoundedB rule.failureContribution &&
    rule.successEffects.boundedB && rule.failureEffects.boundedB &&
    rule.successHealth.boundedB && rule.failureHealth.boundedB &&
    decide (rule.successEvidence ≤ MAX_EVIDENCE) &&
    decide (rule.failureEvidence ≤ MAX_EVIDENCE) &&
    decide (rule.discoveryEvidenceRequired ≤ MAX_EVIDENCE)

structure RawConfig where
  schemaVersion : Nat
  progression : ShipLifeProgression.ProgressionIdentity
  logStream : EventBatch.StreamId
  roster : List Seat
  rules : List TaskRule
  hazardCycle : List Nat
  initialResources : ShipResources
  maxShifts : Nat
deriving DecidableEq

def configValidB (raw : RawConfig) : Bool :=
  decide (raw.schemaVersion > 0) &&
    decide (raw.logStream.aggregate.namespaceId = raw.progression.federationId) &&
    decide (raw.roster.length = CrewFieldMission.CREW_SIZE) &&
    decide (raw.roster.map Seat.id = [⟨0⟩, ⟨1⟩, ⟨2⟩, ⟨3⟩]) &&
    decide (raw.roster.map Seat.role = CrewFieldMission.expectedRoles) &&
    decide (raw.roster.map Seat.playerKey).Nodup &&
    decide (raw.rules ≠ []) && decide (raw.rules.length ≤ MAX_RULES) &&
    decide (raw.rules.map TaskRule.key).Nodup &&
    raw.rules.all taskRuleValidB &&
    decide (raw.hazardCycle ≠ []) &&
    decide (raw.hazardCycle.length ≤ MAX_HAZARD_CYCLE) &&
    raw.hazardCycle.all (fun roll => decide (roll < 100)) &&
    raw.initialResources.boundedB &&
    decide (0 < raw.maxShifts ∧ raw.maxShifts ≤ MAX_SHIFTS)

structure Config where
  private mk ::
  raw : RawConfig
  valid : configValidB raw = true

def activate? (raw : RawConfig) : Option Config :=
  if valid : configValidB raw = true then some ⟨raw, valid⟩ else none

/-! ## Derived shift state -/

structure MasteryRow where
  seat : SeatId
  station : Station
  xp : Nat
  level : Nat
deriving DecidableEq, Repr

def healthFor? : List OfficerHealth → SeatId → Option OfficerHealth
  | [], _ => none
  | row :: rows, seat => if row.seat = seat then some row else healthFor? rows seat

def setHealth : List OfficerHealth → OfficerHealth → List OfficerHealth
  | [], replacement => [replacement]
  | row :: rows, replacement =>
      if row.seat = replacement.seat then replacement :: rows
      else row :: setHealth rows replacement

def masteryFor : List MasteryRow → SeatId → Station → MasteryRow
  | [], seat, station => ⟨seat, station, 0, 0⟩
  | row :: rows, seat, station =>
      if row.seat = seat ∧ row.station = station then row
      else masteryFor rows seat station

def setMastery : List MasteryRow → MasteryRow → List MasteryRow
  | [], replacement => [replacement]
  | row :: rows, replacement =>
      if row.seat = replacement.seat ∧ row.station = replacement.station then
        replacement :: rows
      else row :: setMastery rows replacement

def findSeat? : List Seat → SeatId → Option Seat
  | [], _ => none
  | seat :: seats, id => if seat.id = id then some seat else findSeat? seats id

def findRule? : List TaskRule → Station → Task → Option TaskRule
  | [], _, _ => none
  | rule :: rules, station, task =>
      if rule.station = station ∧ rule.task = task then some rule
      else findRule? rules station task

structure BetaCanonProposal where
  sourceShift : Nat
  officer : Digest32
  artifact : ContentContract.ArtifactId
  evidence : Nat
  taskContentId : Digest32
deriving DecidableEq

structure ProgressionEffect where
  maintenanceSuccess : Nat
  meaningfulFailure : Nat
  trainingObserved : Nat
  recoveryObserved : Nat
deriving DecidableEq, Repr

structure ResolvedShift where
  shift : Nat
  officer : Seat
  rule : TaskRule
  hazardRoll : Nat
  success : Bool
  contribution : ContributionDelta
  worldEffects : WorldEffects
  resourcesBefore : ShipResources
  resourcesAfter : ShipResources
  healthBefore : OfficerHealth
  healthAfter : OfficerHealth
  evidenceBefore : Nat
  evidenceAfter : Nat
  betaProposal : Option BetaCanonProposal
  progression : ProgressionEffect
deriving DecidableEq

structure LogbookEntry where
  shift : Nat
  officer : Digest32
  seat : SeatId
  role : CrewRole
  participation : OfficerLogbook.Participation
  station : Station
  task : Task
  success : Bool
  hazardRoll : Nat
  riskThreshold : Nat
  contribution : ContributionDelta
  worldEffects : WorldEffects
  resourcesBefore : ShipResources
  resourcesAfter : ShipResources
  healthBefore : ShipLifeProgression.DerivedHealthView
  healthAfter : ShipLifeProgression.DerivedHealthView
  evidenceBefore : Nat
  evidenceAfter : Nat
  masteryBefore : MasteryRow
  masteryAfter : MasteryRow
  galleyLocalService : Option
    (Fin (GalleyMaintenanceDailyRuntime.MAX_LOCAL_SERVICE + 1))
  betaProposal : Option BetaCanonProposal
  progression : ProgressionEffect
  terminalContentId : Digest32
deriving DecidableEq

/-- Enough material to create an EventStatement after the host supplies the
current stream head and canonical payload digest.  It is not finality. -/
structure EventIntent where
  stream : EventBatch.StreamId
  expectedSequence : Nat
  entry : LogbookEntry
deriving DecidableEq

structure IntentDigestBoundary where
  payloadDigest : LogbookEntry → Digest32

def EventIntent.statement? (boundary : IntentDigestBoundary)
    (head : EventBatch.StreamHead) (intent : EventIntent) :
    Option EventSourcing.EventStatement := do
  if head.stream ≠ intent.stream then none
  if intent.expectedSequence ≠ head.sequence + 1 then none
  some {
    aggregate := intent.stream.aggregate
    version := intent.stream.version
    sequence := intent.expectedSequence
    predecessor := head.head
    payloadDigest := boundary.payloadDigest intent.entry
  }

/-- Explicit non-authority: an intent cannot manufacture an applied/finalized
batch. -/
def fabricateFinality (_intent : EventIntent) : Option EventBatch.AppliedBatch := none

theorem event_intent_has_no_finality (intent : EventIntent) :
    fabricateFinality intent = none := rfl

inductive Phase where
  | idle
  | claimed (officer : Seat)
  | assigned (officer : Seat) (rule : TaskRule)
  | awaitingDebrief (resolved : ResolvedShift)
deriving DecidableEq

structure State where
  private mk ::
  sequence : Nat
  shift : Nat
  resources : ShipResources
  evidence : Nat
  health : List OfficerHealth
  mastery : List MasteryRow
  phase : Phase
  history : List LogbookEntry
  intents : List EventIntent
  consumedActions : Finset Digest32
deriving DecidableEq

def initialState (config : Config) : State where
  sequence := 0
  shift := 0
  resources := config.raw.initialResources
  evidence := 0
  health := config.raw.roster.map fun seat => ⟨seat.id, 0, 0, 0⟩
  mastery := []
  phase := .idle
  history := []
  intents := []
  consumedActions := ∅

def hazardAt (config : Config) (shift : Nat) : Nat :=
  config.raw.hazardCycle.getD (shift % config.raw.hazardCycle.length) 0

inductive Action where
  | claimOfficer (actor : Digest32) (seat : SeatId)
  | chooseTask (station : Station) (task : Task)
  | resolve
  | debrief
deriving DecidableEq

structure Command where
  sequence : Nat
  nullifier : Digest32
  action : Action
deriving DecidableEq

/-- UI-only holder metadata.  It has no power field. -/
structure HolderPresentation where
  eligible : Bool
  affordance : Option ShipLifeProgression.HolderAffordance
deriving DecidableEq

/-- Raw client submission.  Any claimed semantic output causes admission to
fail; holder presentation is erased. -/
structure SubmittedCommand where
  command : Command
  claimedContribution : Option ContributionDelta := none
  claimedWorldEffects : Option WorldEffects := none
  claimedSafe : Option Bool := none
  claimedCanonArtifact : Option ContentContract.ArtifactId := none
  holder : Option HolderPresentation := none
deriving DecidableEq

def SubmittedCommand.admit? (submitted : SubmittedCommand) : Option Command := do
  if submitted.claimedContribution.isSome then none
  if submitted.claimedWorldEffects.isSome then none
  if submitted.claimedSafe.isSome then none
  if submitted.claimedCanonArtifact.isSome then none
  some submitted.command

theorem holder_presentation_erased (command : Command)
    (left right : Option HolderPresentation) :
    ({ command, holder := left : SubmittedCommand }).admit? =
      ({ command, holder := right : SubmittedCommand }).admit? := rfl

inductive Error where
  | wrongSequence
  | replayedAction
  | shiftLimit
  | wrongPhase
  | unknownOfficer
  | officerActorMismatch
  | unknownTask
  | roleMismatch
  | insufficientResources
  | resourceBound
  | evidenceBound
  | missingHealth
  | historyLimit
  | callerAuthoredOutcome
deriving DecidableEq, Repr

private def progressionOf (rule : TaskRule) (success : Bool)
    (before after : OfficerHealth) : ProgressionEffect where
  maintenanceSuccess :=
    if success && (rule.station = .engineSpine || rule.station = .galley) then 1 else 0
  meaningfulFailure := if success then 0 else 1
  trainingObserved := 1
  recoveryObserved :=
    if after.wounds < before.wounds || after.strain < before.strain then 1 else 0

private def resolveAssigned (config : Config) (state : State)
    (officer : Seat) (rule : TaskRule) : Except Error State := do
  let healthBefore ← match healthFor? state.health officer.id with
    | none => throw .missingHealth
    | some health => pure health
  let roll := hazardAt config state.shift
  let success := decide (rule.riskThreshold ≤ roll)
  let contribution := if success then rule.successContribution else rule.failureContribution
  let effects := if success then rule.successEffects else rule.failureEffects
  let healthEffect := if success then rule.successHealth else rule.failureHealth
  let evidenceGain := if success then rule.successEvidence else rule.failureEvidence
  let resourcesAfter ← match effects.apply? state.resources with
    | none => throw .insufficientResources
    | some resources => pure resources
  if !resourcesAfter.boundedB then throw .resourceBound
  if MAX_EVIDENCE < state.evidence + evidenceGain then throw .evidenceBound
  let evidenceAfter := state.evidence + evidenceGain
  let healthAfter := healthBefore.apply healthEffect
  let betaProposal :=
    if success && rule.discoveryEvidenceRequired ≤ evidenceAfter then
      rule.betaDiscovery.map fun artifact => {
        sourceShift := state.shift
        officer := officer.playerKey
        artifact
        evidence := evidenceAfter
        taskContentId := rule.taskContentId
      }
    else none
  let resolved : ResolvedShift := {
    shift := state.shift
    officer
    rule
    hazardRoll := roll
    success
    contribution
    worldEffects := effects
    resourcesBefore := state.resources
    resourcesAfter
    healthBefore
    healthAfter
    evidenceBefore := state.evidence
    evidenceAfter
    betaProposal
    progression := progressionOf rule success healthBefore healthAfter
  }
  pure { state with
    resources := resourcesAfter
    evidence := evidenceAfter
    health := setHealth state.health healthAfter
    phase := .awaitingDebrief resolved }

private def debriefResolved (config : Config) (state : State)
    (resolved : ResolvedShift) : Except Error State := do
  if state.history.length ≥ MAX_HISTORY then throw .historyLimit
  let masteryBefore := masteryFor state.mastery resolved.officer.id resolved.rule.station
  let xp := masteryBefore.xp + resolved.contribution.score + 1
  let masteryAfter : MasteryRow := {
    masteryBefore with xp, level := xp / MASTERY_LEVEL_SIZE }
  let localService := if resolved.rule.station = .galley then
    some resolved.rule.localService else none
  let terminalContentId := if resolved.success then
    resolved.rule.successContentId else resolved.rule.failureContentId
  let entry : LogbookEntry := {
    shift := resolved.shift
    officer := resolved.officer.playerKey
    seat := resolved.officer.id
    role := resolved.officer.role
    participation := .principal
    station := resolved.rule.station
    task := resolved.rule.task
    success := resolved.success
    hazardRoll := resolved.hazardRoll
    riskThreshold := resolved.rule.riskThreshold
    contribution := resolved.contribution
    worldEffects := resolved.worldEffects
    resourcesBefore := resolved.resourcesBefore
    resourcesAfter := resolved.resourcesAfter
    healthBefore := resolved.healthBefore.progressionView
    healthAfter := resolved.healthAfter.progressionView
    evidenceBefore := resolved.evidenceBefore
    evidenceAfter := resolved.evidenceAfter
    masteryBefore
    masteryAfter
    galleyLocalService := localService
    betaProposal := resolved.betaProposal
    progression := resolved.progression
    terminalContentId
  }
  let intent : EventIntent := {
    stream := config.raw.logStream
    expectedSequence := state.history.length + 1
    entry
  }
  pure { state with
    shift := state.shift + 1
    mastery := setMastery state.mastery masteryAfter
    phase := .idle
    history := state.history ++ [entry]
    intents := state.intents ++ [intent] }

private def applyAction (config : Config) (state : State)
    (action : Action) : Except Error State :=
  match action, state.phase with
  | .claimOfficer actor seatId, .idle => do
      if state.shift ≥ config.raw.maxShifts then throw .shiftLimit
      let officer ← match findSeat? config.raw.roster seatId with
        | none => throw .unknownOfficer
        | some officer => pure officer
      if actor ≠ officer.playerKey then throw .officerActorMismatch
      pure { state with phase := .claimed officer }
  | .chooseTask station task, .claimed officer => do
      let rule ← match findRule? config.raw.rules station task with
        | none => throw .unknownTask
        | some rule => pure rule
      if officer.role ≠ rule.role then throw .roleMismatch
      pure { state with phase := .assigned officer rule }
  | .resolve, .assigned officer rule => resolveAssigned config state officer rule
  | .debrief, .awaitingDebrief resolved => debriefResolved config state resolved
  | _, _ => .error .wrongPhase

/-- The canonical semantic judge.  Sequence and nullifier advance even for a
meaningful risk failure, but never for a refused command. -/
def judge (config : Config) (state : State) (command : Command) :
    Except Error State := do
  if command.sequence ≠ state.sequence then throw .wrongSequence
  if command.nullifier ∈ state.consumedActions then throw .replayedAction
  let next ← applyAction config state command.action
  pure { next with
    sequence := state.sequence + 1
    consumedActions := insert command.nullifier state.consumedActions }

def judgeSubmitted (config : Config) (state : State)
    (submitted : SubmittedCommand) : Except Error State :=
  match submitted.admit? with
  | none => .error .callerAuthoredOutcome
  | some command => judge config state command

theorem holder_status_cannot_change_transition (config : Config) (state : State)
    (command : Command) (left right : Option HolderPresentation) :
    judgeSubmitted config state { command, holder := left } =
      judgeSubmitted config state { command, holder := right } := rfl

def replay (config : Config) : State → List Command → Except Error State
  | state, [] => .ok state
  | state, command :: commands => do
      let next ← judge config state command
      replay config next commands

theorem replay_append (config : Config) (state : State)
    (left right : List Command) :
    replay config state (left ++ right) = do
      let middle ← replay config state left
      replay config middle right := by
  induction left generalizing state with
  | nil => rfl
  | cons command commands ih =>
      simp only [List.cons_append, replay]
      cases judge config state command <;> simp [ih]

theorem replay_deterministic (config : Config) (state : State)
    (commands : List Command) {left right : State}
    (hl : replay config state commands = .ok left)
    (hr : replay config state commands = .ok right) : left = right := by
  rw [hl] at hr
  exact Except.ok.inj hr

theorem caller_claimed_outcome_is_refused (config : Config) (state : State)
    (command : Command) (claimed : ContributionDelta) :
    judgeSubmitted config state {
      command
      claimedContribution := some claimed
    } = .error .callerAuthoredOutcome := by
  rfl

#assert_axioms event_intent_has_no_finality
#assert_axioms holder_presentation_erased
#assert_axioms holder_status_cannot_change_transition
#assert_axioms replay_append
#assert_axioms replay_deterministic
#assert_axioms caller_claimed_outcome_is_refused

end Dregg2.Games.PathOfAngels.NightWatchCampaign
