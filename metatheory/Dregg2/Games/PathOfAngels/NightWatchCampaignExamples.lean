/-
# NightWatchCampaignExamples — the first constructed `NightWatchCampaign.Config`

`NightWatchCampaign` is a complete Lean-authored judged game kernel with six pinned
theorems, and every one of them is parametric over `Config`.  Until this file, **no
value of `Config` existed anywhere in the repository**: no `activate?` call, no
`RawConfig` literal, no fixture.  The kernel had never been run on any input, so the
satisfiability of its own validity floor `configValidB` was unproven and those six
theorems held of a type nothing had exhibited.  That is the parametric-theorem-over-an-
uninhabited-premise class that cost the Galley kernel ~5,100 deleted lines.

This module closes it by exhibiting one:

* `fixture_config_valid` / `fixture_config_activates` — `configValidB` IS satisfiable,
  by a named authored config, and `activate?` accepts it.  `Config.mk` is private, so
  `activate?` is the only route; `campaign_config_constructor_is_private` proves that,
  which is what makes the activation theorem load-bearing rather than decorative.
* A four-watch campaign replayed to an EXACT state: a success, a meaningful failure, a
  recovery, and a galley watch that levels a seat up and wraps the hazard cycle.
* Refusal theorems that each assert the exact `Error` constructor AND pin the reason,
  by exhibiting the minimal neighbouring command that IS accepted.  A refusal that
  fires through a different check than its name says is a defect this project has been
  bitten by repeatedly; every refusal below is isolated to one changed field.

Everything here is authored and judged in Lean.  No Rust participates: the kernel, the
config, the commands and the expected outcomes are all Lean terms, and the pins below
say exactly which of them the kernel checked and which the compiled evaluator did.

⚑ Two structural facts about `NightWatchCampaign` that shape this file.  `Config.mk`
and `State.mk` are both `private`, so from an importing module neither a config nor a
state can be written down as a literal.  A config is obtained through `activate?`; a
state is pinned through `StateView` + `state_view_is_injective`, which names all ten
`State` fields and proves that naming them names the state.
-/
import Dregg2.Games.PathOfAngels.NightWatchCampaign
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.NightWatchCampaignExamples

open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.NightWatchCampaign

set_option autoImplicit false
set_option maxRecDepth 100000

/-! ## Opaque authored digests

Every digest below is a byte-replicated literal with a distinct tag.  Nothing in this
module lets a `decide`/`native_decide` push a digest through a sponge — `NightWatchCampaign`
never hashes — so the digest fields stay cheap, opaque, comparable literals. -/

def digest (tag : Nat) : Digest32 where
  bytes := List.replicate 32 (⟨tag % 256, Nat.mod_lt _ (by omega)⟩ : Fin 256)
  length_eq := by simp

/-! ## The authored deployment identity

`configValidB` requires `logStream.aggregate.namespaceId = progression.federationId`;
both are `digest 1` below, and `fixture_log_stream_is_a_valid_event_stream` additionally
shows the stream would pass `EventBatch.StreamId.validB`, which `configValidB` does not
itself demand. -/

def fixtureProgression : ShipLifeProgression.ProgressionIdentity where
  federationId := digest 1
  contentSession := digest 2
  contentEpoch := ⟨7⟩
  season := ⟨3⟩
  activationDigest := digest 3
  owner := digest 4

def fixtureWorld : EventBatch.WorldIdentity where
  federationId := digest 1
  contentRoot := digest 5
  activationDigest := digest 3
  contentSession := digest 2
  contentEpoch := ⟨7⟩

def fixtureLogStream : EventBatch.StreamId where
  world := fixtureWorld
  aggregate := { namespaceId := digest 1, kind := 9, key := digest 6 }
  version := ⟨1⟩

/-! ## The roster

`configValidB` pins the roster to exactly `CrewFieldMission.CREW_SIZE` seats, with ids
`[⟨0⟩, ⟨1⟩, ⟨2⟩, ⟨3⟩]` in order, roles exactly `CrewFieldMission.expectedRoles`, and
pairwise distinct player keys. -/

def pathfinderSeat : CrewRelayExpedition.Seat where
  id := ⟨0⟩
  playerKey := digest 10
  credential := ⟨100⟩
  role := .pathfinder
  initialCounter := 0

def engineerSeat : CrewRelayExpedition.Seat where
  id := ⟨1⟩
  playerKey := digest 11
  credential := ⟨101⟩
  role := .engineer
  initialCounter := 0

def containmentSeat : CrewRelayExpedition.Seat where
  id := ⟨2⟩
  playerKey := digest 12
  credential := ⟨102⟩
  role := .containment
  initialCounter := 0

def quartermasterSeat : CrewRelayExpedition.Seat where
  id := ⟨3⟩
  playerKey := digest 13
  credential := ⟨103⟩
  role := .quartermaster
  initialCounter := 0

def fixtureRoster : List CrewRelayExpedition.Seat :=
  [pathfinderSeat, engineerSeat, containmentSeat, quartermasterSeat]

/-! ## The authored task table

`hazardAt config shift = hazardCycle.getD (shift % hazardCycle.length) 0` and
`success := decide (rule.riskThreshold ≤ roll)`, so with `hazardCycle = [70, 10, 55]`
the outcome of every watch is fully determined by its shift.  The thresholds below are
chosen so the four-watch campaign demonstrates, in order: a success, a *meaningful
failure*, a real recovery, and a galley success at the wrapped hazard index. -/

/-- Shift 0 (roll 70) succeeds at threshold 40.  Authors a beta discovery whose evidence
bar is met, so this watch is the one that proposes canon. -/
def coolantBalanceRule : TaskRule where
  station := .engineSpine
  task := .coolantBalance
  role := .engineer
  riskThreshold := 40
  successContribution := ⟨3, 0, 2, 0, 5⟩
  failureContribution := ⟨0, 0, 1, 0, 1⟩
  successEffects := { spendSupplies := 2, gainPropellant := 6, gainMorale := 3 }
  failureEffects := { spendSupplies := 1, spendMorale := 2 }
  successHealth := { strainAdded := 1 }
  failureHealth := { woundsAdded := 2, strainAdded := 3 }
  successEvidence := 7
  failureEvidence := 1
  localService := 0
  betaDiscovery := some ⟨9001⟩
  discoveryEvidenceRequired := 5
  taskContentId := digest 60
  successContentId := digest 61
  failureContentId := digest 62

/-- Shift 1 (roll 10) FAILS at threshold 60.  It authors a discovery with a zero evidence
bar, so the only thing withholding canon on this watch is the failure itself. -/
def inspectSealRule : TaskRule where
  station := .containment
  task := .inspectSeal
  role := .containment
  riskThreshold := 60
  successContribution := ⟨4, 1, 0, 0, 6⟩
  failureContribution := ⟨0, 0, 1, 0, 2⟩
  successEffects := { gainSupplies := 5 }
  failureEffects := { spendSupplies := 3, spendMorale := 4, gainMunitions := 1 }
  successHealth := { strainAdded := 1 }
  failureHealth := { woundsAdded := 2, strainAdded := 1 }
  successEvidence := 9
  failureEvidence := 2
  localService := 0
  betaDiscovery := some ⟨9003⟩
  discoveryEvidenceRequired := 0
  taskContentId := digest 63
  successContentId := digest 64
  failureContentId := digest 65

/-- Shift 2 (roll 55) succeeds at threshold 30 and heals the wounds shift 1 inflicted.
Its discovery bar (100) is above the evidence the campaign can reach, so it is the
control showing the *gate*, not the success flag, is what withholds canon here. -/
def recoveryRoundRule : TaskRule where
  station := .infirmary
  task := .recoveryRound
  role := .containment
  riskThreshold := 30
  successContribution := ⟨0, 0, 5, 0, 8⟩
  failureContribution := ⟨0, 0, 0, 0, 1⟩
  successEffects := { spendSupplies := 4, gainMorale := 2 }
  failureEffects := { spendMorale := 1 }
  successHealth := { woundsRecovered := 2, strainRecovered := 1 }
  failureHealth := { strainAdded := 1 }
  successEvidence := 3
  failureEvidence := 0
  localService := 0
  betaDiscovery := some ⟨9002⟩
  discoveryEvidenceRequired := 100
  taskContentId := digest 69
  successContentId := digest 70
  failureContentId := digest 71

/-- Shift 3 wraps the hazard cycle back to index 0 (roll 70) and succeeds at threshold 20.
The only `.galley` rule, so the only one whose `localService` reaches a logbook entry. -/
def rationAuditRule : TaskRule where
  station := .galley
  task := .rationAudit
  role := .quartermaster
  riskThreshold := 20
  successContribution := ⟨0, 4, 3, 0, 12⟩
  failureContribution := ⟨0, 0, 0, 0, 1⟩
  successEffects := { spendPropellant := 1, gainSupplies := 9, gainMorale := 2 }
  failureEffects := { spendSupplies := 2 }
  successHealth := { strainAdded := 2 }
  failureHealth := { strainAdded := 4 }
  successEvidence := 4
  failureEvidence := 0
  localService := 40
  betaDiscovery := none
  discoveryEvidenceRequired := 0
  taskContentId := digest 72
  successContentId := digest 73
  failureContentId := digest 74

/-- A valid authored rule the ship cannot afford: its success arm spends more propellant
than the campaign ever holds.  It exists to make `.insufficientResources` reachable from
the SAME config, so that refusal is demonstrated on the fixture rather than asserted. -/
def unaffordableSurveyRule : TaskRule where
  station := .signalGallery
  task := .traceSignal
  role := .pathfinder
  riskThreshold := 50
  successContribution := ⟨6, 0, 0, 0, 4⟩
  failureContribution := ⟨0, 0, 0, 0, 1⟩
  successEffects := { spendPropellant := 999999 }
  failureEffects := { spendMorale := 1 }
  successHealth := { strainAdded := 1 }
  failureHealth := { strainAdded := 2 }
  successEvidence := 1
  failureEvidence := 0
  localService := 0
  betaDiscovery := none
  discoveryEvidenceRequired := 0
  taskContentId := digest 75
  successContentId := digest 76
  failureContentId := digest 77

/-- `maxShifts = 4` is deliberately exactly the campaign length, so the ceiling is
reachable and `the_campaign_refuses_a_fifth_watch_at_the_authored_shift_ceiling` is a
real refusal rather than a statement about an unreachable bound.
`(.bridge, .plotDrift)` is deliberately left unauthored so `.unknownTask` is reachable. -/
def fixtureRawConfig : RawConfig where
  schemaVersion := 1
  progression := fixtureProgression
  logStream := fixtureLogStream
  roster := fixtureRoster
  rules :=
    [coolantBalanceRule, inspectSealRule, recoveryRoundRule, rationAuditRule,
     unaffordableSurveyRule]
  hazardCycle := [70, 10, 55]
  initialResources := ⟨120, 40, 60, 50⟩
  maxShifts := 4

/-! ## `configValidB` is satisfiable — the theorem this module exists for

Every conjunct of the fifteen-clause floor at `NightWatchCampaign.lean:216` holds of
`fixtureRawConfig`.  Compiled evaluation, not the kernel: the floor decides `Nodup` over
four 32-byte digests and five rule keys, which the compiler settles in milliseconds. -/

theorem fixture_config_valid : configValidB fixtureRawConfig = true := by
  native_decide

theorem fixture_log_stream_is_a_valid_event_stream :
    EventBatch.StreamId.validB fixtureLogStream = true := by
  native_decide

theorem fixture_activate_isSome : (activate? fixtureRawConfig).isSome = true := by
  unfold NightWatchCampaign.activate?
  rw [dif_pos fixture_config_valid]
  rfl

/-- The first `NightWatchCampaign.Config` value in the repository. -/
def fixtureConfig : Config := (activate? fixtureRawConfig).get fixture_activate_isSome

theorem fixture_config_activates : activate? fixtureRawConfig = some fixtureConfig :=
  (Option.some_get fixture_activate_isSome).symm

theorem fixture_config_raw : fixtureConfig.raw = fixtureRawConfig := by
  have h : activate? fixtureRawConfig = some fixtureConfig := fixture_config_activates
  unfold NightWatchCampaign.activate? at h
  rw [dif_pos fixture_config_valid] at h
  injection h with h
  exact (congrArg NightWatchCampaign.Config.raw h).symm

/-! ## Constructor teeth

These are what make the activation theorem load-bearing.  If either constructor were
made public, a downstream module could mint a `Config` that never crossed `configValidB`
(or a `State` that never crossed `judge`), and `fixture_config_activates` would stop
being the only route in.  Both declarations turn red on that change. -/

theorem campaign_config_constructor_is_private : True := by
  fail_if_success (have _constructor := @NightWatchCampaign.Config.mk)
  trivial

theorem campaign_state_constructor_is_private : True := by
  fail_if_success (have _constructor := @NightWatchCampaign.State.mk)
  trivial

/-! ## Naming a state

`State.mk` is private, so no importing module can write a state literal.  `StateView`
names all ten `State` fields and `state_view_is_injective` proves that a `StateView`
determines the `State` it came from — so `view s = v` below is an EXACT state claim,
not a partial observation. -/

structure StateView where
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

def view (state : State) : StateView where
  sequence := state.sequence
  shift := state.shift
  resources := state.resources
  evidence := state.evidence
  health := state.health
  mastery := state.mastery
  phase := state.phase
  history := state.history
  intents := state.intents
  consumedActions := state.consumedActions

theorem state_view_is_injective {left right : State} (h : view left = view right) :
    left = right := by
  have h1 : left.sequence = right.sequence := congrArg StateView.sequence h
  have h2 : left.shift = right.shift := congrArg StateView.shift h
  have h3 : left.resources = right.resources := congrArg StateView.resources h
  have h4 : left.evidence = right.evidence := congrArg StateView.evidence h
  have h5 : left.health = right.health := congrArg StateView.health h
  have h6 : left.mastery = right.mastery := congrArg StateView.mastery h
  have h7 : left.phase = right.phase := congrArg StateView.phase h
  have h8 : left.history = right.history := congrArg StateView.history h
  have h9 : left.intents = right.intents := congrArg StateView.intents h
  have h10 : left.consumedActions = right.consumedActions :=
    congrArg StateView.consumedActions h
  clear h
  cases left
  cases right
  simp_all

/-- The strict phase cycle `applyAction` enforces, as a number, so a whole replay's
phase trace can be stated in one list. -/
def phaseStage : Phase → Nat
  | .idle => 0
  | .claimed _ => 1
  | .assigned _ _ => 2
  | .awaitingDebrief _ => 3

/-! ## The campaign — sixteen commands, four strict watches -/

def cmd (index : Nat) (action : Action) : Command where
  sequence := index
  nullifier := digest (200 + index)
  action

/-- Shift 0: the engineer balances coolant.  Roll 70 ≥ threshold 40, so it SUCCEEDS. -/
def watchOne : List Command :=
  [ cmd 0 (.claimOfficer (digest 11) ⟨1⟩)
  , cmd 1 (.chooseTask .engineSpine .coolantBalance)
  , cmd 2 .resolve
  , cmd 3 .debrief ]

/-- Shift 1: containment inspects a seal.  Roll 10 < threshold 60, so it FAILS — and a
meaningful failure is not an error: it still moves resources, wounds the officer, earns
evidence and mastery, appends a logbook entry, and advances the shift. -/
def watchTwo : List Command :=
  [ cmd 4 (.claimOfficer (digest 12) ⟨2⟩)
  , cmd 5 (.chooseTask .containment .inspectSeal)
  , cmd 6 .resolve
  , cmd 7 .debrief ]

/-- Shift 2: the same officer recovers in the infirmary.  Roll 55 ≥ threshold 30. -/
def watchThree : List Command :=
  [ cmd 8 (.claimOfficer (digest 12) ⟨2⟩)
  , cmd 9 (.chooseTask .infirmary .recoveryRound)
  , cmd 10 .resolve
  , cmd 11 .debrief ]

/-- Shift 3: the quartermaster audits rations.  The hazard index wraps to 0 (roll 70). -/
def watchFour : List Command :=
  [ cmd 12 (.claimOfficer (digest 13) ⟨3⟩)
  , cmd 13 (.chooseTask .galley .rationAudit)
  , cmd 14 .resolve
  , cmd 15 .debrief ]

def campaign : List Command := watchOne ++ watchTwo ++ watchThree ++ watchFour

def runFrom (commands : List Command) : Except Error State :=
  replay fixtureConfig (initialState fixtureConfig) commands

/-! ## The exact expected logbook

These four entries are the campaign's whole semantic output.  They are authored here as
literals and proved equal to what `debriefResolved` actually appended. -/

def entryOne : LogbookEntry where
  shift := 0
  officer := digest 11
  seat := ⟨1⟩
  role := .engineer
  participation := .principal
  station := .engineSpine
  task := .coolantBalance
  success := true
  hazardRoll := 70
  riskThreshold := 40
  contribution := ⟨3, 0, 2, 0, 5⟩
  worldEffects := { spendSupplies := 2, gainPropellant := 6, gainMorale := 3 }
  resourcesBefore := ⟨120, 40, 60, 50⟩
  resourcesAfter := ⟨126, 40, 58, 53⟩
  healthBefore := ⟨0, 0, false, 0⟩
  healthAfter := ⟨0, 1, true, 0⟩
  evidenceBefore := 0
  evidenceAfter := 7
  masteryBefore := ⟨⟨1⟩, .engineSpine, 0, 0⟩
  masteryAfter := ⟨⟨1⟩, .engineSpine, 6, 0⟩
  galleyLocalService := none
  betaProposal := some ⟨0, digest 11, ⟨9001⟩, 7, digest 60⟩
  progression := ⟨1, 0, 1, 0⟩
  terminalContentId := digest 61

def entryTwo : LogbookEntry where
  shift := 1
  officer := digest 12
  seat := ⟨2⟩
  role := .containment
  participation := .principal
  station := .containment
  task := .inspectSeal
  success := false
  hazardRoll := 10
  riskThreshold := 60
  contribution := ⟨0, 0, 1, 0, 2⟩
  worldEffects := { spendSupplies := 3, spendMorale := 4, gainMunitions := 1 }
  resourcesBefore := ⟨126, 40, 58, 53⟩
  resourcesAfter := ⟨126, 41, 55, 49⟩
  healthBefore := ⟨0, 0, false, 0⟩
  healthAfter := ⟨2, 1, true, 0⟩
  evidenceBefore := 7
  evidenceAfter := 9
  masteryBefore := ⟨⟨2⟩, .containment, 0, 0⟩
  masteryAfter := ⟨⟨2⟩, .containment, 3, 0⟩
  galleyLocalService := none
  betaProposal := none
  progression := ⟨0, 1, 1, 0⟩
  terminalContentId := digest 65

def entryThree : LogbookEntry where
  shift := 2
  officer := digest 12
  seat := ⟨2⟩
  role := .containment
  participation := .principal
  station := .infirmary
  task := .recoveryRound
  success := true
  hazardRoll := 55
  riskThreshold := 30
  contribution := ⟨0, 0, 5, 0, 8⟩
  worldEffects := { spendSupplies := 4, gainMorale := 2 }
  resourcesBefore := ⟨126, 41, 55, 49⟩
  resourcesAfter := ⟨126, 41, 51, 51⟩
  healthBefore := ⟨2, 1, true, 0⟩
  healthAfter := ⟨0, 0, false, 0⟩
  evidenceBefore := 9
  evidenceAfter := 12
  masteryBefore := ⟨⟨2⟩, .infirmary, 0, 0⟩
  masteryAfter := ⟨⟨2⟩, .infirmary, 9, 0⟩
  galleyLocalService := none
  betaProposal := none
  progression := ⟨0, 0, 1, 1⟩
  terminalContentId := digest 70

def entryFour : LogbookEntry where
  shift := 3
  officer := digest 13
  seat := ⟨3⟩
  role := .quartermaster
  participation := .principal
  station := .galley
  task := .rationAudit
  success := true
  hazardRoll := 70
  riskThreshold := 20
  contribution := ⟨0, 4, 3, 0, 12⟩
  worldEffects := { spendPropellant := 1, gainSupplies := 9, gainMorale := 2 }
  resourcesBefore := ⟨126, 41, 51, 51⟩
  resourcesAfter := ⟨125, 41, 60, 53⟩
  healthBefore := ⟨0, 0, false, 0⟩
  healthAfter := ⟨0, 2, true, 0⟩
  evidenceBefore := 12
  evidenceAfter := 16
  masteryBefore := ⟨⟨3⟩, .galley, 0, 0⟩
  masteryAfter := ⟨⟨3⟩, .galley, 13, 1⟩
  galleyLocalService := some 40
  betaProposal := none
  progression := ⟨1, 0, 1, 0⟩
  terminalContentId := digest 73

def campaignHistory : List LogbookEntry := [entryOne, entryTwo, entryThree, entryFour]

def intentOne : EventIntent := ⟨fixtureLogStream, 1, entryOne⟩
def intentTwo : EventIntent := ⟨fixtureLogStream, 2, entryTwo⟩
def intentThree : EventIntent := ⟨fixtureLogStream, 3, entryThree⟩
def intentFour : EventIntent := ⟨fixtureLogStream, 4, entryFour⟩

def campaignIntents : List EventIntent := [intentOne, intentTwo, intentThree, intentFour]

/-- The exact resolved shift the third command of watch one produces, before the debrief
turns it into a logbook entry.  `ResolvedShift` has a public constructor, so this one
intermediate object CAN be written down literally. -/
def resolvedOne : ResolvedShift where
  shift := 0
  officer := engineerSeat
  rule := coolantBalanceRule
  hazardRoll := 70
  success := true
  contribution := ⟨3, 0, 2, 0, 5⟩
  worldEffects := { spendSupplies := 2, gainPropellant := 6, gainMorale := 3 }
  resourcesBefore := ⟨120, 40, 60, 50⟩
  resourcesAfter := ⟨126, 40, 58, 53⟩
  healthBefore := ⟨⟨1⟩, 0, 0, 0⟩
  healthAfter := ⟨⟨1⟩, 0, 1, 0⟩
  evidenceBefore := 0
  evidenceAfter := 7
  betaProposal := some ⟨0, digest 11, ⟨9001⟩, 7, digest 60⟩
  progression := ⟨1, 0, 1, 0⟩

/-! ## The exact states -/

def viewInitial : StateView where
  sequence := 0
  shift := 0
  resources := ⟨120, 40, 60, 50⟩
  evidence := 0
  health := [⟨⟨0⟩, 0, 0, 0⟩, ⟨⟨1⟩, 0, 0, 0⟩, ⟨⟨2⟩, 0, 0, 0⟩, ⟨⟨3⟩, 0, 0, 0⟩]
  mastery := []
  phase := .idle
  history := []
  intents := []
  consumedActions := ∅

def viewAfterWatchOne : StateView where
  sequence := 4
  shift := 1
  resources := ⟨126, 40, 58, 53⟩
  evidence := 7
  health := [⟨⟨0⟩, 0, 0, 0⟩, ⟨⟨1⟩, 0, 1, 0⟩, ⟨⟨2⟩, 0, 0, 0⟩, ⟨⟨3⟩, 0, 0, 0⟩]
  mastery := [⟨⟨1⟩, .engineSpine, 6, 0⟩]
  phase := .idle
  history := [entryOne]
  intents := [intentOne]
  consumedActions := {digest 200, digest 201, digest 202, digest 203}

def viewAfterCampaign : StateView where
  sequence := 16
  shift := 4
  resources := ⟨125, 41, 60, 53⟩
  evidence := 16
  health := [⟨⟨0⟩, 0, 0, 0⟩, ⟨⟨1⟩, 0, 1, 0⟩, ⟨⟨2⟩, 0, 0, 1⟩, ⟨⟨3⟩, 0, 2, 0⟩]
  mastery :=
    [⟨⟨1⟩, .engineSpine, 6, 0⟩, ⟨⟨2⟩, .containment, 3, 0⟩,
     ⟨⟨2⟩, .infirmary, 9, 0⟩, ⟨⟨3⟩, .galley, 13, 1⟩]
  phase := .idle
  history := campaignHistory
  intents := campaignIntents
  consumedActions := (campaign.map Command.nullifier).toFinset

theorem initial_state_is_the_authored_initial_condition :
    view (initialState fixtureConfig) = viewInitial := by
  native_decide

theorem hazard_cycle_is_deterministic_and_wraps_at_the_cycle_length :
    [0, 1, 2, 3, 4, 5].map (hazardAt fixtureConfig) = [70, 10, 55, 70, 10, 55] := by
  native_decide

/-! ## One complete watch, replayed and proved

`applyAction` admits exactly `.idle --claimOfficer--> .claimed --chooseTask--> .assigned
--resolve--> .awaitingDebrief --debrief--> .idle`.  The next four theorems replay that
cycle on the fixture and pin every intermediate phase and the terminal state. -/

theorem one_complete_watch_claims_the_authored_engineer_seat :
    (runFrom (watchOne.take 1)).map State.phase = .ok (.claimed engineerSeat) := by
  native_decide

theorem one_complete_watch_assigns_the_authored_coolant_rule :
    (runFrom (watchOne.take 2)).map State.phase
      = .ok (.assigned engineerSeat coolantBalanceRule) := by
  native_decide

theorem one_complete_watch_resolves_to_the_exact_resolved_shift :
    (runFrom (watchOne.take 3)).map State.phase = .ok (.awaitingDebrief resolvedOne) := by
  native_decide

/-- The keystone.  Four commands, replayed through `judge`, reach EXACTLY this state —
exact by `state_view_is_injective`, which proves a `StateView` determines its `State`. -/
theorem one_complete_watch_reaches_the_exact_expected_state :
    (runFrom watchOne).map view = .ok viewAfterWatchOne := by
  native_decide

theorem the_full_campaign_reaches_the_exact_expected_state :
    (runFrom campaign).map view = .ok viewAfterCampaign := by
  native_decide

/-- Seventeen prefixes, four strict cycles: the phase never skips a step and always
returns to `.idle`. -/
theorem the_campaign_is_four_strict_four_command_cycles :
    (List.range 17).map
        (fun n => (runFrom (campaign.take n)).map (fun s => phaseStage s.phase))
      = [.ok 0, .ok 1, .ok 2, .ok 3,
         .ok 0, .ok 1, .ok 2, .ok 3,
         .ok 0, .ok 1, .ok 2, .ok 3,
         .ok 0, .ok 1, .ok 2, .ok 3, .ok 0] := by
  native_decide

theorem the_campaign_consumes_sixteen_distinct_nullifiers :
    (campaign.map Command.nullifier).toFinset.card = 16 := by
  native_decide

/-! ## What the watches actually DID

The theorems above pin the state.  These pin the *semantics* of the four entries the
state now carries: resources moved by exactly the rule's `WorldEffects`, evidence is the
running sum of the authored per-watch evidence, and each entry took the arm its own
hazard roll selected. -/

theorem every_logged_watch_moved_resources_by_exactly_its_authored_effects :
    campaignHistory.all
        (fun e => decide (e.worldEffects.apply? e.resourcesBefore = some e.resourcesAfter))
      = true := by
  decide

theorem the_success_watches_took_the_success_arms_and_the_failure_watch_the_failure_arm :
    entryOne.contribution = coolantBalanceRule.successContribution ∧
    entryOne.worldEffects = coolantBalanceRule.successEffects ∧
    entryOne.terminalContentId = coolantBalanceRule.successContentId ∧
    entryTwo.contribution = inspectSealRule.failureContribution ∧
    entryTwo.worldEffects = inspectSealRule.failureEffects ∧
    entryTwo.terminalContentId = inspectSealRule.failureContentId ∧
    entryThree.worldEffects = recoveryRoundRule.successEffects ∧
    entryFour.worldEffects = rationAuditRule.successEffects :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem evidence_accumulates_exactly_the_authored_per_watch_evidence :
    entryOne.evidenceBefore = 0 ∧
    entryOne.evidenceAfter = entryOne.evidenceBefore + coolantBalanceRule.successEvidence ∧
    entryTwo.evidenceBefore = entryOne.evidenceAfter ∧
    entryTwo.evidenceAfter = entryTwo.evidenceBefore + inspectSealRule.failureEvidence ∧
    entryThree.evidenceBefore = entryTwo.evidenceAfter ∧
    entryThree.evidenceAfter =
      entryThree.evidenceBefore + recoveryRoundRule.successEvidence ∧
    entryFour.evidenceBefore = entryThree.evidenceAfter ∧
    entryFour.evidenceAfter = entryFour.evidenceBefore + rationAuditRule.successEvidence ∧
    entryFour.evidenceAfter = 16 := by
  decide

/-- A failure is a game outcome, not a refusal: watch two moved resources, wounded its
officer, earned evidence and mastery, appended an entry, and advanced the shift. -/
theorem a_meaningful_failure_still_advances_the_watch :
    entryTwo.success = false ∧
    entryTwo.progression.meaningfulFailure = 1 ∧
    entryTwo.resourcesAfter ≠ entryTwo.resourcesBefore ∧
    entryTwo.healthAfter.wounds = 2 ∧
    entryTwo.evidenceAfter = entryTwo.evidenceBefore + 2 ∧
    entryTwo.masteryAfter.xp = 3 ∧
    entryThree.shift = entryTwo.shift + 1 := by
  decide

theorem a_failed_watch_proposes_no_canon_even_though_its_rule_authors_a_discovery :
    inspectSealRule.betaDiscovery = some ⟨9003⟩ ∧
    inspectSealRule.discoveryEvidenceRequired = 0 ∧
    entryTwo.success = false ∧
    entryTwo.betaProposal = none := by
  decide

theorem the_discovery_gate_withholds_canon_below_the_authored_evidence_bar :
    recoveryRoundRule.betaDiscovery = some ⟨9002⟩ ∧
    recoveryRoundRule.discoveryEvidenceRequired = 100 ∧
    entryThree.success = true ∧
    entryThree.evidenceAfter = 12 ∧
    entryThree.betaProposal = none := by
  decide

theorem the_only_beta_proposal_names_the_authored_artifact_and_the_evidence_that_earned_it :
    campaignHistory.filterMap LogbookEntry.betaProposal
      = [⟨0, digest 11, ⟨9001⟩, 7, digest 60⟩] := by
  native_decide

theorem the_recovery_watch_healed_the_wounds_the_failure_inflicted :
    entryThree.healthBefore = entryTwo.healthAfter ∧
    entryThree.healthAfter.wounds = 0 ∧
    entryThree.healthAfter.strain = 0 ∧
    entryThree.healthBefore.inRecovery = true ∧
    entryThree.healthAfter.inRecovery = false ∧
    entryThree.progression.recoveryObserved = 1 := by
  decide

theorem mastery_is_keyed_by_seat_and_station_not_by_seat_alone :
    viewAfterCampaign.mastery.filter (fun row => decide (row.seat = ⟨2⟩))
      = [⟨⟨2⟩, .containment, 3, 0⟩, ⟨⟨2⟩, .infirmary, 9, 0⟩] := by
  decide

theorem mastery_levels_up_at_the_authored_level_size :
    (masteryFor viewAfterCampaign.mastery ⟨3⟩ .galley).xp = 13 ∧
    (masteryFor viewAfterCampaign.mastery ⟨3⟩ .galley).level = 1 ∧
    entryFour.masteryAfter.xp =
      entryFour.masteryBefore.xp + entryFour.contribution.score + 1 ∧
    entryFour.masteryAfter.level = entryFour.masteryAfter.xp / MASTERY_LEVEL_SIZE := by
  decide

theorem only_the_galley_watch_carries_a_local_service_figure :
    campaignHistory.map LogbookEntry.galleyLocalService = [none, none, none, some 40] ∧
    rationAuditRule.localService = 40 := by
  decide

theorem every_intent_carries_its_entry_and_the_next_stream_sequence :
    campaignIntents.map EventIntent.expectedSequence = [1, 2, 3, 4] ∧
    campaignIntents.map EventIntent.entry = campaignHistory ∧
    campaignIntents.all (fun intent => decide (intent.stream = fixtureLogStream)) = true := by
  native_decide

/-- The module's `event_intent_has_no_finality`, exercised on four real intents. -/
theorem no_campaign_intent_can_fabricate_finality :
    campaignIntents.all (fun intent => (fabricateFinality intent).isNone) = true := by
  decide

/-! ## Refusals, each isolated to the check its name says

Every theorem below asserts the exact `Error` constructor AND exhibits the minimal
neighbouring command that IS accepted, so the refusal cannot be attributed to some
earlier check that happened to fire first. -/

/-- Five out-of-order commands, one per wrong `(action, phase)` pair the kernel can be
offered early.  The same actions in the authored order are accepted — that is
`one_complete_watch_reaches_the_exact_expected_state`. -/
theorem out_of_order_commands_refuse_wrongPhase :
    runFrom [cmd 0 .resolve] = .error .wrongPhase ∧
    runFrom [cmd 0 .debrief] = .error .wrongPhase ∧
    runFrom [cmd 0 (.chooseTask .engineSpine .coolantBalance)] = .error .wrongPhase ∧
    runFrom (watchOne.take 1 ++ [cmd 1 (.claimOfficer (digest 11) ⟨1⟩)])
      = .error .wrongPhase ∧
    runFrom (watchOne.take 2 ++ [cmd 2 .debrief]) = .error .wrongPhase := by
  native_decide

/-- The two commands differ in the nullifier and NOTHING else — same sequence, same
action, same prior state — so the refusal is the nullifier check and not another. -/
theorem a_replayed_nullifier_refuses_while_a_fresh_one_at_the_same_sequence_is_accepted :
    runFrom
        [ cmd 0 (.claimOfficer (digest 11) ⟨1⟩)
        , { sequence := 1, nullifier := digest 200
          , action := .chooseTask .engineSpine .coolantBalance } ]
      = .error .replayedAction ∧
    (runFrom
        [ cmd 0 (.claimOfficer (digest 11) ⟨1⟩)
        , { sequence := 1, nullifier := digest 240
          , action := .chooseTask .engineSpine .coolantBalance } ]).toOption.isSome
      = true := by
  native_decide

/-- Same nullifier, same action; only the sequence number moves. -/
theorem a_wrong_sequence_refuses_while_the_expected_sequence_is_accepted :
    runFrom [{ sequence := 1, nullifier := digest 241
             , action := .claimOfficer (digest 11) ⟨1⟩ }]
      = .error .wrongSequence ∧
    (runFrom [{ sequence := 0, nullifier := digest 241
              , action := .claimOfficer (digest 11) ⟨1⟩ }]).toOption.isSome = true := by
  native_decide

/-- The actor and the seat are each individually legitimate — `digest 12` holds seat
`⟨2⟩` and seat `⟨1⟩` is held by `digest 11` — and both of those claims are accepted.
Only the *pairing* refuses, so this is the actor↔seat binding and not seat lookup. -/
theorem claiming_a_seat_you_do_not_hold_refuses_officerActorMismatch :
    runFrom [{ sequence := 0, nullifier := digest 242
             , action := .claimOfficer (digest 12) ⟨1⟩ }]
      = .error .officerActorMismatch ∧
    (runFrom [{ sequence := 0, nullifier := digest 242
              , action := .claimOfficer (digest 12) ⟨2⟩ }]).toOption.isSome = true ∧
    (runFrom [{ sequence := 0, nullifier := digest 242
              , action := .claimOfficer (digest 11) ⟨1⟩ }]).toOption.isSome = true := by
  native_decide

/-- The distinguishing companion to the previous theorem: an absent seat refuses at the
roster lookup, BEFORE the actor comparison, and reports a different error. -/
theorem an_unseated_seat_id_refuses_unknownOfficer_not_officerActorMismatch :
    runFrom [{ sequence := 0, nullifier := digest 243
             , action := .claimOfficer (digest 11) ⟨7⟩ }]
      = .error .unknownOfficer ∧
    findSeat? fixtureRoster ⟨7⟩ = none ∧
    (findSeat? fixtureRoster ⟨1⟩).isSome = true := by
  native_decide

/-- The engineer cannot take the quartermaster's galley task.  The rule IS found — third
conjunct — so this is the role check, not `unknownTask`; and the quartermaster taking the
identical task is accepted. -/
theorem a_role_mismatched_task_refuses_roleMismatch_while_its_authored_role_is_accepted :
    runFrom (watchOne.take 1 ++
        [{ sequence := 1, nullifier := digest 244
         , action := .chooseTask .galley .rationAudit }])
      = .error .roleMismatch ∧
    (runFrom
        [ cmd 0 (.claimOfficer (digest 13) ⟨3⟩)
        , { sequence := 1, nullifier := digest 244
          , action := .chooseTask .galley .rationAudit } ]).toOption.isSome = true ∧
    (findRule? fixtureRawConfig.rules .galley .rationAudit).isSome = true := by
  native_decide

/-- `(.bridge, .plotDrift)` is unauthored, so lookup fails before the role check. -/
theorem an_unauthored_task_refuses_unknownTask_not_roleMismatch :
    runFrom (watchOne.take 1 ++
        [{ sequence := 1, nullifier := digest 245
         , action := .chooseTask .bridge .plotDrift }])
      = .error .unknownTask ∧
    findRule? fixtureRawConfig.rules .bridge .plotDrift = none := by
  native_decide

/-- The identical claim was accepted as `campaign`'s thirteenth command at shift 3; at
shift 4 it hits the authored ceiling. -/
theorem the_campaign_refuses_a_fifth_watch_at_the_authored_shift_ceiling :
    runFrom (campaign ++
        [{ sequence := 16, nullifier := digest 246
         , action := .claimOfficer (digest 11) ⟨1⟩ }])
      = .error .shiftLimit ∧
    fixtureRawConfig.maxShifts = 4 ∧
    viewAfterCampaign.shift = 4 := by
  native_decide

/-- The claim and the task assignment are both accepted; only `resolve` refuses, because
the authored success arm spends 999999 propellant against a hold of 120. -/
theorem an_unaffordable_spend_refuses_insufficientResources_only_at_resolve :
    (runFrom
        [ cmd 0 (.claimOfficer (digest 10) ⟨0⟩)
        , cmd 1 (.chooseTask .signalGallery .traceSignal) ]).toOption.isSome = true ∧
    runFrom
        [ cmd 0 (.claimOfficer (digest 10) ⟨0⟩)
        , cmd 1 (.chooseTask .signalGallery .traceSignal)
        , cmd 2 .resolve ]
      = .error .insufficientResources ∧
    unaffordableSurveyRule.successEffects.spendPropellant = 999999 ∧
    fixtureRawConfig.initialResources.propellant = 120 := by
  native_decide

/-- A claimed semantic outcome is refused; the same command carrying only UI holder
metadata is accepted, on the real fixture. -/
theorem a_caller_authored_outcome_is_refused_while_holder_metadata_is_erased :
    judgeSubmitted fixtureConfig (initialState fixtureConfig)
        { command := cmd 0 (.claimOfficer (digest 11) ⟨1⟩)
        , claimedContribution := some ⟨9, 9, 9, 9, 9⟩ }
      = .error .callerAuthoredOutcome ∧
    (judgeSubmitted fixtureConfig (initialState fixtureConfig)
        { command := cmd 0 (.claimOfficer (digest 11) ⟨1⟩)
        , holder := some { eligible := true, affordance := none } }).toOption.isSome
      = true := by
  native_decide

/-! ## One arm of `resolveAssigned` cannot fire

`resolveAssigned` (`NightWatchCampaign.lean:489-492`) obtains `resourcesAfter` from
`WorldEffects.apply?` and then re-checks `if !resourcesAfter.boundedB then throw
.resourceBound`.  `apply?` already returns `none` on an unbounded result — and `none`
is mapped to `.insufficientResources` one line earlier — so the theorem below shows
`.resourceBound` is unreachable from that call site.  This is not fixture-specific: it
holds for every `WorldEffects` and every `ShipResources`. -/

theorem worldEffects_apply_returns_only_bounded_resources
    {effect : WorldEffects} {before after : ShipResources}
    (h : effect.apply? before = some after) : after.boundedB = true := by
  simp only [WorldEffects.apply?, bind, Option.bind] at h
  split_ifs at h with h1 h2 h3 h4 h5
  simp_all

/-! ## Pins

`#assert_axioms` where the kernel checked it; `#assert_compiled` where only the compiled
evaluator reached.  Everything mentioning `fixtureConfig` is necessarily compiled-pinned:
`fixtureConfig` is defined through `fixture_activate_isSome`, which rests on
`fixture_config_valid`'s `native_decide` oracle, and `collectAxioms` walks that closure.
The kernel-pinned group is exactly the facts stated over the raw authored literals — and
`#assert_compiled` REFUSES a kernel-clean declaration, so the split below is checked, not
asserted. -/

#assert_compiled fixture_config_valid
#assert_compiled fixture_log_stream_is_a_valid_event_stream
#assert_compiled fixture_activate_isSome
#assert_compiled fixture_config_activates
#assert_compiled fixture_config_raw
#assert_axioms campaign_config_constructor_is_private
#assert_axioms campaign_state_constructor_is_private
#assert_axioms state_view_is_injective
#assert_compiled initial_state_is_the_authored_initial_condition
#assert_compiled hazard_cycle_is_deterministic_and_wraps_at_the_cycle_length
#assert_compiled one_complete_watch_claims_the_authored_engineer_seat
#assert_compiled one_complete_watch_assigns_the_authored_coolant_rule
#assert_compiled one_complete_watch_resolves_to_the_exact_resolved_shift
#assert_compiled one_complete_watch_reaches_the_exact_expected_state
#assert_compiled the_full_campaign_reaches_the_exact_expected_state
#assert_compiled the_campaign_is_four_strict_four_command_cycles
#assert_compiled the_campaign_consumes_sixteen_distinct_nullifiers
#assert_axioms every_logged_watch_moved_resources_by_exactly_its_authored_effects
#assert_axioms the_success_watches_took_the_success_arms_and_the_failure_watch_the_failure_arm
#assert_axioms evidence_accumulates_exactly_the_authored_per_watch_evidence
#assert_axioms a_meaningful_failure_still_advances_the_watch
#assert_axioms a_failed_watch_proposes_no_canon_even_though_its_rule_authors_a_discovery
#assert_axioms the_discovery_gate_withholds_canon_below_the_authored_evidence_bar
#assert_compiled the_only_beta_proposal_names_the_authored_artifact_and_the_evidence_that_earned_it
#assert_axioms the_recovery_watch_healed_the_wounds_the_failure_inflicted
#assert_axioms mastery_is_keyed_by_seat_and_station_not_by_seat_alone
#assert_axioms mastery_levels_up_at_the_authored_level_size
#assert_axioms only_the_galley_watch_carries_a_local_service_figure
#assert_compiled every_intent_carries_its_entry_and_the_next_stream_sequence
#assert_axioms no_campaign_intent_can_fabricate_finality
#assert_compiled out_of_order_commands_refuse_wrongPhase
#assert_compiled a_replayed_nullifier_refuses_while_a_fresh_one_at_the_same_sequence_is_accepted
#assert_compiled a_wrong_sequence_refuses_while_the_expected_sequence_is_accepted
#assert_compiled claiming_a_seat_you_do_not_hold_refuses_officerActorMismatch
#assert_compiled an_unseated_seat_id_refuses_unknownOfficer_not_officerActorMismatch
#assert_compiled a_role_mismatched_task_refuses_roleMismatch_while_its_authored_role_is_accepted
#assert_compiled an_unauthored_task_refuses_unknownTask_not_roleMismatch
#assert_compiled the_campaign_refuses_a_fifth_watch_at_the_authored_shift_ceiling
#assert_compiled an_unaffordable_spend_refuses_insufficientResources_only_at_resolve
#assert_compiled a_caller_authored_outcome_is_refused_while_holder_metadata_is_erased
#assert_axioms worldEffects_apply_returns_only_bounded_resources

end Dregg2.Games.PathOfAngels.NightWatchCampaignExamples
