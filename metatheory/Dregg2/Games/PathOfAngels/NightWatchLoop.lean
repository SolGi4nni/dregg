/-
# NightWatchLoop — replay semantics for the first private-beta watch

This module is the mechanical layer for the private `afterwatch-night-watch-beta-one`
content pack.  It contains no prose and no operation that can promote beta material
into alpha canon.  Stable finite identifiers name every player choice, maintenance
action, semantic event, debrief, artifact, and recovery transition.

The important split is command versus event.  A caller submits a small command;
`execute` derives the only admissible ordered events and replays them through the
same reducer used for recovery.  Event payloads redundantly carry exact effects so
replay can refuse a substituted success, relic, recipient, serving disposition, or
debrief.  Nothing consults host time: commons scarcity is an ordered finalized-day
ledger, and recovery requires a strictly later finalized day.

This is beta gameplay only.  The three portable relic candidates remain quarantined
and non-market.  The environmental witness thread is evidence, never custody.
Holder status and token balance do not occur in the state or transition vocabulary.

## ⚑ STATUS 2026-08-05 — this is NOT the shipped night watch, and it is unreachable

There are two Path-of-Angels state machines with "Night Watch" in the name.  They
share **no type, no relation and no theorem** — only the name.

* **`NightWatchCampaign`** is the one that SHIPS: officers, stations, authored
  tasks, hazard, resources, evidence, wounds, mastery.  It has a canonical JSON
  boundary (`NightWatchCampaignWire`), an `@[export]`, and a proved four-command
  watch (`NightWatchCampaignExamples`).
* **This module** is a different game for the same fiction: rotations, a commons
  serving economy, encounters, routes, extraction terminals, debriefs, recovery.

**Nothing here can be reached from outside this file.**  `Policy` is `private mk ::`
and requires a `ContentMembershipAdmission`, which is also `private mk ::` and whose
only construction site in the entire repository is `fixturePolicy` below.  So
`initialState` — the sole public producer of a `State` — has no callable argument,
and every theorem in `NightWatchLoopWire` about `preparePublic` quantifies over a
type no importer can instantiate.  `NightWatchLoopExamples` says so in its own
docblock.  The sealing is deliberate; the consequence that no player can reach any
of this is the unpaid bill.

**But the content is NOT dead, and that is measured, not assumed.**  The analyses
below enumerate 741 reachable states in 13 layers, proved *closed* under one
`execute` step of the whole `choose`/`extract` alphabet — not depth-capped.  All 21
authored choices are live and all 11 terminals reachable.  What is inert is three
of the four budgets.

So the disposition is a real decision, not a cleanup: either this gets an
authenticated admission producer (the `ActivatedContent.authorizeEmbeddedGalleyPolicyForWorld?`
shape, which is what makes Galley's policy reachable) or it is deleted.  It should
not simply sit here unreachable — a second kernel nobody can enter is exactly the
shape that cost the Galley 5,111 lines.  Whichever way it goes, this docblock is
the record that it was chosen and not forgotten.
-/
import Dregg2.Games.PathOfAngels.Core
import Dregg2.Games.PathOfAngels.CrewRelayExpedition
import Dregg2.Games.PathOfAngels.EventBatch
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.NightWatchLoop

open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.CrewRelayExpedition

set_option autoImplicit false

abbrev TURN_BUDGET : Nat := 18
abbrev OPERATIONAL_BUDGET : Nat := 20
abbrev SUPPLY_SPEND_LIMIT : Nat := 8
abbrev CLUE_INTEL_LIMIT : Nat := 12
abbrev MAX_COMMONS_VISITS : Nat := 128
abbrev DEBRIEF_SCHEMA_VERSION : Nat := 1

/-! ## Stable content identities -/

inductive RotationId where
  | pressureWeather | quietShift | returnAlarm | filterRain
  | witnessShift | maintenanceHeat | firstReturn | ordinarySound
deriving Repr, DecidableEq

def RotationId.code : RotationId → Nat
  | .pressureWeather => 0 | .quietShift => 1 | .returnAlarm => 2 | .filterRain => 3
  | .witnessShift => 4 | .maintenanceHeat => 5 | .firstReturn => 6 | .ordinarySound => 7

def rotationForDay (dayIndex : Nat) : RotationId :=
  match dayIndex % 8 with
  | 0 => .pressureWeather | 1 => .quietShift | 2 => .returnAlarm | 3 => .filterRain
  | 4 => .witnessShift | 5 => .maintenanceHeat | 6 => .firstReturn | _ => .ordinarySound

inductive ServingTag where | steady | alert | recovery | expedition
deriving Repr, DecidableEq

/-- All thirty-two authored commons choices.  These constructor names are the
stable semantic ids corresponding to the private pack's kebab-case ids. -/
inductive ServingChoiceId where
  | steadyBowl | watchCup | softReturn | liftPacket
  | quietBroth | saltFold | sharedHeel | sealedFlask
  | amberMash | lampTea | watchCrust | returnSling
  | filterCake | brightPickle | drySleeve | sealedCrumb
  | witnessStew | intervalCoffee | recoveryPair | chalkPacket
  | coolGrain | trenchSalt | wrappedFruit | heatShieldTin
  | homePot | awakeSlice | blueTray | secondWindowKit
  | ordinaryBowl | scratchTonic | offWatchPudding | plainReturnKit
deriving Repr, DecidableEq

def ServingChoiceId.code : ServingChoiceId → Nat
  | .steadyBowl => 0 | .watchCup => 1 | .softReturn => 2 | .liftPacket => 3
  | .quietBroth => 4 | .saltFold => 5 | .sharedHeel => 6 | .sealedFlask => 7
  | .amberMash => 8 | .lampTea => 9 | .watchCrust => 10 | .returnSling => 11
  | .filterCake => 12 | .brightPickle => 13 | .drySleeve => 14 | .sealedCrumb => 15
  | .witnessStew => 16 | .intervalCoffee => 17 | .recoveryPair => 18 | .chalkPacket => 19
  | .coolGrain => 20 | .trenchSalt => 21 | .wrappedFruit => 22 | .heatShieldTin => 23
  | .homePot => 24 | .awakeSlice => 25 | .blueTray => 26 | .secondWindowKit => 27
  | .ordinaryBowl => 28 | .scratchTonic => 29 | .offWatchPudding => 30 | .plainReturnKit => 31

def ServingChoiceId.rotation : ServingChoiceId → RotationId
  | .steadyBowl | .watchCup | .softReturn | .liftPacket => .pressureWeather
  | .quietBroth | .saltFold | .sharedHeel | .sealedFlask => .quietShift
  | .amberMash | .lampTea | .watchCrust | .returnSling => .returnAlarm
  | .filterCake | .brightPickle | .drySleeve | .sealedCrumb => .filterRain
  | .witnessStew | .intervalCoffee | .recoveryPair | .chalkPacket => .witnessShift
  | .coolGrain | .trenchSalt | .wrappedFruit | .heatShieldTin => .maintenanceHeat
  | .homePot | .awakeSlice | .blueTray | .secondWindowKit => .firstReturn
  | .ordinaryBowl | .scratchTonic | .offWatchPudding | .plainReturnKit => .ordinarySound

def ServingChoiceId.capacity : ServingChoiceId → Nat
  | .steadyBowl => 24 | .watchCup => 12 | .softReturn => 8 | .liftPacket => 6
  | .quietBroth => 18 | .saltFold => 10 | .sharedHeel => 32 | .sealedFlask => 5
  | .amberMash => 20 | .lampTea => 16 | .watchCrust => 28 | .returnSling => 8
  | .filterCake => 22 | .brightPickle => 14 | .drySleeve => 10 | .sealedCrumb => 7
  | .witnessStew => 26 | .intervalCoffee => 12 | .recoveryPair => 10 | .chalkPacket => 9
  | .coolGrain => 24 | .trenchSalt => 18 | .wrappedFruit => 11 | .heatShieldTin => 6
  | .homePot => 30 | .awakeSlice => 15 | .blueTray => 12 | .secondWindowKit => 4
  | .ordinaryBowl => 36 | .scratchTonic => 13 | .offWatchPudding => 18 | .plainReturnKit => 8

def ServingChoiceId.localService : ServingChoiceId → Nat
  | .steadyBowl => 8 | .watchCup => 5 | .softReturn => 12 | .liftPacket => 3
  | .quietBroth => 7 | .saltFold => 6 | .sharedHeel => 4 | .sealedFlask => 2
  | .amberMash => 9 | .lampTea => 5 | .watchCrust => 6 | .returnSling => 3
  | .filterCake => 7 | .brightPickle => 4 | .drySleeve => 8 | .sealedCrumb => 2
  | .witnessStew => 8 | .intervalCoffee => 6 | .recoveryPair => 10 | .chalkPacket => 3
  | .coolGrain => 7 | .trenchSalt => 5 | .wrappedFruit => 9 | .heatShieldTin => 3
  | .homePot => 9 | .awakeSlice => 5 | .blueTray => 12 | .secondWindowKit => 2
  | .ordinaryBowl => 8 | .scratchTonic => 4 | .offWatchPudding => 10 | .plainReturnKit => 3

def ServingChoiceId.tag : ServingChoiceId → ServingTag
  | .steadyBowl | .quietBroth | .watchCrust | .filterCake | .witnessStew
  | .coolGrain | .homePot | .ordinaryBowl => .steady
  | .watchCup | .saltFold | .lampTea | .brightPickle | .intervalCoffee
  | .trenchSalt | .awakeSlice | .scratchTonic => .alert
  | .softReturn | .sharedHeel | .amberMash | .drySleeve | .recoveryPair
  | .wrappedFruit | .blueTray | .offWatchPudding => .recovery
  | .liftPacket | .sealedFlask | .returnSling | .sealedCrumb | .chalkPacket
  | .heatShieldTin | .secondWindowKit | .plainReturnKit => .expedition

inductive MaintenanceActionId where
  | readTwinGauges | isolateFeederThree | routeReturnBypass | ventMemoryPocket
  | calibrateReturnFloat | reseedCultureCup | verifyFirstCycle
deriving Repr, DecidableEq

def maintenanceProcedure : List MaintenanceActionId :=
  [.readTwinGauges, .isolateFeederThree, .routeReturnBypass, .ventMemoryPocket,
   .calibrateReturnFloat, .reseedCultureCup, .verifyFirstCycle]

def MaintenanceActionId.code : MaintenanceActionId → Nat
  | .readTwinGauges => 0 | .isolateFeederThree => 1 | .routeReturnBypass => 2
  | .ventMemoryPocket => 3 | .calibrateReturnFloat => 4 | .reseedCultureCup => 5
  | .verifyFirstCycle => 6

inductive Route where | maintenanceSpine | signalGallery | sealedNave
deriving Repr, DecidableEq

def Route.code : Route → Nat
  | .maintenanceSpine => 0 | .signalGallery => 1 | .sealedNave => 2

inductive EncounterId where
  | countingClearances | anticipatingTruss | pressureIntervals | senderlessSequence
  | heatlessShoal | seamWhenUnseen | inverseToolCradle | uncommandedReturn
deriving Repr, DecidableEq

def EncounterId.code : EncounterId → Nat
  | .countingClearances => 0 | .anticipatingTruss => 1 | .pressureIntervals => 2
  | .senderlessSequence => 3 | .heatlessShoal => 4 | .seamWhenUnseen => 5
  | .inverseToolCradle => 6 | .uncommandedReturn => 7

def routeEncounters : Route → List EncounterId
  | .maintenanceSpine =>
      [.countingClearances, .anticipatingTruss, .pressureIntervals, .uncommandedReturn]
  | .signalGallery =>
      [.countingClearances, .senderlessSequence, .heatlessShoal, .uncommandedReturn]
  | .sealedNave =>
      [.countingClearances, .seamWhenUnseen, .inverseToolCradle,
       .heatlessShoal, .uncommandedReturn]

/-- Choices are semantic ids, not labels.  Several are intentionally prudent
exits or mistakes; the reducer does not silently turn them into the best path. -/
inductive ChoiceId where
  | markMovingClearance | observeSecondMovement | ignoreMovingClearance
  | braceObservedRhythm | overdriveTruss | withdrawAtTruss
  | replaySharedIntervals | commitPrivateIntervals | misventRelief
  | triangulateFullSequence | preserveRawTrace | moveBeforeRepeat
  | screenCorridor | waitMovementCycle | abandonShoal
  | performTwoRoleHandoff | recordClosedThreshold | withdrawFromThreshold
  | exchangeCalibrationBlock | photographCradle | leaveCavityUntouched
deriving Repr, DecidableEq

def ChoiceId.code : ChoiceId → Nat
  | .markMovingClearance => 100 | .observeSecondMovement => 101 | .ignoreMovingClearance => 102
  | .braceObservedRhythm => 110 | .overdriveTruss => 111 | .withdrawAtTruss => 112
  | .replaySharedIntervals => 120 | .commitPrivateIntervals => 121 | .misventRelief => 122
  | .triangulateFullSequence => 130 | .preserveRawTrace => 131 | .moveBeforeRepeat => 132
  | .screenCorridor => 140 | .waitMovementCycle => 141 | .abandonShoal => 142
  | .performTwoRoleHandoff => 150 | .recordClosedThreshold => 151
  | .withdrawFromThreshold => 152 | .exchangeCalibrationBlock => 160
  | .photographCradle => 161 | .leaveCavityUntouched => 162

def ChoiceId.encounter : ChoiceId → EncounterId
  | .markMovingClearance | .observeSecondMovement | .ignoreMovingClearance => .countingClearances
  | .braceObservedRhythm | .overdriveTruss | .withdrawAtTruss => .anticipatingTruss
  | .replaySharedIntervals | .commitPrivateIntervals | .misventRelief => .pressureIntervals
  | .triangulateFullSequence | .preserveRawTrace | .moveBeforeRepeat => .senderlessSequence
  | .screenCorridor | .waitMovementCycle | .abandonShoal => .heatlessShoal
  | .performTwoRoleHandoff | .recordClosedThreshold | .withdrawFromThreshold => .seamWhenUnseen
  | .exchangeCalibrationBlock | .photographCradle | .leaveCavityUntouched => .inverseToolCradle

inductive ExtractionChoice where | returnNow | descendFurther
deriving Repr, DecidableEq

/-! The private pack authors exactly six route/extraction rows.  Choice-caused
failures remain mechanically real, but live in the explicitly unactivated draft
namespace below instead of being laundered into the authored table. -/
inductive AuthoredOutcomeId where
  | maintenanceReturn | maintenanceDeep
  | signalReturn | signalDeep
  | sealedReturn | sealedDeep
deriving Repr, DecidableEq

def AuthoredOutcomeId.code : AuthoredOutcomeId → Nat
  | .maintenanceReturn => 0 | .maintenanceDeep => 1
  | .signalReturn => 2 | .signalDeep => 3
  | .sealedReturn => 4 | .sealedDeep => 5

def AuthoredOutcomeId.operationalCost : AuthoredOutcomeId → Nat
  | .maintenanceReturn => 2 | .maintenanceDeep => 5
  | .signalReturn => 3 | .signalDeep => 7
  | .sealedReturn => 11 | .sealedDeep => 12

inductive MechanicalDraftOutcomeId where
  | maintenanceReturnInjured | maintenanceWithdrawn
  | signalReturnPartial | signalCorridorLost | sealedReturnClosed
deriving Repr, DecidableEq

def MechanicalDraftOutcomeId.code : MechanicalDraftOutcomeId → Nat
  | .maintenanceReturnInjured => 0 | .maintenanceWithdrawn => 1
  | .signalReturnPartial => 2 | .signalCorridorLost => 3 | .sealedReturnClosed => 4

inductive TerminalId where
  | authored (outcome : AuthoredOutcomeId)
  | mechanicalDraft (outcome : MechanicalDraftOutcomeId)
deriving Repr, DecidableEq

def TerminalId.code : TerminalId → Nat
  | .authored outcome => outcome.code
  | .mechanicalDraft outcome => 100 + outcome.code

structure DebriefId where
  schemaVersion : Nat
  terminal : TerminalId
deriving Repr, DecidableEq

def debriefFor (terminal : TerminalId) : DebriefId :=
  ⟨DEBRIEF_SCHEMA_VERSION, terminal⟩

inductive EventId where
  | servingAllocated | maintenancePerformed | briefingDelivered | handoffRecorded
  | routeCommitted | choiceResolved | extractionResolved | injuryRecorded
  | recoveryServingRecorded | recoveryCalibrationCompleted | nextWatchEnrolled
  | draftSettlementActivated | debriefIssued
deriving Repr, DecidableEq

def EventId.code : EventId → Nat
  | .servingAllocated => 1 | .maintenancePerformed => 2 | .briefingDelivered => 3
  | .handoffRecorded => 4 | .routeCommitted => 5 | .choiceResolved => 6
  | .extractionResolved => 7 | .injuryRecorded => 8 | .recoveryServingRecorded => 9
  | .recoveryCalibrationCompleted => 10 | .debriefIssued => 11
  | .nextWatchEnrolled => 12
  | .draftSettlementActivated => 13

/-! ## Exact beta evidence and non-market recovery objects -/

def artifactClearanceMotion : ArtifactId := ⟨1⟩
def artifactMaintenanceLoadTrace : ArtifactId := ⟨2⟩
def artifactPressureIntervalRecord : ArtifactId := ⟨3⟩
def artifactGallerySequence : ArtifactId := ⟨4⟩
def artifactShoalMotion : ArtifactId := ⟨5⟩
def artifactThresholdHandoff : ArtifactId := ⟨6⟩
def artifactCradleExchange : ArtifactId := ⟨7⟩
def artifactReturnWindow : ArtifactId := ⟨8⟩

def allowedArtifacts : Finset ArtifactId :=
  { artifactClearanceMotion, artifactMaintenanceLoadTrace, artifactPressureIntervalRecord,
    artifactGallerySequence, artifactShoalMotion, artifactThresholdHandoff,
    artifactCradleExchange, artifactReturnWindow }

def relicSilentBearing : RelicId := ⟨1⟩
def relicIndexFilm : RelicId := ⟨2⟩
def relicThresholdWedge : RelicId := ⟨3⟩
def relicWitnessThread : RelicId := ⟨4⟩

/-- Only portable, quarantined candidates may enter contribution custody.  The
witness thread is deliberately absent because it remains part of the lift. -/
def allowedCarriedRelics : Finset RelicId :=
  { relicSilentBearing, relicIndexFilm, relicThresholdWedge }

inductive RecoveryGrade where
  | clean | injured | marked | lostOpportunity | containmentDebt | failedReturn
deriving Repr, DecidableEq

inductive InjuryId where | engineerCompression
deriving Repr, DecidableEq

/-! ## Activated identity, content authority, and role-recipient binding -/

structure FinalizedDayId where
  contentEpoch : EpochId
  dayIndex : Nat
deriving Repr, DecidableEq

structure OfficerSeat where
  role : CrewRole
  recipient : Digest32
deriving DecidableEq

/-- Exact activated content scope.  Both digests are full-width semantic fields;
neither is reconstructed from a caller's command. -/
structure ContentScope where
  component : Digest32
  packDigest : Digest32
deriving DecidableEq

/-- Opaque evidence that the future host authenticated membership of this exact
component/pack in this exact five-field world.  There is deliberately no public
producer in this module. -/
structure ContentMembershipAdmission where
  private mk ::
  world : EventBatch.WorldIdentity
  scope : ContentScope
deriving DecidableEq

def exactRoles : List CrewRole :=
  [.pathfinder, .engineer, .containment, .quartermaster]

def seatForRole? : List OfficerSeat → CrewRole → Option OfficerSeat
  | [], _ => none
  | seat :: seats, role => if seat.role = role then some seat else seatForRole? seats role

structure RawPolicy where
  world : EventBatch.WorldIdentity
  content : ContentScope
  missionId : MissionId
  sessionId : Digest32
  missionDay : FinalizedDayId
  watchOfficer : Digest32
  roster : List OfficerSeat
deriving DecidableEq

def rawPolicyValidB (raw : RawPolicy) : Bool :=
  raw.world.validB &&
  decide (raw.missionDay.contentEpoch = raw.world.contentEpoch) &&
  decide (raw.roster.map OfficerSeat.role = exactRoles) &&
  decide (raw.roster.map OfficerSeat.recipient).Nodup &&
  decide (raw.watchOfficer ∈ raw.roster.map OfficerSeat.recipient)

structure Policy where
  private mk ::
  raw : RawPolicy
  membership : ContentMembershipAdmission
  valid : rawPolicyValidB raw = true
  membership_world_exact : membership.world = raw.world
  membership_content_exact : membership.scope = raw.content
deriving DecidableEq

structure DraftActivationBody where
  world : EventBatch.WorldIdentity
  content : ContentScope
  missionId : MissionId
  sessionId : Digest32
  outcome : MechanicalDraftOutcomeId
  predecessorSequence : Nat
deriving DecidableEq

structure SignedDraftActivationCarrier where
  body : DraftActivationBody
  signature : Digest32
deriving DecidableEq

/-- Opaque evidence that the future content-authority host activated one exact
mechanical draft terminal for world settlement.  There is no public producer.
The separate carrier lets the reducer recheck every signed field and reject a
mutation without pretending this module verifies deployment signatures. -/
structure DraftActivationAdmission where
  private mk ::
  authenticatedCarrier : SignedDraftActivationCarrier
deriving DecidableEq

/-! ## Commons receipts use finalized-day order, never host time -/

structure ServingVisitKey where
  day : FinalizedDayId
  visitor : Digest32
deriving DecidableEq

structure ServingCount where
  day : FinalizedDayId
  choice : ServingChoiceId
  served : Nat
deriving DecidableEq

def servingCountFor : List ServingCount → FinalizedDayId → ServingChoiceId → Nat
  | [], _, _ => 0
  | row :: rows, day, choice =>
      if row.day = day ∧ row.choice = choice then row.served
      else servingCountFor rows day choice

def setServingCount : List ServingCount → ServingCount → List ServingCount
  | [], replacement => [replacement]
  | row :: rows, replacement =>
      if row.day = replacement.day ∧ row.choice = replacement.choice then replacement :: rows
      else row :: setServingCount rows replacement

inductive ServingDisposition where | featured | neighborlyAlternative
deriving Repr, DecidableEq

/-- `allocationOrdinal` is the exact count observed before this allocation.
Alternative service preserves the saturated count rather than inventing stock. -/
structure ServingReceipt where
  day : FinalizedDayId
  visitor : Digest32
  rotation : RotationId
  choice : ServingChoiceId
  allocationOrdinal : Nat
  disposition : ServingDisposition
  nextFeaturedCount : Nat
  localService : Nat
deriving DecidableEq

/-! ## Choice effects and exact terminal tables -/

structure ChoiceDelta where
  turnCost : Nat
  operationalCost : Nat
  supplyCost : Nat
  clueIntel : Nat
  artifacts : Finset ArtifactId
  causesInjury : Bool
deriving DecidableEq

def ChoiceId.delta : ChoiceId → ChoiceDelta
  | .markMovingClearance => ⟨1, 0, 0, 0, {artifactClearanceMotion}, false⟩
  | .observeSecondMovement => ⟨2, 1, 0, 1, {artifactClearanceMotion}, false⟩
  | .ignoreMovingClearance => ⟨1, 0, 0, 0, ∅, false⟩
  | .braceObservedRhythm => ⟨1, 1, 0, 0, {artifactMaintenanceLoadTrace}, false⟩
  | .overdriveTruss => ⟨2, 2, 2, 0, {artifactMaintenanceLoadTrace}, true⟩
  | .withdrawAtTruss => ⟨1, 0, 0, 0, ∅, false⟩
  | .replaySharedIntervals => ⟨1, 1, 0, 1, {artifactPressureIntervalRecord}, false⟩
  | .commitPrivateIntervals => ⟨2, 1, 0, 2, {artifactPressureIntervalRecord}, false⟩
  | .misventRelief => ⟨1, 1, 1, 0, ∅, false⟩
  | .triangulateFullSequence => ⟨3, 3, 0, 3, {artifactGallerySequence}, false⟩
  | .preserveRawTrace => ⟨1, 1, 0, 1, {artifactGallerySequence}, false⟩
  | .moveBeforeRepeat => ⟨1, 0, 0, 0, ∅, false⟩
  | .screenCorridor => ⟨1, 1, 0, 0, {artifactShoalMotion}, false⟩
  | .waitMovementCycle => ⟨2, 1, 0, 1, {artifactShoalMotion}, false⟩
  | .abandonShoal => ⟨1, 0, 0, 0, ∅, false⟩
  | .performTwoRoleHandoff => ⟨2, 1, 0, 1, {artifactThresholdHandoff}, false⟩
  | .recordClosedThreshold => ⟨1, 0, 0, 1, ∅, false⟩
  | .withdrawFromThreshold => ⟨1, 0, 0, 0, ∅, false⟩
  | .exchangeCalibrationBlock => ⟨3, 3, 0, 1, {artifactCradleExchange}, false⟩
  | .photographCradle => ⟨1, 1, 0, 1, ∅, false⟩
  | .leaveCavityUntouched => ⟨1, 0, 0, 0, ∅, false⟩

def terminalRawContribution : TerminalId → RawContribution
  | .authored .maintenanceReturn => ⟨2, 4, 4, 0, 18, []⟩
  | .authored .maintenanceDeep => ⟨3, 2, 3, 0, 48, [relicSilentBearing]⟩
  | .authored .signalReturn => ⟨6, 2, 3, 0, 25, []⟩
  | .authored .signalDeep => ⟨8, 0, 2, 0, 62, [relicIndexFilm]⟩
  | .authored .sealedReturn => ⟨4, 1, 6, 0, 31, []⟩
  | .authored .sealedDeep => ⟨5, 0, 5, 0, 79, [relicThresholdWedge]⟩
  | .mechanicalDraft .maintenanceReturnInjured => ⟨1, 2, 3, 0, 10, []⟩
  | .mechanicalDraft .maintenanceWithdrawn => ⟨0, 0, 2, 0, 4, []⟩
  | .mechanicalDraft .signalReturnPartial => ⟨3, 2, 2, 0, 12, []⟩
  | .mechanicalDraft .signalCorridorLost => ⟨2, 1, 2, 0, 8, []⟩
  | .mechanicalDraft .sealedReturnClosed => ⟨1, 2, 3, 0, 9, []⟩

def TerminalId.grade : TerminalId → RecoveryGrade
  | .authored .maintenanceReturn | .authored .signalReturn => .clean
  | .authored .maintenanceDeep | .mechanicalDraft .maintenanceReturnInjured => .injured
  | .authored .signalDeep => .marked
  | .authored .sealedReturn => .lostOpportunity
  | .authored .sealedDeep => .containmentDebt
  | .mechanicalDraft _ => .failedReturn

def TerminalId.featuredArtifact : TerminalId → ArtifactId
  | .authored .maintenanceReturn | .mechanicalDraft .maintenanceReturnInjured =>
      artifactMaintenanceLoadTrace
  | .mechanicalDraft .maintenanceWithdrawn => artifactClearanceMotion
  | .authored .maintenanceDeep => artifactPressureIntervalRecord
  | .authored .signalReturn | .mechanicalDraft .signalReturnPartial => artifactGallerySequence
  | .authored .signalDeep | .mechanicalDraft .signalCorridorLost => artifactShoalMotion
  | .authored .sealedReturn => artifactThresholdHandoff
  | .mechanicalDraft .sealedReturnClosed => artifactClearanceMotion
  | .authored .sealedDeep => artifactCradleExchange

/-- Only the six activated pack rows carry a pack-authored extraction cost. -/
def TerminalId.authoredOperationalCost? : TerminalId → Option Nat
  | .authored outcome => some outcome.operationalCost
  | .mechanicalDraft _ => none

def nightWatchContributionBudget : ContributionBudget where
  intel := 12
  supplies := 8
  cohesion := 8
  influence := 0
  score := 100
  relics := 3

structure OutcomeReceipt where
  private mk ::
  terminal : TerminalId
  contribution : Contribution
  featuredArtifact : ArtifactId
  recoveryGrade : RecoveryGrade
  carriedRelics : Finset RelicId
  debrief : DebriefId
  terminalOperationalCost : Nat
  terminal_cost_exact : terminalOperationalCost = terminal.authoredOperationalCost?.getD 0
  within_budget : contribution.within nightWatchContributionBudget = true
  relics_allowlisted : carriedRelics ⊆ allowedCarriedRelics
  artifact_allowlisted : featuredArtifact ∈ allowedArtifacts
deriving DecidableEq

def outcomeReceipt? (terminal : TerminalId) : Option OutcomeReceipt := do
  let contribution ← validateContribution (terminalRawContribution terminal)
  if hb : contribution.within nightWatchContributionBudget = true then
    if h : contribution.relics ⊆ allowedCarriedRelics then
      have ha : terminal.featuredArtifact ∈ allowedArtifacts := by
        cases terminal <;> rename_i outcome <;> cases outcome <;> decide
      some {
        terminal
        contribution
        featuredArtifact := terminal.featuredArtifact
        recoveryGrade := terminal.grade
        carriedRelics := contribution.relics
        debrief := debriefFor terminal
        terminalOperationalCost := terminal.authoredOperationalCost?.getD 0
        terminal_cost_exact := rfl
        within_budget := hb
        relics_allowlisted := h
        artifact_allowlisted := ha
      }
    else none
  else none

/-! ## Handoffs, recovery, and replay state -/

structure BriefingReceipt where
  role : CrewRole
  recipient : Digest32
  briefingId : Nat
deriving DecidableEq

def briefingIdFor : CrewRole → Nat
  | .pathfinder => 1 | .engineer => 2 | .containment => 3 | .quartermaster => 4

inductive Phase where
  | galley | maintenance | briefings | routeSelection | encounters
  | extraction | returned | debriefed
deriving Repr, DecidableEq

structure HandoffSummary where
  role : CrewRole
  signer : Digest32
  recipient : Digest32
  briefingId : Nat
  recommendedRoute : Route
  deepConsent : Bool
deriving DecidableEq

/-- Exact pre-state named by a role handoff.  This is a semantic root object,
not a lossy digest standing in for equality. -/
structure HandoffPredecessor where
  missionId : MissionId
  sessionId : Digest32
  sequence : Nat
  phase : Phase
  briefings : List BriefingReceipt
  handoffs : List HandoffSummary
  counters : List Nat
deriving DecidableEq

structure HandoffBody where
  world : EventBatch.WorldIdentity
  content : ContentScope
  missionId : MissionId
  sessionId : Digest32
  role : CrewRole
  signer : Digest32
  recipient : Digest32
  previousCounter : Nat
  counter : Nat
  predecessor : HandoffPredecessor
  recommendedRoute : Route
  deepConsent : Bool
deriving DecidableEq

structure HandoffSignature where
  value : Digest32
deriving DecidableEq

structure SignedHandoffCarrier where
  body : HandoffBody
  signature : HandoffSignature
deriving DecidableEq

/-- Opaque future-host admission for one already authenticated signed handoff.
This module has deliberately no public producer.  Its private fixtures exercise
binding checks; they are not a signature implementation or public authority. -/
structure HandoffAdmission where
  private mk ::
  authenticatedCarrier : SignedHandoffCarrier
deriving DecidableEq

structure HandoffReceipt where
  role : CrewRole
  signer : Digest32
  recipient : Digest32
  briefingId : Nat
  previousCounter : Nat
  counter : Nat
  recommendedRoute : Route
  deepConsent : Bool
  signature : HandoffSignature
deriving DecidableEq

def HandoffReceipt.summary (receipt : HandoffReceipt) : HandoffSummary where
  role := receipt.role
  signer := receipt.signer
  recipient := receipt.recipient
  briefingId := receipt.briefingId
  recommendedRoute := receipt.recommendedRoute
  deepConsent := receipt.deepConsent

def handoffForRole? : List HandoffReceipt → CrewRole → Option HandoffReceipt
  | [], _ => none
  | handoff :: handoffs, role =>
      if handoff.role = role then some handoff else handoffForRole? handoffs role

def specialistSupport (handoffs : List HandoffReceipt) (route : Route) : Nat :=
  handoffs.countP fun handoff =>
    handoff.role != .quartermaster && handoff.recommendedRoute = route

def unanimousDeepB (handoffs : List HandoffReceipt) (route : Route) : Bool :=
  decide (handoffs.length = 4) && handoffs.all fun handoff =>
    handoff.deepConsent && decide (handoff.recommendedRoute = route)

inductive RecoveryState where
  | fit
  | treatmentNeeded (officer : Digest32) (injury : InjuryId) (source : TerminalId)
  | calibrationNeeded (officer : Digest32) (injury : InjuryId)
      (source : TerminalId) (serving : ServingReceipt)
  | recovered (officer : Digest32) (injury : InjuryId) (source : TerminalId)
deriving DecidableEq

def RecoveryState.hasActiveInjury : RecoveryState → Bool
  | .treatmentNeeded .. | .calibrationNeeded .. => true
  | .fit | .recovered .. => false

structure EncounterFlags where
  entryMarked : Bool := false
  navigationDebt : Bool := false
  pressureOpen : Bool := false
  sequenceComplete : Bool := false
  corridorOpen : Bool := false
  thresholdOpen : Bool := false
  cradleExchanged : Bool := false
deriving DecidableEq

structure NextWatchBody where
  world : EventBatch.WorldIdentity
  content : ContentScope
  missionId : MissionId
  sessionId : Digest32
  watchDay : FinalizedDayId
  role : CrewRole
  recipient : Digest32
  predecessorSequence : Nat
deriving DecidableEq

/-- Opaque future-host admission for one exact next-watch enrollment.  The
semantic reducer still rechecks scope, day, sequence, role recipient, and the
active recovery lock.  There is no public producer here. -/
structure NextWatchAdmission where
  private mk ::
  body : NextWatchBody
deriving DecidableEq

structure NextWatchReceipt where
  watchDay : FinalizedDayId
  role : CrewRole
  recipient : Digest32
  admittedAtSequence : Nat
deriving DecidableEq

structure State where
  private mk ::
  policy : Policy
  sequence : Nat
  phase : Phase
  visitKeys : Finset ServingVisitKey
  servingCounts : List ServingCount
  servings : List ServingReceipt
  initialServing : Option ServingReceipt
  maintenanceProgress : Nat
  maintenanceActors : Finset Digest32
  maintenanceContribution : Option Contribution
  briefings : List BriefingReceipt
  handoffs : List HandoffReceipt
  handoffCounters : List Nat
  route : Option Route
  encounterIndex : Nat
  turnsSpent : Nat
  operationalSpent : Nat
  suppliesSpent : Nat
  clueIntel : Nat
  evidence : Finset ArtifactId
  flags : EncounterFlags
  pendingInjury : Option (Digest32 × InjuryId × TerminalId)
  pendingTerminal : Option TerminalId
  pendingRecoveryServing : Option (InjuryId × TerminalId × ServingReceipt)
  outcome : Option OutcomeReceipt
  recovery : RecoveryState
  nextWatchEnrollments : List NextWatchReceipt
  debrief : Option DebriefId
deriving DecidableEq

def initialState (policy : Policy) : State where
  policy
  sequence := 0
  phase := .galley
  visitKeys := ∅
  servingCounts := []
  servings := []
  initialServing := none
  maintenanceProgress := 0
  maintenanceActors := ∅
  maintenanceContribution := none
  briefings := []
  handoffs := []
  handoffCounters := [0, 0, 0, 0]
  route := none
  encounterIndex := 0
  turnsSpent := 0
  operationalSpent := 0
  suppliesSpent := 0
  clueIntel := 0
  evidence := ∅
  flags := {}
  pendingInjury := none
  pendingTerminal := none
  pendingRecoveryServing := none
  outcome := none
  recovery := .fit
  nextWatchEnrollments := []
  debrief := none

def rosterContains (policy : Policy) (actor : Digest32) : Bool :=
  decide (actor ∈ policy.raw.roster.map OfficerSeat.recipient)

def roleIndex : CrewRole → Nat
  | .pathfinder => 0 | .engineer => 1 | .containment => 2 | .quartermaster => 3

def counterForRole (state : State) (role : CrewRole) : Nat :=
  state.handoffCounters.getD (roleIndex role) 0

def setRoleCounter (counters : List Nat) (role : CrewRole) (counter : Nat) : List Nat :=
  counters.set (roleIndex role) counter

def handoffPredecessor (state : State) : HandoffPredecessor where
  missionId := state.policy.raw.missionId
  sessionId := state.policy.raw.sessionId
  sequence := state.sequence
  phase := state.phase
  briefings := state.briefings
  handoffs := state.handoffs.map HandoffReceipt.summary
  counters := state.handoffCounters

def expectedEncounter? (state : State) : Option EncounterId := do
  let route ← state.route
  (routeEncounters route)[state.encounterIndex]?

def canSpendB (state : State) (delta : ChoiceDelta) : Bool :=
  decide (state.turnsSpent + delta.turnCost ≤ TURN_BUDGET) &&
  decide (state.operationalSpent + delta.operationalCost ≤ OPERATIONAL_BUDGET) &&
  decide (state.suppliesSpent + delta.supplyCost ≤ SUPPLY_SPEND_LIMIT) &&
  decide (state.clueIntel + delta.clueIntel ≤ CLUE_INTEL_LIMIT) &&
  decide (state.evidence ∪ delta.artifacts ⊆ allowedArtifacts)

def choicePreconditionB (state : State) (choice : ChoiceId) : Bool :=
  state.phase = .encounters && expectedEncounter? state = some choice.encounter &&
  canSpendB state choice.delta &&
  match choice with
  | .braceObservedRhythm =>
      (handoffForRole? state.handoffs .engineer).any fun h =>
        decide (h.recommendedRoute = .maintenanceSpine)
  | .commitPrivateIntervals =>
      (handoffForRole? state.handoffs .pathfinder).any fun h =>
        decide (h.recommendedRoute = .maintenanceSpine)
  | .screenCorridor =>
      (handoffForRole? state.handoffs .containment).any fun h =>
        state.route.any fun route => decide (h.recommendedRoute = route)
  | .performTwoRoleHandoff =>
      specialistSupport state.handoffs .sealedNave ≥ 2
  | .exchangeCalibrationBlock => unanimousDeepB state.handoffs .sealedNave
  | _ => true

structure ChoiceReceipt where
  private mk ::
  encounter : EncounterId
  choice : ChoiceId
  delta : ChoiceDelta
  nextEncounterIndex : Nat
  delta_exact : delta = choice.delta
deriving DecidableEq

structure InjuryReceipt where
  officer : Digest32
  role : CrewRole
  injury : InjuryId
  source : TerminalId
deriving DecidableEq

structure RecoveryServingReceipt where
  injury : InjuryId
  source : TerminalId
  serving : ServingReceipt
deriving DecidableEq

structure RecoveryCalibrationReceipt where
  officer : Digest32
  injury : InjuryId
  source : TerminalId
deriving DecidableEq

inductive Event where
  | servingAllocated (receipt : ServingReceipt)
  | maintenancePerformed (actor : Digest32) (index : Nat) (action : MaintenanceActionId)
  | briefingDelivered (receipt : BriefingReceipt)
  | handoffRecorded (carrier : SignedHandoffCarrier) (admission : HandoffAdmission)
  | routeCommitted (route : Route)
  | choiceResolved (receipt : ChoiceReceipt)
  | extractionResolved (receipt : OutcomeReceipt)
  | injuryRecorded (receipt : InjuryReceipt)
  | recoveryServingRecorded (receipt : RecoveryServingReceipt)
  | recoveryCalibrationCompleted (receipt : RecoveryCalibrationReceipt)
  | nextWatchEnrolled (admission : NextWatchAdmission)
  | draftSettlementActivated (receipt : OutcomeReceipt)
      (carrier : SignedDraftActivationCarrier) (admission : DraftActivationAdmission)
  | debriefIssued (debrief : DebriefId)
deriving DecidableEq

def Event.id : Event → EventId
  | .servingAllocated _ => .servingAllocated
  | .maintenancePerformed .. => .maintenancePerformed
  | .briefingDelivered _ => .briefingDelivered
  | .handoffRecorded _ _ => .handoffRecorded
  | .routeCommitted _ => .routeCommitted
  | .choiceResolved _ => .choiceResolved
  | .extractionResolved _ => .extractionResolved
  | .injuryRecorded _ => .injuryRecorded
  | .recoveryServingRecorded _ => .recoveryServingRecorded
  | .recoveryCalibrationCompleted _ => .recoveryCalibrationCompleted
  | .nextWatchEnrolled _ => .nextWatchEnrolled
  | .draftSettlementActivated .. => .draftSettlementActivated
  | .debriefIssued _ => .debriefIssued

structure EventEnvelope where
  sequence : Nat
  payload : Event
deriving DecidableEq

/-! ## Canonical event reducer -/

def expectedServingReceipt? (state : State) (day : FinalizedDayId)
    (visitor : Digest32) (choice : ServingChoiceId) : Option ServingReceipt := do
  if day.contentEpoch != state.policy.raw.missionDay.contentEpoch then none
  if rotationForDay day.dayIndex != choice.rotation then none
  let key : ServingVisitKey := ⟨day, visitor⟩
  if key ∈ state.visitKeys then none
  let dayVisits := state.visitKeys.filter fun key => key.day = day
  if MAX_COMMONS_VISITS ≤ dayVisits.card then none
  let served := servingCountFor state.servingCounts day choice
  let hasCapacity := served < choice.capacity
  some {
    day
    visitor
    rotation := choice.rotation
    choice
    allocationOrdinal := served
    disposition := if hasCapacity then .featured else .neighborlyAlternative
    nextFeaturedCount := if hasCapacity then served + 1 else served
    localService := if hasCapacity then choice.localService else 0
  }

private def applyServing (state : State) (receipt : ServingReceipt) : Option State := do
  let expected ← expectedServingReceipt? state receipt.day receipt.visitor receipt.choice
  if receipt != expected then none
  let galleyVisit := state.phase = .galley && receipt.day = state.policy.raw.missionDay
  let initial := galleyVisit &&
    receipt.visitor = state.policy.raw.watchOfficer
  let recoveryVisit := state.phase = .debriefed &&
    match state.recovery with
    | .treatmentNeeded officer _ _ =>
        receipt.visitor = officer && state.policy.raw.missionDay.dayIndex < receipt.day.dayIndex
    | _ => false
  if !galleyVisit && !recoveryVisit then none
  if recoveryVisit && receipt.choice.tag != .recovery then none
  let pendingRecoveryServing ←
    if recoveryVisit then
      match state.recovery with
      | .treatmentNeeded _ injury source => some (some (injury, source, receipt))
      | _ => none
    else some state.pendingRecoveryServing
  let key : ServingVisitKey := ⟨receipt.day, receipt.visitor⟩
  let counts :=
    if receipt.disposition = .featured then
      setServingCount state.servingCounts ⟨receipt.day, receipt.choice, receipt.nextFeaturedCount⟩
    else state.servingCounts
  some { state with
    visitKeys := insert key state.visitKeys
    servingCounts := counts
    servings := state.servings ++ [receipt]
    pendingRecoveryServing
    initialServing := if initial then some receipt else state.initialServing
    phase := if initial then .maintenance else state.phase }

def maintenanceContribution? : Option Contribution :=
  validateContribution ⟨0, 2, 2, 0, 14, []⟩

def maintenanceContribution : Contribution :=
  { intel := ⟨0, by decide⟩
    supplies := ⟨2, by decide⟩
    cohesion := ⟨2, by decide⟩
    influence := ⟨0, by decide⟩
    score := ⟨14, by decide⟩
    relics := ∅
    relics_bounded := by simp }

theorem maintenanceContribution_validates_exactly :
    maintenanceContribution? = some maintenanceContribution := by native_decide

private def applyMaintenance (state : State) (actor : Digest32) (index : Nat)
    (action : MaintenanceActionId) : Option State := do
  if state.phase != .maintenance then none
  if !rosterContains state.policy actor then none
  if index != state.maintenanceProgress then none
  let expected ← maintenanceProcedure[index]?
  if action != expected then none
  let progress := index + 1
  if progress = maintenanceProcedure.length then
    let contribution ← maintenanceContribution?
    some { state with
      maintenanceProgress := progress
      maintenanceActors := insert actor state.maintenanceActors
      maintenanceContribution := some contribution
      phase := .briefings }
  else
    some { state with
      maintenanceProgress := progress
      maintenanceActors := insert actor state.maintenanceActors }

private def applyBriefing (state : State) (receipt : BriefingReceipt) : Option State := do
  if state.phase != .briefings then none
  let seat ← seatForRole? state.policy.raw.roster receipt.role
  if receipt.recipient != seat.recipient then none
  if receipt.briefingId != briefingIdFor receipt.role then none
  if state.briefings.any (fun prior => prior.role = receipt.role) then none
  some { state with briefings := state.briefings ++ [receipt] }

private def applyHandoff (state : State) (carrier : SignedHandoffCarrier)
    (admission : HandoffAdmission) : Option State := do
  if state.phase != .briefings then none
  if carrier != admission.authenticatedCarrier then none
  let body := carrier.body
  if body.world != state.policy.raw.world then none
  if body.content != state.policy.raw.content then none
  if body.missionId != state.policy.raw.missionId then none
  if body.sessionId != state.policy.raw.sessionId then none
  let seat ← seatForRole? state.policy.raw.roster body.role
  if body.signer != seat.recipient || body.recipient != seat.recipient then none
  if body.previousCounter != counterForRole state body.role then none
  if body.counter != body.previousCounter + 1 then none
  if body.predecessor != handoffPredecessor state then none
  let briefingId := briefingIdFor body.role
  if !state.briefings.any (fun briefing => briefing.role = body.role &&
      briefing.recipient = body.recipient && briefing.briefingId = briefingId) then none
  if state.handoffs.any (fun prior => prior.role = body.role) then none
  let receipt : HandoffReceipt := {
    role := body.role
    signer := body.signer
    recipient := body.recipient
    briefingId
    previousCounter := body.previousCounter
    counter := body.counter
    recommendedRoute := body.recommendedRoute
    deepConsent := body.deepConsent
    signature := carrier.signature
  }
  let handoffs := state.handoffs ++ [receipt]
  some { state with
    handoffs
    handoffCounters := setRoleCounter state.handoffCounters body.role body.counter
    phase := if handoffs.length = 4 then .routeSelection else .briefings }

private def applyRoute (state : State) (route : Route) : Option State :=
  if state.phase != .routeSelection then none
  else if specialistSupport state.handoffs route < 2 then none
  else some { state with phase := .encounters, route := some route, encounterIndex := 0 }

private def earlyOutcomeForChoice (state : State) : ChoiceId → Option TerminalId
  | .withdrawAtTruss => some (.mechanicalDraft .maintenanceWithdrawn)
  | .abandonShoal =>
      match state.route with
      | some .signalGallery => some (.mechanicalDraft .signalCorridorLost)
      | some .sealedNave => some (.mechanicalDraft .sealedReturnClosed)
      | _ => none
  | .withdrawFromThreshold | .recordClosedThreshold =>
      some (.mechanicalDraft .sealedReturnClosed)
  | _ => none

private def updateFlags (flags : EncounterFlags) (choice : ChoiceId) : EncounterFlags :=
  match choice with
  | .markMovingClearance | .observeSecondMovement => { flags with entryMarked := true }
  | .ignoreMovingClearance => { flags with navigationDebt := true }
  | .replaySharedIntervals | .commitPrivateIntervals => { flags with pressureOpen := true }
  | .triangulateFullSequence => { flags with sequenceComplete := true }
  | .screenCorridor | .waitMovementCycle => { flags with corridorOpen := true }
  | .performTwoRoleHandoff => { flags with thresholdOpen := true }
  | .exchangeCalibrationBlock => { flags with cradleExchanged := true }
  | _ => flags

private def applyChoice (state : State) (receipt : ChoiceReceipt) : Option State := do
  if !choicePreconditionB state receipt.choice then none
  let encounter ← expectedEncounter? state
  if receipt.encounter != encounter then none
  if receipt.delta != receipt.choice.delta then none
  let advance := receipt.choice != .misventRelief
  let expectedIndex := if advance then state.encounterIndex + 1 else state.encounterIndex
  if receipt.nextEncounterIndex != expectedIndex then none
  let pendingInjury ←
    if receipt.delta.causesInjury then
      match seatForRole? state.policy.raw.roster .engineer with
      | none => none
      | some engineer => some (some (engineer.recipient, .engineerCompression,
          .mechanicalDraft .maintenanceReturnInjured))
    else some state.pendingInjury
  let early := earlyOutcomeForChoice state receipt.choice
  some { state with
    encounterIndex := expectedIndex
    turnsSpent := state.turnsSpent + receipt.delta.turnCost
    operationalSpent := state.operationalSpent + receipt.delta.operationalCost
    suppliesSpent := state.suppliesSpent + receipt.delta.supplyCost
    clueIntel := state.clueIntel + receipt.delta.clueIntel
    evidence := state.evidence ∪ receipt.delta.artifacts
    flags := updateFlags state.flags receipt.choice
    pendingInjury
    pendingTerminal := early
    phase := if early.isSome then .extraction else
      if expectedEncounter? { state with encounterIndex := expectedIndex } =
          some .uncommandedReturn then .extraction else .encounters }

private def expectedTerminalId? (state : State) (choice : ExtractionChoice) : Option TerminalId := do
  if state.phase != .extraction then none
  let route ← state.route
  let early : Option TerminalId :=
    if state.flags.navigationDebt then
      match route with
      | .maintenanceSpine => some (.mechanicalDraft .maintenanceWithdrawn)
      | .signalGallery => some (.mechanicalDraft .signalCorridorLost)
      | .sealedNave => some (.mechanicalDraft .sealedReturnClosed)
    else if route = .maintenanceSpine && state.encounterIndex < 3 then
      some (.mechanicalDraft .maintenanceWithdrawn)
    else if route = .signalGallery && !state.flags.corridorOpen then
      some (.mechanicalDraft .signalCorridorLost)
    else if route = .sealedNave && !state.flags.thresholdOpen then
      some (.mechanicalDraft .sealedReturnClosed)
    else none
  match early with
  | some outcome => some outcome
  | none =>
      match route, choice with
      | .maintenanceSpine, .returnNow =>
          if state.pendingInjury.isSome || state.recovery.hasActiveInjury then
            some (.mechanicalDraft .maintenanceReturnInjured)
          else if artifactMaintenanceLoadTrace ∈ state.evidence then
            some (.authored .maintenanceReturn) else none
      | .maintenanceSpine, .descendFurther =>
          if unanimousDeepB state.handoffs route && state.flags.pressureOpen then
              if 3 ≤ state.clueIntel && artifactPressureIntervalRecord ∈ state.evidence then
                some (.authored .maintenanceDeep) else none
          else none
      | .signalGallery, .returnNow =>
          if state.flags.sequenceComplete && artifactGallerySequence ∈ state.evidence then
            some (.authored .signalReturn)
          else some (.mechanicalDraft .signalReturnPartial)
      | .signalGallery, .descendFurther =>
          if unanimousDeepB state.handoffs route && state.flags.sequenceComplete &&
              state.flags.corridorOpen && 4 ≤ state.clueIntel &&
              artifactGallerySequence ∈ state.evidence && artifactShoalMotion ∈ state.evidence then
            some (.authored .signalDeep) else none
      | .sealedNave, .returnNow =>
          if state.flags.thresholdOpen && 2 ≤ state.clueIntel &&
              artifactThresholdHandoff ∈ state.evidence then
            some (.authored .sealedReturn)
          else some (.mechanicalDraft .sealedReturnClosed)
      | .sealedNave, .descendFurther =>
          if unanimousDeepB state.handoffs route && state.flags.thresholdOpen &&
              state.flags.cradleExchanged && state.flags.corridorOpen && 2 ≤ state.clueIntel &&
              artifactThresholdHandoff ∈ state.evidence && artifactCradleExchange ∈ state.evidence then
            some (.authored .sealedDeep) else none

def expectedOutcomeReceipt? (state : State) (choice : ExtractionChoice) : Option OutcomeReceipt := do
  let terminal ← expectedTerminalId? state choice
  outcomeReceipt? terminal

private def applyExtraction (state : State) (receipt : OutcomeReceipt) : Option State := do
  let expectedReturn ← expectedOutcomeReceipt? state .returnNow
  let expectedDeep := expectedOutcomeReceipt? state .descendFurther
  if receipt != expectedReturn && some receipt != expectedDeep then none
  if !receipt.carriedRelics ⊆ allowedCarriedRelics then none
  if receipt.featuredArtifact ∉ allowedArtifacts then none
  let extractionCost := receipt.terminalOperationalCost
  if OPERATIONAL_BUDGET < state.operationalSpent + extractionCost then none
  let pendingInjury ←
    if receipt.terminal = .authored .maintenanceDeep && state.pendingInjury.isNone &&
        !state.recovery.hasActiveInjury then
      match seatForRole? state.policy.raw.roster .engineer with
      | none => none
      | some engineer => some (some (engineer.recipient, .engineerCompression, receipt.terminal))
    else some (state.pendingInjury.map fun (officer, injury, _) =>
      (officer, injury, receipt.terminal))
  let recovery :=
    match state.recovery with
    | .treatmentNeeded officer injury _ =>
        .treatmentNeeded officer injury receipt.terminal
    | other => other
  some { state with
    phase := .returned
    operationalSpent := state.operationalSpent + extractionCost
    evidence := insert receipt.featuredArtifact state.evidence
    outcome := some receipt
    recovery
    pendingInjury
    pendingTerminal := none }

private def applyInjury (state : State) (receipt : InjuryReceipt) : Option State := do
  let pending ← state.pendingInjury
  if pending != (receipt.officer, receipt.injury, receipt.source) then none
  if receipt.role != .engineer then none
  some { state with
    pendingInjury := none
    recovery := .treatmentNeeded receipt.officer receipt.injury receipt.source }

private def applyRecoveryServing (state : State)
    (receipt : RecoveryServingReceipt) : Option State := do
  let pending ← state.pendingRecoveryServing
  if pending != (receipt.injury, receipt.source, receipt.serving) then none
  let latest ← state.servings.getLast?
  if receipt.serving != latest then none
  if receipt.serving.choice.tag != .recovery then none
  match state.recovery with
  | .treatmentNeeded officer injury source =>
      if receipt.injury != injury || receipt.source != source ||
          receipt.serving.visitor != officer then none
      else some { state with
        pendingRecoveryServing := none
        recovery := RecoveryState.calibrationNeeded officer injury source receipt.serving }
  | _ => none

private def applyRecoveryCalibration (state : State)
    (receipt : RecoveryCalibrationReceipt) : Option State :=
  match state.recovery with
  | .calibrationNeeded officer injury source _ =>
      if receipt.officer != officer || receipt.injury != injury || receipt.source != source then none
      else some { state with recovery := .recovered officer injury source }
  | _ => none

private def applyNextWatchEnrollment (state : State)
    (admission : NextWatchAdmission) : Option State := do
  if state.phase != .debriefed then none
  if state.pendingInjury.isSome || state.pendingTerminal.isSome ||
      state.pendingRecoveryServing.isSome then none
  let body := admission.body
  if body.world != state.policy.raw.world || body.content != state.policy.raw.content then none
  if body.missionId != state.policy.raw.missionId ||
      body.sessionId != state.policy.raw.sessionId then none
  if body.watchDay.contentEpoch != state.policy.raw.world.contentEpoch then none
  if body.watchDay.dayIndex ≤ state.policy.raw.missionDay.dayIndex then none
  if body.predecessorSequence != state.sequence then none
  let seat ← seatForRole? state.policy.raw.roster body.role
  if body.recipient != seat.recipient then none
  let available := match state.recovery with
    | .treatmentNeeded officer _ _ | .calibrationNeeded officer _ _ _ =>
        !(body.role = .engineer && body.recipient = officer)
    | .fit | .recovered .. => true
  if !available then none
  if state.nextWatchEnrollments.any (fun prior => prior.watchDay = body.watchDay &&
      prior.role = body.role && prior.recipient = body.recipient) then none
  some { state with nextWatchEnrollments := state.nextWatchEnrollments ++ [{
    watchDay := body.watchDay
    role := body.role
    recipient := body.recipient
    admittedAtSequence := state.sequence
  }] }

private def applyDebrief (state : State) (debrief : DebriefId) : Option State := do
  if state.phase != .returned then none
  if state.pendingInjury.isSome || state.pendingTerminal.isSome ||
      state.pendingRecoveryServing.isSome then none
  let outcome ← state.outcome
  match outcome.terminal with
  | .mechanicalDraft _ => none
  | .authored _ => pure ()
  if debrief != outcome.debrief then none
  if debrief.schemaVersion != DEBRIEF_SCHEMA_VERSION then none
  some { state with phase := .debriefed, debrief := some debrief }

private def applyDraftSettlement (state : State) (receipt : OutcomeReceipt)
    (carrier : SignedDraftActivationCarrier)
    (admission : DraftActivationAdmission) : Option State := do
  if state.phase != .returned then none
  if state.pendingInjury.isSome || state.pendingTerminal.isSome ||
      state.pendingRecoveryServing.isSome then none
  if carrier != admission.authenticatedCarrier then none
  let outcome ← state.outcome
  if receipt != outcome then none
  let draft ← match receipt.terminal with
    | .mechanicalDraft draft => some draft
    | .authored _ => none
  if carrier.body.world != state.policy.raw.world ||
      carrier.body.content != state.policy.raw.content then none
  if carrier.body.missionId != state.policy.raw.missionId ||
      carrier.body.sessionId != state.policy.raw.sessionId then none
  if carrier.body.outcome != draft then none
  if carrier.body.predecessorSequence != state.sequence then none
  some { state with phase := .debriefed, debrief := some receipt.debrief }

def consequenceOrderB (state : State) (event : Event) : Bool :=
  match state.pendingInjury, state.pendingTerminal, state.pendingRecoveryServing with
  | some _, _, _ => match event with | .injuryRecorded _ => true | _ => false
  | none, some _, _ => match event with | .extractionResolved _ => true | _ => false
  | none, none, some _ => match event with | .recoveryServingRecorded _ => true | _ => false
  | none, none, none => true

def applyEvent (state : State) (event : EventEnvelope) : Option State := do
  if event.sequence != state.sequence + 1 then none
  if !consequenceOrderB state event.payload then none
  let after ← match event.payload with
    | .servingAllocated receipt => applyServing state receipt
    | .maintenancePerformed actor index action => applyMaintenance state actor index action
    | .briefingDelivered receipt => applyBriefing state receipt
    | .handoffRecorded carrier admission => applyHandoff state carrier admission
    | .routeCommitted route => applyRoute state route
    | .choiceResolved receipt => applyChoice state receipt
    | .extractionResolved receipt => applyExtraction state receipt
    | .injuryRecorded receipt => applyInjury state receipt
    | .recoveryServingRecorded receipt => applyRecoveryServing state receipt
    | .recoveryCalibrationCompleted receipt => applyRecoveryCalibration state receipt
    | .nextWatchEnrolled admission => applyNextWatchEnrollment state admission
    | .draftSettlementActivated receipt carrier admission =>
        applyDraftSettlement state receipt carrier admission
    | .debriefIssued debrief => applyDebrief state debrief
  some { after with sequence := event.sequence }

def replay : State → List EventEnvelope → Option State
  | state, [] => some state
  | state, event :: events => do
      let after ← applyEvent state event
      replay after events

/-! ## Commands derive events; callers do not submit effect-bearing receipts -/

inductive Command where
  | claimServing (day : FinalizedDayId) (visitor : Digest32) (choice : ServingChoiceId)
  | performMaintenance (actor : Digest32) (action : MaintenanceActionId)
  | deliverBriefing (role : CrewRole) (recipient : Digest32)
  | recordHandoff (carrier : SignedHandoffCarrier) (admission : HandoffAdmission)
  | commitRoute (route : Route)
  | choose (choice : ChoiceId)
  | extract (choice : ExtractionChoice)
  | completeRecoveryCalibration (officer : Digest32)
  | enrollNextWatch (admission : NextWatchAdmission)
  | activateDraftSettlement (carrier : SignedDraftActivationCarrier)
      (admission : DraftActivationAdmission)
  | issueDebrief
deriving DecidableEq

private def envelopeFrom (sequence : Nat) (payload : Event) : EventEnvelope :=
  ⟨sequence, payload⟩

private def plannedPayloads? (state : State) : Command → Option (List Event)
  | .claimServing day visitor choice => do
      let serving ← expectedServingReceipt? state day visitor choice
      if state.phase = .galley then
        some [.servingAllocated serving]
      else
        match state.recovery with
        | .treatmentNeeded _ injury source =>
            if choice.tag != .recovery then none
            else some [.servingAllocated serving,
              .recoveryServingRecorded ⟨injury, source, serving⟩]
        | _ => none
  | .performMaintenance actor action =>
      some [.maintenancePerformed actor state.maintenanceProgress action]
  | .deliverBriefing role recipient =>
      some [.briefingDelivered ⟨role, recipient, briefingIdFor role⟩]
  | .recordHandoff carrier admission => some [.handoffRecorded carrier admission]
  | .commitRoute route => some [.routeCommitted route]
  | .choose choice => do
      if !choicePreconditionB state choice then none
      let encounter ← expectedEncounter? state
      let nextIndex := if choice = .misventRelief then state.encounterIndex
        else state.encounterIndex + 1
      let choiceEvent := Event.choiceResolved
        ⟨encounter, choice, choice.delta, nextIndex, rfl⟩
      let injuryEvents ←
        if choice.delta.causesInjury then
          match seatForRole? state.policy.raw.roster .engineer with
          | none => none
          | some engineer => some [Event.injuryRecorded
              ⟨engineer.recipient, .engineer, .engineerCompression,
                .mechanicalDraft .maintenanceReturnInjured⟩]
        else some []
      let earlyEvents ←
        match earlyOutcomeForChoice state choice with
        | none => some []
        | some outcome => do
            let receipt ← outcomeReceipt? outcome
            some [Event.extractionResolved receipt]
      some ([choiceEvent] ++ injuryEvents ++ earlyEvents)
  | .extract choice => do
      let receipt ← expectedOutcomeReceipt? state choice
      let injuryEvents ←
        if receipt.terminal = .authored .maintenanceDeep && state.pendingInjury.isNone &&
            !state.recovery.hasActiveInjury then
          match seatForRole? state.policy.raw.roster .engineer with
          | none => none
          | some engineer => some [Event.injuryRecorded
              ⟨engineer.recipient, .engineer, .engineerCompression, receipt.terminal⟩]
        else some []
      some ([Event.extractionResolved receipt] ++ injuryEvents)
  | .completeRecoveryCalibration officer =>
      match state.recovery with
      | .calibrationNeeded expected injury source _ =>
          if officer != expected then none
          else some [.recoveryCalibrationCompleted ⟨officer, injury, source⟩]
      | _ => none
  | .enrollNextWatch admission => some [.nextWatchEnrolled admission]
  | .activateDraftSettlement carrier admission => do
      let receipt ← state.outcome
      match receipt.terminal with
      | .authored _ => none
      | .mechanicalDraft _ =>
          some [.draftSettlementActivated receipt carrier admission]
  | .issueDebrief => do
      let outcome ← state.outcome
      match outcome.terminal with
      | .authored _ => some [.debriefIssued outcome.debrief]
      | .mechanicalDraft _ => none

def numberEvents : Nat → List Event → List EventEnvelope
  | _, [] => []
  | sequence, event :: events =>
      envelopeFrom (sequence + 1) event :: numberEvents (sequence + 1) events

structure AcceptedTransition (before : State) (command : Command) where
  private mk ::
  events : List EventEnvelope
  after : State
  events_nonempty : events ≠ []
  replay_exact : replay before events = some after

def execute (before : State) (command : Command) : Option (AcceptedTransition before command) :=
  match hpayloads : plannedPayloads? before command with
  | none => none
  | some payloads =>
      if hempty : payloads = [] then none
      else
        let events := numberEvents before.sequence payloads
        match hreplay : replay before events with
        | none => none
        | some after =>
            have hne : events ≠ [] := by
              intro hevents
              cases payloads with
              | nil => exact hempty rfl
              | cons payload rest => simp [events, numberEvents] at hevents
            some ⟨events, after, hne, hreplay⟩

/-- The replay guarantee is carried by `AcceptedTransition`'s FIELD, so every
inhabitant of the type has it whether or not `execute` produced it.  This used to
be stated with a hypothesis `execute before command = some transition` that the
proof ignored, under the name `execute_replays_exactly` — a name claiming
something about `execute` that the term never used.  `execute` is the only
producer of this type in this module; that is the fact doing the work, and it is
structural, not a theorem this statement proves. -/
theorem accepted_transition_carries_its_exact_replay {before : State} {command : Command}
    (transition : AcceptedTransition before command) :
    replay before transition.events = some transition.after :=
  transition.replay_exact

/- `replay_deterministic` used to sit here: "if `replay b e = some l` and
`replay b e = some r` then `l = r`".  That is true of every Lean function applied
twice to the same arguments and says nothing about `replay`, this reducer, or
event sourcing.  DELETED rather than renamed — there is no non-trivial
determinism fact to state, because `replay` is a function. -/

theorem choice_receipt_uses_exact_delta (receipt : ChoiceReceipt) :
    receipt.delta = receipt.choice.delta := receipt.delta_exact

theorem outcome_receipt_relics_are_exactly_allowlisted (receipt : OutcomeReceipt) :
    receipt.carriedRelics ⊆ allowedCarriedRelics := receipt.relics_allowlisted

theorem outcome_receipt_is_within_pack_budget (receipt : OutcomeReceipt) :
    receipt.contribution.within nightWatchContributionBudget = true :=
  receipt.within_budget

theorem outcome_receipt_terminal_cost_is_exact (receipt : OutcomeReceipt) :
    receipt.terminalOperationalCost = receipt.terminal.authoredOperationalCost?.getD 0 :=
  receipt.terminal_cost_exact

theorem debrief_version_is_semantic (terminal : TerminalId) :
    (debriefFor terminal).schemaVersion = DEBRIEF_SCHEMA_VERSION := rfl

theorem witness_thread_is_not_carried : relicWitnessThread ∉ allowedCarriedRelics := by
  decide

/-- The compression consequence has an actual semantic tooth: the exact engineer
recipient cannot take that role again until the two recovery events complete. -/
def roleAvailableB (state : State) (role : CrewRole) (recipient : Digest32) : Bool :=
  match state.recovery with
  | .treatmentNeeded officer _ _ | .calibrationNeeded officer _ _ _ =>
      !(role = .engineer && recipient = officer)
  | .fit | .recovered .. => true

theorem treatment_locks_exact_engineer (state : State) (officer : Digest32)
    (injury : InjuryId) (source : TerminalId)
    (h : state.recovery = .treatmentNeeded officer injury source) :
    roleAvailableB state .engineer officer = false := by
  simp [roleAvailableB, h]

theorem treatment_does_not_lock_other_role (state : State) (officer : Digest32)
    (injury : InjuryId) (source : TerminalId)
    (h : state.recovery = .treatmentNeeded officer injury source) :
    roleAvailableB state .pathfinder officer = true := by
  simp [roleAvailableB, h]

/-! ## Private semantic fixtures

These constructors remain in this module so no imported client receives a
content-membership or handoff-admission producer.  They exercise hostile signed
carrier mutations and full replay paths; they are not production authority. -/

private def fixtureDigest (n : Nat) : Digest32 where
  bytes := List.replicate 32 ⟨n % 256, Nat.mod_lt _ (by omega)⟩
  length_eq := by simp

private def fixtureWorld : EventBatch.WorldIdentity where
  federationId := fixtureDigest 1
  contentRoot := fixtureDigest 2
  activationDigest := fixtureDigest 3
  contentSession := fixtureDigest 4
  contentEpoch := ⟨1⟩

private def fixtureContent : ContentScope := ⟨fixtureDigest 5, fixtureDigest 6⟩
private def fixtureDay : FinalizedDayId := ⟨⟨1⟩, 5⟩
private def fixtureRecoveryDay : FinalizedDayId := ⟨⟨1⟩, 6⟩
private def fixturePathfinder : Digest32 := fixtureDigest 10
private def fixtureEngineer : Digest32 := fixtureDigest 11
private def fixtureContainment : Digest32 := fixtureDigest 12
private def fixtureQuartermaster : Digest32 := fixtureDigest 13

private def fixtureRecipient : CrewRole → Digest32
  | .pathfinder => fixturePathfinder | .engineer => fixtureEngineer
  | .containment => fixtureContainment | .quartermaster => fixtureQuartermaster

private def fixtureRawPolicy : RawPolicy where
  world := fixtureWorld
  content := fixtureContent
  missionId := ⟨7001⟩
  sessionId := fixtureDigest 20
  missionDay := fixtureDay
  watchOfficer := fixturePathfinder
  roster :=
    [ ⟨.pathfinder, fixturePathfinder⟩, ⟨.engineer, fixtureEngineer⟩
    , ⟨.containment, fixtureContainment⟩, ⟨.quartermaster, fixtureQuartermaster⟩ ]

private def fixturePolicy : Policy :=
  let membership : ContentMembershipAdmission := ⟨fixtureWorld, fixtureContent⟩
  ⟨fixtureRawPolicy, membership, by native_decide, rfl, rfl⟩

private def runCommands : State → List Command → Option State
  | state, [] => some state
  | state, command :: commands => do
      let accepted ← execute state command
      runCommands accepted.after commands

private def fixtureMaintenanceCommands : List Command :=
  [ .claimServing fixtureDay fixturePathfinder .coolGrain
  , .performMaintenance fixturePathfinder .readTwinGauges
  , .performMaintenance fixtureEngineer .isolateFeederThree
  , .performMaintenance fixtureContainment .routeReturnBypass
  , .performMaintenance fixtureQuartermaster .ventMemoryPocket
  , .performMaintenance fixturePathfinder .calibrateReturnFloat
  , .performMaintenance fixtureEngineer .reseedCultureCup
  , .performMaintenance fixtureContainment .verifyFirstCycle ]

private def fixtureAfterMaintenance : State :=
  (runCommands (initialState fixturePolicy) fixtureMaintenanceCommands).get (by native_decide)

private def fixtureCarrier (state : State) (role : CrewRole) (route : Route)
    (consent : Bool) : SignedHandoffCarrier :=
  { body := {
      world := state.policy.raw.world
      content := state.policy.raw.content
      missionId := state.policy.raw.missionId
      sessionId := state.policy.raw.sessionId
      role
      signer := fixtureRecipient role
      recipient := fixtureRecipient role
      previousCounter := counterForRole state role
      counter := counterForRole state role + 1
      predecessor := handoffPredecessor state
      recommendedRoute := route
      deepConsent := consent
    }
    signature := ⟨fixtureDigest (90 + roleIndex role)⟩ }

private def fixtureAdmission (carrier : SignedHandoffCarrier) : HandoffAdmission := ⟨carrier⟩

private def addFixtureHandoffs : State → List CrewRole → Route → Bool → Option State
  | state, [], _, _ => some state
  | state, role :: roles, route, consent => do
      let briefed ← execute state (.deliverBriefing role
        (fixtureRecipient role))
      let carrier := fixtureCarrier briefed.after role route consent
      let handed ← execute briefed.after (.recordHandoff carrier (fixtureAdmission carrier))
      addFixtureHandoffs handed.after roles route consent

private def fixtureRouteReady? (route : Route) (consent : Bool) : Option State :=
  addFixtureHandoffs fixtureAfterMaintenance exactRoles route consent

private def fixtureBeforeDeepExtraction : State :=
  let routeReady := (fixtureRouteReady? .maintenanceSpine true).get (by native_decide)
  let commands : List Command :=
    [ .commitRoute .maintenanceSpine
    , .choose .observeSecondMovement
    , .choose .braceObservedRhythm
    , .choose .commitPrivateIntervals ]
  (runCommands routeReady commands).get (by native_decide)

private def fixtureDeepDebriefed : State :=
  (runCommands fixtureBeforeDeepExtraction
    [.extract .descendFurther, .issueDebrief]).get (by native_decide)

private def fixtureAtMaintenanceTruss : State :=
  (runCommands ((fixtureRouteReady? .maintenanceSpine false).get (by native_decide))
    [.commitRoute .maintenanceSpine, .choose .markMovingClearance]).get (by native_decide)

private def fixtureDraftReturned : State :=
  (runCommands fixtureAtMaintenanceTruss [.choose .withdrawAtTruss]).get (by native_decide)

private def fixtureDraftCarrier (state : State)
    (outcome : MechanicalDraftOutcomeId) : SignedDraftActivationCarrier :=
  { body := {
      world := state.policy.raw.world
      content := state.policy.raw.content
      missionId := state.policy.raw.missionId
      sessionId := state.policy.raw.sessionId
      outcome
      predecessorSequence := state.sequence
    }
    signature := fixtureDigest (180 + outcome.code) }

private def fixtureDraftAdmission
    (carrier : SignedDraftActivationCarrier) : DraftActivationAdmission := ⟨carrier⟩

private def fixtureEnrollment (state : State) (role : CrewRole)
    (recipient : Digest32) : NextWatchAdmission := ⟨{
  world := state.policy.raw.world
  content := state.policy.raw.content
  missionId := state.policy.raw.missionId
  sessionId := state.policy.raw.sessionId
  watchDay := fixtureRecoveryDay
  role
  recipient
  predecessorSequence := state.sequence
}⟩

/-- Five per-field rechecks in `applyHandoff`, each exercised with an admission
over the SAME mutated carrier, so the generic `carrier != admission` gate is not
what refuses them.

⚠ This was named `hostile_handoff_authority_substitutions_are_refused` and
carried a sixth conjunct pairing a route-mutated carrier with the UNMUTATED
carrier's admission.  That conjunct tested nothing about routes: it is caught by
`carrier != admission.authenticatedCarrier`, exactly like any other mutation
would be.  The route and consent fields have their own theorem below, and it
records that they are NOT independently rechecked. -/
theorem hostile_handoff_field_substitutions_are_refused :
    let briefed := (execute fixtureAfterMaintenance
      (.deliverBriefing .engineer fixtureEngineer)).get (by native_decide) |>.after
    let good := fixtureCarrier briefed .engineer .maintenanceSpine true
    let badSigner := { good with body := { good.body with signer := fixturePathfinder } }
    let badRecipient := { good with body := { good.body with recipient := fixturePathfinder } }
    let badCounter := { good with body := { good.body with counter := good.body.previousCounter } }
    let badRoot := { good with body := { good.body with predecessor :=
      { good.body.predecessor with sequence := good.body.predecessor.sequence + 1 } } }
    let badPack := { good with body := { good.body with content :=
      { good.body.content with packDigest := fixtureDigest 255 } } }
    execute briefed (.recordHandoff badSigner (fixtureAdmission badSigner)) = none ∧
    execute briefed (.recordHandoff badRecipient (fixtureAdmission badRecipient)) = none ∧
    execute briefed (.recordHandoff badCounter (fixtureAdmission badCounter)) = none ∧
    execute briefed (.recordHandoff badRoot (fixtureAdmission badRoot)) = none ∧
    execute briefed (.recordHandoff badPack (fixtureAdmission badPack)) = none := by
  native_decide

/-- ⚠ MEASURED, not a refusal: `applyHandoff` rechecks world, content, mission,
session, seat, signer, recipient, the counter chain, the predecessor root, the
briefing and single-use — and never looks at `recommendedRoute` or `deepConsent`.
Both are copied straight onto the receipt (`applyHandoff`), and both are
load-bearing: `specialistSupport` gates `applyRoute`, and `unanimousDeepB` gates
all three deep terminals.  Change either in the carrier and hand in an admission
over that same carrier, and the reducer records the changed value.

This is not a soundness hole — `HandoffAdmission` is `private mk ::` over the
WHOLE `SignedHandoffCarrier`, so nothing outside this module can mint one, and
the last two conjuncts show a carrier the admission does not cover is refused.
It is stated as an accepted-and-recorded fact rather than hidden inside a
refusal, because the reducer's own coverage stops at the admission here. -/
theorem handoff_route_and_deep_consent_are_bound_only_by_the_admission :
    let briefed := (execute fixtureAfterMaintenance
      (.deliverBriefing .engineer fixtureEngineer)).get (by native_decide) |>.after
    let good := fixtureCarrier briefed .engineer .maintenanceSpine true
    let otherRoute := { good with body := { good.body with recommendedRoute := .sealedNave } }
    let otherConsent := { good with body := { good.body with deepConsent := false } }
    (execute briefed (.recordHandoff otherRoute (fixtureAdmission otherRoute))).map
      (fun accepted => accepted.after.handoffs.map HandoffReceipt.recommendedRoute) =
        some [.sealedNave] ∧
    (execute briefed (.recordHandoff otherConsent (fixtureAdmission otherConsent))).map
      (fun accepted => accepted.after.handoffs.map HandoffReceipt.deepConsent) = some [false] ∧
    execute briefed (.recordHandoff otherRoute (fixtureAdmission good)) = none ∧
    execute briefed (.recordHandoff otherConsent (fixtureAdmission good)) = none := by
  native_decide

theorem mechanical_draft_requires_exact_opaque_activation_to_debrief :
    let good := fixtureDraftCarrier fixtureDraftReturned .maintenanceWithdrawn
    let wrongOutcome := { good with body :=
      { good.body with outcome := .signalReturnPartial } }
    let wrongWorld := { good with body :=
      { good.body with world := { good.body.world with contentRoot := fixtureDigest 250 } } }
    let wrongPack := { good with body :=
      { good.body with content := { good.body.content with packDigest := fixtureDigest 251 } } }
    let wrongComponent := { good with body :=
      { good.body with content := { good.body.content with component := fixtureDigest 249 } } }
    let wrongMission := { good with body :=
      { good.body with missionId := ⟨999⟩ } }
    let wrongSession := { good with body :=
      { good.body with sessionId := fixtureDigest 252 } }
    let wrongSequence := { good with body :=
      { good.body with predecessorSequence := good.body.predecessorSequence + 1 } }
    let wrongSignature := { good with signature := fixtureDigest 248 }
    execute fixtureDraftReturned .issueDebrief = none ∧
    (execute fixtureDraftReturned
      (.activateDraftSettlement good (fixtureDraftAdmission good))).isSome ∧
    execute fixtureDraftReturned
      (.activateDraftSettlement wrongOutcome (fixtureDraftAdmission wrongOutcome)) = none ∧
    execute fixtureDraftReturned
      (.activateDraftSettlement wrongWorld (fixtureDraftAdmission wrongWorld)) = none ∧
    execute fixtureDraftReturned
      (.activateDraftSettlement wrongPack (fixtureDraftAdmission wrongPack)) = none ∧
    execute fixtureDraftReturned
      (.activateDraftSettlement wrongComponent (fixtureDraftAdmission wrongComponent)) = none ∧
    execute fixtureDraftReturned
      (.activateDraftSettlement wrongMission (fixtureDraftAdmission wrongMission)) = none ∧
    execute fixtureDraftReturned
      (.activateDraftSettlement wrongSession (fixtureDraftAdmission wrongSession)) = none ∧
    execute fixtureDraftReturned
      (.activateDraftSettlement wrongSequence (fixtureDraftAdmission wrongSequence)) = none ∧
    execute fixtureDraftReturned
      (.activateDraftSettlement wrongSignature (fixtureDraftAdmission good)) = none ∧
    execute fixtureDraftReturned
      (.activateDraftSettlement wrongOutcome (fixtureDraftAdmission good)) = none := by
  native_decide

theorem extraction_injury_prefix_cannot_bypass_or_reorder_injury :
    let transition := (execute fixtureBeforeDeepExtraction (.extract .descendFurther)).get
      (by native_decide)
    let extraction := transition.events[0]
    let injury := transition.events[1]
    let midState := (applyEvent fixtureBeforeDeepExtraction extraction).get (by native_decide)
    midState.pendingInjury.isSome ∧
    execute midState .issueDebrief = none ∧
    applyEvent fixtureBeforeDeepExtraction
      ⟨fixtureBeforeDeepExtraction.sequence + 1, injury.payload⟩ = none ∧
    (applyEvent midState injury).isSome := by
  native_decide

theorem choice_injury_prefix_cannot_bypass_or_reorder_injury :
    let transition := (execute fixtureAtMaintenanceTruss (.choose .overdriveTruss)).get
      (by native_decide)
    let choice := transition.events[0]
    let injury := transition.events[1]
    let midState := (applyEvent fixtureAtMaintenanceTruss choice).get (by native_decide)
    midState.pendingInjury.isSome ∧
    execute midState (.choose .replaySharedIntervals) = none ∧
    applyEvent fixtureAtMaintenanceTruss
      ⟨fixtureAtMaintenanceTruss.sequence + 1, injury.payload⟩ = none ∧
    (applyEvent midState injury).isSome := by
  native_decide

theorem choice_early_extraction_prefix_cannot_bypass_or_reorder_terminal :
    let transition := (execute fixtureAtMaintenanceTruss (.choose .withdrawAtTruss)).get
      (by native_decide)
    let choice := transition.events[0]
    let extraction := transition.events[1]
    let midState := (applyEvent fixtureAtMaintenanceTruss choice).get (by native_decide)
    midState.pendingTerminal = some (.mechanicalDraft .maintenanceWithdrawn) ∧
    execute midState .issueDebrief = none ∧
    applyEvent fixtureAtMaintenanceTruss
      ⟨fixtureAtMaintenanceTruss.sequence + 1, extraction.payload⟩ = none ∧
    (applyEvent midState extraction).isSome := by
  native_decide

theorem serving_recovery_prefix_cannot_bypass_or_reorder_recovery :
    let transition := (execute fixtureDeepDebriefed
      (.claimServing fixtureRecoveryDay fixtureEngineer .blueTray)).get (by native_decide)
    let serving := transition.events[0]
    let recovery := transition.events[1]
    let midState := (applyEvent fixtureDeepDebriefed serving).get (by native_decide)
    midState.pendingRecoveryServing.isSome ∧
    execute midState (.completeRecoveryCalibration fixtureEngineer) = none ∧
    execute midState (.enrollNextWatch
      (fixtureEnrollment midState .pathfinder fixturePathfinder)) = none ∧
    applyEvent fixtureDeepDebriefed
      ⟨fixtureDeepDebriefed.sequence + 1, recovery.payload⟩ = none ∧
    (applyEvent midState recovery).isSome := by
  native_decide

theorem omission_and_reorder_cannot_skip_intermediate_phases :
    execute fixtureAfterMaintenance (.commitRoute .maintenanceSpine) = none ∧
    (let carrier := fixtureCarrier fixtureAfterMaintenance .engineer .maintenanceSpine true
     execute fixtureAfterMaintenance (.recordHandoff carrier (fixtureAdmission carrier)) = none) ∧
    execute (initialState fixturePolicy)
      (.performMaintenance fixtureEngineer .readTwinGauges) = none := by
  native_decide

theorem maintenance_completion_is_once_only_and_exact :
    fixtureAfterMaintenance.maintenanceContribution = some maintenanceContribution ∧
    execute fixtureAfterMaintenance
      (.performMaintenance fixtureContainment .verifyFirstCycle) = none := by
  native_decide

theorem pack_authored_operational_costs_are_exact :
    ([ .maintenanceReturn, .maintenanceDeep, .signalReturn,
       .signalDeep, .sealedReturn, .sealedDeep ] : List AuthoredOutcomeId).map
      AuthoredOutcomeId.operationalCost = [2, 5, 3, 7, 11, 12] := by
  decide

theorem deep_watch_charges_choice_costs_plus_exact_pack_terminal_cost :
    fixtureDeepDebriefed.operationalSpent = 8 ∧
      fixtureDeepDebriefed.outcome.map OutcomeReceipt.terminalOperationalCost = some 5 := by
  native_decide

theorem navigation_debt_changes_terminal_semantics :
    let ready := (fixtureRouteReady? .maintenanceSpine false).get (by native_decide)
    let indebted := (runCommands ready
      [.commitRoute .maintenanceSpine, .choose .ignoreMovingClearance,
       .choose .braceObservedRhythm, .choose .replaySharedIntervals]).get (by native_decide)
    expectedOutcomeReceipt? indebted .returnNow |>.map OutcomeReceipt.terminal =
      some (.mechanicalDraft .maintenanceWithdrawn) := by
  native_decide

theorem deep_terminal_requires_both_clue_threshold_and_exact_evidence :
    expectedOutcomeReceipt? ({ fixtureBeforeDeepExtraction with clueIntel := 0 } : State)
      .descendFurther = none ∧
    expectedOutcomeReceipt? ({ fixtureBeforeDeepExtraction with evidence :=
      (fixtureBeforeDeepExtraction.evidence.erase artifactPressureIntervalRecord) } : State)
      .descendFurther = none := by
  native_decide

theorem formerly_dominated_choices_change_real_terminal_availability :
    let maintenanceBase := (runCommands
      ((fixtureRouteReady? .maintenanceSpine true).get (by native_decide))
      [.commitRoute .maintenanceSpine, .choose .observeSecondMovement,
       .choose .braceObservedRhythm]).get (by native_decide)
    let replayed := (execute maintenanceBase (.choose .replaySharedIntervals)).get
      (by native_decide) |>.after
    let privatelyCommitted := (execute maintenanceBase
      (.choose .commitPrivateIntervals)).get (by native_decide) |>.after
    let signalBase := (runCommands
      ((fixtureRouteReady? .signalGallery true).get (by native_decide))
      [.commitRoute .signalGallery, .choose .markMovingClearance,
       .choose .triangulateFullSequence]).get (by native_decide)
    let screened := (execute signalBase (.choose .screenCorridor)).get
      (by native_decide) |>.after
    let waited := (execute signalBase (.choose .waitMovementCycle)).get
      (by native_decide) |>.after
    let sealedBase := (runCommands
      ((fixtureRouteReady? .sealedNave false).get (by native_decide))
      [.commitRoute .sealedNave, .choose .markMovingClearance,
       .choose .performTwoRoleHandoff]).get (by native_decide)
    let photographed := (runCommands sealedBase
      [.choose .photographCradle, .choose .screenCorridor]).get (by native_decide)
    let untouched := (runCommands sealedBase
      [.choose .leaveCavityUntouched, .choose .screenCorridor]).get (by native_decide)
    expectedOutcomeReceipt? replayed .descendFurther = none ∧
    (expectedOutcomeReceipt? privatelyCommitted .descendFurther).isSome ∧
    expectedOutcomeReceipt? screened .descendFurther = none ∧
    (expectedOutcomeReceipt? waited .descendFurther).isSome ∧
    (expectedOutcomeReceipt? photographed .returnNow).map OutcomeReceipt.terminal =
      some (.authored .sealedReturn) ∧
    (expectedOutcomeReceipt? untouched .returnNow).map OutcomeReceipt.terminal =
      some (.mechanicalDraft .sealedReturnClosed) := by
  native_decide

theorem exact_engineer_reenrollment_requires_both_later_day_recovery_steps :
    let injured := fixtureDeepDebriefed
    let engineerBefore := fixtureEnrollment injured .engineer fixtureEngineer
    let pathfinderBefore := fixtureEnrollment injured .pathfinder fixturePathfinder
    let treated := (execute injured
      (.claimServing fixtureRecoveryDay fixtureEngineer .blueTray)).get (by native_decide) |>.after
    let engineerDuring := fixtureEnrollment treated .engineer fixtureEngineer
    let recovered := (execute treated
      (.completeRecoveryCalibration fixtureEngineer)).get (by native_decide) |>.after
    let engineerAfter := fixtureEnrollment recovered .engineer fixtureEngineer
    execute injured (.enrollNextWatch engineerBefore) = none ∧
    (execute injured (.enrollNextWatch pathfinderBefore)).isSome ∧
    execute treated (.enrollNextWatch engineerDuring) = none ∧
    (execute recovered (.enrollNextWatch engineerAfter)).isSome := by
  native_decide

/-- The GENERAL fact the old `finalized_days_are_zero_based_and_recovery_is_strictly_later`
name claimed and did not have: it only checked that two private fixture constants
differ by one, while the enforcement is the `recoveryVisit` guard inside
`applyServing`, which was proven nowhere.

For EVERY state and EVERY serving receipt: once the watch is `debriefed`, a day
that is not strictly after the mission day cannot be served.  `galleyVisit` needs
`phase = .galley`, `recoveryVisit` needs the strict inequality, and `applyServing`
refuses when neither holds.  No fixture, no `native_decide`, no host time. -/
theorem recovery_serving_requires_a_strictly_later_finalized_day
    (state : State) (receipt : ServingReceipt)
    (hphase : state.phase = .debriefed)
    (hday : receipt.day.dayIndex ≤ state.policy.raw.missionDay.dayIndex) :
    applyServing state receipt = none := by
  unfold applyServing
  cases hexpected : expectedServingReceipt? state receipt.day receipt.visitor receipt.choice with
  | none => simp
  | some expected =>
      simp only [hphase]
      cases hrecovery : state.recovery <;> simp_all

/-- The falsifier for the floor above plus the fixture constants the private
recovery fixtures rely on.  The gate is SATISFIABLE (the next finalized day is
served) and REFUTABLE (the mission day itself is refused, with a rotation-correct
recovery serving so the refusal is the day gate and not the rotation). -/
theorem the_strictly_later_day_gate_refuses_the_mission_day_and_admits_the_next :
    rotationForDay 0 = .pressureWeather ∧
    fixtureDay.dayIndex = 5 ∧ fixtureRecoveryDay.dayIndex = fixtureDay.dayIndex + 1 ∧
    rotationForDay fixtureDay.dayIndex = ServingChoiceId.rotation .wrappedFruit ∧
    ServingChoiceId.tag .wrappedFruit = .recovery ∧
    execute fixtureDeepDebriefed
      (.claimServing fixtureDay fixtureEngineer .wrappedFruit) = none ∧
    (execute fixtureDeepDebriefed
      (.claimServing fixtureRecoveryDay fixtureEngineer .blueTray)).isSome := by
  native_decide

private def fixtureDailySaturation : List Command :=
  (List.range MAX_COMMONS_VISITS).map fun index =>
    .claimServing fixtureDay (fixtureDigest (100 + index)) .coolGrain

private def fixtureSaturatedDay : State :=
  (runCommands (initialState fixturePolicy) fixtureDailySaturation).get (by native_decide)

theorem commons_visit_bound_rolls_over_per_finalized_daily_aggregate :
    expectedServingReceipt? fixtureSaturatedDay fixtureDay (fixtureDigest 240) .coolGrain = none ∧
    (expectedServingReceipt? fixtureSaturatedDay fixtureRecoveryDay
      (fixtureDigest 240) .homePot).isSome := by
  native_decide

theorem different_pack_digest_forces_policy_inequality (left right : Policy)
    (hpack : left.raw.content.packDigest ≠ right.raw.content.packDigest) : left ≠ right := by
  intro hpolicy
  exact hpack (congrArg (fun policy => policy.raw.content.packDigest) hpolicy)

/-! ## A design instrument over the authored watch

`Policy` has no public producer, so this lives beside the fixtures rather than in
its own module: nothing outside this file can build a `State` to walk.

Everything below walks the REAL machine.  Every successor is `execute`, every
refusal is `choicePreconditionB`, every terminal is the one a state actually
committed into `outcome` or the one `expectedOutcomeReceipt?` offers.  There is
deliberately no second cost model, because `ChoiceDelta` is NOT a sufficient
statistic for a choice and an analysis over the delta rows alone calls two live
actions dead:

* `misventRelief` ⟨1,1,1,0,∅,false⟩ is dominated by `replaySharedIntervals`
  ⟨1,1,0,1,{artifact},false⟩ — no better on any axis, strictly worse in supply and
  in clue intel, and it takes no artifact — yet it is the only choice that does
  not advance `encounterIndex` (`plannedPayloads?`).  It is a retry, not a move —
  and it is the ONE place any budget in this module ever bites.
* `ignoreMovingClearance` ties `markMovingClearance` on all four costs and on
  `causesInjury`, and is weakly worse only in artifacts, which can never hurt
  (`canSpendB` refuses only non-allowlisted ones).  They diverge in `updateFlags`:
  `navigationDebt` versus `entryMarked`, and `expectedTerminalId?` reads
  `navigationDebt` FIRST, ahead of every authored row.

SCOPE — and the names say it.  The prelude is the fixture one: the galley visit,
the seven maintenance steps, and four handoffs that all recommend the same route
with the same deep consent.  Six roots, one per (route, consent).  That is the
permissive setting for every route-sensitive gate here (`specialistSupport` is 3
of 3, `unanimousDeepB` holds exactly when consent is set), but it is one prelude
and not the whole `Policy` space, and nothing below claims otherwise.

The alphabet walked is `choose` and `extract`.  The enumeration is NOT
bounded-depth: `night_watch_reachable_set_is_closed_under_choose_and_extract`
proves the list contains all six roots and is closed under one step of every
command in that alphabet, so it is the exact reachable set for that alphabet from
those roots. -/

private def allChoiceIds : List ChoiceId :=
  [ .markMovingClearance, .observeSecondMovement, .ignoreMovingClearance
  , .braceObservedRhythm, .overdriveTruss, .withdrawAtTruss
  , .replaySharedIntervals, .commitPrivateIntervals, .misventRelief
  , .triangulateFullSequence, .preserveRawTrace, .moveBeforeRepeat
  , .screenCorridor, .waitMovementCycle, .abandonShoal
  , .performTwoRoleHandoff, .recordClosedThreshold, .withdrawFromThreshold
  , .exchangeCalibrationBlock, .photographCradle, .leaveCavityUntouched ]

private def allExtractionChoices : List ExtractionChoice := [.returnNow, .descendFurther]

private def allTerminalIds : List TerminalId :=
  [ .authored .maintenanceReturn, .authored .maintenanceDeep
  , .authored .signalReturn, .authored .signalDeep
  , .authored .sealedReturn, .authored .sealedDeep
  , .mechanicalDraft .maintenanceReturnInjured, .mechanicalDraft .maintenanceWithdrawn
  , .mechanicalDraft .signalReturnPartial, .mechanicalDraft .signalCorridorLost
  , .mechanicalDraft .sealedReturnClosed ]

/-- Nothing below can be an accident of a hand-written list that missed a
constructor: each enumeration is proven to contain every inhabitant of its type
by case analysis, not by counting. -/
theorem choice_extraction_and_terminal_enumerations_are_complete :
    (∀ choice : ChoiceId, choice ∈ allChoiceIds) ∧
    (∀ choice : ExtractionChoice, choice ∈ allExtractionChoices) ∧
    (∀ terminal : TerminalId, terminal ∈ allTerminalIds) := by
  refine ⟨fun choice => ?_, fun choice => ?_, fun terminal => ?_⟩
  · cases choice <;> decide
  · cases choice <;> decide
  · cases terminal <;> rename_i outcome <;> cases outcome <;> decide

private def containsState (states : List State) (state : State) : Bool :=
  states.any fun other => decide (other = state)

/-- One step of the watch alphabet, through `execute` — never through a
re-derived transition. -/
private def stepFrom (state : State) : List State :=
  (allChoiceIds.filterMap fun choice => (execute state (.choose choice)).map (·.after)) ++
  (allExtractionChoices.filterMap fun choice => (execute state (.extract choice)).map (·.after))

private def freshFrom (seen : List State) (frontier : List State) : List State :=
  frontier.foldl (fun acc state =>
    (stepFrom state).foldl (fun acc' next =>
      if containsState seen next || containsState acc' next then acc' else acc' ++ [next]) acc) []

/-- Breadth-first layers, deduplicated against every earlier layer, so a state's
layer index is its exact minimum command distance from a root. -/
private def bfsLayers : Nat → List State → List State → List (List State)
  | 0, _, _ => []
  | fuel + 1, seen, frontier =>
      if frontier.isEmpty then []
      else frontier :: bfsLayers fuel (seen ++ freshFrom seen frontier) (freshFrom seen frontier)

private def routeRoot? (route : Route) (consent : Bool) : Option State := do
  let ready ← fixtureRouteReady? route consent
  let committed ← execute ready (.commitRoute route)
  some committed.after

private def routeConsentGrid : List (Route × Bool) :=
  [ (.maintenanceSpine, true), (.maintenanceSpine, false)
  , (.signalGallery, true), (.signalGallery, false)
  , (.sealedNave, true), (.sealedNave, false) ]

private def nightWatchRoots : List State :=
  routeConsentGrid.filterMap fun pair => routeRoot? pair.1 pair.2

private def nightWatchLayers : List (List State) :=
  bfsLayers 40 nightWatchRoots nightWatchRoots

private def nightWatchReachable : List State := nightWatchLayers.flatten

private def encounterStates : List State :=
  nightWatchReachable.filter fun state => decide (state.phase = .encounters)

/-- `filterMap` dropped nothing: all six (route, consent) preludes reach a
committed route, in grid order, each after exactly seventeen events — the galley
visit, seven maintenance steps, four briefings, four handoffs and the route
commitment, one event apiece. -/
theorem every_route_and_consent_prelude_commits_after_seventeen_events :
    nightWatchRoots.length = 6 ∧
    nightWatchRoots.map State.route = routeConsentGrid.map (fun pair => some pair.1) ∧
    nightWatchRoots.all (fun state => decide (state.sequence = 17)) = true := by
  native_decide

/-- ⚑ THE COMPLETENESS CLAIM every result below rests on.  The enumerated list
contains all six roots and every `execute`-successor of every state in it under
the whole `choose`/`extract` alphabet.  A set containing the roots and closed
under the transition relation contains everything reachable from the roots, so
these are exhaustive results and not depth-limited ones. -/
theorem night_watch_reachable_set_is_closed_under_choose_and_extract :
    nightWatchRoots.all (fun state => containsState nightWatchReachable state) = true ∧
    (nightWatchReachable.flatMap stepFrom).all
      (fun state => containsState nightWatchReachable state) = true ∧
    nightWatchLayers.map List.length = [6, 18, 54, 105, 138, 96, 62, 62, 62, 56, 44, 25, 13] ∧
    nightWatchReachable.length = 741 ∧
    (nightWatchReachable.foldl (fun acc state =>
      if containsState acc state then acc else acc ++ [state]) []).length = 741 := by
  native_decide

/-! ### 1 — terminal reachability -/

private def reachableTerminals : List TerminalId :=
  allTerminalIds.filter fun terminal =>
    nightWatchReachable.any fun state =>
      state.outcome.any fun receipt => decide (receipt.terminal = terminal)

private def offeredTerminals : List TerminalId :=
  allTerminalIds.filter fun terminal =>
    nightWatchReachable.any fun state =>
      allExtractionChoices.any fun choice =>
        (expectedOutcomeReceipt? state choice).any fun receipt =>
          decide (receipt.terminal = terminal)

private def terminalsForRoute (route : Route) : List TerminalId :=
  allTerminalIds.filter fun terminal =>
    nightWatchReachable.any fun state =>
      decide (state.route = some route) &&
        state.outcome.any fun receipt => decide (receipt.terminal = terminal)

/-- ANSWER: no terminal is unreachable.  All eleven — six authored rows and five
mechanical drafts — are both offered by `expectedOutcomeReceipt?` from a reachable
state and actually committed into some reachable state's `outcome`, and the three
routes partition them 4/4/3 with no terminal crossing a route. -/
theorem every_terminal_is_reachable_and_the_routes_partition_them :
    reachableTerminals = allTerminalIds ∧
    offeredTerminals = allTerminalIds ∧
    terminalsForRoute .maintenanceSpine =
      [ .authored .maintenanceReturn, .authored .maintenanceDeep
      , .mechanicalDraft .maintenanceReturnInjured
      , .mechanicalDraft .maintenanceWithdrawn ] ∧
    terminalsForRoute .signalGallery =
      [ .authored .signalReturn, .authored .signalDeep
      , .mechanicalDraft .signalReturnPartial, .mechanicalDraft .signalCorridorLost ] ∧
    terminalsForRoute .sealedNave =
      [ .authored .sealedReturn, .authored .sealedDeep
      , .mechanicalDraft .sealedReturnClosed ] := by
  native_decide

/-! ### 2 — dead choices -/

private def liveChoices : List ChoiceId :=
  allChoiceIds.filter fun choice =>
    nightWatchReachable.any fun state => (execute state (.choose choice)).isSome

private def deadChoices : List ChoiceId :=
  allChoiceIds.filter fun choice =>
    !nightWatchReachable.any fun state => (execute state (.choose choice)).isSome

/-- ANSWER: no choice is dead.  All twenty-one authored choices are accepted by
`execute` from some reachable state — including the two a cost-row analysis
would have retired. -/
theorem no_authored_choice_is_dead_in_the_reachable_watch :
    liveChoices = allChoiceIds ∧ deadChoices = [] ∧ allChoiceIds.length = 21 := by
  native_decide

/-- Why a `ChoiceDelta` analysis would have been wrong.  `misventRelief` is
dominated on every cost axis by `replaySharedIntervals` and is still the only way
to stay on an encounter; `ignoreMovingClearance` ties `markMovingClearance` on all
four costs and on injury, differs only by an artifact it does not take, and sets a
DIFFERENT flag — which is the flag `expectedTerminalId?` consults first. -/
theorem cost_row_domination_does_not_survive_the_real_transition :
    let atIntervals := (runCommands
      ((fixtureRouteReady? .maintenanceSpine true).get (by native_decide))
      [.commitRoute .maintenanceSpine, .choose .observeSecondMovement,
       .choose .braceObservedRhythm]).get (by native_decide)
    let retried := (execute atIntervals (.choose .misventRelief)).get (by native_decide) |>.after
    let advanced := (execute atIntervals
      (.choose .replaySharedIntervals)).get (by native_decide) |>.after
    let entry := (fixtureRouteReady? .maintenanceSpine true).get (by native_decide)
    let committed := (execute entry (.commitRoute .maintenanceSpine)).get (by native_decide) |>.after
    let ignored := (execute committed
      (.choose .ignoreMovingClearance)).get (by native_decide) |>.after
    let marked := (execute committed
      (.choose .markMovingClearance)).get (by native_decide) |>.after
    (ChoiceId.delta .misventRelief).turnCost = (ChoiceId.delta .replaySharedIntervals).turnCost ∧
    (ChoiceId.delta .misventRelief).operationalCost =
      (ChoiceId.delta .replaySharedIntervals).operationalCost ∧
    (ChoiceId.delta .replaySharedIntervals).supplyCost <
      (ChoiceId.delta .misventRelief).supplyCost ∧
    (ChoiceId.delta .misventRelief).clueIntel <
      (ChoiceId.delta .replaySharedIntervals).clueIntel ∧
    retried.encounterIndex = atIntervals.encounterIndex ∧
    advanced.encounterIndex = atIntervals.encounterIndex + 1 ∧
    (execute retried (.choose .replaySharedIntervals)).isSome ∧
    (ChoiceId.delta .ignoreMovingClearance).turnCost =
      (ChoiceId.delta .markMovingClearance).turnCost ∧
    (ChoiceId.delta .ignoreMovingClearance).operationalCost =
      (ChoiceId.delta .markMovingClearance).operationalCost ∧
    (ChoiceId.delta .ignoreMovingClearance).supplyCost =
      (ChoiceId.delta .markMovingClearance).supplyCost ∧
    (ChoiceId.delta .ignoreMovingClearance).clueIntel =
      (ChoiceId.delta .markMovingClearance).clueIntel ∧
    (ChoiceId.delta .ignoreMovingClearance).causesInjury =
      (ChoiceId.delta .markMovingClearance).causesInjury ∧
    ignored.flags.navigationDebt = true ∧ ignored.flags.entryMarked = false ∧
    marked.flags.entryMarked = true ∧ marked.flags.navigationDebt = false := by
  native_decide

/-! ### 3 — which budgets bind -/

/-- A budget binds at a state/choice pair exactly when zeroing that ONE counter
turns a refusal into an acceptance.  Zeroing a counter can only move
`choicePreconditionB` through its `canSpendB` clause — no other part of the
predicate reads a spend counter — so this isolates the budget without restating
the gate.  (`choicePreconditionB`, not `execute`: `execute` also runs
`applyExtraction`, which reads `clueIntel` through `expectedTerminalId?`, and an
`execute`-based probe reports a clue-intel binding that is really a terminal
re-selection.) -/
private def choicesRefusedSolelyBy (relax : State → State) : List ChoiceId :=
  allChoiceIds.filter fun choice =>
    nightWatchReachable.any fun state =>
      !choicePreconditionB state choice && choicePreconditionB (relax state) choice

/-- ANSWER: one of the four budgets binds.  `SUPPLY_SPEND_LIMIT = 8` refuses
`misventRelief` — the retry — on a path every other gate admits.  The turn,
operational and clue-intel budgets never refuse anything the rest of the gate
would have taken. -/
theorem only_the_supply_limit_ever_refuses_an_otherwise_admitted_choice :
    choicesRefusedSolelyBy (fun state => { state with suppliesSpent := 0 }) = [.misventRelief] ∧
    choicesRefusedSolelyBy (fun state => { state with turnsSpent := 0 }) = [] ∧
    choicesRefusedSolelyBy (fun state => { state with operationalSpent := 0 }) = [] ∧
    choicesRefusedSolelyBy (fun state => { state with clueIntel := 0 }) = [] := by
  native_decide

/-- The stronger form of the same answer: three of the four `canSpendB` clauses
never EVALUATE to false anywhere in the reachable watch — over every
encounter-phase state and every choice, not merely the currently-gated ones.  A
clause that never fires cannot change the reachable set, so `TURN_BUDGET`,
`OPERATIONAL_BUDGET` and `CLUE_INTEL_LIMIT` are inert at these values.  The
fourth conjunct is the falsifier: the supply clause DOES fire.  The fifth is the
extraction-side operational check in `applyExtraction`, which also never fires. -/
theorem three_of_four_budget_clauses_never_fire_in_the_reachable_watch :
    encounterStates.all (fun state => allChoiceIds.all fun choice =>
      decide (state.turnsSpent + choice.delta.turnCost ≤ TURN_BUDGET)) = true ∧
    encounterStates.all (fun state => allChoiceIds.all fun choice =>
      decide (state.operationalSpent + choice.delta.operationalCost ≤ OPERATIONAL_BUDGET)) = true ∧
    encounterStates.all (fun state => allChoiceIds.all fun choice =>
      decide (state.clueIntel + choice.delta.clueIntel ≤ CLUE_INTEL_LIMIT)) = true ∧
    encounterStates.all (fun state => allChoiceIds.all fun choice =>
      decide (state.suppliesSpent + choice.delta.supplyCost ≤ SUPPLY_SPEND_LIMIT)) = false ∧
    nightWatchReachable.all (fun state => allExtractionChoices.all fun choice =>
      (expectedOutcomeReceipt? state choice).all fun receipt =>
        decide (state.operationalSpent + receipt.terminalOperationalCost
          ≤ OPERATIONAL_BUDGET)) = true := by
  native_decide

/-- The headroom behind that answer, as numbers a designer can retune against:
the maxima actually attained, first over encounter-phase states (where choices are
priced) and then over the whole reachable watch (where extraction costs land).
`SUPPLY_SPEND_LIMIT` is the only one reached; the turn budget of 18 tops out at
13, the clue-intel limit of 12 at 5. -/
theorem watch_counter_maxima_show_which_budgets_are_reached :
    (encounterStates.foldl (fun bound state => max bound state.turnsSpent) 0,
     encounterStates.foldl (fun bound state => max bound state.operationalSpent) 0,
     encounterStates.foldl (fun bound state => max bound state.suppliesSpent) 0,
     encounterStates.foldl (fun bound state => max bound state.clueIntel) 0) = (11, 10, 8, 4) ∧
    (nightWatchReachable.foldl (fun bound state => max bound state.turnsSpent) 0,
     nightWatchReachable.foldl (fun bound state => max bound state.operationalSpent) 0,
     nightWatchReachable.foldl (fun bound state => max bound state.suppliesSpent) 0,
     nightWatchReachable.foldl (fun bound state => max bound state.clueIntel) 0) =
       (13, 18, 8, 5) ∧
    (TURN_BUDGET, OPERATIONAL_BUDGET, SUPPLY_SPEND_LIMIT, CLUE_INTEL_LIMIT) = (18, 20, 8, 12) := by
  native_decide

/-! ### 4 — execution floors -/

private def watchCommandFloor (terminal : TerminalId) : Option Nat :=
  nightWatchLayers.findIdx? fun layer =>
    layer.any fun state => state.outcome.any fun receipt => decide (receipt.terminal = terminal)

private def terminalFloorTable : List (TerminalId × Option Nat) :=
  allTerminalIds.map fun terminal => (terminal, watchCommandFloor terminal)

/-- ANSWER: the shortest accepted `choose`/`extract` sequence from a
committed-route root to each terminal.  Add the seventeen prelude commands from
`initialState fixturePolicy` (one event apiece, pinned above) for the floor from
a cold start: 19 for the two two-command drafts, 20, 21, and 22 for the sealed
authored rows.  The three cheapest are early exits that need no `extract` at all —
a `choose` carrying its own `extractionResolved` — which is why they undercut
every authored row by two commands. -/
theorem watch_command_floors_to_every_terminal_from_the_route_roots :
    terminalFloorTable =
      [ (.authored .maintenanceReturn, some 4)
      , (.authored .maintenanceDeep, some 4)
      , (.authored .signalReturn, some 4)
      , (.authored .signalDeep, some 4)
      , (.authored .sealedReturn, some 5)
      , (.authored .sealedDeep, some 5)
      , (.mechanicalDraft .maintenanceReturnInjured, some 4)
      , (.mechanicalDraft .maintenanceWithdrawn, some 2)
      , (.mechanicalDraft .signalReturnPartial, some 4)
      , (.mechanicalDraft .signalCorridorLost, some 3)
      , (.mechanicalDraft .sealedReturnClosed, some 2) ] := by
  native_decide

#assert_axioms accepted_transition_carries_its_exact_replay
#assert_axioms choice_receipt_uses_exact_delta
#assert_axioms outcome_receipt_relics_are_exactly_allowlisted
#assert_axioms outcome_receipt_is_within_pack_budget
#assert_axioms outcome_receipt_terminal_cost_is_exact
#assert_axioms debrief_version_is_semantic
#assert_axioms witness_thread_is_not_carried
#assert_axioms treatment_locks_exact_engineer
#assert_axioms treatment_does_not_lock_other_role
#assert_axioms recovery_serving_requires_a_strictly_later_finalized_day
#assert_axioms choice_extraction_and_terminal_enumerations_are_complete
#assert_compiled maintenanceContribution_validates_exactly
#assert_compiled hostile_handoff_field_substitutions_are_refused
#assert_compiled handoff_route_and_deep_consent_are_bound_only_by_the_admission
#assert_compiled mechanical_draft_requires_exact_opaque_activation_to_debrief
#assert_compiled extraction_injury_prefix_cannot_bypass_or_reorder_injury
#assert_compiled choice_injury_prefix_cannot_bypass_or_reorder_injury
#assert_compiled choice_early_extraction_prefix_cannot_bypass_or_reorder_terminal
#assert_compiled serving_recovery_prefix_cannot_bypass_or_reorder_recovery
#assert_compiled omission_and_reorder_cannot_skip_intermediate_phases
#assert_compiled maintenance_completion_is_once_only_and_exact
#assert_axioms pack_authored_operational_costs_are_exact
#assert_compiled deep_watch_charges_choice_costs_plus_exact_pack_terminal_cost
#assert_compiled navigation_debt_changes_terminal_semantics
#assert_compiled deep_terminal_requires_both_clue_threshold_and_exact_evidence
#assert_compiled formerly_dominated_choices_change_real_terminal_availability
#assert_compiled exact_engineer_reenrollment_requires_both_later_day_recovery_steps
#assert_compiled the_strictly_later_day_gate_refuses_the_mission_day_and_admits_the_next
#assert_compiled commons_visit_bound_rolls_over_per_finalized_daily_aggregate
#assert_axioms different_pack_digest_forces_policy_inequality
#assert_compiled every_route_and_consent_prelude_commits_after_seventeen_events
#assert_compiled night_watch_reachable_set_is_closed_under_choose_and_extract
#assert_compiled every_terminal_is_reachable_and_the_routes_partition_them
#assert_compiled no_authored_choice_is_dead_in_the_reachable_watch
#assert_compiled cost_row_domination_does_not_survive_the_real_transition
#assert_compiled only_the_supply_limit_ever_refuses_an_otherwise_admitted_choice
#assert_compiled three_of_four_budget_clauses_never_fire_in_the_reachable_watch
#assert_compiled watch_counter_maxima_show_which_budgets_are_reached
#assert_compiled watch_command_floors_to_every_terminal_from_the_route_roots

end Dregg2.Games.PathOfAngels.NightWatchLoop
