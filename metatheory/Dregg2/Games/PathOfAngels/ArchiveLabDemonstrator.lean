/-
# ArchiveLabDemonstrator — one complete finite theory/evidence investigation

Eight archived observations describe an unexplained signal aboard the ship.  Two
are attractive contaminated leads.  One rejected hypothesis has both sound support
and stronger sound refutation, so the player must represent a contradiction rather
than merely collect clues agreeing with the answer.

The optimal research route uses all fourteen operations: screen and test six exact
archive origins, triangulate two independently-held supporting observations, and
publish.  The bounded selection-lattice analyzer exhausts every evidence subset,
every zero-or-one triangulation, and every hypothesis (29,696 candidates) and finds
one winning selection.  This is fiction-neutral content: ids and mechanisms, no PoA
story reveal.
-/
import Dregg2.Games.PathOfAngels.ArchiveLab
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.ArchiveLabDemonstrator

open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.FieldArchive
open Dregg2.Games.PathOfAngels.ArchiveLab

set_option autoImplicit false

/-! ## Exact activated domain and archived source records -/

def taggedDigest (tag : Nat) : Digest32 where
  bytes := byte tag :: List.replicate 31 0
  length_eq := by simp

def federation : Digest32 := taggedDigest 1
def contentRoot : Digest32 := taggedDigest 2
def activationDigest : Digest32 := taggedDigest 3
def contentSession : Digest32 := taggedDigest 4
def runSeed : Digest32 := taggedDigest 5
def sourceDigest : Digest32 := taggedDigest 6

def epoch : EpochId := ⟨17⟩
def sourceMissionId : MissionId := ⟨700⟩
def researchMissionId : MissionId := ⟨701⟩

def analystA : Digest32 := taggedDigest 31
def analystB : Digest32 := taggedDigest 32
def analystC : Digest32 := taggedDigest 33
def demoPlayer : Digest32 := taggedDigest 41
def demoActorRoot : Digest32 := taggedDigest 42

def sourceBudget : ContributionBudget where
  intel := ⟨0, by decide⟩
  supplies := ⟨0, by decide⟩
  cohesion := ⟨0, by decide⟩
  influence := ⟨0, by decide⟩
  score := ⟨0, by decide⟩
  relics := ⟨0, by decide⟩

def researchBudget : ContributionBudget where
  intel := ⟨100, by decide⟩
  supplies := ⟨0, by decide⟩
  cohesion := ⟨1, by decide⟩
  influence := ⟨0, by decide⟩
  score := ⟨500, by decide⟩
  relics := ⟨0, by decide⟩

def sourceArtifact (index : Nat) : ArtifactRef where
  missionId := sourceMissionId
  artifactId := ⟨100 + index⟩
  sourceDigest
  contentDigest := taggedDigest (80 + index)

def sourceMission (index : Nat) : MissionSpec where
  missionId := sourceMissionId
  artifact := sourceArtifact index
  epoch
  federationId := federation
  contentRoot
  activationDigest
  contentSession
  runSeed
  budget := sourceBudget
  allowedRelics := ∅
  privacy := .public
  ballot := .none
  artifact_matches := rfl
  allowed_relics_bounded := by simp

def originKey (index : Nat) (holder : Digest32) : ReceiptKey where
  federationId := federation
  contentSession
  contentEpoch := epoch
  playerKey := holder
  playerCounter := index + 1

def sourceEntry (index : Nat) (holder : Digest32) : ArchiveEntry where
  artifact := sourceArtifact index
  originKey := originKey index holder
  mission := sourceMission index
  federationId := federation
  contentRoot
  activationDigest
  contentSession
  contentEpoch := epoch

def researchArtifact : ArtifactRef where
  missionId := researchMissionId
  artifactId := ⟨900⟩
  sourceDigest := taggedDigest 90
  contentDigest := taggedDigest 91

def researchMission : MissionSpec where
  missionId := researchMissionId
  artifact := researchArtifact
  epoch
  federationId := federation
  contentRoot
  activationDigest
  contentSession
  runSeed
  budget := researchBudget
  allowedRelics := ∅
  privacy := .public
  ballot := .none
  artifact_matches := rfl
  allowed_relics_bounded := by simp

/-! ## Four hypotheses and eight observations -/

def resonance : HypothesisId := ⟨0⟩
def maintenanceBeacon : HypothesisId := ⟨1⟩
def externalCarrier : HypothesisId := ⟨2⟩
def sensorArtifact : HypothesisId := ⟨3⟩

def thermalRise : ObservationId := ⟨0⟩
def carrierBeat : ObservationId := ⟨1⟩
def regularPing : ObservationId := ⟨2⟩
def timingDrift : ObservationId := ⟨3⟩
def hullScrape : ObservationId := ⟨4⟩
def pressureSilence : ObservationId := ⟨5⟩
def sensorDropout : ObservationId := ⟨6⟩
def gyroContinuity : ObservationId := ⟨7⟩

def observation (id : ObservationId) (holder : Digest32) (bearing : Bearing)
    (weight : Fin 5) (information : Fin 6) (verdict : EvidenceVerdict) : Observation where
  id
  entry := sourceEntry id.value holder
  sourceMission := sourceMissionId
  custody := {
    originKey := originKey id.value holder
    holder
    transferSequence := id.value + 1
  }
  bearing
  weight
  information
  verdict

def thermalObservation : Observation :=
  observation thermalRise analystA (.supports resonance) ⟨2, by decide⟩ ⟨3, by decide⟩ .sound

def carrierObservation : Observation :=
  observation carrierBeat analystB (.supports resonance) ⟨3, by decide⟩ ⟨4, by decide⟩ .sound

/-- Attractive false lead: it resembles a maintenance cadence but fails testing. -/
def pingObservation : Observation :=
  observation regularPing analystA (.supports maintenanceBeacon)
    ⟨2, by decide⟩ ⟨2, by decide⟩ .contaminated

def timingObservation : Observation :=
  observation timingDrift analystC (.refutes maintenanceBeacon)
    ⟨3, by decide⟩ ⟨3, by decide⟩ .sound

/-- A real weak support which must remain visible beside stronger refutation. -/
def scrapeObservation : Observation :=
  observation hullScrape analystA (.supports externalCarrier)
    ⟨1, by decide⟩ ⟨2, by decide⟩ .sound

def silenceObservation : Observation :=
  observation pressureSilence analystC (.refutes externalCarrier)
    ⟨2, by decide⟩ ⟨3, by decide⟩ .sound

/-- Second attractive false lead. -/
def dropoutObservation : Observation :=
  observation sensorDropout analystA (.supports sensorArtifact)
    ⟨2, by decide⟩ ⟨2, by decide⟩ .contaminated

def gyroObservation : Observation :=
  observation gyroContinuity analystB (.refutes sensorArtifact)
    ⟨3, by decide⟩ ⟨3, by decide⟩ .sound

def demoObservations : List Observation :=
  [ thermalObservation, carrierObservation, pingObservation, timingObservation
  , scrapeObservation, silenceObservation, dropoutObservation, gyroObservation
  ]

def demoArchive : ArchiveState where
  entries := demoObservations.map (·.entry) |>.toFinset

def demoRawConfig : RawConfig where
  mission := researchMission
  sourceMission := sourceMissionId
  archive := demoArchive
  hypotheses := [resonance, maintenanceBeacon, externalCarrier, sensorArtifact]
  observations := demoObservations
  allowedCustodians := {analystA, analystB, analystC}
  operationBudget := 14
  publishSupportFloor := 5

theorem demo_config_valid : configValidB demoRawConfig = true := by
  native_decide

def demoConfig : Config := ⟨demoRawConfig, demo_config_valid⟩

def demoContext : JudgeContext where
  actorRoot := demoActorRoot
  playerKey := demoPlayer
  previousPlayerCounter := 8

def demoSession : SessionKey := sessionKey demoConfig demoContext

def act (sequence : Nat) (command : Command) : Action :=
  { session := demoSession, sequence, command }

/-! ## The exact winning route -/

def evidenceActions : List Action :=
  [ act 0 (.screen thermalRise), act 1 (.test thermalRise)
  , act 2 (.screen carrierBeat), act 3 (.test carrierBeat)
  , act 4 (.screen timingDrift), act 5 (.test timingDrift)
  , act 6 (.screen hullScrape), act 7 (.test hullScrape)
  , act 8 (.screen pressureSilence), act 9 (.test pressureSilence)
  , act 10 (.screen gyroContinuity), act 11 (.test gyroContinuity)
  ]

def winningActions : List Action := evidenceActions ++
  [act 12 (.triangulate thermalRise carrierBeat), act 13 (.publish resonance)]

def evidenceState : State :=
  match replay demoConfig (initialState demoConfig demoContext) evidenceActions with
  | some state => state
  | none => initialState demoConfig demoContext

theorem evidence_route_reaches_theory_decision :
    evidenceState.operationsSpent = 12 ∧
      supportScore demoConfig evidenceState resonance = 5 ∧
      refuteScore demoConfig evidenceState resonance = 0 ∧
      supportScore demoConfig evidenceState externalCarrier = 1 ∧
      refuteScore demoConfig evidenceState externalCarrier = 2 := by
  native_decide

def winningReplayB : Bool :=
  match replay demoConfig (initialState demoConfig demoContext) winningActions with
  | some state =>
      decide (state.published = some resonance) &&
      decide (state.operationsSpent = 14) &&
      decide (state.nextSequence = 14) &&
      publishableB demoConfig state resonance
  | none => false

theorem winning_route_publishes : winningReplayB = true := by
  native_decide

def winningJudgeB : Bool :=
  match judge demoConfig WorldState.empty demoContext winningActions with
  | some run =>
      decide (run.record.artifact = researchArtifact) &&
      decide (run.record.hypothesis = resonance) &&
      decide (run.record.evidence.length = 6) &&
      decide (run.record.support = 5) &&
      decide (run.record.refutation = 0) &&
      decide (run.record.information = 20) &&
      decide (run.record.operationsSpent = 14) &&
      decide (run.receipt.contribution.intel.val = 20) &&
      decide (run.receipt.contribution.cohesion.val = 1) &&
      decide (run.receipt.contribution.score.val = 75) &&
      decide (researchArtifact ∈ run.afterWorld.betaArtifacts) &&
      decide (run.receipt.playerCounter = 9) &&
      decide (run.receipt.transcriptDigest = transcriptDigest winningActions)
  | none => false

theorem winning_route_produces_exact_record_and_contribution : winningJudgeB = true := by
  native_decide

def winningProvenanceExactB : Bool :=
  match judge demoConfig WorldState.empty demoContext winningActions with
  | none => false
  | some run => run.record.evidence.all (fun used =>
      match demoObservations.find? (fun authored => authored.id = used.observationId) with
      | none => false
      | some authored =>
          decide (used = EvidenceUse.ofObservation authored) &&
          decide (authored.entry ∈ demoArchive.entries) &&
          decide (used.originKey = authored.entry.originKey) &&
          decide (used.custody.originKey = authored.entry.originKey) &&
          decide (used.sourceMission = sourceMissionId) &&
          decide (authored.entry.federationId = researchMission.federationId) &&
          decide (authored.entry.contentSession = researchMission.contentSession) &&
          decide (authored.entry.contentEpoch = researchMission.epoch))

theorem winning_record_preserves_every_archive_and_custody_binding :
    winningProvenanceExactB = true := by
  native_decide

/-! ## False leads, contradictions, and hostile replay -/

def noTriangulationActions : List Action :=
  evidenceActions ++ [act 12 (.publish resonance)]

theorem publication_without_independent_triangulation_refuses :
    replay demoConfig (initialState demoConfig demoContext) noTriangulationActions = none := by
  native_decide

/-- Screening the false maintenance lead consumes the one operation that publication
needs.  The later sequence-correct publish reaches an exhausted receiver and refuses. -/
def decoyActions : List Action := evidenceActions ++
  [ act 12 (.screen regularPing)
  , act 13 (.triangulate thermalRise carrierBeat)
  , act 14 (.publish resonance)
  ]

theorem chasing_the_false_lead_loses_the_publication_window :
    replay demoConfig (initialState demoConfig demoContext) decoyActions = none := by
  native_decide

def contaminatedTestActions : List Action :=
  [act 0 (.screen regularPing), act 1 (.test regularPing)]

def contaminatedState : State :=
  match replay demoConfig (initialState demoConfig demoContext) contaminatedTestActions with
  | some state => state
  | none => initialState demoConfig demoContext

theorem contaminated_lead_cannot_forge_support_or_information :
    supportScore demoConfig contaminatedState maintenanceBeacon = 0 ∧
      informationGain demoConfig contaminatedState = 0 := by
  native_decide

theorem witnessed_external_carrier_contradiction_is_real :
    0 < supportScore demoConfig evidenceState externalCarrier ∧
      supportScore demoConfig evidenceState externalCarrier <
        refuteScore demoConfig evidenceState externalCarrier ∧
      witnessedContradictionB demoConfig evidenceState resonance = true := by
  native_decide

def copiedSession : SessionKey := { demoSession with playerKey := taggedDigest 99 }
def copiedFirstAction : Action := { (act 0 (.screen thermalRise)) with session := copiedSession }

theorem copied_cross_player_action_refuses :
    step demoConfig (initialState demoConfig demoContext) copiedFirstAction = none := by
  native_decide

def afterFirstAction : State :=
  match step demoConfig (initialState demoConfig demoContext) (act 0 (.screen thermalRise)) with
  | some state => state
  | none => initialState demoConfig demoContext

theorem identical_envelope_replay_refuses :
    step demoConfig afterFirstAction (act 0 (.screen thermalRise)) = none := by
  native_decide

def maxCounterContext : JudgeContext where
  actorRoot := demoActorRoot
  playerKey := demoPlayer
  previousPlayerCounter := PLAYER_COUNTER_MODULUS - 1

def actionForContext (context : JudgeContext) (action : Action) : Action :=
  { action with session := sessionKey demoConfig context }

def maxCounterActions : List Action :=
  winningActions.map (actionForContext maxCounterContext)

/-- The puzzle itself replays and reaches publication under the exhausted
session key.  Settlement alone refuses because its next counter would be exactly
`2^64`, so this fixture isolates the counter boundary from every game rule. -/
def maxCounterBoundaryB : Bool :=
  (match replay demoConfig (initialState demoConfig maxCounterContext) maxCounterActions with
   | some state => decide (state.published = some resonance)
   | none => false) &&
  decide (judge demoConfig WorldState.empty maxCounterContext maxCounterActions = none)

theorem otherwise_valid_run_at_max_counter_is_refused : maxCounterBoundaryB = true := by
  native_decide

def afterTriangulation : State :=
  match step demoConfig evidenceState (act 12 (.triangulate thermalRise carrierBeat)) with
  | some state => state
  | none => evidenceState

theorem reversing_a_consumed_pair_does_not_create_a_second_triangulation :
    step demoConfig afterTriangulation (act 13 (.triangulate carrierBeat thermalRise)) = none := by
  native_decide

/-! ## Hostile catalogue fixtures -/

def forgedOriginObservation : Observation :=
  { thermalObservation with
    custody := { thermalObservation.custody with originKey := originKey 15 analystA } }

def forgedOriginRaw : RawConfig :=
  { demoRawConfig with observations := forgedOriginObservation :: demoObservations.drop 1 }

theorem forged_custody_origin_is_rejected : configValidB forgedOriginRaw = false := by
  native_decide

def wrongMissionObservation : Observation :=
  { thermalObservation with sourceMission := ⟨999⟩ }

def wrongMissionRaw : RawConfig :=
  { demoRawConfig with observations := wrongMissionObservation :: demoObservations.drop 1 }

theorem wrong_source_mission_is_rejected : configValidB wrongMissionRaw = false := by
  native_decide

def unarchivedObservation : Observation :=
  { thermalObservation with entry := sourceEntry 15 analystA }

def unarchivedRaw : RawConfig :=
  { demoRawConfig with observations := unarchivedObservation :: demoObservations.drop 1 }

theorem unarchived_observation_is_rejected : configValidB unarchivedRaw = false := by
  native_decide

def sameHolderCarrierObservation : Observation :=
  { carrierObservation with
    custody := { carrierObservation.custody with holder := analystA } }

def sameHolderRaw : RawConfig :=
  { demoRawConfig with
    observations := thermalObservation :: sameHolderCarrierObservation :: demoObservations.drop 2 }

theorem transferred_same_holder_catalogue_is_well_formed : configValidB sameHolderRaw = true := by
  native_decide

def sameHolderConfig : Config := ⟨sameHolderRaw, transferred_same_holder_catalogue_is_well_formed⟩

def sameHolderContext : JudgeContext := demoContext
def sameHolderSession : SessionKey := sessionKey sameHolderConfig sameHolderContext

def sameHolderAction (sequence : Nat) (command : Command) : Action :=
  { session := sameHolderSession, sequence, command }

def sameHolderEvidenceActions : List Action :=
  [ sameHolderAction 0 (.screen thermalRise), sameHolderAction 1 (.test thermalRise)
  , sameHolderAction 2 (.screen carrierBeat), sameHolderAction 3 (.test carrierBeat)
  ]

def sameHolderEvidenceState : State :=
  match replay sameHolderConfig (initialState sameHolderConfig sameHolderContext)
      sameHolderEvidenceActions with
  | some state => state
  | none => initialState sameHolderConfig sameHolderContext

theorem same_custodian_cannot_self_triangulate :
    step sameHolderConfig sameHolderEvidenceState
      (sameHolderAction 4 (.triangulate thermalRise carrierBeat)) = none := by
  native_decide

/-! ## Exhaustive bounded evidence-selection lattice -/

structure AbstractPlan where
  tested : List ObservationId
  triangulation : Option PairKey
  hypothesis : HypothesisId
deriving DecidableEq

def observationIds : List ObservationId := demoObservations.map (·.id)

def subsets {α : Type} : List α → List (List α)
  | [] => [[]]
  | head :: tail =>
      let rest := subsets tail
      rest ++ rest.map (head :: ·)

def pairOptions : List (Option PairKey) :=
  none :: (observationIds.flatMap fun left =>
    (observationIds.filter fun right => decide (left.value < right.value)).map fun right =>
      some (PairKey.canonical left right))

def abstractPlans : List AbstractPlan :=
  (subsets observationIds).flatMap fun tested =>
    pairOptions.flatMap fun triangulation =>
      demoRawConfig.hypotheses.map fun hypothesis => ⟨tested, triangulation, hypothesis⟩

def abstractState (plan : AbstractPlan) : State :=
  let tested := plan.tested.toFinset
  let triangulations := match plan.triangulation with
    | none => ∅
    | some pair => {pair}
  { session := demoSession
    nextSequence := 2 * tested.card + triangulations.card
    operationsSpent := 2 * tested.card + triangulations.card
    screened := tested
    tested
    triangulations
    published := none }

/-- The final publication costs one more operation. -/
def abstractPlanWinsB (plan : AbstractPlan) : Bool :=
  decide ((abstractState plan).operationsSpent < demoRawConfig.operationBudget) &&
    publishableB demoConfig (abstractState plan) plan.hypothesis

def winningAbstractPlans : List AbstractPlan :=
  abstractPlans.filter abstractPlanWinsB

def canonicalPlan : AbstractPlan where
  tested := [thermalRise, carrierBeat, timingDrift, hullScrape, pressureSilence, gyroContinuity]
  triangulation := some (PairKey.canonical thermalRise carrierBeat)
  hypothesis := resonance

theorem abstract_lattice_has_29696_candidates : abstractPlans.length = 29696 := by
  native_decide

theorem canonical_plan_is_the_unique_winning_selection :
    winningAbstractPlans = [canonicalPlan] := by
  native_decide

/-! ## Axiom accounting -/

#assert_compiled demo_config_valid
#assert_compiled evidence_route_reaches_theory_decision
#assert_compiled winning_route_publishes
#assert_compiled winning_route_produces_exact_record_and_contribution
#assert_compiled winning_record_preserves_every_archive_and_custody_binding
#assert_compiled publication_without_independent_triangulation_refuses
#assert_compiled chasing_the_false_lead_loses_the_publication_window
#assert_compiled contaminated_lead_cannot_forge_support_or_information
#assert_compiled witnessed_external_carrier_contradiction_is_real
#assert_compiled copied_cross_player_action_refuses
#assert_compiled identical_envelope_replay_refuses
#assert_compiled otherwise_valid_run_at_max_counter_is_refused
#assert_compiled reversing_a_consumed_pair_does_not_create_a_second_triangulation
#assert_compiled forged_custody_origin_is_rejected
#assert_compiled wrong_source_mission_is_rejected
#assert_compiled unarchived_observation_is_rejected
#assert_compiled transferred_same_holder_catalogue_is_well_formed
#assert_compiled same_custodian_cannot_self_triangulate
#assert_compiled abstract_lattice_has_29696_candidates
#assert_compiled canonical_plan_is_the_unique_winning_selection

end Dregg2.Games.PathOfAngels.ArchiveLabDemonstrator
