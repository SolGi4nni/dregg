/-
# Archive Lab — bounded theory-building over exact Field Archive evidence

This is a playable deduction game, not a free-form lore authoring surface.  The
player spends a finite analysis budget screening and testing archived observations,
triangulates independent provenance, resolves a real contradiction, and may publish
one beta research record.  Evidence weights, contamination, information gain and
score are authored data interpreted by this Lean state machine; no action contains a
claimed score, confidence, artifact, or contribution.

Every observation is bound to an exact `FieldArchive.ArchiveEntry`, its receipt key,
source mission, activated content domain, and a custody stamp.  Publication records
the research mission's exact artifact through `applyContribution`.  This module does
not import or expose a curator promotion operation: the result is beta material only.
-/
import Dregg2.Games.PathOfAngels.FieldArchive
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.ArchiveLab

open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.FieldArchive

set_option autoImplicit false

/-! ## Authored evidence catalogue -/

structure HypothesisId where
  value : Nat
deriving DecidableEq, Repr

structure ObservationId where
  value : Nat
deriving DecidableEq, Repr

inductive Bearing where
  | supports (hypothesis : HypothesisId)
  | refutes (hypothesis : HypothesisId)
deriving DecidableEq, Repr

def Bearing.hypothesis : Bearing → HypothesisId
  | .supports hypothesis => hypothesis
  | .refutes hypothesis => hypothesis

inductive EvidenceVerdict where
  | sound
  | contaminated
deriving DecidableEq, Repr

/-- Custody is an authored, exact binding to the archived origin.  Signatures and
transfer authorization live outside this finite game; this object records the
already-admitted holder and transfer sequence which the activated pack names. -/
structure CustodyStamp where
  originKey : ReceiptKey
  holder : Digest32
  transferSequence : Nat
deriving DecidableEq

structure Observation where
  id : ObservationId
  entry : ArchiveEntry
  sourceMission : MissionId
  custody : CustodyStamp
  bearing : Bearing
  /-- Strength `1..4`; zero is rejected by catalogue validation. -/
  weight : Fin 5
  /-- Information value `0..5`, paid only when sound evidence is tested. -/
  information : Fin 6
  verdict : EvidenceVerdict
deriving DecidableEq

structure RawConfig where
  mission : MissionSpec
  sourceMission : MissionId
  /-- Activated, authenticated content supplied by the curator/runtime boundary.
  This game verifies exact membership and every deduction from it; it does not
  replay the `FieldArchive.Acquisition` history which produced the snapshot. -/
  archive : ArchiveState
  hypotheses : List HypothesisId
  observations : List Observation
  allowedCustodians : Finset Digest32
  operationBudget : Nat
  publishSupportFloor : Nat
deriving DecidableEq

def observationValidB (raw : RawConfig) (observation : Observation) : Bool :=
  decide (observation.entry ∈ raw.archive.entries) &&
  decide (observation.entry.originKey = observation.custody.originKey) &&
  decide (observation.sourceMission = raw.sourceMission) &&
  decide (observation.entry.mission.missionId = raw.sourceMission) &&
  decide (observation.entry.artifact.missionId = raw.sourceMission) &&
  decide (observation.entry.federationId = raw.mission.federationId) &&
  decide (observation.entry.contentRoot = raw.mission.contentRoot) &&
  decide (observation.entry.activationDigest = raw.mission.activationDigest) &&
  decide (observation.entry.contentSession = raw.mission.contentSession) &&
  decide (observation.entry.contentEpoch = raw.mission.epoch) &&
  decide (observation.custody.holder ∈ raw.allowedCustodians) &&
  decide (0 < observation.custody.transferSequence) &&
  decide (observation.bearing.hypothesis ∈ raw.hypotheses) &&
  decide (0 < observation.weight.val) &&
  decide (observation.id.value < 16) &&
  decide (observation.bearing.hypothesis.value < 16)

/-- Fourteen unit-cost operations fit exactly in the faithful 32-byte transcript
projection below (one length byte plus fourteen tag/payload pairs). -/
def configValidB (raw : RawConfig) : Bool :=
  decide raw.hypotheses.Nodup &&
  decide (raw.hypotheses ≠ []) &&
  decide (raw.observations.map (·.id) |>.Nodup) &&
  raw.observations.all (observationValidB raw) &&
  decide (0 < raw.operationBudget) &&
  decide (raw.operationBudget ≤ 14) &&
  decide (0 < raw.publishSupportFloor)

structure Config where
  raw : RawConfig
  valid : configValidB raw = true

def observationById? (config : Config) (id : ObservationId) : Option Observation :=
  config.raw.observations.find? (fun observation => observation.id = id)

/-- Catalogue validity turns every referenced observation into an exact archive,
receipt-origin, source-mission, activation-domain, and custody binding. -/
theorem Config.observation_has_exact_authority (config : Config) (observation : Observation)
    (member : observation ∈ config.raw.observations) :
    observation.entry ∈ config.raw.archive.entries ∧
    observation.entry.originKey = observation.custody.originKey ∧
    observation.sourceMission = config.raw.sourceMission ∧
    observation.entry.mission.missionId = config.raw.sourceMission ∧
    observation.entry.artifact.missionId = config.raw.sourceMission ∧
    observation.entry.federationId = config.raw.mission.federationId ∧
    observation.entry.contentRoot = config.raw.mission.contentRoot ∧
    observation.entry.activationDigest = config.raw.mission.activationDigest ∧
    observation.entry.contentSession = config.raw.mission.contentSession ∧
    observation.entry.contentEpoch = config.raw.mission.epoch ∧
    observation.custody.holder ∈ config.raw.allowedCustodians ∧
    0 < observation.custody.transferSequence := by
  have allValid : config.raw.observations.all (observationValidB config.raw) = true := by
    have valid := config.valid
    simp only [configValidB, Bool.and_eq_true] at valid
    tauto
  have valid := (List.all_eq_true.mp allValid) observation member
  simp only [observationValidB, Bool.and_eq_true, decide_eq_true_eq] at valid
  tauto

/-! ## Sequenced play -/

structure SessionKey where
  federationId : Digest32
  contentSession : Digest32
  contentEpoch : EpochId
  missionId : MissionId
  playerKey : Digest32
  playerCounter : Nat
deriving DecidableEq

structure PairKey where
  low : ObservationId
  high : ObservationId
deriving DecidableEq, Repr

def PairKey.canonical (left right : ObservationId) : PairKey :=
  if left.value ≤ right.value then ⟨left, right⟩ else ⟨right, left⟩

inductive Command where
  | screen (observation : ObservationId)
  | test (observation : ObservationId)
  | triangulate (left right : ObservationId)
  | publish (hypothesis : HypothesisId)
deriving DecidableEq, Repr

structure Action where
  session : SessionKey
  sequence : Nat
  command : Command
deriving DecidableEq

structure JudgeContext where
  actorRoot : Digest32
  playerKey : Digest32
  previousPlayerCounter : Nat

/-- The receipt counter must fit the canonical unsigned 64-bit player-counter
domain.  `Nat` arithmetic itself cannot overflow, but a value outside this wire
domain is not an admissible PoA run. -/
def JudgeContext.nextCounterAdmissibleB (context : JudgeContext) : Bool :=
  decide (context.previousPlayerCounter + 1 < PLAYER_COUNTER_MODULUS)

def sessionKey (config : Config) (context : JudgeContext) : SessionKey where
  federationId := config.raw.mission.federationId
  contentSession := config.raw.mission.contentSession
  contentEpoch := config.raw.mission.epoch
  missionId := config.raw.mission.missionId
  playerKey := context.playerKey
  playerCounter := context.previousPlayerCounter + 1

structure State where
  session : SessionKey
  nextSequence : Nat
  operationsSpent : Nat
  screened : Finset ObservationId
  tested : Finset ObservationId
  triangulations : Finset PairKey
  published : Option HypothesisId
deriving DecidableEq

def initialState (config : Config) (context : JudgeContext) : State where
  session := sessionKey config context
  nextSequence := 0
  operationsSpent := 0
  screened := ∅
  tested := ∅
  triangulations := ∅
  published := none

def charged (state : State) : State :=
  { state with
    nextSequence := state.nextSequence + 1
    operationsSpent := state.operationsSpent + 1 }

def testedObservations (config : Config) (state : State) : List Observation :=
  config.raw.observations.filter (fun observation => decide (observation.id ∈ state.tested))

def soundTestedObservations (config : Config) (state : State) : List Observation :=
  (testedObservations config state).filter (fun observation =>
    decide (observation.verdict = .sound))

def supportScore (config : Config) (state : State) (hypothesis : HypothesisId) : Nat :=
  (soundTestedObservations config state).foldl (fun total observation =>
    match observation.bearing with
    | .supports candidate => if candidate = hypothesis then total + observation.weight.val else total
    | .refutes _ => total) 0

def refuteScore (config : Config) (state : State) (hypothesis : HypothesisId) : Nat :=
  (soundTestedObservations config state).foldl (fun total observation =>
    match observation.bearing with
    | .refutes candidate => if candidate = hypothesis then total + observation.weight.val else total
    | .supports _ => total) 0

def informationGain (config : Config) (state : State) : Nat :=
  (soundTestedObservations config state).foldl
      (fun total observation => total + observation.information.val) 0 +
    2 * state.triangulations.card

def pairSupportsHypothesisB (config : Config) (pair : PairKey)
    (hypothesis : HypothesisId) : Bool :=
  match observationById? config pair.low, observationById? config pair.high with
  | some left, some right =>
      decide (left.verdict = .sound) &&
      decide (right.verdict = .sound) &&
      decide (left.bearing = .supports hypothesis) &&
      decide (right.bearing = .supports hypothesis)
  | _, _ => false

def hasIndependentSupportB (config : Config) (state : State)
    (hypothesis : HypothesisId) : Bool :=
  decide ((state.triangulations.filter (fun pair =>
    decide (pair.low ∈ state.tested) &&
    decide (pair.high ∈ state.tested) &&
    (match observationById? config pair.low, observationById? config pair.high with
     | some left, some right =>
         decide (left.entry.originKey ≠ right.entry.originKey) &&
         decide (left.custody.holder ≠ right.custody.holder)
     | _, _ => false) &&
    pairSupportsHypothesisB config pair hypothesis = true)).card > 0)

def alternativesRefutedB (config : Config) (state : State)
    (hypothesis : HypothesisId) : Bool :=
  config.raw.hypotheses.all (fun alternative =>
    if alternative = hypothesis then true
    else decide (supportScore config state alternative < refuteScore config state alternative))

/-- A successful publication must have encountered a live contradiction, not only
accumulated one-sided clues: some rejected alternative had sound support but still
lost to stronger sound refutation. -/
def witnessedContradictionB (config : Config) (state : State)
    (hypothesis : HypothesisId) : Bool :=
  config.raw.hypotheses.any (fun alternative =>
    decide (alternative ≠ hypothesis) &&
    decide (0 < supportScore config state alternative) &&
    decide (supportScore config state alternative < refuteScore config state alternative))

def publishableB (config : Config) (state : State) (hypothesis : HypothesisId) : Bool :=
  decide (hypothesis ∈ config.raw.hypotheses) &&
  decide (config.raw.publishSupportFloor ≤ supportScore config state hypothesis) &&
  decide (refuteScore config state hypothesis = 0) &&
  hasIndependentSupportB config state hypothesis &&
  alternativesRefutedB config state hypothesis &&
  witnessedContradictionB config state hypothesis

def triangulatableB (config : Config) (state : State)
    (leftId rightId : ObservationId) : Bool :=
  match observationById? config leftId, observationById? config rightId with
  | some left, some right =>
      decide (leftId ≠ rightId) &&
      decide (leftId ∈ state.tested) &&
      decide (rightId ∈ state.tested) &&
      decide (left.verdict = .sound) &&
      decide (right.verdict = .sound) &&
      decide (left.entry.originKey ≠ right.entry.originKey) &&
      decide (left.custody.holder ≠ right.custody.holder) &&
      (match left.bearing, right.bearing with
       | .supports leftHypothesis, .supports rightHypothesis =>
           decide (leftHypothesis = rightHypothesis)
       | _, _ => false) &&
      decide (PairKey.canonical leftId rightId ∉ state.triangulations)
  | _, _ => false

/-- Command-local update before the common sequence/cost charge. -/
def commandStep (config : Config) (state : State) : Command → Option State
  | .screen id =>
      match observationById? config id with
      | none => none
      | some _ =>
          if id ∈ state.screened then none
          else some { state with screened := insert id state.screened }
  | .test id =>
      match observationById? config id with
      | none => none
      | some _ =>
          if id ∉ state.screened then none
          else if id ∈ state.tested then none
          else some { state with tested := insert id state.tested }
  | .triangulate left right =>
      if triangulatableB config state left right then
        some { state with
          triangulations := insert (PairKey.canonical left right) state.triangulations }
      else none
  | .publish hypothesis =>
      if publishableB config state hypothesis then
        some { state with published := some hypothesis }
      else none

/-- The rules oracle.  Every command costs one operation.  A wrong session,
wrong sequence, closed state, exhausted budget, duplicate operation, unresolved
provenance relation, or unpublishable theory refuses rather than accepting a no-op. -/
def step (config : Config) (state : State) (action : Action) : Option State :=
  if action.session ≠ state.session then none
  else if action.sequence ≠ state.nextSequence then none
  else if state.published.isSome then none
  else if config.raw.operationBudget ≤ state.operationsSpent then none
  else (commandStep config state action.command).map charged

def replay (config : Config) : State → List Action → Option State
  | state, [] => some state
  | state, action :: actions =>
      match step config state action with
      | none => none
      | some next => replay config next actions

/-! ## Exact research record and beta contribution -/

structure EvidenceUse where
  observationId : ObservationId
  artifact : ArtifactRef
  originKey : ReceiptKey
  sourceMission : MissionId
  custody : CustodyStamp
  bearing : Bearing
  verdict : EvidenceVerdict
  weight : Nat
  information : Nat
deriving DecidableEq

def EvidenceUse.ofObservation (observation : Observation) : EvidenceUse where
  observationId := observation.id
  artifact := observation.entry.artifact
  originKey := observation.entry.originKey
  sourceMission := observation.sourceMission
  custody := observation.custody
  bearing := observation.bearing
  verdict := observation.verdict
  weight := observation.weight.val
  information := observation.information.val

def selectedEvidence (config : Config) (state : State) : List EvidenceUse :=
  (testedObservations config state).map EvidenceUse.ofObservation

theorem selected_evidence_has_exact_archive_source (config : Config) (state : State)
    (used : EvidenceUse) (member : used ∈ selectedEvidence config state) :
    ∃ observation ∈ config.raw.observations,
      observation.id ∈ state.tested ∧
      used = EvidenceUse.ofObservation observation ∧
      observation.entry ∈ config.raw.archive.entries ∧
      used.originKey = observation.entry.originKey ∧
      used.custody.originKey = observation.entry.originKey ∧
      used.sourceMission = config.raw.sourceMission := by
  simp only [selectedEvidence, List.mem_map] at member
  obtain ⟨observation, testedMember, hevidence⟩ := member
  have authoredMember : observation ∈ config.raw.observations := by
    exact (List.mem_filter.mp testedMember).1
  have tested : observation.id ∈ state.tested := by
    exact of_decide_eq_true (List.mem_filter.mp testedMember).2
  have authority := config.observation_has_exact_authority observation authoredMember
  refine ⟨observation, authoredMember, tested, ?_, authority.1, ?_, ?_, ?_⟩
  · exact hevidence.symm
  · rw [← hevidence]
    rfl
  · rw [← hevidence]
    exact authority.2.1.symm
  · rw [← hevidence]
    exact authority.2.2.1

def byte (value : Nat) : Fin 256 := ⟨value % 256, Nat.mod_lt _ (by omega)⟩

def commandTag : Command → Nat
  | .screen _ => 1
  | .test _ => 2
  | .triangulate _ _ => 3
  | .publish _ => 4

def commandPayload : Command → Nat
  | .screen observation => observation.value
  | .test observation => observation.value
  | .triangulate left right => left.value * 16 + right.value
  | .publish hypothesis => hypothesis.value

def commandAt? (actions : List Action) (index : Nat) : Option Command :=
  (actions[index]?).map (·.command)

/-- Faithful for every accepted run: catalogue ids are below 16, the budget is at
most 14, and each command occupies its tag/payload pair.  Session/counter/domain
identity is carried separately by `RunReceipt`. -/
def transcriptDigest (actions : List Action) : Digest32 where
  bytes := List.ofFn (fun index : Fin 32 =>
    if index.val = 0 then byte actions.length
    else
      let offset := index.val - 1
      let commandIndex := offset / 2
      match commandAt? actions commandIndex with
      | none => 0
      | some command =>
          if offset % 2 = 0 then byte (commandTag command)
          else byte (commandPayload command))
  length_eq := by simp

structure ResearchRecord where
  missionId : MissionId
  artifact : ArtifactRef
  session : SessionKey
  hypothesis : HypothesisId
  evidence : List EvidenceUse
  triangulations : Finset PairKey
  support : Nat
  refutation : Nat
  information : Nat
  operationsSpent : Nat
  transcriptDigest : Digest32
deriving DecidableEq

def terminalRecord? (config : Config) (state : State)
    (actions : List Action) : Option ResearchRecord := do
  let hypothesis ← state.published
  some {
    missionId := config.raw.mission.missionId
    artifact := config.raw.mission.artifact
    session := state.session
    hypothesis
    evidence := selectedEvidence config state
    triangulations := state.triangulations
    support := supportScore config state hypothesis
    refutation := refuteScore config state hypothesis
    information := informationGain config state
    operationsSpent := state.operationsSpent
    transcriptDigest := transcriptDigest actions
  }

def rawContribution (record : ResearchRecord) : RawContribution where
  intel := record.information
  supplies := 0
  cohesion := 1
  influence := 0
  score := 10 * record.support + record.information + 5 * record.triangulations.card
  relics := []

structure JudgedRun where
  finalState : State
  record : ResearchRecord
  afterWorld : WorldState
  receipt : RunReceipt

/-- Publication is one transaction: deterministic replay, derived record, derived
bounded contribution, mission admission, exact world application, and receipt. -/
def judge (config : Config) (before : WorldState) (context : JudgeContext)
    (actions : List Action) : Option JudgedRun :=
  if context.nextCounterAdmissibleB then
    match hreplay : replay config (initialState config context) actions with
    | none => none
    | some finalState =>
        match hrecord : terminalRecord? config finalState actions with
        | none => none
        | some record =>
            match hcontribution : validateContribution (rawContribution record) with
            | none => none
            | some contribution =>
                if config.raw.mission.acceptsContribution contribution then
                  match happlied : applyContribution config.raw.mission contribution before with
                  | none => none
                  | some afterWorld => some {
                      finalState
                      record
                      afterWorld
                      receipt := {
                        mission := config.raw.mission
                        federationId := config.raw.mission.federationId
                        contentRoot := config.raw.mission.contentRoot
                        activationDigest := config.raw.mission.activationDigest
                        contentSession := config.raw.mission.contentSession
                        contentEpoch := config.raw.mission.epoch
                        actorRoot := context.actorRoot
                        playerKey := context.playerKey
                        previousPlayerCounter := context.previousPlayerCounter
                        playerCounter := context.previousPlayerCounter + 1
                        runSeed := config.raw.mission.runSeed
                        preWorld := before
                        postWorld := afterWorld
                        contribution
                        transcriptDigest := transcriptDigest actions
                        federation_matches := rfl
                        content_root_matches := rfl
                        activation_matches := rfl
                        content_session_matches := rfl
                        content_epoch_matches := rfl
                        run_seed_matches := rfl
                        player_counter_advances := rfl
                        applied := happlied
                      }
                    }
                else none
  else none

/-! ## General laws -/

theorem step_deterministic (config : Config) (state : State) (action : Action)
    {left right : State} (hleft : step config state action = some left)
    (hright : step config state action = some right) : left = right := by
  rw [hleft] at hright
  exact Option.some.inj hright

theorem replay_nil (config : Config) (state : State) : replay config state [] = some state := rfl

theorem replay_append (config : Config) (state : State) (left right : List Action) :
    replay config state (left ++ right) =
      (replay config state left).bind (fun next => replay config next right) := by
  induction left generalizing state with
  | nil => rfl
  | cons action actions induction =>
      simp only [List.cons_append, replay]
      split <;> simp_all

theorem wrong_session_refuses (config : Config) (state : State) (action : Action)
    (wrong : action.session ≠ state.session) : step config state action = none := by
  simp [step, wrong]

theorem wrong_sequence_refuses (config : Config) (state : State) (action : Action)
    (wrong : action.sequence ≠ state.nextSequence) : step config state action = none := by
  by_cases hs : action.session = state.session
  · simp [step, hs, wrong]
  · simp [step, hs]

theorem closed_state_refuses (config : Config) (state : State) (action : Action)
    (closed : state.published.isSome = true) : step config state action = none := by
  by_cases hs : action.session = state.session
  · by_cases hq : action.sequence = state.nextSequence
    · simp [step, hs, hq, closed]
    · simp [step, hs, hq]
  · simp [step, hs]

theorem exhausted_budget_refuses (config : Config) (state : State) (action : Action)
    (spent : config.raw.operationBudget ≤ state.operationsSpent) :
    step config state action = none := by
  by_cases hs : action.session = state.session
  · by_cases hq : action.sequence = state.nextSequence
    · by_cases hc : state.published.isSome
      · simp [step, hs, hq, hc]
      · simp [step, hs, hq, hc, spent]
    · simp [step, hs, hq]
  · simp [step, hs]

theorem commandStep_preserves_counters (config : Config) (state : State)
    (command : Command) {next : State}
    (accepted : commandStep config state command = some next) :
    next.nextSequence = state.nextSequence ∧
      next.operationsSpent = state.operationsSpent := by
  cases command with
  | screen observation =>
      simp only [commandStep] at accepted
      split at accepted <;> try contradiction
      split at accepted <;> try contradiction
      injection accepted with exact
      rw [← exact]
      exact ⟨rfl, rfl⟩
  | test observation =>
      simp only [commandStep] at accepted
      split at accepted <;> try contradiction
      split at accepted <;> try contradiction
      split at accepted <;> try contradiction
      injection accepted with exact
      rw [← exact]
      exact ⟨rfl, rfl⟩
  | triangulate left right =>
      simp only [commandStep] at accepted
      split at accepted <;> try contradiction
      injection accepted with exact
      rw [← exact]
      exact ⟨rfl, rfl⟩
  | publish hypothesis =>
      simp only [commandStep] at accepted
      split at accepted <;> try contradiction
      injection accepted with exact
      rw [← exact]
      exact ⟨rfl, rfl⟩

theorem accepted_action_advances_sequence_and_cost
    (config : Config) (state : State) (action : Action) {next : State}
    (accepted : step config state action = some next) :
    next.nextSequence = state.nextSequence + 1 ∧
      next.operationsSpent = state.operationsSpent + 1 := by
  unfold step at accepted
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  next =>
    cases hcommand : commandStep config state action.command with
    | none => simp [hcommand] at accepted
    | some provisional =>
        simp only [hcommand, Option.map_some, Option.some.injEq] at accepted
        rw [← accepted]
        have preserved := commandStep_preserves_counters config state action.command hcommand
        simp [charged, preserved.1, preserved.2]

/-- Replaying the identical accepted envelope at its successor fails because its
sequence number has already been consumed. -/
theorem accepted_action_cannot_be_replayed (config : Config) (state : State)
    (action : Action) {next : State} (accepted : step config state action = some next) :
    step config next action = none := by
  have advanced := (accepted_action_advances_sequence_and_cost config state action accepted).1
  have sessionExact : action.session = state.session := by
    by_contra wrong
    rw [wrong_session_refuses config state action wrong] at accepted
    contradiction
  have sequenceExact : action.sequence = state.nextSequence := by
    by_contra wrong
    rw [wrong_sequence_refuses config state action wrong] at accepted
    contradiction
  apply wrong_sequence_refuses
  rw [sequenceExact, advanced]
  omega

theorem terminal_record_names_exact_beta_artifact (config : Config) (state : State)
    (actions : List Action) {record : ResearchRecord}
    (terminal : terminalRecord? config state actions = some record) :
    record.missionId = config.raw.mission.missionId ∧
      record.artifact = config.raw.mission.artifact := by
  unfold terminalRecord? at terminal
  cases hp : state.published with
  | none => simp [hp] at terminal
  | some hypothesis =>
      simp only [hp] at terminal
      injection terminal with exact
      rw [← exact]
      exact ⟨rfl, rfl⟩

theorem judge_some_exact (config : Config) (before : WorldState) (context : JudgeContext)
    (actions : List Action) {run : JudgedRun}
    (accepted : judge config before context actions = some run) :
    replay config (initialState config context) actions = some run.finalState ∧
    terminalRecord? config run.finalState actions = some run.record ∧
    validateContribution (rawContribution run.record) = some run.receipt.contribution ∧
    applyContribution config.raw.mission run.receipt.contribution before = some run.afterWorld ∧
    run.record.artifact = config.raw.mission.artifact ∧
    run.receipt.transcriptDigest = transcriptDigest actions := by
  unfold judge at accepted
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  simp only [Option.some.injEq] at accepted
  subst run
  refine ⟨by assumption, by assumption, by assumption, by assumption, ?_, rfl⟩
  exact (terminal_record_names_exact_beta_artifact config _ actions (by assumption)).2

theorem judge_refuses_exhausted_player_counter (config : Config) (before : WorldState)
    (context : JudgeContext) (actions : List Action)
    (exhausted : PLAYER_COUNTER_MODULUS ≤ context.previousPlayerCounter + 1) :
    judge config before context actions = none := by
  simp [judge, JudgeContext.nextCounterAdmissibleB, Nat.not_lt.mpr exhausted]

theorem judge_records_exact_beta_artifact (config : Config) (before : WorldState)
    (context : JudgeContext) (actions : List Action) {run : JudgedRun}
    (accepted : judge config before context actions = some run) :
    config.raw.mission.artifact ∈ run.afterWorld.betaArtifacts := by
  exact applyContribution_records_exact_artifact (judge_some_exact
    config before context actions accepted).2.2.2.1

theorem judge_contribution_is_not_caller_supplied (config : Config) (before : WorldState)
    (context : JudgeContext) (actions : List Action) {run : JudgedRun}
    (accepted : judge config before context actions = some run) :
    validateContribution (rawContribution run.record) = some run.receipt.contribution :=
  (judge_some_exact config before context actions accepted).2.2.1

#assert_axioms step_deterministic
#assert_axioms Config.observation_has_exact_authority
#assert_axioms selected_evidence_has_exact_archive_source
#assert_axioms replay_nil
#assert_axioms replay_append
#assert_axioms wrong_session_refuses
#assert_axioms wrong_sequence_refuses
#assert_axioms closed_state_refuses
#assert_axioms exhausted_budget_refuses
#assert_axioms commandStep_preserves_counters
#assert_axioms accepted_action_advances_sequence_and_cost
#assert_axioms accepted_action_cannot_be_replayed
#assert_axioms terminal_record_names_exact_beta_artifact
#assert_axioms judge_some_exact
#assert_axioms judge_refuses_exhausted_player_counter
#assert_axioms judge_records_exact_beta_artifact
#assert_axioms judge_contribution_is_not_caller_supplied

end Dregg2.Games.PathOfAngels.ArchiveLab
