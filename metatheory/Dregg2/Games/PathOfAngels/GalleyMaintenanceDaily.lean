/-
# GalleyMaintenanceDaily — one replayable commons maintenance loop

This is deliberately an integration, not a third event kernel.  A daily begins
with the existing `HolderMechanics` ballot surface: public one-player/one-voice,
holder choir votes with the already-proved cap, and zero-world-output holder
sponsorship.  Only a two-chamber pass opens a short ordered maintenance procedure.
Sentyr authors every task, instruction, action, success, and failure content id.

The procedure has one terminal output.  It is not a self-declared contribution:
the reducer accepts an exact `FinalizedRunEventAggregate.Payload` only after that
aggregate's native check re-runs, and only when the judged mission, contribution,
and federation equal this daily's activated specification.  This module never
calls the finalized aggregate reducer or any Canon operation; it merely prepares
one exact, already-checkable payload for the durable aggregate adapter.

All transitions replay through the shared `EventSourcing` module.  Digest
faithfulness and atomic cursor persistence remain its named deployment boundary.
-/
import Dregg2.Games.PathOfAngels.HolderMechanics
import Dregg2.Games.PathOfAngels.FinalizedRunEventAggregate
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.GalleyMaintenanceDaily

open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.NetworkJudgeWire


set_option autoImplicit false

abbrev MAX_PROCEDURE_STEPS : Nat := 8

structure MaintainerId where
  digest : Digest32
deriving DecidableEq

/-- Activated daily content.  The holder policy is retained exactly, and the
output mission is proven to share its federation and epoch. -/
structure DailySpec where
  holderPolicy : HolderMechanics.Policy
  dailyId : Digest32
  taskContentId : Digest32
  instructionContentId : Digest32
  successContentId : Digest32
  failureContentId : Digest32
  procedure : List Digest32
  procedure_nonempty : procedure ≠ []
  procedure_bounded : procedure.length ≤ MAX_PROCEDURE_STEPS
  outputMission : MissionSpec
  outputContribution : Contribution
  output_federation_exact : outputMission.federationId = holderPolicy.federationId
  output_epoch_exact : outputMission.epoch = holderPolicy.contentEpoch
deriving DecidableEq

inductive Phase
  | ballot
  | maintenance
  | completed
  | outputRecorded
deriving DecidableEq, Repr

/-- The constructor is private.  Production reaches maintenance only through a
two-chamber pass; the private post-ballot fixture below cannot leak as an API. -/
structure State where
  private mk ::
  spec : DailySpec
  sequence : Nat
  phase : Phase
  holderState : HolderMechanics.State
  progress : Nat
  performed : List Digest32
  maintainers : Finset MaintainerId
  terminalContentId : Option Digest32
  finalizedOutput : Option FinalizedRunEventAggregate.Payload
  lastParticipantReceipt : Option HolderMechanics.Receipt
deriving DecidableEq

def initialState (spec : DailySpec) : State :=
  ⟨spec, 0, .ballot, HolderMechanics.initialState spec.holderPolicy, 0, [], ∅, none, none, none⟩

inductive Action
  | participant (payload : HolderMechanics.Payload)
  | openMaintenance
  | perform (maintainer : MaintainerId) (actionContentId : Digest32)
  | recordFinalizedOutput (payload : FinalizedRunEventAggregate.Payload)

structure Payload where
  sequence : Nat
  action : Action

/-- Daily ballot events admit only the HolderMechanics surfaces relevant here.
Insurance/side-expedition receipts belong to their own activities, so this daily
cannot smuggle an extra world contribution alongside its one terminal output. -/
def dailyParticipantAllowedB : HolderMechanics.Payload → Bool
  | .publicVote _ => true
  | .holder event =>
      match event.action with
      | .choirVote _ => true
      | .sponsorPublicPlayer _ => true
      | _ => false

/-! ## Exact finalized-run output boundary -/

/-- Checked handoff value.  Its private constructor retains the native aggregate
check and exact authored mission/contribution/federation equalities. -/
structure ExactFinalizedOutput (spec : DailySpec) where
  private mk ::
  raw : FinalizedRunEventAggregate.Payload
  checked : FinalizedRunEventAggregate.CheckedPayload
  checked_exact : FinalizedRunEventAggregate.checkPayload? raw = some checked
  mission_exact : checked.settlement.judgedRun.receipt.mission = spec.outputMission
  contribution_exact :
    checked.settlement.judgedRun.receipt.contribution = spec.outputContribution
  federation_exact : raw.finalized.federationId = spec.holderPolicy.federationId

def checkFinalizedOutput? (spec : DailySpec) (raw : FinalizedRunEventAggregate.Payload) :
    Option (ExactFinalizedOutput spec) :=
  match hchecked : FinalizedRunEventAggregate.checkPayload? raw with
  | none => none
  | some checked =>
      if hmission : checked.settlement.judgedRun.receipt.mission = spec.outputMission then
        if hcontribution :
            checked.settlement.judgedRun.receipt.contribution = spec.outputContribution then
          if hfederation : raw.finalized.federationId = spec.holderPolicy.federationId then
            some ⟨raw, checked, hchecked, hmission, hcontribution, hfederation⟩
          else none
        else none
      else none

theorem ExactFinalizedOutput.exact {spec : DailySpec}
    (output : ExactFinalizedOutput spec) :
    FinalizedRunEventAggregate.checkPayload? output.raw = some output.checked ∧
      output.checked.settlement.judgedRun.receipt.mission = spec.outputMission ∧
      output.checked.settlement.judgedRun.receipt.contribution = spec.outputContribution ∧
      output.raw.finalized.federationId = spec.holderPolicy.federationId :=
  ⟨output.checked_exact, output.mission_exact, output.contribution_exact,
    output.federation_exact⟩

/-! ## One reducer -/

private def participantStep (spec : DailySpec) (state : State) (payload : HolderMechanics.Payload) :
    Option State :=
  if state.phase != .ballot then none
  else if dailyParticipantAllowedB payload != true then none
  else if payload.sequence != state.sequence + 1 then none
  else
    match HolderMechanics.applyPayload spec.holderPolicy state.holderState payload with
    | none => none
    | some (holderState, receipt) =>
        some { state with
          sequence := state.sequence + 1
          holderState
          lastParticipantReceipt := some receipt }

private def openMaintenanceStep (spec : DailySpec) (state : State) : Option State :=
  if state.phase != .ballot then none
  else if HolderMechanics.twoChamberResult spec.holderPolicy state.holderState != .passed then none
  else some { state with sequence := state.sequence + 1, phase := .maintenance }

private def performStep (spec : DailySpec) (state : State) (maintainer : MaintainerId)
    (actionContentId : Digest32) : Option State :=
  if state.phase != .maintenance then none
  else
    match spec.procedure[state.progress]? with
    | none => none
    | some expected =>
        if actionContentId != expected then none
        else
          let progress := state.progress + 1
          let finished := progress = spec.procedure.length
          some { state with
            sequence := state.sequence + 1
            phase := if finished then .completed else .maintenance
            progress
            performed := state.performed ++ [actionContentId]
            maintainers := insert maintainer state.maintainers
            terminalContentId := if finished then some spec.successContentId else none }

private def recordOutputStep (spec : DailySpec) (state : State)
    (raw : FinalizedRunEventAggregate.Payload) : Option State :=
  if state.phase != .completed then none
  else if state.finalizedOutput.isSome then none
  else do
    let output ← checkFinalizedOutput? spec raw
    some { state with
      sequence := state.sequence + 1
      phase := .outputRecorded
      finalizedOutput := some output.raw }

/-- Exact reducer for the daily stream.  Outer stream sequence is checked here;
the participant branch additionally requires the nested HolderMechanics sequence
to be identical, so the ballot prefix has one dense replay order. -/
def reduce (spec : DailySpec) : EventSourcing.Reducer State Payload := fun state payload =>
  if state.spec != spec then none
  else if payload.sequence != state.sequence + 1 then none
  else
    match payload.action with
    | .participant participant => participantStep spec state participant
    | .openMaintenance => openMaintenanceStep spec state
    | .perform maintainer actionContentId =>
        performStep spec state maintainer actionContentId
    | .recordFinalizedOutput raw => recordOutputStep spec state raw

/-- A successful admitted holder choir event is delegated without semantic
translation.  The daily records the exact HolderMechanics successor and receipt. -/
theorem admitted_holder_choir_delegates (spec : DailySpec) (state : State)
    (event : HolderMechanics.HolderEvent) (choice : HolderMechanics.VoteChoice)
    (holderAfter : HolderMechanics.State) (receipt : HolderMechanics.Receipt)
    (hspec : state.spec = spec) (hphase : state.phase = .ballot)
    (hsequence : event.grant.binding.eventSequence = state.sequence + 1)
    (haction : event.action = .choirVote choice)
    (hstep : HolderMechanics.applyPayload spec.holderPolicy state.holderState (.holder event) =
      some (holderAfter, receipt)) :
    reduce spec state {
      sequence := state.sequence + 1
      action := .participant (.holder event)
    } = some { state with
      sequence := state.sequence + 1
      holderState := holderAfter
      lastParticipantReceipt := some receipt } := by
  subst spec
  simp [reduce, participantStep, HolderMechanics.Payload.sequence, hphase, hsequence,
    haction, hstep, dailyParticipantAllowedB]

/-! ## Shared event-sourcing adapter -/

def streamSpec (spec : DailySpec) : EventSourcing.StreamSpec where
  aggregate := {
    namespaceId := spec.holderPolicy.federationId
    kind := 9
    key := spec.dailyId
  }
  version := ⟨1⟩
  genesisHead := spec.holderPolicy.eventGenesisHead

def nextEnvelope (spec : DailySpec) (digests : EventSourcing.DigestBoundary Payload)
    (cursor : EventSourcing.Cursor) (payload : Payload) : EventSourcing.EventEnvelope Payload :=
  let statement : EventSourcing.EventStatement := {
    aggregate := (streamSpec spec).aggregate
    version := (streamSpec spec).version
    sequence := cursor.sequence + 1
    predecessor := cursor.head
    payloadDigest := digests.payloadDigest payload
  }
  { statement, payload, eventDigest := digests.eventDigest statement }

inductive SourcedError
  | projectionCursorSequence
  | payloadStatementSequence
  | eventSource (error : EventSourcing.Error)
deriving DecidableEq, Repr

def applySourcedEvent (spec : DailySpec) (digests : EventSourcing.DigestBoundary Payload)
    (before : EventSourcing.ReplayState State) (event : EventSourcing.EventEnvelope Payload) :
    Except SourcedError (EventSourcing.ReplayState State) := do
  if before.projection.sequence != before.cursor.sequence then
    throw .projectionCursorSequence
  if event.payload.sequence != event.statement.sequence then
    throw .payloadStatementSequence
  match EventSourcing.applyEvent (streamSpec spec) digests (reduce spec) before event with
  | .ok applied => .ok applied.state
  | .error error => .error (.eventSource error)

/-! ## Executable daily and hostile paths -/

private def digestByte (value : Nat) : Digest32 where
  bytes := List.replicate 32 ⟨value % 256, Nat.mod_lt _ (by omega)⟩
  length_eq := by simp

private def fixtureHolderPolicy : HolderMechanics.Policy where
  federationId := fixtureFederationId
  dreggMint := 42
  snapshotSlot := 100
  contentEpoch := fixtureConfig.mission.epoch
  eventId := digestByte 70
  rulesDigest := digestByte 71
  eventGenesisHead := digestByte 72
  sideExpeditionKey := digestByte 73
  choirBonusCap := 3
  insuranceCap := ⟨20, by native_decide⟩
  sponsorCredit := ⟨2, by native_decide⟩
  holderQuorum := 1
  publicQuorum := 1

private def actionA : Digest32 := digestByte 80
private def actionB : Digest32 := digestByte 81
private def actionC : Digest32 := digestByte 82

private def fixtureSpec : DailySpec where
  holderPolicy := fixtureHolderPolicy
  dailyId := digestByte 74
  taskContentId := digestByte 75
  instructionContentId := digestByte 76
  successContentId := digestByte 77
  failureContentId := digestByte 78
  procedure := [actionA, actionB, actionC]
  procedure_nonempty := by decide
  procedure_bounded := by decide
  outputMission := fixtureConfig.mission
  outputContribution := fixtureConfig.reward
  output_federation_exact := rfl
  output_epoch_exact := rfl

private def fixtureCoordinate : FinalizedRunEventAggregate.FinalizedTurnCoordinate where
  federationId := fixtureCarrier.federationId
  commitOrdinal := 7
  turnHash := digestByte 90
  receiptHash := digestByte 91
  eventIndex := 0
  actorRoot := fixtureCarrier.actorRoot
  signer := fixtureCarrier.playerKey

private def fixtureFinalizedPayload : FinalizedRunEventAggregate.Payload where
  finalized := fixtureCoordinate
  judgeInput := fixtureInputBytes
  judgeOutput := fixtureOutputBytes

/-- Test-only post-ballot seed.  Its enclosing `State` constructor and this value
are private; production can reach this phase only through `openMaintenanceStep`. -/
private def fixtureMaintenanceReady : State :=
  ⟨fixtureSpec, 0, .maintenance, HolderMechanics.initialState fixtureHolderPolicy,
    0, [], ∅, none, none, none⟩

private def maintainerA : MaintainerId := ⟨digestByte 92⟩
private def maintainerB : MaintainerId := ⟨digestByte 93⟩

private def fixtureDigests : EventSourcing.DigestBoundary Payload where
  payloadDigest payload := digestByte (100 + payload.sequence)
  eventDigest statement := digestByte (120 + statement.sequence)

private def cursorAfter (spec : DailySpec) (event : EventSourcing.EventEnvelope Payload) : EventSourcing.Cursor where
  aggregate := (streamSpec spec).aggregate
  version := (streamSpec spec).version
  sequence := event.statement.sequence
  head := event.eventDigest

private def stepA : Payload := ⟨1, .perform maintainerA actionA⟩
private def eventA :=
  nextEnvelope fixtureSpec fixtureDigests (streamSpec fixtureSpec).genesisCursor stepA
private def stepB : Payload := ⟨2, .perform maintainerB actionB⟩
private def eventB := nextEnvelope fixtureSpec fixtureDigests
  (cursorAfter fixtureSpec eventA) stepB
private def stepC : Payload := ⟨3, .perform maintainerA actionC⟩
private def eventC := nextEnvelope fixtureSpec fixtureDigests
  (cursorAfter fixtureSpec eventB) stepC
private def outputPayload : Payload := ⟨4, .recordFinalizedOutput fixtureFinalizedPayload⟩
private def outputEvent := nextEnvelope fixtureSpec fixtureDigests
  (cursorAfter fixtureSpec eventC) outputPayload

private def fixtureReplay : Except EventSourcing.Error (EventSourcing.ReplayState State) :=
  EventSourcing.replay (streamSpec fixtureSpec) fixtureDigests (reduce fixtureSpec)
    { cursor := (streamSpec fixtureSpec).genesisCursor,
      projection := fixtureMaintenanceReady }
    [eventA, eventB, eventC, outputEvent]

theorem three_step_daily_replays_to_one_exact_finalized_output :
    fixtureReplay.toOption.map (fun replayed =>
      decide (replayed.projection.phase = .outputRecorded) &&
      decide (replayed.projection.progress = 3) &&
      decide (replayed.projection.performed = [actionA, actionB, actionC]) &&
      decide (replayed.projection.terminalContentId = some fixtureSpec.successContentId) &&
      decide (replayed.projection.finalizedOutput = some fixtureFinalizedPayload) &&
      decide (replayed.projection.finalizedOutput.bind FinalizedRunEventAggregate.checkPayload? |>.isSome)) =
      some true := by
  native_decide

private def fixturePublicPlayer : HolderMechanics.PublicPlayerId := ⟨digestByte 94⟩
private def fixturePublicVote : HolderMechanics.PublicVote where
  federationId := fixtureHolderPolicy.federationId
  contentEpoch := fixtureHolderPolicy.contentEpoch
  eventId := fixtureHolderPolicy.eventId
  rulesDigest := fixtureHolderPolicy.rulesDigest
  sequence := 1
  player := fixturePublicPlayer
  choice := .yes

theorem public_ballot_event_delegates_to_holder_mechanics :
    (reduce fixtureSpec (initialState fixtureSpec)
      ⟨1, .participant (.publicVote fixturePublicVote)⟩).map
        (fun state => state.holderState.publicChamber.yes) = some 1 := by
  native_decide

theorem ballot_cannot_open_with_public_chamber_alone :
    let afterPublic := (reduce fixtureSpec (initialState fixtureSpec)
      ⟨1, .participant (.publicVote fixturePublicVote)⟩).get (by native_decide)
    reduce fixtureSpec afterPublic ⟨2, .openMaintenance⟩ = none := by
  native_decide

theorem wrong_authored_step_is_refused_without_advancing :
    reduce fixtureSpec fixtureMaintenanceReady
      ⟨1, .perform maintainerA actionC⟩ = none := by
  native_decide

theorem premature_finalized_output_is_refused :
    reduce fixtureSpec fixtureMaintenanceReady
      ⟨1, .recordFinalizedOutput fixtureFinalizedPayload⟩ = none := by
  native_decide

private def fixtureCompleted : State :=
  (EventSourcing.replay (streamSpec fixtureSpec) fixtureDigests (reduce fixtureSpec)
    { cursor := (streamSpec fixtureSpec).genesisCursor,
      projection := fixtureMaintenanceReady }
    [eventA, eventB, eventC]).toOption.get (by native_decide) |>.projection

theorem forged_finalized_judge_output_is_refused :
    let hostile := { fixtureFinalizedPayload with judgeOutput := "{}" }
    reduce fixtureSpec fixtureCompleted ⟨4, .recordFinalizedOutput hostile⟩ = none := by
  native_decide

theorem mismatched_contribution_contract_is_refused :
    let altered := { fixtureSpec with outputContribution := Contribution.zero }
    let completedUnderAltered : State :=
      ⟨altered, 3, .completed, HolderMechanics.initialState altered.holderPolicy,
        3, altered.procedure, {maintainerA}, some altered.successContentId, none, none⟩
    reduce altered completedUnderAltered
      ⟨4, .recordFinalizedOutput fixtureFinalizedPayload⟩ = none := by
  native_decide

private def fixtureRecorded : State := fixtureReplay.toOption.get (by native_decide) |>.projection

theorem second_finalized_output_is_refused :
    reduce fixtureSpec fixtureRecorded
      ⟨5, .recordFinalizedOutput fixtureFinalizedPayload⟩ = none := by
  native_decide

theorem participant_event_after_ballot_phase_is_refused :
    let vote := { fixturePublicVote with sequence := 1 }
    reduce fixtureSpec fixtureMaintenanceReady ⟨1, .participant (.publicVote vote)⟩ = none := by
  native_decide

theorem sourced_payload_sequence_mismatch_is_refused :
    let bad := { eventA with payload := ⟨2, .perform maintainerA actionA⟩ }
    applySourcedEvent fixtureSpec fixtureDigests
      { cursor := (streamSpec fixtureSpec).genesisCursor,
        projection := fixtureMaintenanceReady } bad =
      .error .payloadStatementSequence := by
  native_decide

#assert_axioms ExactFinalizedOutput.exact
#assert_axioms admitted_holder_choir_delegates

#assert_compiled three_step_daily_replays_to_one_exact_finalized_output
#assert_compiled public_ballot_event_delegates_to_holder_mechanics
#assert_compiled ballot_cannot_open_with_public_chamber_alone
#assert_compiled wrong_authored_step_is_refused_without_advancing
#assert_compiled premature_finalized_output_is_refused
#assert_compiled forged_finalized_judge_output_is_refused
#assert_compiled mismatched_contribution_contract_is_refused
#assert_compiled second_finalized_output_is_refused
#assert_compiled participant_event_after_ballot_phase_is_refused
#assert_compiled sourced_payload_sequence_mismatch_is_refused

end Dregg2.Games.PathOfAngels.GalleyMaintenanceDaily
