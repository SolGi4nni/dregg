/-
# NightWatchLoopWireExamples — executable boundary and replay fixtures

These fixtures exercise only proof-erased wire values.  In particular, they do
not manufacture a `Policy`, `State`, `Streams`, or any authority admission.
The end-to-end planner remains usable only with those opaque values supplied by
the activated Lean runtime.
-/
import Dregg2.Games.PathOfAngels.NightWatchLoopWire

namespace Dregg2.Games.PathOfAngels.NightWatchLoopWireExamples

open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.NightWatchLoopWire

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

private def digest (value : Nat) : Digest32 where
  bytes := List.replicate 32 ⟨value % 256, Nat.mod_lt _ (by decide)⟩
  length_eq := by simp

private def world : WorldWire :=
  ⟨digest 1, digest 2, digest 3, digest 4, 7⟩

private def otherWorld : WorldWire :=
  ⟨digest 91, digest 92, digest 93, digest 94, 8⟩

private def policy : PolicyViewWire where
  world := world
  content := ⟨digest 5, digest 6⟩
  missionId := 42
  sessionId := digest 7
  missionDay := ⟨7, 19⟩
  watchOfficer := digest 10
  roster := [⟨0, digest 10⟩, ⟨1, digest 11⟩, ⟨2, digest 12⟩, ⟨3, digest 13⟩]

private def flags : FlagsWire := ⟨false, false, false, false, false, false, false⟩

private def stateAt (sequence : Nat) : StateSnapshotWire where
  policy := policy
  sequence := sequence
  phase := 0
  visitKeys := []
  servingCounts := []
  servings := []
  initialServing := none
  maintenanceProgress := 0
  maintenanceActors := []
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
  evidence := []
  flags := flags
  pendingInjury := none
  pendingTerminal := none
  pendingRecoveryServing := none
  outcome := none
  recovery := .fit
  nextWatchEnrollments := []
  debrief := none

private def command : PublicCommandWire := .commitRoute 0

private def coordinate : CoordinateWire where
  world := world
  commitOrdinal := 73
  blockId := digest 20
  turnHash := digest 21
  receiptHash := digest 22
  actorRoot := digest 23
  signer := digest 24

private def head (slot sequence : Nat) (semanticHead : Digest32) : HeadWire where
  world := world
  namespaceId := world.federationId
  kind := 100 + slot
  key := digest (30 + slot)
  version := 1
  sequence := sequence
  head := semanticHead

private def initialHeads : List HeadWire :=
  [head 0 4 (digest 50), head 1 8 (digest 51), head 2 2 (digest 52),
   head 3 5 (digest 53), head 4 9 (digest 54)]

private def trustedCoordinate : EventBatch.FinalizedTurnCoordinate := coordinate.toSemantic
private def trustedHeads : List EventBatch.StreamHead := initialHeads.map HeadWire.toSemantic

private def routeEvent : EventEnvelopeWire :=
  ⟨1, 5, [0], [], [], []⟩

private def indexedRoute : IndexedEventWire where
  eventIndex := 0
  namespaceId := world.federationId
  kind := 101
  key := digest 31
  version := 1
  sequence := 9
  predecessor := digest 51
  payloadDigest := digest 60
  eventDigest := digest 61

private def successorHeads : List HeadWire :=
  [head 0 4 (digest 50), head 1 9 (digest 61), head 2 2 (digest 52),
   head 3 5 (digest 53), head 4 9 (digest 54)]

private def planningInput : PlanningInputWire where
  policy := policy
  state := stateAt 0
  command := command
  coordinate := coordinate
  initialHeads := initialHeads

private def preparedOutput : PreparedOutputWire where
  policy := policy
  beforeSequence := 0
  command := command
  acceptedEvents := [routeEvent]
  after := stateAt 1
  intents := [.semantic routeEvent]
  initialHeads := initialHeads
  batch := ⟨coordinate, [indexedRoute], digest 62⟩
  successorHeads := successorHeads

def publicCommands : List PublicCommandWire :=
  [.claimServing ⟨7, 19⟩ (digest 10) 31,
   .performMaintenance (digest 11) 6,
   .deliverBriefing 2 (digest 12),
   .commitRoute 2,
   .choose 162,
   .extract 1,
   .completeRecoveryCalibration (digest 11),
   .issueDebrief]

theorem every_public_command_roundtrips :
    publicCommands.all (fun value => decodeCommand value.toJson = some value) = true := by
  native_decide

theorem policy_view_roundtrips : decodePolicyView policy.toJson = some policy := by
  native_decide

theorem complete_state_view_roundtrips :
    decodeStateView (stateAt 0).toJson = some (stateAt 0) := by
  native_decide

theorem accepted_event_view_roundtrips :
    decodeEventView routeEvent.toJson = some routeEvent := by
  native_decide

theorem planning_input_roundtrips :
    decodePlanningInput planningInput.toJson = some planningInput := by
  native_decide

theorem prepared_output_roundtrips_with_exact_predecessor_replay :
    decodePreparedOutput preparedOutput.toJson = some preparedOutput := by
  native_decide

theorem public_stable_code_tables_are_exact :
    ([0, 1, 2, 3].map roleOfCode? =
      [some .pathfinder, some .engineer, some .containment, some .quartermaster]) ∧
    ([0, 1, 2].map routeOfCode?).all Option.isSome = true ∧
    ((List.range 7).map maintenanceOfCode?).all Option.isSome = true ∧
    ((List.range 32).map servingOfCode?).all Option.isSome = true ∧
    ([100, 101, 102, 110, 111, 112, 120, 121, 122, 130, 131, 132,
      140, 141, 142, 150, 151, 152, 160, 161, 162].map choiceOfCode?).all Option.isSome = true ∧
    ([0, 1, 2, 3, 4, 5, 100, 101, 102, 103, 104].map terminalOfCode?).all Option.isSome = true := by
  decide

theorem authority_command_tags_are_refused :
    decodeCommand
      "{\"format\":\"POA-NIGHT-WATCH-COMMAND-1\",\"kind\":\"record_handoff\"}" = none ∧
    decodeCommand
      "{\"format\":\"POA-NIGHT-WATCH-COMMAND-1\",\"kind\":\"enroll_next_watch\"}" = none ∧
    decodeCommand
      "{\"format\":\"POA-NIGHT-WATCH-COMMAND-1\",\"kind\":\"activate_draft_settlement\"}" = none := by
  native_decide

theorem unknown_fields_key_reordering_and_whitespace_are_refused :
    decodeCommand
      "{\"format\":\"POA-NIGHT-WATCH-COMMAND-1\",\"kind\":\"issue_debrief\",\"extra\":0}" = none ∧
    decodeCommand
      "{\"kind\":\"issue_debrief\",\"format\":\"POA-NIGHT-WATCH-COMMAND-1\"}" = none ∧
    decodeCommand (PublicCommandWire.toJson .issueDebrief ++ " ") = none := by
  native_decide

theorem explicit_byte_limit_is_enforced :
    decodeCommandWithLimit 1 (PublicCommandWire.toJson .issueDebrief) = none := by
  native_decide

def sparseInvalidChoiceCodes : List Nat :=
  [0, 99, 103, 104, 105, 106, 107, 108, 109,
   113, 114, 115, 116, 117, 118, 119,
   123, 124, 125, 126, 127, 128, 129,
   133, 134, 135, 136, 137, 138, 139,
   143, 144, 145, 146, 147, 148, 149,
   153, 154, 155, 156, 157, 158, 159, 163, 999]

theorem sparse_command_codes_are_refused :
    sparseInvalidChoiceCodes.all (fun code =>
      decodeCommand (PublicCommandWire.toJson (.choose code)) = none) = true := by
  native_decide

private def oversizedBytes : String :=
  String.ofList (List.replicate (WIRE_BYTE_LIMIT + 1) 'x')

theorem default_limits_refuse_oversize_state_input_and_output :
    decodeStateView oversizedBytes = none ∧
    decodePlanningInput oversizedBytes = none ∧
    decodePreparedOutput oversizedBytes = none := by
  native_decide

theorem authority_event_ids_are_refused :
    decodeEventView (⟨1, 4, [], [], [], []⟩ : EventEnvelopeWire).toJson = none ∧
    decodeEventView (⟨1, 12, [], [], [], []⟩ : EventEnvelopeWire).toJson = none ∧
    decodeEventView (⟨1, 13, [], [], [], []⟩ : EventEnvelopeWire).toJson = none := by
  native_decide

theorem every_finalized_coordinate_field_is_checked_against_trusted_input :
    let mutations : List CoordinateWire :=
      [{ coordinate with world := otherWorld },
       { coordinate with commitOrdinal := coordinate.commitOrdinal + 1 },
       { coordinate with blockId := digest 80 },
       { coordinate with turnHash := digest 81 },
       { coordinate with receiptHash := digest 82 },
       { coordinate with actorRoot := digest 83 },
       { coordinate with signer := digest 84 }]
    mutations.all (fun mutated =>
      checkTrustedCarrier trustedCoordinate trustedHeads
        { planningInput with coordinate := mutated } = .error .coordinateSubstitution) = true := by
  native_decide

theorem every_stream_head_field_is_checked_against_trusted_input :
    let original := head 0 4 (digest 50)
    let tails := [head 1 8 (digest 51), head 2 2 (digest 52),
      head 3 5 (digest 53), head 4 9 (digest 54)]
    let mutations : List HeadWire :=
      [{ original with world := otherWorld, namespaceId := otherWorld.federationId },
       { original with namespaceId := digest 85 },
       { original with kind := original.kind + 1 },
       { original with key := digest 86 },
       { original with version := original.version + 1 },
       { original with sequence := original.sequence + 1 },
       { original with head := digest 87 }]
    mutations.all (fun mutated =>
      checkTrustedCarrier trustedCoordinate trustedHeads
        { planningInput with initialHeads := mutated :: tails } = .error .headSubstitution) = true := by
  native_decide

theorem policy_state_substitution_is_refused :
    let altered : PlanningInputWire :=
      { planningInput with policy := { policy with missionId := policy.missionId + 1 } }
    decodePlanningInput altered.toJson = none := by
  native_decide

theorem coordinate_world_substitution_is_refused :
    let altered : PlanningInputWire :=
      { planningInput with coordinate := { coordinate with world := otherWorld } }
    decodePlanningInput altered.toJson = none := by
  native_decide

theorem duplicate_initial_stream_identity_is_refused :
    let altered : PlanningInputWire :=
      { planningInput with initialHeads := [head 0 4 (digest 50), head 0 4 (digest 50),
          head 2 2 (digest 52), head 3 5 (digest 53), head 4 9 (digest 54)] }
    decodePlanningInput altered.toJson = none := by
  native_decide

theorem predecessor_substitution_is_refused :
    let alteredEvent := { indexedRoute with predecessor := digest 99 }
    let altered : PreparedOutputWire :=
      { preparedOutput with batch := { preparedOutput.batch with events := [alteredEvent] } }
    decodePreparedOutput altered.toJson = none := by
  native_decide

theorem non_successor_sequence_is_refused :
    let alteredEvent := { indexedRoute with sequence := indexedRoute.sequence + 1 }
    let altered : PreparedOutputWire :=
      { preparedOutput with batch := { preparedOutput.batch with events := [alteredEvent] } }
    decodePreparedOutput altered.toJson = none := by
  native_decide

theorem successor_head_substitution_is_refused :
    let altered : PreparedOutputWire :=
      { preparedOutput with successorHeads := initialHeads }
    decodePreparedOutput altered.toJson = none := by
  native_decide

theorem intent_stream_substitution_is_refused :
    let wrongStreamEvent : IndexedEventWire := {
      indexedRoute with
      kind := 100
      key := digest 30
      sequence := 5
      predecessor := digest 50
    }
    let wrongSuccessors :=
      [head 0 5 (digest 61), head 1 8 (digest 51), head 2 2 (digest 52),
       head 3 5 (digest 53), head 4 9 (digest 54)]
    let altered : PreparedOutputWire := {
      preparedOutput with
      batch := { preparedOutput.batch with events := [wrongStreamEvent] }
      successorHeads := wrongSuccessors
    }
    decodePreparedOutput altered.toJson = none := by
  native_decide

theorem semantic_event_substitution_is_refused :
    let otherEvent : EventEnvelopeWire := ⟨1, 5, [1], [], [], []⟩
    let altered : PreparedOutputWire :=
      { preparedOutput with acceptedEvents := [otherEvent] }
    decodePreparedOutput altered.toJson = none := by
  native_decide

theorem accepted_event_sequences_are_dense :
    denseEventSequenceB 9 [⟨10, 5, [0], [], [], []⟩,
      ⟨11, 5, [1], [], [], []⟩] = true ∧
    denseEventSequenceB 9 [⟨10, 5, [0], [], [], []⟩,
      ⟨12, 5, [1], [], [], []⟩] = false := by
  native_decide

theorem successful_decoders_preserve_exact_bytes
    {bytes : String} {value : PublicCommandWire}
    (accepted : decodeCommandWithLimit WIRE_BYTE_LIMIT bytes = some value) :
    value.toJson = bytes :=
  decodeCommandWithLimit_reencodes accepted

#assert_compiled every_public_command_roundtrips
#assert_compiled policy_view_roundtrips
#assert_compiled complete_state_view_roundtrips
#assert_compiled accepted_event_view_roundtrips
#assert_compiled planning_input_roundtrips
#assert_compiled prepared_output_roundtrips_with_exact_predecessor_replay
#assert_axioms public_stable_code_tables_are_exact
#assert_compiled authority_command_tags_are_refused
#assert_compiled unknown_fields_key_reordering_and_whitespace_are_refused
#assert_compiled explicit_byte_limit_is_enforced
#assert_compiled sparse_command_codes_are_refused
#assert_compiled default_limits_refuse_oversize_state_input_and_output
#assert_compiled authority_event_ids_are_refused
#assert_compiled every_finalized_coordinate_field_is_checked_against_trusted_input
#assert_compiled every_stream_head_field_is_checked_against_trusted_input
#assert_compiled policy_state_substitution_is_refused
#assert_compiled coordinate_world_substitution_is_refused
#assert_compiled duplicate_initial_stream_identity_is_refused
#assert_compiled predecessor_substitution_is_refused
#assert_compiled non_successor_sequence_is_refused
#assert_compiled successor_head_substitution_is_refused
#assert_compiled intent_stream_substitution_is_refused
#assert_compiled semantic_event_substitution_is_refused
#assert_compiled accepted_event_sequences_are_dense
#assert_axioms successful_decoders_preserve_exact_bytes
#assert_axioms roleOfCode_roleCode
#assert_axioms routeOfCode_code
#assert_axioms maintenanceOfCode_code
#assert_axioms servingOfCode_code
#assert_axioms choiceOfCode_code
#assert_axioms terminalOfCode_code
#assert_axioms phaseOfCode_phaseCode
#assert_axioms preparePublic_refuses_coordinate_substitution
#assert_axioms preparePublic_refuses_head_substitution

end Dregg2.Games.PathOfAngels.NightWatchLoopWireExamples
