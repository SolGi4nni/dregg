/-
# Path of Angels — Signal network judge

This is the first complete internal settlement evaluator for a PoA minigame.  The
node supplies one canonical `NetworkJudgeWire` value.  Lean reconstructs the complete
world, canon, active configuration, finalized carrier, and request; checks that
the configuration is the Signal program emitted by `Emit`; replays exactly one
Signal action through `judgeActive`; applies its closed `GameEffect`; and emits a
canonical successor plus the semantic receipt.

There is intentionally no Rust-shaped alternate judge in this module.  This
function becomes authoritative only when the node adapter replaces caller data
with the persisted active Canon/config and derives `FinalizedCarrier` from the
finalized SignedTurn signer and AIR-bound pre-state root.  It must never be exposed
as a public HTTP oracle accepting caller-authored authority fields.
-/
import Dregg2.Games.PathOfAngels.NetworkJudgeWire

namespace Dregg2.Games.PathOfAngels.NetworkJudge

open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.NetworkJudgeWire

set_option autoImplicit false

/-! ## Exact active Signal projection -/

/-- Rebuild the only Signal configuration this boundary accepts.  The five
authenticated identities remain variable, but every game-semantic field comes
from the Lean emitter: mission/artifact ids, epoch/session/seed, budget, privacy,
ballot, target, reward, and allowed relics. -/
def emittedSignalConfig (config : SignalTriangulation.Config) :
    SignalTriangulation.Config :=
  Emit.signalConfig config.mission.federationId
    config.mission.artifact.sourceDigest config.mission.artifact.contentDigest
    config.mission.contentRoot config.mission.activationDigest

def exactEmittedSignalConfig (config : SignalTriangulation.Config) : Bool :=
  decide (ActiveGame.configClaim (.signal config) =
    ActiveGame.configClaim (.signal (emittedSignalConfig config)))

/-- Cross-object state checks that are not game-judge concerns.  In particular,
the request must pin the state it saw, and world/canon must name the same complete
artifact population.  Strict `<` leaves room for the successor sequence/revision
inside the bounded network format. -/
def preStateChecks (input : SemanticInput) : Bool :=
  exactEmittedSignalConfig input.config &&
  decide (input.request.missionId = input.config.mission.missionId.value) &&
  decide (input.request.expectedWorldSequence = input.world.sequence) &&
  decide (input.request.expectedCanonRevision = input.canon.revision) &&
  decide (input.world = input.canon.world) &&
  decide (input.canon.world.betaArtifacts = input.canon.known) &&
  decide (input.world.sequence < WIRE_NAT_LIMIT) &&
  decide (input.canon.revision < WIRE_NAT_LIMIT)

def activeOf (input : SemanticInput) : ActiveRunState := {
  game := .signal input.config
  federationId := input.canon.federationId
  contentRoot := input.canon.contentRoot
  activationDigest := input.canon.activationDigest
  contentSession := input.canon.contentSession
  contentEpoch := input.canon.contentEpoch
  runSeed := input.config.mission.runSeed
  world := input.canon.world
  playerCounters := input.canon.playerCounters
}

def claimOf (input : SemanticInput) : RunClaim := {
  config := .signal input.config.target input.config.mission input.config.reward
  federationId := input.request.federationId
  contentRoot := input.request.contentRoot
  activationDigest := input.request.activationDigest
  contentSession := input.request.contentSession
  contentEpoch := ⟨input.request.contentEpoch⟩
  runSeed := input.request.runSeed
  actorRoot := input.request.actorRoot
  playerKey := input.request.playerKey
  claimedPreviousPlayerCounter := input.request.previousPlayerCounter
}

def oneSignalAction? (request : SignalRequestWire) :
    Option SignalTriangulation.Action := do
  match request.actions with
  | [wireAction] =>
      let action ← wireAction.toSemantic?
      some (.submit action)
  | _ => none

/-! ## Proof-carrying settlement -/

/-- A successful settlement retains both executable evidence edges: the closed
game registry accepted the run, and Canon accepted the resulting one-shot effect.
The printable receipt is a projection of this evidence, not caller data. -/
structure Settlement where
  active : ActiveRunState
  carrier : FinalizedCarrier
  claim : RunClaim
  submitted : SubmittedRun
  judgedRun : JudgedRun
  judgeAccepted : judgeActive active carrier claim submitted = some judgedRun
  beforeCanon : CanonState
  successorCanon : CanonState
  canonApplied : applyGameEffect (.recordRun judgedRun) beforeCanon = some successorCanon

def Settlement.receipt (settlement : Settlement) : RunReceipt :=
  settlement.judgedRun.receipt

def Settlement.successorWorld (settlement : Settlement) : WorldState :=
  settlement.receipt.postWorld

/-- The complete semantic transition.  Refusal at any stage is `none`; there is
no accepted no-op and no partial Canon write. -/
def settle (input : SemanticInput) : Option Settlement :=
  if preStateChecks input then
    match oneSignalAction? input.request with
    | none => none
    | some action =>
        let active := activeOf input
        let claim := claimOf input
        let submitted : SubmittedRun := .signal [action]
        match hj : judgeActive active input.carrier claim submitted with
        | none => none
        | some judgedRun =>
            match hc : applyGameEffect (.recordRun judgedRun) input.canon with
            | none => none
            | some successorCanon =>
                some {
                  active
                  carrier := input.carrier
                  claim
                  submitted
                  judgedRun
                  judgeAccepted := hj
                  beforeCanon := input.canon
                  successorCanon
                  canonApplied := hc
                }
  else none

theorem Settlement.receipt_applied (settlement : Settlement) :
    applyContribution settlement.receipt.mission settlement.receipt.contribution
      settlement.receipt.preWorld = some settlement.receipt.postWorld :=
  settlement.judgedRun.applied

theorem Settlement.canon_records_receipt (settlement : Settlement) :
    settlement.receipt.mission.artifact ∈ settlement.successorCanon.known :=
  applyGameEffect_records_beta_candidate settlement.canonApplied

theorem Settlement.canon_consumes_receipt (settlement : Settlement) :
    settlement.receipt.key ∈ settlement.successorCanon.consumedRuns :=
  applyGameEffect_consumes_counter settlement.canonApplied

theorem Settlement.counter_advances (settlement : Settlement) :
    (settlement.beforeCanon.playerCounters.lookup settlement.receipt.counterKey).val =
        settlement.receipt.previousPlayerCounter ∧
      (settlement.successorCanon.playerCounters.lookup settlement.receipt.counterKey).val =
        settlement.receipt.playerCounter :=
  applyGameEffect_advances_player_counter settlement.canonApplied

theorem Settlement.successor_world_chained (settlement : Settlement) :
    settlement.successorCanon.world = settlement.successorWorld :=
  (applyGameEffect_chains_world settlement.canonApplied).2

theorem Settlement.replay_refused (settlement : Settlement) :
    applyGameEffect (.recordRun settlement.judgedRun) settlement.successorCanon = none :=
  applyGameEffect_same_counter_replay_refused settlement.canonApplied

/-! ## Canonical network entry point -/

def canonicalOutput? (output : SignalOutputWire) : Option SignalOutputWire :=
  if decodeSignalOutput output.toJson = some output then some output else none

theorem canonicalOutput_sound {output accepted : SignalOutputWire}
    (h : canonicalOutput? output = some accepted) :
    accepted = output ∧ decodeSignalOutput accepted.toJson = some accepted := by
  simp only [canonicalOutput?] at h
  split at h
  · rename_i decoded
    cases h
    exact ⟨rfl, decoded⟩
  · contradiction

def Settlement.toWire? (settlement : Settlement) : Option SignalOutputWire := do
  let successorCanon ← CanonStateWire.ofSemantic? settlement.successorCanon
  canonicalOutput? {
    receipt := SignalReceiptWire.ofSemantic settlement.receipt
    successorWorld := WorldStateWire.ofSemantic settlement.successorWorld
    successorCanon
  }

theorem Settlement.toWire_decodes {settlement : Settlement} {output : SignalOutputWire}
    (h : settlement.toWire? = some output) :
    decodeSignalOutput output.toJson = some output := by
  cases hc : CanonStateWire.ofSemantic? settlement.successorCanon with
  | none => simp [Settlement.toWire?, hc] at h
  | some successorCanon =>
      have accepted : canonicalOutput? {
          receipt := SignalReceiptWire.ofSemantic settlement.receipt
          successorWorld := WorldStateWire.ofSemantic settlement.successorWorld
          successorCanon
        } = some output := by
        simpa [Settlement.toWire?, hc] using h
      exact (canonicalOutput_sound accepted).2

/-- Typed-output form of the gate, useful to state semantic properties without
parsing its own freshly encoded result. -/
def processSignal (bytes : String) : Option SignalOutputWire := do
  let wire ← decodeSignalInput bytes
  let input ← wire.toSemantic?
  let settlement ← settle input
  settlement.toWire?

/-- Internal Signal evaluator.  Decode, semantic reconstruction, exact replay,
Canon transition, and output encoding are one fail-closed composition.  The
authority-origin precondition is described in the module header. -/
def processSignalWire (bytes : String) : Option String :=
  (processSignal bytes).map SignalOutputWire.toJson

/-- **`@[export dregg_poa_signal_judge]`** — the internal evaluator boundary.
`""` is the fail-closed refusal sentinel; every accepted result is the nonempty,
canonical `POA-SIGNAL-OUT-1` JSON emitted by `processSignalWire` itself.

This export authenticates nothing outside the supplied semantic carrier.  A host
must derive that carrier from finalized authority before calling it; in
particular this is not a public oracle for caller-authored state. -/
@[export dregg_poa_signal_judge]
def signalJudgeFFI (bytes : String) : String :=
  (processSignalWire bytes).getD ""

theorem signalJudgeFFI_success_iff {inputBytes outputBytes : String}
    (output_nonempty : outputBytes ≠ "") :
    signalJudgeFFI inputBytes = outputBytes ↔
      processSignalWire inputBytes = some outputBytes := by
  cases processed : processSignalWire inputBytes with
  | none =>
      constructor
      · intro accepted
        have empty : "" = outputBytes := by
          simpa [signalJudgeFFI, processed] using accepted
        exact (output_nonempty empty.symm).elim
      · intro accepted
        contradiction
  | some output =>
      simp [signalJudgeFFI, processed]

theorem processSignal_output_decodes {inputBytes : String} {output : SignalOutputWire}
    (h : processSignal inputBytes = some output) :
    decodeSignalOutput output.toJson = some output := by
  cases hdecode : decodeSignalInput inputBytes with
  | none => simp [processSignal, hdecode] at h
  | some wire =>
      cases hsemantic : wire.toSemantic? with
      | none => simp [processSignal, hdecode, hsemantic] at h
      | some input =>
          cases hsettle : settle input with
          | none => simp [processSignal, hdecode, hsemantic, hsettle] at h
          | some settlement =>
              have hwire : settlement.toWire? = some output := by
                simpa [processSignal, hdecode, hsemantic, hsettle] using h
              exact Settlement.toWire_decodes hwire

theorem processSignalWire_output_is_lean_encoded {inputBytes outputBytes : String}
    (h : processSignalWire inputBytes = some outputBytes) :
    ∃ output, processSignal inputBytes = some output ∧ output.toJson = outputBytes := by
  unfold processSignalWire at h
  cases hp : processSignal inputBytes with
  | none => simp [hp] at h
  | some output =>
      simp [hp] at h
      exact ⟨output, rfl, h⟩

theorem processSignalWire_output_decodes {inputBytes outputBytes : String}
    (h : processSignalWire inputBytes = some outputBytes) :
    ∃ output, decodeSignalOutput outputBytes = some output := by
  obtain ⟨output, processed, encoded⟩ :=
    processSignalWire_output_is_lean_encoded h
  refine ⟨output, ?_⟩
  rw [← encoded]
  exact processSignal_output_decodes processed

/-- Authoritative output verification requires the original input: recompute the
entire strict decode → Signal judge → Canon transition, require byte equality,
then reconstruct the already-matched output for inspection.  Standalone
`decodeSignalOutputSemantic` is intentionally not a substitute for this check. -/
def verifySignalTransition (inputBytes outputBytes : String) : Option SemanticOutput := do
  let expectedBytes ← processSignalWire inputBytes
  if expectedBytes = outputBytes then
    decodeSignalOutputSemantic outputBytes
  else none

/-! ## Genuine inhabitation and fail-closed boundary examples -/

/-- This is the actual emitted Signal puzzle, not an independently assembled
receipt-shaped value.  It traverses strict input decode, semantic reconstruction,
the abstract `JudgedRun` constructor boundary, Canon's world chain, and strict
successor encoding. -/
theorem fixture_processSignalWire_success :
    processSignalWire fixtureInputBytes = some fixtureOutputBytes := by
  native_decide

theorem fixture_signalJudgeFFI_success :
    signalJudgeFFI fixtureInputBytes = fixtureOutputBytes := by
  native_decide

theorem fixture_signalJudgeFFI_malformed_refused :
    signalJudgeFFI (fixtureInputBytes ++ "\n") = "" := by
  native_decide

theorem fixture_verifySignalTransition_success :
    (verifySignalTransition fixtureInputBytes fixtureOutputBytes).isSome = true := by
  native_decide

def incompleteCanonOutputWire : SignalOutputWire := {
  fixtureOutputWire with
  successorCanon := { fixtureSuccessorCanonWire with
    known := []
    consumedRuns := []
    playerCounters := []
    revision := 0 }
}

/-- A well-shaped standalone output is not enough: exact transition verification
rejects the same world paired with a Canon state that omitted settlement effects. -/
theorem fixture_incomplete_canon_output_refused :
    verifySignalTransition fixtureInputBytes incompleteCanonOutputWire.toJson = none := by
  native_decide

def wrongPlayerInputWire : SignalInputWire := {
  fixtureInputWire with
  request := { fixtureInputWire.request with playerKey := fixtureActorRoot }
}

theorem fixture_wrong_player_refused :
    processSignalWire wrongPlayerInputWire.toJson = none := by
  native_decide

def wrongConfigInputWire : SignalInputWire := {
  fixtureInputWire with
  config := { fixtureInputWire.config with
    reward := { fixtureInputWire.config.reward with score := 499 } }
}

theorem fixture_wrong_config_refused :
    processSignalWire wrongConfigInputWire.toJson = none := by
  native_decide

def wrongCurrentCounterInputWire : SignalInputWire := {
  fixtureInputWire with
  carrier := { fixtureInputWire.carrier with currentPlayerCounter := 1 }
  request := { fixtureInputWire.request with previousPlayerCounter := 1 }
}

theorem fixture_wrong_current_counter_refused :
    processSignalWire wrongCurrentCounterInputWire.toJson = none := by
  native_decide

def staleCounterInputWire : SignalInputWire := {
  fixtureInputWire with
  request := { fixtureInputWire.request with previousPlayerCounter := 1 }
}

theorem fixture_stale_counter_refused :
    processSignalWire staleCounterInputWire.toJson = none := by
  native_decide

def wrongActionInputWire : SignalInputWire := {
  fixtureInputWire with
  request := { fixtureInputWire.request with
    actions := [{ low := 0, mid := 0, high := 0 }] }
}

theorem fixture_wrong_action_refused :
    processSignalWire wrongActionInputWire.toJson = none := by
  native_decide

def multipleActionsInputWire : SignalInputWire := {
  fixtureInputWire with
  request := { fixtureInputWire.request with
    actions := [CodeWire.ofSemantic Emit.signalTarget, CodeWire.ofSemantic Emit.signalTarget] }
}

theorem fixture_multiple_actions_refused :
    processSignalWire multipleActionsInputWire.toJson = none := by
  native_decide

def staleRevisionInputWire : SignalInputWire := {
  fixtureInputWire with
  request := { fixtureInputWire.request with expectedCanonRevision := 1 }
}

theorem fixture_stale_revision_refused :
    processSignalWire staleRevisionInputWire.toJson = none := by
  native_decide

/-- Replaying the original counter-zero request against the genuine successor
state fails because Canon now records counter one (and the original receipt key). -/
def replayAgainstSuccessorInputWire : SignalInputWire := {
  fixtureInputWire with
  world := fixturePostWorldWire
  canon := fixtureSuccessorCanonWire
  request := { fixtureInputWire.request with
    expectedWorldSequence := 1
    expectedCanonRevision := 1 }
}

theorem fixture_replay_against_successor_refused :
    processSignalWire replayAgainstSuccessorInputWire.toJson = none := by
  native_decide

#assert_axioms Settlement.receipt_applied
#assert_axioms Settlement.canon_records_receipt
#assert_axioms Settlement.canon_consumes_receipt
#assert_axioms Settlement.counter_advances
#assert_axioms Settlement.successor_world_chained
#assert_axioms Settlement.replay_refused
#assert_axioms canonicalOutput_sound
#assert_axioms Settlement.toWire_decodes
#assert_axioms processSignal_output_decodes
#assert_axioms processSignalWire_output_is_lean_encoded
#assert_axioms processSignalWire_output_decodes
#assert_axioms signalJudgeFFI_success_iff
#assert_compiled fixture_processSignalWire_success
#assert_compiled fixture_signalJudgeFFI_success
#assert_compiled fixture_signalJudgeFFI_malformed_refused
#assert_compiled fixture_verifySignalTransition_success
#assert_compiled fixture_incomplete_canon_output_refused
#assert_compiled fixture_wrong_player_refused
#assert_compiled fixture_wrong_config_refused
#assert_compiled fixture_wrong_current_counter_refused
#assert_compiled fixture_stale_counter_refused
#assert_compiled fixture_wrong_action_refused
#assert_compiled fixture_multiple_actions_refused
#assert_compiled fixture_stale_revision_refused
#assert_compiled fixture_replay_against_successor_refused

end Dregg2.Games.PathOfAngels.NetworkJudge
