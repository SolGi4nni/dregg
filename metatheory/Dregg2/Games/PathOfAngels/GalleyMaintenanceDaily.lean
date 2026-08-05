/-
# GalleyMaintenanceDaily — one replayable commons maintenance loop

This is deliberately an integration, not a third event kernel.  A daily begins
with the existing `HolderMechanics` ballot surface: authoritative public
one-player/one-voice, an exactly-one-voice advisory holder choir, and
zero-world-output holder sponsorship.  Only a public-chamber pass opens a short
ordered maintenance procedure.
Sentyr authors every task, instruction, action, success, and failure content id.

The same stream also carries the galley's shared daily commons.  A bounded set
of authored rotations selects an exact scene and menu by day.  Each player may
visit once; scarce featured servings have capacities, but filling one never
turns later players away—they receive an authored neighborly alternative.  The
small local-service amount is type-capped and is deliberately outside voting,
procedure progress, finalized output, and canon authority.  DREGG sponsorships
are retained as acknowledgements while a parametric theorem proves that their
accepted transition leaves both ballot chambers unchanged.

The procedure has one terminal output.  It is not a self-declared contribution:
the secure surface requires an opaque durable-output admission over the exact
activated full specification and finalized coordinate, then re-runs the native
judge and exact mission/contribution/federation checks.  Exact coordinates and
receipt hashes are first consumed by a separate deployment-global registry CAS;
the output action has no authority constructor without that committed proof.

The raw reducer and event adapter are private.  Production commands retain the
exact activation, prestate, cursor/head, actor, sequence and consume-once
nullifier.  The only public continuation surface starts from an opaque persisted
runtime, uses its deployment-fixed digest boundary, and returns an opaque
candidate that becomes a predecessor only after exact whole-snapshot CAS.
-/
import Dregg2.Games.PathOfAngels.HolderMechanics
import Dregg2.Games.PathOfAngels.FinalizedRunEventAggregate
import Dregg2.Games.PathOfAngels.GalleyCommons
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.GalleyMaintenanceDaily

open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.NetworkJudgeWire


set_option autoImplicit false

abbrev MAX_PROCEDURE_STEPS : Nat := 8
abbrev MAX_ROTATIONS : Nat := 16
abbrev MAX_COMMONS_CHOICES : Nat := 8
abbrev MAX_LOCAL_SERVICE : Nat := 100

structure MaintainerId where
  digest : Digest32
deriving DecidableEq

structure CommonsChoice where
  choiceId : Digest32
  labelContentId : Digest32
  servedContentId : Digest32
  alternativeContentId : Digest32
  capacity : Nat
  localService : Fin (MAX_LOCAL_SERVICE + 1)
deriving DecidableEq

structure CommonsRotation where
  rotationId : Digest32
  sceneContentId : Digest32
  choices : List CommonsChoice
deriving DecidableEq

structure RawCommonsPolicy where
  rotations : List CommonsRotation
deriving DecidableEq

def commonsRotationValidB (rotation : CommonsRotation) : Bool :=
  decide (rotation.choices ≠ []) &&
  decide (rotation.choices.length ≤ MAX_COMMONS_CHOICES) &&
  decide ((rotation.choices.map CommonsChoice.choiceId).Nodup) &&
  rotation.choices.all (fun choice => decide (0 < choice.capacity))

def commonsPolicyValidB (raw : RawCommonsPolicy) : Bool :=
  decide (raw.rotations ≠ []) &&
  decide (raw.rotations.length ≤ MAX_ROTATIONS) &&
  decide ((raw.rotations.map CommonsRotation.rotationId).Nodup) &&
  raw.rotations.all commonsRotationValidB

structure CommonsPolicy where
  raw : RawCommonsPolicy
  valid : commonsPolicyValidB raw = true
deriving DecidableEq

def activeRotation? (policy : CommonsPolicy) (dayIndex : Nat) : Option CommonsRotation :=
  policy.raw.rotations[dayIndex % policy.raw.rotations.length]?

def CommonsRotation.findChoice? (rotation : CommonsRotation) (choiceId : Digest32) :
    Option CommonsChoice :=
  rotation.choices.find? (fun choice => choice.choiceId = choiceId)

structure ChoiceCount where
  rotationId : Digest32
  choiceId : Digest32
  served : Nat
deriving DecidableEq

def choiceCountFor : List ChoiceCount → Digest32 → Digest32 → Nat
  | [], _, _ => 0
  | count :: counts, rotationId, choiceId =>
      if count.rotationId = rotationId ∧ count.choiceId = choiceId then count.served
      else choiceCountFor counts rotationId choiceId

def setChoiceCount : List ChoiceCount → ChoiceCount → List ChoiceCount
  | [], replacement => [replacement]
  | count :: counts, replacement =>
      if count.rotationId = replacement.rotationId ∧ count.choiceId = replacement.choiceId then
        replacement :: counts
      else count :: setChoiceCount counts replacement

inductive CommonsDisposition
  | served
  | neighborlyAlternative
deriving DecidableEq, Repr

structure CommonsOutcome where
  visitor : MaintainerId
  rotationId : Digest32
  choiceId : Digest32
  disposition : CommonsDisposition
  contentId : Digest32
  localService : Fin (MAX_LOCAL_SERVICE + 1)
deriving DecidableEq

/-- Activated daily content.  The holder policy is retained exactly, and the
output mission is proven to share its federation and epoch. -/
structure DailySpec where
  holderPolicy : HolderMechanics.Policy
  activationKey : Digest32
  outputCommitKey : Digest32
  dayIndex : Nat
  commons : CommonsPolicy
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
public-chamber pass; the private post-ballot fixture below cannot leak as an API. -/
structure State where
  private mk ::
  spec : DailySpec
  sequence : Nat
  phase : Phase
  holderState : HolderMechanics.State
  progress : Nat
  performed : List Digest32
  maintainers : Finset MaintainerId
  commonsVisitors : Finset MaintainerId
  choiceCounts : List ChoiceCount
  commonsOutcomes : List CommonsOutcome
  localServiceTotal : Nat
  serviceAcknowledgements : List HolderMechanics.Sponsorship
  terminalContentId : Option Digest32
  finalizedOutput : Option FinalizedRunEventAggregate.Payload
  lastParticipantReceipt : Option HolderMechanics.Receipt
deriving DecidableEq

private def initialState (spec : DailySpec) : State :=
  ⟨spec, 0, .ballot, HolderMechanics.initialState spec.holderPolicy, 0, [], ∅,
    ∅, [], [], 0, [], none, none, none⟩

inductive Action
  | participant (payload : HolderMechanics.Payload)
  | openMaintenance
  | perform (maintainer : MaintainerId) (actionContentId : Digest32)
  | visitCommons (visitor : MaintainerId) (choiceId : Digest32)
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
          serviceAcknowledgements :=
            match receipt.effect with
            | .publicSponsorship sponsorship =>
                state.serviceAcknowledgements ++ [sponsorship]
            | _ => state.serviceAcknowledgements
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

/-- The shared galley is deliberately scarce without being punitive.  Every
visitor receives an authored scene.  Capacity determines only whether it is the
featured serving or the explicitly authored neighborly alternative.  The local
service score is bounded in the type and never enters either voting chamber or
the finalized world contribution. -/
private def visitCommonsStep (spec : DailySpec) (state : State) (visitor : MaintainerId)
    (choiceId : Digest32) : Option State :=
  if state.phase != .maintenance && state.phase != .completed then none
  else if visitor ∈ state.commonsVisitors then none
  else
    match activeRotation? spec.commons spec.dayIndex with
    | none => none
    | some rotation =>
        match rotation.findChoice? choiceId with
        | none => none
        | some choice =>
            let served := choiceCountFor state.choiceCounts rotation.rotationId choice.choiceId
            let hasCapacity := served < choice.capacity
            let disposition :=
              if hasCapacity then CommonsDisposition.served else CommonsDisposition.neighborlyAlternative
            let contentId :=
              if hasCapacity then choice.servedContentId else choice.alternativeContentId
            let localService :=
              if hasCapacity then choice.localService else ⟨0, by omega⟩
            let counts :=
              if hasCapacity then
                setChoiceCount state.choiceCounts {
                  rotationId := rotation.rotationId
                  choiceId := choice.choiceId
                  served := served + 1
                }
              else state.choiceCounts
            let outcome : CommonsOutcome := {
              visitor
              rotationId := rotation.rotationId
              choiceId := choice.choiceId
              disposition
              contentId
              localService
            }
            some { state with
              sequence := state.sequence + 1
              commonsVisitors := insert visitor state.commonsVisitors
              choiceCounts := counts
              commonsOutcomes := state.commonsOutcomes ++ [outcome]
              localServiceTotal := state.localServiceTotal + localService.val }

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
private def reduce (spec : DailySpec) : EventSourcing.Reducer State Payload := fun state payload =>
  if state.spec != spec then none
  else if payload.sequence != state.sequence + 1 then none
  else
    match payload.action with
    | .participant participant => participantStep spec state participant
    | .openMaintenance => openMaintenanceStep spec state
    | .perform maintainer actionContentId =>
        performStep spec state maintainer actionContentId
    | .visitCommons visitor choiceId => visitCommonsStep spec state visitor choiceId
    | .recordFinalizedOutput raw => recordOutputStep spec state raw

/-- Everything capable of changing narrative authority or producing the daily's
world output.  Commons service and sponsorship acknowledgements are intentionally
absent. -/
structure PowerProjection where
  holderChamber : HolderMechanics.ChamberTally
  publicChamber : HolderMechanics.ChamberTally
  phase : Phase
  progress : Nat
  finalizedOutput : Option FinalizedRunEventAggregate.Payload
deriving DecidableEq

def powerProjection (state : State) : PowerProjection where
  holderChamber := state.holderState.holderChamber
  publicChamber := state.holderState.publicChamber
  phase := state.phase
  progress := state.progress
  finalizedOutput := state.finalizedOutput

theorem successful_commons_visit_preserves_power (spec : DailySpec) (before after : State)
    (visitor : MaintainerId) (choiceId : Digest32)
    (hstep : visitCommonsStep spec before visitor choiceId = some after) :
    powerProjection after = powerProjection before := by
  unfold visitCommonsStep at hstep
  split at hstep <;> try contradiction
  split at hstep <;> try contradiction
  split at hstep <;> try contradiction
  split at hstep <;> try contradiction
  injection hstep with hstate
  subst after
  rfl

theorem commons_outcome_local_service_bounded (outcome : CommonsOutcome) :
    outcome.localService.val ≤ MAX_LOCAL_SERVICE :=
  Nat.lt_succ_iff.mp outcome.localService.isLt

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
      serviceAcknowledgements :=
        match receipt.effect with
        | .publicSponsorship sponsorship =>
            state.serviceAcknowledgements ++ [sponsorship]
        | _ => state.serviceAcknowledgements
      lastParticipantReceipt := some receipt } := by
  subst spec
  simp [reduce, participantStep, HolderMechanics.Payload.sequence, hphase, hsequence,
    haction, hstep, dailyParticipantAllowedB]

/-- Sponsorship is service recognition, never a hidden ballot.  This is a
parametric statement over every admitted grant and pre-state, rather than a
fixture: whenever the DREGG sponsorship branch accepts, both chambers are
identical to their prior values. -/
theorem dregg_sponsorship_preserves_chamber_power (policy : HolderMechanics.Policy)
    (before after : HolderMechanics.State) (event : HolderMechanics.HolderEvent)
    (beneficiary : HolderMechanics.PublicPlayerId) (receipt : HolderMechanics.Receipt)
    (haction : event.action = .sponsorPublicPlayer beneficiary)
    (hstep : HolderMechanics.applyPayload policy before (.holder event) = some (after, receipt)) :
    after.holderChamber = before.holderChamber ∧
      after.publicChamber = before.publicChamber := by
  change HolderMechanics.applyHolder policy before event = some (after, receipt) at hstep
  unfold HolderMechanics.applyHolder at hstep
  rw [haction] at hstep
  split at hstep <;> simp_all
  rcases hstep with ⟨_, _, rfl, _⟩
  exact ⟨rfl, rfl⟩

/-! ## The exported game surface — ONE semantics for the Galley daily

⚑ There have been two Galley state machines.  This module's `reduce` (the
ballot / authored procedure / scarce commons / one finalized world output) and
`GalleyMaintenanceDailyRuntime.reduce` (one visit per player against a
`serviceTarget` meter) share exactly one identifier — `MAX_LOCAL_SERVICE` — and
no type, no relation and no theorem.  Only the Runtime one carries `@[export]`,
so the Runtime has been the entire shipped semantics.

**No refinement theorem between them is honest and none will be written here.**
They are not two implementations of one game:

* the Runtime's sponsor transition adds `policy.sponsorService` to the only
  progress variable it has, while this kernel's sponsorship provably moves
  nothing (`dregg_sponsorship_preserves_chamber_power`) — a *contradiction*
  under any relation that maps progress to progress, not a gap;
* a commons visit here pays `choice.localService` or `0` by capacity, and the
  Runtime pays a policy constant with no capacity, no rotation and no
  authored alternative;
* `perform` (an ordered authored procedure) and `recordFinalizedOutput` (the
  world contribution, through a deployment-global coordinate/receipt registry)
  have no Runtime counterpart at all, and the Runtime's four anchor roots have
  no counterpart here.

A simulation would therefore have to be stated over a `CommonsPolicy` carrier
that no authored `DailySpec` and no emitted `PolicyWire` constructs — the
identity-carrier vacuity shape — and, worse, over `ActivatedDaily`, which has
no inhabitant anywhere in the tree (see the tower note below).  A theorem
universally quantified over an uninhabited premise is the apex-vacuity wound,
not a weld.

So the resolution is a cutover, not a bridge: **this reducer becomes the one
semantics, and `GalleyMaintenanceDailyRuntime` becomes a pure wire codec over
the two functions below.**  `NightWatchLoopRuntime` is already exactly that
shape over `NightWatchLoop.execute` — this is the house pattern, one directory
over, not a new architecture.

⚑ What is NOT exportable, and is not merely un-exported.  Everything below
`/-! ## Opaque activation …-/` is a capability and CAS tower with **no
inhabitant at any level**, measured against HEAD:

* `HostInitializer.mk` is private and has **zero construction sites in the
  repository** — not even a fixture — so `provisionCapabilities` and
  `GalleyCommons.provisionDeployment` are uncallable, and `ActivatedDaily`,
  `DailyDeploymentSnapshot`, `AdmittedDailyCommand` and `PersistedDailyRuntime`
  are empty outside this file's private fixtures;
* `DailyPersistenceCASContract`, `OutputRegistryPersistenceContract` and
  `GalleyCommons.PersistenceCASContract` are **never constructed anywhere**,
  and neither is any `DailyCanonicalSerializer` / `CanonicalSerializer`, so
  `faithful` is never discharged;
* consequently `PersistedDailyTransition.same_successor`, every
  `revisionZero_same_genesis`, every `deployment_scoped` and every
  `same_root` is `∀ persistence, …` over a record type with no value.

They also *cannot* be given one across the FFI: `loadedAt`, `createGenesis`,
`rootedAt` and `compareAndSwap` are `Prop`-valued host predicates, and a
`String → String` export cannot receive a `Prop`.  The durability, CAS,
world-activation audit and receipt resolution these model are already done, for
real and with independent re-checks at five hops, in `persist/`.  The tower is
therefore dead weight to be deleted by the cutover lane, not a gate to be
opened — and the two boundary modules' privacy theorems are, read correctly,
the machine-checked certificate that nothing can get in.

Publishing the two functions below does **not** widen the reachable state set.
`State.mk`, `initialState` and all five `*Step` functions stay private
(`GalleyMaintenanceDailyBoundary`), so the only `State` an importer can name is
`genesisState spec` and the only way to move is `step`.  In particular no caller
can start a daily already in `.maintenance`: every route to that phase runs
`openMaintenanceStep`, which refuses unless `twoChamberResult = .passed`.  The
refutation to watch is the boundary module: make `State.mk`, `initialState` or
`fixtureMaintenanceReady` public and `raw_replay_surface_is_private` /
`daily_state_constructor_is_private` / `post_ballot_fixture_is_private` go red. -/

/-- The one public entrance to a daily.  Ballot phase, empty board. -/
def genesisState (spec : DailySpec) : State := initialState spec

/-- The exported transition.  Definitionally `reduce`; there is no second
reducer, and a codec layer must call this rather than restate it. -/
def step (spec : DailySpec) (state : State) (payload : Payload) : Option State :=
  reduce spec state payload

theorem step_is_reduce (spec : DailySpec) (state : State) (payload : Payload) :
    step spec state payload = reduce spec state payload := rfl

theorem genesisState_is_ballot (spec : DailySpec) :
    (genesisState spec).phase = .ballot ∧ (genesisState spec).sequence = 0 ∧
      (genesisState spec).progress = 0 ∧ (genesisState spec).performed = [] ∧
      (genesisState spec).terminalContentId = none ∧
      (genesisState spec).finalizedOutput = none :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem genesisState_carries_its_spec (spec : DailySpec) :
    (genesisState spec).spec = spec := rfl

/-! ## Shared event-sourcing adapter -/

def streamSpec (spec : DailySpec) : EventSourcing.StreamSpec where
  aggregate := {
    namespaceId := spec.holderPolicy.federationId
    kind := 9
    key := spec.dailyId
  }
  version := ⟨1⟩
  genesisHead := spec.holderPolicy.eventGenesisHead

private def nextEnvelope (spec : DailySpec) (digests : EventSourcing.DigestBoundary Payload)
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

private def applySourcedEvent (spec : DailySpec) (digests : EventSourcing.DigestBoundary Payload)
    (before : EventSourcing.ReplayState State) (event : EventSourcing.EventEnvelope Payload) :
    Except SourcedError (EventSourcing.ReplayState State) := do
  if before.projection.sequence != before.cursor.sequence then
    throw .projectionCursorSequence
  if event.payload.sequence != event.statement.sequence then
    throw .payloadStatementSequence
  match EventSourcing.applyEvent (streamSpec spec) digests (reduce spec) before event with
  | .ok applied => .ok applied.state
  | .error error => .error (.eventSource error)

/-! ## Opaque activation, exact command admission, and durable continuation -/

structure DailyActivationProvenance where
  private mk ::
  tokenDigest : Digest32
deriving DecidableEq

structure OutputCommitProvenance where
  private mk ::
  tokenDigest : Digest32
deriving DecidableEq

structure DailyDetachedSignature where
  bytes : List (Fin 256)
deriving DecidableEq

structure CanonicalActivationTranscript where
  deploymentId : Digest32
  genesisHead : Digest32
  trustedActivationKey : Digest32
  spec : DailySpec
  provenance : DailyActivationProvenance
deriving DecidableEq

/-- Exact full-spec activation.  Importers cannot construct it from a raw
`DailySpec`; the deployment adapter must verify the entire structural
transcript. -/
structure ActivatedDaily where
  private mk ::
  deploymentId : Digest32
  expectedDeploymentId : Digest32
  deployment_exact : deploymentId = expectedDeploymentId
  genesisHead : Digest32
  trustedActivationKey : Digest32
  spec : DailySpec
  trusted_key_exact : trustedActivationKey = spec.activationKey
  provenance : DailyActivationProvenance
  transcript : CanonicalActivationTranscript
  transcript_exact : transcript = {
    deploymentId, genesisHead, trustedActivationKey, spec, provenance }

theorem ActivatedDaily.exact (activation : ActivatedDaily) :
    activation.transcript = {
      deploymentId := activation.deploymentId
      genesisHead := activation.genesisHead
      trustedActivationKey := activation.trustedActivationKey
      spec := activation.spec
      provenance := activation.provenance
    } := activation.transcript_exact

structure DailyActivationOracle where
  oracleId : Digest32
  verifyActivation : Digest32 → CanonicalActivationTranscript → DailyDetachedSignature → Bool

structure DailyActivationCapability (oracle : DailyActivationOracle) where
  private mk ::
  provenance : DailyActivationProvenance
  expectedDeploymentId : Digest32
  trustedActivationKey : Digest32

inductive DailyActivationRefusal where
  | invalidSignature
  | wrongGenesisHead
  | wrongDeployment
  | untrustedActivationKey
deriving DecidableEq, Repr

def admitDailyActivation (oracle : DailyActivationOracle)
    (cap : DailyActivationCapability oracle) (deploymentId genesisHead : Digest32)
    (spec : DailySpec) (signature : DailyDetachedSignature) :
    Except DailyActivationRefusal ActivatedDaily :=
  if hdeployment : deploymentId = cap.expectedDeploymentId then
    if hkey : spec.activationKey = cap.trustedActivationKey then
      if genesisHead ≠ (streamSpec spec).genesisHead then .error .wrongGenesisHead
      else
    let transcript : CanonicalActivationTranscript :=
      { deploymentId, genesisHead, trustedActivationKey := cap.trustedActivationKey,
        spec, provenance := cap.provenance }
    if oracle.verifyActivation cap.trustedActivationKey transcript signature then
      .ok ⟨deploymentId, cap.expectedDeploymentId, hdeployment, genesisHead,
        cap.trustedActivationKey, spec, hkey.symm, cap.provenance, transcript, rfl⟩
    else .error .invalidSignature
    else .error .untrustedActivationKey
  else .error .wrongDeployment

theorem ActivatedDaily.cap_pins_deployment_and_key (activation : ActivatedDaily) :
    activation.deploymentId = activation.expectedDeploymentId ∧
      activation.trustedActivationKey = activation.spec.activationKey :=
  ⟨activation.deployment_exact, activation.trusted_key_exact⟩

def initialActivatedState (activation : ActivatedDaily) : State :=
  initialState activation.spec

structure DailyDeploymentSnapshot where
  private mk ::
  revision : Nat
  activation : ActivatedDaily
  replay : EventSourcing.ReplayState State
  spentActionNullifiers : Finset Digest32

/-- Canonical revision-zero daily snapshot for an exact admitted activation. -/
def dailyGenesisSnapshot (activation : ActivatedDaily) : DailyDeploymentSnapshot :=
  ⟨0, activation,
    ⟨(streamSpec activation.spec).genesisCursor, initialActivatedState activation⟩, ∅⟩

structure CanonicalOutputCommitTranscript where
  activation : CanonicalActivationTranscript
  outputProvenance : OutputCommitProvenance
  payload : FinalizedRunEventAggregate.Payload
deriving DecidableEq

structure DailyOutputCommitOracle where
  oracleId : Digest32
  verifyCommittedOutput :
    Digest32 → CanonicalOutputCommitTranscript → DailyDetachedSignature → Bool

structure DailyOutputCommitCapability (oracle : DailyOutputCommitOracle) where
  private mk ::
  provenance : OutputCommitProvenance

/-- Admission from the durable finalized-turn store.  Besides that adapter's
signature, this retains the native judge check and the exact activated daily
mission/contribution contract. -/
structure AdmittedDurableOutput (activation : ActivatedDaily)
    (raw : FinalizedRunEventAggregate.Payload) where
  private mk ::
  provenance : OutputCommitProvenance
  checked : ExactFinalizedOutput activation.spec
  transcript : CanonicalOutputCommitTranscript
  transcript_exact : transcript = {
    activation := activation.transcript
    outputProvenance := provenance
    payload := raw
  }

theorem AdmittedDurableOutput.exact {activation : ActivatedDaily}
    {raw : FinalizedRunEventAggregate.Payload}
    (admission : AdmittedDurableOutput activation raw) :
    admission.transcript = {
      activation := activation.transcript
      outputProvenance := admission.provenance
      payload := raw
    } := admission.transcript_exact

inductive DailyOutputRefusal where
  | wrongDailyContract
  | invalidCommitSignature
deriving DecidableEq, Repr

def admitDurableOutput (oracle : DailyOutputCommitOracle)
    (cap : DailyOutputCommitCapability oracle) (activation : ActivatedDaily)
    (raw : FinalizedRunEventAggregate.Payload) (signature : DailyDetachedSignature) :
    Except DailyOutputRefusal (AdmittedDurableOutput activation raw) :=
  match checkFinalizedOutput? activation.spec raw with
  | none => .error .wrongDailyContract
  | some checked =>
      let transcript : CanonicalOutputCommitTranscript :=
        { activation := activation.transcript, outputProvenance := cap.provenance, payload := raw }
      if oracle.verifyCommittedOutput activation.spec.outputCommitKey transcript signature then
        .ok ⟨cap.provenance, checked, transcript, rfl⟩
      else .error .invalidCommitSignature

/-! ### Deployment-global finalized-output nullifier registry -/

/-- One registry is keyed by deployment, not by daily activation.  Its revision
and both nullifier sets are independently persisted/CASed by the output adapter. -/
structure OutputRegistryState where
  private mk ::
  deploymentId : Digest32
  revision : Nat
  consumedCoordinates : Finset FinalizedRunEventAggregate.FinalizedTurnCoordinate
  consumedReceiptHashes : Finset Digest32
deriving DecidableEq

/-- The only revision-zero registry value exported by the module. -/
def outputRegistryGenesisState (deploymentId : Digest32) : OutputRegistryState :=
  ⟨deploymentId, 0, ∅, ∅⟩

inductive OutputRegistryRefusal where
  | wrongDeployment
  | coordinateReplay
  | receiptReplay
  | loadDeployment
  | commitDeployment
deriving DecidableEq, Repr

structure OutputRegistryCandidate (activation : ActivatedDaily)
    (raw : FinalizedRunEventAggregate.Payload) (before : OutputRegistryState) where
  private mk ::
  after : OutputRegistryState
  deployment_exact : before.deploymentId = activation.deploymentId
  after_exact : after = {
    deploymentId := before.deploymentId
    revision := before.revision + 1
    consumedCoordinates := insert raw.finalized before.consumedCoordinates
    consumedReceiptHashes := insert raw.finalized.receiptHash before.consumedReceiptHashes
  }

def proposeOutputConsumption (before : OutputRegistryState) (activation : ActivatedDaily)
    (raw : FinalizedRunEventAggregate.Payload)
    (_admission : AdmittedDurableOutput activation raw) :
    Except OutputRegistryRefusal (OutputRegistryCandidate activation raw before) :=
  if hdeployment : before.deploymentId = activation.deploymentId then
    if raw.finalized ∈ before.consumedCoordinates then .error .coordinateReplay
    else if raw.finalized.receiptHash ∈ before.consumedReceiptHashes then .error .receiptReplay
    else .ok ⟨{
      deploymentId := before.deploymentId
      revision := before.revision + 1
      consumedCoordinates := insert raw.finalized before.consumedCoordinates
      consumedReceiptHashes := insert raw.finalized.receiptHash before.consumedReceiptHashes
    }, hdeployment, rfl⟩
  else .error .wrongDeployment

/-- Proof that the deployment-global registry, rather than one daily snapshot,
atomically consumed this coordinate and receipt hash.  The constructor is private
and the sole public producer below requires an exact registry CAS receipt. -/
structure ConsumedDurableOutput (activation : ActivatedDaily)
    (raw : FinalizedRunEventAggregate.Payload) where
  private mk ::
  before : OutputRegistryState
  after : OutputRegistryState
  exact : after = {
    deploymentId := before.deploymentId
    revision := before.revision + 1
    consumedCoordinates := insert raw.finalized before.consumedCoordinates
    consumedReceiptHashes := insert raw.finalized.receiptHash before.consumedReceiptHashes
  }
  deployment_exact : before.deploymentId = activation.deploymentId

/-- Ordinary actions need no finalized-output witness.  The output action has
no constructor without the globally consumed durable-coordinate proof above. -/
inductive ActionAuthority (activation : ActivatedDaily) : Action → Type where
  | participant (payload : HolderMechanics.Payload) :
      ActionAuthority activation (.participant payload)
  | openMaintenance : ActionAuthority activation .openMaintenance
  | perform (maintainer : MaintainerId) (contentId : Digest32) :
      ActionAuthority activation (.perform maintainer contentId)
  | visitCommons (visitor : MaintainerId) (choiceId : Digest32) :
      ActionAuthority activation (.visitCommons visitor choiceId)
  | recordFinalizedOutput (raw : FinalizedRunEventAggregate.Payload)
      (consumed : ConsumedDurableOutput activation raw) :
      ActionAuthority activation (.recordFinalizedOutput raw)

def actionActor (spec : DailySpec) : Action → Digest32
  | .participant (.holder event) => event.player.digest
  | .participant (.publicVote vote) => vote.player.digest
  | .openMaintenance => spec.activationKey
  | .perform maintainer _ => maintainer.digest
  | .visitCommons visitor _ => visitor.digest
  | .recordFinalizedOutput _ => spec.activationKey

structure CanonicalDailyCommandTranscript where
  storeRevision : Nat
  activation : CanonicalActivationTranscript
  beforeCursor : EventSourcing.Cursor
  beforeState : State
  spentActionNullifiers : Finset Digest32
  event : EventSourcing.EventEnvelope Payload
  actor : Digest32
  nullifier : Digest32

structure DailyCommandOracle where
  oracleId : Digest32
  verifyCommand : Digest32 → CanonicalDailyCommandTranscript → DailyDetachedSignature → Bool

structure DailyCommandCapability (oracle : DailyCommandOracle) where
  private mk ::
  provenance : DailyActivationProvenance

structure AdmittedDailyCommand (before : DailyDeploymentSnapshot)
    (event : EventSourcing.EventEnvelope Payload) where
  private mk ::
  actor : Digest32
  nullifier : Digest32
  actionAuthority : ActionAuthority before.activation event.payload.action
  transcript : CanonicalDailyCommandTranscript
  transcript_exact : transcript = {
    storeRevision := before.revision
    activation := before.activation.transcript
    beforeCursor := before.replay.cursor
    beforeState := before.replay.projection
    spentActionNullifiers := before.spentActionNullifiers
    event
    actor
    nullifier
  }

theorem AdmittedDailyCommand.exact {before : DailyDeploymentSnapshot}
    {event : EventSourcing.EventEnvelope Payload}
    (command : AdmittedDailyCommand before event) :
    command.transcript = {
      storeRevision := before.revision
      activation := before.activation.transcript
      beforeCursor := before.replay.cursor
      beforeState := before.replay.projection
      spentActionNullifiers := before.spentActionNullifiers
      event
      actor := command.actor
      nullifier := command.nullifier
    } := command.transcript_exact

inductive DailyCommandRefusal where
  | activationProvenance
  | actorMismatch
  | staleSequence
  | staleHead
  | nullifierReplay
  | invalidSignature
deriving DecidableEq, Repr

def admitDailyCommand (oracle : DailyCommandOracle)
    (cap : DailyCommandCapability oracle) (before : DailyDeploymentSnapshot)
    (event : EventSourcing.EventEnvelope Payload) (actor nullifier : Digest32)
    (actionAuthority : ActionAuthority before.activation event.payload.action)
    (signature : DailyDetachedSignature) :
    Except DailyCommandRefusal (AdmittedDailyCommand before event) :=
  if cap.provenance ≠ before.activation.provenance then .error .activationProvenance
  else if actor ≠ actionActor before.activation.spec event.payload.action then .error .actorMismatch
  else if event.payload.sequence ≠ before.replay.cursor.sequence + 1 ∨
      event.statement.sequence ≠ before.replay.cursor.sequence + 1 then
    .error .staleSequence
  else if event.statement.predecessor ≠ before.replay.cursor.head then .error .staleHead
  else if nullifier ∈ before.spentActionNullifiers then .error .nullifierReplay
  else
    let transcript : CanonicalDailyCommandTranscript := {
      storeRevision := before.revision
      activation := before.activation.transcript
      beforeCursor := before.replay.cursor
      beforeState := before.replay.projection
      spentActionNullifiers := before.spentActionNullifiers
      event
      actor
      nullifier
    }
    if oracle.verifyCommand actor transcript signature then
      .ok ⟨actor, nullifier, actionAuthority, transcript, rfl⟩
    else .error .invalidSignature

inductive SecureDailyRefusal where
  | eventSource (error : SourcedError)
deriving DecidableEq, Repr

/-- Pure candidate only.  The result type is opaque and is not accepted as a
predecessor by this function or by command admission. -/
structure DailyTransitionCandidate (before : DailyDeploymentSnapshot)
    (event : EventSourcing.EventEnvelope Payload) where
  private mk ::
  after : DailyDeploymentSnapshot
  activation_exact : after.activation = before.activation

private def proposeDaily (digests : EventSourcing.DigestBoundary Payload)
    (before : DailyDeploymentSnapshot) (event : EventSourcing.EventEnvelope Payload)
    (command : AdmittedDailyCommand before event) :
    Except SecureDailyRefusal (DailyTransitionCandidate before event) := do
  let replay ← match applySourcedEvent before.activation.spec digests before.replay event with
    | .ok replay => .ok replay
    | .error error => .error (.eventSource error)
  .ok ⟨{
    revision := before.revision + 1
    activation := before.activation
    replay
    spentActionNullifiers := insert command.nullifier before.spentActionNullifiers
  }, rfl⟩

abbrev DailyCanonicalBytes := List (Fin 256)

structure DailyCanonicalSerializer (α : Type) where
  encode : α → DailyCanonicalBytes
  faithful : Function.Injective encode

structure OutputRegistryPersistenceContract where
  serializer : DailyCanonicalSerializer OutputRegistryState
  hashAlgorithmId : Digest32
  storeKindId : Digest32
  realHash : DailyCanonicalBytes → Digest32
  loadedAt : Nat → Digest32 → DailyCanonicalBytes → Prop
  createGenesis : Digest32 → Digest32 → DailyCanonicalBytes → Prop
  rootedAt : Digest32 → Nat → Digest32 → DailyCanonicalBytes → Prop
  compareAndSwap : Digest32 → Nat → Digest32 → Nat → DailyCanonicalBytes → Prop
  genesisRooted : ∀ {deploymentId root : Digest32} {bytes : DailyCanonicalBytes},
    createGenesis deploymentId root bytes → rootedAt deploymentId 0 root bytes
  rootedZeroWasGenesis : ∀ {deploymentId root : Digest32} {bytes : DailyCanonicalBytes},
    rootedAt deploymentId 0 root bytes → createGenesis deploymentId root bytes
  genesisUnique : ∀ {deploymentId leftRoot rightRoot : Digest32}
      {left right : DailyCanonicalBytes},
    createGenesis deploymentId leftRoot left →
    createGenesis deploymentId rightRoot right →
    leftRoot = rightRoot ∧ left = right
  casPreservesRoot : ∀ {deploymentId : Digest32} {beforeRevision : Nat}
      {beforeRoot : Digest32} {beforeBytes : DailyCanonicalBytes}
      {afterRevision : Nat} {afterBytes : DailyCanonicalBytes},
    rootedAt deploymentId beforeRevision beforeRoot beforeBytes →
    compareAndSwap deploymentId beforeRevision beforeRoot afterRevision afterBytes →
    rootedAt deploymentId afterRevision
      (realHash (hashAlgorithmId.bytes ++ storeKindId.bytes ++ afterBytes)) afterBytes
  singleWinner : ∀ {deploymentId : Digest32} {expectedRevision : Nat} {expected : Digest32}
      {leftRevision rightRevision : Nat} {left right : DailyCanonicalBytes},
    compareAndSwap deploymentId expectedRevision expected leftRevision left →
    compareAndSwap deploymentId expectedRevision expected rightRevision right →
    leftRevision = rightRevision ∧ left = right

def outputRegistryIdentity (persistence : OutputRegistryPersistenceContract)
    (state : OutputRegistryState) : Digest32 :=
  persistence.realHash
    (persistence.hashAlgorithmId.bytes ++ persistence.storeKindId.bytes ++
      persistence.serializer.encode state)

structure OutputRegistryPersistenceCapability
    (persistence : OutputRegistryPersistenceContract) where
  private mk ::
  expectedDeploymentId : Digest32

structure OutputRegistryGenesisCapability
    (persistence : OutputRegistryPersistenceContract) where
  private mk ::
  expectedDeploymentId : Digest32

/-- Unique canonical output-registry root created atomically for one deployment. -/
structure OutputRegistryGenesisCertificate
    (persistence : OutputRegistryPersistenceContract) where
  private mk ::
  deploymentId : Digest32
  state : OutputRegistryState
  canonical : state = outputRegistryGenesisState deploymentId
  created : persistence.createGenesis deploymentId
    (outputRegistryIdentity persistence state) (persistence.serializer.encode state)
  rooted : persistence.rootedAt deploymentId state.revision
    (outputRegistryIdentity persistence state) (persistence.serializer.encode state)

def bootstrapOutputRegistry {persistence : OutputRegistryPersistenceContract}
    (cap : OutputRegistryGenesisCapability persistence)
    (created : persistence.createGenesis cap.expectedDeploymentId
      (outputRegistryIdentity persistence
        (outputRegistryGenesisState cap.expectedDeploymentId))
      (persistence.serializer.encode
        (outputRegistryGenesisState cap.expectedDeploymentId))) :
    OutputRegistryGenesisCertificate persistence :=
  ⟨cap.expectedDeploymentId, outputRegistryGenesisState cap.expectedDeploymentId,
    rfl, created, persistence.genesisRooted created⟩

structure DurableOutputRegistryLoad (persistence : OutputRegistryPersistenceContract)
    (state : OutputRegistryState) where
  private mk ::
  expectedDeploymentId : Digest32
  included : persistence.loadedAt state.revision
    (outputRegistryIdentity persistence state) (persistence.serializer.encode state)
  rooted : persistence.rootedAt expectedDeploymentId state.revision
    (outputRegistryIdentity persistence state) (persistence.serializer.encode state)

def admitDurableOutputRegistryLoad {persistence : OutputRegistryPersistenceContract}
    (cap : OutputRegistryPersistenceCapability persistence) (state : OutputRegistryState)
    (included : persistence.loadedAt state.revision (outputRegistryIdentity persistence state)
      (persistence.serializer.encode state))
    (rooted : persistence.rootedAt cap.expectedDeploymentId state.revision
      (outputRegistryIdentity persistence state) (persistence.serializer.encode state)) :
    DurableOutputRegistryLoad persistence state :=
  ⟨cap.expectedDeploymentId, included, rooted⟩

theorem DurableOutputRegistryLoad.exact {persistence : OutputRegistryPersistenceContract}
    {state : OutputRegistryState} (load : DurableOutputRegistryLoad persistence state) :
    persistence.loadedAt state.revision (outputRegistryIdentity persistence state)
      (persistence.serializer.encode state) := load.included

theorem DurableOutputRegistryLoad.rooted_exact
    {persistence : OutputRegistryPersistenceContract} {state : OutputRegistryState}
    (load : DurableOutputRegistryLoad persistence state) :
    persistence.rootedAt load.expectedDeploymentId state.revision
      (outputRegistryIdentity persistence state) (persistence.serializer.encode state) :=
  load.rooted

structure PersistedOutputRegistry (persistence : OutputRegistryPersistenceContract) where
  private mk ::
  deploymentId : Digest32
  state : OutputRegistryState
  deployment_exact : deploymentId = state.deploymentId
  rooted : persistence.rootedAt deploymentId state.revision
    (outputRegistryIdentity persistence state) (persistence.serializer.encode state)

/-- Genesis is one of exactly two safe lineage entrances; the other is a
durable load carrying `rootedAt` below. -/
def startOutputRegistry {persistence : OutputRegistryPersistenceContract}
    (root : OutputRegistryGenesisCertificate persistence) :
    PersistedOutputRegistry persistence :=
  ⟨root.deploymentId, root.state, by simp [root.canonical, outputRegistryGenesisState],
    root.rooted⟩

theorem OutputRegistryGenesisCertificate.same_root
    {persistence : OutputRegistryPersistenceContract}
    (left right : OutputRegistryGenesisCertificate persistence)
    (sameDeployment : left.deploymentId = right.deploymentId) : left.state = right.state := by
  have rightCreated := right.created
  rw [← sameDeployment] at rightCreated
  exact persistence.serializer.faithful
    (persistence.genesisUnique left.created rightCreated).2

def admitPersistedOutputRegistry {persistence : OutputRegistryPersistenceContract}
    {state : OutputRegistryState} (load : DurableOutputRegistryLoad persistence state) :
    Except OutputRegistryRefusal (PersistedOutputRegistry persistence) :=
  if h : load.expectedDeploymentId = state.deploymentId then
    .ok ⟨load.expectedDeploymentId, state, h, load.rooted⟩
  else .error .loadDeployment

/-- Hostile duplicate-genesis/reset theorem: a rooted revision-zero load for
the same deployment is byte-for-byte the unique certified genesis state. -/
theorem DurableOutputRegistryLoad.revisionZero_same_genesis
    {persistence : OutputRegistryPersistenceContract} {state : OutputRegistryState}
    (root : OutputRegistryGenesisCertificate persistence)
    (load : DurableOutputRegistryLoad persistence state)
    (sameDeployment : root.deploymentId = load.expectedDeploymentId)
    (revisionZero : state.revision = 0) : state = root.state := by
  have loadedCreated : persistence.createGenesis load.expectedDeploymentId
      (outputRegistryIdentity persistence state) (persistence.serializer.encode state) := by
    apply persistence.rootedZeroWasGenesis
    simpa [revisionZero] using load.rooted
  rw [← sameDeployment] at loadedCreated
  exact persistence.serializer.faithful
    (persistence.genesisUnique loadedCreated root.created).2

structure PersistedOutputRegistryTransition (persistence : OutputRegistryPersistenceContract)
    (deploymentId : Digest32)
    (before after : OutputRegistryState) where
  private mk ::
  committed : persistence.compareAndSwap deploymentId before.revision
    (outputRegistryIdentity persistence before) after.revision
    (persistence.serializer.encode after)

def admitOutputRegistryCASReceipt {persistence : OutputRegistryPersistenceContract}
    (cap : OutputRegistryPersistenceCapability persistence)
    (before after : OutputRegistryState)
    (committed : persistence.compareAndSwap cap.expectedDeploymentId before.revision
      (outputRegistryIdentity persistence before) after.revision
      (persistence.serializer.encode after)) :
    PersistedOutputRegistryTransition persistence cap.expectedDeploymentId before after :=
  ⟨committed⟩

structure CommittedOutputConsumption (persistence : OutputRegistryPersistenceContract)
    (activation : ActivatedDaily) (raw : FinalizedRunEventAggregate.Payload) where
  private mk ::
  registry : PersistedOutputRegistry persistence
  consumed : ConsumedDurableOutput activation raw

def proposePersistedOutputConsumption {persistence : OutputRegistryPersistenceContract}
    (before : PersistedOutputRegistry persistence) (activation : ActivatedDaily)
    (raw : FinalizedRunEventAggregate.Payload)
    (admission : AdmittedDurableOutput activation raw) :
    Except OutputRegistryRefusal (OutputRegistryCandidate activation raw before.state) :=
  proposeOutputConsumption before.state activation raw admission

def continueOutputConsumption {persistence : OutputRegistryPersistenceContract}
    {before : PersistedOutputRegistry persistence} {activation : ActivatedDaily}
    {raw : FinalizedRunEventAggregate.Payload}
    (candidate : OutputRegistryCandidate activation raw before.state)
    (receipt : PersistedOutputRegistryTransition persistence before.deploymentId
      before.state candidate.after) :
    Except OutputRegistryRefusal (CommittedOutputConsumption persistence activation raw) :=
  have rootedAfter : persistence.rootedAt before.deploymentId candidate.after.revision
        (outputRegistryIdentity persistence candidate.after)
        (persistence.serializer.encode candidate.after) := by
      simpa [outputRegistryIdentity] using
        persistence.casPreservesRoot before.rooted receipt.committed
  have deploymentAfter : before.deploymentId = candidate.after.deploymentId := by
    rw [before.deployment_exact, candidate.after_exact]
  .ok ⟨⟨before.deploymentId, candidate.after, deploymentAfter, rootedAfter⟩,
    ⟨before.state, candidate.after, candidate.after_exact, candidate.deployment_exact⟩⟩

theorem PersistedOutputRegistryTransition.same_successor
    {persistence : OutputRegistryPersistenceContract}
    {deploymentId : Digest32} {before left right : OutputRegistryState}
    (leftWon : PersistedOutputRegistryTransition persistence deploymentId before left)
    (rightWon : PersistedOutputRegistryTransition persistence deploymentId before right) : left = right :=
  persistence.serializer.faithful <|
    (persistence.singleWinner leftWon.committed rightWon.committed).2

theorem PersistedOutputRegistryTransition.deployment_scoped
    {persistence : OutputRegistryPersistenceContract} {deploymentId : Digest32}
    {before after : OutputRegistryState}
    (receipt : PersistedOutputRegistryTransition persistence deploymentId before after) :
    persistence.compareAndSwap deploymentId before.revision
      (outputRegistryIdentity persistence before) after.revision
      (persistence.serializer.encode after) :=
  receipt.committed

structure DailyPersistenceCASContract where
  /-- Deployment-fixed event hashing.  Callers cannot swap in an accepting
  digest boundary after command admission. -/
  digests : EventSourcing.DigestBoundary Payload
  serializer : DailyCanonicalSerializer DailyDeploymentSnapshot
  hashAlgorithmId : Digest32
  storeKindId : Digest32
  realHash : DailyCanonicalBytes → Digest32
  loadedAt : Nat → Digest32 → DailyCanonicalBytes → Prop
  createGenesis : Digest32 → Digest32 → DailyCanonicalBytes → Prop
  rootedAt : Digest32 → Nat → Digest32 → DailyCanonicalBytes → Prop
  compareAndSwap : Digest32 → Nat → Digest32 → Nat → DailyCanonicalBytes → Prop
  genesisRooted : ∀ {deploymentId root : Digest32} {bytes : DailyCanonicalBytes},
    createGenesis deploymentId root bytes → rootedAt deploymentId 0 root bytes
  rootedZeroWasGenesis : ∀ {deploymentId root : Digest32} {bytes : DailyCanonicalBytes},
    rootedAt deploymentId 0 root bytes → createGenesis deploymentId root bytes
  genesisUnique : ∀ {deploymentId leftRoot rightRoot : Digest32}
      {left right : DailyCanonicalBytes},
    createGenesis deploymentId leftRoot left →
    createGenesis deploymentId rightRoot right →
    leftRoot = rightRoot ∧ left = right
  casPreservesRoot : ∀ {deploymentId : Digest32} {beforeRevision : Nat}
      {beforeRoot : Digest32} {beforeBytes : DailyCanonicalBytes}
      {afterRevision : Nat} {afterBytes : DailyCanonicalBytes},
    rootedAt deploymentId beforeRevision beforeRoot beforeBytes →
    compareAndSwap deploymentId beforeRevision beforeRoot afterRevision afterBytes →
    rootedAt deploymentId afterRevision
      (realHash (hashAlgorithmId.bytes ++ storeKindId.bytes ++ afterBytes)) afterBytes
  singleWinner : ∀ {deploymentId : Digest32} {expectedRevision : Nat} {expected : Digest32}
      {leftRevision rightRevision : Nat} {left right : DailyCanonicalBytes},
    compareAndSwap deploymentId expectedRevision expected leftRevision left →
    compareAndSwap deploymentId expectedRevision expected rightRevision right →
    leftRevision = rightRevision ∧ left = right

def dailySnapshotIdentity (persistence : DailyPersistenceCASContract)
    (snapshot : DailyDeploymentSnapshot) : Digest32 :=
  persistence.realHash
    (persistence.hashAlgorithmId.bytes ++ persistence.storeKindId.bytes ++
      persistence.serializer.encode snapshot)

structure DailyPersistenceCapability (persistence : DailyPersistenceCASContract) where
  private mk ::
  provenance : DailyActivationProvenance
  expectedDeploymentId : Digest32

structure DailyRootGenesisCapability (persistence : DailyPersistenceCASContract) where
  private mk ::
  provenance : DailyActivationProvenance
  expectedDeploymentId : Digest32

structure DailyRootCertificate (persistence : DailyPersistenceCASContract) where
  private mk ::
  provenance : DailyActivationProvenance
  deploymentId : Digest32
  activation : ActivatedDaily
  snapshot : DailyDeploymentSnapshot
  activation_exact : snapshot.activation = activation
  deployment_exact : deploymentId = snapshot.activation.deploymentId
  canonical : snapshot = dailyGenesisSnapshot snapshot.activation
  created : persistence.createGenesis deploymentId
    (dailySnapshotIdentity persistence snapshot) (persistence.serializer.encode snapshot)
  rooted : persistence.rootedAt deploymentId snapshot.revision
    (dailySnapshotIdentity persistence snapshot) (persistence.serializer.encode snapshot)

inductive DailyGenesisRefusal where
  | wrongDeployment
  | activationProvenance
deriving DecidableEq, Repr

def bootstrapDailyRoot {persistence : DailyPersistenceCASContract}
    (cap : DailyRootGenesisCapability persistence) (activation : ActivatedDaily)
    (created : persistence.createGenesis cap.expectedDeploymentId
      (dailySnapshotIdentity persistence (dailyGenesisSnapshot activation))
      (persistence.serializer.encode (dailyGenesisSnapshot activation))) :
    Except DailyGenesisRefusal (DailyRootCertificate persistence) :=
  if hdeployment : cap.expectedDeploymentId = activation.deploymentId then
    if hprovenance : cap.provenance = activation.provenance then
      .ok ⟨cap.provenance, cap.expectedDeploymentId, activation,
        dailyGenesisSnapshot activation, rfl,
        by simpa using hdeployment, rfl, created, persistence.genesisRooted created⟩
    else .error .activationProvenance
  else .error .wrongDeployment

structure DurableDailyLoad (persistence : DailyPersistenceCASContract)
    (snapshot : DailyDeploymentSnapshot) where
  private mk ::
  provenance : DailyActivationProvenance
  expectedDeploymentId : Digest32
  included : persistence.loadedAt snapshot.revision
    (dailySnapshotIdentity persistence snapshot) (persistence.serializer.encode snapshot)
  rooted : persistence.rootedAt expectedDeploymentId snapshot.revision
    (dailySnapshotIdentity persistence snapshot) (persistence.serializer.encode snapshot)

def admitDurableDailyLoad {persistence : DailyPersistenceCASContract}
    (cap : DailyPersistenceCapability persistence) (snapshot : DailyDeploymentSnapshot)
    (included : persistence.loadedAt snapshot.revision
      (dailySnapshotIdentity persistence snapshot) (persistence.serializer.encode snapshot))
    (rooted : persistence.rootedAt cap.expectedDeploymentId snapshot.revision
      (dailySnapshotIdentity persistence snapshot) (persistence.serializer.encode snapshot)) :
    DurableDailyLoad persistence snapshot :=
  ⟨cap.provenance, cap.expectedDeploymentId, included, rooted⟩

theorem DurableDailyLoad.exact {persistence : DailyPersistenceCASContract}
    {snapshot : DailyDeploymentSnapshot} (load : DurableDailyLoad persistence snapshot) :
    persistence.loadedAt snapshot.revision (dailySnapshotIdentity persistence snapshot)
      (persistence.serializer.encode snapshot) := load.included

theorem DurableDailyLoad.rooted_exact {persistence : DailyPersistenceCASContract}
    {snapshot : DailyDeploymentSnapshot} (load : DurableDailyLoad persistence snapshot) :
    persistence.rootedAt load.expectedDeploymentId snapshot.revision
      (dailySnapshotIdentity persistence snapshot) (persistence.serializer.encode snapshot) :=
  load.rooted

structure PersistedDailyRuntime (persistence : DailyPersistenceCASContract) where
  private mk ::
  deploymentId : Digest32
  snapshot : DailyDeploymentSnapshot
  deployment_exact : deploymentId = snapshot.activation.deploymentId
  rooted : persistence.rootedAt deploymentId snapshot.revision
    (dailySnapshotIdentity persistence snapshot) (persistence.serializer.encode snapshot)

def startPersistedDaily {persistence : DailyPersistenceCASContract}
    (root : DailyRootCertificate persistence) : PersistedDailyRuntime persistence :=
  ⟨root.deploymentId, root.snapshot, root.deployment_exact, root.rooted⟩

inductive DailyPersistenceRefusal where
  | activationProvenance
  | wrongDeployment
  | cursorVersion
  | wrongSpec
  | cursorProjectionSequence
  | cursorAggregate
  | commitProvenance
deriving DecidableEq, Repr

def admitPersistedDailyRuntime {persistence : DailyPersistenceCASContract}
    {snapshot : DailyDeploymentSnapshot} (load : DurableDailyLoad persistence snapshot) :
    Except DailyPersistenceRefusal (PersistedDailyRuntime persistence) :=
  if load.provenance ≠ snapshot.activation.provenance then .error .activationProvenance
  else if hdeployment : load.expectedDeploymentId = snapshot.activation.deploymentId then
    if snapshot.replay.cursor.version ≠ (streamSpec snapshot.activation.spec).version then
      .error .cursorVersion
    else if snapshot.replay.projection.spec ≠ snapshot.activation.spec then .error .wrongSpec
    else if snapshot.replay.projection.sequence ≠ snapshot.replay.cursor.sequence then
      .error .cursorProjectionSequence
    else if snapshot.replay.cursor.aggregate ≠ (streamSpec snapshot.activation.spec).aggregate then
      .error .cursorAggregate
    else .ok ⟨load.expectedDeploymentId, snapshot, hdeployment, load.rooted⟩
  else .error .wrongDeployment

theorem admitPersistedDailyRuntime_wrong_cursor_version
    {persistence : DailyPersistenceCASContract} {snapshot : DailyDeploymentSnapshot}
    (load : DurableDailyLoad persistence snapshot)
    (provenanceExact : load.provenance = snapshot.activation.provenance)
    (deploymentExact : load.expectedDeploymentId = snapshot.activation.deploymentId)
    (wrongVersion : snapshot.replay.cursor.version ≠
      (streamSpec snapshot.activation.spec).version) :
    admitPersistedDailyRuntime load = .error .cursorVersion := by
  simp [admitPersistedDailyRuntime, provenanceExact, deploymentExact, wrongVersion]

structure PersistedDailyTransition (persistence : DailyPersistenceCASContract)
    (deploymentId : Digest32)
    (before after : DailyDeploymentSnapshot) where
  private mk ::
  provenance : DailyActivationProvenance
  committed : persistence.compareAndSwap deploymentId before.revision
    (dailySnapshotIdentity persistence before) after.revision
    (persistence.serializer.encode after)

theorem PersistedDailyTransition.same_successor
    {persistence : DailyPersistenceCASContract} {deploymentId : Digest32}
    {before left right : DailyDeploymentSnapshot}
    (leftWon : PersistedDailyTransition persistence deploymentId before left)
    (rightWon : PersistedDailyTransition persistence deploymentId before right) : left = right :=
  persistence.serializer.faithful <|
    (persistence.singleWinner leftWon.committed rightWon.committed).2

theorem PersistedDailyTransition.deployment_scoped
    {persistence : DailyPersistenceCASContract} {deploymentId : Digest32}
    {before after : DailyDeploymentSnapshot}
    (receipt : PersistedDailyTransition persistence deploymentId before after) :
    persistence.compareAndSwap deploymentId before.revision
      (dailySnapshotIdentity persistence before) after.revision
      (persistence.serializer.encode after) :=
  receipt.committed

def admitDailyCASReceipt {persistence : DailyPersistenceCASContract}
    (cap : DailyPersistenceCapability persistence) (before after : DailyDeploymentSnapshot)
    (committed : persistence.compareAndSwap cap.expectedDeploymentId before.revision
      (dailySnapshotIdentity persistence before) after.revision
      (persistence.serializer.encode after)) :
    PersistedDailyTransition persistence cap.expectedDeploymentId before after :=
  ⟨cap.provenance, committed⟩

def proposePersistedDaily {persistence : DailyPersistenceCASContract}
    (before : PersistedDailyRuntime persistence) (event : EventSourcing.EventEnvelope Payload)
    (command : AdmittedDailyCommand before.snapshot event) :
    Except SecureDailyRefusal (DailyTransitionCandidate before.snapshot event) :=
  proposeDaily persistence.digests before.snapshot event command

def continuePersistedDaily {persistence : DailyPersistenceCASContract}
    {before : PersistedDailyRuntime persistence} {event : EventSourcing.EventEnvelope Payload}
    (candidate : DailyTransitionCandidate before.snapshot event)
    (receipt : PersistedDailyTransition persistence before.deploymentId
      before.snapshot candidate.after) :
    Except DailyPersistenceRefusal (PersistedDailyRuntime persistence) :=
  if receipt.provenance ≠ before.snapshot.activation.provenance then
    .error .commitProvenance
  else
    have rootedAfter : persistence.rootedAt before.deploymentId candidate.after.revision
        (dailySnapshotIdentity persistence candidate.after)
        (persistence.serializer.encode candidate.after) := by
      simpa [dailySnapshotIdentity] using
        persistence.casPreservesRoot before.rooted receipt.committed
    have deploymentAfter : before.deploymentId = candidate.after.activation.deploymentId := by
      rw [before.deployment_exact, candidate.activation_exact]
    .ok ⟨before.deploymentId, candidate.after, deploymentAfter, rootedAfter⟩

theorem DurableDailyLoad.revisionZero_same_genesis
    {persistence : DailyPersistenceCASContract} {snapshot : DailyDeploymentSnapshot}
    (root : DailyRootCertificate persistence)
    (load : DurableDailyLoad persistence snapshot)
    (sameDeployment : root.deploymentId = load.expectedDeploymentId)
    (revisionZero : snapshot.revision = 0) : snapshot = root.snapshot := by
  have loadedCreated : persistence.createGenesis load.expectedDeploymentId
      (dailySnapshotIdentity persistence snapshot) (persistence.serializer.encode snapshot) := by
    apply persistence.rootedZeroWasGenesis
    simpa [revisionZero] using load.rooted
  rw [← sameDeployment] at loadedCreated
  exact persistence.serializer.faithful
    (persistence.genesisUnique loadedCreated root.created).2

/-! ### One shared trusted-host provisioning portal -/

/-- The sole Daily-side host initialization token.  It is intentionally opaque:
the runtime portal supplies it, and this module turns it into a deployment-pinned
bundle rather than asking the host to construct each capability ad hoc. -/
structure HostInitializer where
  private mk ::
  dailyProvenance : DailyActivationProvenance
  outputProvenance : OutputCommitProvenance
  trustedActivationKey : Digest32

structure ProvisionedCapabilityBundle
    (commonsOracle : GalleyCommons.AdmissionOracle)
    (commonsPersistence : GalleyCommons.PersistenceCASContract)
    (activationOracle : DailyActivationOracle)
    (outputOracle : DailyOutputCommitOracle)
    (commandOracle : DailyCommandOracle)
    (dailyPersistence : DailyPersistenceCASContract)
    (registryPersistence : OutputRegistryPersistenceContract) where
  private mk ::
  deploymentId : Digest32
  commons : GalleyCommons.ProvisionedDeployment commonsOracle commonsPersistence
  activation : DailyActivationCapability activationOracle
  output : DailyOutputCommitCapability outputOracle
  command : DailyCommandCapability commandOracle
  dailyStore : DailyPersistenceCapability dailyPersistence
  dailyGenesis : DailyRootGenesisCapability dailyPersistence
  dailyGenesis_deployment : dailyGenesis.expectedDeploymentId = deploymentId
  outputRegistry : OutputRegistryPersistenceCapability registryPersistence
  outputRegistryGenesis : OutputRegistryGenesisCapability registryPersistence
  outputRegistryGenesis_deployment :
    outputRegistryGenesis.expectedDeploymentId = deploymentId

/-- Callable non-fixture bridge which pins every PoA capability to the Commons
deployment whose unique root has already won create-if-absent. -/
def provisionCapabilities
    (initializer : HostInitializer)
    {commonsOracle : GalleyCommons.AdmissionOracle}
    {commonsPersistence : GalleyCommons.PersistenceCASContract}
    {activationOracle : DailyActivationOracle}
    {outputOracle : DailyOutputCommitOracle}
    {commandOracle : DailyCommandOracle}
    {dailyPersistence : DailyPersistenceCASContract}
    {registryPersistence : OutputRegistryPersistenceContract}
    (commons : GalleyCommons.ProvisionedDeployment commonsOracle commonsPersistence) :
    ProvisionedCapabilityBundle commonsOracle commonsPersistence activationOracle outputOracle
      commandOracle dailyPersistence registryPersistence :=
  ⟨commons.deploymentId, commons,
    ⟨initializer.dailyProvenance, commons.deploymentId, initializer.trustedActivationKey⟩,
    ⟨initializer.outputProvenance⟩, ⟨initializer.dailyProvenance⟩,
    ⟨initializer.dailyProvenance, commons.deploymentId⟩,
    ⟨initializer.dailyProvenance, commons.deploymentId⟩, rfl,
    ⟨commons.deploymentId⟩, ⟨commons.deploymentId⟩, rfl⟩

structure ProvisionedDeployment
    (commonsOracle : GalleyCommons.AdmissionOracle)
    (commonsPersistence : GalleyCommons.PersistenceCASContract)
    (activationOracle : DailyActivationOracle)
    (outputOracle : DailyOutputCommitOracle)
    (commandOracle : DailyCommandOracle)
    (dailyPersistence : DailyPersistenceCASContract)
    (registryPersistence : OutputRegistryPersistenceContract) where
  private mk ::
  capabilities : ProvisionedCapabilityBundle commonsOracle commonsPersistence activationOracle
    outputOracle commandOracle dailyPersistence registryPersistence
  activation : ActivatedDaily
  activation_deployment : activation.deploymentId = capabilities.deploymentId
  dailyRoot : DailyRootCertificate dailyPersistence
  registryRoot : OutputRegistryGenesisCertificate registryPersistence

/-- Second and final provisioning step: after exact activation admission, create
the Daily and output-registry roots under the Commons deployment id. -/
def initializeDeployment
    {commonsOracle : GalleyCommons.AdmissionOracle}
    {commonsPersistence : GalleyCommons.PersistenceCASContract}
    {activationOracle : DailyActivationOracle}
    {outputOracle : DailyOutputCommitOracle}
    {commandOracle : DailyCommandOracle}
    {dailyPersistence : DailyPersistenceCASContract}
    {registryPersistence : OutputRegistryPersistenceContract}
    (caps : ProvisionedCapabilityBundle commonsOracle commonsPersistence activationOracle
      outputOracle commandOracle dailyPersistence registryPersistence)
    (activation : ActivatedDaily)
    (dailyCreated : dailyPersistence.createGenesis caps.deploymentId
      (dailySnapshotIdentity dailyPersistence (dailyGenesisSnapshot activation))
      (dailyPersistence.serializer.encode (dailyGenesisSnapshot activation)))
    (registryCreated : registryPersistence.createGenesis caps.deploymentId
      (outputRegistryIdentity registryPersistence
        (outputRegistryGenesisState caps.deploymentId))
      (registryPersistence.serializer.encode
        (outputRegistryGenesisState caps.deploymentId))) :
    Except DailyGenesisRefusal
      (ProvisionedDeployment commonsOracle commonsPersistence activationOracle outputOracle
        commandOracle dailyPersistence registryPersistence) :=
  if hdeployment : activation.deploymentId = caps.deploymentId then do
    have dailyCreated' : dailyPersistence.createGenesis caps.dailyGenesis.expectedDeploymentId
        (dailySnapshotIdentity dailyPersistence (dailyGenesisSnapshot activation))
        (dailyPersistence.serializer.encode (dailyGenesisSnapshot activation)) := by
      simpa [caps.dailyGenesis_deployment] using dailyCreated
    have registryCreated' :
        registryPersistence.createGenesis caps.outputRegistryGenesis.expectedDeploymentId
          (outputRegistryIdentity registryPersistence
            (outputRegistryGenesisState caps.outputRegistryGenesis.expectedDeploymentId))
          (registryPersistence.serializer.encode
            (outputRegistryGenesisState caps.outputRegistryGenesis.expectedDeploymentId)) := by
      simpa [caps.outputRegistryGenesis_deployment] using registryCreated
    let dailyRoot ← bootstrapDailyRoot caps.dailyGenesis activation dailyCreated'
    let registryRoot := bootstrapOutputRegistry caps.outputRegistryGenesis registryCreated'
    .ok ⟨caps, activation, hdeployment, dailyRoot, registryRoot⟩
  else .error .wrongDeployment

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
  insuranceCap := ⟨20, by native_decide⟩
  sponsorCredit := ⟨2, by native_decide⟩
  publicQuorum := 1

private def actionA : Digest32 := digestByte 80
private def actionB : Digest32 := digestByte 81
private def actionC : Digest32 := digestByte 82

private def brothChoice : CommonsChoice where
  choiceId := digestByte 140
  labelContentId := digestByte 141
  servedContentId := digestByte 142
  alternativeContentId := digestByte 143
  capacity := 1
  localService := ⟨5, by native_decide⟩

private def teaChoice : CommonsChoice where
  choiceId := digestByte 144
  labelContentId := digestByte 145
  servedContentId := digestByte 146
  alternativeContentId := digestByte 147
  capacity := 2
  localService := ⟨3, by native_decide⟩

private def nightChoice : CommonsChoice where
  choiceId := digestByte 148
  labelContentId := digestByte 149
  servedContentId := digestByte 150
  alternativeContentId := digestByte 151
  capacity := 1
  localService := ⟨8, by native_decide⟩

private def fixtureCommonsRaw : RawCommonsPolicy where
  rotations := [
    { rotationId := digestByte 152, sceneContentId := digestByte 153,
      choices := [brothChoice, teaChoice] },
    { rotationId := digestByte 154, sceneContentId := digestByte 155,
      choices := [nightChoice] }
  ]

private theorem fixture_commons_valid : commonsPolicyValidB fixtureCommonsRaw = true := by
  native_decide

private def fixtureCommons : CommonsPolicy := ⟨fixtureCommonsRaw, fixture_commons_valid⟩

private def fixtureSpec : DailySpec where
  holderPolicy := fixtureHolderPolicy
  activationKey := digestByte 156
  outputCommitKey := digestByte 157
  dayIndex := 0
  commons := fixtureCommons
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

private def fixtureDailyProvenance : DailyActivationProvenance := ⟨digestByte 158⟩
private def fixtureOutputProvenance : OutputCommitProvenance := ⟨digestByte 159⟩

private def fixtureActivationOracle : DailyActivationOracle where
  oracleId := digestByte 160
  verifyActivation _ _ _ := true

private def fixtureActivationCapability : DailyActivationCapability fixtureActivationOracle :=
  ⟨fixtureDailyProvenance, digestByte 161, fixtureSpec.activationKey⟩

private def fixtureSignature : DailyDetachedSignature := ⟨[]⟩

private def fixtureActivation : ActivatedDaily :=
  (admitDailyActivation fixtureActivationOracle fixtureActivationCapability
    (digestByte 161) fixtureHolderPolicy.eventGenesisHead fixtureSpec fixtureSignature).toOption.get
      (by native_decide)

theorem activation_with_wrong_genesis_head_is_refused :
    (match admitDailyActivation fixtureActivationOracle fixtureActivationCapability
      (digestByte 161) (digestByte 255) fixtureSpec fixtureSignature with
    | .error error => error
    | .ok _ => .invalidSignature) = .wrongGenesisHead := by
  native_decide

theorem candidate_spec_cannot_choose_its_own_activation_key :
    let selfKeyed := { fixtureSpec with activationKey := digestByte 254 }
    (match admitDailyActivation fixtureActivationOracle fixtureActivationCapability
      (digestByte 161) fixtureHolderPolicy.eventGenesisHead selfKeyed fixtureSignature with
    | .error error => error
    | .ok _ => .invalidSignature) = .untrustedActivationKey := by
  native_decide

theorem activation_capability_pins_deployment_id :
    (match admitDailyActivation fixtureActivationOracle fixtureActivationCapability
      (digestByte 253) fixtureHolderPolicy.eventGenesisHead fixtureSpec fixtureSignature with
    | .error error => error
    | .ok _ => .invalidSignature) = .wrongDeployment := by
  native_decide

private def fixtureOutputOracle : DailyOutputCommitOracle where
  oracleId := digestByte 162
  verifyCommittedOutput _ _ _ := true

private def fixtureOutputCapability : DailyOutputCommitCapability fixtureOutputOracle :=
  ⟨fixtureOutputProvenance⟩

private def fixtureCommandOracle : DailyCommandOracle where
  oracleId := digestByte 163
  verifyCommand _ _ _ := true

private def fixtureCommandCapability : DailyCommandCapability fixtureCommandOracle :=
  ⟨fixtureDailyProvenance⟩

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
    0, [], ∅, ∅, [], [], 0, [], none, none, none⟩

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
private def commonsVisitA : Payload := ⟨4, .visitCommons maintainerA brothChoice.choiceId⟩
private def commonsEventA := nextEnvelope fixtureSpec fixtureDigests
  (cursorAfter fixtureSpec eventC) commonsVisitA
private def commonsVisitB : Payload := ⟨5, .visitCommons maintainerB brothChoice.choiceId⟩
private def commonsEventB := nextEnvelope fixtureSpec fixtureDigests
  (cursorAfter fixtureSpec commonsEventA) commonsVisitB
private def outputPayload : Payload := ⟨6, .recordFinalizedOutput fixtureFinalizedPayload⟩
private def outputEvent := nextEnvelope fixtureSpec fixtureDigests
  (cursorAfter fixtureSpec commonsEventB) outputPayload

private def fixtureReplay : Except EventSourcing.Error (EventSourcing.ReplayState State) :=
  EventSourcing.replay (streamSpec fixtureSpec) fixtureDigests (reduce fixtureSpec)
    { cursor := (streamSpec fixtureSpec).genesisCursor,
      projection := fixtureMaintenanceReady }
    [eventA, eventB, eventC, commonsEventA, commonsEventB, outputEvent]

theorem three_step_daily_replays_to_one_exact_finalized_output :
    fixtureReplay.toOption.map (fun replayed =>
      decide (replayed.projection.phase = .outputRecorded) &&
      decide (replayed.projection.progress = 3) &&
      decide (replayed.projection.performed = [actionA, actionB, actionC]) &&
      decide (replayed.projection.terminalContentId = some fixtureSpec.successContentId) &&
      decide (replayed.projection.commonsOutcomes.map CommonsOutcome.disposition =
        [.served, .neighborlyAlternative]) &&
      decide (replayed.projection.commonsOutcomes.map CommonsOutcome.contentId =
        [brothChoice.servedContentId, brothChoice.alternativeContentId]) &&
      decide (replayed.projection.localServiceTotal = brothChoice.localService.val) &&
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

theorem public_chamber_can_open_without_holder_veto :
    let afterPublic := (reduce fixtureSpec (initialState fixtureSpec)
      ⟨1, .participant (.publicVote fixturePublicVote)⟩).get (by native_decide)
    (reduce fixtureSpec afterPublic ⟨2, .openMaintenance⟩).map State.phase =
      some .maintenance := by
  native_decide

theorem wrong_authored_step_is_refused_without_advancing :
    reduce fixtureSpec fixtureMaintenanceReady
      ⟨1, .perform maintainerA actionC⟩ = none := by
  native_decide

theorem authored_rotation_repeats_deterministically :
    activeRotation? fixtureCommons 0 = fixtureCommonsRaw.rotations[0]? ∧
      activeRotation? fixtureCommons 1 = fixtureCommonsRaw.rotations[1]? ∧
      activeRotation? fixtureCommons 2 = fixtureCommonsRaw.rotations[0]? := by
  native_decide

theorem unknown_commons_choice_is_refused_without_advancing :
    reduce fixtureSpec fixtureMaintenanceReady
      ⟨1, .visitCommons maintainerA (digestByte 199)⟩ = none := by
  native_decide

private def afterFirstCommonsVisit : State :=
  (reduce fixtureSpec fixtureMaintenanceReady
    ⟨1, .visitCommons maintainerA brothChoice.choiceId⟩).get (by native_decide)

theorem one_commons_visit_per_player_is_enforced :
    reduce fixtureSpec afterFirstCommonsVisit
      ⟨2, .visitCommons maintainerA teaChoice.choiceId⟩ = none := by
  native_decide

theorem full_commons_choice_gives_authored_neighborly_alternative :
    let second := reduce fixtureSpec afterFirstCommonsVisit
      ⟨2, .visitCommons maintainerB brothChoice.choiceId⟩
    second.map (fun state =>
      decide (state.sequence = 2) &&
      decide (state.commonsOutcomes.map CommonsOutcome.disposition =
        [.served, .neighborlyAlternative]) &&
      decide (state.commonsOutcomes.map CommonsOutcome.contentId =
        [brothChoice.servedContentId, brothChoice.alternativeContentId]) &&
      decide (state.localServiceTotal = brothChoice.localService.val)) = some true := by
  native_decide

theorem authored_commons_strategies_have_distinct_outcomes :
    let brothPath := reduce fixtureSpec fixtureMaintenanceReady
      ⟨1, .visitCommons maintainerA brothChoice.choiceId⟩
    let teaPath := reduce fixtureSpec fixtureMaintenanceReady
      ⟨1, .visitCommons maintainerA teaChoice.choiceId⟩
    brothPath.bind (fun brothState =>
      teaPath.map (fun teaState =>
        decide (brothState.commonsOutcomes.head?.map CommonsOutcome.contentId =
          some brothChoice.servedContentId) &&
        decide (teaState.commonsOutcomes.head?.map CommonsOutcome.contentId =
          some teaChoice.servedContentId) &&
        decide (brothState.localServiceTotal = 5) &&
        decide (teaState.localServiceTotal = 3))) = some true := by
  native_decide

theorem commons_visit_does_not_change_power_projection :
    (reduce fixtureSpec fixtureMaintenanceReady
      ⟨1, .visitCommons maintainerA brothChoice.choiceId⟩).map powerProjection =
      some (powerProjection fixtureMaintenanceReady) := by
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

private def fixtureMaintenanceSnapshot : DailyDeploymentSnapshot where
  revision := 0
  activation := fixtureActivation
  replay := {
    cursor := (streamSpec fixtureSpec).genesisCursor
    projection := fixtureMaintenanceReady
  }
  spentActionNullifiers := ∅

theorem forged_maintainer_identity_is_refused_at_admission :
    (match admitDailyCommand fixtureCommandOracle fixtureCommandCapability
      fixtureMaintenanceSnapshot eventA fixtureSpec.activationKey (digestByte 170)
      (.perform maintainerA actionA) fixtureSignature with
    | .error error => error
    | .ok _ => .invalidSignature) = .actorMismatch := by
  native_decide

theorem replayed_action_nullifier_is_refused_at_admission :
    let nullifier := digestByte 171
    let replayed := { fixtureMaintenanceSnapshot with
      spentActionNullifiers := {nullifier} }
    (match admitDailyCommand fixtureCommandOracle fixtureCommandCapability
      replayed eventA maintainerA.digest nullifier
      (.perform maintainerA actionA) fixtureSignature with
    | .error error => error
    | .ok _ => .invalidSignature) = .nullifierReplay := by
  native_decide

private def fixtureCompletedSnapshot : DailyDeploymentSnapshot where
  revision := 3
  activation := fixtureActivation
  replay := {
    cursor := cursorAfter fixtureSpec eventC
    projection := fixtureCompleted
  }
  spentActionNullifiers := ∅

private def secureOutputPayload : Payload :=
  ⟨4, .recordFinalizedOutput fixtureFinalizedPayload⟩

private def secureOutputEvent : EventSourcing.EventEnvelope Payload :=
  nextEnvelope fixtureSpec fixtureDigests (cursorAfter fixtureSpec eventC) secureOutputPayload

private def fixtureDurableOutputAdmission :
    AdmittedDurableOutput fixtureActivation fixtureFinalizedPayload :=
  (admitDurableOutput fixtureOutputOracle fixtureOutputCapability fixtureActivation
    fixtureFinalizedPayload fixtureSignature).toOption.get (by native_decide)

private def fixtureOutputRegistry : OutputRegistryState where
  deploymentId := fixtureActivation.deploymentId
  revision := 0
  consumedCoordinates := ∅
  consumedReceiptHashes := ∅

private def fixtureOutputCandidate :
    OutputRegistryCandidate fixtureActivation fixtureFinalizedPayload fixtureOutputRegistry :=
  (proposeOutputConsumption fixtureOutputRegistry fixtureActivation fixtureFinalizedPayload
    fixtureDurableOutputAdmission).toOption.get (by native_decide)

private def fixtureConsumedOutput :
    ConsumedDurableOutput fixtureActivation fixtureFinalizedPayload :=
  ⟨fixtureOutputRegistry, fixtureOutputCandidate.after, fixtureOutputCandidate.after_exact,
    fixtureOutputCandidate.deployment_exact⟩

private def fixtureSecureOutputCommand :
    AdmittedDailyCommand fixtureCompletedSnapshot secureOutputEvent :=
  (admitDailyCommand fixtureCommandOracle fixtureCommandCapability
    fixtureCompletedSnapshot secureOutputEvent fixtureSpec.activationKey
    (digestByte 172)
    (.recordFinalizedOutput fixtureFinalizedPayload fixtureConsumedOutput)
    fixtureSignature).toOption.get (by native_decide)

theorem deployment_registry_candidate_binds_both_output_nullifiers :
    fixtureOutputCandidate.after = {
      deploymentId := fixtureActivation.deploymentId
      revision := 1
      consumedCoordinates := {fixtureFinalizedPayload.finalized}
      consumedReceiptHashes := {fixtureFinalizedPayload.finalized.receiptHash}
    } := by
  native_decide

theorem deployment_registry_refuses_reused_receipt_hash :
    let receiptOnly : OutputRegistryState := {
      deploymentId := fixtureActivation.deploymentId
      revision := 9
      consumedCoordinates := ∅
      consumedReceiptHashes := {fixtureFinalizedPayload.finalized.receiptHash}
    }
    (match proposeOutputConsumption receiptOnly fixtureActivation fixtureFinalizedPayload
      fixtureDurableOutputAdmission with
    | .error error => error
    | .ok _ => .wrongDeployment) = .receiptReplay := by
  native_decide

private def fixtureSpecB : DailySpec := { fixtureSpec with dailyId := digestByte 174 }

private def fixtureActivationB : ActivatedDaily :=
  (admitDailyActivation fixtureActivationOracle fixtureActivationCapability
    fixtureActivation.deploymentId fixtureHolderPolicy.eventGenesisHead fixtureSpecB
    fixtureSignature).toOption.get (by native_decide)

private def fixtureDurableOutputAdmissionB :
    AdmittedDurableOutput fixtureActivationB fixtureFinalizedPayload :=
  (admitDurableOutput fixtureOutputOracle fixtureOutputCapability fixtureActivationB
    fixtureFinalizedPayload fixtureSignature).toOption.get (by native_decide)

theorem deployment_registry_refuses_cross_activation_coordinate_replay :
    (match proposeOutputConsumption fixtureOutputCandidate.after fixtureActivationB
      fixtureFinalizedPayload fixtureDurableOutputAdmissionB with
    | .error error => error
    | .ok _ => .wrongDeployment) = .coordinateReplay := by
  native_decide

theorem globally_consumed_output_can_record_exact_daily_output :
    (proposeDaily fixtureDigests fixtureCompletedSnapshot secureOutputEvent
      fixtureSecureOutputCommand).toOption.map (fun candidate =>
        decide (candidate.after.replay.projection.finalizedOutput =
          some fixtureFinalizedPayload)) = some true := by
  native_decide

theorem forged_finalized_judge_output_is_refused :
    let hostile := { fixtureFinalizedPayload with judgeOutput := "{}" }
    reduce fixtureSpec fixtureCompleted ⟨4, .recordFinalizedOutput hostile⟩ = none := by
  native_decide

theorem mismatched_contribution_contract_is_refused :
    let altered := { fixtureSpec with outputContribution := Contribution.zero }
    let completedUnderAltered : State :=
      ⟨altered, 3, .completed, HolderMechanics.initialState altered.holderPolicy,
        3, altered.procedure, {maintainerA}, ∅, [], [], 0, [],
        some altered.successContentId, none, none⟩
    reduce altered completedUnderAltered
      ⟨4, .recordFinalizedOutput fixtureFinalizedPayload⟩ = none := by
  native_decide

private def fixtureRecorded : State := fixtureReplay.toOption.get (by native_decide) |>.projection

theorem second_finalized_output_is_refused :
    reduce fixtureSpec fixtureRecorded
      ⟨7, .recordFinalizedOutput fixtureFinalizedPayload⟩ = none := by
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
#assert_axioms step_is_reduce
#assert_axioms genesisState_is_ballot
#assert_axioms genesisState_carries_its_spec
#assert_axioms admitted_holder_choir_delegates
#assert_axioms dregg_sponsorship_preserves_chamber_power
#assert_axioms successful_commons_visit_preserves_power
#assert_axioms commons_outcome_local_service_bounded
#assert_axioms PersistedDailyTransition.same_successor
#assert_axioms PersistedOutputRegistryTransition.same_successor
#assert_axioms PersistedOutputRegistryTransition.deployment_scoped
#assert_axioms PersistedDailyTransition.deployment_scoped
#assert_axioms DurableDailyLoad.exact
#assert_axioms DurableOutputRegistryLoad.exact
#assert_axioms DurableDailyLoad.rooted_exact
#assert_axioms DurableOutputRegistryLoad.rooted_exact
#assert_axioms DurableDailyLoad.revisionZero_same_genesis
#assert_axioms DurableOutputRegistryLoad.revisionZero_same_genesis
#assert_axioms OutputRegistryGenesisCertificate.same_root
#assert_axioms ActivatedDaily.exact
#assert_axioms ActivatedDaily.cap_pins_deployment_and_key
#assert_axioms admitPersistedDailyRuntime_wrong_cursor_version
#assert_axioms AdmittedDurableOutput.exact
#assert_axioms AdmittedDailyCommand.exact

#assert_compiled three_step_daily_replays_to_one_exact_finalized_output
#assert_compiled activation_with_wrong_genesis_head_is_refused
#assert_compiled candidate_spec_cannot_choose_its_own_activation_key
#assert_compiled activation_capability_pins_deployment_id
#assert_compiled public_ballot_event_delegates_to_holder_mechanics
#assert_compiled public_chamber_can_open_without_holder_veto
#assert_compiled wrong_authored_step_is_refused_without_advancing
#assert_compiled authored_rotation_repeats_deterministically
#assert_compiled unknown_commons_choice_is_refused_without_advancing
#assert_compiled one_commons_visit_per_player_is_enforced
#assert_compiled full_commons_choice_gives_authored_neighborly_alternative
#assert_compiled authored_commons_strategies_have_distinct_outcomes
#assert_compiled commons_visit_does_not_change_power_projection
#assert_compiled forged_maintainer_identity_is_refused_at_admission
#assert_compiled replayed_action_nullifier_is_refused_at_admission
#assert_compiled deployment_registry_candidate_binds_both_output_nullifiers
#assert_compiled deployment_registry_refuses_reused_receipt_hash
#assert_compiled deployment_registry_refuses_cross_activation_coordinate_replay
#assert_compiled globally_consumed_output_can_record_exact_daily_output
#assert_compiled premature_finalized_output_is_refused
#assert_compiled forged_finalized_judge_output_is_refused
#assert_compiled mismatched_contribution_contract_is_refused
#assert_compiled second_finalized_output_is_refused
#assert_compiled participant_event_after_ballot_phase_is_refused
#assert_compiled sourced_payload_sequence_mismatch_is_refused

end Dregg2.Games.PathOfAngels.GalleyMaintenanceDaily
