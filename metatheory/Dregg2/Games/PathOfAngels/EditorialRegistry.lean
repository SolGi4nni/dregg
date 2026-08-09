/-
# EditorialRegistry — exact beta research, curator-only continuity

This is an authority stress test, not a generic content database.  A provisional
requires both a closed Cartography judgment and an opaque adapter capability over
the exact finalized root, catalogue, notebook, and authored expedition keys.  The
editorial state lives under a private canonical deployment store with one head per
registry id, one selected exact origin, monotone revision and curator counters,
and append-only decision history.

No score, price, custody claim, reputation value, or audience vote inhabits the
curator capability.  The capability is indexed by the exact policy, store snapshot,
prestate, and faithful structural transcript.  The transition independently checks
the canonical head, registry/content identity, actor root, expected revision and
counter, then recomputes the successor root from the complete semantic successor
preimage.  The pure result becomes canonical only after the sealed runtime CAS
adapter issues its single-winner receipt.  State/store constructors are private;
browser/wire callers receive only deterministic projections.
-/
import Dregg2.Games.PathOfAngels.Cartography
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.EditorialRegistry

open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.Cartography
open Dregg2.Games.PathOfAngels.DeckGraph
open Dregg2.Games.PathOfAngels.DeckExpedition

set_option autoImplicit false

/-! ## Exact provisional research origin -/

/-- Exact upstream material authenticated before an editorial provisional can
exist.  The catalogue retains every authored observation and therefore every
expedition origin; the actions retain the exact notebook replay. -/
structure ProvisionalOriginTranscript where
  finalizedActorRoot : Digest32
  catalogue : CatalogueDigest
  playerKey : Digest32
  previousPlayerCounter : Nat
  actions : List Cartography.Action
  authoredOrigins : List ExpeditionKey
deriving DecidableEq

def authoredOrigins (config : Cartography.Config) : List ExpeditionKey :=
  config.raw.observations.map Observation.originKey

def provisionalOriginTranscript (config : Cartography.Config) (context : JudgeContext)
    (actions : List Cartography.Action) : ProvisionalOriginTranscript where
  finalizedActorRoot := context.actorRoot
  catalogue := config.raw.catalogueDigest
  playerKey := context.playerKey
  previousPlayerCounter := context.previousPlayerCounter
  actions
  authoredOrigins := authoredOrigins config

/-- Opaque evidence that the adapter authenticated the exact finalized
Cartography transcript and independently resolved its authored expedition keys.
There is deliberately no public producer. -/
structure ProvisionalOriginCapability (config : Cartography.Config) (context : JudgeContext)
    (actions : List Cartography.Action) where
  private mk ::
  verifierId : Digest32
  receiptIndexRoot : Digest32
  verificationReceipt : Digest32
  transcript : ProvisionalOriginTranscript
  resolvedOrigins : List ExpeditionKey
  transcript_exact : transcript = provisionalOriginTranscript config context actions
  origins_exact : resolvedOrigins = authoredOrigins config

theorem ProvisionalOriginCapability.exact {config : Cartography.Config}
    {context : JudgeContext} {actions : List Cartography.Action}
    (capability : ProvisionalOriginCapability config context actions) :
    capability.transcript = provisionalOriginTranscript config context actions ∧
      capability.resolvedOrigins = authoredOrigins config :=
  ⟨capability.transcript_exact, capability.origins_exact⟩

/-- Public, immutable view of the complete research object under review.  The
artifact alone is not its identity: the authenticated upstream transcript and
digest, catalogue, actor root, player counter, observations, connections, and
hazard claims all remain attached. -/
structure ProvisionalView where
  artifact : ArtifactRef
  catalogue : CatalogueDigest
  session : SessionKey
  originTranscript : ProvisionalOriginTranscript
  originVerifierId : Digest32
  originReceiptIndexRoot : Digest32
  originVerificationReceipt : Digest32
  provenance : List ObservationProvenance
  connections : Finset HotspotId
  hazardClaims : Finset HazardClaim
  disputedHazards : Finset HazardId
  federationId : Digest32
  contentRoot : Digest32
  activationDigest : Digest32
  contentSession : Digest32
  contentEpoch : EpochId
  missionId : MissionId
deriving DecidableEq

/-- A provisional is not receipt-shaped data.  Its private constructor retains
the successful public judge equation and the opaque authenticated-origin evidence
which was required before replay. -/
structure ProvisionalArtifact where
  private mk ::
  private config : Cartography.Config
  private context : JudgeContext
  private actions : List Cartography.Action
  private originAuthority : ProvisionalOriginCapability config context actions
  private revision : MapRevision config
  private judged : Cartography.judge config context actions = some revision

/-- Sole producer: authenticate the exact upstream origin transcript, then replay
the exact Cartography notebook from its counter-bound initial state.  A locally
replayed expedition receipt or Cartography judgment alone cannot call this API. -/
def judgeProvisional (config : Cartography.Config) (context : JudgeContext)
    (actions : List Cartography.Action)
    (authority : ProvisionalOriginCapability config context actions) : Option ProvisionalArtifact :=
  if authority.transcript != provisionalOriginTranscript config context actions then none
  else if authority.resolvedOrigins != authoredOrigins config then none
  else match h : Cartography.judge config context actions with
    | none => none
    | some revision => some ⟨config, context, actions, authority, revision, h⟩

def ProvisionalArtifact.view (provisional : ProvisionalArtifact) : ProvisionalView where
  artifact := provisional.revision.artifact
  catalogue := provisional.revision.session.catalogueDigest
  session := provisional.revision.session
  originTranscript := provisional.originAuthority.transcript
  originVerifierId := provisional.originAuthority.verifierId
  originReceiptIndexRoot := provisional.originAuthority.receiptIndexRoot
  originVerificationReceipt := provisional.originAuthority.verificationReceipt
  provenance := provisional.revision.provenance
  connections := provisional.revision.connections
  hazardClaims := provisional.revision.hazardClaims
  disputedHazards := provisional.revision.disputedHazards
  federationId := provisional.config.raw.mapPolicy.mission.federationId
  contentRoot := provisional.config.raw.mapPolicy.mission.contentRoot
  activationDigest := provisional.config.raw.mapPolicy.mission.activationDigest
  contentSession := provisional.config.raw.mapPolicy.mission.contentSession
  contentEpoch := provisional.config.raw.mapPolicy.mission.epoch
  missionId := provisional.config.raw.mapPolicy.mission.missionId

/-- Every admitted provisional exposes the exact successful opaque revision
origin, and its one beta artifact is precisely the projected artifact. -/
theorem ProvisionalArtifact.exact_judged_beta (provisional : ProvisionalArtifact) :
    Cartography.judge provisional.config provisional.context provisional.actions =
        some provisional.revision ∧
      provisional.revision.artifact = provisional.config.raw.revisionArtifact ∧
      provisional.revision.beta.betaCandidates = {provisional.view.artifact} := by
  refine ⟨provisional.judged, ?_⟩
  have exact := Cartography.judged_revision_has_exact_beta_artifact
    provisional.config provisional.context provisional.actions
    provisional.revision provisional.judged
  exact ⟨exact.1, exact.2.trans (by simp [ProvisionalArtifact.view, exact.1])⟩

theorem judgeProvisional_success_exact {config : Cartography.Config}
    {context : JudgeContext} {actions : List Cartography.Action}
    {authority : ProvisionalOriginCapability config context actions}
    {provisional : ProvisionalArtifact}
    (h : judgeProvisional config context actions authority = some provisional) :
    ∃ revision : MapRevision config,
      Cartography.judge config context actions = some revision ∧
      provisional.view.artifact = revision.artifact ∧
      revision.beta.betaCandidates = {provisional.view.artifact} := by
  unfold judgeProvisional at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  rename_i revision judged
  injection h with heq
  subst provisional
  refine ⟨revision, judged, rfl, ?_⟩
  exact (ProvisionalArtifact.exact_judged_beta
    ⟨config, context, actions, authority, revision, judged⟩).2.2

/-- Re-pin the upstream ADT boundary at the editorial import edge: an arbitrary
receipt-shaped value cannot be inserted into the provenance chain. -/
theorem expedition_receipt_constructor_remains_private : True :=
  Cartography.extraction_receipt_constructor_is_private

/-! ## Canonical registry identity, state, and store -/

structure RegistryIdentity where
  registryId : Digest32
  federationId : Digest32
  contentRoot : Digest32
  activationDigest : Digest32
  contentSession : Digest32
  contentEpoch : EpochId
deriving DecidableEq

inductive Decision where
  | promoted (selected : ProvisionalView)
  | superseded (previous replacement : ProvisionalView)
  | retracted (previous : ProvisionalView)
deriving DecidableEq

inductive EditorialAction where
  | promote (candidate : ProvisionalArtifact)
  | supersede (expected : ProvisionalView) (replacement : ProvisionalArtifact)
  | retract (expected : ProvisionalView)

def EditorialAction.view : EditorialAction → Decision
  | .promote candidate => .promoted candidate.view
  | .supersede expected replacement => .superseded expected replacement.view
  | .retract expected => .retracted expected

structure HistoryEntry where
  registryId : Digest32
  revision : PlayerCounter
  curatorCounter : PlayerCounter
  actorRoot : Digest32
  nextActorRoot : Digest32
  beforeSelection : Option ProvisionalView
  afterSelection : Option ProvisionalView
  decision : Decision
deriving DecidableEq

private structure StateData where
  identity : RegistryIdentity
  curatorKey : Digest32
  actorRoot : Digest32
  revision : PlayerCounter
  curatorCounter : PlayerCounter
  selected : Option ProvisionalView
  retired : Finset ProvisionalView
  history : List HistoryEntry
deriving DecidableEq

/-- The representation cannot be decoded, record-updated, or reconstructed from
a public projection.  Only verified genesis/step proposal preparation produces it;
canonical installation additionally requires a sealed CAS receipt. -/
structure RegistryState where
  private mk ::
  private data : StateData
deriving DecidableEq

structure PublicProjection where
  identity : RegistryIdentity
  curatorKey : Digest32
  actorRoot : Digest32
  revision : PlayerCounter
  curatorCounter : PlayerCounter
  selected : Option ProvisionalView
  retired : Finset ProvisionalView
  history : List HistoryEntry
deriving DecidableEq

def project (state : RegistryState) : PublicProjection where
  identity := state.data.identity
  curatorKey := state.data.curatorKey
  actorRoot := state.data.actorRoot
  revision := state.data.revision
  curatorCounter := state.data.curatorCounter
  selected := state.data.selected
  retired := state.data.retired
  history := state.data.history

/-- Faithful, finite deployment policy identity.  This is what a store proposal
persists; the executable function comes from the sealed implementation carrying
this id. -/
structure PolicyCommitment where
  identity : RegistryIdentity
  curatorKey : Digest32
  genesisActorRoot : Digest32
  authoredCatalogue : CatalogueDigest
  authoredMission : MissionId
  authoredArtifact : ArtifactRef
  actorRootImplementationId : Digest32
deriving DecidableEq

/-- Non-recursive exact preimage of registry genesis. -/
structure GenesisRootPreimage where
  policy : PolicyCommitment
deriving DecidableEq

/-- Exact semantic preimage of one successor.  It contains the entire predecessor
and every successor field except the root itself; the new history entry is
deterministically recoverable from these fields. -/
structure SuccessorRootPreimage where
  policy : PolicyCommitment
  priorActorRoot : Digest32
  priorRevision : PlayerCounter
  priorCuratorCounter : PlayerCounter
  priorSelection : Option ProvisionalView
  priorRetired : Finset ProvisionalView
  priorHistory : List HistoryEntry
  nextRevision : PlayerCounter
  nextCuratorCounter : PlayerCounter
  nextSelection : Option ProvisionalView
  nextRetired : Finset ProvisionalView
  decision : Decision
deriving DecidableEq

inductive ActorRootPreimage where
  | genesis (preimage : GenesisRootPreimage)
  | successor (preimage : SuccessorRootPreimage)
deriving DecidableEq

abbrev ActorRootOracle := ActorRootPreimage → Digest32

/-- Sealed resolver output.  Callers cannot pair a familiar implementation id
with substitute executable semantics: the id and function have one private
constructor and travel as one capability. -/
structure ActorRootImplementation where
  private mk ::
  implementationId : Digest32
  commit : ActorRootOracle

/-- Deployment policy pins the exact authored Cartography catalogue and the
identity of the actor-root commitment implementation. -/
structure Policy where
  identity : RegistryIdentity
  curatorKey : Digest32
  genesisActorRoot : Digest32
  authoredCatalogue : CatalogueDigest
  authoredMission : MissionId
  authoredArtifact : ArtifactRef
  rootImplementation : ActorRootImplementation

def catalogueRawConfig (catalogue : CatalogueDigest) : Cartography.RawConfig where
  mapPolicy := catalogue.mapPolicy
  revisionArtifact := catalogue.revisionArtifact
  source := catalogue.source
  bridge := catalogue.bridge
  observations := catalogue.observations
  operationBudget := catalogue.operationBudget

def policyValidB (policy : Policy) : Bool :=
  Cartography.configValidB (catalogueRawConfig policy.authoredCatalogue) &&
  decide (policy.authoredMission = policy.authoredCatalogue.mapPolicy.mission.missionId) &&
  decide (policy.authoredMission = policy.authoredCatalogue.bridge.mapMissionId) &&
  decide (policy.authoredArtifact = policy.authoredCatalogue.revisionArtifact) &&
  decide (policy.authoredArtifact ∈ policy.authoredCatalogue.mapPolicy.allowedBeta) &&
  decide (policy.identity.federationId =
    policy.authoredCatalogue.mapPolicy.mission.federationId) &&
  decide (policy.identity.contentRoot = policy.authoredCatalogue.mapPolicy.mission.contentRoot) &&
  decide (policy.identity.activationDigest =
    policy.authoredCatalogue.mapPolicy.mission.activationDigest) &&
  decide (policy.identity.contentSession =
    policy.authoredCatalogue.mapPolicy.mission.contentSession) &&
  decide (policy.identity.contentEpoch = policy.authoredCatalogue.mapPolicy.mission.epoch)

def policyCommitment (policy : Policy) : PolicyCommitment where
  identity := policy.identity
  curatorKey := policy.curatorKey
  genesisActorRoot := policy.genesisActorRoot
  authoredCatalogue := policy.authoredCatalogue
  authoredMission := policy.authoredMission
  authoredArtifact := policy.authoredArtifact
  actorRootImplementationId := policy.rootImplementation.implementationId

def genesisRootPreimage (policy : Policy) : GenesisRootPreimage where
  policy := policyCommitment policy

def authoredProvenance (policy : Policy) : List ObservationProvenance :=
  policy.authoredCatalogue.observations.map Observation.provenance

/-- Exact authored-origin admission.  Same-domain alternate catalogues, missions,
artifacts, and provenance rows are rejected. -/
def originViewMatchesPolicyB (policy : Policy) (view : ProvisionalView) : Bool :=
  decide (
    view.catalogue = policy.authoredCatalogue ∧
    view.session.catalogueDigest = policy.authoredCatalogue ∧
    view.originTranscript.catalogue = policy.authoredCatalogue ∧
    view.originTranscript.finalizedActorRoot = view.session.actorRoot ∧
    view.originTranscript.playerKey = view.session.playerKey ∧
    view.originTranscript.previousPlayerCounter + 1 = view.session.playerCounter ∧
    view.originTranscript.authoredOrigins =
      policy.authoredCatalogue.observations.map Observation.originKey ∧
    view.missionId = policy.authoredMission ∧
    view.session.missionId = policy.authoredMission ∧
    view.session.federationId = policy.identity.federationId ∧
    view.session.contentSession = policy.identity.contentSession ∧
    view.session.contentEpoch = policy.identity.contentEpoch ∧
    view.artifact = policy.authoredArtifact ∧
    view.federationId = policy.identity.federationId ∧
    view.contentRoot = policy.identity.contentRoot ∧
    view.activationDigest = policy.identity.activationDigest ∧
    view.contentSession = policy.identity.contentSession ∧
    view.contentEpoch = policy.identity.contentEpoch) &&
  !view.provenance.isEmpty &&
  view.provenance.all (fun origin => decide (origin ∈ authoredProvenance policy))

def originMatchesPolicyB (policy : Policy) (candidate : ProvisionalArtifact) : Bool :=
  originViewMatchesPolicyB policy candidate.view

/-- Everything signed by the curator adapter.  The exact next root is checked
against the semantic successor preimage rather than trusted as envelope data. -/
structure Envelope where
  registryId : Digest32
  federationId : Digest32
  contentRoot : Digest32
  activationDigest : Digest32
  contentSession : Digest32
  contentEpoch : EpochId
  signer : Digest32
  actorRoot : Digest32
  nextActorRoot : Digest32
  expectedRevision : PlayerCounter
  previousCounter : PlayerCounter
  counter : PlayerCounter
  action : EditorialAction

structure RegistryHead where
  registryId : Digest32
  policy : PolicyCommitment
  actorRoot : Digest32
  revision : PlayerCounter
deriving DecidableEq

def headFor? : List RegistryHead → Digest32 → Option RegistryHead
  | [], _ => none
  | head :: heads, registryId =>
      if head.registryId = registryId then some head else headFor? heads registryId

private def setHead : List RegistryHead → RegistryHead → List RegistryHead
  | [], replacement => [replacement]
  | head :: heads, replacement =>
      if head.registryId = replacement.registryId then replacement :: heads
      else head :: setHead heads replacement

/-- Pure deployment/head snapshot used to prepare an exact CAS request.  It is not
itself a claim about the runtime's mutable canonical database. -/
structure DeploymentStore where
  private mk ::
  sequence : Nat
  heads : List RegistryHead
deriving DecidableEq

structure StoreProjection where
  sequence : Nat
  heads : List RegistryHead
deriving DecidableEq

def projectStore (store : DeploymentStore) : StoreProjection :=
  ⟨store.sequence, store.heads⟩

inductive CasPurpose where
  | registryGenesis
  | editorialStep
deriving DecidableEq

/-- Exact request submitted to the runtime's canonical compare-and-swap adapter. -/
structure StoreCasRequest where
  purpose : CasPurpose
  expected : StoreProjection
  replacement : StoreProjection
deriving DecidableEq

def storeCasRequest (purpose : CasPurpose) (expected replacement : DeploymentStore) :
    StoreCasRequest :=
  ⟨purpose, projectStore expected, projectStore replacement⟩

/-- Sealed receipt issued only by the mutable persistence adapter after
`expected` matched the canonical store and `replacement` won the single CAS.
Lean intentionally cannot manufacture or linearize this event. -/
structure CanonicalCasCommit (request : StoreCasRequest) where
  private mk ::
  adapterId : Digest32
  observedCanonicalRoot : Digest32
  committedReplacementRoot : Digest32
  singleWinnerReceipt : Digest32

structure GenesisTranscript where
  beforeStore : StoreProjection
  identity : RegistryIdentity
  curatorKey : Digest32
  genesisActorRoot : Digest32
  authoredCatalogue : CatalogueDigest
  authoredMission : MissionId
  authoredArtifact : ArtifactRef
  actorRootImplementationId : Digest32
deriving DecidableEq

def genesisTranscript (store : DeploymentStore) (policy : Policy) : GenesisTranscript where
  beforeStore := projectStore store
  identity := policy.identity
  curatorKey := policy.curatorKey
  genesisActorRoot := policy.genesisActorRoot
  authoredCatalogue := policy.authoredCatalogue
  authoredMission := policy.authoredMission
  authoredArtifact := policy.authoredArtifact
  actorRootImplementationId := policy.rootImplementation.implementationId

/-- Exact authenticated one-shot deployment command.  The adapter must bind the
complete store snapshot and authored policy transcript. -/
structure GenesisCapability (store : DeploymentStore) (policy : Policy) where
  private mk ::
  issuerId : Digest32
  finalizedDeploymentRoot : Digest32
  verificationReceipt : Digest32
  transcript : GenesisTranscript
  transcript_exact : transcript = genesisTranscript store policy

theorem GenesisCapability.exact {store : DeploymentStore} {policy : Policy}
    (capability : GenesisCapability store policy) :
    capability.transcript = genesisTranscript store policy :=
  capability.transcript_exact

private def initialState (policy : Policy) : RegistryState :=
  ⟨{
    identity := policy.identity
    curatorKey := policy.curatorKey
    actorRoot := policy.genesisActorRoot
    revision := 0
    curatorCounter := 0
    selected := none
    retired := ∅
    history := []
  }⟩

/-- Pure one-shot genesis proposal.  It rejects an existing registry id and
computes the exact replacement store/state, but does not claim that persistence
accepted it. -/
structure OpenProposal where
  expectedStore : DeploymentStore
  replacementStore : DeploymentStore
  state : RegistryState
deriving DecidableEq

def OpenProposal.casRequest (proposal : OpenProposal) : StoreCasRequest :=
  storeCasRequest .registryGenesis proposal.expectedStore proposal.replacementStore

def prepareOpenRegistry (store : DeploymentStore) (policy : Policy)
    (capability : GenesisCapability store policy) : Option (DeploymentStore × RegistryState) :=
  if policyValidB policy != true then none
  else if capability.transcript != genesisTranscript store policy then none
  else if headFor? store.heads policy.identity.registryId |>.isSome then none
  else if policy.genesisActorRoot !=
      policy.rootImplementation.commit (.genesis (genesisRootPreimage policy)) then
    none
  else
    let state := initialState policy
    let head : RegistryHead :=
      ⟨policy.identity.registryId, policyCommitment policy,
        policy.genesisActorRoot, state.data.revision⟩
    some (⟨store.sequence + 1, head :: store.heads⟩, state)

def commitOpenRegistry (proposal : OpenProposal)
    (_commit : CanonicalCasCommit proposal.casRequest) : DeploymentStore × RegistryState :=
  (proposal.replacementStore, proposal.state)

def prepareOpenProposal (store : DeploymentStore) (policy : Policy)
    (capability : GenesisCapability store policy) : Option OpenProposal := do
  let (replacementStore, state) ← prepareOpenRegistry store policy capability
  some { expectedStore := store, replacementStore, state }

theorem openRegistry_existing_head_refused (store : DeploymentStore) (policy : Policy)
    (capability : GenesisCapability store policy)
    (opened : (headFor? store.heads policy.identity.registryId).isSome = true) :
    prepareOpenRegistry store policy capability = none := by
  simp [prepareOpenRegistry, opened]

def validateProjection (state : RegistryState) (claimed : PublicProjection) : Bool :=
  decide (project state = claimed)

theorem projection_deterministic (state : RegistryState) (left right : PublicProjection)
    (hl : project state = left) (hr : project state = right) : left = right := by
  rw [← hl, ← hr]

/-! ## Exact curator transcript, pure proposal, and sealed commit boundary -/

structure CuratorTranscript where
  beforeStore : StoreProjection
  beforeState : PublicProjection
  identity : RegistryIdentity
  curatorKey : Digest32
  authoredCatalogue : CatalogueDigest
  authoredMission : MissionId
  authoredArtifact : ArtifactRef
  actorRootImplementationId : Digest32
  registryId : Digest32
  federationId : Digest32
  contentRoot : Digest32
  activationDigest : Digest32
  contentSession : Digest32
  contentEpoch : EpochId
  signer : Digest32
  actorRoot : Digest32
  nextActorRoot : Digest32
  expectedRevision : PlayerCounter
  previousCounter : PlayerCounter
  counter : PlayerCounter
  action : Decision
deriving DecidableEq

def curatorTranscript (policy : Policy) (store : DeploymentStore) (state : RegistryState)
    (envelope : Envelope) : CuratorTranscript where
  beforeStore := projectStore store
  beforeState := project state
  identity := policy.identity
  curatorKey := policy.curatorKey
  authoredCatalogue := policy.authoredCatalogue
  authoredMission := policy.authoredMission
  authoredArtifact := policy.authoredArtifact
  actorRootImplementationId := policy.rootImplementation.implementationId
  registryId := envelope.registryId
  federationId := envelope.federationId
  contentRoot := envelope.contentRoot
  activationDigest := envelope.activationDigest
  contentSession := envelope.contentSession
  contentEpoch := envelope.contentEpoch
  signer := envelope.signer
  actorRoot := envelope.actorRoot
  nextActorRoot := envelope.nextActorRoot
  expectedRevision := envelope.expectedRevision
  previousCounter := envelope.previousCounter
  counter := envelope.counter
  action := envelope.action.view

/-- Opaque output of the curator signature/finality adapter.  Its private
constructor carries a faithful structural transcript, not a caller-selected tag. -/
structure CuratorCapability (policy : Policy) (store : DeploymentStore)
    (state : RegistryState) (envelope : Envelope) where
  private mk ::
  verifierId : Digest32
  finalizedTurnRoot : Digest32
  verificationReceipt : Digest32
  transcript : CuratorTranscript
  transcript_exact : transcript = curatorTranscript policy store state envelope

theorem CuratorCapability.exact {policy : Policy} {store : DeploymentStore}
    {state : RegistryState} {envelope : Envelope}
    (capability : CuratorCapability policy store state envelope) :
    capability.transcript = curatorTranscript policy store state envelope :=
  capability.transcript_exact

def canonicalHeadB (policy : Policy) (store : DeploymentStore) (state : RegistryState) : Bool :=
  match headFor? store.heads state.data.identity.registryId with
  | none => false
  | some head => decide (
      head.policy = policyCommitment policy ∧
      head.actorRoot = state.data.actorRoot ∧ head.revision = state.data.revision)

def authorityChecks (policy : Policy) (state : RegistryState) (envelope : Envelope) : Bool :=
  decide (
    state.data.identity = policy.identity ∧
    state.data.curatorKey = policy.curatorKey ∧
    envelope.registryId = policy.identity.registryId ∧
    envelope.federationId = policy.identity.federationId ∧
    envelope.contentRoot = policy.identity.contentRoot ∧
    envelope.activationDigest = policy.identity.activationDigest ∧
    envelope.contentSession = policy.identity.contentSession ∧
    envelope.contentEpoch = policy.identity.contentEpoch ∧
    envelope.signer = policy.curatorKey ∧
    envelope.actorRoot = state.data.actorRoot ∧
    envelope.expectedRevision = state.data.revision ∧
    envelope.previousCounter = state.data.curatorCounter)

private def actionTransition (policy : Policy) (state : RegistryState) :
    EditorialAction → Option (Option ProvisionalView × Finset ProvisionalView × Decision)
  | .promote candidate =>
      let view := candidate.view
      if originMatchesPolicyB policy candidate != true then none
      else if state.data.selected.isSome then none
      else if view ∈ state.data.retired then none
      else some (some view, state.data.retired, .promoted view)
  | .supersede expected replacement =>
      let view := replacement.view
      if originMatchesPolicyB policy replacement != true then none
      else if state.data.selected != some expected then none
      else if view = expected then none
      else if view ∈ state.data.retired then none
      else some (some view, insert expected state.data.retired,
        .superseded expected view)
  | .retract expected =>
      if state.data.selected != some expected then none
      else some (none, insert expected state.data.retired, .retracted expected)

def successorRootPreimage (policy : Policy) (state : RegistryState)
    (nextRevision nextCounter : PlayerCounter) (selected : Option ProvisionalView)
    (retired : Finset ProvisionalView) (decision : Decision) : SuccessorRootPreimage where
  policy := policyCommitment policy
  priorActorRoot := state.data.actorRoot
  priorRevision := state.data.revision
  priorCuratorCounter := state.data.curatorCounter
  priorSelection := state.data.selected
  priorRetired := state.data.retired
  priorHistory := state.data.history
  nextRevision := nextRevision
  nextCuratorCounter := nextCounter
  nextSelection := selected
  nextRetired := retired
  decision := decision

/-- Fully derived semantic successor.  `expectedRoot` is not supplied by the
envelope; it is recomputed from the complete successor preimage. -/
structure PreparedSuccessor where
  nextRevision : PlayerCounter
  nextCounter : PlayerCounter
  selected : Option ProvisionalView
  retired : Finset ProvisionalView
  decision : Decision
  preimage : SuccessorRootPreimage
  expectedRoot : Digest32
deriving DecidableEq

def prepareSuccessor? (policy : Policy) (state : RegistryState) (envelope : Envelope) :
    Option PreparedSuccessor := do
  let nextRevision ← state.data.revision.next
  let nextCounter ← state.data.curatorCounter.next
  if envelope.counter != nextCounter then none
  else do
    let (selected, retired, decision) ← actionTransition policy state envelope.action
    let preimage := successorRootPreimage policy state nextRevision nextCounter
      selected retired decision
    some {
      nextRevision
      nextCounter
      selected
      retired
      decision
      preimage
      expectedRoot := policy.rootImplementation.commit (.successor preimage)
    }

private def commit (policy : Policy) (state : RegistryState) (envelope : Envelope)
    (nextRevision nextCounter : PlayerCounter) (selected : Option ProvisionalView)
    (retired : Finset ProvisionalView) (decision : Decision) : RegistryState :=
  let entry : HistoryEntry := {
    registryId := policy.identity.registryId
    revision := nextRevision
    curatorCounter := nextCounter
    actorRoot := envelope.actorRoot
    nextActorRoot := envelope.nextActorRoot
    beforeSelection := state.data.selected
    afterSelection := selected
    decision
  }
  ⟨{
    identity := state.data.identity
    curatorKey := state.data.curatorKey
    actorRoot := envelope.nextActorRoot
    revision := nextRevision
    curatorCounter := nextCounter
    selected
    retired
    history := state.data.history ++ [entry]
  }⟩

/-- Pure editorial proposal.  It authenticates the full transcript, checks the
supplied expected state against the supplied store snapshot, and derives the exact
replacement.  The separate sealed CAS receipt is what says the runtime installed it. -/
def prepareStep (policy : Policy) (store : DeploymentStore) (state : RegistryState)
    (envelope : Envelope)
    (capability : CuratorCapability policy store state envelope) :
    Option (DeploymentStore × RegistryState) :=
  if policyValidB policy != true then none
  else if canonicalHeadB policy store state != true then none
  else if capability.transcript != curatorTranscript policy store state envelope then none
  else if authorityChecks policy state envelope != true then none
  else match prepareSuccessor? policy state envelope with
    | none => none
    | some prepared =>
      if envelope.nextActorRoot != prepared.expectedRoot then none
      else if envelope.nextActorRoot = envelope.actorRoot then none
      else
        let after := commit policy state envelope prepared.nextRevision prepared.nextCounter
          prepared.selected prepared.retired prepared.decision
        let nextHead : RegistryHead :=
          ⟨policy.identity.registryId, policyCommitment policy,
            after.data.actorRoot, after.data.revision⟩
        let storeAfter : DeploymentStore :=
          ⟨store.sequence + 1, setHead store.heads nextHead⟩
        some (storeAfter, after)

structure StepProposal where
  expectedStore : DeploymentStore
  replacementStore : DeploymentStore
  after : RegistryState
deriving DecidableEq

def StepProposal.casRequest (proposal : StepProposal) : StoreCasRequest :=
  storeCasRequest .editorialStep proposal.expectedStore proposal.replacementStore

def prepareStepProposal (policy : Policy) (store : DeploymentStore) (state : RegistryState)
    (envelope : Envelope) (capability : CuratorCapability policy store state envelope) :
    Option StepProposal := do
  let (replacementStore, after) ← prepareStep policy store state envelope capability
  some { expectedStore := store, replacementStore, after }

def commitStepProposal (proposal : StepProposal)
    (_commit : CanonicalCasCommit proposal.casRequest) : DeploymentStore × RegistryState :=
  (proposal.replacementStore, proposal.after)

/-- Every successful transition exposes the exact derived successor preimage and
commits precisely its oracle root into the returned state. -/
theorem step_successor_root_exact {policy : Policy} {store afterStore : DeploymentStore}
    {state after : RegistryState} {envelope : Envelope}
    {capability : CuratorCapability policy store state envelope}
    (h : prepareStep policy store state envelope capability = some (afterStore, after)) :
    ∃ prepared : PreparedSuccessor,
      prepareSuccessor? policy state envelope = some prepared ∧
      envelope.nextActorRoot = prepared.expectedRoot ∧
      (project after).actorRoot = envelope.nextActorRoot := by
  unfold prepareStep at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  rename_i prepared preparedExact rootExact rootMoves
  refine ⟨prepared, preparedExact, ?_, ?_⟩
  · simpa using rootExact
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    change after.data.actorRoot = envelope.nextActorRoot
    rw [← h.2]
    rfl

theorem step_deterministic {policy : Policy} {store : DeploymentStore}
    {state : RegistryState} {envelope : Envelope}
    {capability : CuratorCapability policy store state envelope}
    {left right : DeploymentStore × RegistryState}
    (hl : prepareStep policy store state envelope capability = some left)
    (hr : prepareStep policy store state envelope capability = some right) : left = right := by
  rw [hl] at hr
  exact Option.some.inj hr

theorem history_deletion_projection_refused (state : RegistryState)
    (claimed : PublicProjection)
    (deleted : claimed.history ≠ (project state).history) :
    validateProjection state claimed = false := by
  simp [validateProjection]
  intro equal
  apply deleted
  exact congrArg PublicProjection.history equal.symm

theorem step_noncanonical_head_refused (policy : Policy) (store : DeploymentStore)
    (state : RegistryState) (envelope : Envelope)
    (capability : CuratorCapability policy store state envelope)
    (stale : canonicalHeadB policy store state ≠ true) :
    prepareStep policy store state envelope capability = none := by
  simp [prepareStep, stale]

theorem step_wrong_revision_refused (policy : Policy) (store : DeploymentStore)
    (state : RegistryState) (envelope : Envelope)
    (capability : CuratorCapability policy store state envelope)
    (stale : envelope.expectedRevision ≠ (project state).revision) :
    prepareStep policy store state envelope capability = none := by
  have staleData : envelope.expectedRevision ≠ state.data.revision := by
    simpa [project] using stale
  simp [prepareStep, authorityChecks, staleData]

theorem step_wrong_content_epoch_refused (policy : Policy) (store : DeploymentStore)
    (state : RegistryState) (envelope : Envelope)
    (capability : CuratorCapability policy store state envelope)
    (wrong : envelope.contentEpoch ≠ policy.identity.contentEpoch) :
    prepareStep policy store state envelope capability = none := by
  simp [prepareStep, authorityChecks, wrong]

theorem cross_registry_replay_refused (policy : Policy) (store : DeploymentStore)
    (state : RegistryState) (envelope : Envelope)
    (capability : CuratorCapability policy store state envelope)
    (wrong : envelope.registryId ≠ policy.identity.registryId) :
    prepareStep policy store state envelope capability = none := by
  simp [prepareStep, authorityChecks, wrong]

theorem cross_content_replay_refused (policy : Policy) (store : DeploymentStore)
    (state : RegistryState) (envelope : Envelope)
    (capability : CuratorCapability policy store state envelope)
    (wrong : envelope.contentRoot ≠ policy.identity.contentRoot) :
    prepareStep policy store state envelope capability = none := by
  simp [prepareStep, authorityChecks, wrong]

/-! ## Non-editor influence cannot exercise authority -/

inductive AuthorityAttempt (policy : Policy) (store : DeploymentStore)
    (state : RegistryState) (envelope : Envelope) where
  | editor (capability : CuratorCapability policy store state envelope)
  | popularity (audienceCount : Nat)
  | marketPrice (quotedPrice : Nat)
  | custody (claimedHolder : Digest32)
  | reputation (score : Nat)
  | poll (yesVotes noVotes : Nat)

def submitAttempt (policy : Policy) (store : DeploymentStore) (state : RegistryState)
    (envelope : Envelope) :
    AuthorityAttempt policy store state envelope → Option (DeploymentStore × RegistryState)
  | .editor capability => prepareStep policy store state envelope capability
  | .popularity _ => none
  | .marketPrice _ => none
  | .custody _ => none
  | .reputation _ => none
  | .poll _ _ => none

theorem popularity_cannot_promote (policy : Policy) (store : DeploymentStore) (state : RegistryState)
    (envelope : Envelope) (audienceCount : Nat) :
    submitAttempt policy store state envelope (.popularity audienceCount) = none := rfl

theorem item_price_cannot_promote (policy : Policy) (store : DeploymentStore) (state : RegistryState)
    (envelope : Envelope) (quotedPrice : Nat) :
    submitAttempt policy store state envelope (.marketPrice quotedPrice) = none := rfl

theorem custody_cannot_promote (policy : Policy) (store : DeploymentStore) (state : RegistryState)
    (envelope : Envelope) (holder : Digest32) :
    submitAttempt policy store state envelope (.custody holder) = none := rfl

theorem reputation_cannot_promote (policy : Policy) (store : DeploymentStore) (state : RegistryState)
    (envelope : Envelope) (score : Nat) :
    submitAttempt policy store state envelope (.reputation score) = none := rfl

theorem poll_tally_cannot_promote (policy : Policy) (store : DeploymentStore) (state : RegistryState)
    (envelope : Envelope) (yesVotes noVotes : Nat) :
    submitAttempt policy store state envelope (.poll yesVotes noVotes) = none := rfl

/-- A browser may name an artifact and fabricate provenance-shaped fields, but
there is deliberately no conversion to the private provisional type. -/
structure UntrustedBetaClaim where
  artifact : ArtifactRef
  claimedCatalogue : CatalogueDigest
  claimedMission : MissionId
  claimedOrigin : ExpeditionKey
  claimedContentRoot : Digest32
  claimedActivationDigest : Digest32
  claimedEpoch : EpochId
deriving DecidableEq

def submitUntrustedBetaClaim (_policy : Policy) (_store : DeploymentStore)
    (_state : RegistryState) (_claim : UntrustedBetaClaim) :
    Option (DeploymentStore × RegistryState) := none

theorem forged_beta_artifact_is_refused (policy : Policy) (store : DeploymentStore)
    (state : RegistryState) (claim : UntrustedBetaClaim) :
    submitUntrustedBetaClaim policy store state claim = none := rfl

/-! ## Executable editorial fixture

⚑ **THE FIXTURE NO LONGER EVALUATES IN THIS MODULE (2026-08-08).** This module is in the
`Dregg2.FFI` closure — the crypto archive's build — and a `native_decide` here made every
game-fixture regression a hard failure of every Rust proving target. The fixture's
STATEMENTS stay here, each as an evaluation-free `check_* : Bool` definition, because they
must see the private editorial machinery (`fixturePolicy`, `fixtureStore`, `fixtureInitial`,
the sealed capabilities). The EVALUATION — each `check_* = true`, pinned by `native_decide`
+ `#assert_compiled` — lives in `EditorialRegistryFixtures.lean`, rooted in the
`PathOfAngelsGuards` library: a plain `lake build` still runs every pin, and a stale
fixture reds the guard library instead of the archive.

Fail-closed convention: `fixtureStore`/`fixtureInitial` match on `fixtureOpened?` and fall
back to the pre-genesis store/state — unreachable while `check_fixture_registry_opens`
pins true, and an inert refusal magnet if a regression ever made genesis refuse.

⚠ Named residue, two construction proofs: `fixture_provisionalA_exists` and
`fixture_provisionalB_exists` stay `native_decide` HERE because `ProvisionalArtifact` has a
private proof-carrying constructor with no in-module fallback inhabitant — `fixtureA` and
`fixtureB` (which the whole fixture universe consumes) can only be obtained through
`Option.get` over the successful judgment. Breaking either judgment therefore still reds
this module (and the archive). Everything else moved. -/

private def fixtureOriginCapability (config : Cartography.Config) (context : JudgeContext)
    (actions : List Cartography.Action) : ProvisionalOriginCapability config context actions :=
  let transcript := provisionalOriginTranscript config context actions
  {
    verifierId := Cartography.digestFilled 87
    receiptIndexRoot := Cartography.digestFilled 88
    verificationReceipt := Cartography.digestFilled 89
    transcript
    resolvedOrigins := authoredOrigins config
    transcript_exact := rfl
    origins_exact := rfl
  }

private def fixtureProvisionalA? : Option ProvisionalArtifact :=
  judgeProvisional Cartography.fixtureConfig Cartography.fixtureContext
    Cartography.cooperativeActions
    (fixtureOriginCapability Cartography.fixtureConfig Cartography.fixtureContext
      Cartography.cooperativeActions)

private def fixtureProvisionalB? : Option ProvisionalArtifact :=
  judgeProvisional Cartography.fixtureConfig Cartography.fixtureContext
    Cartography.presentOnlyActions
    (fixtureOriginCapability Cartography.fixtureConfig Cartography.fixtureContext
      Cartography.presentOnlyActions)

/-- Both provisionals judge successfully. (Pinned `= true` in `EditorialRegistryFixtures`;
the construction proofs below are the named residue that already forces this.) -/
def check_fixture_provisionals_exist : Bool :=
  fixtureProvisionalA?.isSome && fixtureProvisionalB?.isSome

/-- Named residue: `ProvisionalArtifact` has no in-module fallback inhabitant, so the
`Option.get` constructions below need these proofs as data at elaboration. -/
private theorem fixture_provisionalA_exists : fixtureProvisionalA?.isSome = true := by
  native_decide

private theorem fixture_provisionalB_exists : fixtureProvisionalB?.isSome = true := by
  native_decide

private def fixtureA : ProvisionalArtifact :=
  fixtureProvisionalA?.get fixture_provisionalA_exists

private def fixtureB : ProvisionalArtifact :=
  fixtureProvisionalB?.get fixture_provisionalB_exists

private def fixtureIdentity : RegistryIdentity where
  registryId := Cartography.digestFilled 90
  federationId := fixtureA.view.federationId
  contentRoot := fixtureA.view.contentRoot
  activationDigest := fixtureA.view.activationDigest
  contentSession := fixtureA.view.contentSession
  contentEpoch := fixtureA.view.contentEpoch

private def fixtureActorRootOracle : ActorRootOracle
  | .genesis _ => Cartography.digestFilled 92
  | .successor preimage =>
      match preimage.decision with
      | .promoted selected =>
          if selected = fixtureA.view then Cartography.digestFilled 93
          else Cartography.digestFilled 94
      | .superseded _ _ => Cartography.digestFilled 95
      | .retracted _ => Cartography.digestFilled 96

private def fixtureRootImplementation : ActorRootImplementation :=
  ⟨Cartography.digestFilled 97, fixtureActorRootOracle⟩

private def fixturePolicy : Policy where
  identity := fixtureIdentity
  curatorKey := Cartography.digestFilled 91
  genesisActorRoot := Cartography.digestFilled 92
  authoredCatalogue := Cartography.fixtureConfig.raw.catalogueDigest
  authoredMission := Cartography.fixtureConfig.raw.mapPolicy.mission.missionId
  authoredArtifact := Cartography.fixtureConfig.raw.revisionArtifact
  rootImplementation := fixtureRootImplementation

/-- (Pinned `= true` in `EditorialRegistryFixtures`.) -/
def check_fixture_policy_valid : Bool := policyValidB fixturePolicy

private def fixtureEmptyStore : DeploymentStore := ⟨0, []⟩

/-- Test-only stand-in for the runtime's sealed single-winner persistence receipt. -/
private def fixtureCasCommit (request : StoreCasRequest) : CanonicalCasCommit request :=
  ⟨Cartography.digestFilled 103, Cartography.digestFilled 104,
    Cartography.digestFilled 105, Cartography.digestFilled 106⟩

private def fixtureGenesisCapability (store : DeploymentStore) :
    GenesisCapability store fixturePolicy :=
  let transcript := genesisTranscript store fixturePolicy
  {
    issuerId := Cartography.digestFilled 98
    finalizedDeploymentRoot := Cartography.digestFilled 99
    verificationReceipt := Cartography.digestFilled 100
    transcript
    transcript_exact := rfl
  }

private def fixtureOpenProposal? : Option OpenProposal :=
  prepareOpenProposal fixtureEmptyStore fixturePolicy
    (fixtureGenesisCapability fixtureEmptyStore)

private def fixtureOpened? : Option (DeploymentStore × RegistryState) := do
  let proposal ← fixtureOpenProposal?
  some (commitOpenRegistry proposal (fixtureCasCommit proposal.casRequest))

/-- Genesis + sealed CAS receipt opens the registry.
(Pinned `= true` in `EditorialRegistryFixtures`.) -/
def check_fixture_registry_opens : Bool := fixtureOpened?.isSome

private def fixtureStore : DeploymentStore :=
  match fixtureOpened? with
  | some result => result.1
  | none => fixtureEmptyStore  -- unreachable while `check_fixture_registry_opens` pins true

private def fixtureInitial : RegistryState :=
  match fixtureOpened? with
  | some result => result.2
  | none => initialState fixturePolicy  -- unreachable while `check_fixture_registry_opens` pins true

private def fixtureCuratorCapabilityFor (policy : Policy) (store : DeploymentStore)
    (state : RegistryState) (envelope : Envelope) :
    CuratorCapability policy store state envelope :=
  let transcript := curatorTranscript policy store state envelope
  {
    verifierId := Cartography.digestFilled 101
    finalizedTurnRoot := envelope.actorRoot
    verificationReceipt := Cartography.digestFilled 102
    transcript
    transcript_exact := rfl
  }

private def fixtureCuratorCapability (store : DeploymentStore) (state : RegistryState)
    (envelope : Envelope) : CuratorCapability fixturePolicy store state envelope :=
  fixtureCuratorCapabilityFor fixturePolicy store state envelope

private def fixtureCommittedStep? (policy : Policy) (store : DeploymentStore)
    (state : RegistryState) (envelope : Envelope)
    (capability : CuratorCapability policy store state envelope) :
    Option (DeploymentStore × RegistryState) := do
  let proposal ← prepareStepProposal policy store state envelope capability
  some (commitStepProposal proposal (fixtureCasCommit proposal.casRequest))

private def promoteA : Envelope where
  registryId := fixtureIdentity.registryId
  federationId := fixtureIdentity.federationId
  contentRoot := fixtureIdentity.contentRoot
  activationDigest := fixtureIdentity.activationDigest
  contentSession := fixtureIdentity.contentSession
  contentEpoch := fixtureIdentity.contentEpoch
  signer := fixturePolicy.curatorKey
  actorRoot := fixturePolicy.genesisActorRoot
  nextActorRoot := Cartography.digestFilled 93
  expectedRevision := 0
  previousCounter := 0
  counter := 1
  action := .promote fixtureA

private def afterPromoteA? : Option (DeploymentStore × RegistryState) :=
  fixtureCommittedStep? fixturePolicy fixtureStore fixtureInitial promoteA
    (fixtureCuratorCapability fixtureStore fixtureInitial promoteA)

private def competingPromoteB : Envelope :=
  { promoteA with
    nextActorRoot := Cartography.digestFilled 94
    action := .promote fixtureB }

private def supersedeAWithB : Envelope where
  registryId := fixtureIdentity.registryId
  federationId := fixtureIdentity.federationId
  contentRoot := fixtureIdentity.contentRoot
  activationDigest := fixtureIdentity.activationDigest
  contentSession := fixtureIdentity.contentSession
  contentEpoch := fixtureIdentity.contentEpoch
  signer := fixturePolicy.curatorKey
  actorRoot := Cartography.digestFilled 93
  nextActorRoot := Cartography.digestFilled 95
  expectedRevision := 1
  previousCounter := 1
  counter := 2
  action := .supersede fixtureA.view fixtureB

private def afterSupersede? : Option (DeploymentStore × RegistryState) := do
  let (store, promoted) ← afterPromoteA?
  fixtureCommittedStep? fixturePolicy store promoted supersedeAWithB
    (fixtureCuratorCapability store promoted supersedeAWithB)

private def retractB : Envelope where
  registryId := fixtureIdentity.registryId
  federationId := fixtureIdentity.federationId
  contentRoot := fixtureIdentity.contentRoot
  activationDigest := fixtureIdentity.activationDigest
  contentSession := fixtureIdentity.contentSession
  contentEpoch := fixtureIdentity.contentEpoch
  signer := fixturePolicy.curatorKey
  actorRoot := Cartography.digestFilled 95
  nextActorRoot := Cartography.digestFilled 96
  expectedRevision := 2
  previousCounter := 2
  counter := 3
  action := .retract fixtureB.view

private def afterRetraction? : Option (DeploymentStore × RegistryState) := do
  let (store, superseded) ← afterSupersede?
  fixtureCommittedStep? fixturePolicy store superseded retractB
    (fixtureCuratorCapability store superseded retractB)

private def promotionProbe : Option Bool :=
  afterPromoteA?.map fun result =>
    let state := result.2
    decide ((project state).selected = some fixtureA.view) &&
    decide ((project state).history.length = 1) &&
    decide ((project state).revision.val = 1) &&
    decide ((project state).curatorCounter.val = 1)

/-- (Pinned `= true` in `EditorialRegistryFixtures`.) -/
def check_fixture_promotion_selects_exact_origin : Bool :=
  decide (promotionProbe = some true)

private def competingPromotionProbe : Option Bool :=
  afterPromoteA?.map fun result =>
    let storeAfter := result.1
    (prepareStep fixturePolicy storeAfter fixtureInitial competingPromoteB
      (fixtureCuratorCapability storeAfter fixtureInitial competingPromoteB)).isNone

/-- Once one same-head command wins, a freshly authenticated competing command
against the old state is refused by the moved canonical head.
(Pinned `= true` in `EditorialRegistryFixtures`.) -/
def check_competing_promotion_at_same_revision_is_refused : Bool :=
  decide (competingPromotionProbe = some true)

/-- Honest boundary witness: pure proposal evaluation is non-linear.  The same old
snapshot can prepare two forks; only the external sealed CAS issuer may choose one
and it must issue at most one `CanonicalCasCommit`.
(Pinned `= true` in `EditorialRegistryFixtures`.) -/
def check_same_old_snapshot_prepares_competing_forks : Bool :=
  (prepareStep fixturePolicy fixtureStore fixtureInitial promoteA
    (fixtureCuratorCapability fixtureStore fixtureInitial promoteA)).isSome &&
  (prepareStep fixturePolicy fixtureStore fixtureInitial competingPromoteB
    (fixtureCuratorCapability fixtureStore fixtureInitial competingPromoteB)).isSome

/-- (Pinned `= true` in `EditorialRegistryFixtures`.) -/
def check_repeated_genesis_is_refused : Bool :=
  (prepareOpenRegistry fixtureStore fixturePolicy
    (fixtureGenesisCapability fixtureStore)).isNone

private def arbitraryRootEnvelope : Envelope :=
  { promoteA with nextActorRoot := Cartography.digestFilled 250 }

/-- (Pinned `= true` in `EditorialRegistryFixtures`.) -/
def check_arbitrary_successor_root_is_refused : Bool :=
  (prepareStep fixturePolicy fixtureStore fixtureInitial arbitraryRootEnvelope
    (fixtureCuratorCapability fixtureStore fixtureInitial arbitraryRootEnvelope)).isNone

private def staleSupersession : Envelope :=
  { supersedeAWithB with expectedRevision := 0 }

private def staleSupersessionProbe : Option Bool :=
  afterPromoteA?.map fun result =>
    let store := result.1
    let state := result.2
    (prepareStep fixturePolicy store state staleSupersession
      (fixtureCuratorCapability store state staleSupersession)).isNone

/-- (Pinned `= true` in `EditorialRegistryFixtures`.) -/
def check_stale_supersession_is_refused : Bool :=
  decide (staleSupersessionProbe = some true)

private def supersessionProbe : Option Bool :=
  afterSupersede?.map fun result =>
    let state := result.2
    decide ((project state).selected = some fixtureB.view) &&
    decide (fixtureA.view ∈ (project state).retired) &&
    decide ((project state).history.length = 2)

/-- (Pinned `= true` in `EditorialRegistryFixtures`.) -/
def check_exact_supersession_preserves_prior_history : Bool :=
  decide (supersessionProbe = some true)

private def retractionProbe : Option Bool :=
  afterRetraction?.map fun result =>
    let state := result.2
    decide ((project state).selected = none) &&
    decide (fixtureA.view ∈ (project state).retired) &&
    decide (fixtureB.view ∈ (project state).retired) &&
    decide ((project state).history.length = 3)

/-- (Pinned `= true` in `EditorialRegistryFixtures`.) -/
def check_retraction_keeps_all_prior_history : Bool :=
  decide (retractionProbe = some true)

private def wrongEpochEnvelope : Envelope :=
  { promoteA with contentEpoch := ⟨fixtureIdentity.contentEpoch.value + 1⟩ }

/-- (Pinned `= true` in `EditorialRegistryFixtures`.) -/
def check_wrong_content_epoch_is_refused : Bool :=
  (prepareStep fixturePolicy fixtureStore fixtureInitial wrongEpochEnvelope
    (fixtureCuratorCapability fixtureStore fixtureInitial wrongEpochEnvelope)).isNone

private def crossContentEnvelope : Envelope :=
  { promoteA with contentRoot := Cartography.digestFilled 200 }

/-- (Pinned `= true` in `EditorialRegistryFixtures`.) -/
def check_cross_content_envelope_replay_is_refused : Bool :=
  (prepareStep fixturePolicy fixtureStore fixtureInitial crossContentEnvelope
    (fixtureCuratorCapability fixtureStore fixtureInitial crossContentEnvelope)).isNone

/-- (Pinned `= true` in `EditorialRegistryFixtures`.) -/
def check_alternate_catalogue_and_mission_are_refused : Bool :=
  !(originViewMatchesPolicyB fixturePolicy
    { fixtureA.view with catalogue := Cartography.reorderedCatalogueConfig.raw.catalogueDigest })
  && !(originViewMatchesPolicyB fixturePolicy
    { fixtureA.view with missionId := ⟨fixtureA.view.missionId.value + 1⟩ })

private def alternateCataloguePolicy : Policy :=
  { fixturePolicy with
    authoredCatalogue := Cartography.reorderedCatalogueConfig.raw.catalogueDigest }

/-- (Pinned `= true` in `EditorialRegistryFixtures`.) -/
def check_canonical_head_refuses_alternate_catalogue_policy : Bool :=
  (prepareStep alternateCataloguePolicy fixtureStore fixtureInitial promoteA
    (fixtureCuratorCapabilityFor alternateCataloguePolicy fixtureStore fixtureInitial
      promoteA)).isNone

/-- The old `fabricatedOrigin` def reached through `roomObservation?.get (by native_decide)`;
the probe folds that prerequisite into a fail-closed `map`, so a missing room observation
answers `false` in the guard library instead of wedging this module. -/
private def fabricatedOriginProbe : Option Bool :=
  Cartography.roomObservation?.map fun room =>
    let authentic := Observation.provenance room
    let fabricated : ObservationProvenance :=
      { authentic with originKey := { authentic.originKey with counter := 999_999 } }
    !(originViewMatchesPolicyB fixturePolicy
      { fixtureA.view with provenance := [fabricated] })

/-- (Pinned `= true` in `EditorialRegistryFixtures`.) -/
def check_fabricated_unreachable_receipt_is_refused : Bool :=
  decide (fabricatedOriginProbe = some true)

#assert_axioms ProvisionalArtifact.exact_judged_beta
#assert_axioms judgeProvisional_success_exact
#assert_axioms expedition_receipt_constructor_remains_private
#assert_axioms ProvisionalOriginCapability.exact
#assert_axioms GenesisCapability.exact
#assert_axioms CuratorCapability.exact
#assert_axioms openRegistry_existing_head_refused
#assert_axioms projection_deterministic
#assert_axioms step_successor_root_exact
#assert_axioms step_deterministic
#assert_axioms history_deletion_projection_refused
#assert_axioms step_noncanonical_head_refused
#assert_axioms step_wrong_revision_refused
#assert_axioms step_wrong_content_epoch_refused
#assert_axioms cross_registry_replay_refused
#assert_axioms cross_content_replay_refused
#assert_axioms popularity_cannot_promote
#assert_axioms item_price_cannot_promote
#assert_axioms custody_cannot_promote
#assert_axioms reputation_cannot_promote
#assert_axioms poll_tally_cannot_promote
#assert_axioms forged_beta_artifact_is_refused

-- The sixteen fixture pins (`#assert_compiled` + `native_decide`) live in
-- `EditorialRegistryFixtures.lean`, rooted in `PathOfAngelsGuards` — see the fixture
-- header above. Named residue staying here: `fixture_provisionalA_exists`,
-- `fixture_provisionalB_exists` (private construction proofs for `fixtureA`/`fixtureB`).

end Dregg2.Games.PathOfAngels.EditorialRegistry
