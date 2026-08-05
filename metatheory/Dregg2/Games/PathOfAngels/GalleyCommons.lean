/-
# Galley Commons — settled public-goods play aboard the Khovokhi

The reconstitution vat consumes canon-settled activity credits, not receipt-shaped
claims. `SettledRun` has a private constructor in `Canon`; `GalleyCredit` also has a
private constructor and can only be projected from one of those settled values.
It retains the complete authority domain and derives its one admissible `PoolId`
from immutable receipt fields. A settlement therefore cannot cross-spend into a
fresh pool with a different deployment identity.

Players asynchronously contribute exact supply/cohesion credits to a bounded
epoch pool. A finalized governance envelope chooses an authored recipe, allocation
and batch size. Eligible players claim at most one ration; after the authored
claim deadline a finalized-epoch capability may advance the pool and records any
unclaimed batch as ordinary commons consumption. A collecting epoch that cannot
finish may roll over after its authored deadline under exact consensus finality;
settled resources carry forward while global receipt nullifiers remain consumed.
There is no streak state and a gap of any positive size changes no economic projection.

The raw evaluator is private. Public proposals begin from an opaque persisted
runtime and validate pool/config identity, both conservation laws, exact state
sequence, actor counter, action authority and successor. Their raw candidate
cannot continue execution: only an exact whole-store CAS receipt can produce the
next persisted runtime. Consensus finality uses a distinct opaque capability and
key and certifies the exact canonical store/head; governance cannot self-certify
a free-floating future epoch.

Recipes emit only predeclared candidate artifacts. Importing `Canon` supplies the
settlement type; this module exposes no promotion or canon-status operation.
-/
import Dregg2.Games.PathOfAngels.Canon
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.GalleyCommons

open Dregg2.Games.PathOfAngels

set_option autoImplicit false

abbrev MAX_MEMBERS : Nat := 32
abbrev MAX_RECIPES : Nat := 16
abbrev MAX_SOURCES : Nat := 32
abbrev MAX_CANDIDATES : Nat := 64
abbrev MAX_RECEIPTS_PER_EPOCH : Nat := 64

/-! ## Deployment identity and settled credits -/

/-- Opaque deployment-admission provenance.  The host issues a distinct token
for one exact `AdmissionOracle` implementation.  Admitted objects retain this
token, and pool state refuses values from another admission session even when
both oracles accept the same bytes or advertise the same public ids. -/
structure AdmissionProvenance where
  private mk ::
  tokenDigest : Digest32
deriving DecidableEq

/-- A logical pool is one deployment, not one in-memory state snapshot.  Every
field is recoverable from a settled receipt; `deploymentDigest` is the activated
source artifact's exact content digest. -/
structure PoolId where
  federationId : Digest32
  contentRoot : Digest32
  activationDigest : Digest32
  contentSession : Digest32
  deploymentDigest : Digest32
deriving DecidableEq

def poolIdOfReceipt (receipt : RunReceipt) : PoolId where
  federationId := receipt.federationId
  contentRoot := receipt.contentRoot
  activationDigest := receipt.activationDigest
  contentSession := receipt.contentSession
  deploymentDigest := receipt.mission.artifact.contentDigest

/-- Private settled-credit projection.  The redundant fields are intentional:
wire/runtime adapters can bind every value without reopening the nested evidence. -/
structure GalleyCredit where
  private mk ::
  private settled : SettledRun
  admissionProvenance : AdmissionProvenance
  poolId : PoolId
  contentRoot : Digest32
  activationDigest : Digest32
  sourceMission : MissionId
  runSeed : Digest32
  federationId : Digest32
  contentSession : Digest32
  contentEpoch : EpochId
  playerKey : Digest32
  previousPlayerCounter : Nat
  playerCounter : Nat
  counterKey : PlayerCounterKey
  receiptKey : ReceiptKey
  contribution : Contribution

/-- The only credit constructor accepts Canon's private-constructor settlement. -/
private def creditFromSettled (provenance : AdmissionProvenance)
    (settled : SettledRun) : GalleyCredit :=
  let receipt := settled.judged.receipt
  {
    settled
    admissionProvenance := provenance
    poolId := poolIdOfReceipt receipt
    contentRoot := receipt.contentRoot
    activationDigest := receipt.activationDigest
    sourceMission := receipt.mission.missionId
    runSeed := receipt.runSeed
    federationId := receipt.federationId
    contentSession := receipt.contentSession
    contentEpoch := receipt.contentEpoch
    playerKey := receipt.playerKey
    previousPlayerCounter := receipt.previousPlayerCounter
    playerCounter := receipt.playerCounter
    counterKey := receipt.counterKey
    receiptKey := receipt.key
    contribution := receipt.contribution
  }

theorem credit_exact_pool (provenance : AdmissionProvenance) (settled : SettledRun) :
    (creditFromSettled provenance settled).poolId = poolIdOfReceipt settled.judged.receipt := rfl

theorem credit_exact_receipt_key (provenance : AdmissionProvenance) (settled : SettledRun) :
    (creditFromSettled provenance settled).receiptKey = settled.judged.receipt.key := rfl

theorem credit_exact_counter_key (provenance : AdmissionProvenance) (settled : SettledRun) :
    (creditFromSettled provenance settled).counterKey = settled.judged.receipt.counterKey := rfl

theorem credit_retains_settled_domain (provenance : AdmissionProvenance)
    (settled : SettledRun) :
    let credit := creditFromSettled provenance settled
    credit.contentRoot = settled.judged.receipt.contentRoot ∧
    credit.activationDigest = settled.judged.receipt.activationDigest ∧
    credit.sourceMission = settled.judged.receipt.mission.missionId ∧
    credit.runSeed = settled.judged.receipt.runSeed ∧
    credit.federationId = settled.judged.receipt.federationId ∧
    credit.contentSession = settled.judged.receipt.contentSession ∧
    credit.contentEpoch = settled.judged.receipt.contentEpoch ∧
    credit.playerKey = settled.judged.receipt.playerKey ∧
    credit.playerCounter = settled.judged.receipt.playerCounter := by
  simp [creditFromSettled]

/-! ## Authored policy -/

structure RecipeId where
  value : Nat
deriving DecidableEq, Repr

inductive Allocation where
  | openCommons
  | contributorsFirst
  | cohesionCrew
deriving DecidableEq, Repr

structure SourcePolicy where
  mission : MissionId
  runSeed : Digest32
deriving DecidableEq

structure Recipe where
  id : RecipeId
  supplyPerRation : Nat
  cohesionCost : Nat
  maxBatch : Nat
  minContributors : Nat
  allocations : Finset Allocation
  candidateArtifact : ArtifactRef
deriving DecidableEq

structure RawConfig where
  poolId : PoolId
  configDigest : Digest32
  openingEpoch : EpochId
  governanceKey : Digest32
  /-- Distinct consensus-finality authority.  Governance cannot certify its own
  chosen future height. -/
  finalityKey : Digest32
  members : Finset Digest32
  sources : Finset SourcePolicy
  allowedBeta : Finset ArtifactRef
  maxPoolSupply : Nat
  maxPoolCohesion : Nat
  maxReserveSupply : Nat
  maxReserveCohesion : Nat
  perPlayerSupplyCap : Nat
  perPlayerCohesionCap : Nat
  maxReceiptsPerEpoch : Nat
  collectionWindow : Nat
  claimWindow : Nat
  initialReserveSupply : Nat
  initialReserveCohesion : Nat
  recipes : List Recipe
deriving DecidableEq

def recipeValidB (raw : RawConfig) (recipe : Recipe) : Bool :=
  decide (0 < recipe.supplyPerRation) &&
  decide (0 < recipe.maxBatch) &&
  decide (recipe.maxBatch ≤ raw.members.card) &&
  decide (0 < recipe.minContributors) &&
  decide (recipe.minContributors ≤ raw.members.card) &&
  decide recipe.allocations.Nonempty &&
  decide (recipe.candidateArtifact ∈ raw.allowedBeta) &&
  decide (recipe.candidateArtifact.contentDigest = raw.configDigest) &&
  decide (recipe.maxBatch * recipe.supplyPerRation ≤
    raw.maxPoolSupply + raw.maxReserveSupply) &&
  decide (recipe.cohesionCost ≤ raw.maxPoolCohesion + raw.maxReserveCohesion)

def configValidB (raw : RawConfig) : Bool :=
  decide (raw.configDigest = raw.poolId.deploymentDigest) &&
  decide (raw.finalityKey ≠ raw.governanceKey) &&
  decide raw.members.Nonempty &&
  decide (raw.members.card ≤ MAX_MEMBERS) &&
  decide raw.sources.Nonempty &&
  decide (raw.sources.card ≤ MAX_SOURCES) &&
  decide (raw.allowedBeta.card ≤ MAX_CANDIDATES) &&
  decide (0 < raw.maxPoolSupply) &&
  decide (0 < raw.maxPoolCohesion) &&
  decide (0 < raw.perPlayerSupplyCap) &&
  decide (raw.perPlayerSupplyCap ≤ raw.maxPoolSupply) &&
  decide (0 < raw.perPlayerCohesionCap) &&
  decide (raw.perPlayerCohesionCap ≤ raw.maxPoolCohesion) &&
  decide (0 < raw.maxReceiptsPerEpoch) &&
  decide (raw.maxReceiptsPerEpoch ≤ MAX_RECEIPTS_PER_EPOCH) &&
  decide (0 < raw.collectionWindow) &&
  decide (0 < raw.claimWindow) &&
  decide (raw.initialReserveSupply ≤ raw.maxReserveSupply) &&
  decide (raw.initialReserveCohesion ≤ raw.maxReserveCohesion) &&
  decide (raw.recipes ≠ []) &&
  decide (raw.recipes.length ≤ MAX_RECIPES) &&
  decide ((raw.recipes.map (·.id)).Nodup) &&
  raw.recipes.all (recipeValidB raw)

structure Config where
  raw : RawConfig
  valid : configValidB raw = true

def findRecipe? (config : Config) (id : RecipeId) : Option Recipe :=
  config.raw.recipes.find? (fun recipe => recipe.id = id)

/-- Collision-independent semantic transcript of every policy field consumed by
the galley machine.  The compact `Digest32` below is only a wire projection of
this value; authority and store identity retain this structure itself. -/
structure ConfigTranscript where
  poolId : PoolId
  declaredDigest : Digest32
  openingEpoch : EpochId
  governanceKey : Digest32
  finalityKey : Digest32
  members : Finset Digest32
  sources : Finset SourcePolicy
  allowedBeta : Finset ArtifactRef
  maxPoolSupply : Nat
  maxPoolCohesion : Nat
  maxReserveSupply : Nat
  maxReserveCohesion : Nat
  perPlayerSupplyCap : Nat
  perPlayerCohesionCap : Nat
  maxReceiptsPerEpoch : Nat
  collectionWindow : Nat
  claimWindow : Nat
  initialReserveSupply : Nat
  initialReserveCohesion : Nat
  recipes : List Recipe
deriving DecidableEq

def configTranscript (config : Config) : ConfigTranscript where
  poolId := config.raw.poolId
  declaredDigest := config.raw.configDigest
  openingEpoch := config.raw.openingEpoch
  governanceKey := config.raw.governanceKey
  finalityKey := config.raw.finalityKey
  members := config.raw.members
  sources := config.raw.sources
  allowedBeta := config.raw.allowedBeta
  maxPoolSupply := config.raw.maxPoolSupply
  maxPoolCohesion := config.raw.maxPoolCohesion
  maxReserveSupply := config.raw.maxReserveSupply
  maxReserveCohesion := config.raw.maxReserveCohesion
  perPlayerSupplyCap := config.raw.perPlayerSupplyCap
  perPlayerCohesionCap := config.raw.perPlayerCohesionCap
  maxReceiptsPerEpoch := config.raw.maxReceiptsPerEpoch
  collectionWindow := config.raw.collectionWindow
  claimWindow := config.raw.claimWindow
  initialReserveSupply := config.raw.initialReserveSupply
  initialReserveCohesion := config.raw.initialReserveCohesion
  recipes := config.raw.recipes

structure ExactConfigDigest where
  transcript : ConfigTranscript
deriving DecidableEq

def exactConfigDigest (config : Config) : ExactConfigDigest := ⟨configTranscript config⟩

/-! ## Private-constructed state -/

structure CreditCounterRow where
  key : PlayerCounterKey
  counter : Nat
deriving DecidableEq

def creditCounterFor : List CreditCounterRow → PlayerCounterKey → Nat
  | [], _ => 0
  | row :: rows, key => if row.key = key then row.counter else creditCounterFor rows key

def setCreditCounter : List CreditCounterRow → PlayerCounterKey → Nat → List CreditCounterRow
  | [], key, counter => [{ key, counter }]
  | row :: rows, key, counter =>
      if row.key = key then { key, counter } :: rows
      else row :: setCreditCounter rows key counter

structure ActorCounterRow where
  actor : Digest32
  counter : Nat
deriving DecidableEq

def actorCounterFor : List ActorCounterRow → Digest32 → Nat
  | [], _ => 0
  | row :: rows, actor => if row.actor = actor then row.counter else actorCounterFor rows actor

def setActorCounter : List ActorCounterRow → Digest32 → Nat → List ActorCounterRow
  | [], actor, counter => [{ actor, counter }]
  | row :: rows, actor, counter =>
      if row.actor = actor then { actor, counter } :: rows
      else row :: setActorCounter rows actor counter

structure Tally where
  player : Digest32
  supply : Nat
  cohesion : Nat
deriving DecidableEq

def tallyFor : List Tally → Digest32 → Tally
  | [], player => { player, supply := 0, cohesion := 0 }
  | tally :: tallies, player =>
      if tally.player = player then tally else tallyFor tallies player

def setTally : List Tally → Tally → List Tally
  | [], replacement => [replacement]
  | tally :: tallies, replacement =>
      if tally.player = replacement.player then replacement :: tallies
      else tally :: setTally tallies replacement

def addTally (tallies : List Tally) (player : Digest32) (supply cohesion : Nat) : List Tally :=
  let old := tallyFor tallies player
  setTally tallies {
    player
    supply := old.supply + supply
    cohesion := old.cohesion + cohesion
  }

structure MenuOutcome where
  epoch : EpochId
  recipe : RecipeId
  allocation : Allocation
  servings : Nat
  contributors : Nat
  candidateArtifact : ArtifactRef
deriving DecidableEq

structure Batch where
  private mk ::
  outcome : MenuOutcome
  claimDeadline : EpochId
  remaining : Nat
  claimed : Finset Digest32
deriving DecidableEq

structure Phase where
  private mk ::
  private batch : Option Batch
deriving DecidableEq

private def collectingPhase : Phase := ⟨none⟩
private def finalizedPhase (batch : Batch) : Phase := ⟨some batch⟩

def byte (n : Nat) : Fin 256 := ⟨n % 256, Nat.mod_lt _ (by omega)⟩

/-- Runtime-facing bytes.  `CanonicalSerializer.faithful` is the boundary law:
two different semantic values may not acquire the same canonical byte string. -/
abbrev CanonicalBytes := List (Fin 256)

structure CanonicalSerializer (α : Type) where
  encode : α → CanonicalBytes
  faithful : Function.Injective encode

def digestWords (digest : Digest32) : List Nat := digest.bytes.map Fin.val

def poolIdTranscript (poolId : PoolId) : List Nat :=
  digestWords poolId.federationId ++ digestWords poolId.contentRoot ++
  digestWords poolId.activationDigest ++ digestWords poolId.contentSession ++
  digestWords poolId.deploymentDigest

def artifactTranscript (artifact : ArtifactRef) : List Nat :=
  [artifact.missionId.value, artifact.artifactId.value] ++
  digestWords artifact.sourceDigest ++ digestWords artifact.contentDigest

def sourcePolicyTranscript (source : SourcePolicy) : List Nat :=
  [source.mission.value] ++ digestWords source.runSeed

def allocationSetTranscript (allocations : Finset Allocation) : List Nat :=
  [if .openCommons ∈ allocations then 1 else 0,
   if .contributorsFirst ∈ allocations then 1 else 0,
   if .cohesionCrew ∈ allocations then 1 else 0]

def recipeTranscript (recipe : Recipe) : List Nat :=
  [recipe.id.value, recipe.supplyPerRation, recipe.cohesionCost,
    recipe.maxBatch, recipe.minContributors] ++
  allocationSetTranscript recipe.allocations ++ artifactTranscript recipe.candidateArtifact

/-- Canonical commutative projection of a digest set.  Exact authority does not
rely on this compact summary: `ConfigTranscript` retains the `Finset` itself. -/
def digestSetWords (values : Finset Digest32) : List Nat :=
  values.card :: (List.range 32).map (fun lane =>
    values.sum (fun value => (digestWords value).getD lane 0))

def sourceSetWords (values : Finset SourcePolicy) : List Nat :=
  values.card :: values.sum (fun source => source.mission.value) ::
    (List.range 32).map (fun lane =>
      values.sum (fun source => (digestWords source.runSeed).getD lane 0))

def artifactSetWords (values : Finset ArtifactRef) : List Nat :=
  values.card :: values.sum (fun artifact => artifact.missionId.value) ::
    values.sum (fun artifact => artifact.artifactId.value) ::
    (List.range 32).map (fun lane =>
      values.sum (fun artifact => (digestWords artifact.sourceDigest).getD lane 0)) ++
    (List.range 32).map (fun lane =>
      values.sum (fun artifact => (digestWords artifact.contentDigest).getD lane 0))

private def digestLane (words : List Nat) (lane : Nat) : Nat :=
  words.zipIdx.foldl (fun accumulator indexed =>
    if indexed.2 % 32 = lane then
      (accumulator * 131 + indexed.1 + indexed.2 + 1) % 256
    else accumulator) 0

/-- Deterministic compact checksum for tests and state labels.  This mod-256
mixer is deliberately NOT a signature digest, CAS identity, or authority root;
production admission below requires a separately supplied canonical serializer
and real hash/signature verifier over the exact structural transcript. -/
def transcriptDigest (words : List Nat) : Digest32 where
  bytes := List.ofFn (fun lane : Fin 32 => byte (digestLane words lane.val))
  length_eq := by simp

/-- Standing collision witness: changing one transcript word by 256 preserves
the compact checksum.  No authority or persistence decision may rely on it. -/
theorem transcriptDigest_add_256_collision :
    transcriptDigest [0] = transcriptDigest [256] ∧ [0] ≠ [256] := by
  native_decide

def configTranscriptWords (config : Config) : List Nat :=
  [1, config.raw.openingEpoch.value, config.raw.maxPoolSupply,
    config.raw.maxPoolCohesion, config.raw.maxReserveSupply,
    config.raw.maxReserveCohesion, config.raw.perPlayerSupplyCap,
    config.raw.perPlayerCohesionCap, config.raw.maxReceiptsPerEpoch,
    config.raw.collectionWindow, config.raw.claimWindow, config.raw.initialReserveSupply,
    config.raw.initialReserveCohesion] ++
  poolIdTranscript config.raw.poolId ++ digestWords config.raw.configDigest ++
  digestWords config.raw.governanceKey ++ digestWords config.raw.finalityKey ++
  digestSetWords config.raw.members ++
  sourceSetWords config.raw.sources ++ artifactSetWords config.raw.allowedBeta ++
  [config.raw.recipes.length] ++ config.raw.recipes.flatMap (fun recipe =>
    let words := recipeTranscript recipe
    words.length :: words)

def configWireDigest (config : Config) : Digest32 :=
  transcriptDigest (configTranscriptWords config)

def genesisTranscript (config : Config) : List Nat :=
  2 :: configTranscriptWords config

structure State where
  private mk ::
  admissionProvenance : AdmissionProvenance
  poolId : PoolId
  configDigest : Digest32
  commitment : Digest32
  epoch : EpochId
  collectionDeadline : EpochId
  genesisSupply : Nat
  genesisCohesion : Nat
  reserveSupply : Nat
  reserveCohesion : Nat
  poolSupply : Nat
  poolCohesion : Nat
  totalSupplyReceived : Nat
  totalCohesionReceived : Nat
  totalSupplyUsed : Nat
  totalCohesionUsed : Nat
  producedRations : Nat
  playerRationsClaimed : Nat
  commonsRationsConsumed : Nat
  sequence : Nat
  creditCounters : List CreditCounterRow
  actorCounters : List ActorCounterRow
  tallies : List Tally
  consumedCredits : Finset ReceiptKey
  private phase : Phase
  lastMenu : Option MenuOutcome
  candidateArtifacts : Finset ArtifactRef
deriving DecidableEq

/-- The canonical store retains the exact config and exact state at each pool
head.  A declared `configDigest` cannot substitute a shadow policy. -/
structure PoolHead where
  poolId : PoolId
  config : ConfigTranscript
  head : State
deriving DecidableEq

/-- Canonical deployment state.  Global nullifiers deliberately survive pool
epochs and local state snapshots. -/
structure DeploymentStore where
  private mk ::
  pools : List PoolHead
  redeemedCredits : Finset ReceiptKey
  sequence : Nat
deriving DecidableEq

/-- The one canonical pre-pool deployment root.  Publishing this constructor
function does not expose `DeploymentStore.mk`: callers can obtain only the
empty revision-zero value whose durable creation is certified below. -/
def deploymentGenesisStore : DeploymentStore := ⟨[], ∅, 0⟩

structure StoreSnapshot where
  pools : List PoolHead
  redeemedCredits : Finset ReceiptKey
  sequence : Nat
deriving DecidableEq

def DeploymentStore.snapshot (store : DeploymentStore) : StoreSnapshot where
  pools := store.pools
  redeemedCredits := store.redeemedCredits
  sequence := store.sequence

/-- Collision-independent identity for one exact store snapshot.  A runtime may
hash its canonical encoding, but authority retains the exact snapshot. -/
structure StoreRoot where
  private mk ::
  snapshot : StoreSnapshot
deriving DecidableEq

def DeploymentStore.root (store : DeploymentStore) : StoreRoot := ⟨store.snapshot⟩

/-- Explicit host persistence contract.  The expected CAS identity is a real
runtime hash of the faithful canonical encoding of the *entire* old store
snapshot.  The replacement is likewise the faithful encoding of the entire new
snapshot.  `State.commitment` and `transcriptDigest` never enter this identity.

`compareAndSwap expected replacement` is the durable adapter operation;
`singleWinner` is its atomic single-winner TCB. -/
structure PersistenceCASContract where
  storeSerializer : CanonicalSerializer StoreSnapshot
  hashAlgorithmId : Digest32
  storeKindId : Digest32
  realHash : CanonicalBytes → Digest32
  /-- Durable load/inclusion proof, binding the faithful full snapshot, its
  real-hash identity and the exact external store revision. -/
  loadedAt : Nat → Digest32 → CanonicalBytes → Prop
  /-- Atomic create-if-absent for the deployment's one root key. -/
  createGenesis : Digest32 → Digest32 → CanonicalBytes → Prop
  /-- Durable membership in the unique CAS lineage rooted by `createGenesis`. -/
  rootedAt : Digest32 → Nat → Digest32 → CanonicalBytes → Prop
  compareAndSwap : Digest32 → Nat → Digest32 → Nat → CanonicalBytes → Prop
  genesisRooted : ∀ {deploymentId root : Digest32} {bytes : CanonicalBytes},
    createGenesis deploymentId root bytes → rootedAt deploymentId 0 root bytes
  rootedZeroWasGenesis : ∀ {deploymentId root : Digest32} {bytes : CanonicalBytes},
    rootedAt deploymentId 0 root bytes → createGenesis deploymentId root bytes
  genesisUnique : ∀ {deploymentId leftRoot rightRoot : Digest32}
      {left right : CanonicalBytes},
    createGenesis deploymentId leftRoot left →
    createGenesis deploymentId rightRoot right →
    leftRoot = rightRoot ∧ left = right
  casPreservesRoot : ∀ {deploymentId : Digest32} {beforeRevision : Nat}
      {beforeRoot : Digest32} {beforeBytes : CanonicalBytes}
      {afterRevision : Nat} {afterBytes : CanonicalBytes},
    rootedAt deploymentId beforeRevision beforeRoot beforeBytes →
    compareAndSwap deploymentId beforeRevision beforeRoot afterRevision afterBytes →
    rootedAt deploymentId afterRevision (realHash
      ([byte 0x50, byte 0x4f, byte 0x41, byte 0x01, byte 0x53] ++
        hashAlgorithmId.bytes ++ storeKindId.bytes ++ afterBytes)) afterBytes
  singleWinner : ∀ {deploymentId : Digest32} {expectedRevision : Nat} {expected : Digest32}
      {leftRevision rightRevision : Nat} {left right : CanonicalBytes},
    compareAndSwap deploymentId expectedRevision expected leftRevision left →
    compareAndSwap deploymentId expectedRevision expected rightRevision right →
    leftRevision = rightRevision ∧ left = right

/-- Domain-separated real-hash identity for durable store CAS. -/
def PersistenceCASContract.storeIdentity (persistence : PersistenceCASContract)
    (store : DeploymentStore) : Digest32 :=
  persistence.realHash
    ([byte 0x50, byte 0x4f, byte 0x41, byte 0x01, byte 0x53] ++
      persistence.hashAlgorithmId.bytes ++
      persistence.storeKindId.bytes ++
      persistence.storeSerializer.encode store.snapshot)

/-- Evidence returned by the host only after the candidate won durable CAS.
The constructor is private: callers cannot choose a convenient persistence
predicate and mint their own successful receipt. -/
structure PersistedTransition (persistence : PersistenceCASContract) (deploymentId : Digest32)
    (before after : DeploymentStore) where
  private mk ::
  admissionProvenance : AdmissionProvenance
  committed : persistence.compareAndSwap deploymentId before.sequence (persistence.storeIdentity before)
    after.sequence (persistence.storeSerializer.encode after.snapshot)

/-- Opaque handle held only by the durable-store adapter.  Choosing an
always-true CAS predicate is insufficient because callers cannot construct the
capability for it. -/
structure PersistenceCapability (persistence : PersistenceCASContract) where
  private mk ::
  admissionProvenance : AdmissionProvenance
  expectedDeploymentId : Digest32

/-- The one authority permitted to create a deployment's absent root key. -/
structure DeploymentRootGenesisCapability (persistence : PersistenceCASContract) where
  private mk ::
  admissionProvenance : AdmissionProvenance
  deploymentId : Digest32

/-- Opaque certificate for the canonical empty store at the deployment's unique
durable root.  It is the sole public source of a first `DeploymentStore`. -/
structure DeploymentRootCertificate (persistence : PersistenceCASContract) where
  private mk ::
  admissionProvenance : AdmissionProvenance
  deploymentId : Digest32
  store : DeploymentStore
  canonical : store = deploymentGenesisStore
  created : persistence.createGenesis deploymentId
    (persistence.storeIdentity store) (persistence.storeSerializer.encode store.snapshot)
  rooted : persistence.rootedAt deploymentId store.sequence
    (persistence.storeIdentity store) (persistence.storeSerializer.encode store.snapshot)

/-- Checked create-if-absent bootstrap.  A second root for the same deployment
cannot obtain `created`; `genesisUnique` also makes any two certificates exact. -/
def bootstrapDeploymentRoot {persistence : PersistenceCASContract}
    (cap : DeploymentRootGenesisCapability persistence)
    (created : persistence.createGenesis cap.deploymentId
      (persistence.storeIdentity deploymentGenesisStore)
      (persistence.storeSerializer.encode deploymentGenesisStore.snapshot)) :
    DeploymentRootCertificate persistence :=
  ⟨cap.admissionProvenance, cap.deploymentId, deploymentGenesisStore, rfl, created,
    persistence.genesisRooted created⟩

/-- Opaque proof that this exact faithful snapshot came from durable storage at
its exact revision.  Capability possession alone cannot manufacture it. -/
structure DurableStoreLoad (persistence : PersistenceCASContract)
    (store : DeploymentStore) where
  private mk ::
  admissionProvenance : AdmissionProvenance
  deploymentId : Digest32
  included : persistence.loadedAt store.sequence (persistence.storeIdentity store)
    (persistence.storeSerializer.encode store.snapshot)
  rooted : persistence.rootedAt deploymentId store.sequence
    (persistence.storeIdentity store) (persistence.storeSerializer.encode store.snapshot)

def admitDurableStoreLoad {persistence : PersistenceCASContract}
    (cap : PersistenceCapability persistence) (store : DeploymentStore)
    (included : persistence.loadedAt store.sequence (persistence.storeIdentity store)
      (persistence.storeSerializer.encode store.snapshot))
    (rooted : persistence.rootedAt cap.expectedDeploymentId store.sequence
      (persistence.storeIdentity store) (persistence.storeSerializer.encode store.snapshot)) :
    DurableStoreLoad persistence store :=
  ⟨cap.admissionProvenance, cap.expectedDeploymentId, included, rooted⟩

theorem DurableStoreLoad.exact {persistence : PersistenceCASContract}
    {store : DeploymentStore} (load : DurableStoreLoad persistence store) :
    persistence.loadedAt store.sequence (persistence.storeIdentity store)
      (persistence.storeSerializer.encode store.snapshot) :=
  load.included

theorem DurableStoreLoad.rooted_exact {persistence : PersistenceCASContract}
    {store : DeploymentStore} (load : DurableStoreLoad persistence store) :
    persistence.rootedAt load.deploymentId store.sequence
      (persistence.storeIdentity store) (persistence.storeSerializer.encode store.snapshot) :=
  load.rooted

def admitCASReceipt {persistence : PersistenceCASContract}
    (cap : PersistenceCapability persistence) (before after : DeploymentStore)
    (committed : persistence.compareAndSwap cap.expectedDeploymentId before.sequence
      (persistence.storeIdentity before)
      after.sequence (persistence.storeSerializer.encode after.snapshot)) :
    PersistedTransition persistence cap.expectedDeploymentId before after :=
  ⟨cap.admissionProvenance, committed⟩

theorem DeploymentRootCertificate.same_root {persistence : PersistenceCASContract}
    (left right : DeploymentRootCertificate persistence)
    (_sameDeployment : left.deploymentId = right.deploymentId) : left.store = right.store := by
  exact left.canonical.trans right.canonical.symm

theorem DeploymentStore.snapshot_injective : Function.Injective DeploymentStore.snapshot := by
  intro left right exact
  cases left
  cases right
  simp_all [DeploymentStore.snapshot]

/-- A hostile revision-zero reload cannot reset a deployment to a second empty
or edited root.  Rooted revision zero must be a genesis creation, and atomic
genesis uniqueness plus faithful bytes recovers the exact certified store. -/
theorem DurableStoreLoad.revisionZero_same_genesis
    {persistence : PersistenceCASContract} {store : DeploymentStore}
    (root : DeploymentRootCertificate persistence)
    (load : DurableStoreLoad persistence store)
    (sameDeployment : root.deploymentId = load.deploymentId)
    (revisionZero : store.sequence = 0) : store = root.store := by
  have loadedCreated : persistence.createGenesis load.deploymentId
      (persistence.storeIdentity store)
      (persistence.storeSerializer.encode store.snapshot) := by
    apply persistence.rootedZeroWasGenesis
    simpa [revisionZero] using load.rooted
  rw [← sameDeployment] at loadedCreated
  have bytesExact := (persistence.genesisUnique loadedCreated root.created).2
  apply DeploymentStore.snapshot_injective
  exact persistence.storeSerializer.faithful bytesExact

theorem PersistedTransition.same_successor {persistence : PersistenceCASContract}
    {deploymentId : Digest32} {before left right : DeploymentStore}
    (leftWon : PersistedTransition persistence deploymentId before left)
    (rightWon : PersistedTransition persistence deploymentId before right) : left = right :=
  DeploymentStore.snapshot_injective <|
    persistence.storeSerializer.faithful <|
      (persistence.singleWinner leftWon.committed rightWon.committed).2

/-- The deployment is an index of the receipt and an argument of the durable
CAS fact; it cannot be supplied or relabelled after admission. -/
theorem PersistedTransition.deployment_scoped {persistence : PersistenceCASContract}
    {deploymentId : Digest32} {before after : DeploymentStore}
    (receipt : PersistedTransition persistence deploymentId before after) :
    persistence.compareAndSwap deploymentId before.sequence
      (persistence.storeIdentity before) after.sequence
      (persistence.storeSerializer.encode after.snapshot) :=
  receipt.committed

def poolHeadById? : List PoolHead → PoolId → Option PoolHead
  | [], _ => none
  | head :: heads, poolId =>
      if head.poolId = poolId then some head else poolHeadById? heads poolId

private def setPoolHead : List PoolHead → PoolHead → List PoolHead
  | [], replacement => [replacement]
  | head :: heads, replacement =>
      if head.poolId = replacement.poolId then replacement :: heads
      else head :: setPoolHead heads replacement

def openedPools (store : DeploymentStore) : Finset PoolId :=
  (store.pools.map PoolHead.poolId).toFinset

structure CanonicalGenesisTranscript where
  storeRoot : StoreRoot
  config : ConfigTranscript
  admissionProvenance : AdmissionProvenance
deriving DecidableEq

structure ExactGenesisDigest where
  transcript : CanonicalGenesisTranscript
deriving DecidableEq

/-- Exact externally authenticated opening request.  `openPool` independently
checks the signed old structural root and complete config transcript. -/
structure GenesisAuthority (store : DeploymentStore) (config : Config) where
  private mk ::
  admissionProvenance : AdmissionProvenance
  canonicalStoreRoot : StoreRoot
  signedConfig : ConfigTranscript
  transcript : CanonicalGenesisTranscript
  exactDigest : ExactGenesisDigest
  wireTranscript : List Nat
  digest : Digest32

def genesisAuthorityTranscript (store : DeploymentStore) (config : Config) : List Nat :=
  [4, store.sequence, store.pools.length, store.redeemedCredits.card] ++
  genesisTranscript config ++ digestWords (configWireDigest config)

def genesisAuthorityValidB {store : DeploymentStore} {config : Config}
    (authority : GenesisAuthority store config) : Bool :=
  decide (authority.canonicalStoreRoot = store.root) &&
  decide (authority.signedConfig = configTranscript config) &&
  decide (authority.transcript =
    ({
      storeRoot := store.root
      config := configTranscript config
      admissionProvenance := authority.admissionProvenance
    } : CanonicalGenesisTranscript)) &&
  decide (authority.exactDigest = ⟨authority.transcript⟩) &&
  decide (authority.wireTranscript = genesisAuthorityTranscript store config) &&
  decide (authority.digest = transcriptDigest authority.wireTranscript)

inductive OpenRefusal where
  | staleStore
  | authenticationMismatch
  | alreadyOpened
deriving DecidableEq, Repr

private def genesisState (config : Config) (provenance : AdmissionProvenance) : State where
  admissionProvenance := provenance
  poolId := config.raw.poolId
  configDigest := config.raw.configDigest
  commitment := transcriptDigest (genesisTranscript config)
  epoch := config.raw.openingEpoch
  collectionDeadline := ⟨config.raw.openingEpoch.value + config.raw.collectionWindow⟩
  genesisSupply := config.raw.initialReserveSupply
  genesisCohesion := config.raw.initialReserveCohesion
  reserveSupply := config.raw.initialReserveSupply
  reserveCohesion := config.raw.initialReserveCohesion
  poolSupply := 0
  poolCohesion := 0
  totalSupplyReceived := 0
  totalCohesionReceived := 0
  totalSupplyUsed := 0
  totalCohesionUsed := 0
  producedRations := 0
  playerRationsClaimed := 0
  commonsRationsConsumed := 0
  sequence := 0
  creditCounters := []
  actorCounters := []
  tallies := []
  consumedCredits := ∅
  phase := collectingPhase
  lastMenu := none
  candidateArtifacts := ∅

/-- Pure checked pool-opening candidate.  When the caller threads the returned
store, reopening refuses; global one-shot creation requires a
`PersistedTransition` from the runtime persistence adapter. -/
def openPool (canonical expected : DeploymentStore) (config : Config)
    (authority : GenesisAuthority expected config) : Except OpenRefusal (DeploymentStore × State) :=
  if canonical != expected then .error .staleStore
  else if config.raw.poolId ∈ openedPools canonical then .error .alreadyOpened
  else if genesisAuthorityValidB authority != true then .error .authenticationMismatch
  else
    let state := genesisState config authority.admissionProvenance
    let head : PoolHead :=
      { poolId := config.raw.poolId, config := configTranscript config, head := state }
    .ok (⟨head :: canonical.pools, canonical.redeemedCredits, canonical.sequence + 1⟩, state)

theorem openPool_same_pool_refused {store : DeploymentStore} {config : Config}
    {authority : GenesisAuthority store config} {storeAfter : DeploymentStore} {state : State}
    (opened : openPool store store config authority = .ok (storeAfter, state))
    (nextAuthority : GenesisAuthority storeAfter config) :
    openPool storeAfter storeAfter config nextAuthority = .error .alreadyOpened := by
  unfold openPool at opened
  split at opened <;> try contradiction
  split at opened <;> try contradiction
  split at opened <;> try contradiction
  simp only [Except.ok.injEq] at opened
  injection opened with storeExact _
  have already : config.raw.poolId ∈ openedPools storeAfter := by
    rw [← storeExact]
    simp [openedPools]
  simp [openPool, already]

def contributors (config : Config) (state : State) : Finset Digest32 :=
  config.raw.members.filter (fun player =>
    let tally := tallyFor state.tallies player
    decide (0 < tally.supply + tally.cohesion))

def allocationEligibleB (state : State) (allocation : Allocation) (player : Digest32) : Bool :=
  let tally := tallyFor state.tallies player
  match allocation with
  | .openCommons => true
  | .contributorsFirst => decide (0 < tally.supply + tally.cohesion)
  | .cohesionCrew => decide (0 < tally.cohesion)

def openRations (state : State) : Nat :=
  match state.phase.batch with
  | none => 0
  | some batch => batch.remaining

def ResourcesConserved (state : State) : Prop :=
  state.genesisSupply + state.totalSupplyReceived =
      state.totalSupplyUsed + state.reserveSupply + state.poolSupply ∧
  state.genesisCohesion + state.totalCohesionReceived =
      state.totalCohesionUsed + state.reserveCohesion + state.poolCohesion

def RationsConserved (state : State) : Prop :=
  state.producedRations =
    state.playerRationsClaimed + state.commonsRationsConsumed + openRations state

def resourcesConservedB (state : State) : Bool :=
  decide (state.genesisSupply + state.totalSupplyReceived =
    state.totalSupplyUsed + state.reserveSupply + state.poolSupply) &&
  decide (state.genesisCohesion + state.totalCohesionReceived =
    state.totalCohesionUsed + state.reserveCohesion + state.poolCohesion)

def rationsConservedB (state : State) : Bool :=
  decide (state.producedRations =
    state.playerRationsClaimed + state.commonsRationsConsumed + openRations state)

def phaseValidB (config : Config) (state : State) : Bool :=
  match state.phase.batch with
  | none => decide (openRations state = 0) &&
      decide (state.epoch.value < state.collectionDeadline.value)
  | some batch =>
      decide (batch.outcome.epoch = state.epoch) &&
      decide (batch.claimDeadline.value = state.epoch.value + config.raw.claimWindow) &&
      decide (0 < batch.outcome.servings) &&
      decide (batch.remaining ≤ batch.outcome.servings) &&
      decide (batch.claimed.card + batch.remaining = batch.outcome.servings) &&
      decide (batch.claimed ⊆ config.raw.members) &&
      decide (batch.outcome.candidateArtifact ∈ state.candidateArtifacts)

def creditCountersValidB (config : Config) (state : State) : Bool :=
  decide ((state.creditCounters.map (·.key)).Nodup) &&
  state.creditCounters.all (fun row =>
    decide (row.key.federationId = config.raw.poolId.federationId) &&
    decide (row.key.contentSession = config.raw.poolId.contentSession) &&
    decide (row.counter < PLAYER_COUNTER_MODULUS))

def actorCountersValidB (state : State) : Bool :=
  decide ((state.actorCounters.map (·.actor)).Nodup) &&
  state.actorCounters.all (fun row => decide (row.counter < PLAYER_COUNTER_MODULUS))

def talliesValidB (config : Config) (state : State) : Bool :=
  decide ((state.tallies.map (·.player)).Nodup) &&
  state.tallies.all (fun tally =>
    decide (tally.player ∈ config.raw.members) &&
    decide (tally.supply ≤ config.raw.perPlayerSupplyCap) &&
    decide (tally.cohesion ≤ config.raw.perPlayerCohesionCap))

def consumedCreditsValidB (config : Config) (state : State) : Bool :=
  decide ((state.consumedCredits.filter (fun key =>
    key.federationId = config.raw.poolId.federationId ∧
    key.contentSession = config.raw.poolId.contentSession ∧
    key.contentEpoch = state.epoch)).card = state.consumedCredits.card)

def lastMenuValidB (state : State) : Bool :=
  match state.lastMenu with
  | none => true
  | some outcome => decide (outcome.candidateArtifact ∈ state.candidateArtifacts)

/-- Checked both before and after every public transition. -/
def stateValidB (config : Config) (state : State) : Bool :=
  decide (state.poolId = config.raw.poolId) &&
  decide (state.configDigest = config.raw.configDigest) &&
  resourcesConservedB state &&
  rationsConservedB state &&
  decide (state.reserveSupply ≤ config.raw.maxReserveSupply) &&
  decide (state.reserveCohesion ≤ config.raw.maxReserveCohesion) &&
  decide (state.poolSupply ≤ config.raw.maxPoolSupply) &&
  decide (state.poolCohesion ≤ config.raw.maxPoolCohesion) &&
  decide (state.consumedCredits.card ≤ config.raw.maxReceiptsPerEpoch) &&
  decide (state.candidateArtifacts ⊆ config.raw.allowedBeta) &&
  creditCountersValidB config state &&
  actorCountersValidB state &&
  talliesValidB config state &&
  consumedCreditsValidB config state &&
  lastMenuValidB state &&
  phaseValidB config state

theorem resourcesConservedB_iff (state : State) :
    resourcesConservedB state = true ↔ ResourcesConserved state := by
  simp [resourcesConservedB, ResourcesConserved]

theorem rationsConservedB_iff (state : State) :
    rationsConservedB state = true ↔ RationsConserved state := by
  simp [rationsConservedB, RationsConserved]

theorem openPool_resources_conserved {store : DeploymentStore} {config : Config}
    {authority : GenesisAuthority store config} {storeAfter : DeploymentStore} {state : State}
    (opened : openPool store store config authority = .ok (storeAfter, state)) :
    ResourcesConserved state := by
  unfold openPool at opened
  split at opened <;> try contradiction
  split at opened <;> try contradiction
  split at opened <;> try contradiction
  simp only [Except.ok.injEq] at opened
  injection opened with _ stateExact
  rw [← stateExact]
  simp [genesisState, ResourcesConserved]

theorem openPool_rations_conserved {store : DeploymentStore} {config : Config}
    {authority : GenesisAuthority store config} {storeAfter : DeploymentStore} {state : State}
    (opened : openPool store store config authority = .ok (storeAfter, state)) :
    RationsConserved state := by
  unfold openPool at opened
  split at opened <;> try contradiction
  split at opened <;> try contradiction
  split at opened <;> try contradiction
  simp only [Except.ok.injEq] at opened
  injection opened with _ stateExact
  rw [← stateExact]
  simp [genesisState, RationsConserved, openRations, collectingPhase]

/-! ## Exact command transcripts and private authenticated authority -/

inductive Command where
  | contribute (credit : GalleyCredit)
  | finalize (epoch : EpochId) (recipe : RecipeId) (allocation : Allocation) (servings : Nat)
  | claim (epoch : EpochId) (player : Digest32)
  | advance (next : EpochId)
  /-- Finality-gated escape hatch for a collecting epoch whose authored menu
  cannot be completed.  Existing resources carry forward; no credit is replayed. -/
  | rollover (next : EpochId)

def allocationTag : Allocation → Nat
  | .openCommons => 0
  | .contributorsFirst => 1
  | .cohesionCrew => 2

def creditTranscript (credit : GalleyCredit) : List Nat :=
  [credit.sourceMission.value, credit.contentEpoch.value, credit.previousPlayerCounter,
    credit.playerCounter, credit.contribution.intel.val, credit.contribution.supplies.val,
    credit.contribution.cohesion.val, credit.contribution.influence.val,
    credit.contribution.score.val] ++
  digestWords credit.admissionProvenance.tokenDigest ++
  poolIdTranscript credit.poolId ++ digestWords credit.runSeed ++
  digestWords credit.playerKey ++ digestWords credit.receiptKey.federationId ++
  digestWords credit.receiptKey.contentSession ++
  [credit.receiptKey.contentEpoch.value, credit.receiptKey.playerCounter]

def commandPayload : Command → List Nat
  | .contribute credit => 0 :: creditTranscript credit
  | .finalize epoch recipe allocation servings =>
      [1, epoch.value, recipe.value, allocationTag allocation, servings]
  | .claim epoch player => [2, epoch.value] ++ digestWords player
  | .advance next => [3, next.value]
  | .rollover next => [4, next.value]

/-- Collision-independent finality statement.  Consensus certifies an observed
epoch at one exact canonical store/head; it does not sign a free-floating epoch
chosen by governance. -/
structure CanonicalFinalityTranscript where
  storeRoot : StoreRoot
  config : ConfigTranscript
  state : State
  certifiedEpoch : EpochId
  finalizedRoot : Digest32
  admissionProvenance : AdmissionProvenance
deriving DecidableEq

structure ExactFinalityDigest where
  transcript : CanonicalFinalityTranscript
deriving DecidableEq

/-- Typed finalized-chain input.  The private certificate is indexed by the
complete config and exact epoch; an arbitrary `Option EpochId` cannot stand in
for finality.  Its structural transcript is authoritative; the legacy compact
`digest` is only a deterministic state label. -/
structure FinalizedEpochCertificate (config : Config) (epoch : EpochId) where
  private mk ::
  admissionProvenance : AdmissionProvenance
  canonicalStoreRoot : StoreRoot
  canonicalState : State
  finalizedRoot : Digest32
  transcript : CanonicalFinalityTranscript
  exactDigest : ExactFinalityDigest
  wireTranscript : List Nat
  digest : Digest32
  transcript_exact : transcript =
    { storeRoot := canonicalStoreRoot, config := configTranscript config,
      state := canonicalState, certifiedEpoch := epoch, finalizedRoot,
      admissionProvenance }
  exact_digest_exact : exactDigest = ⟨transcript⟩
  wire_transcript_exact : wireTranscript =
    [5, epoch.value, canonicalState.sequence] ++ configTranscriptWords config ++
      digestWords canonicalState.commitment ++ digestWords finalizedRoot
  digest_exact : digest = transcriptDigest wireTranscript

inductive CommandFinality (config : Config) : (command : Command) → Type where
  | contribute (credit : GalleyCredit) : CommandFinality config (.contribute credit)
  | claim (epoch : EpochId) (player : Digest32) : CommandFinality config (.claim epoch player)
  | finalize (epoch : EpochId) (recipe : RecipeId) (allocation : Allocation) (servings : Nat)
      (certificate : FinalizedEpochCertificate config epoch) :
      CommandFinality config (.finalize epoch recipe allocation servings)
  | advance (next : EpochId) (certificate : FinalizedEpochCertificate config next) :
      CommandFinality config (.advance next)
  | rollover (next : EpochId) (certificate : FinalizedEpochCertificate config next) :
      CommandFinality config (.rollover next)

inductive FinalityView where
  | notRequired
  | finalized (provenance : AdmissionProvenance) (epoch : EpochId) (root digest : Digest32)
deriving DecidableEq

def CommandFinality.view {config : Config} {command : Command} :
    CommandFinality config command → FinalityView
  | .contribute _ => .notRequired
  | .claim _ _ => .notRequired
  | .finalize epoch _ _ _ certificate =>
      .finalized certificate.admissionProvenance epoch certificate.finalizedRoot certificate.digest
  | .advance next certificate =>
      .finalized certificate.admissionProvenance next certificate.finalizedRoot certificate.digest
  | .rollover next certificate =>
      .finalized certificate.admissionProvenance next certificate.finalizedRoot certificate.digest

def CommandFinality.admissionProvenance? {config : Config} {command : Command} :
    CommandFinality config command → Option AdmissionProvenance
  | .contribute credit => some credit.admissionProvenance
  | .claim _ _ => none
  | .finalize _ _ _ _ certificate => some certificate.admissionProvenance
  | .advance _ certificate => some certificate.admissionProvenance
  | .rollover _ certificate => some certificate.admissionProvenance

def FinalizedEpochCertificate.matchesHeadB {config : Config} {epoch : EpochId}
    (certificate : FinalizedEpochCertificate config epoch)
    (store : DeploymentStore) (state : State) : Bool :=
  decide (certificate.canonicalStoreRoot = store.root) &&
  decide (certificate.canonicalState = state) &&
  decide (certificate.transcript = {
    storeRoot := store.root
    config := configTranscript config
    state
    certifiedEpoch := epoch
    finalizedRoot := certificate.finalizedRoot
    admissionProvenance := certificate.admissionProvenance
  })

def CommandFinality.matchesHeadB {config : Config} {command : Command}
    (finality : CommandFinality config command) (store : DeploymentStore)
    (state : State) : Bool :=
  match finality with
  | .contribute _ => true
  | .claim _ _ => true
  | .finalize epoch _ _ _ certificate =>
      certificate.matchesHeadB store state && decide (epoch = state.epoch)
  | .advance _ certificate => certificate.matchesHeadB store state
  | .rollover _ certificate => certificate.matchesHeadB store state

structure GalleyCreditView where
  admissionProvenance : AdmissionProvenance
  poolId : PoolId
  contentRoot : Digest32
  activationDigest : Digest32
  sourceMission : MissionId
  runSeed : Digest32
  federationId : Digest32
  contentSession : Digest32
  contentEpoch : EpochId
  playerKey : Digest32
  previousPlayerCounter : Nat
  playerCounter : Nat
  counterKey : PlayerCounterKey
  receiptKey : ReceiptKey
  contribution : Contribution
deriving DecidableEq

def GalleyCredit.view (credit : GalleyCredit) : GalleyCreditView where
  admissionProvenance := credit.admissionProvenance
  poolId := credit.poolId
  contentRoot := credit.contentRoot
  activationDigest := credit.activationDigest
  sourceMission := credit.sourceMission
  runSeed := credit.runSeed
  federationId := credit.federationId
  contentSession := credit.contentSession
  contentEpoch := credit.contentEpoch
  playerKey := credit.playerKey
  previousPlayerCounter := credit.previousPlayerCounter
  playerCounter := credit.playerCounter
  counterKey := credit.counterKey
  receiptKey := credit.receiptKey
  contribution := credit.contribution

inductive CommandView where
  | contribute (credit : GalleyCreditView)
  | finalize (epoch : EpochId) (recipe : RecipeId) (allocation : Allocation) (servings : Nat)
  | claim (epoch : EpochId) (player : Digest32)
  | advance (next : EpochId)
  | rollover (next : EpochId)
deriving DecidableEq

def Command.view : Command → CommandView
  | .contribute credit => .contribute credit.view
  | .finalize epoch recipe allocation servings => .finalize epoch recipe allocation servings
  | .claim epoch player => .claim epoch player
  | .advance next => .advance next
  | .rollover next => .rollover next

/-- Collision-independent signed semantic transcript.  It binds the exact
canonical store snapshot, complete config, complete prestate and command. -/
structure CanonicalCommandTranscript where
  storeRoot : StoreRoot
  config : ConfigTranscript
  state : State
  command : CommandView
  admissionProvenance : AdmissionProvenance
  actor : Digest32
  previousCounter : Nat
  actionCounter : Nat
  finality : FinalityView
deriving DecidableEq

structure ExactCommandDigest where
  transcript : CanonicalCommandTranscript
deriving DecidableEq

def finalityWords : FinalityView → List Nat
  | .notRequired => [0]
  | .finalized provenance epoch root digest =>
      [1, epoch.value] ++ digestWords provenance.tokenDigest ++
        digestWords root ++ digestWords digest

def commandTranscript (store : DeploymentStore) (config : Config) (state : State)
    (command : Command) (provenance : AdmissionProvenance)
    (actor : Digest32) (previousCounter actionCounter : Nat)
    (finality : CommandFinality config command) : CanonicalCommandTranscript where
  storeRoot := store.root
  config := configTranscript config
  state
  command := command.view
  admissionProvenance := provenance
  actor
  previousCounter
  actionCounter
  finality := finality.view

def commandTranscriptWords (store : DeploymentStore) (config : Config) (state : State)
    (command : Command) (provenance : AdmissionProvenance)
    (actor : Digest32) (previousCounter actionCounter : Nat)
    (finality : CommandFinality config command) : List Nat :=
  [6, store.sequence, store.pools.length, store.redeemedCredits.card,
    state.sequence, previousCounter, actionCounter] ++
  configTranscriptWords config ++ digestWords (configWireDigest config) ++
  digestWords state.commitment ++ digestWords provenance.tokenDigest ++ digestWords actor ++
  finalityWords finality.view ++ commandPayload command

def commandDigest (store : DeploymentStore) (config : Config) (state : State)
    (command : Command) (provenance : AdmissionProvenance)
    (actor : Digest32) (previousCounter actionCounter : Nat)
    (finality : CommandFinality config command) : Digest32 :=
  transcriptDigest
    (commandTranscriptWords store config state command provenance actor
      previousCounter actionCounter finality)

/-- Authenticated authority indexed by the exact expected store, prestate and
command.  The finalized-turn adapter must supply the typed finality certificate. -/
structure AuthenticatedCommand (store : DeploymentStore) (config : Config)
    (state : State) (command : Command) where
  private mk ::
  admissionProvenance : AdmissionProvenance
  actor : Digest32
  expectedStateSequence : Nat
  previousActionCounter : Nat
  actionCounter : Nat
  finality : CommandFinality config command
  transcript : CanonicalCommandTranscript
  exactDigest : ExactCommandDigest
  digest : Digest32
  sequence_exact : expectedStateSequence = state.sequence
  transcript_exact : transcript = commandTranscript store config state command admissionProvenance actor
    previousActionCounter actionCounter finality
  exact_digest_exact : exactDigest = ⟨transcript⟩
  digest_exact : digest = commandDigest store config state command admissionProvenance actor
    previousActionCounter actionCounter finality

theorem AuthenticatedCommand.exact {store : DeploymentStore} {config : Config}
    {state : State} {command : Command}
    (authority : AuthenticatedCommand store config state command) :
    authority.expectedStateSequence = state.sequence ∧
    authority.transcript = commandTranscript store config state command authority.admissionProvenance
      authority.actor
      authority.previousActionCounter authority.actionCounter authority.finality ∧
    authority.exactDigest = ⟨authority.transcript⟩ ∧
    authority.digest = commandDigest store config state command authority.admissionProvenance
      authority.actor
      authority.previousActionCounter authority.actionCounter authority.finality :=
  ⟨authority.sequence_exact, authority.transcript_exact,
    authority.exact_digest_exact, authority.digest_exact⟩

/-! ## Sealed production admission boundary -/

structure CanonicalSettledInclusionTranscript where
  config : ConfigTranscript
  credit : GalleyCreditView
deriving DecidableEq

structure DetachedSignature where
  bytes : CanonicalBytes
deriving DecidableEq

inductive AdmissionDomain where
  | genesis | finality | command | settledInclusion
deriving DecidableEq

def AdmissionDomain.tag : AdmissionDomain → Fin 256
  | .genesis => byte 0x47
  | .finality => byte 0x46
  | .command => byte 0x43
  | .settledInclusion => byte 0x49

/-- Deployment-supplied cryptographic boundary.  Each serializer must be
injective over the exact semantic object; `realHash` and `verifySignature` are
the runtime's production primitives, never the toy `transcriptDigest`. -/
structure AdmissionOracle where
  oracleId : Digest32
  hashAlgorithmId : Digest32
  genesisSerializer : CanonicalSerializer CanonicalGenesisTranscript
  finalitySerializer : CanonicalSerializer CanonicalFinalityTranscript
  commandSerializer : CanonicalSerializer CanonicalCommandTranscript
  settledSerializer : CanonicalSerializer CanonicalSettledInclusionTranscript
  realHash : CanonicalBytes → Digest32
  verifySignature : Digest32 → Digest32 → DetachedSignature → Bool

/-- Opaque authority to invoke a particular deployment oracle.  Its constructor
is unavailable to importers, preventing callers from supplying an always-true
verifier and treating it as production admission. -/
structure AdmissionCapability (oracle : AdmissionOracle) where
  private mk ::
  provenance : AdmissionProvenance

/-- Separate authority for the consensus-finality adapter.  Possessing command
or governance admission does not grant this capability. -/
structure ConsensusFinalityCapability (oracle : AdmissionOracle) where
  private mk ::
  provenance : AdmissionProvenance

/-- Single narrow trusted-host portal.  The runtime supplies this opaque value;
ordinary Lean callers cannot mint it or any capability in the provisioned
bundle.  This is an explicit trusted-beta boundary, not a kernel proof of host
authorization. -/
structure HostInitializer where
  private mk ::
  provenance : AdmissionProvenance
  deploymentId : Digest32

/-- Exact Commons authority bundle plus the unique durable deployment root. -/
structure ProvisionedDeployment (oracle : AdmissionOracle)
    (persistence : PersistenceCASContract) where
  private mk ::
  deploymentId : Digest32
  admission : AdmissionCapability oracle
  finality : ConsensusFinalityCapability oracle
  storeCapability : PersistenceCapability persistence
  rootGenesis : DeploymentRootGenesisCapability persistence
  root : DeploymentRootCertificate persistence

/-- Callable non-fixture provisioning bridge.  `created` must come from the
host's atomic create-if-absent operation, so calling this twice for a different
root is ruled out by the persistence contract's `genesisUnique` law. -/
def provisionDeployment (initializer : HostInitializer) (oracle : AdmissionOracle)
    (persistence : PersistenceCASContract)
    (created : persistence.createGenesis initializer.deploymentId
      (persistence.storeIdentity deploymentGenesisStore)
      (persistence.storeSerializer.encode deploymentGenesisStore.snapshot)) :
    ProvisionedDeployment oracle persistence :=
  let rootCap : DeploymentRootGenesisCapability persistence :=
    ⟨initializer.provenance, initializer.deploymentId⟩
  ⟨initializer.deploymentId, ⟨initializer.provenance⟩, ⟨initializer.provenance⟩,
    ⟨initializer.provenance, initializer.deploymentId⟩, rootCap,
    bootstrapDeploymentRoot rootCap created⟩

inductive AdmissionRefusal where
  | invalidSignature
  | crossOracleProvenance
  | wrongDeploymentRoot
deriving DecidableEq, Repr

def admissionPreimage (oracle : AdmissionOracle) (domain : AdmissionDomain)
    (payload : CanonicalBytes) : CanonicalBytes :=
  [byte 0x50, byte 0x4f, byte 0x41, byte 0x01, domain.tag] ++
    oracle.oracleId.bytes ++ oracle.hashAlgorithmId.bytes ++ payload

def genesisSignatureHash (oracle : AdmissionOracle) (store : DeploymentStore)
    (config : Config) (provenance : AdmissionProvenance) : Digest32 :=
  let exact : CanonicalGenesisTranscript :=
    {
      storeRoot := store.root
      config := configTranscript config
      admissionProvenance := provenance
    }
  oracle.realHash (admissionPreimage oracle .genesis (oracle.genesisSerializer.encode exact))

def finalitySignatureHash (oracle : AdmissionOracle) (store : DeploymentStore)
    (config : Config) (state : State) (epoch : EpochId)
    (finalizedRoot : Digest32) (provenance : AdmissionProvenance) : Digest32 :=
  let exact : CanonicalFinalityTranscript :=
    {
      storeRoot := store.root
      config := configTranscript config
      state
      certifiedEpoch := epoch
      finalizedRoot
      admissionProvenance := provenance
    }
  oracle.realHash (admissionPreimage oracle .finality (oracle.finalitySerializer.encode exact))

def commandSignatureHash (oracle : AdmissionOracle) (store : DeploymentStore) (config : Config)
    (state : State) (command : Command) (provenance : AdmissionProvenance)
    (actor : Digest32) (previous next : Nat)
    (finality : CommandFinality config command) : Digest32 :=
  let exact := commandTranscript store config state command provenance actor previous next finality
  oracle.realHash (admissionPreimage oracle .command (oracle.commandSerializer.encode exact))

def settledInclusionSignatureHash (oracle : AdmissionOracle) (config : Config)
    (credit : GalleyCredit) : Digest32 :=
  let exact : CanonicalSettledInclusionTranscript :=
    { config := configTranscript config, credit := credit.view }
  oracle.realHash (admissionPreimage oracle .settledInclusion
    (oracle.settledSerializer.encode exact))

/-- The only public settled-credit inclusion path. -/
def admitSettledInclusion (oracle : AdmissionOracle) (cap : AdmissionCapability oracle)
    (config : Config) (settled : SettledRun) (signature : DetachedSignature) :
    Except AdmissionRefusal GalleyCredit :=
  let credit := creditFromSettled cap.provenance settled
  let messageHash := settledInclusionSignatureHash oracle config credit
  if oracle.verifySignature config.raw.governanceKey messageHash signature then .ok credit
  else .error .invalidSignature

def admitGenesis (oracle : AdmissionOracle) (cap : AdmissionCapability oracle)
    {persistence : PersistenceCASContract} (root : DeploymentRootCertificate persistence)
    (config : Config) (signature : DetachedSignature) :
    Except AdmissionRefusal (GenesisAuthority root.store config) :=
  if root.admissionProvenance ≠ cap.provenance then .error .crossOracleProvenance
  else if root.deploymentId ≠ config.raw.poolId.deploymentDigest then
    .error .wrongDeploymentRoot
  else
    let messageHash := genesisSignatureHash oracle root.store config cap.provenance
    if oracle.verifySignature config.raw.governanceKey messageHash signature then
    let exact : CanonicalGenesisTranscript :=
      {
        storeRoot := root.store.root
        config := configTranscript config
        admissionProvenance := cap.provenance
      }
    .ok {
      admissionProvenance := cap.provenance
      canonicalStoreRoot := root.store.root
      signedConfig := configTranscript config
      transcript := exact
      exactDigest := ⟨exact⟩
      wireTranscript := genesisAuthorityTranscript root.store config
      digest := transcriptDigest (genesisAuthorityTranscript root.store config)
    }
    else .error .invalidSignature

def admitConsensusFinality (oracle : AdmissionOracle)
    (cap : ConsensusFinalityCapability oracle)
    (store : DeploymentStore) (config : Config) (state : State)
    (epoch : EpochId) (finalizedRoot : Digest32)
    (signature : DetachedSignature) :
    Except AdmissionRefusal (FinalizedEpochCertificate config epoch) :=
  let messageHash := finalitySignatureHash oracle store config state epoch finalizedRoot cap.provenance
  if oracle.verifySignature config.raw.finalityKey messageHash signature then
    let exact : CanonicalFinalityTranscript :=
      {
        storeRoot := store.root
        config := configTranscript config
        state
        certifiedEpoch := epoch
        finalizedRoot
        admissionProvenance := cap.provenance
      }
    let wire := [5, epoch.value, state.sequence] ++ configTranscriptWords config ++
      digestWords state.commitment ++ digestWords finalizedRoot
    .ok {
      admissionProvenance := cap.provenance
      canonicalStoreRoot := store.root
      canonicalState := state
      finalizedRoot
      transcript := exact
      exactDigest := ⟨exact⟩
      wireTranscript := wire
      digest := transcriptDigest wire
      transcript_exact := rfl
      exact_digest_exact := rfl
      wire_transcript_exact := rfl
      digest_exact := rfl
    }
  else .error .invalidSignature

def admitCommand (oracle : AdmissionOracle) (cap : AdmissionCapability oracle)
    (store : DeploymentStore) (config : Config) (state : State) (command : Command)
    (actor : Digest32) (finality : CommandFinality config command)
    (signature : DetachedSignature) :
    Except AdmissionRefusal (AuthenticatedCommand store config state command) :=
  let previous := actorCounterFor state.actorCounters actor
  let next := previous + 1
  let exact := commandTranscript store config state command cap.provenance actor previous next finality
  let messageHash := commandSignatureHash oracle store config state command cap.provenance
    actor previous next finality
  if finality.admissionProvenance?.any (fun provenance => decide (provenance ≠ cap.provenance)) then
    .error .crossOracleProvenance
  else if oracle.verifySignature actor messageHash signature then
    .ok {
      admissionProvenance := cap.provenance
      actor
      expectedStateSequence := state.sequence
      previousActionCounter := previous
      actionCounter := next
      finality
      transcript := exact
      exactDigest := ⟨exact⟩
      digest := commandDigest store config state command cap.provenance actor previous next finality
      sequence_exact := rfl
      transcript_exact := rfl
      exact_digest_exact := rfl
      digest_exact := rfl
    }
  else .error .invalidSignature

inductive Refusal where
  | staleStore
  | staleHead
  | unopenedPool
  | invalidState
  | invalidSuccessor
  | wrongPool
  | wrongConfig
  | staleStateSequence
  | actionCounterMismatch
  | actionCounterOutOfRange
  | actorMismatch
  | governanceCapabilityMismatch
  | crossOracleProvenance
  | finalityHeadMismatch
  | notCollecting
  | notFinalized
  | wrongEpoch
  | wrongContentDomain
  | sourceNotAuthored
  | unknownPlayer
  | creditReplay
  | creditCounterMismatch
  | creditCounterOutOfRange
  | notGalleyContribution
  | playerCapExceeded
  | poolCapacityExceeded
  | receiptCapacityExceeded
  | unknownRecipe
  | allocationNotAuthored
  | invalidBatchSize
  | insufficientContributors
  | scarceSupply
  | scarceCohesion
  | reserveCapacityExceeded
  | ineligibleForAllocation
  | alreadyClaimed
  | noRations
  | epochDoesNotAdvance
  | earlyAdvance
  | authenticationMismatch
deriving DecidableEq, Repr

def pureGalleyContributionB (contribution : Contribution) : Bool :=
  decide (contribution.intel.val = 0) &&
  decide (contribution.influence.val = 0) &&
  decide (contribution.score.val = 0) &&
  decide (contribution.relics = ∅) &&
  decide (0 < contribution.supplies.val + contribution.cohesion.val)

private def applyCredit (state : State) (credit : GalleyCredit) : State :=
  let supply := credit.contribution.supplies.val
  let cohesion := credit.contribution.cohesion.val
  { state with
    poolSupply := state.poolSupply + supply
    poolCohesion := state.poolCohesion + cohesion
    totalSupplyReceived := state.totalSupplyReceived + supply
    totalCohesionReceived := state.totalCohesionReceived + cohesion
    creditCounters := setCreditCounter state.creditCounters credit.counterKey credit.playerCounter
    tallies := addTally state.tallies credit.playerKey supply cohesion
    consumedCredits := insert credit.receiptKey state.consumedCredits
  }

private def finalizeBatch (config : Config) (state : State) (recipe : Recipe)
    (allocation : Allocation) (servings : Nat) : State :=
  let supplyCost := servings * recipe.supplyPerRation
  let outcome : MenuOutcome := {
    epoch := state.epoch
    recipe := recipe.id
    allocation
    servings
    contributors := (contributors config state).card
    candidateArtifact := recipe.candidateArtifact
  }
  let batch : Batch := {
    outcome
    claimDeadline := ⟨state.epoch.value + config.raw.claimWindow⟩
    remaining := servings
    claimed := ∅
  }
  { state with
    reserveSupply := state.reserveSupply + state.poolSupply - supplyCost
    reserveCohesion := state.reserveCohesion + state.poolCohesion - recipe.cohesionCost
    poolSupply := 0
    poolCohesion := 0
    totalSupplyUsed := state.totalSupplyUsed + supplyCost
    totalCohesionUsed := state.totalCohesionUsed + recipe.cohesionCost
    producedRations := state.producedRations + servings
    phase := finalizedPhase batch
    lastMenu := some outcome
    candidateArtifacts := insert recipe.candidateArtifact state.candidateArtifacts
  }

private def claimRation (state : State) (batch : Batch) (player : Digest32) : State :=
  { state with
    playerRationsClaimed := state.playerRationsClaimed + 1
    phase := finalizedPhase {
      batch with
      remaining := batch.remaining - 1
      claimed := insert player batch.claimed
    }
  }

private def advanceEpoch (config : Config) (state : State) (batch : Batch) (next : EpochId) : State :=
  { state with
    epoch := next
    collectionDeadline := ⟨next.value + config.raw.collectionWindow⟩
    poolSupply := 0
    poolCohesion := 0
    commonsRationsConsumed := state.commonsRationsConsumed + batch.remaining
    tallies := []
    consumedCredits := ∅
    phase := collectingPhase
  }

/-- Timeout rollover for an unfinalizable collecting epoch.  Resources and
global nullifiers stay put; only epoch-local admission counters/tallies reset so
new settled work can join the carried pool. -/
private def rolloverEpoch (config : Config) (state : State) (next : EpochId) : State :=
  { state with
    epoch := next
    collectionDeadline := ⟨next.value + config.raw.collectionWindow⟩
    creditCounters := []
    tallies := []
    consumedCredits := ∅
  }

private def successorCommitment (commandHash : Digest32) : Digest32 :=
  transcriptDigest (3 :: digestWords commandHash)

private def commitAuthenticated {store : DeploymentStore} {config : Config}
    {before : State} {command : Command}
    (state : State) (authority : AuthenticatedCommand store config before command) : State :=
  { state with
    sequence := state.sequence + 1
    actorCounters := setActorCounter state.actorCounters authority.actor authority.actionCounter
    commitment := successorCommitment authority.digest
  }

private def contributeCore (store : DeploymentStore) (config : Config) (state : State)
    (credit : GalleyCredit)
    (authority : AuthenticatedCommand store config state (.contribute credit)) : Except Refusal State :=
  match state.phase.batch with
  | some _ => .error .notCollecting
  | none =>
      if authority.actor ≠ credit.playerKey then .error .actorMismatch
      else if credit.poolId ≠ config.raw.poolId then .error .wrongPool
      else if credit.contentEpoch ≠ state.epoch then .error .wrongEpoch
      else if credit.federationId ≠ config.raw.poolId.federationId ∨
          credit.contentRoot ≠ config.raw.poolId.contentRoot ∨
          credit.activationDigest ≠ config.raw.poolId.activationDigest ∨
          credit.contentSession ≠ config.raw.poolId.contentSession then
        .error .wrongContentDomain
      else if { mission := credit.sourceMission, runSeed := credit.runSeed } ∉ config.raw.sources then
        .error .sourceNotAuthored
      else if credit.playerKey ∉ config.raw.members then .error .unknownPlayer
      else if credit.receiptKey ∈ state.consumedCredits then .error .creditReplay
      else if creditCounterFor state.creditCounters credit.counterKey ≠
          credit.previousPlayerCounter then .error .creditCounterMismatch
      else if PLAYER_COUNTER_MODULUS ≤ credit.playerCounter then .error .creditCounterOutOfRange
      else if pureGalleyContributionB credit.contribution ≠ true then
        .error .notGalleyContribution
      else
        let old := tallyFor state.tallies credit.playerKey
        let supply := credit.contribution.supplies.val
        let cohesion := credit.contribution.cohesion.val
        if config.raw.perPlayerSupplyCap < old.supply + supply ∨
            config.raw.perPlayerCohesionCap < old.cohesion + cohesion then
          .error .playerCapExceeded
        else if config.raw.maxPoolSupply < state.poolSupply + supply ∨
            config.raw.maxPoolCohesion < state.poolCohesion + cohesion then
          .error .poolCapacityExceeded
        else if config.raw.maxReceiptsPerEpoch ≤ state.consumedCredits.card then
          .error .receiptCapacityExceeded
        else .ok (applyCredit state credit)

private def finalizeCore (store : DeploymentStore) (config : Config) (state : State) (epoch : EpochId)
    (recipeId : RecipeId) (allocation : Allocation) (servings : Nat)
    (authority : AuthenticatedCommand store config state
      (.finalize epoch recipeId allocation servings)) : Except Refusal State :=
  match state.phase.batch with
  | some _ => .error .notCollecting
  | none =>
      if authority.actor ≠ config.raw.governanceKey then .error .governanceCapabilityMismatch
      else if epoch ≠ state.epoch then .error .wrongEpoch
      else match findRecipe? config recipeId with
        | none => .error .unknownRecipe
        | some recipe =>
            if allocation ∉ recipe.allocations then .error .allocationNotAuthored
            else if servings = 0 ∨ recipe.maxBatch < servings then .error .invalidBatchSize
            else if (contributors config state).card < recipe.minContributors then
              .error .insufficientContributors
            else
              let supplyCost := servings * recipe.supplyPerRation
              let availableSupply := state.reserveSupply + state.poolSupply
              let availableCohesion := state.reserveCohesion + state.poolCohesion
              if availableSupply < supplyCost then .error .scarceSupply
              else if availableCohesion < recipe.cohesionCost then .error .scarceCohesion
              else if config.raw.maxReserveSupply < availableSupply - supplyCost ∨
                  config.raw.maxReserveCohesion < availableCohesion - recipe.cohesionCost then
                .error .reserveCapacityExceeded
              else .ok (finalizeBatch config state recipe allocation servings)

private def claimCore (store : DeploymentStore) (config : Config) (state : State)
    (epoch : EpochId) (player : Digest32)
    (authority : AuthenticatedCommand store config state (.claim epoch player)) : Except Refusal State :=
  match state.phase.batch with
  | none => .error .notFinalized
  | some batch =>
      if authority.actor ≠ player then .error .actorMismatch
      else if epoch ≠ state.epoch then .error .wrongEpoch
      else if player ∉ config.raw.members then .error .unknownPlayer
      else if allocationEligibleB state batch.outcome.allocation player ≠ true then
        .error .ineligibleForAllocation
      else if player ∈ batch.claimed then .error .alreadyClaimed
      else if batch.remaining = 0 then .error .noRations
      else .ok (claimRation state batch player)

private def advanceCore (store : DeploymentStore) (config : Config) (state : State) (next : EpochId)
    (authority : AuthenticatedCommand store config state (.advance next)) : Except Refusal State :=
  match state.phase.batch with
  | none => .error .notFinalized
  | some batch =>
      if authority.actor ≠ config.raw.governanceKey then .error .governanceCapabilityMismatch
      else if ¬state.epoch.value < next.value then .error .epochDoesNotAdvance
      else if next.value < batch.claimDeadline.value then .error .earlyAdvance
      else .ok (advanceEpoch config state batch next)

private def rolloverCore (store : DeploymentStore) (config : Config) (state : State)
    (next : EpochId)
    (authority : AuthenticatedCommand store config state (.rollover next)) : Except Refusal State :=
  match state.phase.batch with
  | some _ => .error .notCollecting
  | none =>
      if authority.actor ≠ config.raw.governanceKey then .error .governanceCapabilityMismatch
      else if ¬state.epoch.value < next.value then .error .epochDoesNotAdvance
      else if next.value < state.collectionDeadline.value then .error .earlyAdvance
      else .ok (rolloverEpoch config state next)

private def coreStep (store : DeploymentStore) (config : Config) (state : State) (command : Command)
    (authority : AuthenticatedCommand store config state command) : Except Refusal State :=
  match command with
  | .contribute credit => contributeCore store config state credit authority
  | .finalize epoch recipe allocation servings =>
      finalizeCore store config state epoch recipe allocation servings authority
  | .claim epoch player => claimCore store config state epoch player authority
  | .advance next => advanceCore store config state next authority
  | .rollover next => rolloverCore store config state next authority

/-- Branch-local checked transition.  It is private because local replay safety
cannot prevent a fork from spending the same nullifier twice. -/
private def executeAtHead (store : DeploymentStore) (config : Config) (state : State)
    (command : Command)
    (authority : AuthenticatedCommand store config state command) : Except Refusal State :=
  if stateValidB config state ≠ true then .error .invalidState
  else if authority.expectedStateSequence ≠ state.sequence then .error .staleStateSequence
  else if authority.admissionProvenance ≠ state.admissionProvenance ∨
      authority.finality.admissionProvenance?.any
        (fun provenance => decide (provenance ≠ state.admissionProvenance)) then
    .error .crossOracleProvenance
  else if authority.finality.matchesHeadB store state ≠ true then
    .error .finalityHeadMismatch
  else if authority.transcript ≠ commandTranscript store config state command
      authority.admissionProvenance authority.actor
      authority.previousActionCounter authority.actionCounter authority.finality ∨
      authority.exactDigest ≠ ⟨authority.transcript⟩ ∨
      authority.digest ≠ commandDigest store config state command authority.admissionProvenance authority.actor
        authority.previousActionCounter authority.actionCounter authority.finality then
    .error .authenticationMismatch
  else if authority.previousActionCounter ≠ actorCounterFor state.actorCounters authority.actor ∨
      authority.actionCounter ≠ authority.previousActionCounter + 1 then
    .error .actionCounterMismatch
  else if PLAYER_COUNTER_MODULUS ≤ authority.actionCounter then .error .actionCounterOutOfRange
  else do
    let candidate ← coreStep store config state command authority
    let committed := commitAuthenticated candidate authority
    if stateValidB config committed = true then .ok committed else .error .invalidSuccessor

def commandReceiptKey? : Command → Option ReceiptKey
  | .contribute credit => some credit.receiptKey
  | _ => none

private def commitStore (store : DeploymentStore) (config : Config) (command : Command)
    (state : State) : DeploymentStore :=
  let redeemed := match commandReceiptKey? command with
    | none => store.redeemedCredits
    | some key => insert key store.redeemedCredits
  let head : PoolHead := { poolId := config.raw.poolId, config := configTranscript config, head := state }
  ⟨setPoolHead store.pools head, redeemed, store.sequence + 1⟩

/-- Pure checked mutation candidate over an exact presented store/head/config and
global receipt-nullifier snapshot.  This function does not itself perform atomic
I/O: the runtime must compare against its durable current store and issue a
`PersistedTransition`; only that adapter contract supplies single-winner CAS. -/
private def execute (canonical expected : DeploymentStore) (config : Config) (state : State)
    (command : Command)
    (authority : AuthenticatedCommand expected config state command) :
    Except Refusal (DeploymentStore × State) :=
  if canonical != expected then .error .staleStore
  else match poolHeadById? canonical.pools config.raw.poolId with
    | none => .error .unopenedPool
    | some head =>
      if head.config != configTranscript config then .error .wrongConfig
      else if head.head != state then .error .staleHead
      else match commandReceiptKey? command with
        | some key =>
          if key ∈ canonical.redeemedCredits then .error .creditReplay
          else do
            let committed ← executeAtHead expected config state command authority
            .ok (commitStore canonical config command committed, committed)
        | none => do
          let committed ← executeAtHead expected config state command authority
          .ok (commitStore canonical config command committed, committed)

/-! ## Durable continuation surface -/

/-- Only this opaque value may be used as the predecessor of a production
command.  Raw `(DeploymentStore × State)` values returned by the private pure
candidate evaluator are therefore not continuation authority. -/
structure PersistedPoolRuntime (persistence : PersistenceCASContract) where
  private mk ::
  admissionProvenance : AdmissionProvenance
  deploymentId : Digest32
  store : DeploymentStore
  config : Config
  state : State
  rooted : persistence.rootedAt deploymentId store.sequence
    (persistence.storeIdentity store) (persistence.storeSerializer.encode store.snapshot)

inductive PersistenceRefusal where
  | provenanceMismatch
  | wrongDeployment
  | unopenedPool
  | wrongConfig
  | staleHead
deriving DecidableEq, Repr

/-- Initial durable-head admission is deliberately capability-gated.  The
adapter must present the exact store snapshot it just loaded; structural checks
then bind its pool head, full config and prestate. -/
def admitPersistedRuntime {persistence : PersistenceCASContract}
    {store : DeploymentStore} (load : DurableStoreLoad persistence store)
    (config : Config) (state : State) :
    Except PersistenceRefusal (PersistedPoolRuntime persistence) :=
  if load.admissionProvenance ≠ state.admissionProvenance then
    .error .provenanceMismatch
  else if load.deploymentId ≠ config.raw.poolId.deploymentDigest then
    .error .wrongDeployment
  else match poolHeadById? store.pools config.raw.poolId with
    | none => .error .unopenedPool
    | some head =>
      if head.config ≠ configTranscript config then .error .wrongConfig
      else if head.head ≠ state then .error .staleHead
      else .ok ⟨load.admissionProvenance, load.deploymentId, store, config, state, load.rooted⟩

/-- Unpersisted result.  The constructor is private and the value cannot be fed
to `proposePersisted`; it can only be promoted by an exact CAS receipt. -/
structure TransitionCandidate {persistence : PersistenceCASContract}
    (before : PersistedPoolRuntime persistence) (command : Command) where
  private mk ::
  afterStore : DeploymentStore
  afterState : State

def proposePersisted {persistence : PersistenceCASContract}
    (before : PersistedPoolRuntime persistence) (command : Command)
    (authority : AuthenticatedCommand before.store before.config before.state command) :
    Except Refusal (TransitionCandidate before command) := do
  let (afterStore, afterState) ←
    execute before.store before.store before.config before.state command authority
  .ok ⟨afterStore, afterState⟩

/-- The sole continuation constructor.  Its dependent receipt states that this
exact candidate won CAS against this exact persisted predecessor. -/
def continueFromCommit {persistence : PersistenceCASContract}
    {before : PersistedPoolRuntime persistence} {command : Command}
    (candidate : TransitionCandidate before command)
    (receipt : PersistedTransition persistence before.deploymentId
      before.store candidate.afterStore) :
    Except PersistenceRefusal (PersistedPoolRuntime persistence) :=
  if receipt.admissionProvenance ≠ before.admissionProvenance then
    .error .provenanceMismatch
  else
    have rootedAfter : persistence.rootedAt before.deploymentId candidate.afterStore.sequence
        (persistence.storeIdentity candidate.afterStore)
        (persistence.storeSerializer.encode candidate.afterStore.snapshot) := by
      simpa [PersistenceCASContract.storeIdentity] using
        persistence.casPreservesRoot before.rooted receipt.committed
    .ok ⟨before.admissionProvenance, before.deploymentId, candidate.afterStore,
      before.config, candidate.afterState, rootedAfter⟩

/-! ## Kernel invariants -/

theorem applyCredit_preserves_resources (state : State) (credit : GalleyCredit)
    (conserved : ResourcesConserved state) : ResourcesConserved (applyCredit state credit) := by
  rcases conserved with ⟨supply, cohesion⟩
  constructor <;> simp [applyCredit] at * <;> omega

theorem finalizeBatch_preserves_resources (config : Config) (state : State)
    (recipe : Recipe) (allocation : Allocation) (servings : Nat)
    (conserved : ResourcesConserved state)
    (supplyEnough : servings * recipe.supplyPerRation ≤ state.reserveSupply + state.poolSupply)
    (cohesionEnough : recipe.cohesionCost ≤ state.reserveCohesion + state.poolCohesion) :
    ResourcesConserved (finalizeBatch config state recipe allocation servings) := by
  rcases conserved with ⟨supply, cohesion⟩
  constructor <;> simp [finalizeBatch] at * <;> omega

theorem claimRation_preserves_resources (state : State) (batch : Batch)
    (player : Digest32) (conserved : ResourcesConserved state) :
    ResourcesConserved (claimRation state batch player) := by
  simpa [claimRation, ResourcesConserved] using conserved

theorem advanceEpoch_preserves_resources (config : Config) (state : State) (batch : Batch) (next : EpochId)
    (poolsEmpty : state.poolSupply = 0 ∧ state.poolCohesion = 0)
    (conserved : ResourcesConserved state) : ResourcesConserved (advanceEpoch config state batch next) := by
  rcases poolsEmpty with ⟨supplyEmpty, cohesionEmpty⟩
  simpa [advanceEpoch, ResourcesConserved, supplyEmpty, cohesionEmpty] using conserved

theorem rolloverEpoch_preserves_resources (config : Config) (state : State) (next : EpochId)
    (conserved : ResourcesConserved state) : ResourcesConserved (rolloverEpoch config state next) := by
  simpa [rolloverEpoch, ResourcesConserved] using conserved

theorem rolloverEpoch_carries_settled_pool (config : Config) (state : State) (next : EpochId) :
    (rolloverEpoch config state next).poolSupply = state.poolSupply ∧
      (rolloverEpoch config state next).poolCohesion = state.poolCohesion :=
  ⟨rfl, rfl⟩

theorem candidate_is_exact_authored_recipe (config : Config) (state : State) (recipe : Recipe)
    (allocation : Allocation) (servings : Nat) :
    recipe.candidateArtifact ∈
      (finalizeBatch config state recipe allocation servings).candidateArtifacts := by
  simp [finalizeBatch]

structure EconomicProjection where
  reserveSupply : Nat
  reserveCohesion : Nat
  totalSupplyReceived : Nat
  totalCohesionReceived : Nat
  totalSupplyUsed : Nat
  totalCohesionUsed : Nat
  producedRations : Nat
  playerRationsClaimed : Nat
  commonsRationsConsumed : Nat
  creditCounters : List CreditCounterRow
  actorCounters : List ActorCounterRow
  candidateArtifacts : Finset ArtifactRef
deriving DecidableEq

def economicProjection (state : State) : EconomicProjection where
  reserveSupply := state.reserveSupply
  reserveCohesion := state.reserveCohesion
  totalSupplyReceived := state.totalSupplyReceived
  totalCohesionReceived := state.totalCohesionReceived
  totalSupplyUsed := state.totalSupplyUsed
  totalCohesionUsed := state.totalCohesionUsed
  producedRations := state.producedRations
  playerRationsClaimed := state.playerRationsClaimed
  commonsRationsConsumed := state.commonsRationsConsumed
  creditCounters := state.creditCounters
  actorCounters := state.actorCounters
  candidateArtifacts := state.candidateArtifacts

/-- Quiet-epoch gaps do not alter supplies, rations, counters, or candidates. -/
theorem advance_gap_economically_irrelevant (config : Config) (state : State) (batch : Batch)
    (near far : EpochId) :
    economicProjection (advanceEpoch config state batch near) =
      economicProjection (advanceEpoch config state batch far) := rfl

/-! ## Fully settled multiplayer fixture -/

def digest (tag : Nat) : Digest32 where
  bytes := List.replicate 32 (byte tag)
  length_eq := by simp

def alice : Digest32 := digest 1
def bob : Digest32 := digest 2
def cara : Digest32 := digest 3
def dave : Digest32 := digest 4
def governance : Digest32 := digest 5
def federation : Digest32 := digest 80
def contentRoot : Digest32 := digest 81
def activationDigest : Digest32 := digest 82
def contentSession : Digest32 := digest 83
def deploymentDigest : Digest32 := digest 84
def sourceMissionId : MissionId := ⟨700⟩
def sourceRunSeed : Digest32 := digest 85
def epochTwelve : EpochId := ⟨12⟩
def epochNineteen : EpochId := ⟨19⟩

def demoPoolId : PoolId where
  federationId := federation
  contentRoot
  activationDigest
  contentSession
  deploymentDigest

def candidateArtifact (id : Nat) : ArtifactRef where
  missionId := ⟨900⟩
  artifactId := ⟨id⟩
  sourceDigest := digest (100 + id)
  contentDigest := deploymentDigest

def broth : Recipe where
  id := ⟨1⟩
  supplyPerRation := 2
  cohesionCost := 1
  maxBatch := 4
  minContributors := 2
  allocations := {.openCommons, .contributorsFirst}
  candidateArtifact := candidateArtifact 1

def embercakes : Recipe where
  id := ⟨2⟩
  supplyPerRation := 3
  cohesionCost := 4
  maxBatch := 3
  minContributors := 3
  allocations := {.cohesionCrew}
  candidateArtifact := candidateArtifact 2

def lavishPlate : Recipe where
  id := ⟨3⟩
  supplyPerRation := 5
  cohesionCost := 2
  maxBatch := 3
  minContributors := 2
  allocations := {.openCommons}
  candidateArtifact := candidateArtifact 3

def demoRawConfig : RawConfig where
  poolId := demoPoolId
  configDigest := deploymentDigest
  openingEpoch := epochTwelve
  governanceKey := governance
  finalityKey := digest 6
  members := {alice, bob, cara, dave}
  sources := {{ mission := sourceMissionId, runSeed := sourceRunSeed }}
  allowedBeta := {candidateArtifact 1, candidateArtifact 2, candidateArtifact 3}
  maxPoolSupply := 20
  maxPoolCohesion := 20
  maxReserveSupply := 10
  maxReserveCohesion := 10
  perPlayerSupplyCap := 6
  perPlayerCohesionCap := 4
  maxReceiptsPerEpoch := 8
  collectionWindow := 3
  claimWindow := 2
  initialReserveSupply := 3
  initialReserveCohesion := 1
  recipes := [broth, embercakes, lavishPlate]

def demoConfig : Config where
  raw := demoRawConfig
  valid := by native_decide

def sourceArtifact : ArtifactRef where
  missionId := sourceMissionId
  artifactId := ⟨701⟩
  sourceDigest := digest 86
  contentDigest := deploymentDigest

def sourceReward : Contribution where
  intel := 0
  supplies := 3
  cohesion := 2
  influence := 0
  score := 0
  relics := ∅
  relics_bounded := by simp

def sourceBudget : ContributionBudget where
  intel := 0
  supplies := 3
  cohesion := 2
  influence := 0
  score := 0
  relics := 0

def sourceMission (epoch : EpochId) : MissionSpec where
  missionId := sourceMissionId
  artifact := sourceArtifact
  epoch
  federationId := federation
  contentRoot
  activationDigest
  contentSession
  runSeed := sourceRunSeed
  budget := sourceBudget
  allowedRelics := ∅
  privacy := .public
  ballot := .none
  artifact_matches := rfl
  allowed_relics_bounded := by simp

theorem sourceReward_accepted (epoch : EpochId) :
    (sourceMission epoch).acceptsContribution sourceReward = true := by
  simp [MissionSpec.acceptsContribution, Contribution.within, sourceMission,
    sourceReward, sourceBudget]

def sourceConfig (epoch : EpochId) : SignalTriangulation.Config where
  target := SignalTriangulation.targetFromSeed sourceRunSeed
  mission := sourceMission epoch
  reward := sourceReward
  reward_accepted := sourceReward_accepted epoch
  target_eq := rfl

def playerCounterKey (epoch : EpochId) (player : Digest32) : PlayerCounterKey where
  federationId := federation
  contentSession
  contentEpoch := epoch
  playerKey := player

def fixtureCanon (epoch : EpochId) : CanonState :=
  CanonState.empty federation contentRoot activationDigest contentSession epoch governance

def activeFor (epoch : EpochId) (canon : CanonState) : ActiveRunState where
  game := .signal (sourceConfig epoch)
  federationId := federation
  contentRoot
  activationDigest
  contentSession
  contentEpoch := epoch
  runSeed := sourceRunSeed
  world := canon.world
  playerCounters := canon.playerCounters

def carrierFor (epoch : EpochId) (player actorRoot : Digest32) (canon : CanonState) :
    FinalizedCarrier where
  federationId := federation
  contentRoot
  activationDigest
  contentSession
  contentEpoch := epoch
  actorRoot
  playerKey := player
  currentPlayerCounter := canon.playerCounters.lookup (playerCounterKey epoch player)

def claimFor (epoch : EpochId) (player actorRoot : Digest32) (canon : CanonState) : RunClaim :=
  let carrier := carrierFor epoch player actorRoot canon
  {
    config := (ActiveGame.configClaim (.signal (sourceConfig epoch)))
    federationId := federation
    contentRoot
    activationDigest
    contentSession
    contentEpoch := epoch
    runSeed := sourceRunSeed
    actorRoot
    playerKey := player
    claimedPreviousPlayerCounter := carrier.currentPlayerCounter.val
  }

private def fixtureProvenance : AdmissionProvenance := ⟨digest 198⟩
private def alternateProvenance : AdmissionProvenance := ⟨digest 199⟩

private def settleFixture? (epoch : EpochId) (player actorRoot : Digest32) (canon : CanonState) :
    Option (GalleyCredit × CanonState) :=
  let active := activeFor epoch canon
  let carrier := carrierFor epoch player actorRoot canon
  let claim := claimFor epoch player actorRoot canon
  match settleActiveRun active carrier claim
      (.signal [.submit (SignalTriangulation.targetFromSeed sourceRunSeed)]) canon with
  | none => none
  | some settled => some (creditFromSettled fixtureProvenance settled, settled.postCanon)

private def wrongRootSettlement? : Option SettledRun :=
  let canon := fixtureCanon epochTwelve
  let active := activeFor epochTwelve canon
  let carrier := carrierFor epochTwelve alice (digest 200) canon
  let wrongClaim := claimFor epochTwelve alice (digest 201) canon
  settleActiveRun active carrier wrongClaim
    (.signal [.submit (SignalTriangulation.targetFromSeed sourceRunSeed)]) canon

private def fixtureStore : DeploymentStore := ⟨[], ∅, 0⟩

private def fixtureGenesisAuthority (store : DeploymentStore) (config : Config) :
    GenesisAuthority store config where
  admissionProvenance := fixtureProvenance
  canonicalStoreRoot := store.root
  signedConfig := configTranscript config
  transcript := {
    storeRoot := store.root
    config := configTranscript config
    admissionProvenance := fixtureProvenance
  }
  exactDigest := ⟨{
    storeRoot := store.root
    config := configTranscript config
    admissionProvenance := fixtureProvenance
  }⟩
  wireTranscript := genesisAuthorityTranscript store config
  digest := transcriptDigest (genesisAuthorityTranscript store config)

private abbrev PoolRuntime := DeploymentStore × State

private def fixtureOpen? (config : Config) : Option PoolRuntime :=
  (openPool fixtureStore fixtureStore config
    (fixtureGenesisAuthority fixtureStore config)).toOption

private def fixtureFinality (store : DeploymentStore) (config : Config) (state : State)
    (epoch : EpochId) :
    FinalizedEpochCertificate config epoch :=
  let root := digest (220 + epoch.value)
  let transcript : CanonicalFinalityTranscript :=
    {
      storeRoot := store.root
      config := configTranscript config
      state
      certifiedEpoch := epoch
      finalizedRoot := root
      admissionProvenance := fixtureProvenance
    }
  let wire := [5, epoch.value, state.sequence] ++ configTranscriptWords config ++
    digestWords state.commitment ++ digestWords root
  {
    admissionProvenance := fixtureProvenance
    canonicalStoreRoot := store.root
    canonicalState := state
    finalizedRoot := root
    transcript
    exactDigest := ⟨transcript⟩
    wireTranscript := wire
    digest := transcriptDigest wire
    transcript_exact := rfl
    exact_digest_exact := rfl
    wire_transcript_exact := rfl
    digest_exact := rfl
  }

private def fixtureOpenedRuntime : PoolRuntime :=
  (fixtureOpen? demoConfig).get (by native_decide)

private def fixtureOpeningFinality (epoch : EpochId) :
    FinalizedEpochCertificate demoConfig epoch :=
  fixtureFinality fixtureOpenedRuntime.1 demoConfig fixtureOpenedRuntime.2 epoch

private def fixtureAuthority (store : DeploymentStore) (config : Config) (state : State)
    (command : Command) (actor : Digest32) (finality : CommandFinality config command) :
    AuthenticatedCommand store config state command :=
  let previous := actorCounterFor state.actorCounters actor
  let next := previous + 1
  let transcript := commandTranscript store config state command fixtureProvenance
    actor previous next finality
  {
    admissionProvenance := fixtureProvenance
    actor
    expectedStateSequence := state.sequence
    previousActionCounter := previous
    actionCounter := next
    finality
    transcript
    exactDigest := ⟨transcript⟩
    digest := commandDigest store config state command fixtureProvenance actor previous next finality
    sequence_exact := rfl
    transcript_exact := rfl
    exact_digest_exact := rfl
    digest_exact := rfl
  }

private def executeContribution (runtime : PoolRuntime) (credit : GalleyCredit) :
    Except Refusal PoolRuntime :=
  let (store, state) := runtime
  let command := Command.contribute credit
  execute store store demoConfig state command
    (fixtureAuthority store demoConfig state command credit.playerKey (.contribute credit))

private def collectThree? : Option PoolRuntime := do
  let canon0 := fixtureCanon epochTwelve
  let (aliceCredit, canon1) ← settleFixture? epochTwelve alice (digest 210) canon0
  let (bobCredit, canon2) ← settleFixture? epochTwelve bob (digest 211) canon1
  let (caraCredit, _canon3) ← settleFixture? epochTwelve cara (digest 212) canon2
  let opened ← fixtureOpen? demoConfig
  let one ← (executeContribution opened aliceCredit).toOption
  let two ← (executeContribution one bobCredit).toOption
  (executeContribution two caraCredit).toOption

private def finalizeWith (runtime : PoolRuntime) (recipe : Recipe) (allocation : Allocation)
    (servings : Nat) : Except Refusal PoolRuntime :=
  let (store, state) := runtime
  let command := Command.finalize state.epoch recipe.id allocation servings
  let finality := CommandFinality.finalize state.epoch recipe.id allocation servings
    (fixtureFinality store demoConfig state state.epoch)
  execute store store demoConfig state command
    (fixtureAuthority store demoConfig state command governance finality)

private def emberFinalized? : Option PoolRuntime := do
  let collected ← collectThree?
  (finalizeWith collected embercakes .cohesionCrew 3).toOption

private def claimForSelf (runtime : PoolRuntime) (player : Digest32) : Except Refusal PoolRuntime :=
  let (store, state) := runtime
  let command := Command.claim state.epoch player
  execute store store demoConfig state command
    (fixtureAuthority store demoConfig state command player (.claim state.epoch player))

private def claimedByThree? : Option PoolRuntime := do
  let finalized ← emberFinalized?
  let one ← (claimForSelf finalized alice).toOption
  let two ← (claimForSelf one bob).toOption
  (claimForSelf two cara).toOption

private def advanceWith (runtime : PoolRuntime) (next : EpochId) : Except Refusal PoolRuntime :=
  let (store, state) := runtime
  let command := Command.advance next
  let finality := CommandFinality.advance next (fixtureFinality store demoConfig state next)
  execute store store demoConfig state command
    (fixtureAuthority store demoConfig state command governance finality)

private def rolloverWith (runtime : PoolRuntime) (next : EpochId) : Except Refusal PoolRuntime :=
  let (store, state) := runtime
  let command := Command.rollover next
  let finality := CommandFinality.rollover next
    (fixtureFinality store demoConfig state next)
  execute store store demoConfig state command
    (fixtureAuthority store demoConfig state command governance finality)

theorem arbitrary_root_settlement_unavailable : wrongRootSettlement? = none := by
  native_decide

theorem real_settlements_feed_exact_pool :
    collectThree?.map (fun runtime =>
      let state := runtime.2
      decide (state.poolSupply = 9) && decide (state.poolCohesion = 6) &&
      decide ((contributors demoConfig state).card = 3) && resourcesConservedB state) = some true := by
  native_decide

theorem stale_consensus_finality_head_is_refused :
    (match collectThree? with
    | none => false
    | some (store, state) =>
        let command := Command.finalize state.epoch broth.id .openCommons 1
        let stale := fixtureOpeningFinality state.epoch
        let finality := CommandFinality.finalize state.epoch broth.id .openCommons 1 stale
        decide (execute store store demoConfig state command
          (fixtureAuthority store demoConfig state command governance finality) =
            .error .finalityHeadMismatch)) = true := by
  native_decide

theorem collecting_timeout_rolls_settled_pool_without_replay :
    (match collectThree? with
    | none => false
    | some runtime =>
        let next := runtime.2.collectionDeadline
        match rolloverWith runtime next with
        | .error _ => false
        | .ok later =>
            decide (later.2.epoch = next) &&
            decide (later.2.poolSupply = runtime.2.poolSupply) &&
            decide (later.2.poolCohesion = runtime.2.poolCohesion) &&
            decide (later.2.consumedCredits = ∅) &&
            decide (later.1.redeemedCredits = runtime.1.redeemedCredits) &&
            decide ((contributors demoConfig later.2).card = 0) &&
            resourcesConservedB later.2) = true := by
  native_decide

theorem early_collecting_rollover_is_refused :
    (match collectThree? with
    | none => false
    | some runtime =>
        let early : EpochId := ⟨runtime.2.epoch.value + 1⟩
        decide (rolloverWith runtime early = .error .earlyAdvance)) = true := by
  native_decide

/-- Internal hostile decoder model: even if private construction were bypassed by
a broken decoder, the sole public executor refuses the unconserved state. -/
private def forgedUnconservedState : State :=
  { genesisState demoConfig fixtureProvenance with totalSupplyReceived := 99 }

theorem forged_unconserved_state_refused :
    (match fixtureOpen? demoConfig with
    | none => false
    | some (store, _) =>
        let command := Command.claim epochTwelve alice
        decide (execute store store demoConfig forgedUnconservedState command
          (fixtureAuthority store demoConfig forgedUnconservedState command alice
            (.claim epochTwelve alice)) = .error .staleHead)) = true := by
  native_decide

def alternatePoolId : PoolId := { demoPoolId with deploymentDigest := digest 250 }

def alternateCandidate (id : Nat) : ArtifactRef :=
  { candidateArtifact id with contentDigest := digest 250 }

def alternateRawConfig : RawConfig := {
  demoRawConfig with
  poolId := alternatePoolId
  configDigest := digest 250
  allowedBeta := {alternateCandidate 1, alternateCandidate 2, alternateCandidate 3}
  recipes := [
    { broth with candidateArtifact := alternateCandidate 1 },
    { embercakes with candidateArtifact := alternateCandidate 2 },
    { lavishPlate with candidateArtifact := alternateCandidate 3 }
  ]
}

def alternateConfig : Config where
  raw := alternateRawConfig
  valid := by native_decide

theorem fresh_pool_cross_spend_refused :
    (match settleFixture? epochTwelve alice (digest 210) (fixtureCanon epochTwelve) with
    | none => false
    | some (credit, _) =>
        match fixtureOpen? alternateConfig with
        | none => false
        | some (store, state) =>
            let command := Command.contribute credit
            decide (execute store store alternateConfig state command
              (fixtureAuthority store alternateConfig state command alice (.contribute credit)) =
                .error .wrongPool)) = true := by
  native_decide

/-- A credit admitted by a different oracle session cannot be laundered through
a correctly authenticated command from this pool's admission session.  The
same settled receipt and command fields are retained; only opaque provenance
differs. -/
theorem cross_oracle_settled_credit_is_refused :
    (match settleFixture? epochTwelve alice (digest 210) (fixtureCanon epochTwelve),
        fixtureOpen? demoConfig with
    | some (credit, _), some (store, state) =>
        let foreignCredit : GalleyCredit :=
          { credit with admissionProvenance := alternateProvenance }
        let command := Command.contribute foreignCredit
        decide (execute store store demoConfig state command
          (fixtureAuthority store demoConfig state command alice (.contribute foreignCredit)) =
            .error .crossOracleProvenance)
    | _, _ => false) = true := by
  native_decide

/-- Threading the candidate successor provides the local half of one-shot
opening.  Durable single-winner status still comes from `PersistenceCASContract`. -/
theorem threaded_store_refuses_pool_reopen :
    (match openPool fixtureStore fixtureStore demoConfig
        (fixtureGenesisAuthority fixtureStore demoConfig) with
    | .error _ => false
    | .ok (storeAfterOpen, state) =>
        let oldAuthority := fixtureGenesisAuthority fixtureStore demoConfig
        decide (openPool storeAfterOpen fixtureStore demoConfig oldAuthority =
          .error .staleStore) &&
        decide (openPool storeAfterOpen storeAfterOpen demoConfig
          (fixtureGenesisAuthority storeAfterOpen demoConfig) = .error .alreadyOpened) &&
        decide (state.sequence = 0)) = true := by
  native_decide

/-- Honest limitation witness: copying the same old store and authority evaluates
to two successful opening candidates.  Pure Lean has not persisted either one. -/
theorem copied_old_store_recomputes_genesis_successfully :
    let authority := fixtureGenesisAuthority fixtureStore demoConfig
    (openPool fixtureStore fixtureStore demoConfig authority).isOk = true ∧
      (openPool fixtureStore fixtureStore demoConfig authority).isOk = true := by
  native_decide

theorem arbitrary_genesis_store_root_refused :
    let hostileRoot : StoreRoot := ⟨{ fixtureStore.snapshot with sequence := 99 }⟩
    let hostile : GenesisAuthority fixtureStore demoConfig := {
      admissionProvenance := fixtureProvenance
      canonicalStoreRoot := hostileRoot
      signedConfig := configTranscript demoConfig
      transcript := {
        storeRoot := hostileRoot
        config := configTranscript demoConfig
        admissionProvenance := fixtureProvenance
      }
      exactDigest := ⟨{
        storeRoot := hostileRoot
        config := configTranscript demoConfig
        admissionProvenance := fixtureProvenance
      }⟩
      wireTranscript := genesisAuthorityTranscript fixtureStore demoConfig
      digest := transcriptDigest (genesisAuthorityTranscript fixtureStore demoConfig)
    }
    openPool fixtureStore fixtureStore demoConfig hostile = .error .authenticationMismatch := by
  native_decide

theorem claim_for_another_player_refused :
    (match emberFinalized? with
    | none => false
    | some runtime =>
        let store := runtime.1
        let state := runtime.2
        let command := Command.claim state.epoch alice
        decide (execute store store demoConfig state command
          (fixtureAuthority store demoConfig state command dave (.claim state.epoch alice)) =
            .error .actorMismatch)) = true := by
  native_decide

theorem early_advance_cannot_burn_unclaimed_rations :
    (match emberFinalized? with
    | none => false
    | some runtime =>
        decide (advanceWith runtime ⟨13⟩ = .error .earlyAdvance) &&
        decide (openRations runtime.2 = 3)) = true := by
  native_decide

theorem returning_contributor_new_epoch_counter_zero_accepted :
    (match claimedByThree? with
    | none => false
    | some served =>
        match advanceWith served epochNineteen with
        | .error _ => false
        | .ok later =>
            match settleFixture? epochNineteen alice (digest 213) (fixtureCanon epochNineteen) with
            | none => false
            | some (credit, _) =>
                decide (credit.previousPlayerCounter = 0) &&
                decide (creditCounterFor later.2.creditCounters credit.counterKey = 0) &&
                (executeContribution later credit).isOk) = true := by
  native_decide

theorem credit_replay_refuses_under_fresh_exact_authority :
    (match settleFixture? epochTwelve alice (digest 210) (fixtureCanon epochTwelve) with
    | none => false
    | some (credit, _) =>
        match fixtureOpen? demoConfig with
        | none => false
        | some (store, state) =>
            let command := Command.contribute credit
            match execute store store demoConfig state command
                (fixtureAuthority store demoConfig state command alice (.contribute credit)) with
            | .error _ => false
            | .ok (afterStore, after) =>
                decide (execute afterStore afterStore demoConfig after command
                  (fixtureAuthority afterStore demoConfig after command alice (.contribute credit)) =
                    .error .creditReplay)) = true := by
  native_decide

/-- When a host threads its chosen successor, an attempt based on the prior
snapshot is stale.  This is not a proof that the first candidate won persistence. -/
theorem threaded_successor_refuses_old_credit_branch :
    (match settleFixture? epochTwelve alice (digest 210) (fixtureCanon epochTwelve),
        fixtureOpen? demoConfig with
    | some (credit, _), some (store, state) =>
        let command := Command.contribute credit
        let authority := fixtureAuthority store demoConfig state command alice (.contribute credit)
        match execute store store demoConfig state command authority with
        | .error _ => false
        | .ok (canonicalAfter, _) =>
            decide (execute canonicalAfter store demoConfig state command authority =
              .error .staleStore)
    | _, _ => false) = true := by
  native_decide

/-- After a caller threads one candidate successor, the sibling is locally stale.
The persistence contract, not this pure evaluation, decides which sibling won. -/
theorem threaded_successor_refuses_governance_sibling :
    (match collectThree? with
    | none => false
    | some (store, state) =>
        let leftCommand := Command.finalize state.epoch broth.id .openCommons 4
        let leftFinality := CommandFinality.finalize state.epoch broth.id .openCommons 4
          (fixtureFinality store demoConfig state state.epoch)
        let rightCommand := Command.finalize state.epoch embercakes.id .cohesionCrew 3
        let rightFinality := CommandFinality.finalize state.epoch embercakes.id .cohesionCrew 3
          (fixtureFinality store demoConfig state state.epoch)
        let leftAuthority := fixtureAuthority store demoConfig state leftCommand governance leftFinality
        let rightAuthority := fixtureAuthority store demoConfig state rightCommand governance rightFinality
        match execute store store demoConfig state leftCommand leftAuthority with
        | .error _ => false
        | .ok (canonicalAfter, _) =>
            decide (execute canonicalAfter store demoConfig state rightCommand rightAuthority =
              .error .staleStore)) = true := by
  native_decide

/-- Honest fork witness: both conflicting governance decisions succeed when
evaluated from copies of the same old store/head.  Their successor stores differ,
so `PersistenceCASContract.singleWinner` is the necessary external tooth. -/
theorem copied_old_head_admits_conflicting_governance_candidates :
    (match collectThree? with
    | none => false
    | some (store, state) =>
        let leftCommand := Command.finalize state.epoch broth.id .openCommons 4
        let leftFinality := CommandFinality.finalize state.epoch broth.id .openCommons 4
          (fixtureFinality store demoConfig state state.epoch)
        let rightCommand := Command.finalize state.epoch embercakes.id .cohesionCrew 3
        let rightFinality := CommandFinality.finalize state.epoch embercakes.id .cohesionCrew 3
          (fixtureFinality store demoConfig state state.epoch)
        let leftAuthority := fixtureAuthority store demoConfig state leftCommand governance leftFinality
        let rightAuthority := fixtureAuthority store demoConfig state rightCommand governance rightFinality
        match execute store store demoConfig state leftCommand leftAuthority,
            execute store store demoConfig state rightCommand rightAuthority with
        | .ok left, .ok right =>
            decide (left.1 ≠ right.1) && decide (left.2.lastMenu ≠ right.2.lastMenu)
        | _, _ => false) = true := by
  native_decide

def shadowBroth : Recipe := { broth with supplyPerRation := 1 }

def shadowRawConfig : RawConfig :=
  { demoRawConfig with recipes := [shadowBroth, embercakes, lavishPlate] }

def shadowConfig : Config where
  raw := shadowRawConfig
  valid := by native_decide

/-- Same caller-declared `configDigest`, different consumed recipe policy.  Exact
config identity and its wire projection both move, and the old pool head refuses
execution under the shadow config. -/
theorem shadow_recipe_same_declared_digest_refused :
    (match fixtureOpen? demoConfig with
    | none => false
    | some (store, state) =>
        let command := Command.claim state.epoch alice
        let authority := fixtureAuthority store shadowConfig state command alice
          (.claim state.epoch alice)
        decide (shadowConfig.raw.configDigest = demoConfig.raw.configDigest) &&
        decide (configTranscript shadowConfig ≠ configTranscript demoConfig) &&
        decide (exactConfigDigest shadowConfig ≠ exactConfigDigest demoConfig) &&
        decide (configWireDigest shadowConfig ≠ configWireDigest demoConfig) &&
        decide (execute store store shadowConfig state command authority = .error .wrongConfig)) =
      true := by
  native_decide

theorem finalized_certificate_constructor_is_private : True := by
  fail_if_success
    (have _constructor := FinalizedEpochCertificate.mk)
  trivial

theorem finalized_certificate_epoch_substitution_unavailable : True := by
  fail_if_success
    (have _wrong : FinalizedEpochCertificate demoConfig epochNineteen :=
      fixtureOpeningFinality epochTwelve)
  trivial

theorem finalized_command_binds_exact_typed_epoch :
    let certificate := fixtureOpeningFinality epochTwelve
    let evidence := CommandFinality.finalize epochTwelve broth.id .openCommons 1 certificate
    evidence.view = .finalized fixtureProvenance epochTwelve
      certificate.finalizedRoot certificate.digest := by
  native_decide

theorem authored_choices_are_distinct_and_scarcity_has_teeth :
    (match collectThree? with
    | none => false
    | some runtime =>
        match finalizeWith runtime broth .openCommons 4,
            finalizeWith runtime embercakes .cohesionCrew 3 with
        | .ok brothState, .ok emberState =>
            decide (brothState.2.lastMenu ≠ emberState.2.lastMenu) &&
            decide (brothState.2.reserveSupply ≠ emberState.2.reserveSupply) &&
            decide (finalizeWith runtime lavishPlate .openCommons 3 = .error .scarceSupply)
        | _, _ => false) = true := by
  native_decide

theorem one_ration_cap_and_allocation_teeth :
    (match emberFinalized? with
    | none => false
    | some runtime =>
        match claimForSelf runtime alice with
        | .error _ => false
        | .ok claimed =>
            decide (claimForSelf claimed alice = .error .alreadyClaimed) &&
            decide (claimForSelf runtime dave = .error .ineligibleForAllocation)) = true := by
  native_decide

theorem exact_conservation_and_candidate_only_output :
    claimedByThree?.map (fun runtime =>
      let state := runtime.2
      resourcesConservedB state && rationsConservedB state &&
      decide (state.reserveSupply = 3) && decide (state.reserveCohesion = 3) &&
      decide (state.totalSupplyReceived = 9) && decide (state.totalSupplyUsed = 9) &&
      decide (state.producedRations = 3) && decide (state.playerRationsClaimed = 3) &&
      decide (candidateArtifact 2 ∈ state.candidateArtifacts) &&
      decide (state.candidateArtifacts ⊆ demoConfig.raw.allowedBeta)) = some true := by
  native_decide

theorem skipped_epochs_have_no_missed_day_penalty :
    (match emberFinalized? with
    | none => false
    | some runtime =>
        match advanceWith runtime epochNineteen with
        | .error _ => false
        | .ok later =>
            decide (later.2.commonsRationsConsumed = 3) &&
            decide (later.2.producedRations = 3) &&
            rationsConservedB later.2 &&
            decide (later.2.reserveSupply = runtime.2.reserveSupply) &&
            decide (later.2.reserveCohesion = runtime.2.reserveCohesion)) = true := by
  native_decide

theorem command_digest_binds_recipe_allocation_servings_action_and_prestate :
    (match collectThree? with
    | none => false
    | some (store, state) =>
        let previous := actorCounterFor state.actorCounters governance
        let next := previous + 1
        let baseCommand := Command.finalize state.epoch embercakes.id .cohesionCrew 3
        let baseFinality := CommandFinality.finalize state.epoch embercakes.id .cohesionCrew 3
          (fixtureFinality store demoConfig state state.epoch)
        let recipeCommand := Command.finalize state.epoch broth.id .cohesionCrew 3
        let recipeFinality := CommandFinality.finalize state.epoch broth.id .cohesionCrew 3
          (fixtureFinality store demoConfig state state.epoch)
        let allocationCommand := Command.finalize state.epoch embercakes.id .openCommons 3
        let allocationFinality := CommandFinality.finalize state.epoch embercakes.id .openCommons 3
          (fixtureFinality store demoConfig state state.epoch)
        let servingsCommand := Command.finalize state.epoch embercakes.id .cohesionCrew 2
        let servingsFinality := CommandFinality.finalize state.epoch embercakes.id .cohesionCrew 2
          (fixtureFinality store demoConfig state state.epoch)
        let claimCommand := Command.claim state.epoch governance
        let base := commandDigest store demoConfig state baseCommand fixtureProvenance
          governance previous next baseFinality
        let recipeSwap := commandDigest store demoConfig state recipeCommand fixtureProvenance
          governance previous next
          recipeFinality
        let allocationSwap := commandDigest store demoConfig state allocationCommand fixtureProvenance governance
          previous next allocationFinality
        let servingsSwap := commandDigest store demoConfig state servingsCommand fixtureProvenance governance previous next
          servingsFinality
        let actionSwap := commandDigest store demoConfig state claimCommand fixtureProvenance governance previous next
          (.claim state.epoch governance)
        let hostilePrestate : State := { state with commitment := digest 249 }
        let prestateSwap := commandDigest store demoConfig hostilePrestate baseCommand fixtureProvenance governance
          previous next baseFinality
        decide (base ≠ recipeSwap) && decide (base ≠ allocationSwap) &&
        decide (base ≠ servingsSwap) && decide (base ≠ actionSwap) &&
        decide (base ≠ prestateSwap)) = true := by
  native_decide

#assert_axioms credit_exact_pool
#assert_axioms credit_exact_receipt_key
#assert_axioms credit_exact_counter_key
#assert_axioms credit_retains_settled_domain
#assert_axioms openPool_same_pool_refused
#assert_axioms AuthenticatedCommand.exact
#assert_axioms resourcesConservedB_iff
#assert_axioms rationsConservedB_iff
#assert_axioms openPool_resources_conserved
#assert_axioms openPool_rations_conserved
#assert_axioms applyCredit_preserves_resources
#assert_axioms finalizeBatch_preserves_resources
#assert_axioms claimRation_preserves_resources
#assert_axioms advanceEpoch_preserves_resources
#assert_axioms rolloverEpoch_preserves_resources
#assert_axioms rolloverEpoch_carries_settled_pool
#assert_axioms candidate_is_exact_authored_recipe
#assert_axioms advance_gap_economically_irrelevant
#assert_axioms sourceReward_accepted
#assert_axioms finalized_certificate_constructor_is_private
#assert_axioms finalized_certificate_epoch_substitution_unavailable
#assert_axioms PersistedTransition.same_successor
#assert_axioms PersistedTransition.deployment_scoped
#assert_axioms DurableStoreLoad.exact
#assert_axioms DurableStoreLoad.rooted_exact
#assert_axioms DeploymentRootCertificate.same_root
#assert_axioms DurableStoreLoad.revisionZero_same_genesis

#assert_compiled arbitrary_root_settlement_unavailable
#assert_compiled real_settlements_feed_exact_pool
#assert_compiled stale_consensus_finality_head_is_refused
#assert_compiled collecting_timeout_rolls_settled_pool_without_replay
#assert_compiled early_collecting_rollover_is_refused
#assert_compiled forged_unconserved_state_refused
#assert_compiled fresh_pool_cross_spend_refused
#assert_compiled cross_oracle_settled_credit_is_refused
#assert_compiled threaded_store_refuses_pool_reopen
#assert_compiled copied_old_store_recomputes_genesis_successfully
#assert_compiled claim_for_another_player_refused
#assert_compiled early_advance_cannot_burn_unclaimed_rations
#assert_compiled returning_contributor_new_epoch_counter_zero_accepted
#assert_compiled credit_replay_refuses_under_fresh_exact_authority
#assert_compiled threaded_successor_refuses_old_credit_branch
#assert_compiled threaded_successor_refuses_governance_sibling
#assert_compiled copied_old_head_admits_conflicting_governance_candidates
#assert_compiled shadow_recipe_same_declared_digest_refused
#assert_compiled arbitrary_genesis_store_root_refused
#assert_compiled finalized_command_binds_exact_typed_epoch
#assert_compiled authored_choices_are_distinct_and_scarcity_has_teeth
#assert_compiled one_ration_cap_and_allocation_teeth
#assert_compiled exact_conservation_and_candidate_only_output
#assert_compiled skipped_epochs_have_no_missed_day_penalty
#assert_compiled command_digest_binds_recipe_allocation_servings_action_and_prestate

end Dregg2.Games.PathOfAngels.GalleyCommons
