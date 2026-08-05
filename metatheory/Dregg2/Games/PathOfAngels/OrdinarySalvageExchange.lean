/-
# Path of Angels — ordinary expedition salvage exchange

This is the canonical custody seam for exchangeable expedition salvage.  A
market unit can be created only from an ordinary-part mint carried by a sealed
`CrewFieldMissionRuntime` result which was included in an accepted
`EventBatch`.  Story relics inhabit a different type and have no ingress.

The exchange is a barter of two exact serialized part units.  DREGG balances,
holder status, payouts, fees, and fungible token amounts do not occur in the
state or transition.  The Dark Bazaar is used only for its exact V1
same-opening book: a settlement receipt is indexed by the exact two-part claim
and an `OpeningAwareBookReceipt`, then swaps custody and nothing else.

As in `BazaarGame`, every command consumes only a receipt-backed durable load
and emits a persistence candidate.  A candidate cannot drive another command;
the node must first return an exact successful CAS receipt.
-/
import Dregg2.Games.PathOfAngels.ShipExpeditionSeason
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.OrdinarySalvageExchange

open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.BazaarGame
open Dregg2.Games.PathOfAngels.DarkBazaar
open Dregg2.Games.PathOfAngels.ShipExpeditionSeason

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-! ## Finalized ordinary mint provenance -/

/-- Exact identity of one non-fungible unit within a bounded ordinary mint. -/
structure UnitKey where
  runtimeReceipt : Digest32
  sourceBatch : Digest32
  part : CrewFieldMissionRuntime.PartId
  serial : Nat
deriving DecidableEq

/-- Proof-carrying selection of one ordinary unit from an exact finalized
runtime/EventBatch receipt.  The constructor is private. -/
structure MintAuthorization where
  private mk ::
  receipt : RuntimeEventBatchReceipt
  mint : CrewFieldMissionRuntime.OrdinaryMintAuthorization
  included : mint ∈ receipt.output.receipt.ordinaryMints
  marketExact : mint.marketEligible = true
  recipientExact : mint.recipient = receipt.owner
  positive : 0 < mint.quantity
  bounded : mint.quantity ≤ CrewFieldMissionRuntime.MAX_PART_QUANTITY
  serial : Nat
  serialLt : serial < mint.quantity

/-- Select a unit only from an ordinary mint already carried by the sealed
runtime/EventBatch receipt.  No digest-shaped substitute is accepted. -/
def MintAuthorization.ofFinalized
    (receipt : RuntimeEventBatchReceipt)
    (mint : CrewFieldMissionRuntime.OrdinaryMintAuthorization)
    (included : mint ∈ receipt.output.receipt.ordinaryMints)
    (marketExact : mint.marketEligible = true)
    (recipientExact : mint.recipient = receipt.owner)
    (positive : 0 < mint.quantity)
    (bounded : mint.quantity ≤ CrewFieldMissionRuntime.MAX_PART_QUANTITY)
    (serial : Nat) (serialLt : serial < mint.quantity) : MintAuthorization :=
  ⟨receipt, mint, included, marketExact, recipientExact, positive, bounded,
    serial, serialLt⟩

/-- The only market-bearing ordinary unit.  Its private constructor prevents a
raw `PartId` (and therefore a numerically similar relic id) from becoming
custody by itself. -/
structure MarketUnit where
  private mk ::
  key : UnitKey
  initialOwner : Digest32
deriving DecidableEq

def MintAuthorization.unit (authorization : MintAuthorization) : MarketUnit :=
  ⟨{
      runtimeReceipt := authorization.receipt.receiptId
      sourceBatch := authorization.receipt.sourceBatchDigest
      part := authorization.mint.part
      serial := authorization.serial
    }, authorization.mint.recipient⟩

theorem MintAuthorization.unit_owner_is_runtime_actor
    (authorization : MintAuthorization) :
    authorization.unit.initialOwner = authorization.receipt.owner :=
  authorization.recipientExact

/-- Story/canon relics have no ordinary-market producer. -/
def relicMarketIngress (_ : ContentContract.RelicId) : Option MarketUnit := none

theorem content_relic_market_ingress_absent (relic : ContentContract.RelicId) :
    relicMarketIngress relic = none := rfl

/-! ## Exact custody and two-part barter claim -/

structure CustodyEntry where
  key : UnitKey
  sourceBatch : Digest32
  owner : Digest32
deriving DecidableEq

def MarketUnit.entry (unit : MarketUnit) : CustodyEntry :=
  ⟨unit.key, unit.key.sourceBatch, unit.initialOwner⟩

structure Inventory where
  entries : List CustodyEntry
  keysNodup : (entries.map CustodyEntry.key).Nodup
deriving DecidableEq

def Inventory.ownerOf? (inventory : Inventory) (key : UnitKey) : Option Digest32 :=
  (inventory.entries.find? fun entry => entry.key = key).map CustodyEntry.owner

structure InitialCustodyAuthorization where
  private mk ::
  offered : MintAuthorization
  requested : MintAuthorization
  unitsDistinct : offered.unit.key ≠ requested.unit.key
  ownersDistinct : offered.unit.initialOwner ≠ requested.unit.initialOwner

def InitialCustodyAuthorization.ofFinalizedMints
    (offered requested : MintAuthorization)
    (unitsDistinct : offered.unit.key ≠ requested.unit.key)
    (ownersDistinct : offered.unit.initialOwner ≠ requested.unit.initialOwner) :
    InitialCustodyAuthorization :=
  ⟨offered, requested, unitsDistinct, ownersDistinct⟩

def Inventory.ofAuthorization
    (authorization : InitialCustodyAuthorization) : Inventory where
  entries := [authorization.offered.unit.entry,
    authorization.requested.unit.entry]
  keysNodup := by
    simp [MarketUnit.entry, authorization.unitsDistinct]

theorem Inventory.ofAuthorization_offered_owner
    (authorization : InitialCustodyAuthorization) :
    (Inventory.ofAuthorization authorization).ownerOf?
      authorization.offered.unit.key =
        some authorization.offered.unit.initialOwner := by
  simp [Inventory.ownerOf?, Inventory.ofAuthorization, MarketUnit.entry]

theorem Inventory.ofAuthorization_requested_owner
    (authorization : InitialCustodyAuthorization) :
    (Inventory.ofAuthorization authorization).ownerOf?
      authorization.requested.unit.key =
        some authorization.requested.unit.initialOwner := by
  simp [Inventory.ownerOf?, Inventory.ofAuthorization, MarketUnit.entry,
    authorization.unitsDistinct]

structure ExchangeClaim where
  exchangeId : Digest32
  seller : Digest32
  buyer : Digest32
  offered : UnitKey
  requested : UnitKey
deriving DecidableEq

/-- Exact durable custody proof for opening one barter. -/
structure CustodyAuthorization (inventory : Inventory)
    (claim : ExchangeClaim) where
  private mk ::
  sellerOwns : inventory.ownerOf? claim.offered = some claim.seller
  buyerOwns : inventory.ownerOf? claim.requested = some claim.buyer
  unitsDistinct : claim.offered ≠ claim.requested
  partiesDistinct : claim.seller ≠ claim.buyer

def CustodyAuthorization.ofExact (inventory : Inventory)
    (claim : ExchangeClaim)
    (sellerOwns : inventory.ownerOf? claim.offered = some claim.seller)
    (buyerOwns : inventory.ownerOf? claim.requested = some claim.buyer)
    (unitsDistinct : claim.offered ≠ claim.requested)
    (partiesDistinct : claim.seller ≠ claim.buyer) :
    CustodyAuthorization inventory claim :=
  ⟨sellerOwns, buyerOwns, unitsDistinct, partiesDistinct⟩

def InitialCustodyAuthorization.exchangeClaim
    (authorization : InitialCustodyAuthorization)
    (exchangeId : Digest32) : ExchangeClaim where
  exchangeId
  seller := authorization.offered.unit.initialOwner
  buyer := authorization.requested.unit.initialOwner
  offered := authorization.offered.unit.key
  requested := authorization.requested.unit.key

def InitialCustodyAuthorization.custody
    (authorization : InitialCustodyAuthorization)
    (exchangeId : Digest32) :
    CustodyAuthorization (Inventory.ofAuthorization authorization)
      (authorization.exchangeClaim exchangeId) :=
  CustodyAuthorization.ofExact _ _
    (Inventory.ofAuthorization_offered_owner authorization)
    (Inventory.ofAuthorization_requested_owner authorization)
    authorization.unitsDistinct authorization.ownersDistinct

private def CustodyEntry.swapped (claim : ExchangeClaim)
    (entry : CustodyEntry) : CustodyEntry :=
  if entry.key = claim.offered then { entry with owner := claim.buyer }
  else if entry.key = claim.requested then { entry with owner := claim.seller }
  else entry

private theorem CustodyEntry.swapped_key (claim : ExchangeClaim)
    (entry : CustodyEntry) : (entry.swapped claim).key = entry.key := by
  unfold CustodyEntry.swapped
  split <;> try rfl
  split <;> rfl

private theorem CustodyEntry.swapped_sourceBatch (claim : ExchangeClaim)
    (entry : CustodyEntry) :
    (entry.swapped claim).sourceBatch = entry.sourceBatch := by
  unfold CustodyEntry.swapped
  split <;> try rfl
  split <;> rfl

def Inventory.swap (inventory : Inventory) (claim : ExchangeClaim) : Inventory where
  entries := inventory.entries.map (CustodyEntry.swapped claim)
  keysNodup := by
    simpa [List.map_map, Function.comp_def, CustodyEntry.swapped_key] using
      inventory.keysNodup

theorem InitialCustodyAuthorization.swap_owners
    (authorization : InitialCustodyAuthorization) (exchangeId : Digest32) :
    let claim := authorization.exchangeClaim exchangeId
    let swapped := (Inventory.ofAuthorization authorization).swap claim
    swapped.ownerOf? claim.offered = some claim.buyer ∧
      swapped.ownerOf? claim.requested = some claim.seller := by
  have requestedNe :
      authorization.requested.unit.key ≠ authorization.offered.unit.key :=
    Ne.symm authorization.unitsDistinct
  simp [InitialCustodyAuthorization.exchangeClaim, Inventory.swap,
    Inventory.ofAuthorization, Inventory.ownerOf?, CustodyEntry.swapped,
    MarketUnit.entry, authorization.unitsDistinct, requestedNe]

/-! ## Exact DrEX same-opening receipt, without a token leg -/

structure PartOpeningStatement where
  exchange : ExchangeClaim
  book : BookBindingKey
deriving DecidableEq

/-- Runtime output of the combined ordinary-part intent / V1 same-opening
verifier.  There is no producer in Lean. -/
structure UpstreamPartOpeningAuthorization (statement : PartOpeningStatement) where
  private mk ::
  private authenticated : True

structure OpeningReceipt where
  private mk ::
  claim : ExchangeClaim
  book : OpeningAwareBookReceipt
  authorization : UpstreamPartOpeningAuthorization ⟨claim, book.bindingKey⟩
  sellerExact : book.claim.spec.seller.value = claim.seller
  buyerExact : book.claim.spec.buyer.value = claim.buyer
  oneForOne : book.claim.output.volume = 1

def OpeningReceipt.ofUpstream (claim : ExchangeClaim)
    (book : OpeningAwareBookReceipt)
    (authorization : UpstreamPartOpeningAuthorization ⟨claim, book.bindingKey⟩)
    (sellerExact : book.claim.spec.seller.value = claim.seller)
    (buyerExact : book.claim.spec.buyer.value = claim.buyer)
    (oneForOne : book.claim.output.volume = 1) : OpeningReceipt :=
  ⟨claim, book, authorization, sellerExact, buyerExact, oneForOne⟩

theorem OpeningReceipt.has_exact_v1_same_opening_book (receipt : OpeningReceipt) :
    receipt.book.transcript.card = 4 :=
  receipt.book.transcript_card

/-! ## Persisted custody state and exact CAS -/

inductive CompletionKind where
  | cancelled
  | exchanged
deriving DecidableEq, Repr

structure ExchangeReceipt where
  private mk ::
  claim : ExchangeClaim
  offeredSourceBatch : Digest32
  requestedSourceBatch : Digest32
  opening : BookBindingKey
deriving DecidableEq

structure Completion where
  exchangeId : Digest32
  kind : CompletionKind
deriving DecidableEq

structure StateKey where
  authority : Digest32
  revision : PlayerCounter
  inventory : Inventory
  current : Option ExchangeClaim
  completions : List Completion
  receipts : List ExchangeReceipt
  consumedMints : Finset UnitKey
  consumedExchanges : Finset Digest32
deriving DecidableEq

structure State where
  private mk ::
  authority : Digest32
  revision : PlayerCounter
  inventory : Inventory
  current : Option ExchangeClaim
  completions : List Completion
  receipts : List ExchangeReceipt
  consumedMints : Finset UnitKey
  consumedExchanges : Finset Digest32

def State.key (state : State) : StateKey :=
  ⟨state.authority, state.revision, state.inventory, state.current,
    state.completions, state.receipts, state.consumedMints,
    state.consumedExchanges⟩

structure RegistryGenesis {authorityId : Digest32}
    (_authority : DeploymentAuthority authorityId) where
  private mk ::
  private authenticated : True

structure Registry where
  private mk ::
  authority : Digest32
  revision : PlayerCounter
  head : Option StateKey

private def zeroCounter : PlayerCounter := ⟨0, by decide⟩

def Registry.open {authorityId : Digest32}
    {authority : DeploymentAuthority authorityId}
    (_genesis : RegistryGenesis authority) : Registry :=
  ⟨authorityId, zeroCounter, none⟩

structure RuntimeCasRequest where
  expected : Option StateKey
  replacement : StateKey
deriving DecidableEq

inductive Refusal where
  | registryAuthorityMismatch
  | registryAlreadyInitialized
  | wrongAuthority
  | revisionExhausted
  | staleCanonicalHead
  | exchangeAlreadyOpen
  | noOpenExchange
  | exchangeReplay
  | openingMismatch
deriving DecidableEq, Repr

def runtimeCas (persisted : Option StateKey) (request : RuntimeCasRequest) :
    Except Refusal (Option StateKey) :=
  if persisted ≠ request.expected then .error .staleCanonicalHead
  else .ok (some request.replacement)

structure PersistenceCandidate where
  private mk ::
  private predecessor : Option StateKey
  private registry : Registry
  private state : State
  private headExact : registry.head = some state.key
  private revisionExact : registry.revision = state.revision

def PersistenceCandidate.request (candidate : PersistenceCandidate) :
    RuntimeCasRequest :=
  ⟨candidate.predecessor, candidate.state.key⟩

structure SuccessfulPersistence (request : RuntimeCasRequest) where
  private mk ::
  observedBefore : Option StateKey
  observedAfter : Option StateKey
  expectedExact : observedBefore = request.expected
  appliedExact : runtimeCas observedBefore request = .ok observedAfter
  replacementExact : observedAfter = some request.replacement

structure UpstreamDurableLoad (registry : Registry) (state : State) where
  private mk ::
  headExact : registry.head = some state.key
  revisionExact : registry.revision = state.revision

structure DurableDeployment where
  private mk ::
  private registry : Registry
  private state : State
  private headExact : registry.head = some state.key
  private revisionExact : registry.revision = state.revision

def DurableDeployment.ofUpstream {registry : Registry} {state : State}
    (load : UpstreamDurableLoad registry state) : DurableDeployment :=
  ⟨registry, state, load.headExact, load.revisionExact⟩

def PersistenceCandidate.continue (candidate : PersistenceCandidate)
    (_receipt : SuccessfulPersistence candidate.request) : DurableDeployment :=
  ⟨candidate.registry, candidate.state, candidate.headExact,
    candidate.revisionExact⟩

def DurableDeployment.key (live : DurableDeployment) : StateKey := live.state.key

def DurableDeployment.pending (live : DurableDeployment) : Option ExchangeClaim :=
  live.state.current

def DurableDeployment.latestReceipt (live : DurableDeployment) :
    Option ExchangeReceipt := live.state.receipts.head?

theorem PersistenceCandidate.continuation_replacement_exact
    (candidate : PersistenceCandidate)
    (receipt : SuccessfulPersistence candidate.request) :
    (candidate.continue receipt).key = candidate.request.replacement := by
  rfl

theorem runtimeCas_same_old_fork_has_one_winner
    (old firstNext secondNext : StateKey) (changed : firstNext ≠ old) :
    let first : RuntimeCasRequest := ⟨some old, firstNext⟩
    let second : RuntimeCasRequest := ⟨some old, secondNext⟩
    runtimeCas (some old) first = .ok (some firstNext) ∧
      runtimeCas (some firstNext) second = .error .staleCanonicalHead := by
  simp [runtimeCas, changed]

theorem runtimeCas_at_exact_expected (request : RuntimeCasRequest) :
    runtimeCas request.expected request = .ok (some request.replacement) := by
  simp [runtimeCas]

def Registry.initialize {authorityId : Digest32}
    (_authority : DeploymentAuthority authorityId) (registry : Registry)
    (authorization : InitialCustodyAuthorization) :
    Except Refusal PersistenceCandidate :=
  if registry.authority ≠ authorityId then .error .registryAuthorityMismatch
  else if registry.head.isSome then .error .registryAlreadyInitialized
  else match registry.revision.next with
    | none => .error .revisionExhausted
    | some revision =>
        let inventory := Inventory.ofAuthorization authorization
        let state : State := {
          authority := authorityId
          revision
          inventory
          current := none
          completions := []
          receipts := []
          consumedMints := {authorization.offered.unit.key,
            authorization.requested.unit.key}
          consumedExchanges := ∅
        }
        let nextRegistry : Registry := ⟨authorityId, revision, some state.key⟩
        .ok ⟨none, nextRegistry, state, rfl, rfl⟩

private def preparePersistence (live : DurableDeployment)
    (proposed : State) : Except Refusal PersistenceCandidate :=
  match live.state.revision.next with
  | none => .error .revisionExhausted
  | some revision =>
      let state := { proposed with revision }
      let registry : Registry := ⟨live.state.authority, revision, some state.key⟩
      .ok ⟨some live.state.key, registry, state, rfl, rfl⟩

/-- Open a barter only from exact custody in the durable predecessor. -/
def openExchange (live : DurableDeployment)
    {authorityId : Digest32} (_authority : DeploymentAuthority authorityId)
    (claim : ExchangeClaim)
    (_custody : CustodyAuthorization live.key.inventory claim) :
    Except Refusal PersistenceCandidate :=
  if authorityId ≠ live.state.authority then .error .wrongAuthority
  else if claim.exchangeId ∈ live.state.consumedExchanges then .error .exchangeReplay
  else if live.state.current.isSome then .error .exchangeAlreadyOpen
  else preparePersistence live { live.state with current := some claim }

/-- Cancel consumes the exchange identity but moves no custody. -/
def cancelExchange (live : DurableDeployment)
    {authorityId : Digest32} (_authority : DeploymentAuthority authorityId) :
    Except Refusal PersistenceCandidate :=
  if authorityId ≠ live.state.authority then .error .wrongAuthority
  else match live.state.current with
    | none => .error .noOpenExchange
    | some claim => preparePersistence live {
        live.state with
        current := none
        completions := ⟨claim.exchangeId, .cancelled⟩ :: live.state.completions
        consumedExchanges := insert claim.exchangeId live.state.consumedExchanges
      }

/-- Exact DrEX opening swaps precisely two already-custodied ordinary units.
There is no payout or holder-weight input to this transition. -/
def settleExchange (live : DurableDeployment)
    {authorityId : Digest32} (_authority : DeploymentAuthority authorityId)
    (opening : OpeningReceipt) : Except Refusal PersistenceCandidate :=
  if authorityId ≠ live.state.authority then .error .wrongAuthority
  else if opening.claim.exchangeId ∈ live.state.consumedExchanges then
    .error .exchangeReplay
  else match live.state.current with
    | none => .error .noOpenExchange
    | some claim =>
        if claim ≠ opening.claim then .error .openingMismatch
        else
          let exchangeReceipt : ExchangeReceipt := {
            claim
            offeredSourceBatch := claim.offered.sourceBatch
            requestedSourceBatch := claim.requested.sourceBatch
            opening := opening.book.bindingKey
          }
          preparePersistence live {
            live.state with
            inventory := live.state.inventory.swap claim
            current := none
            completions := ⟨claim.exchangeId, .exchanged⟩ ::
              live.state.completions
            receipts := exchangeReceipt :: live.state.receipts
            consumedExchanges := insert claim.exchangeId
              live.state.consumedExchanges
          }

theorem settleExchange_exact_pending_accepts (live : DurableDeployment)
    {authorityId : Digest32} (authority : DeploymentAuthority authorityId)
    (opening : OpeningReceipt)
    (authorityExact : authorityId = live.key.authority)
    (pendingExact : live.pending = some opening.claim)
    (fresh : opening.claim.exchangeId ∉ live.key.consumedExchanges)
    (revisionAvailable : live.key.revision.next.isSome = true) :
    ∃ candidate, settleExchange live authority opening = .ok candidate := by
  unfold settleExchange
  have authorityExact' : authorityId = live.state.authority := by
    simpa [DurableDeployment.key, State.key] using authorityExact
  have fresh' : opening.claim.exchangeId ∉ live.state.consumedExchanges := by
    simpa [DurableDeployment.key, State.key] using fresh
  have pendingExact' : live.state.current = some opening.claim := by
    simpa [DurableDeployment.pending] using pendingExact
  simp only [authorityExact', ne_eq, if_false, fresh']
  rw [pendingExact']
  simp
  unfold preparePersistence
  have revisionAvailable' : live.state.revision.next.isSome = true := by
    simpa [DurableDeployment.key, State.key] using revisionAvailable
  cases hnext : live.state.revision.next with
  | none => simp [hnext] at revisionAvailable'
  | some revision => simp

theorem settleExchange_replay_refused (live : DurableDeployment)
    {authorityId : Digest32} (authority : DeploymentAuthority authorityId)
    (opening : OpeningReceipt)
    (authorityExact : authorityId = live.key.authority)
    (consumed : opening.claim.exchangeId ∈ live.key.consumedExchanges) :
    settleExchange live authority opening = .error .exchangeReplay := by
  unfold settleExchange
  have authorityExact' : authorityId = live.state.authority := by
    simpa [DurableDeployment.key, State.key] using authorityExact
  have consumed' : opening.claim.exchangeId ∈ live.state.consumedExchanges := by
    simpa [DurableDeployment.key, State.key] using consumed
  simp [authorityExact', consumed']

theorem settleExchange_wrong_opening_refused (live : DurableDeployment)
    {authorityId : Digest32} (authority : DeploymentAuthority authorityId)
    (opening : OpeningReceipt) (pending : ExchangeClaim)
    (authorityExact : authorityId = live.key.authority)
    (fresh : opening.claim.exchangeId ∉ live.key.consumedExchanges)
    (pendingExact : live.pending = some pending)
    (wrong : pending ≠ opening.claim) :
    settleExchange live authority opening = .error .openingMismatch := by
  unfold settleExchange
  have authorityExact' : authorityId = live.state.authority := by
    simpa [DurableDeployment.key, State.key] using authorityExact
  have fresh' : opening.claim.exchangeId ∉ live.state.consumedExchanges := by
    simpa [DurableDeployment.key, State.key] using fresh
  have pendingExact' : live.state.current = some pending := by
    simpa [DurableDeployment.pending] using pendingExact
  simp [authorityExact', fresh', pendingExact', wrong]

/-! ## Generic semantic teeth -/

theorem settlement_preserves_unit_identity_and_batch_provenance
    (inventory : Inventory) (claim : ExchangeClaim) :
    (inventory.swap claim).entries.map (fun entry => (entry.key, entry.sourceBatch)) =
      inventory.entries.map (fun entry => (entry.key, entry.sourceBatch)) := by
  simp [Inventory.swap, List.map_map, CustodyEntry.swapped_key,
    CustodyEntry.swapped_sourceBatch]

theorem settlement_has_no_token_or_payout_transition
    (inventory : Inventory) (claim : ExchangeClaim) :
    (inventory.swap claim).entries.length = inventory.entries.length := by
  simp [Inventory.swap]

#assert_axioms MintAuthorization.unit_owner_is_runtime_actor
#assert_axioms content_relic_market_ingress_absent
#assert_axioms Inventory.ofAuthorization_offered_owner
#assert_axioms Inventory.ofAuthorization_requested_owner
#assert_axioms InitialCustodyAuthorization.swap_owners
#assert_axioms OpeningReceipt.has_exact_v1_same_opening_book
#assert_axioms PersistenceCandidate.continuation_replacement_exact
#assert_axioms runtimeCas_same_old_fork_has_one_winner
#assert_axioms runtimeCas_at_exact_expected
#assert_axioms settleExchange_exact_pending_accepts
#assert_axioms settleExchange_replay_refused
#assert_axioms settleExchange_wrong_opening_refused
#assert_axioms settlement_preserves_unit_identity_and_batch_provenance
#assert_axioms settlement_has_no_token_or_payout_transition

end Dregg2.Games.PathOfAngels.OrdinarySalvageExchange
