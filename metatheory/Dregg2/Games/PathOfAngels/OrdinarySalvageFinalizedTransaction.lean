/-
# Path of Angels — finalized ordinary-salvage transaction

This module closes one deliberately narrow join which the source-only ordinary
salvage exchange leaves abstract.  One transaction consumes an authenticated
load of the deployment's single canonical custody/mint-nullifier head, two
exact unit sources, one exact operator-visible V1 opening authorization, and an
opaque admission for the finalized Dregg carrier.  It emits a custody successor
and one two-event `EventBatch` envelope for custody plus the rebuildable market
projection.

The absences are part of the contract:

* `UpstreamCanonicalLoad` has no Lean producer.  Native storage must attest the
  one deployment-global head; a caller-authored state is not authority.
* `UpstreamFinalizedCarrier` has no Lean producer.  Native finality must weld the
  coordinate to the real `CommitRecord`.
* `UpstreamOpeningAwareAuthorization` has no Lean producer.  Its eventual
  verifier must bind the complete statement, including both serialized
  `UnitKey`s, actors, exchange identity, and exact V1 book binding.
* the privacy grade is `operatorVisibleOpeningAwareJudge`.  The source verifier
  and judge may see the order/opening.  Nothing here claims house blindness.
* `AtomicCommitIntent` is an all-or-none persistence demand, not a claim that a
  host already performed it.  The state replacement and EventBatch must be
  committed by one outer writer before the successor can receive a new
  `UpstreamCanonicalLoad`.

The custody key set is also the deployment-global mint-nullifier set.  A
finalized mint can enter it once; an existing unit can be traded repeatedly,
but only from its current canonical owner.  Story relics use a disjoint type and
have no producer into either source form.
-/
import Dregg2.Games.PathOfAngels.OrdinarySalvageExchange
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.OrdinarySalvageFinalizedTransaction

open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.BazaarGame
open Dregg2.Games.PathOfAngels.EventSourcing
open Dregg2.Games.PathOfAngels.OrdinarySalvageExchange

set_option autoImplicit false

/-! ## Pinned deployment and honestly named privacy -/

inductive PrivacyGrade where
  | operatorVisibleOpeningAwareJudge
deriving DecidableEq, Repr

structure RawConfig where
  authority : Digest32
  world : EventBatch.WorldIdentity
  custodyStream : EventBatch.StreamId
  projectionStream : EventBatch.StreamId
deriving DecidableEq

structure Config where
  private mk ::
  raw : RawConfig
  worldValid : raw.world.validB = true
  custodyValid : raw.custodyStream.validB = true
  projectionValid : raw.projectionStream.validB = true
  custodyWorldExact : raw.custodyStream.world = raw.world
  projectionWorldExact : raw.projectionStream.world = raw.world
  streamsDistinct : raw.custodyStream ≠ raw.projectionStream

def activate? (raw : RawConfig) : Option Config :=
  if hworld : raw.world.validB = true then
    if hcustody : raw.custodyStream.validB = true then
      if hprojection : raw.projectionStream.validB = true then
        if hcustodyWorld : raw.custodyStream.world = raw.world then
          if hprojectionWorld : raw.projectionStream.world = raw.world then
            if hdistinct : raw.custodyStream ≠ raw.projectionStream then
              some ⟨raw, hworld, hcustody, hprojection, hcustodyWorld,
                hprojectionWorld, hdistinct⟩
            else none
          else none
        else none
      else none
    else none
  else none

theorem Config.streams_are_distinct (config : Config) :
    config.raw.custodyStream ≠ config.raw.projectionStream := by
  exact config.streamsDistinct

/-! ## One deployment-global custody and mint-nullifier head -/

structure CanonicalCustody where
  private mk ::
  /-- Membership means both "mint consumed" and "unit currently exists". -/
  mintNullifiers : Finset UnitKey
  private owner : UnitKey → Digest32

def CanonicalCustody.empty (absentOwner : Digest32) : CanonicalCustody :=
  ⟨∅, fun _ => absentOwner⟩

def CanonicalCustody.ownerOf? (custody : CanonicalCustody) (key : UnitKey) :
    Option Digest32 :=
  if key ∈ custody.mintNullifiers then some (custody.owner key) else none

private def CanonicalCustody.afterExchange (before : CanonicalCustody)
    (claim : ExchangeClaim) : CanonicalCustody :=
  ⟨insert claim.offered (insert claim.requested before.mintNullifiers),
    fun key =>
      if key = claim.offered then claim.buyer
      else if key = claim.requested then claim.seller
      else before.owner key⟩

theorem CanonicalCustody.afterExchange_offered_owner
    (before : CanonicalCustody) (claim : ExchangeClaim) :
    (before.afterExchange claim).ownerOf? claim.offered = some claim.buyer := by
  simp [CanonicalCustody.afterExchange, CanonicalCustody.ownerOf?]

theorem CanonicalCustody.afterExchange_requested_owner
    (before : CanonicalCustody) (claim : ExchangeClaim)
    (distinct : claim.offered ≠ claim.requested) :
    (before.afterExchange claim).ownerOf? claim.requested = some claim.seller := by
  simp [CanonicalCustody.afterExchange, CanonicalCustody.ownerOf?, Ne.symm distinct]

structure State where
  private mk ::
  authority : Digest32
  world : EventBatch.WorldIdentity
  revision : Nat
  custody : CanonicalCustody
  consumedExchanges : Finset Digest32
  consumedBooks : Finset BookBindingKey

structure UpstreamGenesis (config : Config) where
  private mk ::
  private authenticated : True

def State.genesis (config : Config) (_genesis : UpstreamGenesis config) : State :=
  ⟨config.raw.authority, config.raw.world, 0,
    CanonicalCustody.empty config.raw.authority, ∅, ∅⟩

/-- Opaque native evidence that `state` is the sole current deployment head. -/
structure UpstreamCanonicalLoad (config : Config) (state : State) where
  private mk ::
  authorityExact : state.authority = config.raw.authority
  worldExact : state.world = config.raw.world
  private authenticated : True

/-- Opaque native evidence that this coordinate is the real finalized carrier. -/
structure UpstreamFinalizedCarrier (config : Config)
    (coordinate : EventBatch.FinalizedTurnCoordinate) where
  private mk ::
  worldExact : coordinate.world = config.raw.world
  private authenticated : True

/-! ## Exact part/book statement -/

structure PartClearingStatement where
  exchange : ExchangeClaim
  book : BookBindingKey
  privacy : PrivacyGrade
deriving DecidableEq

def PartClearingStatement.openingAware (exchange : ExchangeClaim)
    (book : BookBindingKey) : PartClearingStatement :=
  ⟨exchange, book, .operatorVisibleOpeningAwareJudge⟩

/-- Result of the missing combined UnitKey/V1 opening verifier.  Its exact
dependent index is the authority: there is intentionally no Lean producer. -/
structure UpstreamOpeningAwareAuthorization (statement : PartClearingStatement) where
  private mk ::
  private authenticated : True

structure PartClearingReceipt where
  private mk ::
  exchange : ExchangeClaim
  book : OpeningAwareBookReceipt
  authorization : UpstreamOpeningAwareAuthorization
    (PartClearingStatement.openingAware exchange book.bindingKey)
  sellerExact : book.claim.spec.seller.value = exchange.seller
  buyerExact : book.claim.spec.buyer.value = exchange.buyer
  oneForOne : book.claim.output.volume = 1
  partiesDistinct : exchange.seller ≠ exchange.buyer
  unitsDistinct : exchange.offered ≠ exchange.requested

def PartClearingReceipt.ofUpstream (exchange : ExchangeClaim)
    (book : OpeningAwareBookReceipt)
    (authorization : UpstreamOpeningAwareAuthorization
      (PartClearingStatement.openingAware exchange book.bindingKey))
    (sellerExact : book.claim.spec.seller.value = exchange.seller)
    (buyerExact : book.claim.spec.buyer.value = exchange.buyer)
    (oneForOne : book.claim.output.volume = 1)
    (partiesDistinct : exchange.seller ≠ exchange.buyer)
    (unitsDistinct : exchange.offered ≠ exchange.requested) : PartClearingReceipt :=
  ⟨exchange, book, authorization, sellerExact, buyerExact, oneForOne,
    partiesDistinct, unitsDistinct⟩

def PartClearingReceipt.statement (receipt : PartClearingReceipt) :
    PartClearingStatement :=
  PartClearingStatement.openingAware receipt.exchange receipt.book.bindingKey

theorem PartClearingReceipt.privacy_is_operator_visible
    (receipt : PartClearingReceipt) :
    receipt.statement.privacy = .operatorVisibleOpeningAwareJudge := rfl

/-! ## Finalized mint or current-custody source -/

inductive UnitSource where
  | finalized (mint : MintAuthorization)
  | existing (key : UnitKey)

def UnitSource.key : UnitSource → UnitKey
  | .finalized mint => mint.unit.key
  | .existing key => key

def UnitSource.AuthorizedBy (source : UnitSource) (custody : CanonicalCustody)
    (expectedOwner : Digest32) : Prop :=
  match source with
  | .finalized mint =>
      mint.unit.key ∉ custody.mintNullifiers ∧ mint.unit.initialOwner = expectedOwner
  | .existing key => custody.ownerOf? key = some expectedOwner

instance (source : UnitSource) (custody : CanonicalCustody) (owner : Digest32) :
    Decidable (source.AuthorizedBy custody owner) := by
  unfold UnitSource.AuthorizedBy
  split <;> infer_instance

/-- Relics have neither a finalized-mint nor existing-PartId ingress. -/
def relicMarketIngress (_ : ContentContract.RelicId) : Option UnitSource := none

theorem content_relic_has_no_transaction_source (relic : ContentContract.RelicId) :
    relicMarketIngress relic = none := rfl

theorem finalized_mint_already_consumed_is_not_authorized
    (custody : CanonicalCustody) (mint : MintAuthorization) (owner : Digest32)
    (replay : mint.unit.key ∈ custody.mintNullifiers) :
    ¬ (UnitSource.finalized mint).AuthorizedBy custody owner := by
  simp [UnitSource.AuthorizedBy, replay]

theorem existing_unit_authorization_is_exact_current_owner
    (custody : CanonicalCustody) (key : UnitKey) (owner : Digest32) :
    (UnitSource.existing key).AuthorizedBy custody owner ↔
      custody.ownerOf? key = some owner := by
  rfl

structure Command where
  offered : UnitSource
  requested : UnitSource
  clearing : PartClearingReceipt

/-! ## Exact receipt, projection, and two-event intent -/

structure SettlementReceipt where
  exchange : ExchangeClaim
  book : BookBindingKey
  privacy : PrivacyGrade
  finalizedCoordinate : EventBatch.FinalizedTurnCoordinate
  offeredSourceBatch : Digest32
  requestedSourceBatch : Digest32
  beforeStateDigest : Digest32
  afterStateDigest : Digest32
deriving DecidableEq

structure MarketProjection where
  exchangeId : Digest32
  seller : Digest32
  buyer : Digest32
  offered : UnitKey
  requested : UnitKey
  book : BookBindingKey
  privacy : PrivacyGrade
  beforeStateDigest : Digest32
  afterStateDigest : Digest32
deriving DecidableEq

inductive TransactionEvent where
  | custodyTransferred (receipt : SettlementReceipt)
  | marketProjected (projection : MarketProjection)
deriving DecidableEq

structure Boundary where
  stateDigest : State → Digest32
  payloadDigest : TransactionEvent → Digest32
  eventBatch : EventBatch.DigestBoundary

structure AtomicCommitIntent where
  expectedStateDigest : Digest32
  replacementStateDigest : Digest32
  envelope : EventBatch.Envelope
deriving DecidableEq

structure CompleteEventBatchEvidence (boundary : Boundary)
    (initialHeads : List EventBatch.StreamHead) where
  private mk ::
  custodyPayload : TransactionEvent
  projectionPayload : TransactionEvent
  custodyEvent : EventBatch.IndexedEvent
  projectionEvent : EventBatch.IndexedEvent
  envelope : EventBatch.Envelope
  applied : EventBatch.AppliedBatch
  custodyPayloadExact : custodyEvent.statement.payloadDigest =
    boundary.payloadDigest custodyPayload
  projectionPayloadExact : projectionEvent.statement.payloadDigest =
    boundary.payloadDigest projectionPayload
  orderedExact : envelope.statement.events = [custodyEvent, projectionEvent]
  accepted : EventBatch.applyBatch boundary.eventBatch initialHeads envelope = .ok applied

structure Output (boundary : Boundary) (initialHeads : List EventBatch.StreamHead) where
  private mk ::
  successor : State
  receipt : SettlementReceipt
  projection : MarketProjection
  commit : AtomicCommitIntent
  events : CompleteEventBatchEvidence boundary initialHeads
  offeredOwnerExact : successor.custody.ownerOf? receipt.exchange.offered =
    some receipt.exchange.buyer
  requestedOwnerExact : successor.custody.ownerOf? receipt.exchange.requested =
    some receipt.exchange.seller
  offeredMintConsumed : receipt.exchange.offered ∈ successor.custody.mintNullifiers
  requestedMintConsumed : receipt.exchange.requested ∈ successor.custody.mintNullifiers
  exchangeConsumed : receipt.exchange.exchangeId ∈ successor.consumedExchanges
  bookConsumed : receipt.book ∈ successor.consumedBooks
  privacyExact : receipt.privacy = .operatorVisibleOpeningAwareJudge
  commitExpectedExact : commit.expectedStateDigest = receipt.beforeStateDigest
  commitReplacementExact : commit.replacementStateDigest = receipt.afterStateDigest
  commitEnvelopeExact : commit.envelope = events.envelope

inductive Refusal where
  | revisionExhausted
  | exchangeReplay
  | bookReplay
  | sameParty
  | sameUnit
  | offeredKeyMismatch
  | requestedKeyMismatch
  | offeredSourceRejected
  | requestedSourceRejected
  | missingCustodyHead
  | missingProjectionHead
  | eventBatch (error : EventBatch.Error)
deriving DecidableEq, Repr

/-- Cheap deterministic validation is separated from event planning so every
early refusal has a small, independently reusable theorem. -/
def preflight (before : State) (command : Command) : Except Refusal Unit :=
  let claim := command.clearing.exchange
  if EventBatch.WIRE_U64_MODULUS ≤ before.revision + 1 then .error .revisionExhausted
  else if claim.exchangeId ∈ before.consumedExchanges then .error .exchangeReplay
  else if command.clearing.book.bindingKey ∈ before.consumedBooks then .error .bookReplay
  else if claim.seller = claim.buyer then .error .sameParty
  else if claim.offered = claim.requested then .error .sameUnit
  else if command.offered.key != claim.offered then .error .offeredKeyMismatch
  else if command.requested.key != claim.requested then .error .requestedKeyMismatch
  else if !command.offered.AuthorizedBy before.custody claim.seller then
    .error .offeredSourceRejected
  else if !command.requested.AuthorizedBy before.custody claim.buyer then
    .error .requestedSourceRejected
  else .ok ()

private def indexedEvent (boundary : Boundary) (index : Nat)
    (head : EventBatch.StreamHead) (payload : TransactionEvent) :
    EventBatch.IndexedEvent :=
  let statement : EventStatement := {
    aggregate := head.stream.aggregate
    version := head.stream.version
    sequence := head.sequence + 1
    predecessor := head.head
    payloadDigest := boundary.payloadDigest payload }
  ⟨index, statement, boundary.eventBatch.eventDigest statement⟩

private def settleAfterPreflight (config : Config) (boundary : Boundary) (before : State)
    (_load : UpstreamCanonicalLoad config before)
    (coordinate : EventBatch.FinalizedTurnCoordinate)
    (_finalized : UpstreamFinalizedCarrier config coordinate)
    (initialHeads : List EventBatch.StreamHead) (command : Command) :
    Except Refusal (Output boundary initialHeads) := do
  let claim := command.clearing.exchange
  let successor : State :=
    ⟨before.authority, before.world, before.revision + 1,
      before.custody.afterExchange claim,
      insert claim.exchangeId before.consumedExchanges,
      insert command.clearing.book.bindingKey before.consumedBooks⟩
  let beforeDigest := boundary.stateDigest before
  let afterDigest := boundary.stateDigest successor
  let receipt : SettlementReceipt := {
    exchange := claim
    book := command.clearing.book.bindingKey
    privacy := .operatorVisibleOpeningAwareJudge
    finalizedCoordinate := coordinate
    offeredSourceBatch := claim.offered.sourceBatch
    requestedSourceBatch := claim.requested.sourceBatch
    beforeStateDigest := beforeDigest
    afterStateDigest := afterDigest }
  let projection : MarketProjection := {
    exchangeId := claim.exchangeId
    seller := claim.seller
    buyer := claim.buyer
    offered := claim.offered
    requested := claim.requested
    book := command.clearing.book.bindingKey
    privacy := .operatorVisibleOpeningAwareJudge
    beforeStateDigest := beforeDigest
    afterStateDigest := afterDigest }
  let custodyPayload := TransactionEvent.custodyTransferred receipt
  let projectionPayload := TransactionEvent.marketProjected projection
  let custodyHead ← match EventBatch.headFor? initialHeads config.raw.custodyStream with
    | some head => pure head
    | none => throw .missingCustodyHead
  let projectionHead ← match EventBatch.headFor? initialHeads config.raw.projectionStream with
    | some head => pure head
    | none => throw .missingProjectionHead
  let custodyEvent := indexedEvent boundary 0 custodyHead custodyPayload
  let projectionEvent := indexedEvent boundary 1 projectionHead projectionPayload
  let statement : EventBatch.Statement := ⟨coordinate, [custodyEvent, projectionEvent]⟩
  let envelope : EventBatch.Envelope :=
    ⟨statement, boundary.eventBatch.batchDigest statement⟩
  match hbatch : EventBatch.applyBatch boundary.eventBatch initialHeads envelope with
  | .error error => .error (.eventBatch error)
  | .ok applied =>
      let commit : AtomicCommitIntent := ⟨beforeDigest, afterDigest, envelope⟩
      let evidence : CompleteEventBatchEvidence boundary initialHeads :=
        ⟨custodyPayload, projectionPayload, custodyEvent, projectionEvent,
          envelope, applied, rfl, rfl, rfl, hbatch⟩
      .ok ⟨successor, receipt, projection, commit, evidence,
        CanonicalCustody.afterExchange_offered_owner before.custody claim,
        CanonicalCustody.afterExchange_requested_owner before.custody claim
          command.clearing.unitsDistinct,
        by
          change claim.offered ∈ insert claim.offered
            (insert claim.requested before.custody.mintNullifiers)
          simp,
        by
          change claim.requested ∈ insert claim.offered
            (insert claim.requested before.custody.mintNullifiers)
          simp,
        by
          change claim.exchangeId ∈ insert claim.exchangeId before.consumedExchanges
          simp,
        by
          change command.clearing.book.bindingKey ∈
            insert command.clearing.book.bindingKey before.consumedBooks
          simp,
        rfl, rfl, rfl, rfl⟩

/-- One semantic transaction.  Success is still only a persistence candidate:
the host must atomically compare `commit.expectedStateDigest`, install the full
successor image, and append `commit.envelope`. -/
def settle (config : Config) (boundary : Boundary) (before : State)
    (load : UpstreamCanonicalLoad config before)
    (coordinate : EventBatch.FinalizedTurnCoordinate)
    (finalized : UpstreamFinalizedCarrier config coordinate)
    (initialHeads : List EventBatch.StreamHead) (command : Command) :
    Except Refusal (Output boundary initialHeads) :=
  match preflight before command with
  | .error refusal => .error refusal
  | .ok _ => settleAfterPreflight config boundary before load coordinate finalized
      initialHeads command

/-! ## Generic refusal and successful-output laws -/

theorem settle_exchange_replay_refused (config : Config) (boundary : Boundary)
    (before : State) (load : UpstreamCanonicalLoad config before)
    (coordinate : EventBatch.FinalizedTurnCoordinate)
    (finalized : UpstreamFinalizedCarrier config coordinate)
    (initialHeads : List EventBatch.StreamHead) (command : Command)
    (freshRevision : before.revision + 1 < EventBatch.WIRE_U64_MODULUS)
    (replay : command.clearing.exchange.exchangeId ∈ before.consumedExchanges) :
    settle config boundary before load coordinate finalized initialHeads command =
      .error .exchangeReplay := by
  have rejected : preflight before command = .error .exchangeReplay := by
    simp [preflight, Nat.not_le.mpr freshRevision, replay]
  simp [settle, rejected]

theorem settle_book_replay_refused (config : Config) (boundary : Boundary)
    (before : State) (load : UpstreamCanonicalLoad config before)
    (coordinate : EventBatch.FinalizedTurnCoordinate)
    (finalized : UpstreamFinalizedCarrier config coordinate)
    (initialHeads : List EventBatch.StreamHead) (command : Command)
    (freshRevision : before.revision + 1 < EventBatch.WIRE_U64_MODULUS)
    (exchangeFresh : command.clearing.exchange.exchangeId ∉ before.consumedExchanges)
    (replay : command.clearing.book.bindingKey ∈ before.consumedBooks) :
    settle config boundary before load coordinate finalized initialHeads command =
      .error .bookReplay := by
  have rejected : preflight before command = .error .bookReplay := by
    simp [preflight, Nat.not_le.mpr freshRevision, exchangeFresh, replay]
  simp [settle, rejected]

theorem settle_offered_key_substitution_refused
    (config : Config) (boundary : Boundary) (before : State)
    (load : UpstreamCanonicalLoad config before)
    (coordinate : EventBatch.FinalizedTurnCoordinate)
    (finalized : UpstreamFinalizedCarrier config coordinate)
    (initialHeads : List EventBatch.StreamHead) (command : Command)
    (freshRevision : before.revision + 1 < EventBatch.WIRE_U64_MODULUS)
    (exchangeFresh : command.clearing.exchange.exchangeId ∉ before.consumedExchanges)
    (bookFresh : command.clearing.book.bindingKey ∉ before.consumedBooks)
    (partiesDistinct : command.clearing.exchange.seller ≠ command.clearing.exchange.buyer)
    (unitsDistinct : command.clearing.exchange.offered ≠ command.clearing.exchange.requested)
    (substitution : command.offered.key ≠ command.clearing.exchange.offered) :
    settle config boundary before load coordinate finalized initialHeads command =
      .error .offeredKeyMismatch := by
  have rejected : preflight before command = .error .offeredKeyMismatch := by
    simp [preflight, Nat.not_le.mpr freshRevision, exchangeFresh, bookFresh,
      partiesDistinct, unitsDistinct, substitution]
  simp [settle, rejected]

theorem successful_transaction_has_two_ordered_events
    {config : Config} {boundary : Boundary} {before : State}
    {load : UpstreamCanonicalLoad config before}
    {coordinate : EventBatch.FinalizedTurnCoordinate}
    {finalized : UpstreamFinalizedCarrier config coordinate}
    {initialHeads : List EventBatch.StreamHead} {command : Command}
    {output : Output boundary initialHeads}
    (_accepted : settle config boundary before load coordinate finalized initialHeads command =
      .ok output) :
    output.events.envelope.statement.events =
      [output.events.custodyEvent, output.events.projectionEvent] :=
  output.events.orderedExact

theorem successful_transaction_batch_was_applied
    {boundary : Boundary} {initialHeads : List EventBatch.StreamHead}
    (output : Output boundary initialHeads) :
    EventBatch.applyBatch boundary.eventBatch initialHeads output.events.envelope =
      .ok output.events.applied :=
  output.events.accepted

theorem successful_transaction_consumes_exact_assets
    {boundary : Boundary} {initialHeads : List EventBatch.StreamHead}
    (output : Output boundary initialHeads) :
    output.receipt.exchange.offered ∈ output.successor.custody.mintNullifiers ∧
    output.receipt.exchange.requested ∈ output.successor.custody.mintNullifiers ∧
    output.receipt.exchange.exchangeId ∈ output.successor.consumedExchanges ∧
    output.receipt.book ∈ output.successor.consumedBooks :=
  ⟨output.offeredMintConsumed, output.requestedMintConsumed,
    output.exchangeConsumed, output.bookConsumed⟩

theorem successful_transaction_swaps_exact_owners
    {boundary : Boundary} {initialHeads : List EventBatch.StreamHead}
    (output : Output boundary initialHeads) :
    output.successor.custody.ownerOf? output.receipt.exchange.offered =
        some output.receipt.exchange.buyer ∧
      output.successor.custody.ownerOf? output.receipt.exchange.requested =
        some output.receipt.exchange.seller :=
  ⟨output.offeredOwnerExact, output.requestedOwnerExact⟩

theorem successful_transaction_privacy_is_not_house_blind
    {boundary : Boundary} {initialHeads : List EventBatch.StreamHead}
    (output : Output boundary initialHeads) :
    output.receipt.privacy = .operatorVisibleOpeningAwareJudge :=
  output.privacyExact

#assert_axioms Config.streams_are_distinct
#assert_axioms CanonicalCustody.afterExchange_offered_owner
#assert_axioms CanonicalCustody.afterExchange_requested_owner
#assert_axioms PartClearingReceipt.privacy_is_operator_visible
#assert_axioms content_relic_has_no_transaction_source
#assert_axioms finalized_mint_already_consumed_is_not_authorized
#assert_axioms existing_unit_authorization_is_exact_current_owner
#assert_axioms settle_exchange_replay_refused
#assert_axioms settle_book_replay_refused
#assert_axioms settle_offered_key_substitution_refused
#assert_axioms successful_transaction_has_two_ordered_events
#assert_axioms successful_transaction_batch_was_applied
#assert_axioms successful_transaction_consumes_exact_assets
#assert_axioms successful_transaction_swaps_exact_owners
#assert_axioms successful_transaction_privacy_is_not_house_blind

end Dregg2.Games.PathOfAngels.OrdinarySalvageFinalizedTransaction
