/-
# Finalized ordinary-salvage transaction — hostile workbook

These examples exercise the public, proof-carrying surface without pretending
to possess the three native admissions which intentionally have no Lean
producer.  They cover deployment activation, fresh/finalized versus existing
unit sources, mint-nullifier replay, exact UnitKey substitution refusal, exact
book/exchange replay refusal, the relic wall, and the guarantees carried by any
successful two-event transaction output.
-/
import Dregg2.Games.PathOfAngels.OrdinarySalvageFinalizedTransaction

namespace Dregg2.Games.PathOfAngels.OrdinarySalvageFinalizedTransactionExamples

open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.OrdinarySalvageFinalizedTransaction

set_option autoImplicit false

private def digestFilled (value : Nat) : Digest32 where
  bytes := List.replicate 32 ⟨value % 256, Nat.mod_lt _ (by omega)⟩
  length_eq := by simp

private def world : EventBatch.WorldIdentity where
  federationId := digestFilled 1
  contentRoot := digestFilled 2
  activationDigest := digestFilled 3
  contentSession := digestFilled 4
  contentEpoch := ⟨5⟩

private def custodyStream : EventBatch.StreamId where
  world
  aggregate := ⟨world.federationId, 91, digestFilled 6⟩
  version := ⟨1⟩

private def projectionStream : EventBatch.StreamId where
  world
  aggregate := ⟨world.federationId, 92, digestFilled 7⟩
  version := ⟨1⟩

private def rawConfig : RawConfig :=
  ⟨digestFilled 8, world, custodyStream, projectionStream⟩

theorem deployment_shape_activates : (activate? rawConfig).isSome = true := by
  rfl

private def config : Config := (activate? rawConfig).get (by rfl)

theorem activated_streams_are_separate :
    config.raw.custodyStream ≠ config.raw.projectionStream :=
  config.streams_are_distinct

theorem fresh_finalized_mint_is_an_authorized_source
    (mint : OrdinarySalvageExchange.MintAuthorization) :
    (UnitSource.finalized mint).AuthorizedBy
      (CanonicalCustody.empty (digestFilled 20)) mint.unit.initialOwner := by
  simp [UnitSource.AuthorizedBy, CanonicalCustody.empty]

theorem absent_existing_unit_is_not_authorized
    (key : OrdinarySalvageExchange.UnitKey) (owner : Digest32) :
    ¬ (UnitSource.existing key).AuthorizedBy
      (CanonicalCustody.empty (digestFilled 21)) owner := by
  simp [UnitSource.AuthorizedBy, CanonicalCustody.ownerOf?, CanonicalCustody.empty]

theorem consumed_finalized_mint_cannot_reenter (custody : CanonicalCustody)
    (mint : OrdinarySalvageExchange.MintAuthorization) (owner : Digest32)
    (replay : mint.unit.key ∈ custody.mintNullifiers) :
    ¬ (UnitSource.finalized mint).AuthorizedBy custody owner :=
  finalized_mint_already_consumed_is_not_authorized custody mint owner replay

theorem relic_has_no_source (relic : ContentContract.RelicId) :
    relicMarketIngress relic = none := rfl

theorem exact_exchange_replay_is_refused
    (boundary : Boundary) (before : State)
    (load : UpstreamCanonicalLoad config before)
    (coordinate : EventBatch.FinalizedTurnCoordinate)
    (finalized : UpstreamFinalizedCarrier config coordinate)
    (initialHeads : List EventBatch.StreamHead) (command : Command)
    (freshRevision : before.revision + 1 < EventBatch.WIRE_U64_MODULUS)
    (replay : command.clearing.exchange.exchangeId ∈ before.consumedExchanges) :
    settle config boundary before load coordinate finalized initialHeads command =
      .error .exchangeReplay :=
  settle_exchange_replay_refused config boundary before load coordinate finalized
    initialHeads command freshRevision replay

theorem exact_book_replay_is_refused
    (boundary : Boundary) (before : State)
    (load : UpstreamCanonicalLoad config before)
    (coordinate : EventBatch.FinalizedTurnCoordinate)
    (finalized : UpstreamFinalizedCarrier config coordinate)
    (initialHeads : List EventBatch.StreamHead) (command : Command)
    (freshRevision : before.revision + 1 < EventBatch.WIRE_U64_MODULUS)
    (exchangeFresh : command.clearing.exchange.exchangeId ∉ before.consumedExchanges)
    (replay : command.clearing.book.bindingKey ∈ before.consumedBooks) :
    settle config boundary before load coordinate finalized initialHeads command =
      .error .bookReplay :=
  settle_book_replay_refused config boundary before load coordinate finalized
    initialHeads command freshRevision exchangeFresh replay

theorem substituted_offered_unit_is_refused
    (boundary : Boundary) (before : State)
    (load : UpstreamCanonicalLoad config before)
    (coordinate : EventBatch.FinalizedTurnCoordinate)
    (finalized : UpstreamFinalizedCarrier config coordinate)
    (initialHeads : List EventBatch.StreamHead) (command : Command)
    (freshRevision : before.revision + 1 < EventBatch.WIRE_U64_MODULUS)
    (exchangeFresh : command.clearing.exchange.exchangeId ∉ before.consumedExchanges)
    (bookFresh : command.clearing.book.bindingKey ∉ before.consumedBooks)
    (substitution : command.offered.key ≠ command.clearing.exchange.offered) :
    settle config boundary before load coordinate finalized initialHeads command =
      .error .offeredKeyMismatch :=
  settle_offered_key_substitution_refused config boundary before load coordinate finalized
    initialHeads command freshRevision exchangeFresh bookFresh
    command.clearing.partiesDistinct command.clearing.unitsDistinct substitution

theorem every_success_has_exact_custody_replay_and_two_events
    {boundary : Boundary} {initialHeads : List EventBatch.StreamHead}
    (output : Output boundary initialHeads) :
    output.successor.custody.ownerOf? output.receipt.exchange.offered =
        some output.receipt.exchange.buyer ∧
      output.successor.custody.ownerOf? output.receipt.exchange.requested =
        some output.receipt.exchange.seller ∧
      output.receipt.exchange.offered ∈ output.successor.custody.mintNullifiers ∧
      output.receipt.exchange.requested ∈ output.successor.custody.mintNullifiers ∧
      output.receipt.exchange.exchangeId ∈ output.successor.consumedExchanges ∧
      output.receipt.book ∈ output.successor.consumedBooks ∧
      output.events.envelope.statement.events =
        [output.events.custodyEvent, output.events.projectionEvent] ∧
      EventBatch.applyBatch boundary.eventBatch initialHeads output.events.envelope =
        .ok output.events.applied := by
  exact ⟨output.offeredOwnerExact, output.requestedOwnerExact,
    output.offeredMintConsumed, output.requestedMintConsumed,
    output.exchangeConsumed, output.bookConsumed, output.events.orderedExact,
    output.events.accepted⟩

theorem every_success_is_honestly_operator_visible
    {boundary : Boundary} {initialHeads : List EventBatch.StreamHead}
    (output : Output boundary initialHeads) :
    output.receipt.privacy = .operatorVisibleOpeningAwareJudge :=
  successful_transaction_privacy_is_not_house_blind output

#assert_axioms deployment_shape_activates
#assert_axioms activated_streams_are_separate
#assert_axioms fresh_finalized_mint_is_an_authorized_source
#assert_axioms absent_existing_unit_is_not_authorized
#assert_axioms consumed_finalized_mint_cannot_reenter
#assert_axioms relic_has_no_source
#assert_axioms exact_exchange_replay_is_refused
#assert_axioms exact_book_replay_is_refused
#assert_axioms substituted_offered_unit_is_refused
#assert_axioms every_success_has_exact_custody_replay_and_two_events
#assert_axioms every_success_is_honestly_operator_visible

end Dregg2.Games.PathOfAngels.OrdinarySalvageFinalizedTransactionExamples
