/-
# Ordinary expedition salvage exchange — persisted hostile workbook

The mint and DrEX verifier capabilities remain abstract because their only real
producers are the finalized runtime/EventBatch path and the combined opening
verifier.  Everything after those boundaries is an executable, exact Lean
journey: initialize custody, persist, open a barter, persist, settle it, persist,
and inspect the canonical receipt and swapped owners.
-/
import Dregg2.Games.PathOfAngels.OrdinarySalvageExchange

namespace Dregg2.Games.PathOfAngels.OrdinarySalvageExchangeExamples

open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.DarkBazaar
open Dregg2.Games.PathOfAngels.OrdinarySalvageExchange

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private def repeatedDigest (value : Nat) : Digest32 where
  bytes := List.replicate 32 ⟨value % 256, Nat.mod_lt _ (by decide)⟩
  length_eq := by simp

def authorityId : Digest32 := repeatedDigest 88
def exchangeId : Digest32 := repeatedDigest 90
def otherExchangeId : Digest32 := repeatedDigest 91

class FixtureCapabilities where
  authority : BazaarGame.DeploymentAuthority authorityId
  genesis : OrdinarySalvageExchange.RegistryGenesis authority
  offeredMint : MintAuthorization
  requestedMint : MintAuthorization
  unitsDistinct : offeredMint.unit.key ≠ requestedMint.unit.key
  ownersDistinct :
    offeredMint.unit.initialOwner ≠ requestedMint.unit.initialOwner
  book : BazaarGame.OpeningAwareBookReceipt
  bookSellerExact :
    book.claim.spec.seller.value = offeredMint.unit.initialOwner
  bookBuyerExact :
    book.claim.spec.buyer.value = requestedMint.unit.initialOwner
  oneForOne : book.claim.output.volume = 1
  openingAuthorization : (statement : PartOpeningStatement) →
    UpstreamPartOpeningAuthorization statement
  persistence : (candidate : OrdinarySalvageExchange.PersistenceCandidate) →
    OrdinarySalvageExchange.SuccessfulPersistence candidate.request

variable [fixture : FixtureCapabilities]

local notation "authority" => fixture.authority

def offeredUnit : MarketUnit := fixture.offeredMint.unit
def requestedUnit : MarketUnit := fixture.requestedMint.unit

def initialCustody : InitialCustodyAuthorization :=
  InitialCustodyAuthorization.ofFinalizedMints fixture.offeredMint
    fixture.requestedMint fixture.unitsDistinct fixture.ownersDistinct

def registry : Registry := Registry.open fixture.genesis

def acceptedB {T : Type} : Except OrdinarySalvageExchange.Refusal T → Bool
  | .ok _ => true
  | .error _ => false

def refusalB {T : Type} (expected : OrdinarySalvageExchange.Refusal) :
    Except OrdinarySalvageExchange.Refusal T → Bool
  | .ok _ => false
  | .error actual => decide (actual = expected)

def valueOfAccepted {T : Type}
    (result : Except OrdinarySalvageExchange.Refusal T)
    (accepted : acceptedB result = true) : T :=
  match h : result with
  | .ok value => value
  | .error _ => False.elim (by simpa [acceptedB, h] using accepted)

def initialResult := registry.initialize authority initialCustody
theorem initial_accepted : acceptedB initialResult = true := by rfl
def initialCandidate := valueOfAccepted initialResult initial_accepted
def initial : OrdinarySalvageExchange.DurableDeployment :=
  initialCandidate.continue (fixture.persistence initialCandidate)

def claim : ExchangeClaim where
  exchangeId := exchangeId
  seller := initialCustody.offered.unit.initialOwner
  buyer := initialCustody.requested.unit.initialOwner
  offered := initialCustody.offered.unit.key
  requested := initialCustody.requested.unit.key

theorem initial_seller_owns_offered :
    initial.key.inventory.ownerOf? claim.offered = some claim.seller := by
  change (Inventory.ofAuthorization initialCustody).ownerOf?
    initialCustody.offered.unit.key =
      some initialCustody.offered.unit.initialOwner
  exact Inventory.ofAuthorization_offered_owner initialCustody

theorem initial_buyer_owns_requested :
    initial.key.inventory.ownerOf? claim.requested = some claim.buyer := by
  change (Inventory.ofAuthorization initialCustody).ownerOf?
    initialCustody.requested.unit.key =
      some initialCustody.requested.unit.initialOwner
  exact Inventory.ofAuthorization_requested_owner initialCustody

def custody : CustodyAuthorization initial.key.inventory claim :=
  CustodyAuthorization.ofExact initial.key.inventory claim
    initial_seller_owns_offered initial_buyer_owns_requested
    initialCustody.unitsDistinct initialCustody.ownersDistinct

def openResult := openExchange initial authority claim custody
theorem exchange_opens : acceptedB openResult = true := by rfl
def openCandidate := valueOfAccepted openResult exchange_opens
def opened : OrdinarySalvageExchange.DurableDeployment :=
  openCandidate.continue (fixture.persistence openCandidate)

theorem open_is_visible_only_after_persistence : opened.pending = some claim := by
  rfl

def openingStatement : PartOpeningStatement := ⟨claim, fixture.book.bindingKey⟩

def openingReceipt : OpeningReceipt :=
  OpeningReceipt.ofUpstream claim fixture.book
    (fixture.openingAuthorization openingStatement)
    fixture.bookSellerExact fixture.bookBuyerExact fixture.oneForOne

def settleResult := settleExchange opened authority openingReceipt
theorem exact_opening_settles : acceptedB settleResult = true := by
  have fresh : openingReceipt.claim.exchangeId ∉
      opened.key.consumedExchanges := by
    change exchangeId ∉ (∅ : Finset Digest32)
    simp
  obtain ⟨candidate, accepted⟩ :=
    settleExchange_exact_pending_accepts opened authority openingReceipt
      (by rfl) (by rfl) fresh (by rfl)
  change acceptedB (settleExchange opened authority openingReceipt) = true
  rw [accepted]
  rfl
def settleCandidate := valueOfAccepted settleResult exact_opening_settles
def settled : OrdinarySalvageExchange.DurableDeployment :=
  settleCandidate.continue (fixture.persistence settleCandidate)

theorem exact_authorized_swap_has_both_new_owners :
    let swapped := (Inventory.ofAuthorization initialCustody).swap claim
    swapped.ownerOf? claim.offered = some claim.buyer ∧
      swapped.ownerOf? claim.requested = some claim.seller := by
  exact InitialCustodyAuthorization.swap_owners initialCustody exchangeId

theorem exact_v1_book_has_four_distinct_same_opening_statements :
    openingReceipt.book.transcript.card = 4 :=
  openingReceipt.has_exact_v1_same_opening_book

/-! ## Hostile paths -/

def wrongClaim : ExchangeClaim := { claim with exchangeId := otherExchangeId }

def wrongOpening : OpeningReceipt :=
  OpeningReceipt.ofUpstream wrongClaim fixture.book
    (fixture.openingAuthorization ⟨wrongClaim, fixture.book.bindingKey⟩)
    fixture.bookSellerExact fixture.bookBuyerExact fixture.oneForOne

theorem different_exchange_opening_is_refused :
    refusalB .openingMismatch
      (settleExchange opened authority wrongOpening) = true := by
  have wrong : claim ≠ wrongOpening.claim := by
    intro equal
    have ids := congrArg ExchangeClaim.exchangeId equal
    exact (by native_decide : exchangeId ≠ otherExchangeId) ids
  have fresh : wrongOpening.claim.exchangeId ∉ opened.key.consumedExchanges := by
    change otherExchangeId ∉ (∅ : Finset Digest32)
    simp
  have refused := settleExchange_wrong_opening_refused opened authority
    wrongOpening claim (by rfl) fresh open_is_visible_only_after_persistence wrong
  change refusalB .openingMismatch
    (settleExchange opened authority wrongOpening) = true
  rw [refused]
  rfl

def cancelResult := cancelExchange opened authority
theorem competing_cancel_is_locally_valid : acceptedB cancelResult = true := by rfl
def cancelCandidate := valueOfAccepted cancelResult competing_cancel_is_locally_valid

theorem every_exact_candidate_request_succeeds_at_its_expected_head :
    runtimeCas settleCandidate.request.expected settleCandidate.request =
      .ok (some settleCandidate.request.replacement) := by
  exact runtimeCas_at_exact_expected _

theorem restart_continuation_uses_exact_persisted_replacement :
    settled.key = settleCandidate.request.replacement :=
  PersistenceCandidate.continuation_replacement_exact _ _

omit fixture in theorem one_mint_cannot_authorize_both_genesis_units
    (mint : MintAuthorization) :
    ¬ (mint.unit.key ≠ mint.unit.key) := by simp

omit fixture in theorem relic_has_no_market_unit_ingress
    (relic : ContentContract.RelicId) :
    relicMarketIngress relic = none := rfl

#assert_axioms initial_accepted
#assert_axioms initial_seller_owns_offered
#assert_axioms initial_buyer_owns_requested
#assert_axioms exchange_opens
#assert_axioms open_is_visible_only_after_persistence
#assert_axioms exact_opening_settles
#assert_axioms exact_authorized_swap_has_both_new_owners
#assert_axioms exact_v1_book_has_four_distinct_same_opening_statements
#assert_compiled different_exchange_opening_is_refused
#assert_axioms competing_cancel_is_locally_valid
#assert_axioms every_exact_candidate_request_succeeds_at_its_expected_head
#assert_axioms restart_continuation_uses_exact_persisted_replacement
#assert_axioms one_mint_cannot_authorize_both_genesis_units
#assert_axioms relic_has_no_market_unit_ingress

end Dregg2.Games.PathOfAngels.OrdinarySalvageExchangeExamples
