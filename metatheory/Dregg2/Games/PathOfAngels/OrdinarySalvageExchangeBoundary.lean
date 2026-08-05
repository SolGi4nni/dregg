/-
# Ordinary salvage exchange — importer boundary

Importers can select a unit from a finalized runtime/EventBatch ordinary mint,
but cannot fabricate the mint proof, market unit, opening verifier result,
custody state, durable load, or persistence success.  A story relic is not a
market unit and has no coercion into one.
-/
import Dregg2.Games.PathOfAngels.OrdinarySalvageExchange

namespace Dregg2.Games.PathOfAngels.OrdinarySalvageExchangeBoundary

open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.OrdinarySalvageExchange

set_option autoImplicit false

theorem mint_authorization_constructor_is_private : True := by
  fail_if_success (have _ := MintAuthorization.mk)
  trivial

theorem market_unit_constructor_is_private : True := by
  fail_if_success (have _ := MarketUnit.mk)
  trivial

theorem initial_custody_constructor_is_private : True := by
  fail_if_success (have _ := InitialCustodyAuthorization.mk)
  trivial

theorem exact_custody_constructor_is_private : True := by
  fail_if_success (have _ := CustodyAuthorization.mk)
  trivial

theorem opening_authorization_constructor_is_private : True := by
  fail_if_success (have _ := UpstreamPartOpeningAuthorization.mk)
  trivial

theorem opening_receipt_constructor_is_private : True := by
  fail_if_success (have _ := OpeningReceipt.mk)
  trivial

theorem canonical_exchange_receipt_constructor_is_private : True := by
  fail_if_success (have _ := ExchangeReceipt.mk)
  trivial

theorem state_constructor_is_private : True := by
  fail_if_success (have _ := State.mk)
  trivial

theorem persistence_candidate_constructor_is_private : True := by
  fail_if_success (have _ := PersistenceCandidate.mk)
  trivial

theorem persistence_success_constructor_is_private : True := by
  fail_if_success (have _ := SuccessfulPersistence.mk)
  trivial

theorem durable_deployment_constructor_is_private : True := by
  fail_if_success (have _ := DurableDeployment.mk)
  trivial

theorem content_relic_is_not_a_market_unit
    (relic : ContentContract.RelicId) : True := by
  have _absent : relicMarketIngress relic = none := rfl
  fail_if_success (have _unit : MarketUnit := relic)
  trivial

theorem content_relic_ingress_is_always_absent
    (relic : ContentContract.RelicId) :
    relicMarketIngress relic = none := rfl

#assert_axioms mint_authorization_constructor_is_private
#assert_axioms market_unit_constructor_is_private
#assert_axioms initial_custody_constructor_is_private
#assert_axioms exact_custody_constructor_is_private
#assert_axioms opening_authorization_constructor_is_private
#assert_axioms opening_receipt_constructor_is_private
#assert_axioms canonical_exchange_receipt_constructor_is_private
#assert_axioms state_constructor_is_private
#assert_axioms persistence_candidate_constructor_is_private
#assert_axioms persistence_success_constructor_is_private
#assert_axioms durable_deployment_constructor_is_private
#assert_axioms content_relic_is_not_a_market_unit
#assert_axioms content_relic_ingress_is_always_absent

end Dregg2.Games.PathOfAngels.OrdinarySalvageExchangeBoundary
