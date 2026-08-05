/-
# ShipExpeditionSeasonBoundary — derived projection, sealed authority adapters

Importers may author a display plan, call the proof-requiring runtime sealer,
submit already-sealed receipts, and rebuild derived projections.  They cannot
manufacture runtime inclusion, health, PartId Bazaar, season state, unchecked
projection transitions, fanout successors, or fixture authority.
-/
import Dregg2.Games.PathOfAngels.ShipExpeditionSeason
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.ShipExpeditionSeasonBoundary

open Dregg2.Games.PathOfAngels.ShipExpeditionSeason

set_option autoImplicit false

theorem activated_config_constructor_is_private : True := by
  fail_if_success (have _ := Config.mk)
  trivial

theorem derived_state_constructor_is_private : True := by
  fail_if_success (have _ := State.mk)
  trivial

theorem runtime_event_batch_receipt_constructor_is_private : True := by
  fail_if_success (have _ := RuntimeEventBatchReceipt.mk)
  trivial

theorem canonical_health_receipt_constructor_is_private : True := by
  fail_if_success (have _ := CanonicalHealthReceiptInterface.mk)
  trivial

theorem ordinary_part_bazaar_receipt_constructor_is_private : True := by
  fail_if_success (have _ := BazaarPartReceiptInterface.mk)
  trivial

theorem unchecked_runtime_projection_is_private : True := by
  fail_if_success (have _ := acceptRuntime)
  trivial

theorem unchecked_health_projection_is_private : True := by
  fail_if_success (have _ := acceptHealth)
  trivial

theorem unchecked_market_projection_is_private : True := by
  fail_if_success (have _ := acceptPartMarket)
  trivial

theorem event_batch_planning_fold_is_private : True := by
  fail_if_success (have _ := planIndexedEvents)
  trivial

theorem fixture_authority_is_private : True := by
  fail_if_success (have _ := fixtureConfig)
  fail_if_success (have _ := fixtureRuntimeReceipt)
  fail_if_success (have _ := fixtureHealthReceipt)
  fail_if_success (have _ := fixtureMarketReceipt)
  trivial

#assert_axioms activated_config_constructor_is_private
#assert_axioms derived_state_constructor_is_private
#assert_axioms runtime_event_batch_receipt_constructor_is_private
#assert_axioms canonical_health_receipt_constructor_is_private
#assert_axioms ordinary_part_bazaar_receipt_constructor_is_private
#assert_axioms unchecked_runtime_projection_is_private
#assert_axioms unchecked_health_projection_is_private
#assert_axioms unchecked_market_projection_is_private
#assert_axioms event_batch_planning_fold_is_private
#assert_axioms fixture_authority_is_private

end Dregg2.Games.PathOfAngels.ShipExpeditionSeasonBoundary
