/-
# Finalized ordinary-salvage transaction — importer boundary

Importers can activate a public deployment shape and submit already-authorized
inputs.  They cannot mint a canonical load, finalized carrier, opening-aware
UnitKey authorization, semantic state, custody owner map, output, or EventBatch
evidence.  Relics cannot be coerced into either transaction source.
-/
import Dregg2.Games.PathOfAngels.OrdinarySalvageFinalizedTransaction

namespace Dregg2.Games.PathOfAngels.OrdinarySalvageFinalizedTransactionBoundary

open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.OrdinarySalvageFinalizedTransaction

set_option autoImplicit false

theorem activated_config_constructor_is_private : True := by
  fail_if_success (have _ := Config.mk)
  trivial

theorem canonical_custody_constructor_is_private : True := by
  fail_if_success (have _ := CanonicalCustody.mk)
  trivial

theorem canonical_state_constructor_is_private : True := by
  fail_if_success (have _ := State.mk)
  trivial

theorem genesis_admission_constructor_is_private : True := by
  fail_if_success (have _ := UpstreamGenesis.mk)
  trivial

theorem canonical_load_constructor_is_private : True := by
  fail_if_success (have _ := UpstreamCanonicalLoad.mk)
  trivial

theorem finalized_carrier_constructor_is_private : True := by
  fail_if_success (have _ := UpstreamFinalizedCarrier.mk)
  trivial

theorem opening_authorization_constructor_is_private : True := by
  fail_if_success (have _ := UpstreamOpeningAwareAuthorization.mk)
  trivial

theorem clearing_receipt_constructor_is_private : True := by
  fail_if_success (have _ := PartClearingReceipt.mk)
  trivial

theorem transaction_output_constructor_is_private : True := by
  fail_if_success (have _ := Output.mk)
  trivial

theorem event_batch_evidence_constructor_is_private : True := by
  fail_if_success (have _ := CompleteEventBatchEvidence.mk)
  trivial

theorem relic_is_not_a_unit_source (relic : ContentContract.RelicId) : relic = relic := by
  fail_if_success (have _source : UnitSource := relic)
  rfl

theorem relic_transaction_ingress_is_absent (relic : ContentContract.RelicId) :
    relicMarketIngress relic = none := rfl

theorem house_blind_grade_is_not_representable : True := by
  fail_if_success (have _ := PrivacyGrade.houseBlind)
  trivial

#assert_axioms activated_config_constructor_is_private
#assert_axioms canonical_custody_constructor_is_private
#assert_axioms canonical_state_constructor_is_private
#assert_axioms genesis_admission_constructor_is_private
#assert_axioms canonical_load_constructor_is_private
#assert_axioms finalized_carrier_constructor_is_private
#assert_axioms opening_authorization_constructor_is_private
#assert_axioms clearing_receipt_constructor_is_private
#assert_axioms transaction_output_constructor_is_private
#assert_axioms event_batch_evidence_constructor_is_private
#assert_axioms relic_is_not_a_unit_source
#assert_axioms relic_transaction_ingress_is_absent
#assert_axioms house_blind_grade_is_not_representable

end Dregg2.Games.PathOfAngels.OrdinarySalvageFinalizedTransactionBoundary
