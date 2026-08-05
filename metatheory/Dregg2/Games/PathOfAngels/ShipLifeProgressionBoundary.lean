/-
# ShipLifeProgressionBoundary — no shadow-authority regression teeth

Importers may submit receipts to the public reducer and observe its derived
views.  They cannot mint the coordinator state, attach an owner to a Shipworks
settlement, assert attendant EventBatch inclusion, fabricate craft conservation,
forge gallery/health/ordinary-part/holder receipts, call the unchecked fanout
fold, or mint a migration attestation.
-/
import Dregg2.Games.PathOfAngels.ShipLifeProgression
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.ShipLifeProgressionBoundary

open Dregg2.Games.PathOfAngels.ShipLifeProgression

set_option autoImplicit false

theorem activated_config_constructor_is_private : True := by
  fail_if_success (have _ := Config.mk)
  trivial

theorem projection_state_constructor_is_private : True := by
  fail_if_success (have _ := State.mk)
  trivial

theorem attendant_inclusion_receipt_is_private : True := by
  fail_if_success (have _ := AttendantContinuityReceiptInterface.mk)
  trivial

theorem shipworks_owner_binding_receipt_is_private : True := by
  fail_if_success (have _ := ShipworksSettlementReceiptInterface.mk)
  trivial

theorem shipworks_failure_owner_binding_receipt_is_private : True := by
  fail_if_success (have _ := ShipworksFailureReceiptInterface.mk)
  trivial

theorem craft_gear_receipt_is_private : True := by
  fail_if_success (have _ := DreggnetCraftGearReceiptInterface.mk)
  trivial

theorem gallery_receipt_is_private : True := by
  fail_if_success (have _ := GalleryGatedReceiptInterface.mk)
  trivial

theorem holder_cosmetic_receipt_is_private : True := by
  fail_if_success (have _ := HolderCosmeticReceiptInterface.mk)
  trivial

theorem migration_receipt_is_private : True := by
  fail_if_success (have _ := SeasonMigrationReceiptInterface.mk)
  trivial

theorem unchecked_receipt_admission_is_private : True := by
  fail_if_success (have _ := acceptCraftGear)
  fail_if_success (have _ := acceptHolderFlair)
  trivial

theorem unchecked_migration_core_is_private : True := by
  fail_if_success (have _ := migrationCore)
  trivial

theorem unchecked_event_batch_fold_is_private : True := by
  fail_if_success (have _ := planIndexedEvents)
  trivial

theorem fixture_authority_is_private : True := by
  fail_if_success (have _ := fixtureConfig)
  fail_if_success (have _ := fixtureGearReceipt)
  fail_if_success (have _ := fixtureMigrationReceipt)
  trivial

#assert_axioms activated_config_constructor_is_private
#assert_axioms projection_state_constructor_is_private
#assert_axioms attendant_inclusion_receipt_is_private
#assert_axioms shipworks_owner_binding_receipt_is_private
#assert_axioms shipworks_failure_owner_binding_receipt_is_private
#assert_axioms craft_gear_receipt_is_private
#assert_axioms gallery_receipt_is_private
#assert_axioms holder_cosmetic_receipt_is_private
#assert_axioms migration_receipt_is_private
#assert_axioms unchecked_receipt_admission_is_private
#assert_axioms unchecked_migration_core_is_private
#assert_axioms unchecked_event_batch_fold_is_private
#assert_axioms fixture_authority_is_private

end Dregg2.Games.PathOfAngels.ShipLifeProgressionBoundary
