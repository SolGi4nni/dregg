/-
# AttendantKernel — the hostility-lab EVALUATION, out of the crypto archive's build

`AttendantKernel.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build root),
and until 2026-08-08 its lab ran twenty-eight `native_decide` pins at elaboration — so any
game-fixture regression was a hard failure of every Rust proving target in the workspace.
The lab's STATEMENTS remain in `AttendantKernel.lean` as evaluation-free `check_* : Bool`
definitions, beside the private fixtures they must see; THIS module is where they are RUN.
It is rooted in the `PathOfAngelsGuards` library and reachable from `Dregg2.FFI` by
NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged. The fail-closed convention transfers: a check whose
prerequisite probe refuses answers `false`, so a broken prerequisite reds THIS module.

⚠ Two construction proofs did NOT move (`fixtureSupplyTarget_is_the_drawn_instance`,
`fixtureIntelTarget_is_the_drawn_instance`) — `SignalTriangulation.Config` carries the
drawn-target equation as data, so they must elaborate where the fixture configs are built.
They are the named residue; the lab header in `AttendantKernel.lean` records it.
-/
import Dregg2.Games.PathOfAngels.AttendantKernel

namespace Dregg2.Games.PathOfAngels.Attendant

set_option autoImplicit false

theorem playable_care_training_field_loop :
    check_playable_care_training_field_loop = true := by native_decide

theorem hostile_forged_progression_claim_is_refused :
    check_hostile_forged_progression_claim_is_refused = true := by native_decide

theorem hostile_judged_but_unsettled_credit_is_unavailable :
    check_hostile_judged_but_unsettled_credit_is_unavailable = true := by native_decide

theorem hostile_ledger_reopen_credit_reset_is_refused :
    check_hostile_ledger_reopen_credit_reset_is_refused = true := by native_decide

theorem hostile_owner_global_credit_replay_is_refused :
    check_hostile_owner_global_credit_replay_is_refused = true := by native_decide

theorem hostile_cross_attendant_credit_double_spend_is_refused :
    check_hostile_cross_attendant_credit_double_spend_is_refused = true := by native_decide

theorem hostile_cross_instance_envelope_is_refused :
    check_hostile_cross_instance_envelope_is_refused = true := by native_decide

theorem hostile_projection_transplant_is_refused :
    check_hostile_projection_transplant_is_refused = true := by native_decide

theorem hostile_same_header_different_template_policy_is_refused :
    check_hostile_same_header_different_template_policy_is_refused = true := by native_decide

theorem hostile_inventory_policy_substitution_is_refused :
    check_hostile_inventory_policy_substitution_is_refused = true := by native_decide

theorem hostile_cross_owner_colliding_identity_oracle_is_refused :
    check_hostile_cross_owner_colliding_identity_oracle_is_refused = true := by native_decide

theorem hostile_same_epoch_return_is_refused :
    check_hostile_same_epoch_return_is_refused = true := by native_decide

theorem hostile_wrong_signer_is_refused :
    check_hostile_wrong_signer_is_refused = true := by native_decide

theorem hostile_counter_replay_is_refused :
    check_hostile_counter_replay_is_refused = true := by native_decide

theorem hostile_stale_cas_tooth_refuses_advanced_head :
    check_hostile_stale_cas_tooth_refuses_advanced_head = true := by native_decide

theorem hostile_same_snapshot_fork_is_explicit_and_nullifier_closes_replay :
    check_hostile_same_snapshot_fork_is_explicit_and_nullifier_closes_replay = true := by
  native_decide

theorem hostile_wrong_canonical_settlement_identity_is_refused :
    check_hostile_wrong_canonical_settlement_identity_is_refused = true := by native_decide

theorem hostile_settlement_successor_and_root_substitution_are_refused :
    check_hostile_settlement_successor_and_root_substitution_are_refused = true := by
  native_decide

theorem hostile_command_successor_and_root_substitution_are_refused :
    check_hostile_command_successor_and_root_substitution_are_refused = true := by
  native_decide

theorem hostile_action_substitution_breaks_authenticated_preimage :
    check_hostile_action_substitution_breaks_authenticated_preimage = true := by
  native_decide

theorem hostile_prestate_substitution_breaks_authenticated_preimage :
    check_hostile_prestate_substitution_breaks_authenticated_preimage = true := by
  native_decide

theorem max_counter_refuses_before_valid_epoch :
    check_max_counter_refuses_before_valid_epoch = true := by native_decide

theorem field_work_without_equipment_is_refused :
    check_field_work_without_equipment_is_refused = true := by native_decide

theorem equipment_before_training_is_refused :
    check_equipment_before_training_is_refused = true := by native_decide

theorem declared_but_unowned_equipment_is_refused :
    check_declared_but_unowned_equipment_is_refused = true := by native_decide

theorem skipped_epoch_is_refused :
    check_skipped_epoch_is_refused = true := by native_decide

theorem home_absence_cannot_erase_attachment :
    check_home_absence_cannot_erase_attachment = true := by native_decide

theorem fixture_identity_rejects_serial_substitution :
    check_fixture_identity_rejects_serial_substitution = true := by native_decide

#assert_compiled playable_care_training_field_loop
#assert_compiled hostile_forged_progression_claim_is_refused
#assert_compiled hostile_judged_but_unsettled_credit_is_unavailable
#assert_compiled hostile_ledger_reopen_credit_reset_is_refused
#assert_compiled hostile_owner_global_credit_replay_is_refused
#assert_compiled hostile_cross_attendant_credit_double_spend_is_refused
#assert_compiled hostile_cross_instance_envelope_is_refused
#assert_compiled hostile_projection_transplant_is_refused
#assert_compiled hostile_same_header_different_template_policy_is_refused
#assert_compiled hostile_inventory_policy_substitution_is_refused
#assert_compiled hostile_cross_owner_colliding_identity_oracle_is_refused
#assert_compiled hostile_same_epoch_return_is_refused
#assert_compiled hostile_wrong_signer_is_refused
#assert_compiled hostile_counter_replay_is_refused
#assert_compiled hostile_stale_cas_tooth_refuses_advanced_head
#assert_compiled hostile_same_snapshot_fork_is_explicit_and_nullifier_closes_replay
#assert_compiled hostile_wrong_canonical_settlement_identity_is_refused
#assert_compiled hostile_settlement_successor_and_root_substitution_are_refused
#assert_compiled hostile_command_successor_and_root_substitution_are_refused
#assert_compiled hostile_action_substitution_breaks_authenticated_preimage
#assert_compiled hostile_prestate_substitution_breaks_authenticated_preimage
#assert_compiled max_counter_refuses_before_valid_epoch
#assert_compiled field_work_without_equipment_is_refused
#assert_compiled equipment_before_training_is_refused
#assert_compiled declared_but_unowned_equipment_is_refused
#assert_compiled skipped_epoch_is_refused
#assert_compiled home_absence_cannot_erase_attachment
#assert_compiled fixture_identity_rejects_serial_substitution

end Dregg2.Games.PathOfAngels.Attendant
