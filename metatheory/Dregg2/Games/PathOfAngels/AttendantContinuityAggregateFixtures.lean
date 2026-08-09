/-
# AttendantContinuityAggregate — the suite EVALUATION, out of the crypto archive's build

`AttendantContinuityAggregate.lean` sits in the `Dregg2.FFI` closure (the crypto archive's
build root), and until 2026-08-08 its hostile replay suite ran nineteen `native_decide`
pins at elaboration — so any game-fixture regression was a hard failure of every Rust
proving target in the workspace. The suite's STATEMENTS remain in
`AttendantContinuityAggregate.lean` as evaluation-free `check_* : Bool` definitions,
beside the private mock fixtures they must see; THIS module is where they are RUN. It is
rooted in the `PathOfAngelsGuards` library and reachable from `Dregg2.FFI` by NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged. The hostile checks pin the EXACT refusal error, which
refutes acceptance by construction. Named residue: none.
-/
import Dregg2.Games.PathOfAngels.AttendantContinuityAggregate

namespace Dregg2.Games.PathOfAngels.AttendantContinuityAggregate

set_option autoImplicit false

theorem dense_cross_companion_recovery :
    check_dense_cross_companion_recovery = true := by native_decide

theorem hostile_gap_refused :
    check_hostile_gap_refused = true := by native_decide

theorem hostile_wrong_predecessor_refused :
    check_hostile_wrong_predecessor_refused = true := by native_decide

theorem hostile_payload_substitution_refused :
    check_hostile_payload_substitution_refused = true := by native_decide

theorem hostile_cross_companion_prestate_transplant_refused :
    check_hostile_cross_companion_prestate_transplant_refused = true := by native_decide

theorem hostile_stale_owner_ledger_refused :
    check_hostile_stale_owner_ledger_refused = true := by native_decide

theorem hostile_duplicate_receipt_refused :
    check_hostile_duplicate_receipt_refused = true := by native_decide

theorem hostile_duplicate_settled_credit_refused :
    check_hostile_duplicate_settled_credit_refused = true := by native_decide

theorem hostile_unknown_companion_refused :
    check_hostile_unknown_companion_refused = true := by native_decide

theorem hostile_skipped_local_sequence_refused :
    check_hostile_skipped_local_sequence_refused = true := by native_decide

theorem production_boundary_reused_nullifier_refused :
    check_production_boundary_reused_nullifier_refused = true := by native_decide

theorem production_boundary_same_head_successor_refused :
    check_production_boundary_same_head_successor_refused = true := by native_decide

theorem hostile_reused_global_nullifier_refused :
    check_hostile_reused_global_nullifier_refused = true := by native_decide

theorem hostile_canonical_state_mismatch_refused :
    check_hostile_canonical_state_mismatch_refused = true := by native_decide

theorem hostile_duplicate_row_table_refused :
    check_hostile_duplicate_row_table_refused = true := by native_decide

theorem certified_snapshot_recovery_matches_genesis_replay :
    check_certified_snapshot_recovery_matches_genesis_replay = true := by native_decide

theorem hostile_old_snapshot_empty_suffix_refused :
    check_hostile_old_snapshot_empty_suffix_refused = true := by native_decide

theorem hostile_reset_spend_and_receipt_sets_snapshot_refused :
    check_hostile_reset_spend_and_receipt_sets_snapshot_refused = true := by native_decide

theorem hostile_reset_canonical_cas_snapshot_refused :
    check_hostile_reset_canonical_cas_snapshot_refused = true := by native_decide

#assert_compiled dense_cross_companion_recovery
#assert_compiled hostile_gap_refused
#assert_compiled hostile_wrong_predecessor_refused
#assert_compiled hostile_payload_substitution_refused
#assert_compiled hostile_cross_companion_prestate_transplant_refused
#assert_compiled hostile_stale_owner_ledger_refused
#assert_compiled hostile_duplicate_receipt_refused
#assert_compiled hostile_duplicate_settled_credit_refused
#assert_compiled hostile_unknown_companion_refused
#assert_compiled hostile_skipped_local_sequence_refused
#assert_compiled production_boundary_reused_nullifier_refused
#assert_compiled production_boundary_same_head_successor_refused
#assert_compiled hostile_reused_global_nullifier_refused
#assert_compiled hostile_canonical_state_mismatch_refused
#assert_compiled hostile_duplicate_row_table_refused
#assert_compiled certified_snapshot_recovery_matches_genesis_replay
#assert_compiled hostile_old_snapshot_empty_suffix_refused
#assert_compiled hostile_reset_spend_and_receipt_sets_snapshot_refused
#assert_compiled hostile_reset_canonical_cas_snapshot_refused

end Dregg2.Games.PathOfAngels.AttendantContinuityAggregate
