/-
# EditorialRegistry — the fixture EVALUATION, out of the crypto archive's build

`EditorialRegistry.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build
root), and until 2026-08-08 its editorial fixture ran sixteen `native_decide` pins at
elaboration — so any game-fixture regression was a hard failure of every Rust proving
target in the workspace. The fixture's STATEMENTS remain in `EditorialRegistry.lean` as
evaluation-free `check_* : Bool` definitions, beside the private machinery they must see;
THIS module is where they are RUN. It is rooted in the `PathOfAngelsGuards` library and
reachable from `Dregg2.FFI` by NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged. The fail-closed convention transfers: a check whose
prerequisite probe refuses answers `false`, so a broken prerequisite reds THIS module.

⚠ Two construction proofs did NOT move (`fixture_provisionalA_exists`,
`fixture_provisionalB_exists`) — `ProvisionalArtifact` has a private proof-carrying
constructor with no fallback inhabitant, so the proofs must elaborate where
`fixtureA`/`fixtureB` are built. They are the named residue; the fixture header in
`EditorialRegistry.lean` records it.
-/
import Dregg2.Games.PathOfAngels.EditorialRegistry

namespace Dregg2.Games.PathOfAngels.EditorialRegistry

set_option autoImplicit false

theorem fixture_provisionals_exist :
    check_fixture_provisionals_exist = true := by native_decide

theorem fixture_policy_valid :
    check_fixture_policy_valid = true := by native_decide

theorem fixture_registry_opens :
    check_fixture_registry_opens = true := by native_decide

theorem fixture_promotion_selects_exact_origin :
    check_fixture_promotion_selects_exact_origin = true := by native_decide

theorem competing_promotion_at_same_revision_is_refused :
    check_competing_promotion_at_same_revision_is_refused = true := by native_decide

theorem same_old_snapshot_prepares_competing_forks :
    check_same_old_snapshot_prepares_competing_forks = true := by native_decide

theorem repeated_genesis_is_refused :
    check_repeated_genesis_is_refused = true := by native_decide

theorem arbitrary_successor_root_is_refused :
    check_arbitrary_successor_root_is_refused = true := by native_decide

theorem stale_supersession_is_refused :
    check_stale_supersession_is_refused = true := by native_decide

theorem exact_supersession_preserves_prior_history :
    check_exact_supersession_preserves_prior_history = true := by native_decide

theorem retraction_keeps_all_prior_history :
    check_retraction_keeps_all_prior_history = true := by native_decide

theorem wrong_content_epoch_is_refused :
    check_wrong_content_epoch_is_refused = true := by native_decide

theorem cross_content_envelope_replay_is_refused :
    check_cross_content_envelope_replay_is_refused = true := by native_decide

theorem alternate_catalogue_and_mission_are_refused :
    check_alternate_catalogue_and_mission_are_refused = true := by native_decide

theorem canonical_head_refuses_alternate_catalogue_policy :
    check_canonical_head_refuses_alternate_catalogue_policy = true := by native_decide

theorem fabricated_unreachable_receipt_is_refused :
    check_fabricated_unreachable_receipt_is_refused = true := by native_decide

#assert_compiled fixture_provisionals_exist
#assert_compiled fixture_policy_valid
#assert_compiled fixture_registry_opens
#assert_compiled fixture_promotion_selects_exact_origin
#assert_compiled competing_promotion_at_same_revision_is_refused
#assert_compiled same_old_snapshot_prepares_competing_forks
#assert_compiled repeated_genesis_is_refused
#assert_compiled arbitrary_successor_root_is_refused
#assert_compiled stale_supersession_is_refused
#assert_compiled exact_supersession_preserves_prior_history
#assert_compiled retraction_keeps_all_prior_history
#assert_compiled wrong_content_epoch_is_refused
#assert_compiled cross_content_envelope_replay_is_refused
#assert_compiled alternate_catalogue_and_mission_are_refused
#assert_compiled canonical_head_refuses_alternate_catalogue_policy
#assert_compiled fabricated_unreachable_receipt_is_refused

end Dregg2.Games.PathOfAngels.EditorialRegistry
