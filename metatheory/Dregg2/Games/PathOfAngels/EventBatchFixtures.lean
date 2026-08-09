/-
# EventBatch — the fixture EVALUATION, out of the crypto archive's build

`EventBatch.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build root), and
until 2026-08-08 its fixtures ran thirteen `native_decide` pins at elaboration — so any
game-fixture regression was a hard failure of every Rust proving target in the workspace.
The fixtures' STATEMENTS remain in `EventBatch.lean` as evaluation-free `check_* : Bool`
definitions, beside the private fixture material they must see; THIS module is where they
are RUN. It is rooted in the `PathOfAngelsGuards` library and reachable from `Dregg2.FFI`
by NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged. The hostile checks pin the EXACT refusal error,
which refutes acceptance by construction. Named residue: none.
-/
import Dregg2.Games.PathOfAngels.EventBatch

namespace Dregg2.Games.PathOfAngels.EventBatch

set_option autoImplicit false

theorem fixture_cross_aggregate_batch_accepts :
    check_fixture_cross_aggregate_batch_accepts = true := by native_decide

theorem fixture_repeated_stream_is_explicitly_chained :
    check_fixture_repeated_stream_is_explicitly_chained = true := by native_decide

theorem fixture_cross_aggregate_successors_are_exact :
    check_fixture_cross_aggregate_successors_are_exact = true := by native_decide

theorem hostile_semantic_reapplication_refused :
    check_hostile_semantic_reapplication_refused = true := by native_decide

theorem hostile_event_gap_refused :
    check_hostile_event_gap_refused = true := by native_decide

theorem hostile_cross_stream_predecessor_refused :
    check_hostile_cross_stream_predecessor_refused = true := by native_decide

theorem hostile_index_reorder_refused :
    check_hostile_index_reorder_refused = true := by native_decide

theorem hostile_batch_digest_refused :
    check_hostile_batch_digest_refused = true := by native_decide

theorem hostile_duplicate_initial_stream_refused :
    check_hostile_duplicate_initial_stream_refused = true := by native_decide

theorem hostile_foreign_federation_refused :
    check_hostile_foreign_federation_refused = true := by native_decide

theorem world_scoped_streams_separate_activation_session_and_epoch :
    check_world_scoped_streams_separate_activation_session_and_epoch = true := by
  native_decide

theorem hostile_reused_stream_after_world_rollback_refused :
    check_hostile_reused_stream_after_world_rollback_refused = true := by native_decide

theorem hostile_zero_world_identity_refused :
    check_hostile_zero_world_identity_refused = true := by native_decide

#assert_compiled fixture_cross_aggregate_batch_accepts
#assert_compiled fixture_repeated_stream_is_explicitly_chained
#assert_compiled fixture_cross_aggregate_successors_are_exact
#assert_compiled hostile_semantic_reapplication_refused
#assert_compiled hostile_event_gap_refused
#assert_compiled hostile_cross_stream_predecessor_refused
#assert_compiled hostile_index_reorder_refused
#assert_compiled hostile_batch_digest_refused
#assert_compiled hostile_duplicate_initial_stream_refused
#assert_compiled hostile_foreign_federation_refused
#assert_compiled world_scoped_streams_separate_activation_session_and_epoch
#assert_compiled hostile_reused_stream_after_world_rollback_refused
#assert_compiled hostile_zero_world_identity_refused

end Dregg2.Games.PathOfAngels.EventBatch
