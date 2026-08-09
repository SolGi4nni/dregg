/-
# EventSourcing — the adversarial-teeth EVALUATION, out of the crypto archive's build

`EventSourcing.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build root), and
until 2026-08-08 its adversarial teeth ran eight `native_decide` pins at elaboration — so any
game-fixture regression was a hard failure of every Rust proving target in the workspace.
The teeth's STATEMENTS remain in `EventSourcing.lean` as evaluation-free `check_* : Bool`
definitions, beside the private fixtures they must see; THIS module is where they are RUN.
It is rooted in the `PathOfAngelsGuards` library and reachable from `Dregg2.FFI` by
NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged. The hostile checks pin the EXACT refusal error, which
subsumes the old `fail_if_success` "not accepted" harness. Named residue: none.
-/
import Dregg2.Games.PathOfAngels.EventSourcing

namespace Dregg2.Games.PathOfAngels.EventSourcing

set_option autoImplicit false

theorem fixture_dense_rebuild :
    check_fixture_dense_rebuild = true := by native_decide

theorem hostile_gap_refused :
    check_hostile_gap_refused = true := by native_decide

theorem hostile_reorder_refused :
    check_hostile_reorder_refused = true := by native_decide

theorem hostile_wrong_aggregate_refused :
    check_hostile_wrong_aggregate_refused = true := by native_decide

theorem hostile_wrong_version_refused :
    check_hostile_wrong_version_refused = true := by native_decide

theorem hostile_wrong_predecessor_refused :
    check_hostile_wrong_predecessor_refused = true := by native_decide

theorem hostile_wrong_aggregate_snapshot_empty_suffix_refused :
    check_hostile_wrong_aggregate_snapshot_empty_suffix_refused = true := by native_decide

theorem hostile_wrong_version_snapshot_empty_suffix_refused :
    check_hostile_wrong_version_snapshot_empty_suffix_refused = true := by native_decide

#assert_compiled fixture_dense_rebuild
#assert_compiled hostile_gap_refused
#assert_compiled hostile_reorder_refused
#assert_compiled hostile_wrong_aggregate_refused
#assert_compiled hostile_wrong_version_refused
#assert_compiled hostile_wrong_predecessor_refused
#assert_compiled hostile_wrong_aggregate_snapshot_empty_suffix_refused
#assert_compiled hostile_wrong_version_snapshot_empty_suffix_refused

end Dregg2.Games.PathOfAngels.EventSourcing
