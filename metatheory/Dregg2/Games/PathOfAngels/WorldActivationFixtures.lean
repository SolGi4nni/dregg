/-
# WorldActivation — the honest/hostile witness EVALUATION, out of the crypto archive's build

`WorldActivation.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build root), and
until 2026-08-08 its witness section ran twelve `native_decide` pins at elaboration — so any
fixture regression was a hard failure of every Rust proving target in the workspace (the
compilation-unit coupling the stale-fixture outage measured). The witnesses' STATEMENTS remain
in `WorldActivation.lean` as evaluation-free `check_* : Bool` definitions, beside the private
fixture envelopes and lineage they exercise; THIS module is where they are RUN. It is rooted in
the `PathOfAngelsGuards` library and reachable from `Dregg2.FFI` by NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged. The fail-closed convention transfers: a check whose
`Except` lands on any arm but the asserted one answers `false`, so a regression reds THIS
module.

⚠ Named residue: NONE. Nothing in `WorldActivation` demands a proof as data at construction,
so all twelve pins moved.
-/
import Dregg2.Games.PathOfAngels.WorldActivation

namespace Dregg2.Games.PathOfAngels.WorldActivation

set_option autoImplicit false

theorem honest_successor_accepts :
    check_honest_successor_accepts = true := by native_decide

theorem stale_epoch_refused :
    check_stale_epoch_refused = true := by native_decide

theorem counter_skip_refused :
    check_counter_skip_refused = true := by native_decide

theorem wrong_predecessor_refused :
    check_wrong_predecessor_refused = true := by native_decide

theorem unrecorded_rollback_refused :
    check_unrecorded_rollback_refused = true := by native_decide

theorem wrong_curator_key_refused :
    check_wrong_curator_key_refused = true := by native_decide

theorem unverified_native_signature_refused :
    check_unverified_native_signature_refused = true := by native_decide

theorem same_federation_different_content_refused_by_active_world :
    check_same_federation_different_content_refused_by_active_world = true := by native_decide

theorem same_federation_different_session_refused_by_active_world :
    check_same_federation_different_session_refused_by_active_world = true := by native_decide

theorem recorded_rollback_accepts_and_restores_exact_world :
    check_recorded_rollback_accepts_and_restores_exact_world = true := by native_decide

theorem fixture_canonical_input_roundtrips :
    check_fixture_canonical_input_roundtrips = true := by native_decide

theorem exact_world_query_accepts_head_and_refuses_other_content :
    check_exact_world_query_accepts_head_and_refuses_other_content = true := by native_decide

#assert_compiled honest_successor_accepts
#assert_compiled stale_epoch_refused
#assert_compiled counter_skip_refused
#assert_compiled wrong_predecessor_refused
#assert_compiled unrecorded_rollback_refused
#assert_compiled wrong_curator_key_refused
#assert_compiled unverified_native_signature_refused
#assert_compiled same_federation_different_content_refused_by_active_world
#assert_compiled same_federation_different_session_refused_by_active_world
#assert_compiled recorded_rollback_accepts_and_restores_exact_world
#assert_compiled fixture_canonical_input_roundtrips
#assert_compiled exact_world_query_accepts_head_and_refuses_other_content

end Dregg2.Games.PathOfAngels.WorldActivation
