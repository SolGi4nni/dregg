/-
# FinalizedRunEventAggregate — the fixture EVALUATION, out of the crypto archive's build

`FinalizedRunEventAggregate.lean` sits in the `Dregg2.FFI` closure (the crypto archive's
build root), and until 2026-08-08 its fixture ran seven `native_decide` pins at
elaboration — so any game-fixture regression was a hard failure of every Rust proving
target in the workspace. The fixture's STATEMENTS remain in
`FinalizedRunEventAggregate.lean` as evaluation-free `check_* : Bool` definitions, beside
the private fixture material they must see; THIS module is where they are RUN. It is
rooted in the `PathOfAngelsGuards` library and reachable from `Dregg2.FFI` by NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged. The fail-closed convention transfers: a check whose
prerequisite probe refuses answers `false`, so a broken prerequisite reds THIS module.
Named residue: none.
-/
import Dregg2.Games.PathOfAngels.FinalizedRunEventAggregate

namespace Dregg2.Games.PathOfAngels.FinalizedRunEventAggregate

set_option autoImplicit false

theorem fixture_native_judge_event_populates_every_projection :
    check_fixture_native_judge_event_populates_every_projection = true := by native_decide

theorem hostile_non_lean_output_refused :
    check_hostile_non_lean_output_refused = true := by native_decide

theorem hostile_finalized_signer_substitution_refused :
    check_hostile_finalized_signer_substitution_refused = true := by native_decide

theorem hostile_unversioned_second_carrier_event_refused :
    check_hostile_unversioned_second_carrier_event_refused = true := by native_decide

theorem hostile_wrong_stream_predecessor_refused :
    check_hostile_wrong_stream_predecessor_refused = true := by native_decide

theorem hostile_wrong_payload_digest_refused :
    check_hostile_wrong_payload_digest_refused = true := by native_decide

theorem hostile_same_finalized_run_at_fresh_sequence_refused :
    check_hostile_same_finalized_run_at_fresh_sequence_refused = true := by native_decide

#assert_compiled fixture_native_judge_event_populates_every_projection
#assert_compiled hostile_non_lean_output_refused
#assert_compiled hostile_finalized_signer_substitution_refused
#assert_compiled hostile_unversioned_second_carrier_event_refused
#assert_compiled hostile_wrong_stream_predecessor_refused
#assert_compiled hostile_wrong_payload_digest_refused
#assert_compiled hostile_same_finalized_run_at_fresh_sequence_refused

end Dregg2.Games.PathOfAngels.FinalizedRunEventAggregate
