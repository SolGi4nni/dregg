/-
# Signal feedback runtime — the fixture-pin EVALUATION, out of the crypto archive's build

`SignalFeedbackRuntime.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build
root), and until 2026-08-08 its twenty fixture pins ran `native_decide` at elaboration —
each one through the Poseidon2 sponge behind the derivation — so any feedback-fixture
regression was a hard failure of every Rust proving target in the workspace (the
compilation-unit coupling the stale-fixture outage measured). The pins' STATEMENTS remain
in `SignalFeedbackRuntime.lean` as evaluation-free `check_* : Bool` definitions; THIS
module is where they are RUN. It is rooted in the `PathOfAngelsGuards` library and
reachable from `Dregg2.FFI` by NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged.

Named residue in the parent: NONE — no construction there demands a proof as data.
-/
import Dregg2.Games.PathOfAngels.SignalFeedbackRuntime

namespace Dregg2.Games.PathOfAngels.SignalFeedbackRuntime

set_option autoImplicit false

theorem fixtureCommitment_is_the_derived_commitment :
    check_fixtureCommitment_is_the_derived_commitment = true := by native_decide

theorem fixtureTarget_is_the_drawn_instance :
    check_fixtureTarget_is_the_drawn_instance = true := by native_decide

theorem fixture_request_roundtrips :
    check_fixture_request_roundtrips = true := by native_decide

theorem fixture_export_answers :
    check_fixture_export_answers = true := by native_decide

theorem fixture_export_is_not_the_refusal :
    check_fixture_export_is_not_the_refusal = true := by native_decide

theorem fixture_reply_is_canonical_and_states_the_format :
    check_fixture_reply_is_canonical_and_states_the_format = true := by native_decide

theorem fixture_reply_does_not_carry_the_secret :
    check_fixture_reply_does_not_carry_the_secret = true := by native_decide

theorem fixture_reply_does_not_carry_the_run_seed :
    check_fixture_reply_does_not_carry_the_run_seed = true := by native_decide

theorem fixture_reply_does_not_carry_the_commitment :
    check_fixture_reply_does_not_carry_the_commitment = true := by native_decide

theorem fixture_reply_does_not_carry_the_target :
    check_fixture_reply_does_not_carry_the_target = true := by native_decide

theorem fixture_two_guesses_are_classified_differently :
    check_fixture_two_guesses_are_classified_differently = true := by native_decide

theorem fixture_the_target_locks_all_three :
    check_fixture_the_target_locks_all_three = true := by native_decide

theorem fixture_another_player_draws_another_instance :
    check_fixture_another_player_draws_another_instance = true := by native_decide

theorem fixture_unopened_commitment_refused :
    check_fixture_unopened_commitment_refused = true := by native_decide

theorem fixture_trailing_byte_refused :
    check_fixture_trailing_byte_refused = true := by native_decide

theorem fixture_unknown_field_refused :
    check_fixture_unknown_field_refused = true := by native_decide

theorem fixture_uppercase_digest_refused :
    check_fixture_uppercase_digest_refused = true := by native_decide

theorem fixture_wrong_format_refused :
    check_fixture_wrong_format_refused = true := by native_decide

theorem fixture_out_of_range_band_refused :
    check_fixture_out_of_range_band_refused = true := by native_decide

theorem fixture_transposed_keys_refused :
    check_fixture_transposed_keys_refused = true := by native_decide

#assert_compiled fixtureCommitment_is_the_derived_commitment
#assert_compiled fixtureTarget_is_the_drawn_instance
#assert_compiled fixture_request_roundtrips
#assert_compiled fixture_export_answers
#assert_compiled fixture_export_is_not_the_refusal
#assert_compiled fixture_reply_is_canonical_and_states_the_format
#assert_compiled fixture_reply_does_not_carry_the_secret
#assert_compiled fixture_reply_does_not_carry_the_run_seed
#assert_compiled fixture_reply_does_not_carry_the_commitment
#assert_compiled fixture_reply_does_not_carry_the_target
#assert_compiled fixture_two_guesses_are_classified_differently
#assert_compiled fixture_the_target_locks_all_three
#assert_compiled fixture_another_player_draws_another_instance
#assert_compiled fixture_unopened_commitment_refused
#assert_compiled fixture_trailing_byte_refused
#assert_compiled fixture_unknown_field_refused
#assert_compiled fixture_uppercase_digest_refused
#assert_compiled fixture_wrong_format_refused
#assert_compiled fixture_out_of_range_band_refused
#assert_compiled fixture_transposed_keys_refused

end Dregg2.Games.PathOfAngels.SignalFeedbackRuntime
