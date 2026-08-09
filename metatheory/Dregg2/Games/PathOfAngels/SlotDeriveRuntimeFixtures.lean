/-
# Slot-derive runtime — the fixture-pin EVALUATION, out of the crypto archive's build

`SlotDeriveRuntime.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build
root), and until 2026-08-08 its thirteen fixture pins ran `native_decide` at elaboration —
each one a Poseidon2 sponge evaluation — so any derivation-fixture regression was a hard
failure of every Rust proving target in the workspace (the compilation-unit coupling the
stale-fixture outage measured). The pins' STATEMENTS remain in `SlotDeriveRuntime.lean` as
evaluation-free `check_* : Bool` definitions; THIS module is where they are RUN. It is
rooted in the `PathOfAngelsGuards` library and reachable from `Dregg2.FFI` by NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged.

Named residue in the parent: NONE — no construction there demands a proof as data.
-/
import Dregg2.Games.PathOfAngels.SlotDeriveRuntime

namespace Dregg2.Games.PathOfAngels.SlotDeriveRuntime

set_option autoImplicit false

theorem fixture_request_roundtrips :
    check_fixture_request_roundtrips = true := by native_decide

theorem fixture_derives :
    check_fixture_derives = true := by native_decide

theorem fixture_export_answers :
    check_fixture_export_answers = true := by native_decide

theorem fixture_export_is_not_the_refusal :
    check_fixture_export_is_not_the_refusal = true := by native_decide

theorem fixture_reply_is_canonical_and_states_the_format :
    check_fixture_reply_is_canonical_and_states_the_format = true := by native_decide

theorem fixture_reply_does_not_carry_the_secret :
    check_fixture_reply_does_not_carry_the_secret = true := by native_decide

theorem fixture_trailing_byte_refused :
    check_fixture_trailing_byte_refused = true := by native_decide

theorem fixture_unknown_field_refused :
    check_fixture_unknown_field_refused = true := by native_decide

theorem fixture_uppercase_digest_refused :
    check_fixture_uppercase_digest_refused = true := by native_decide

theorem fixture_wrong_format_refused :
    check_fixture_wrong_format_refused = true := by native_decide

theorem fixture_transposed_keys_refused :
    check_fixture_transposed_keys_refused = true := by native_decide

theorem fixture_other_secret_draws_another_instance :
    check_fixture_other_secret_draws_another_instance = true := by native_decide

theorem fixture_commitment_is_player_independent_but_the_seed_is_not :
    check_fixture_commitment_is_player_independent_but_the_seed_is_not = true := by
  native_decide

#assert_compiled fixture_request_roundtrips
#assert_compiled fixture_derives
#assert_compiled fixture_export_answers
#assert_compiled fixture_export_is_not_the_refusal
#assert_compiled fixture_reply_is_canonical_and_states_the_format
#assert_compiled fixture_reply_does_not_carry_the_secret
#assert_compiled fixture_trailing_byte_refused
#assert_compiled fixture_unknown_field_refused
#assert_compiled fixture_uppercase_digest_refused
#assert_compiled fixture_wrong_format_refused
#assert_compiled fixture_transposed_keys_refused
#assert_compiled fixture_other_secret_draws_another_instance
#assert_compiled fixture_commitment_is_player_independent_but_the_seed_is_not

end Dregg2.Games.PathOfAngels.SlotDeriveRuntime
