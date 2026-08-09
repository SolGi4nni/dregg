/-
# Galley maintenance daily runtime — the fixture EVALUATION, out of the crypto archive's build

`GalleyMaintenanceDailyRuntime.lean` sits in the `Dregg2.FFI` closure (the crypto archive's
build root), and until 2026-08-08 its adversarial/end-to-end fixture block ran seventeen
`native_decide` pins at elaboration — so any fixture regression was a hard failure of every Rust
proving target in the workspace (the compilation-unit coupling the stale-fixture outage
measured). The fixtures' STATEMENTS remain in `GalleyMaintenanceDailyRuntime.lean` as
evaluation-free `check_* : Bool` definitions, beside the private policy/viewer/carrier/authority
they exercise (which `GalleyMaintenanceDailyRuntimeBoundary.adversarial_fixtures_are_private`
requires stay private); THIS module is where they are RUN. It is rooted in the
`PathOfAngelsGuards` library and reachable from `Dregg2.FFI` by NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged. The fail-closed convention transfers: a check whose judge
call refuses answers `false`, so a broken prerequisite reds THIS module.

⚠ Named residue: NONE. `fixture_sponsor_wire_refuses_valid_caller_json` stayed behind as a
theorem in the parent because it is `rfl` (the sponsor wire is unconditionally the empty
string), not an evaluation, and its `#assert_axioms` census line stayed with it.
-/
import Dregg2.Games.PathOfAngels.GalleyMaintenanceDailyRuntime

namespace Dregg2.Games.PathOfAngels.GalleyMaintenanceDailyRuntime

set_option autoImplicit false

theorem fixture_policy_valid :
    check_fixture_policy_valid = true := by native_decide

theorem fixture_input_roundtrip :
    check_fixture_input_roundtrip = true := by native_decide

theorem fixture_public_view_accepted :
    check_fixture_public_view_accepted = true := by native_decide

theorem fixture_public_command_accepted :
    check_fixture_public_command_accepted = true := by native_decide

theorem fixture_public_output_redecodes :
    check_fixture_public_output_redecodes = true := by native_decide

theorem fixture_replay_successor_accepted :
    check_fixture_replay_successor_accepted = true := by native_decide

theorem fixture_beta_sponsor_accepted_without_advantage :
    check_fixture_beta_sponsor_accepted_without_advantage = true := by native_decide

theorem fixture_beta_seal_roundtrip :
    check_fixture_beta_seal_roundtrip = true := by native_decide

theorem fixture_internal_sponsor_view_authors_token :
    check_fixture_internal_sponsor_view_authors_token = true := by native_decide

theorem fixture_sponsor_wire_output_never_decodes :
    check_fixture_sponsor_wire_output_never_decodes = true := by native_decide

theorem hostile_wrong_version_refused :
    check_hostile_wrong_version_refused = true := by native_decide

theorem hostile_wrong_payload_digest_refused :
    check_hostile_wrong_payload_digest_refused = true := by native_decide

theorem hostile_stale_projection_refused :
    check_hostile_stale_projection_refused = true := by native_decide

theorem hostile_forged_sponsor_without_authority_refused :
    check_hostile_forged_sponsor_without_authority_refused = true := by native_decide

theorem hostile_trailing_byte_refused :
    check_hostile_trailing_byte_refused = true := by native_decide

theorem hostile_unknown_field_refused :
    check_hostile_unknown_field_refused = true := by native_decide

theorem hostile_tiny_byte_limit_refused :
    check_hostile_tiny_byte_limit_refused = true := by native_decide

#assert_compiled fixture_policy_valid
#assert_compiled fixture_input_roundtrip
#assert_compiled fixture_public_view_accepted
#assert_compiled fixture_public_command_accepted
#assert_compiled fixture_public_output_redecodes
#assert_compiled fixture_replay_successor_accepted
#assert_compiled fixture_beta_sponsor_accepted_without_advantage
#assert_compiled fixture_beta_seal_roundtrip
#assert_compiled fixture_internal_sponsor_view_authors_token
#assert_compiled fixture_sponsor_wire_output_never_decodes
#assert_compiled hostile_wrong_version_refused
#assert_compiled hostile_wrong_payload_digest_refused
#assert_compiled hostile_stale_projection_refused
#assert_compiled hostile_forged_sponsor_without_authority_refused
#assert_compiled hostile_trailing_byte_refused
#assert_compiled hostile_unknown_field_refused
#assert_compiled hostile_tiny_byte_limit_refused

end Dregg2.Games.PathOfAngels.GalleyMaintenanceDailyRuntime
