/-
# Signal authority-head genesis — the fixture-pin EVALUATION, out of the crypto archive's build

`NetworkGenesis.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build root),
and until 2026-08-08 its thirty-five fixture pins ran `native_decide` at elaboration — the
live epoch-1 deployment byte pins plus the hostile ceremony fixtures — so any genesis
fixture regression (and this module's deployment constants are exactly what a re-genesis
staleifies) was a hard failure of every Rust proving target in the workspace. The pins'
STATEMENTS remain in `NetworkGenesis.lean` as evaluation-free `check_* : Bool`
definitions; THIS module is where they are RUN. It is rooted in the `PathOfAngelsGuards`
library and reachable from `Dregg2.FFI` by NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged.

Named residue in the parent: NONE — no construction there demands a proof as data.
-/
import Dregg2.Games.PathOfAngels.NetworkGenesis

namespace Dregg2.Games.PathOfAngels.NetworkGenesis

set_option autoImplicit false

theorem fixture_deployment_id_rederived :
    check_fixture_deployment_id_rederived = true := by native_decide

theorem fixture_input_roundtrip :
    check_fixture_input_roundtrip = true := by native_decide

theorem fixture_checks_accept :
    check_fixture_checks_accept = true := by native_decide

theorem fixture_config_sha256_external_pin :
    check_fixture_config_sha256_external_pin = true := by native_decide

theorem fixture_canon_sha256_external_pin :
    check_fixture_canon_sha256_external_pin = true := by native_decide

theorem fixture_authorizes :
    check_fixture_authorizes = true := by native_decide

theorem fixture_authorized_hashes :
    check_fixture_authorized_hashes = true := by native_decide

theorem fixture_processes :
    check_fixture_processes = true := by native_decide

theorem fixture_ffi_nonempty :
    check_fixture_ffi_nonempty = true := by native_decide

theorem fixture_output_is_semantically_validated :
    check_fixture_output_is_semantically_validated = true := by native_decide

theorem fixture_tampered_output_is_syntax_only :
    check_fixture_tampered_output_is_syntax_only = true := by native_decide

theorem caller_chosen_reward_refused :
    check_caller_chosen_reward_refused = true := by native_decide

theorem inconsistent_content_session_refused :
    check_inconsistent_content_session_refused = true := by native_decide

theorem inconsistent_federation_refused :
    check_inconsistent_federation_refused = true := by native_decide

theorem substituted_deployment_id_refused :
    check_substituted_deployment_id_refused = true := by native_decide

theorem substituted_deployment_digest_refused :
    check_substituted_deployment_digest_refused = true := by native_decide

theorem substituted_deployment_manifest_refused :
    check_substituted_deployment_manifest_refused = true := by native_decide

theorem substituted_deployment_policy_refused :
    check_substituted_deployment_policy_refused = true := by native_decide

theorem substituted_genesis_sha_refused :
    check_substituted_genesis_sha_refused = true := by native_decide

theorem inconsistent_epoch_refused :
    check_inconsistent_epoch_refused = true := by native_decide

theorem inconsistent_content_root_refused :
    check_inconsistent_content_root_refused = true := by native_decide

theorem inconsistent_activation_refused :
    check_inconsistent_activation_refused = true := by native_decide

theorem zero_activation_counter_refused :
    check_zero_activation_counter_refused = true := by native_decide

theorem terminal_activation_counter_refused :
    check_terminal_activation_counter_refused = true := by native_decide

theorem nonzero_genesis_world_refused :
    check_nonzero_genesis_world_refused = true := by native_decide

theorem nonzero_genesis_sequence_refused :
    check_nonzero_genesis_sequence_refused = true := by native_decide

theorem nonzero_genesis_revision_refused :
    check_nonzero_genesis_revision_refused = true := by native_decide

theorem nonzero_genesis_curator_counter_refused :
    check_nonzero_genesis_curator_counter_refused = true := by native_decide

theorem nonzero_genesis_transition_refused :
    check_nonzero_genesis_transition_refused = true := by native_decide

theorem nonzero_genesis_last_digest_refused :
    check_nonzero_genesis_last_digest_refused = true := by native_decide

theorem nonempty_player_counter_refused :
    check_nonempty_player_counter_refused = true := by native_decide

theorem duplicate_player_counter_refused_by_syntax :
    check_duplicate_player_counter_refused_by_syntax = true := by native_decide

theorem trailing_bytes_refused :
    check_trailing_bytes_refused = true := by native_decide

theorem uppercase_digest_refused :
    check_uppercase_digest_refused = true := by native_decide

theorem unknown_top_level_field_refused :
    check_unknown_top_level_field_refused = true := by native_decide

#assert_compiled fixture_deployment_id_rederived
#assert_compiled fixture_input_roundtrip
#assert_compiled fixture_checks_accept
#assert_compiled fixture_config_sha256_external_pin
#assert_compiled fixture_canon_sha256_external_pin
#assert_compiled fixture_authorizes
#assert_compiled fixture_authorized_hashes
#assert_compiled fixture_processes
#assert_compiled fixture_ffi_nonempty
#assert_compiled fixture_output_is_semantically_validated
#assert_compiled fixture_tampered_output_is_syntax_only
#assert_compiled caller_chosen_reward_refused
#assert_compiled inconsistent_content_session_refused
#assert_compiled inconsistent_federation_refused
#assert_compiled substituted_deployment_id_refused
#assert_compiled substituted_deployment_digest_refused
#assert_compiled substituted_deployment_manifest_refused
#assert_compiled substituted_deployment_policy_refused
#assert_compiled substituted_genesis_sha_refused
#assert_compiled inconsistent_epoch_refused
#assert_compiled inconsistent_content_root_refused
#assert_compiled inconsistent_activation_refused
#assert_compiled zero_activation_counter_refused
#assert_compiled terminal_activation_counter_refused
#assert_compiled nonzero_genesis_world_refused
#assert_compiled nonzero_genesis_sequence_refused
#assert_compiled nonzero_genesis_revision_refused
#assert_compiled nonzero_genesis_curator_counter_refused
#assert_compiled nonzero_genesis_transition_refused
#assert_compiled nonzero_genesis_last_digest_refused
#assert_compiled nonempty_player_counter_refused
#assert_compiled duplicate_player_counter_refused_by_syntax
#assert_compiled trailing_bytes_refused
#assert_compiled uppercase_digest_refused
#assert_compiled unknown_top_level_field_refused

end Dregg2.Games.PathOfAngels.NetworkGenesis
