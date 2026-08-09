/-
# EventBatchRuntime — the teeth EVALUATION, out of the crypto archive's build

`EventBatchRuntime.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build
root), and until 2026-08-08 its multi-stream fixture and hostile teeth ran twenty
`native_decide` pins at elaboration — so any game-fixture regression was a hard failure
of every Rust proving target in the workspace. The teeth's STATEMENTS remain in
`EventBatchRuntime.lean` as evaluation-free `check_* : Bool` definitions, beside the
private fixture material and the `@[export]` FFI surface they exercise; THIS module is
where they are RUN. It is rooted in the `PathOfAngelsGuards` library and reachable from
`Dregg2.FFI` by NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged. The fail-closed convention transfers: a check whose
prerequisite plan refuses answers `false`, so a broken prerequisite reds THIS module.
Named residue: none.
-/
import Dregg2.Games.PathOfAngels.EventBatchRuntime

namespace Dregg2.Games.PathOfAngels.EventBatchRuntime

set_option autoImplicit false

theorem fixture_canonical_decode_accepts :
    check_fixture_canonical_decode_accepts = true := by native_decide

theorem fixture_multi_stream_repeated_stream_plans :
    check_fixture_multi_stream_repeated_stream_plans = true := by native_decide

theorem fixture_repeated_stream_uses_prior_successor_storage_digest :
    check_fixture_repeated_stream_uses_prior_successor_storage_digest = true := by
  native_decide

theorem fixture_ffi_emits_nonempty_canonical_plan :
    check_fixture_ffi_emits_nonempty_canonical_plan = true := by native_decide

theorem fixture_initial_heads_digest_export_is_exact :
    check_fixture_initial_heads_digest_export_is_exact = true := by native_decide

theorem hostile_initial_heads_digest_cross_world_refused :
    check_hostile_initial_heads_digest_cross_world_refused = true := by native_decide

theorem hostile_initial_heads_digest_zero_world_refused :
    check_hostile_initial_heads_digest_zero_world_refused = true := by native_decide

theorem hostile_reorder_refused :
    check_hostile_reorder_refused = true := by native_decide

theorem hostile_payload_mutation_refused :
    check_hostile_payload_mutation_refused = true := by native_decide

theorem hostile_projection_mutation_refused :
    check_hostile_projection_mutation_refused = true := by native_decide

theorem hostile_cross_world_refused :
    check_hostile_cross_world_refused = true := by native_decide

theorem hostile_cross_actor_refused :
    check_hostile_cross_actor_refused = true := by native_decide

theorem hostile_authority_actor_binding_refused :
    check_hostile_authority_actor_binding_refused = true := by native_decide

theorem hostile_noncanonical_trailing_byte_refused :
    check_hostile_noncanonical_trailing_byte_refused = true := by native_decide

theorem hostile_unknown_field_refused :
    check_hostile_unknown_field_refused = true := by native_decide

theorem hostile_empty_batch_refused :
    check_hostile_empty_batch_refused = true := by native_decide

theorem hostile_event_count_refused :
    check_hostile_event_count_refused = true := by native_decide

theorem hostile_wire_size_refused :
    check_hostile_wire_size_refused = true := by native_decide

theorem hostile_u64_overflow_refused :
    check_hostile_u64_overflow_refused = true := by native_decide

theorem hostile_sequence_overflow_refused :
    check_hostile_sequence_overflow_refused = true := by native_decide

#assert_compiled fixture_canonical_decode_accepts
#assert_compiled fixture_multi_stream_repeated_stream_plans
#assert_compiled fixture_repeated_stream_uses_prior_successor_storage_digest
#assert_compiled fixture_ffi_emits_nonempty_canonical_plan
#assert_compiled fixture_initial_heads_digest_export_is_exact
#assert_compiled hostile_initial_heads_digest_cross_world_refused
#assert_compiled hostile_initial_heads_digest_zero_world_refused
#assert_compiled hostile_reorder_refused
#assert_compiled hostile_payload_mutation_refused
#assert_compiled hostile_projection_mutation_refused
#assert_compiled hostile_cross_world_refused
#assert_compiled hostile_cross_actor_refused
#assert_compiled hostile_authority_actor_binding_refused
#assert_compiled hostile_noncanonical_trailing_byte_refused
#assert_compiled hostile_unknown_field_refused
#assert_compiled hostile_empty_batch_refused
#assert_compiled hostile_event_count_refused
#assert_compiled hostile_wire_size_refused
#assert_compiled hostile_u64_overflow_refused
#assert_compiled hostile_sequence_overflow_refused

end Dregg2.Games.PathOfAngels.EventBatchRuntime
