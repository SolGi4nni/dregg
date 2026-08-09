/-
# Station Daily Runtime — the wire-fixture EVALUATION, out of the crypto archive's build

`StationDailyRuntime.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build
root; `dregg_poa_station_daily_read` is exported from it), and until 2026-08-08 its gate,
round-trip and hostile-wire fixtures ran sixteen `native_decide` pins at elaboration — so
any game-fixture regression was a hard failure of every Rust proving target in the
workspace.  The STATEMENTS remain in `StationDailyRuntime.lean` as evaluation-free
`check_* : Bool` definitions; THIS module is where they are RUN.  It is rooted in the
`PathOfAngelsGuards` library and reachable from `Dregg2.FFI` by NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged.  `StationDailyRuntime` keeps no `native_decide`
residue of its own — its panel proof is `StationCrateOpen.panel_valid`, cited by name.
-/
import Dregg2.Games.PathOfAngels.StationDailyRuntime

namespace Dregg2.Games.PathOfAngels.StationDailyRuntime

set_option autoImplicit false

theorem the_authored_table_moves_only_supplies :
    check_the_authored_table_moves_only_supplies = true := by native_decide

theorem the_served_ship_moves_when_the_log_records_an_opening :
    check_the_served_ship_moves_when_the_log_records_an_opening = true := by native_decide

theorem the_two_logs_serve_different_documents :
    check_the_two_logs_serve_different_documents = true := by native_decide

theorem a_log_row_from_another_period_is_refused :
    check_a_log_row_from_another_period_is_refused = true := by native_decide

theorem anonymous_request_round_trips :
    check_anonymous_request_round_trips = true := by native_decide

theorem officer_request_round_trips :
    check_officer_request_round_trips = true := by native_decide

theorem both_requests_are_served :
    check_both_requests_are_served = true := by native_decide

theorem the_officer_is_eligible_and_draws_every_authored_period :
    check_the_officer_is_eligible_and_draws_every_authored_period = true := by native_decide

theorem hostile_unknown_field_refuses :
    check_hostile_unknown_field_refuses = true := by native_decide

theorem hostile_transposed_keys_refuse :
    check_hostile_transposed_keys_refuse = true := by native_decide

theorem hostile_wrong_format_refuses :
    check_hostile_wrong_format_refuses = true := by native_decide

theorem hostile_boolean_crew_refuses :
    check_hostile_boolean_crew_refuses = true := by native_decide

theorem hostile_short_digest_refuses :
    check_hostile_short_digest_refuses = true := by native_decide

theorem hostile_trailing_byte_refuses :
    check_hostile_trailing_byte_refuses = true := by native_decide

theorem the_pre_history_request_shape_refuses :
    check_the_pre_history_request_shape_refuses = true := by native_decide

theorem hostile_row_with_a_counter_refuses :
    check_hostile_row_with_a_counter_refuses = true := by native_decide

#assert_compiled the_authored_table_moves_only_supplies
#assert_compiled the_served_ship_moves_when_the_log_records_an_opening
#assert_compiled the_two_logs_serve_different_documents
#assert_compiled a_log_row_from_another_period_is_refused
#assert_compiled anonymous_request_round_trips
#assert_compiled officer_request_round_trips
#assert_compiled both_requests_are_served
#assert_compiled the_officer_is_eligible_and_draws_every_authored_period
#assert_compiled hostile_unknown_field_refuses
#assert_compiled hostile_transposed_keys_refuse
#assert_compiled hostile_wrong_format_refuses
#assert_compiled hostile_boolean_crew_refuses
#assert_compiled hostile_short_digest_refuses
#assert_compiled hostile_trailing_byte_refuses
#assert_compiled the_pre_history_request_shape_refuses
#assert_compiled hostile_row_with_a_counter_refuses

end Dregg2.Games.PathOfAngels.StationDailyRuntime
