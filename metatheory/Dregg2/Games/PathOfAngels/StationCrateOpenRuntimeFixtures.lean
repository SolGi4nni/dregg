/-
# Station Crate Open Runtime — the wire-fixture EVALUATION, out of the crypto archive's build

`StationCrateOpenRuntime.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build
root; `dregg_poa_crate_open` is exported from it), and until 2026-08-08 its poles, loop and
hostile-wire fixtures ran twenty-two `native_decide` pins at elaboration — so any
game-fixture regression was a hard failure of every Rust proving target in the workspace.
The STATEMENTS remain in `StationCrateOpenRuntime.lean` as evaluation-free `check_* : Bool`
definitions; THIS module is where they are RUN.  It is rooted in the `PathOfAngelsGuards`
library and reachable from `Dregg2.FFI` by NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged.  `StationCrateOpenRuntime` keeps no `native_decide`
residue of its own — its deployment is `StationCrateOpen`'s `crate`/`panel`, cited by name.
-/
import Dregg2.Games.PathOfAngels.StationCrateOpenRuntime

namespace Dregg2.Games.PathOfAngels.StationCrateOpenRuntime

set_option autoImplicit false

theorem the_logged_open_really_consumed_the_installed_period :
    check_the_logged_open_really_consumed_the_installed_period = true := by native_decide

theorem an_honest_crate_open_publishes_the_moved_ship :
    check_an_honest_crate_open_publishes_the_moved_ship = true := by native_decide

theorem a_second_open_of_the_installed_period_is_refused :
    check_a_second_open_of_the_installed_period_is_refused = true := by native_decide

theorem the_replay_guard_is_exactly_as_strong_as_the_node_log :
    check_the_replay_guard_is_exactly_as_strong_as_the_node_log = true := by native_decide

theorem the_station_read_serves_the_ship_this_write_published :
    check_the_station_read_serves_the_ship_this_write_published = true := by native_decide

theorem neither_side_of_the_loop_is_a_refusal :
    check_neither_side_of_the_loop_is_a_refusal = true := by native_decide

theorem an_ordinary_open_publishes_an_unmoved_ship :
    check_an_ordinary_open_publishes_an_unmoved_ship = true := by native_decide

theorem an_ineligible_crew_key_is_refused :
    check_an_ineligible_crew_key_is_refused = true := by native_decide

theorem a_log_row_from_another_period_refuses :
    check_a_log_row_from_another_period_refuses = true := by native_decide

theorem a_log_row_naming_a_stowaway_refuses :
    check_a_log_row_naming_a_stowaway_refuses = true := by native_decide

theorem the_published_ship_accumulates_the_whole_crew :
    check_the_published_ship_accumulates_the_whole_crew = true := by native_decide

theorem first_open_request_round_trips :
    check_first_open_request_round_trips = true := by native_decide

theorem second_open_request_round_trips :
    check_second_open_request_round_trips = true := by native_decide

theorem the_export_emits_a_move_and_a_refusal :
    check_the_export_emits_a_move_and_a_refusal = true := by native_decide

theorem hostile_unknown_field_refuses :
    check_hostile_unknown_field_refuses = true := by native_decide

theorem hostile_transposed_keys_refuse :
    check_hostile_transposed_keys_refuse = true := by native_decide

theorem hostile_wrong_format_refuses :
    check_hostile_wrong_format_refuses = true := by native_decide

theorem hostile_row_with_a_counter_refuses :
    check_hostile_row_with_a_counter_refuses = true := by native_decide

theorem the_uppercase_mutation_is_not_a_no_op :
    check_the_uppercase_mutation_is_not_a_no_op = true := by native_decide

theorem hostile_uppercase_digest_refuses :
    check_hostile_uppercase_digest_refuses = true := by native_decide

theorem hostile_trailing_byte_refuses :
    check_hostile_trailing_byte_refuses = true := by native_decide

theorem hostile_empty_wire_refuses :
    check_hostile_empty_wire_refuses = true := by native_decide

#assert_compiled the_logged_open_really_consumed_the_installed_period
#assert_compiled an_honest_crate_open_publishes_the_moved_ship
#assert_compiled a_second_open_of_the_installed_period_is_refused
#assert_compiled the_replay_guard_is_exactly_as_strong_as_the_node_log
#assert_compiled the_station_read_serves_the_ship_this_write_published
#assert_compiled neither_side_of_the_loop_is_a_refusal
#assert_compiled an_ordinary_open_publishes_an_unmoved_ship
#assert_compiled an_ineligible_crew_key_is_refused
#assert_compiled a_log_row_from_another_period_refuses
#assert_compiled a_log_row_naming_a_stowaway_refuses
#assert_compiled the_published_ship_accumulates_the_whole_crew
#assert_compiled first_open_request_round_trips
#assert_compiled second_open_request_round_trips
#assert_compiled the_export_emits_a_move_and_a_refusal
#assert_compiled hostile_unknown_field_refuses
#assert_compiled hostile_transposed_keys_refuse
#assert_compiled hostile_wrong_format_refuses
#assert_compiled hostile_row_with_a_counter_refuses
#assert_compiled the_uppercase_mutation_is_not_a_no_op
#assert_compiled hostile_uppercase_digest_refuses
#assert_compiled hostile_trailing_byte_refuses
#assert_compiled hostile_empty_wire_refuses

end Dregg2.Games.PathOfAngels.StationCrateOpenRuntime
