/-
# Artificer Logic — the measured-design EVALUATION, out of the crypto archive's build

`ArtificerLogic.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build root), and
until 2026-08-08 its measured design properties ran twenty-five `native_decide` evaluations at
elaboration — including the full 1197-state × 24-action parametric closure — so any
game-fixture regression was a hard failure of every Rust proving target in the workspace (the
compilation-unit coupling the stale-fixture outage measured). The properties' STATEMENTS
remain in `ArtificerLogic.lean` as evaluation-free `check_* : Bool` definitions over
`stepR`/`certainWithin`/`rowFor` — the same functions the emitter tabulates and the judge
runs; THIS module is where they are RUN. It is rooted in the `PathOfAngelsGuards` library and
reachable from `Dregg2.FFI` by NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged.

Named residue in the parent: NONE — no construction in `ArtificerLogic.lean` consumes a
`native_decide` proof as data, so every pin moved.
-/
import Dregg2.Games.PathOfAngels.ArtificerLogic

namespace Dregg2.Games.PathOfAngels.ArtificerLogic

set_option autoImplicit false

theorem manual_signatures_are_distinct :
    check_manual_signatures_are_distinct = true := by native_decide

theorem repeated_manual_is_caught :
    check_repeated_manual_is_caught = true := by native_decide

theorem four_charges_are_enough :
    check_four_charges_are_enough = true := by native_decide

theorem three_charges_are_not :
    check_three_charges_are_not = true := by native_decide

theorem an_even_split_is_not_a_good_one :
    check_an_even_split_is_not_a_good_one = true := by native_decide

theorem parametric_layers_are_the_clock :
    check_parametric_layers_are_the_clock = true := by native_decide

theorem parametric_closure_is_closed :
    check_parametric_closure_is_closed = true := by native_decide

theorem parametric_states_nodup :
    check_parametric_states_nodup = true := by native_decide

theorem initial_state_is_declared :
    check_initial_state_is_declared = true := by native_decide

theorem no_declared_state_is_empty :
    check_no_declared_state_is_empty = true := by native_decide

theorem resolve_rows_name_two_states :
    check_resolve_rows_name_two_states = true := by native_decide

theorem the_table_consults_the_instance :
    check_the_table_consults_the_instance = true := by native_decide

theorem every_open_probe_resolves :
    check_every_open_probe_resolves = true := by native_decide

theorem every_declared_reason_is_reachable :
    check_every_declared_reason_is_reachable = true := by native_decide

theorem every_rule_is_identifiable :
    check_every_rule_is_identifiable = true := by native_decide

theorem the_run_can_be_lost :
    check_the_run_can_be_lost = true := by native_decide

theorem the_skill_line_is_real :
    check_the_skill_line_is_real = true := by native_decide

theorem rule_tags_are_distinct :
    check_rule_tags_are_distinct = true := by native_decide

theorem action_tags_are_distinct :
    check_action_tags_are_distinct = true := by native_decide

theorem state_ids_are_distinct :
    check_state_ids_are_distinct = true := by native_decide

theorem parametric_shape_is_measured :
    check_parametric_shape_is_measured = true := by native_decide

theorem action_codes_are_distinct :
    check_action_codes_are_distinct = true := by native_decide

#assert_compiled manual_signatures_are_distinct
#assert_compiled repeated_manual_is_caught
#assert_compiled four_charges_are_enough
#assert_compiled three_charges_are_not
#assert_compiled an_even_split_is_not_a_good_one
#assert_compiled parametric_layers_are_the_clock
#assert_compiled parametric_closure_is_closed
#assert_compiled parametric_states_nodup
#assert_compiled initial_state_is_declared
#assert_compiled no_declared_state_is_empty
#assert_compiled resolve_rows_name_two_states
#assert_compiled the_table_consults_the_instance
#assert_compiled every_open_probe_resolves
#assert_compiled every_declared_reason_is_reachable
#assert_compiled every_rule_is_identifiable
#assert_compiled the_run_can_be_lost
#assert_compiled the_skill_line_is_real
#assert_compiled rule_tags_are_distinct
#assert_compiled action_tags_are_distinct
#assert_compiled state_ids_are_distinct
#assert_compiled parametric_shape_is_measured
#assert_compiled action_codes_are_distinct

end Dregg2.Games.PathOfAngels.ArtificerLogic
