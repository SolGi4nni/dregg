/-
# Deck Descent — the measured-design EVALUATION, out of the crypto archive's build

`DeckDescent.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build root), and
until 2026-08-08 its measured design properties ran twenty-two `native_decide` evaluations at
elaboration — the eight-board family census, the four nine-action lines, and the full
1924-state parametric closure — so any game-fixture regression was a hard failure of every
Rust proving target in the workspace (the compilation-unit coupling the stale-fixture outage
measured). The properties' STATEMENTS remain in `DeckDescent.lean` as evaluation-free
`check_* : Bool` definitions over `stepB`/`replayB`/`rowFor` — the same functions the emitter
tabulates and the judge runs; THIS module is where they are RUN. It is rooted in the
`PathOfAngelsGuards` library and reachable from `Dregg2.FFI` by NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged.

Named residue in the parent: NONE — no construction in `DeckDescent.lean` consumes a
`native_decide` proof as data, so every pin moved.
-/
import Dregg2.Games.PathOfAngels.DeckDescent

namespace Dregg2.Games.PathOfAngels.DeckDescent

set_option autoImplicit false

theorem every_board_can_be_banked :
    check_every_board_can_be_banked = true := by native_decide

theorem the_second_relic_makes_east_bankable_alone :
    check_the_second_relic_makes_east_bankable_alone = true := by native_decide

theorem budget_binds_on_the_cautious_lines :
    check_budget_binds_on_the_cautious_lines = true := by native_decide

theorem sweep_costs_the_budget_and_banks_on_one_board :
    check_sweep_costs_the_budget_and_banks_on_one_board = true := by native_decide

theorem budgets_are_incomparable :
    check_budgets_are_incomparable = true := by native_decide

theorem every_board_forks :
    check_every_board_forks = true := by native_decide

theorem every_board_can_be_lost :
    check_every_board_can_be_lost = true := by native_decide

theorem family_shape_is_measured :
    check_family_shape_is_measured = true := by native_decide

theorem the_mirror_is_broken :
    check_the_mirror_is_broken = true := by native_decide

theorem declared_states_fit_the_sling :
    check_declared_states_fit_the_sling = true := by native_decide

theorem walking_in_blind_costs_a_body :
    check_walking_in_blind_costs_a_body = true := by native_decide

theorem the_deck_keeps_what_you_could_not_carry :
    check_the_deck_keeps_what_you_could_not_carry = true := by native_decide

theorem a_sound_shaft_keeps_both_relics :
    check_a_sound_shaft_keeps_both_relics = true := by native_decide

theorem parametric_closure_is_closed :
    check_parametric_closure_is_closed = true := by native_decide

theorem parametric_states_nodup :
    check_parametric_states_nodup = true := by native_decide

theorem initial_state_is_declared :
    check_initial_state_is_declared = true := by native_decide

theorem parametric_shape_is_measured :
    check_parametric_shape_is_measured = true := by native_decide

theorem the_table_consults_the_instance :
    check_the_table_consults_the_instance = true := by native_decide

theorem state_ids_are_distinct :
    check_state_ids_are_distinct = true := by native_decide

theorem state_ids_are_identifiers :
    check_state_ids_are_identifiers = true := by native_decide

#assert_compiled every_board_can_be_banked
#assert_compiled the_second_relic_makes_east_bankable_alone
#assert_compiled budget_binds_on_the_cautious_lines
#assert_compiled sweep_costs_the_budget_and_banks_on_one_board
#assert_compiled budgets_are_incomparable
#assert_compiled every_board_forks
#assert_compiled every_board_can_be_lost
#assert_compiled family_shape_is_measured
#assert_compiled the_mirror_is_broken
#assert_compiled declared_states_fit_the_sling
#assert_compiled walking_in_blind_costs_a_body
#assert_compiled the_deck_keeps_what_you_could_not_carry
#assert_compiled a_sound_shaft_keeps_both_relics
#assert_compiled parametric_closure_is_closed
#assert_compiled parametric_states_nodup
#assert_compiled initial_state_is_declared
#assert_compiled parametric_shape_is_measured
#assert_compiled the_table_consults_the_instance
#assert_compiled state_ids_are_distinct
#assert_compiled state_ids_are_identifiers

end Dregg2.Games.PathOfAngels.DeckDescent
