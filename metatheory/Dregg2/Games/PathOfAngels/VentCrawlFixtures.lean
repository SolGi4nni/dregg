/-
# Vent Crawl — the measured-design EVALUATION, out of the crypto archive's build

`VentCrawl.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build root), and
until 2026-08-08 its measured design properties ran twenty `native_decide` evaluations at
elaboration — the 51-state parametric closure, the per-vein family census, the played-out
lines, and the two Poseidon2 sentinel fixtures — so any game-fixture regression was a hard
failure of every Rust proving target in the workspace (the compilation-unit coupling the
stale-fixture outage measured). The properties' STATEMENTS remain in `VentCrawl.lean` as
evaluation-free `check_* : Bool` definitions over `stepB`/`replayB`/`rowFor`; THIS module is
where they are RUN. It is rooted in the `PathOfAngelsGuards` library and reachable from
`Dregg2.FFI` by NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

⚠ The two sentinel pins at the bottom evaluate Poseidon2 sponges.  That is exactly why they
are HERE and why they are `native_decide`: `Poseidon2BabyBearW16.perm` reduces exponentially
under the elaborator, and the compiled evaluator is the only thing ever asked to run it.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged.

Named residue in the parent: NONE — no construction in `VentCrawl.lean` consumes a
`native_decide` proof as data, so every pin moved.
-/
import Dregg2.Games.PathOfAngels.VentCrawl

namespace Dregg2.Games.PathOfAngels.VentCrawl

set_option autoImplicit false

theorem parametric_closure_is_closed :
    check_parametric_closure_is_closed = true := by native_decide

theorem parametric_states_nodup :
    check_parametric_states_nodup = true := by native_decide

theorem initial_state_is_declared :
    check_initial_state_is_declared = true := by native_decide

theorem parametric_shape_is_measured :
    check_parametric_shape_is_measured = true := by native_decide

theorem the_table_consults_the_day :
    check_the_table_consults_the_day = true := by native_decide

theorem every_declared_reason_fires :
    check_every_declared_reason_fires = true := by native_decide

theorem no_undeclared_reason_fires :
    check_no_undeclared_reason_fires = true := by native_decide

theorem family_shape_is_measured :
    check_family_shape_is_measured = true := by native_decide

theorem a_drowned_run_is_always_worth_submitting :
    check_a_drowned_run_is_always_worth_submitting = true := by native_decide

theorem every_vein_forks :
    check_every_vein_forks = true := by native_decide

theorem state_ids_are_distinct :
    check_state_ids_are_distinct = true := by native_decide

theorem a_calm_tape_rewards_the_deep_line :
    check_a_calm_tape_rewards_the_deep_line = true := by native_decide

theorem a_foul_tape_drowns_the_first_crawl :
    check_a_foul_tape_drowns_the_first_crawl = true := by native_decide

theorem a_drowned_run_cannot_keep_going :
    check_a_drowned_run_cannot_keep_going = true := by native_decide

theorem the_scout_comes_home_where_the_third_crawl_drowns :
    check_the_scout_comes_home_where_the_third_crawl_drowns = true := by native_decide

theorem the_day_table_is_not_a_player_stream :
    check_the_day_table_is_not_a_player_stream = true := by native_decide

theorem two_crawlers_share_a_vein_and_not_a_tape :
    check_two_crawlers_share_a_vein_and_not_a_tape = true := by native_decide

#assert_compiled parametric_closure_is_closed
#assert_compiled parametric_states_nodup
#assert_compiled initial_state_is_declared
#assert_compiled parametric_shape_is_measured
#assert_compiled the_table_consults_the_day
#assert_compiled every_declared_reason_fires
#assert_compiled no_undeclared_reason_fires
#assert_compiled family_shape_is_measured
#assert_compiled a_drowned_run_is_always_worth_submitting
#assert_compiled every_vein_forks
#assert_compiled state_ids_are_distinct
#assert_compiled a_calm_tape_rewards_the_deep_line
#assert_compiled a_foul_tape_drowns_the_first_crawl
#assert_compiled a_drowned_run_cannot_keep_going
#assert_compiled the_scout_comes_home_where_the_third_crawl_drowns
#assert_compiled the_day_table_is_not_a_player_stream
#assert_compiled two_crawlers_share_a_vein_and_not_a_tape

end Dregg2.Games.PathOfAngels.VentCrawl
