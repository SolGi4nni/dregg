/-
# Station Crate Open — the two-pole EVALUATION, out of the crypto archive's build

`StationCrateOpen.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build root),
and until 2026-08-08 its poles and hostile openings ran seven `native_decide` pins at
elaboration — so any game-fixture regression was a hard failure of every Rust proving target
in the workspace.  The STATEMENTS remain in `StationCrateOpen.lean` as evaluation-free
`check_* : Bool` definitions, beside the private accepted-open prerequisite (`firstOpen?`)
they must see; THIS module is where they are RUN.  It is rooted in the `PathOfAngelsGuards`
library and reachable from `Dregg2.FFI` by NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged.  The fail-closed convention transfers: a check whose
prerequisite open refuses answers `false`, so a broken prerequisite reds THIS module.

⚠ One construction proof did NOT move (`panel_valid`) — `Panel` carries its validity proof
as data, so it must elaborate where `panel` is built.  It is the named residue; the poles
header in `StationCrateOpen.lean` records it.
-/
import Dregg2.Games.PathOfAngels.StationCrateOpen

namespace Dregg2.Games.PathOfAngels.StationCrateOpen

set_option autoImplicit false

theorem an_honest_salvage_open_moves_the_supplies_gauge :
    check_an_honest_salvage_open_moves_the_supplies_gauge = true := by native_decide

theorem an_ordinary_open_moves_no_gauge :
    check_an_ordinary_open_moves_no_gauge = true := by native_decide

theorem the_first_period_is_consumed_by_crew_41 :
    check_the_first_period_is_consumed_by_crew_41 = true := by native_decide

theorem the_replay_open_is_refused_and_never_reaches_the_panel :
    check_the_replay_open_is_refused_and_never_reaches_the_panel = true := by native_decide

theorem a_wrong_period_open_is_refused_and_never_reaches_the_panel :
    check_a_wrong_period_open_is_refused_and_never_reaches_the_panel = true := by native_decide

theorem the_communal_gauge_accumulates_only_the_salvage_draw :
    check_the_communal_gauge_accumulates_only_the_salvage_draw = true := by native_decide

theorem the_face_is_the_same_whatever_order_the_crew_arrives :
    check_the_face_is_the_same_whatever_order_the_crew_arrives = true := by native_decide

#assert_compiled an_honest_salvage_open_moves_the_supplies_gauge
#assert_compiled an_ordinary_open_moves_no_gauge
#assert_compiled the_first_period_is_consumed_by_crew_41
#assert_compiled the_replay_open_is_refused_and_never_reaches_the_panel
#assert_compiled a_wrong_period_open_is_refused_and_never_reaches_the_panel
#assert_compiled the_communal_gauge_accumulates_only_the_salvage_draw
#assert_compiled the_face_is_the_same_whatever_order_the_crew_arrives

end Dregg2.Games.PathOfAngels.StationCrateOpen
