/-
# DeckExpedition — the fixture EVALUATION, out of the crypto archive's build

`DeckExpedition.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build root),
and until 2026-08-08 its fixtures ran eleven `native_decide` pins at elaboration — whole
expedition replays — so a game-fixture regression was a hard failure of every Rust proving
target in the workspace (the compilation-unit coupling the stale-fixture outage measured).
The STATEMENTS remain in `DeckExpedition.lean` as evaluation-free `check_* : Bool`
definitions, beside the pack, party and transcripts they replay; THIS module is where they
are RUN.  It is rooted in the `PathOfAngelsGuards` library and reachable from `Dregg2.FFI`
by NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged.  The fail-closed convention transfers: a check whose
prerequisite replay refuses answers `false`, so a broken prerequisite reds THIS module.

⚠ Two construction proofs did NOT move (`fixture_raw_config_valid`,
`fixture_tight_raw_config_valid`) — `Config` carries its validity proof as data, so they
must elaborate where `fixtureConfig` and `fixtureTightConfig` are built.  They are the
named residue; the fixtures header in `DeckExpedition.lean` records it.
-/
import Dregg2.Games.PathOfAngels.DeckExpedition

namespace Dregg2.Games.PathOfAngels.DeckExpedition

set_option autoImplicit false

theorem fixture_initial_state_valid :
    check_fixture_initial_state_valid = true := by native_decide

theorem fixture_full_expedition_accepts :
    check_fixture_full_expedition_accepts = true := by native_decide

theorem fixture_withdrawal_restores_custody :
    check_fixture_withdrawal_restores_custody = true := by native_decide

theorem fixture_same_key_replay_refused :
    check_fixture_same_key_replay_refused = true := by native_decide

theorem fixture_daily_budget_is_hard :
    check_fixture_daily_budget_is_hard = true := by native_decide

theorem fixture_undeclared_discovery_refused :
    check_fixture_undeclared_discovery_refused = true := by native_decide

theorem fixture_early_extraction_refused :
    check_fixture_early_extraction_refused = true := by native_decide

theorem fixture_turn_budget_refuses_second_run_action :
    check_fixture_turn_budget_refuses_second_run_action = true := by native_decide

theorem fixture_declared_treatment_repairs_injury :
    check_fixture_declared_treatment_repairs_injury = true := by native_decide

#assert_compiled fixture_initial_state_valid
#assert_compiled fixture_full_expedition_accepts
#assert_compiled fixture_withdrawal_restores_custody
#assert_compiled fixture_same_key_replay_refused
#assert_compiled fixture_daily_budget_is_hard
#assert_compiled fixture_undeclared_discovery_refused
#assert_compiled fixture_early_extraction_refused
#assert_compiled fixture_turn_budget_refuses_second_run_action
#assert_compiled fixture_declared_treatment_repairs_injury

end Dregg2.Games.PathOfAngels.DeckExpedition
