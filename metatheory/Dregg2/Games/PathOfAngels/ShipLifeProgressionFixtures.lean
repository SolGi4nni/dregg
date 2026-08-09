/-
# Ship Life Progression — the projection-fixture EVALUATION, out of the crypto archive's build

`ShipLifeProgression.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build
root), and until 2026-08-08 its hostile checks ran `native_decide` pins at elaboration — so
any game-fixture regression was a hard failure of every Rust proving target in the
workspace.  The STATEMENTS remain in `ShipLifeProgression.lean` as evaluation-free
`check_* : Bool` definitions, beside the private sealed-receipt fixtures they must see;
THIS module is where they are RUN.  It is rooted in the `PathOfAngelsGuards` library and
reachable from `Dregg2.FFI` by NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged.  The fail-closed convention transfers: a check whose
accepted-fold prerequisite refuses answers `false`, so a broken prerequisite reds THIS
module.

⚠ One construction cluster did NOT move (`fixtureFailureState` and the
`replayExact`/`failedExact` fields of `fixtureFailureReceipt`) —
`ShipworksFailureReceiptInterface` carries an actual failed replay as proof data, so those
three `native_decide` must elaborate where the receipt is built.  They are the named
residue; the hostile-checks header in `ShipLifeProgression.lean` records it.
-/
import Dregg2.Games.PathOfAngels.ShipLifeProgression

namespace Dregg2.Games.PathOfAngels.ShipLifeProgression

set_option autoImplicit false

theorem cadence_earns_and_spends_one_forgiveness :
    check_cadence_earns_and_spends_one_forgiveness = true := by native_decide

theorem actual_shipworks_settlement_drives_daily_projection :
    check_actual_shipworks_settlement_drives_daily_projection = true := by native_decide

theorem hostile_same_shipworks_receipt_is_idempotently_refused :
    check_hostile_same_shipworks_receipt_is_idempotently_refused = true := by native_decide

theorem actual_failed_replay_is_meaningful_but_nonterminal :
    check_actual_failed_replay_is_meaningful_but_nonterminal = true := by native_decide

theorem craft_projection_conserves_and_never_mints :
    check_craft_projection_conserves_and_never_mints = true := by native_decide

theorem hostile_unknown_gear_is_refused :
    check_hostile_unknown_gear_is_refused = true := by native_decide

theorem holder_cosmetic_changes_style_and_exactly_no_power :
    check_holder_cosmetic_changes_style_and_exactly_no_power = true := by native_decide

theorem gallery_projection_is_balance_neutral_and_authored :
    check_gallery_projection_is_balance_neutral_and_authored = true := by native_decide

theorem season_migration_preserves_power_and_replay_nullifiers :
    check_season_migration_preserves_power_and_replay_nullifiers = true := by native_decide

theorem event_stream_replays_exactly_one_daily_receipt :
    check_event_stream_replays_exactly_one_daily_receipt = true := by native_decide

theorem event_batch_accepts_complete_derived_fanout :
    check_event_batch_accepts_complete_derived_fanout = true := by native_decide

#assert_compiled cadence_earns_and_spends_one_forgiveness
#assert_compiled actual_shipworks_settlement_drives_daily_projection
#assert_compiled hostile_same_shipworks_receipt_is_idempotently_refused
#assert_compiled actual_failed_replay_is_meaningful_but_nonterminal
#assert_compiled craft_projection_conserves_and_never_mints
#assert_compiled hostile_unknown_gear_is_refused
#assert_compiled holder_cosmetic_changes_style_and_exactly_no_power
#assert_compiled gallery_projection_is_balance_neutral_and_authored
#assert_compiled season_migration_preserves_power_and_replay_nullifiers
#assert_compiled event_stream_replays_exactly_one_daily_receipt
#assert_compiled event_batch_accepts_complete_derived_fanout

end Dregg2.Games.PathOfAngels.ShipLifeProgression
