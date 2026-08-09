/-
# Ship Expedition Season — the projection-fixture EVALUATION, out of the crypto archive's build

`ShipExpeditionSeason.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build
root), and until 2026-08-08 its projection and taxonomy fixtures ran `native_decide` pins
at elaboration — so any game-fixture regression was a hard failure of every Rust proving
target in the workspace.  The STATEMENTS remain in `ShipExpeditionSeason.lean` as
evaluation-free `check_* : Bool` definitions, beside the private fixture receipts they must
see; THIS module is where they are RUN.  It is rooted in the `PathOfAngelsGuards` library
and reachable from `Dregg2.FFI` by NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged.  The fail-closed convention transfers: a check whose
accepted-projection prerequisite refuses answers `false`, so a broken prerequisite reds
THIS module.  `ShipExpeditionSeason` keeps no `native_decide` residue of its own.
-/
import Dregg2.Games.PathOfAngels.ShipExpeditionSeason

namespace Dregg2.Games.PathOfAngels.ShipExpeditionSeason

set_option autoImplicit false

theorem runtime_receipt_projects_parts_relics_and_candidate_without_owning_them :
    check_runtime_receipt_projects_parts_relics_and_candidate_without_owning_them = true := by
  native_decide

theorem hostile_same_runtime_run_cannot_project_twice :
    check_hostile_same_runtime_run_cannot_project_twice = true := by native_decide

theorem sealed_health_receipt_only_updates_derived_health :
    check_sealed_health_receipt_only_updates_derived_health = true := by native_decide

theorem sealed_part_market_receipt_never_moves_relic_or_runtime_projection :
    check_sealed_part_market_receipt_never_moves_relic_or_runtime_projection = true := by
  native_decide

#assert_compiled runtime_receipt_projects_parts_relics_and_candidate_without_owning_them
#assert_compiled hostile_same_runtime_run_cannot_project_twice
#assert_compiled sealed_health_receipt_only_updates_derived_health
#assert_compiled sealed_part_market_receipt_never_moves_relic_or_runtime_projection

end Dregg2.Games.PathOfAngels.ShipExpeditionSeason
