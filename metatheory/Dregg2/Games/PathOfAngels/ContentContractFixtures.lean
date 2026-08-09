/-
# ContentContract — the specimen EVALUATION, out of the crypto archive's build

`ContentContract.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build root), and
until 2026-08-08 its spoiler-free specimen and named hostile packs ran eight `native_decide` pins
at elaboration — so any specimen regression was a hard failure of every Rust proving target in
the workspace (the compilation-unit coupling the stale-fixture outage measured). The pins'
STATEMENTS remain in `ContentContract.lean` as evaluation-free `check_* : Bool` definitions,
beside the packs they read; THIS module is where they are RUN. It is rooted in the
`PathOfAngelsGuards` library and reachable from `Dregg2.FFI` by NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged. The hostile checks compare the EXACT error-code lists, so
a pack that refuses for a different reason still fails its pin.

⚠ Named residue: NONE. Every pack in the parent is a plain `def`, so no proof is demanded as
data at construction and all eight pins moved.
-/
import Dregg2.Games.PathOfAngels.ContentContract

namespace Dregg2.Games.PathOfAngels.ContentContract

set_option autoImplicit false

theorem fixture_content_is_valid :
    check_fixture_content_is_valid = true := by native_decide

theorem hostile_role_relabel_refused :
    check_hostile_role_relabel_refused = true := by native_decide

theorem hostile_unreachable_extraction_refused :
    check_hostile_unreachable_extraction_refused = true := by native_decide

theorem hostile_route_encounter_asymmetry_refused :
    check_hostile_route_encounter_asymmetry_refused = true := by native_decide

theorem hostile_unwinnable_budget_refused :
    check_hostile_unwinnable_budget_refused = true := by native_decide

theorem hostile_automatic_recovery_refused :
    check_hostile_automatic_recovery_refused = true := by native_decide

theorem hostile_market_relic_refused :
    check_hostile_market_relic_refused = true := by native_decide

theorem hostile_direct_alpha_promotion_refused :
    check_hostile_direct_alpha_promotion_refused = true := by native_decide

#assert_compiled fixture_content_is_valid
#assert_compiled hostile_role_relabel_refused
#assert_compiled hostile_unreachable_extraction_refused
#assert_compiled hostile_route_encounter_asymmetry_refused
#assert_compiled hostile_unwinnable_budget_refused
#assert_compiled hostile_automatic_recovery_refused
#assert_compiled hostile_market_relic_refused
#assert_compiled hostile_direct_alpha_promotion_refused

end Dregg2.Games.PathOfAngels.ContentContract
