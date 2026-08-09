/-
# Vent Crawl wire — the descriptor-pin EVALUATION, out of the crypto archive's build

`VentCrawlEmit.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build root), and
until 2026-08-08 its descriptor pins ran nineteen `native_decide` evaluations at elaboration
— parsing the rendered bytes back and comparing all 102 rows against `VentCrawl.rowFor`,
plus the five constructively-built falsifiers — so any descriptor regression was a hard
failure of every Rust proving target in the workspace (the compilation-unit coupling the
stale-fixture outage measured). The pins' STATEMENTS remain in `VentCrawlEmit.lean` as
evaluation-free `check_* : Bool` definitions over the live validators and falsifiers; THIS
module is where they are RUN. It is rooted in the `PathOfAngelsGuards` library and reachable
from `Dregg2.FFI` by NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged.

Named residue in the parent: NONE — every pin moved.
-/
import Dregg2.Games.PathOfAngels.VentCrawlEmit

namespace Dregg2.Games.PathOfAngels.VentCrawlEmit

set_option autoImplicit false

theorem ventCrawlDescriptor_exact_schema :
    check_ventCrawlDescriptor_exact_schema = true := by native_decide

theorem ventCrawlDescriptor_table_is_the_kernel :
    check_ventCrawlDescriptor_table_is_the_kernel = true := by native_decide

theorem ventCrawlDescriptor_views_are_the_kernel :
    check_ventCrawlDescriptor_views_are_the_kernel = true := by native_decide

theorem ventCrawlDescriptor_payout_is_the_kernel :
    check_ventCrawlDescriptor_payout_is_the_kernel = true := by native_decide

theorem unpriced_map_is_caught :
    check_unpriced_map_is_caught = true := by native_decide

theorem flattened_wager_is_caught :
    check_flattened_wager_is_caught = true := by native_decide

theorem softened_odds_are_caught :
    check_softened_odds_are_caught = true := by native_decide

theorem pruned_haul_is_caught :
    check_pruned_haul_is_caught = true := by native_decide

theorem truncated_table_is_caught :
    check_truncated_table_is_caught = true := by native_decide

#assert_compiled ventCrawlDescriptor_exact_schema
#assert_compiled ventCrawlDescriptor_table_is_the_kernel
#assert_compiled ventCrawlDescriptor_views_are_the_kernel
#assert_compiled ventCrawlDescriptor_payout_is_the_kernel
#assert_compiled flattened_wager_is_caught
#assert_compiled softened_odds_are_caught
#assert_compiled pruned_haul_is_caught
#assert_compiled truncated_table_is_caught
#assert_compiled unpriced_map_is_caught

end Dregg2.Games.PathOfAngels.VentCrawlEmit
