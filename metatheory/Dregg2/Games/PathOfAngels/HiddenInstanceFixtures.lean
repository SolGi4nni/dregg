/-
# HiddenInstance — the fixture EVALUATION, out of the crypto archive's build

`HiddenInstance.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build root),
and until 2026-08-08 its seven fixtures ran `native_decide` at elaboration — every one of
them a Poseidon2 sponge draw — so a game-fixture regression was a hard failure of every
Rust proving target in the workspace (the compilation-unit coupling the stale-fixture
outage measured).  The STATEMENTS remain in `HiddenInstance.lean` as evaluation-free
`check_* : Bool` definitions, beside the private secrets and mission they are stated over;
THIS module is where they are RUN.  It is rooted in the `PathOfAngelsGuards` library and
reachable from `Dregg2.FFI` by NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

⚠ The sponge cost is real and it is now paid HERE.  `commit`, `runSeedFor` and
`practiceRunSeed` are `@[irreducible]` because a live draw through Lean's ELABORATOR cost
47.6 GB and 68 minutes on one file; `native_decide` runs the COMPILED function, which
ignores irreducibility and is cheap.  Do not replace any pin below with `decide` — that
would hand the kernel the reduction bomb.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged.  There is no residue: `HiddenInstance` builds no
proof-carrying structure that needs a drawn seed at elaboration.
-/
import Dregg2.Games.PathOfAngels.HiddenInstance

namespace Dregg2.Games.PathOfAngels.HiddenInstance

set_option autoImplicit false

theorem commit_separates_secrets : check_commit_separates_secrets = true := by native_decide

theorem commit_separates_slots : check_commit_separates_slots = true := by native_decide

theorem published_context_does_not_determine_the_run_seed :
    check_published_context_does_not_determine_the_run_seed = true := by native_decide

theorem two_players_draw_different_instances :
    check_two_players_draw_different_instances = true := by native_decide

theorem two_slots_draw_different_instances :
    check_two_slots_draw_different_instances = true := by native_decide

theorem practice_is_not_judged : check_practice_is_not_judged = true := by native_decide

theorem commitment_is_not_the_seed : check_commitment_is_not_the_seed = true := by native_decide

#assert_compiled commit_separates_secrets
#assert_compiled commit_separates_slots
#assert_compiled published_context_does_not_determine_the_run_seed
#assert_compiled two_players_draw_different_instances
#assert_compiled two_slots_draw_different_instances
#assert_compiled practice_is_not_judged
#assert_compiled commitment_is_not_the_seed

end Dregg2.Games.PathOfAngels.HiddenInstance
