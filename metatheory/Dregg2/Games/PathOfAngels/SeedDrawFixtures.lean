/-
# SeedDraw — the uniformity EVALUATION, out of the crypto archive's build

`SeedDraw.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build root), and
until 2026-08-08 its uniformity pin ran a `native_decide` at elaboration — so a
game-fixture regression was a hard failure of every Rust proving target in the workspace
(the compilation-unit coupling the stale-fixture outage measured).  The STATEMENT remains
in `SeedDraw.lean` as an evaluation-free `check_* : Bool` definition; THIS module is where
it is RUN.  It is rooted in the `PathOfAngelsGuards` library and reachable from
`Dregg2.FFI` by NOTHING, so:

  * a plain `lake build` still evaluates the pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

The theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified name is unchanged.
-/
import Dregg2.Games.PathOfAngels.SeedDraw

namespace Dregg2.Games.PathOfAngels.SeedDraw

set_option autoImplicit false

theorem draw_is_uniform_on_every_bound :
    check_draw_is_uniform_on_every_bound = true := by native_decide

#assert_compiled draw_is_uniform_on_every_bound

end Dregg2.Games.PathOfAngels.SeedDraw
