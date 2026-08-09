/-
# Salvage lock — the seed-space EVALUATION, out of the crypto archive's build

`SalvageLock.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build root), and until
2026-08-08 its seed-space enumerations ran four `native_decide` pins at elaboration — 6^6
candidate partner rows, 3^6 candidate glyph rows and all 90 seeds — so any change to the seed
space was a hard failure of every Rust proving target in the workspace (the compilation-unit
coupling the stale-fixture outage measured). The pins' STATEMENTS remain in `SalvageLock.lean`
as evaluation-free `check_* : Bool` definitions, beside the independently enumerated domains
they compare against; THIS module is where they are RUN. It is rooted in the
`PathOfAngelsGuards` library and reachable from `Dregg2.FFI` by NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged — including
`SalvageLock.seed_space_is_exactly_the_two_of_each_boards`, which `Emit.lean`'s docblock cites.

⚠ Named residue: NONE. Nothing in the parent demands a proof as data, so all four pins moved.
-/
import Dregg2.Games.PathOfAngels.SalvageLock

namespace Dregg2.Games.PathOfAngels.SalvageLock

set_option autoImplicit false

theorem seed_space_realizes_every_perfect_matching :
    check_seed_space_realizes_every_perfect_matching = true := by native_decide

theorem seed_space_is_exactly_the_two_of_each_boards :
    check_seed_space_is_exactly_the_two_of_each_boards = true := by native_decide

theorem every_matching_has_all_six_labellings :
    check_every_matching_has_all_six_labellings = true := by native_decide

theorem glyph_population_two :
    check_glyph_population_two = true := by native_decide

#assert_compiled seed_space_realizes_every_perfect_matching
#assert_compiled seed_space_is_exactly_the_two_of_each_boards
#assert_compiled every_matching_has_all_six_labellings
#assert_compiled glyph_population_two

end Dregg2.Games.PathOfAngels.SalvageLock
