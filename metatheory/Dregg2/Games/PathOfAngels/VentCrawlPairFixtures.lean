/-
# Vent Crawl, two slings — the measured-design EVALUATION

`VentCrawlPair.lean` states its measured properties as evaluation-free
`check_* : Bool` definitions (a `def` body elaborates without running); THIS module
is where they are RUN, under `native_decide` + `#assert_compiled`, rooted in the
`PathOfAngelsGuards` library.

That is the decoupling every sibling module in this directory already follows, and
the reason is the same one recorded in `VentCrawlFixtures.lean`: a game-fixture
regression must red the guards library, not a Rust proving target.  `VentCrawlPair`
imports `VentCrawl`, which is in the `Dregg2.FFI` closure, so an inline
`native_decide` here would put a nine-state backward induction on the critical path
of the crypto archive's build for no reason at all.

⚠ These pins are `native_decide`, so they are trusting the COMPILER, not the kernel —
`#assert_compiled` is the record of exactly that and it is why each one is named.
Nothing here reduces a Poseidon2 sponge; the arithmetic is `Nat` throughout and the
whole induction is fifteen states deep.
-/
import Dregg2.Games.PathOfAngels.VentCrawlPair

namespace Dregg2.Games.PathOfAngels.VentCrawlPair

set_option autoImplicit false

theorem the_scaled_induction_is_exact :
    check_the_scaled_induction_is_exact = true := by native_decide

theorem the_joint_decision_shape_is_measured :
    check_the_joint_decision_shape_is_measured = true := by native_decide

theorem the_two_crawlers_want_different_moves :
    check_the_two_crawlers_want_different_moves = true := by native_decide

theorem the_joint_optimum_beats_two_solos :
    check_the_joint_optimum_beats_two_solos = true := by native_decide

theorem the_asymmetry_is_where_the_value_is :
    check_the_asymmetry_is_where_the_value_is = true := by native_decide

theorem every_joint_move_is_someones_best :
    check_every_joint_move_is_someones_best = true := by native_decide

theorem the_pair_opens_together :
    check_the_pair_opens_together = true := by native_decide

#assert_compiled the_scaled_induction_is_exact
#assert_compiled the_joint_decision_shape_is_measured
#assert_compiled the_two_crawlers_want_different_moves
#assert_compiled the_joint_optimum_beats_two_solos
#assert_compiled the_asymmetry_is_where_the_value_is
#assert_compiled every_joint_move_is_someones_best
#assert_compiled the_pair_opens_together

end Dregg2.Games.PathOfAngels.VentCrawlPair
