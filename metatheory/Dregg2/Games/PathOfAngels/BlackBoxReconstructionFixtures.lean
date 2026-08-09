/-
# Black Box Reconstruction — the pin EVALUATION, out of the crypto archive's build

`BlackBoxReconstruction.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build
root), and until 2026-08-08 it ran six `native_decide` pins at elaboration — so any
game-fixture regression was a hard failure of every Rust proving target in the workspace.
The pins' STATEMENTS remain in `BlackBoxReconstruction.lean` as evaluation-free
`check_* : Bool` definitions; THIS module is where they are RUN. It is rooted in the
`PathOfAngelsGuards` library and reachable from `Dregg2.FFI` by NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged. Named residue: none — every evaluation moved.
-/
import Dregg2.Games.PathOfAngels.BlackBoxReconstruction

namespace Dregg2.Games.PathOfAngels.BlackBoxReconstruction

set_option autoImplicit false

theorem order_space_is_exactly_the_permutations :
    check_order_space_is_exactly_the_permutations = true := by native_decide

theorem every_instance_is_winnable_inside_the_budget :
    check_every_instance_is_winnable_inside_the_budget = true := by native_decide

theorem the_budget_is_the_listening_policy_worst_case :
    check_the_budget_is_the_listening_policy_worst_case = true := by native_decide

/-- ⚑ The playtest falsifier of 2026-08-09, kept as a number. -/
theorem the_hint_ignoring_scan_no_longer_wins :
    check_the_hint_ignoring_scan_no_longer_wins = true := by native_decide

theorem listening_is_what_closes_the_gap :
    check_listening_is_what_closes_the_gap = true := by native_decide

theorem a_run_can_be_lost :
    check_a_run_can_be_lost = true := by native_decide

theorem every_refusal_is_witnessed :
    check_every_refusal_is_witnessed = true := by native_decide

theorem a_probe_that_is_accepted_witnesses_nothing :
    check_a_probe_that_is_accepted_witnesses_nothing = true := by native_decide

#assert_compiled order_space_is_exactly_the_permutations
#assert_compiled every_instance_is_winnable_inside_the_budget
#assert_compiled the_budget_is_the_listening_policy_worst_case
#assert_compiled the_hint_ignoring_scan_no_longer_wins
#assert_compiled listening_is_what_closes_the_gap
#assert_compiled a_run_can_be_lost
#assert_compiled every_refusal_is_witnessed
#assert_compiled a_probe_that_is_accepted_witnesses_nothing

end Dregg2.Games.PathOfAngels.BlackBoxReconstruction
