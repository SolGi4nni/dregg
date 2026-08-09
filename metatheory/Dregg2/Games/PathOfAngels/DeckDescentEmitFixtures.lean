/-
# Deck Descent wire — the descriptor-pin EVALUATION, out of the crypto archive's build

`DeckDescentEmit.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build root),
and until 2026-08-08 its descriptor pins ran fifteen `native_decide` evaluations at
elaboration — parsing the rendered bytes back and comparing all 17,316 rows against `rowFor`,
plus the four constructively-built falsifiers — so any descriptor regression was a hard
failure of every Rust proving target in the workspace (the compilation-unit coupling the
stale-fixture outage measured). The pins' STATEMENTS remain in `DeckDescentEmit.lean` as
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
import Dregg2.Games.PathOfAngels.DeckDescentEmit

namespace Dregg2.Games.PathOfAngels.DeckDescentEmit

set_option autoImplicit false

theorem descentDescriptor_exact_schema :
    check_descentDescriptor_exact_schema = true := by native_decide

theorem descentDescriptor_table_is_the_kernel :
    check_descentDescriptor_table_is_the_kernel = true := by native_decide

theorem descentDescriptor_views_are_the_kernel :
    check_descentDescriptor_views_are_the_kernel = true := by native_decide

theorem flattened_resolve_is_caught :
    check_flattened_resolve_is_caught = true := by native_decide

theorem truncated_table_is_caught :
    check_truncated_table_is_caught = true := by native_decide

theorem descentDescriptor_practice_is_the_kernel :
    check_descentDescriptor_practice_is_the_kernel = true := by native_decide

theorem a_missing_board_is_caught :
    check_a_missing_board_is_caught = true := by native_decide

theorem a_duplicated_board_is_caught :
    check_a_duplicated_board_is_caught = true := by native_decide

#assert_compiled descentDescriptor_exact_schema
#assert_compiled descentDescriptor_table_is_the_kernel
#assert_compiled descentDescriptor_views_are_the_kernel
#assert_compiled flattened_resolve_is_caught
#assert_compiled truncated_table_is_caught
#assert_compiled descentDescriptor_practice_is_the_kernel
#assert_compiled a_missing_board_is_caught
#assert_compiled a_duplicated_board_is_caught

end Dregg2.Games.PathOfAngels.DeckDescentEmit
