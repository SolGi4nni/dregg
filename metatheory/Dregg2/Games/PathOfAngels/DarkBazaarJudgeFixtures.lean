/-
# Dark Bazaar v1 judge — the fixture EVALUATION, out of the crypto archive's build

`DarkBazaarJudge.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build root), and
until 2026-08-08 its complete executable fixture ran ten `native_decide` pins at elaboration —
each one through the concrete N=4/K=4 private descriptor hash and the exported judge — so any
fixture regression was a hard failure of every Rust proving target in the workspace (the
compilation-unit coupling the stale-fixture outage measured). The fixture's STATEMENTS remain in
`DarkBazaarJudge.lean` as evaluation-free `check_* : Bool` definitions, beside the descriptor
root, commitment and order nullifiers they are built from; THIS module is where they are RUN. It
is rooted in the `PathOfAngelsGuards` library and reachable from `Dregg2.FFI` by NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged.

⚠ Named residue: NONE. Every fixture value in the parent is a plain `def`, so no proof is
demanded as data at construction and all ten pins moved.
-/
import Dregg2.Games.PathOfAngels.DarkBazaarJudge

namespace Dregg2.Games.PathOfAngels.DarkBazaarJudge

set_option autoImplicit false

theorem fixture_input_roundtrip :
    check_fixture_input_roundtrip = true := by native_decide

theorem fixture_semantic_inhabited :
    check_fixture_semantic_inhabited = true := by native_decide

theorem fixture_process_success :
    check_fixture_process_success = true := by native_decide

theorem fixture_trailing_byte_refused :
    check_fixture_trailing_byte_refused = true := by native_decide

theorem fixture_unknown_field_refused :
    check_fixture_unknown_field_refused = true := by native_decide

theorem fixture_uppercase_digest_refused :
    check_fixture_uppercase_digest_refused = true := by native_decide

theorem fixture_reordered_nullifiers_refused :
    check_fixture_reordered_nullifiers_refused = true := by native_decide

theorem fixture_overbound_output_refused :
    check_fixture_overbound_output_refused = true := by native_decide

theorem fixture_wrong_clearing_refused :
    check_fixture_wrong_clearing_refused = true := by native_decide

theorem fixture_wrong_nullifiers_refused :
    check_fixture_wrong_nullifiers_refused = true := by native_decide

#assert_compiled fixture_input_roundtrip
#assert_compiled fixture_semantic_inhabited
#assert_compiled fixture_process_success
#assert_compiled fixture_trailing_byte_refused
#assert_compiled fixture_unknown_field_refused
#assert_compiled fixture_uppercase_digest_refused
#assert_compiled fixture_reordered_nullifiers_refused
#assert_compiled fixture_overbound_output_refused
#assert_compiled fixture_wrong_clearing_refused
#assert_compiled fixture_wrong_nullifiers_refused

end Dregg2.Games.PathOfAngels.DarkBazaarJudge
