/-
# Salvage crate authored rotation — the pin EVALUATION, out of the crypto archive's build

`SalvageCrateExamples.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build root),
and until 2026-08-08 its rotation pins ran `native_decide` at elaboration — so any rotation
regression was a hard failure of every Rust proving target in the workspace (the
compilation-unit coupling the stale-fixture outage measured). Two pins' STATEMENTS remain in
`SalvageCrateExamples.lean` as evaluation-free `check_* : Bool` definitions; THIS module is
where they are RUN. It is rooted in the `PathOfAngelsGuards` library and reachable from
`Dregg2.FFI` by NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged.

⚠ **Named residue, ONE — it did NOT move.** `authored_rotation_config_valid` is required as
DATA by `config := ⟨raw, authored_rotation_config_valid⟩`, and `config` is consumed outside the
module (`StationCrateOpen`, `StationDailyRuntime`), so it can be neither moved nor made an
`Option`. `generated_rotation_is_deterministic` also stayed: it is `rfl`, not an evaluation,
but its statement names `config`, so its census line there is `#assert_compiled`. The
constructor-privacy teeth (`persistent_state_constructor_is_private` and friends) are
`fail_if_success` elaboration checks, not evaluations, and stayed with their `#assert_axioms`.
-/
import Dregg2.Games.PathOfAngels.SalvageCrateExamples

namespace Dregg2.Games.PathOfAngels.SalvageCrateExamples

set_option autoImplicit false

theorem generated_rotation_has_every_authored_period :
    check_generated_rotation_has_every_authored_period = true := by native_decide

theorem generated_rotation_has_no_draw_exhaustion :
    check_generated_rotation_has_no_draw_exhaustion = true := by native_decide

#assert_compiled generated_rotation_has_every_authored_period
#assert_compiled generated_rotation_has_no_draw_exhaustion

end Dregg2.Games.PathOfAngels.SalvageCrateExamples
