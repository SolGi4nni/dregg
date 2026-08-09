/-
# Crew relay vocabulary — the fixture-roster EVALUATION, out of the crypto archive's build

`CrewRelayExpedition.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build root),
and until 2026-08-08 its fixture roster ran a `native_decide` pin at elaboration — so a
game-fixture regression was a hard failure of every Rust proving target in the workspace (the
compilation-unit coupling the stale-fixture outage measured). The STATEMENT remains in
`CrewRelayExpedition.lean` as an evaluation-free `check_* : Bool` definition, beside the roster it
describes; THIS module is where it is RUN. It is rooted in the `PathOfAngelsGuards` library and
reachable from `Dregg2.FFI` by NOTHING, so:

  * a plain `lake build` still evaluates the pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

The theorem keeps the name the in-module `#assert_compiled` census used, so the fully-qualified
name is unchanged.
-/
import Dregg2.Games.PathOfAngels.CrewRelayExpedition

namespace Dregg2.Games.PathOfAngels.CrewRelayExpedition

set_option autoImplicit false

theorem fixture_roster_seats_are_distinct_in_every_authorizing_field :
    check_fixture_roster_seats_are_distinct_in_every_authorizing_field = true := by native_decide

#assert_compiled fixture_roster_seats_are_distinct_in_every_authorizing_field

end Dregg2.Games.PathOfAngels.CrewRelayExpedition
