/-
# Bazaar game runtime — the codec fixture EVALUATION, out of the crypto archive's build

`BazaarGameRuntime.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build root), and
until 2026-08-08 its typed-CAS fixture ran nine `native_decide` pins at elaboration — so any
fixture regression was a hard failure of every Rust proving target in the workspace (the
compilation-unit coupling the stale-fixture outage measured). Six of them are HERE; their
STATEMENTS stay in `BazaarGameRuntime.lean` as evaluation-free `check_* : Bool` definitions.
This module is rooted in the `PathOfAngelsGuards` library and reachable from `Dregg2.FFI` by
NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged.

⚠ **Named residue, THREE — they did NOT move**, because each is required as DATA at
construction: `fixtureIdentity.parties_distinct` (a field of `StableMarketIdentity`),
`fixture_replay_genesis_accepts` and `fixture_replay_advance_accepts` (consumed by
`replayValueOfAccepted`, whose result feeds the `@[export] dregg_poa_bazaar_runtime_fixture`
entry point). `ReplayMachine.mk` is `private` with three proof fields, so no `ReplayApplied`
fallback is constructible and the fail-closed `match` shape does not apply. The parent's fixture
header records all three.
-/
import Dregg2.Games.PathOfAngels.BazaarGameRuntime

namespace Dregg2.Games.PathOfAngels.BazaarGameRuntime

set_option autoImplicit false

theorem fixture_state_codec_is_canonical :
    check_fixture_state_codec_is_canonical = true := by native_decide

theorem fixture_request_codec_is_canonical :
    check_fixture_request_codec_is_canonical = true := by native_decide

theorem fixture_state_trailing_byte_refuses :
    check_fixture_state_trailing_byte_refuses = true := by native_decide

theorem fixture_request_substitution_changes_wire :
    check_fixture_request_substitution_changes_wire = true := by native_decide

theorem fixture_replay_event_codec_is_canonical :
    check_fixture_replay_event_codec_is_canonical = true := by native_decide

theorem fixture_cross_deployment_event_refuses :
    check_fixture_cross_deployment_event_refuses = true := by native_decide

#assert_compiled fixture_state_codec_is_canonical
#assert_compiled fixture_request_codec_is_canonical
#assert_compiled fixture_state_trailing_byte_refuses
#assert_compiled fixture_request_substitution_changes_wire
#assert_compiled fixture_replay_event_codec_is_canonical
#assert_compiled fixture_cross_deployment_event_refuses

end Dregg2.Games.PathOfAngels.BazaarGameRuntime
