/-
# OfficerLogbook — the fixture EVALUATION, out of the crypto archive's build

`OfficerLogbook.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build root),
and until 2026-08-08 its fixtures ran ten `native_decide` pins at elaboration — so any
game-fixture regression was a hard failure of every Rust proving target in the workspace.
The fixtures' STATEMENTS remain in `OfficerLogbook.lean` as evaluation-free
`check_* : Bool` definitions, beside the private fixture material they must see; THIS
module is where they are RUN. It is rooted in the `PathOfAngelsGuards` library and
reachable from `Dregg2.FFI` by NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged. The fail-closed convention transfers: `fixtureAfter`
falls back to the empty projection when the batch refuses, so a broken batch fails the
shape pins in THIS module.

⚠ One construction proof did NOT move (`fixture_settlement_settles`) —
`Shipworks.Settlement` has a private constructor with no fallback inhabitant, so the proof
must elaborate where `fixtureSettlement` is built. It is the named residue; the fixtures
header in `OfficerLogbook.lean` records it.
-/
import Dregg2.Games.PathOfAngels.OfficerLogbook

namespace Dregg2.Games.PathOfAngels.OfficerLogbook

set_option autoImplicit false

theorem fixture_three_source_batch_is_exactly_projected :
    check_fixture_three_source_batch_is_exactly_projected = true := by native_decide

theorem fixture_projection_remains_non_authoritative :
    check_fixture_projection_remains_non_authoritative = true := by native_decide

theorem finalized_crew_member_gets_role_and_assist_not_personal_salvage :
    check_finalized_crew_member_gets_role_and_assist_not_personal_salvage = true := by
  native_decide

theorem hostile_exact_batch_replay_refused :
    check_hostile_exact_batch_replay_refused = true := by native_decide

theorem hostile_receipt_reorder_refused :
    check_hostile_receipt_reorder_refused = true := by native_decide

theorem hostile_nonparticipant_cannot_receive_crew_log :
    check_hostile_nonparticipant_cannot_receive_crew_log = true := by native_decide

theorem hostile_automatic_recovery_mutation_refused :
    check_hostile_automatic_recovery_mutation_refused = true := by native_decide

theorem hostile_market_relic_custody_refused :
    check_hostile_market_relic_custody_refused = true := by native_decide

theorem hostile_contribution_overflow_refused :
    check_hostile_contribution_overflow_refused = true := by native_decide

theorem hostile_foreign_world_refused :
    check_hostile_foreign_world_refused = true := by native_decide

#assert_compiled fixture_three_source_batch_is_exactly_projected
#assert_compiled fixture_projection_remains_non_authoritative
#assert_compiled finalized_crew_member_gets_role_and_assist_not_personal_salvage
#assert_compiled hostile_exact_batch_replay_refused
#assert_compiled hostile_receipt_reorder_refused
#assert_compiled hostile_nonparticipant_cannot_receive_crew_log
#assert_compiled hostile_automatic_recovery_mutation_refused
#assert_compiled hostile_market_relic_custody_refused
#assert_compiled hostile_contribution_overflow_refused
#assert_compiled hostile_foreign_world_refused

end Dregg2.Games.PathOfAngels.OfficerLogbook
