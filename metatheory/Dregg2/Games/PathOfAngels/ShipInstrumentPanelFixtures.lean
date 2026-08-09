/-
# Ship Instrument Panel — the hostility-lab EVALUATION, out of the crypto archive's build

`ShipInstrumentPanel.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build root),
and until 2026-08-08 its hostility lab ran nine `native_decide` pins at elaboration — so any
game-fixture regression was a hard failure of every Rust proving target in the workspace
(the compilation-unit coupling the stale-fixture outage measured). The lab's STATEMENTS
remain in `ShipInstrumentPanel.lean` as evaluation-free `check_* : Bool` definitions, beside
the private lab objects they must see; THIS module is where they are RUN. It is rooted in the
`PathOfAngelsGuards` library and reachable from `Dregg2.FFI` by NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged.

⚠ Three construction proofs did NOT move (`lab_panel_valid`, `other_panel_valid`,
`tiny_panel_valid`) — `Panel` carries its validity proof as data, so they must elaborate
where the lab panels are built. They are the named residue; the lab header in
`ShipInstrumentPanel.lean` records it.
-/
import Dregg2.Games.PathOfAngels.ShipInstrumentPanel

namespace Dregg2.Games.PathOfAngels.ShipInstrumentPanel

set_option autoImplicit false

theorem lab_state_from_another_panel_refuses :
    check_lab_state_from_another_panel_refuses = true := by native_decide

theorem welded_lab_witness_is_refused_by_another_deployment :
    check_welded_lab_witness_is_refused_by_another_deployment = true := by native_decide

theorem welded_same_crew_member_cannot_be_counted_twice :
    check_welded_same_crew_member_cannot_be_counted_twice = true := by native_decide

theorem lab_capacity_refuses_rather_than_forgetting_a_receipt :
    check_lab_capacity_refuses_rather_than_forgetting_a_receipt = true := by native_decide

theorem lab_meter_overflow_refuses_instead_of_clipping :
    check_lab_meter_overflow_refuses_instead_of_clipping = true := by native_decide

theorem welded_lab_witness_is_admitted_by_its_own_deployment :
    check_welded_lab_witness_is_admitted_by_its_own_deployment = true := by native_decide

theorem welded_two_crew_members_of_one_day_are_both_counted :
    check_welded_two_crew_members_of_one_day_are_both_counted = true := by native_decide

theorem welded_lab_day_is_an_ordinary_one :
    check_welded_lab_day_is_an_ordinary_one = true := by native_decide

theorem welded_two_ordinary_days_leave_the_ship_unchanged :
    check_welded_two_ordinary_days_leave_the_ship_unchanged = true := by native_decide

#assert_compiled lab_state_from_another_panel_refuses
#assert_compiled welded_lab_witness_is_refused_by_another_deployment
#assert_compiled welded_same_crew_member_cannot_be_counted_twice
#assert_compiled lab_capacity_refuses_rather_than_forgetting_a_receipt
#assert_compiled lab_meter_overflow_refuses_instead_of_clipping
#assert_compiled welded_lab_witness_is_admitted_by_its_own_deployment
#assert_compiled welded_two_crew_members_of_one_day_are_both_counted
#assert_compiled welded_lab_day_is_an_ordinary_one
#assert_compiled welded_two_ordinary_days_leave_the_ship_unchanged

end Dregg2.Games.PathOfAngels.ShipInstrumentPanel
