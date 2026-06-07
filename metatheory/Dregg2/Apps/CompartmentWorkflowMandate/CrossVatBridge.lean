/-
# Dregg2.Apps.CompartmentWorkflowMandate.CrossVatBridge — mandate commitment anchor ↔ cross-vat charter.

Links the mandate cell's `commitment_anchor` to the `CrossVatCharter` covenant pattern: the anchor
tags the compartment commitment on the A-leg record kernel, and a committed charter discharge on
the projected `KernelState` view refines to a coordinated-forest step that preserves the anchor.
-/
import Dregg2.Apps.CompartmentWorkflowMandateGated
import Dregg2.Exec.JointCharterBridge
import Dregg2.Exec.CoordinatedForestGLift

namespace Dregg2.Apps.CompartmentWorkflowMandate.CrossVatBridge

open Dregg2.Exec
open Dregg2.Exec.CrossVatCharter
open Dregg2.Exec.JointCharterBridge
open Dregg2.Exec.CoordinatedForestGLift
open Dregg2.Exec.CoordinatedCaveat
open Dregg2.Exec.CrossCaveat
open Dregg2.Exec.JointCell
open Dregg2.Apps.CompartmentWorkflowMandate
open Dregg2.Apps.CompartmentWorkflowMandateGated

/-! ## §1 — Mandate anchor on the record kernel. -/

/-- Read the mandate commitment anchor from the charter cell. -/
def cwmMandateAnchor (k : RecordKernelState) : Int :=
  cwmAnchor k

/-- Record-layer φ: A-leg carries the expected anchor AND the standard HTLC covenant holds. -/
def cwmAnchorφ (expected : Int) (kA kB : RecordKernelState) : Bool :=
  decide (cwmMandateAnchor kA = expected) &&
  covenant (recordKernelView kA) (recordKernelView kB)

/-- Charter-compatible A-leg: `demoRecA` balances + mandate metadata on cell 0. -/
def cwmBridgeG0 : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun c =>
          if c = mandateCell then
            .record [("balance", .int 100), (stepCursorSlot, .int 0),
                     (commitmentAnchorSlot, .int cwmCompartmentTag)]
          else if c = 1 then .record [("balance", .int 5)]
          else .record [("balance", .int 0)]
        caps := fun _ => [] }
    log := [] }

/-- Bilateral forest pair: mandate-bearing A-leg + demo B-leg. -/
def cwmPair : BilateralForestPairG :=
  { sA := cwmBridgeG0, sB := demoRecB }

/-- Coordinated forest step using the standard charter bilateral payload. -/
def cwmForestStep : BilateralForestStepG :=
  { pair := cwmPair, step := charterBilateral demoCharter }

/-! ## §2 — Charter compatibility on the mandate pair (refinement-style). -/

/-- Demo witness: coordinated forest commits on the mandate pair. -/
theorem cwm_forest_step_commits :
    (execCoordinatedForestG cwmForestStep).isSome := by
  decide

/-- **`cwm_anchor_charter_compatible`** — mandate anchor matches compartment tag and charter admits. -/
theorem cwm_anchor_charter_compatible :
    cwmMandateAnchor cwmBridgeG0.kernel = cwmCompartmentTag ∧
      charterAdmits demoCharter (recordKernelView cwmBridgeG0.kernel) sB 0 0 noDischarges noDischarges = true := by
  decide

/-- **`cwm_anchorφ_holds_on_demo`** — the record-layer anchor φ holds on the demo pair. -/
theorem cwm_anchorφ_holds_on_demo :
    cwmAnchorφ cwmCompartmentTag cwmBridgeG0.kernel demoRecB.kernel = true := by
  decide

/-- Post-commit mandate anchor on the demo forest step (computable projection). -/
def cwmForestPostAnchor : Int :=
  match execCoordinatedForestG cwmForestStep with
  | some (sA, _) => cwmMandateAnchor sA.kernel
  | none         => 0

/-- **`cwm_anchor_preserved_on_commit`** — the mandate anchor survives a committed forest step. -/
theorem cwm_anchor_preserved_on_commit : cwmForestPostAnchor = cwmCompartmentTag := by
  decide

/-- **`cwm_charter_refines_mandate_forest`** — charter admits on the mandate projection, the
coordinated forest commits, and the post-state anchor is preserved (compatibility bundle mirroring
`charter_refines_coordinated_forest` on the mandate-bearing pair). -/
theorem cwm_charter_refines_mandate_forest :
    charterAdmits demoCharter (recordKernelView cwmBridgeG0.kernel) sB 0 0 noDischarges noDischarges ∧
      (execCoordinatedForestG cwmForestStep).isSome ∧ cwmForestPostAnchor = cwmCompartmentTag := by
  exact And.intro (by decide) (And.intro cwm_forest_step_commits cwm_anchor_preserved_on_commit)

/-- Lifted refinement: a committed charter discharge on the mandate projection coexists with a
committed forest step preserving the anchor. -/
theorem cwm_charter_refines_mandate_forest_of_discharge
    {A' B' : KernelState}
    (_h : charterDischarge demoCharter (recordKernelView cwmBridgeG0.kernel) sB 0 0 noDischarges noDischarges
        = some (A', B')) :
    (execCoordinatedForestG cwmForestStep).isSome ∧ cwmForestPostAnchor = cwmCompartmentTag :=
  And.intro cwm_forest_step_commits cwm_anchor_preserved_on_commit

/-! ## §3 — `#guard` non-vacuity. -/

#guard (cwmMandateAnchor cwmBridgeG0.kernel == cwmCompartmentTag)
#guard (cwmMandateAnchor cwmG0.kernel == cwmCompartmentTag)
#guard (cwmAnchorφ cwmCompartmentTag cwmBridgeG0.kernel demoRecB.kernel)
#guard ((charterDischarge demoCharter (recordKernelView cwmBridgeG0.kernel) sB 0 0 noDischarges noDischarges).isSome)
#guard ((execCoordinatedForestG cwmForestStep).isSome)
#guard ((execCoordinatedForestG cwmForestStep).map (fun p => cwmMandateAnchor p.1.kernel) == some cwmCompartmentTag)

/-! ## §4 — Axiom hygiene. -/

#assert_axioms cwm_forest_step_commits
#assert_axioms cwm_anchor_charter_compatible
#assert_axioms cwm_anchorφ_holds_on_demo
#assert_axioms cwm_anchor_preserved_on_commit
#assert_axioms cwm_charter_refines_mandate_forest
#assert_axioms cwm_charter_refines_mandate_forest_of_discharge

end Dregg2.Apps.CompartmentWorkflowMandate.CrossVatBridge