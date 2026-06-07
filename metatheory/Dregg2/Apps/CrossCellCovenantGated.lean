/-
# Dregg2.Apps.CrossCellCovenantGated — cross-cell covenant as a verified bilateral app.

First Apps witness for **coordinated** cross-cell caveats: the `covenantCoord` + `goodBi` demo through
`CoordinatedForestGate` at the joint `KernelState` layer, plus the cross-vat **charter** from
`CrossVatCharter` (biscuits + covenant + bilateral commit).
-/
import Dregg2.Exec.CoordinatedForestGate
import Dregg2.Exec.CrossVatCharter

namespace Dregg2.Apps.CrossCellCovenantGated

open Dregg2.Exec
open Dregg2.Exec.CoordinatedForestGate
open Dregg2.Exec.CoordinatedCaveat
open Dregg2.Exec.CrossVatCharter
open Dregg2.Exec.StarbridgeGated
open Dregg2.Exec.JointCell
open Dregg2.Exec.CrossCaveat

/-! ## §1 — Fixtures. -/

def demoBind : SharedBinding goodBi :=
  { sidOfA := 42, sidOfB := 42, agreeA := rfl, agreeB := rfl }

def honestStep : BilateralStep :=
  { covenant := covenantCoord, bt := goodBi, bind := demoBind }

def honestCredStep : BilateralCredStep :=
  { covenant := covenantCoord, bt := goodBi, bind := demoBind
  , credA := goodCred, credB := goodCred }

def forgedCredStep : BilateralCredStep :=
  { covenant := covenantCoord, bt := goodBi, bind := demoBind
  , credA := forgedCred, credB := goodCred }

/-! ## §2 — End-user theorems. -/

theorem ccov_forged_cred_rejected :
    execBilateralCredGated sA sB forgedCredStep = none :=
  bilateral_cred_forged_fails

theorem ccov_covenant_teeth :
    execBilateralCoordinated sA sBhigh honestStep = none := by
  unfold honestStep
  exact bilateral_covenant_teeth

theorem ccov_joint_conserves {A' B' : KernelState}
    (h : execBilateralCoordinated sA sB honestStep = some (A', B')) :
    jointTotal A' B' = jointTotal sA sB :=
  (bilateral_coordinated_sound honestStep h).1

theorem ccov_charter_commits :
    (charterDischarge demoCharter sA sB 0 0 noDischarges noDischarges).isSome := by
  decide

/-! ## §3 — `#guard` non-vacuity. -/

#guard ((execBilateralCoordinated sA sB honestStep).isSome)  --  true
#guard ((execBilateralCredGated sA sB forgedCredStep).isSome) == false  --  forged
#guard ((execBilateralCoordinated sA sBhigh honestStep).isSome) == false  --  covenant
#guard ((charterDischarge demoCharter sA sB 0 0 noDischarges noDischarges).isSome)  --  charter

/-! ## §4 — Axiom hygiene. -/

#assert_axioms ccov_forged_cred_rejected
#assert_axioms ccov_covenant_teeth
#assert_axioms ccov_joint_conserves
#assert_axioms ccov_charter_commits

end Dregg2.Apps.CrossCellCovenantGated