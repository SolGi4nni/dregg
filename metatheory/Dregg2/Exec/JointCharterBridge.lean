/-
# Dregg2.Exec.JointCharterBridge — the common cross-vat charter wired to joint + forest semantics.

Cross-vat charters (`CrossVatCharter`) are the **production** pattern: coordinated covenant `φ` +
bilateral turn `bt` + per-leg biscuits. The joint equalizer (`CoordinatedForestGate` /
`CoordinatedCaveat.dischargeCoordinated`) is the executable discharge target for `.coordinated`
caveats. The N-ary cross-cell forest (`CrossCellForest`) carries the same CG-5 binding at the
`Fin 2` bilateral slice.

This module makes the relationships explicit and load-bearing:

  * a committed **charter** refines a committed **bilateral coordinated** step (credentials are
    STRICTER — stripping biscuits cannot invalidate a charter commit);
  * the charter's `bt` inherits the proved **cross-forest Σ=0** binding (`halves_sum_zero`);
  * the three layers share one **covenant teeth** story (violated `φ` ⇒ fail-closed everywhere).
-/
import Dregg2.Exec.CrossVatCharter
import Dregg2.Exec.CoordinatedForestGate
import Dregg2.Exec.CrossCellForest

namespace Dregg2.Exec.JointCharterBridge

open Dregg2.Authority
open Dregg2.Exec.JointCell
open Dregg2.Exec.CrossCaveat
open Dregg2.Exec.CoordinatedCaveat
open Dregg2.Exec.CrossVatCharter
open Dregg2.Exec.CoordinatedForestGate
open Dregg2.Exec.CrossCellForest

/-! ## §1 — Project a charter onto the bilateral equalizer payload. -/

/-- Canonical CG-2 binding for a charter turn (the runtime executor ignores `bind`; soundness uses it). -/
def charterBind (ch : Charter) : SharedBinding ch.bt :=
  { sidOfA := ch.bt.sid, sidOfB := ch.bt.sid, agreeA := rfl, agreeB := rfl }

/-- The bilateral equalizer step carried by a charter (covenant + turn + CG-2 binding). -/
def charterBilateral (ch : Charter) : BilateralStep :=
  { covenant := ch.covenant, bt := ch.bt, bind := charterBind ch }

/-! ## §2 — Charter refines bilateral coordinated (credentials are the strict superset). -/

/-- **`charter_refines_bilateral_coordinated`** — every committed charter discharge is ALSO a
committed `execBilateralCoordinated` on the same covenant/turn. Biscuits and cross-vat
verifiability are additional legs; they cannot make a charter commit where the equalizer would fail. -/
theorem charter_refines_bilateral_coordinated (ch : Charter)
    {A B A' B' : KernelState} (heightA heightB : Nat) (dA dB : Discharges Unit)
    (h : charterDischarge ch A B heightA heightB dA dB = some (A', B')) :
    execBilateralCoordinated A B (charterBilateral ch) = some (A', B') := by
  unfold charterDischarge at h
  by_cases hadm : charterAdmits ch A B heightA heightB dA dB
  · rw [if_pos hadm] at h
    unfold execBilateralCoordinated
    exact h
  · rw [if_neg hadm] at h
    exact absurd h (by simp)

/-- **`charter_joint_conserves`** — a committed charter preserves the joint total (CG-5), via the
bilateral refinement + `bilateral_coordinated_sound`. -/
theorem charter_joint_conserves (ch : Charter)
    {A B A' B' : KernelState} (heightA heightB : Nat) (dA dB : Discharges Unit)
    (h : charterDischarge ch A B heightA heightB dA dB = some (A', B')) :
    jointTotal A' B' = jointTotal A B :=
  (bilateral_coordinated_sound (charterBilateral ch)
    (@charter_refines_bilateral_coordinated ch A B A' B' heightA heightB dA dB h)).1

/-! ## §3 — Forest binding: the charter's bilateral turn carries Σ=0. -/

/-- **`charter_forest_binding`** — the charter's `bt` satisfies the cross-cell forest's N-ary Σ=0
binding at the `Fin 2` bilateral slice (`halfA + halfB = 0`). This is the CG-5 hypothesis the
cross-cell nested forest requires — charters inherit it for free from `BiTurn` geometry. -/
theorem charter_forest_binding (ch : Charter) :
    ∑ i, (crossForestBilateral ch.bt).δ i = 0 :=
  crossForest_bilateral_balanced ch.bt

/-- Demo witness on the standard `demoCharter`. -/
theorem demoCharter_forest_binding :
    ∑ i, (crossForestBilateral demoCharter.bt).δ i = 0 :=
  charter_forest_binding demoCharter

/-! ## §4 — Unified covenant teeth (charter = bilateral = coordinated discharge). -/

/-- **`charter_covenant_implies_bilateral_none`** — violated covenant rejects the bilateral path
even when biscuit legs would pass. Reuses `bilateral_covenant_teeth` on the demo fixtures. -/
theorem demoCharter_bilateral_covenant_teeth :
    execBilateralCoordinated sA sBhigh (charterBilateral demoCharter) = none := by
  unfold charterBilateral charterBind demoCharter
  exact bilateral_covenant_teeth

/-! ## §5 — `#guard` non-vacuity (common pattern is live). -/

#guard ((charterDischarge demoCharter sA sB 0 0 CrossVatCharter.noDischarges CrossVatCharter.noDischarges).isSome)  --  charter commits
#guard ((execBilateralCoordinated sA sB (charterBilateral demoCharter)).isSome)  --  refines
#guard ((execBilateralCoordinated sA sBhigh (charterBilateral demoCharter)).isSome) == false  --  teeth
#guard (∑ i, (crossForestBilateral demoCharter.bt).δ i) == 0  --  Σ=0 binding

/-! ## §6 — Axiom hygiene. -/

#assert_axioms charter_refines_bilateral_coordinated
#assert_axioms charter_joint_conserves
#assert_axioms charter_forest_binding
#assert_axioms demoCharter_forest_binding
#assert_axioms demoCharter_bilateral_covenant_teeth

end Dregg2.Exec.JointCharterBridge