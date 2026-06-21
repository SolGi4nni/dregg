/-
# Metatheory.PolisMonitor — the temporal Monitorable witness (the last frontier piece).

The one object the hyperproperty frontier left open: a `Monitorable` witness for the real *temporal*
polis floor over the deployed observation stream. gpt5.5's headline holds — the ENFORCEABLE floor is
the **safety / bounded-liveness** fragment (a violation has a finite public bad prefix); unbounded
liveness ("the floor is reached *eventually*") is aspirational, NOT monitorable, and we never claim
to enforce it. *Decidable gentleness is bounded gentleness.*

This closes the frontier for the safety + flow fragment over the deployed carrier:
  * `safetyMonitor` — EVERY per-tick safety floor is monitorable (generalizes `neverFalseMon`).
  * `polisFloorMonitor` — the DEPLOYED `PolisStreamCarrier.polisFloorProp` is monitorable.
  * `flowMonitor` + `flowBad_iff_decide` — the flow-policy floor is monitorable AND its bad-prefix
    is DECIDED by the deployed Büchi/DupSim game `FlowRefine.decideRefines` (gpt5.5's pointer, met).
-/
import Metatheory.PolisCrossCell
import Metatheory.PolisStreamCarrier
import Metatheory.PolisFlowRefine

namespace Metatheory.PolisMonitor

open Metatheory.PolisCrossCell Dregg2.Deos.FlowAlgebra Dregg2.Deos.FlowRefine

/-- **`safetyMonitor` — every per-tick SAFETY floor is Monitorable.** The bad prefix is "some past
tick already violated the floor": SOUND (a bad prefix forces a violation) and COMPLETE (every
violation has a bad prefix). So any invariant floor over a public stream is governable from a FINITE
public prefix — no need to observe the infinite stream, no interior. -/
def safetyMonitor {Event : Type} (floor : Event → Prop) :
    Monitorable (fun σ => ∀ n, floor (σ n)) where
  bad σ n := ∃ i, i < n ∧ ¬ floor (σ i)
  sound := fun _ _ => fun ⟨i, _, hi⟩ hp => hi (hp i)
  complete := fun σ h =>
    let key : ∃ n, ¬ floor (σ n) :=
      Classical.byContradiction (fun hc =>
        h (fun n => Classical.byContradiction (fun hn => hc ⟨n, hn⟩)))
    match key with
    | ⟨n, hn⟩ => ⟨n + 1, n, Nat.lt_succ_self n, hn⟩

/-- **The DEPLOYED temporal polis floor is Monitorable.** `PolisStreamCarrier.polisFloorProp floor`
(the floor holds at every tick of the deployed `obsStream`) has a finite-prefix witness for every
violation — the last frontier closed for the SAFETY fragment over the real adversary stream. -/
def polisFloorMonitor {Obs : Type} (floor : Obs → Prop) :
    Monitorable (PolisStreamCarrier.polisFloorProp floor) :=
  safetyMonitor floor

/-- A violation of the deployed temporal floor is witnessed by a finite public prefix. -/
theorem polisFloor_violation_has_finite_witness {Obs : Type}
    (floor : Obs → Prop) (σ : Nat → Obs)
    (h : ¬ PolisStreamCarrier.polisFloorProp floor σ) :
    ∃ n, (polisFloorMonitor floor).bad σ n :=
  violation_has_finite_witness (polisFloorMonitor floor) σ h

/-- **The FLOW-policy floor is Monitorable.** A flow stream is captured exactly when some tick's flow
has already escaped the floor flow `F`. -/
def flowMonitor (F : Proc) : Monitorable (fun σ => ∀ n, σ n ≤ᶠ F) :=
  safetyMonitor (fun p => p ≤ᶠ F)

/-- **The flow monitor's bad-prefix is publicly DECIDABLE via the deployed Büchi game** — "tick `i`'s
flow escaped `F`" is exactly `decideRefines (σ i) F = false` (sound+complete by `decideRefines_iff`),
no motive. gpt5.5's `FlowRefine.decideRefines` pointer, realized as the per-tick bad-shape decision. -/
theorem flowBad_iff_decide (F : Proc) (σ : Nat → Proc) (n : Nat) :
    (flowMonitor F).bad σ n ↔ ∃ i, i < n ∧ decideRefines (σ i) F = false := by
  show (∃ i, i < n ∧ ¬ (σ i ≤ᶠ F)) ↔ _
  refine exists_congr (fun i => and_congr_right (fun _ => ?_))
  rw [← decideRefines_iff (σ i) F]
  cases decideRefines (σ i) F <;> simp

/-! ### The honest boundary: unbounded liveness is NOT monitorable.

A pure liveness property — "the floor is reached at SOME tick" (`∃ n, floor (σ n)`) — has NO finite
bad prefix: any finite prefix could still be extended to satisfy it, so no `Monitorable` witness can
exist. The enforceable polis floor is therefore the SAFETY closure (above) and the BOUNDED-liveness
reductions (`PolisViability.viableWithinB`'s `cwithin` bound), never unbounded liveness. We record
the boundary rather than overclaim it: a finite observation can refute "floor at every tick"; it can
never refute "floor at some tick". -/

/-- Witness of the boundary: no finite prefix of the all-`false` stream refutes the liveness property
`∃ n, σ n = true` — because the prefix can always be extended by a `true`. (Contrast: the SAFETY
property `∀ n, σ n = true` IS refuted by that same prefix.) So liveness is not finite-prefix
monitorable; the enforceable floor stays safety/bounded. -/
theorem liveness_not_prefix_refutable :
    ∀ n : Nat, ∃ τ : Nat → Bool, (∀ i < n, τ i = false) ∧ (∃ m, τ m = true) :=
  fun n => ⟨fun i => decide (i ≥ n), fun i hi => by simp [Nat.not_le.mpr hi],
            ⟨n, by simp⟩⟩

end Metatheory.PolisMonitor
