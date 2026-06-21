/-
# Metatheory.SafetyGame — the canonical object behind the polis governor: the viability kernel.

gpt5.5's refactor: our `genGovStep step floor` is a one-step shield that is maximally permissive
*relative to `floor`* — but the long game showed `floor` itself may not be a controlled invariant.
The canonical fix is to shield the **viability kernel** (= maximal controlled invariant = safety-game
winning region): `K = νX. floor ∧ CPre(X)`, then shield `K`. Then "gentle" is GLOBALLY correct.

This file builds that object and its two load-bearing facts:
  * `kernel_invariant` — from any kernel state there IS a controllable move keeping you in the kernel
    (the kernel is a controlled invariant);
  * `kernel_maximal` — the kernel is the GREATEST floor-contained controlled invariant, so any
    governor that can preserve the floor forever admits no move leaving it (maximal permissiveness).
Shielding `K` with the existing `genGovStep` then inherits `genGov_safe` (∀ controller) and is, by
maximality, the *best* such governor — `envelope_least_restrictive` becomes the local lemma and
`kernel_maximal` the global one (gpt5.5 Q4: compute the kernel, then envelope it).
-/
import Mathlib.Order.FixedPoints
import Metatheory.PolisGovernorTheory

namespace Metatheory.SafetyGame

universe u

/-- A safety game: controllable moves vs adversary responses over a public world, with a floor. -/
structure Game where
  World : Type u
  Move : Type u
  Resp : Type u
  step : World → Move → Resp → World
  legal : World → Move → Resp → Prop
  floor : World → Prop

variable (G : Game)

/-- **Controllable predecessor**: `∃` a controllable move such that EVERY legal adversary response
keeps you in `X`. (Deterministic games: a single response, so this is `∃ m, X (step w m)`.) -/
def CPre (X : G.World → Prop) : G.World → Prop :=
  fun w => ∃ m, ∀ r, G.legal w m r → X (G.step w m r)

theorem CPre_mono : Monotone (CPre G) := by
  intro X Y hXY w hw
  obtain ⟨m, hm⟩ := hw
  exact ⟨m, fun r hr => hXY _ (hm r hr)⟩

/-- The safety functional `Φ X = floor ∧ CPre X`, as a monotone map on `World → Prop`. -/
def Φ : (G.World → Prop) →o (G.World → Prop) where
  toFun X := fun w => G.floor w ∧ CPre G X w
  monotone' := by
    intro X Y hXY w hw
    exact ⟨hw.1, CPre_mono G hXY w hw.2⟩

/-- **The viability kernel** — the greatest controlled invariant inside the floor (`νX. floor ∧ CPre X`). -/
def ViabilityKernel : G.World → Prop := OrderHom.gfp (Φ G)

/-- The kernel is its own `Φ`-image: `K = floor ∧ CPre K`. -/
theorem kernel_fixpoint : Φ G (ViabilityKernel G) = ViabilityKernel G :=
  OrderHom.map_gfp (Φ G)

/-- A kernel state satisfies the floor. -/
theorem kernel_subset_floor (w : G.World) (h : ViabilityKernel G w) : G.floor w := by
  have := kernel_fixpoint G
  rw [← this] at h
  exact h.1

/-- **`kernel_invariant`** — from any kernel state there IS a controllable move keeping you in the
kernel against every adversary response. The kernel is a controlled invariant. -/
theorem kernel_invariant (w : G.World) (h : ViabilityKernel G w) :
    CPre G (ViabilityKernel G) w := by
  have := kernel_fixpoint G
  rw [← this] at h
  exact h.2

/-- **`kernel_maximal`** — the kernel is the GREATEST floor-contained controlled invariant: any `X`
with `X ⊆ floor ∧ CPre X` lies inside it. So no governor that preserves the floor forever can admit
a move leaving the kernel (maximal permissiveness). -/
theorem kernel_maximal (X : G.World → Prop)
    (hX : ∀ w, X w → G.floor w ∧ CPre G X w) :
    ∀ w, X w → ViabilityKernel G w :=
  OrderHom.le_gfp (Φ G) (fun w hw => hX w hw)

/-! ## The shield is the envelope over the kernel — inheriting `genGov_safe` + maximality. -/

/-- Deterministic projection of a game (a single response baked in) to the `step : World → Move →
World` shape the runnable governor uses. -/
def detStep (resp : G.World → G.Move → G.Resp) : G.World → G.Move → G.World :=
  fun w m => G.step w m (resp w m)

open Classical in
/-- The maximally-permissive shield over the deterministic game: admit the controller's move iff its
successor stays in the VIABILITY KERNEL (not merely the raw floor), else shield (stay). This is the
`genGovStep` shape with the floor set to `K`; by `kernel_subset_floor` it preserves the floor, and by
`kernel_maximal` it is the most permissive governor that can. -/
noncomputable def kernelShield (resp : G.World → G.Move → G.Resp)
    (w : G.World) (m : G.Move) : G.World :=
  if ViabilityKernel G (detStep G resp w m) then detStep G resp w m else w

/-- The kernel-shield keeps the kernel for EVERY controller, hence — since `K ⊆ floor` — keeps the
floor forever. The runnable governor on the *right* predicate. -/
theorem kernelShield_preserves (resp : G.World → G.Move → G.Resp)
    (w : G.World) (m : G.Move) (h : ViabilityKernel G w) :
    ViabilityKernel G (kernelShield G resp w m) := by
  unfold kernelShield
  split <;> assumption

end Metatheory.SafetyGame
