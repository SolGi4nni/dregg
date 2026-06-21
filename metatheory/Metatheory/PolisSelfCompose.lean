/-
# Metatheory.PolisSelfCompose — relational domination as 2-safety on the counterfactual product.

gpt5.5's answer to Q4 (`docs/POLIS-HYPERPROPERTY-FRONTIER.md`): domination is comparative — "B was
viable WITHOUT the dominator's public contribution, but is NOT viable WITH it" — a 2-safety
property, classically reduced to a single-trace property on a **self-composed product**. Here the
product is a counterfactual pair of public configs (`actual` vs `actual with the dominator's public
events causally-closed-erased`); both viability sides are the `PolisViability` bounded public game,
so `Dominated` is **decidable** and **interior-free**, and `dominationBar` is an ordinary
`CaptureBar` on the product. (The causally-closed erasure `actual ↦ without` is CONSTRUCTED over the
deployed blocklace in `Metatheory.PolisEraseBlocklace.eraseAuthor`, and the bounded domination bar is
instantiated on real blocklace counterfactual-pairs in `Metatheory.PolisDominationDregg`.)
-/
import Metatheory.PolisViability

namespace Metatheory.PolisSelfCompose

open Metatheory.Polis Metatheory.PolisViability

variable {Config Move : Type}

/-- The self-composition product: the actual public config, and the config with the dominator's
public contribution removed (a causally-closed public erasure — supplied as data). -/
structure CFPair (Config : Type) where
  actual  : Config
  without : Config

/-- **Domination** (relational, 2-safety): `B` was viable WITHOUT the dominator's public actions
but is NOT viable WITH them — a lawful public contribution foreclosed `B`'s bounded option-space.
No interior: both sides are the public bounded game of `PolisViability`. -/
def Dominated (Ar : Arena Config Move) (k : Nat) (p : CFPair Config) : Prop :=
  Viable Ar k p.without ∧ ¬ Viable Ar k p.actual

instance (Ar : Arena Config Move) (k : Nat) (p : CFPair Config) : Decidable (Dominated Ar k p) :=
  inferInstanceAs (Decidable (Viable Ar k p.without ∧ ¬ Viable Ar k p.actual))

/-- **`dominationBar`** — relational domination as a single-trace `CaptureBar` on the self-composed
(counterfactual-pair) product: decidable, interior-free, barring EXACTLY the dominated pairs. The
standard 2-safety self-composition, in the native public game. -/
def dominationBar (Ar : Arena Config Move) (k : Nat) :
    CaptureBar (CFPair Config) (fun p => Dominated Ar k p) where
  badShape := fun p => Dominated Ar k p
  publicDecidable := fun p => inferInstanceAs (Decidable (Dominated Ar k p))
  loadBearing := fun _ h => h
  leastRestrictive := fun _ h => h

/-! ### Non-vacuity (the demo arena, recover-by-decrement, budget 5). -/

/-- A pair where `B` was viable WITHOUT the dominator (dist 3) but foreclosed WITH it (dist 10) is
DOMINATED — detected purely from the public game, no motive. -/
example : Dominated demoArena 5 ⟨10, 3⟩ := by decide
/-- A pair viable on both sides (dist 3 vs 3) is NOT dominated — the dominator made no difference. -/
example : ¬ Dominated demoArena 5 ⟨3, 3⟩ := by decide
/-- And one foreclosed on BOTH sides (dist 10 vs 10) is not *domination* either — B's loss was not
caused by the counterfactual difference (the comparison is load-bearing, not a bare foreclosure). -/
example : ¬ Dominated demoArena 5 ⟨10, 10⟩ := by decide

end Metatheory.PolisSelfCompose
