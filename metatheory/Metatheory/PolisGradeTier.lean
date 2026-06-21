/-
# Metatheory.PolisGradeTier — the DEPLOYED Finality.Tier laundering grade (closes the §5 residual).

`PolisGrade` named "wiring the `Finality.Tier` instance is the deployment step." Here it is: the
deployed `Dregg2.Finality.Tier` IS a `GradeAlgebra` — the LAUNDERING grade, an idempotent quantale
where `⊗ = ⊔ = max` (finality takes the WORST tier reached; it does not accumulate) and the unit is
`causal` (the weakest tier). Combined with `instProd` and the max-plus `ℕ` rent grade, the deployed
product grade `Tier × ℕ` (laundering × rent) is now a quantale for free — gpt5.5 §5, fully wired.
-/
import Metatheory.PolisGrade
import Metatheory.PolisGradeProduct
import Dregg2.Finality

namespace Metatheory.PolisGrade

open Dregg2.Finality

/-- `causal` is the least tier (rank 1 ≤ every rank). -/
theorem Tier.causal_le (a : Tier) : Tier.causal ≤ a := by cases a <;> decide

/-- The deployed **Finality.Tier laundering grade**: idempotent quantale, `⊗ = ⊔ = max`,
unit `causal`. (Finality severity takes the worst tier reached — it does not accumulate; that is
exactly the idempotent `⊗`.) -/
instance instTierGrade : GradeAlgebra Tier where
  le := (· ≤ ·)
  comp := max
  unit := Tier.causal
  join := max
  le_refl := le_refl
  le_trans := fun h₁ h₂ => le_trans h₁ h₂
  comp_unit := fun a => max_eq_right (Tier.causal_le a)
  comp_comm := fun a b => max_comm a b
  comp_assoc := fun a b c => max_assoc a b c
  comp_mono := fun b h => sup_le_sup_right h b
  join_le_left := le_max_left
  join_le_right := le_max_right
  join_lub := fun h₁ h₂ => max_le h₁ h₂
  comp_join := fun a b c => sup_sup_distrib_left a b c

/-! ### The deployed product grade `Tier × ℕ` (laundering × rent) is a quantale, for free. -/

/-- Laundering takes the worst tier (idempotent), rent accumulates (additive) — componentwise, via
`instProd`. A worse-finality+more-rent grade dominates. -/
example : GradeAlgebra.comp ((Tier.causal, 2) : Tier × Nat) (Tier.bft, 3)
        = (Tier.bft, 5) := by
  refine Prod.ext_iff.mpr ⟨?_, ?_⟩
  · show max Tier.causal Tier.bft = Tier.bft; exact max_eq_right (by decide)
  · show (2 : Nat) + 3 = 5; omega

/-- The laundering grade is genuinely idempotent: re-reaching `bft` does not escalate. -/
example : GradeAlgebra.comp (Tier.bft) (Tier.bft) = Tier.bft := max_self _

/-- … but it does take the worst on a join (a constitutional-tier event launders the grade up). -/
example : GradeAlgebra.join (Tier.causal) (Tier.constitutional) = Tier.constitutional :=
  max_eq_right (by decide)

end Metatheory.PolisGrade
