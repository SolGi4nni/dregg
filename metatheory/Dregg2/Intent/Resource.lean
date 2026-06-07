/-
# Dregg2.Intent.Resource — the resource-theory layer (Coecke–Fritz) + the convertibility preorder.

Phase 2, layer 1 (`docs/rebuild/PHASE-2-INTENT-SPEC.md`, `INTENT-REFS-resources.md`). The abstract
home of *what an intent's resources ARE and when one converts to another* — the substrate `Intent`
(face 1, the boundary) and `Match` (the solver) are built over.

**Coecke–Fritz–Spekkens, *A mathematical theory of resources* (arXiv 1409.5531) — two layers, never
conflated (`pdfs/LEARNINGS-laws-linear-monoidal.md`, correction C1):**

  * **Rich layer.** A resource theory IS a *symmetric monoidal category* `(R, ⊗, 𝟙_)`: objects =
    resources, morphisms = the *free* (zero-cost) conversions, `⊗` = "side by side", `𝟙_` = the void
    resource. LINEARITY (no value copied or destroyed — the conservation discipline) is encoded by
    *withholding* the cartesian copy/delete (`CartesianMonoidalCategory`'s `Δ`/`◇`): we require only
    `SymmetricCategory`, never the diagonal. The morphism `offered ⟶ wanted` you plug into an intent's
    hole is the *proof-relevant witness* — "to know `a` converts to `c` is to HOLD a conversion".

  * **Thin layer (Def 4.1).** Collapse each hom-set to "is there ANY conversion?":
    `a ⪰ c := Nonempty (a ⟶ c)`. This forgets WHICH conversion — the thin shadow. **It is exactly the
    intent-match relation:** an intent `a ⊢ c` is fillable iff `a ⪰ c`. The shadow is a preorder
    (reflexive by `𝟙`, transitive by `≫`) compatible with `⊗`.

This module: the `ResourceTheory` name (an SMC, with the linearity note), the convertibility preorder
`⪰` and its preorder + `⊗`-compatibility laws, and a concrete demo resource theory (asset bundles, the
auction carrier) exhibiting the relation's TEETH (an unequal want is unfillable). Conservation as a
monotone (a monoid-hom invariant) is Phase 3; the rich↔thin split is the home of that work.

Pure.
-/
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.Discrete
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Group.Nat.Defs

universe v u

namespace Dregg2.Intent

open CategoryTheory MonoidalCategory

/-! ## 1. `ResourceTheory` — a symmetric monoidal category (the rich layer). -/

/-- **A resource theory** (Coecke–Fritz–Spekkens): a symmetric monoidal category. Objects are
resources, morphisms the free conversions, `⊗` side-by-side, `𝟙_` the void resource. We name the
mathlib bundle (`Category` + `MonoidalCategory` + `SymmetricCategory`) so the rest of the intent stack
reads `[ResourceTheory R]`. LINEARITY is the *absence* of `CartesianMonoidalCategory` — we never assume
copy/delete, so no resource can be duplicated or silently dropped (the conservation discipline, made
structural). The thin convertibility preorder `⪰` (§2) is its shadow. -/
abbrev ResourceTheory (R : Type u) [Category.{v} R] [MonoidalCategory.{v} R] :=
  SymmetricCategory.{v} R

/-! ## 2. The convertibility preorder `⪰` = the intent-match relation (the thin shadow). -/

/-- **Convertibility** `a ⪰ c` (Coecke–Fritz Def 4.1): the resources `a` can be converted into the
outcome `c` — i.e. *some* free conversion exists. The THIN shadow of the rich hom (`Nonempty` forgets
*which* conversion). **This IS the match relation:** an intent `a ⊢ c` is fillable exactly when
`a ⪰ c`, witnessed by a morphism `a ⟶ c`. -/
def Converts {R : Type u} [Category.{v} R] (a c : R) : Prop := Nonempty (a ⟶ c)

@[inherit_doc] scoped infix:50 " ⪰ᵣ " => Converts

variable {R : Type u}

/-- Convertibility is reflexive: every resource converts to itself (the identity conversion). -/
theorem Converts.refl' [Category.{v} R] (a : R) : Converts a a := ⟨𝟙 a⟩

/-- Convertibility is transitive: chain the two conversions (`≫`). This is the bilateral shadow of the
multi-hop solver — `Match`'s coend (`Intent/Match.lean`) is the proof-relevant refinement that keeps
the intermediate object. -/
theorem Converts.trans [Category.{v} R] {a b c : R}
    (h₁ : Converts a b) (h₂ : Converts b c) : Converts a c :=
  h₁.elim fun f => h₂.elim fun g => ⟨f ≫ g⟩

/-- The convertibility preorder, bundled (reflexive + transitive). Provided as a `def` (NOT a global
`instance` — `R` already carries a `Category`, and a stray `Preorder R` instance would be ambiguous).
-/
@[reducible] def convertPreorder [Category.{v} R] : Preorder R where
  le a c := Converts a c
  le_refl := Converts.refl'
  le_trans _ _ _ := Converts.trans

/-- **Convertibility is `⊗`-monotone (compatible with side-by-side composition).** If `a ⪰ c` and
`b ⪰ d` then `a ⊗ b ⪰ c ⊗ d` — convert the two halves independently and tensor the conversions. This
is the monoidal-preorder law (the ordered-commutative-monoid shape of Coecke–Fritz's core layer): the
match relation respects bundling. -/
theorem Converts.tensor [Category.{v} R] [MonoidalCategory.{v} R] {a b c d : R}
    (h₁ : Converts a c) (h₂ : Converts b d) : Converts (a ⊗ b) (c ⊗ d) :=
  h₁.elim fun f => h₂.elim fun g => ⟨MonoidalCategory.tensorHom f g⟩

/-- A one-sided `⊗`-monotone corollary (whisker on the right): `a ⪰ c → a ⊗ b ⪰ c ⊗ b`. The held but
unconverted frame `b` (a catalyst / escrowed bond, Coecke–Fritz §4) rides along unchanged. -/
theorem Converts.tensorRight [Category.{v} R] [MonoidalCategory.{v} R] {a c : R}
    (h : Converts a c) (b : R) : Converts (a ⊗ b) (c ⊗ b) :=
  h.tensor (Converts.refl' b)

/-! ## 3. A concrete resource theory — asset bundles (the auction demo carrier).

The smallest honest instance. A resource is a BUNDLE: counts `(gold, art)` of two asset kinds, as a
multiplicative `CommMonoid` (so it hosts mathlib's `Discrete` symmetric monoidal structure; `*` =
bundle union, `1` = the empty bundle). In the DISCRETE category morphisms are equalities, so
convertibility is EXACT (a bundle converts only to itself). Minimal but genuinely two-sided:

  * a real fill exists (the identity conversion when `offered = wanted`);
  * TEETH — an unequal want is UNFILLABLE (`¬ Converts goldᴮ artᴮ`).

The Phase-4 auction sharpens this to an OFFER-generated category (non-identity conversions = the
market's standing offers), where `⪰` becomes nontrivial and the coend solver does real routing. -/

/-- A resource bundle: `(gold, art)` token counts, multiplicative so `Discrete` is (braided) monoidal
(`*` = pointwise `+` of counts = bundle union; `1` = the empty bundle). -/
abbrev Bundle := Multiplicative (ℕ × ℕ)

/-- Construct a bundle from explicit `(gold, art)` counts. -/
def mkBundle (gold art : ℕ) : Bundle := Multiplicative.ofAdd (gold, art)

/-- **DEMO (non-production): the demo resource theory** — the discrete symmetric monoidal category on
asset bundles. A two-asset `(gold, art)` TOY carrier for exercising the convertibility relation's teeth;
the real per-asset ledger it shadows is `Exec/RecordKernel.lean` (the bridge is `Intent/KernelBridge`).
NOT a shipped resource theory. -/
abbrev DemoRes := Discrete Bundle

/-- `DemoRes` is symmetric: mathlib gives `BraidedCategory (Discrete M)` for a `CommMonoid`; symmetry
of the braiding is free because `Discrete` hom-sets are subsingletons (`instSubsingletonDiscreteHom`).
This completes `DemoRes` as a `ResourceTheory`. -/
instance : SymmetricCategory DemoRes where
  toBraidedCategory := inferInstance
  symmetry _ _ := Subsingleton.elim _ _

/-- A bundle as a resource object of `DemoRes`. -/
def res (gold art : ℕ) : DemoRes := Discrete.mk (mkBundle gold art)

/-! ### Non-vacuity — the match relation has teeth. -/

/-- **A real conversion exists** (reflexivity, concretely): the bundle "2 gold" converts to itself —
the identity fill. -/
example : Converts (res 2 0) (res 2 0) := Converts.refl' _

/-- **TEETH (general): distinct bundles do not convert.** In the discrete resource theory a morphism
forces the underlying bundles equal, so unequal `(gold, art)` counts give no conversion — the
match-relation refuses. (The market's standing offers, Phase 4, are what add non-identity conversions.)
-/
theorem res_no_convert {g a g' a' : ℕ} (h : (g, a) ≠ (g', a')) :
    ¬ Converts (res g a) (res g' a') := by
  rintro ⟨f⟩
  -- a `Discrete` morphism forces the underlying objects equal; but `(g,a) ≠ (g',a')`.
  have he : (res g a).as = (res g' a').as := Discrete.eq_of_hom f
  simp only [res, mkBundle] at he
  exact absurd (Multiplicative.ofAdd.injective he) h

/-- "2 gold" does NOT convert to "1 art" — the canonical teeth witness. -/
theorem demo_no_convert : ¬ Converts (res 2 0) (res 0 1) := res_no_convert (by decide)

/-- **`⊗`-monotonicity is real on the demo:** bundling "1 gold" alongside both sides of the reflexive
conversion of "1 art" still converts. (The thin match relation respects side-by-side composition.) -/
example : Converts (res 1 0 ⊗ res 0 1) (res 1 0 ⊗ res 0 1) :=
  (Converts.refl' (res 1 0)).tensor (Converts.refl' (res 0 1))

end Dregg2.Intent
