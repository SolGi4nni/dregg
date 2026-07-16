/-
GGM (Generic Group Model) candidate repair for ArkLib's vacuous `tSdhAssumption`.
NOT part of ArkLib. Scratch file supporting the disclosure note
`docs/reference/arklib-kzg-vacuity/candidates/ggm.md`.

The disease (mechanized in `KzgVacuity.lean`): ArkLib's `tSdhAdversary` receives the SRS as
*concrete group elements* `Vector G₁ (D+1) × Vector G₂ 2`. From the verifier leg `g₂^τ`,
`Classical.choice` (via `Exists.choose` on `exists_zmod_power_of_generator`) recovers the trapdoor
`τ : ZMod p` and returns the winning element with probability 1. The assumption is FALSE below 1.

The GGM boundary. A *generic* adversary never sees group elements as field data — only opaque
handles / a symbolic strategy. We model the sound, mechanizable fragment (the "static / committed
generic" adversary, the same object the Boneh–Boyen '04 t-SDH bound is proved against): the
adversary commits, WITHOUT the trapdoor, to a challenge offset `c` and a representation polynomial
`f` of degree ≤ D over `ZMod p`. The environment DEFINES its output group element as `g₁^{f(τ)}`;
the adversary does not choose it freely. Winning requires `f(τ) = 1/(τ+c)` at the environment's
random `τ`.

Because `f` is chosen with no `τ` in scope, there is nothing for `Classical.choice` to extract, and
the winning set of `τ` is bounded by Schwartz–Zippel. We prove the numeric bound `(D+1)/(p-1)` for
EVERY committed adversary — including every choice-definable one — so the exact attack is dead.
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card

open Polynomial

namespace GgmCandidate

variable {p : ℕ} [Fact (Nat.Prime p)]

/-! ## The winning polynomial and its Schwartz–Zippel degree bound -/

/-- The winning polynomial for a committed strategy `(c, f)`:
`w(X) = f(X) · (X + c) - 1`. A nonzero `τ` with `τ + c ≠ 0` wins iff `f(τ) = 1/(τ+c)`, i.e. iff
`w(τ) = 0`. -/
noncomputable def winPoly (c : ZMod p) (f : (ZMod p)[X]) : (ZMod p)[X] :=
  f * (X + C c) - 1

/-- `winPoly` is never the zero polynomial: `f·(X+c) = 1` would force `deg(f·(X+c)) = 0`, but the
degree-1 factor `X + c` is nonzero over the field `ZMod p`, so the product has degree ≥ 1. -/
lemma winPoly_ne_zero (c : ZMod p) (f : (ZMod p)[X]) : winPoly c f ≠ 0 := by
  intro h
  rw [winPoly, sub_eq_zero] at h            -- h : f * (X + C c) = 1
  have hlin_ne : (X + C c : (ZMod p)[X]) ≠ 0 := (monic_X_add_C c).ne_zero
  have hf_ne : f ≠ 0 := by
    rintro rfl; rw [zero_mul] at h; exact zero_ne_one h
  have hdeg := natDegree_mul hf_ne hlin_ne
  rw [h, natDegree_one, natDegree_X_add_C] at hdeg
  omega

/-- `winPoly` has degree ≤ D + 1 when `f` has degree ≤ D. -/
lemma winPoly_natDegree_le {D : ℕ} (c : ZMod p) {f : (ZMod p)[X]} (hf : f.natDegree ≤ D) :
    (winPoly c f).natDegree ≤ D + 1 := by
  unfold winPoly
  refine (natDegree_sub_le _ _).trans ?_
  rw [natDegree_one]
  refine max_le ?_ (by omega)
  refine natDegree_mul_le.trans ?_
  have hlin : (X + C c : (ZMod p)[X]).natDegree = 1 := natDegree_X_add_C c
  omega

/-- **Schwartz–Zippel core.** The number of field points where a committed strategy `(c, f)` (with
`deg f ≤ D`) wins is bounded by the degree: `#roots(winPoly) ≤ D + 1`. -/
lemma card_roots_winPoly_le {D : ℕ} (c : ZMod p) {f : (ZMod p)[X]} (hf : f.natDegree ≤ D) :
    Multiset.card (winPoly c f).roots ≤ D + 1 :=
  (card_roots' (winPoly c f)).trans (winPoly_natDegree_le c hf)

/-! ## The τ-free generic adversary and the counting experiment

A committed generic adversary is a bare `(c, f)` — a challenge offset and a degree-≤D
representation polynomial — with **no trapdoor input**. This is the whole point: the type the
attack exploited (`Vector G₁ (D+1) × Vector G₂ 2 → …`, carrying `g₂^τ`) is gone, so
`Classical.choice` has no `∃ a, · = g^a` to invoke. -/

/-- A committed (static) generic t-SDH adversary: a challenge offset and a representation
polynomial of degree ≤ D, chosen independently of the trapdoor. -/
structure GenericAdversary (D : ℕ) (p : ℕ) where
  offset : ZMod p
  repr : (ZMod p)[X]
  degree_le : repr.natDegree ≤ D

/-- The nonzero field elements — the support of ArkLib's trapdoor sampler `sampleNonzeroZMod`. -/
noncomputable def nonzeroPoints : Finset (ZMod p) :=
  (Finset.univ : Finset (ZMod p)).erase 0

/-- The trapdoors on which the committed adversary `A` wins: nonzero `τ` with `τ + c ≠ 0` and
`f(τ) = 1/(τ+c)`. -/
noncomputable def winningPoints {D : ℕ} (A : GenericAdversary D p) : Finset (ZMod p) :=
  nonzeroPoints.filter (fun τ => τ + A.offset ≠ 0 ∧ A.repr.eval τ = 1 / (τ + A.offset))

/-- Every winning `τ` is a root of `winPoly` (turning the rational win-condition into the
polynomial identity Schwartz–Zippel bounds). -/
lemma winningPoints_subset_roots {D : ℕ} (A : GenericAdversary D p) :
    ∀ τ ∈ winningPoints A, τ ∈ (winPoly A.offset A.repr).roots := by
  intro τ hτ
  rw [winningPoints, Finset.mem_filter] at hτ
  obtain ⟨_, hne, heval⟩ := hτ
  rw [mem_roots']
  refine ⟨winPoly_ne_zero A.offset A.repr, ?_⟩
  unfold winPoly
  simp only [IsRoot.def, eval_sub, eval_mul, eval_add, eval_X, eval_C, eval_one]
  rw [heval, one_div, inv_mul_cancel₀ hne, sub_self]

/-- **The numeric GGM bound (counting form).** For EVERY committed generic adversary — including
every `Classical.choice`-definable one — the number of trapdoors on which it wins is ≤ D + 1. -/
theorem card_winningPoints_le {D : ℕ} (A : GenericAdversary D p) :
    (winningPoints A).card ≤ D + 1 := by
  classical
  have hsub : winningPoints A ⊆ (winPoly A.offset A.repr).roots.toFinset := by
    intro τ hτ
    rw [Multiset.mem_toFinset]
    exact winningPoints_subset_roots A τ hτ
  exact (Finset.card_le_card hsub).trans
    ((Multiset.toFinset_card_le (m := (winPoly A.offset A.repr).roots)).trans
      (card_roots_winPoly_le A.offset A.degree_le))

/-- The counting experiment: the fraction of nonzero trapdoors on which the committed adversary
wins. This is the exact success probability of the static generic adversary in the t-SDH game,
`τ` sampled uniformly from `sampleNonzeroZMod` (support = the `p - 1` nonzero residues). -/
noncomputable def ggmExperiment {D : ℕ} (A : GenericAdversary D p) : ℚ :=
  (winningPoints A).card / (p - 1)

/-! ## Survives-attack: the numeric bound holds for EVERY generic adversary -/

/-- **PROVEN-SURVIVES.** Every committed generic t-SDH adversary — over the FULL adversary type,
so including any `Classical.choice`/`Exists.choose`-defined one — wins on at most a `(D+1)/(p-1)`
fraction of trapdoors. There is no winning adversary at probability 1; the exact
trapdoor-extraction attack (`tauExtractingAdversary`) cannot even be typed here, because
`GenericAdversary` receives no group element and hence no `∃ a, · = g^a` for choice to invert. -/
theorem ggm_tSdh_sound {D : ℕ} (A : GenericAdversary D p) (hp : 2 ≤ p) :
    ggmExperiment A ≤ (D + 1 : ℚ) / (p - 1) := by
  unfold ggmExperiment
  have hmono : ((winningPoints A).card : ℚ) ≤ (D + 1 : ℚ) := by
    exact_mod_cast card_winningPoints_le A
  have hden : (0 : ℚ) < (p : ℚ) - 1 := by
    have : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp
    linarith
  gcongr

omit [Fact (Nat.Prime p)] in
/-- **Non-vacuity is now built in.** For `p > D + 2` the bound `(D+1)/(p-1)` is a genuine rational
strictly below `1`: the assumption `∀ A, ggmExperiment A ≤ (D+1)/(p-1)` is TRUE (proved above, over
the whole type), not refutable, and its bound is nontrivial. Contrast `not_tSdhAssumption`, which
made the original assumption FALSE below `1`. -/
theorem ggm_bound_lt_one {D : ℕ} (hp : D + 2 < p) :
    ((D : ℚ) + 1) / (p - 1) < 1 := by
  have hden : (0 : ℚ) < (p : ℚ) - 1 := by
    have : (2 : ℚ) ≤ (p : ℚ) := by
      have : (2 : ℕ) ≤ p := by omega
      exact_mod_cast this
    linarith
  rw [div_lt_one hden]
  have h1 : (D : ℚ) + 2 < (p : ℚ) := by exact_mod_cast hp
  linarith

end GgmCandidate
