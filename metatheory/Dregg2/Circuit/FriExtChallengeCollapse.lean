import Mathlib.Tactic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Algebra.Algebra.Basic
import Dregg2.Circuit.FriSoundness

/-!
# `FriExtChallengeCollapse` — for BASE-field words, ONE extension challenge forces correlated
agreement, at ANY radius

Deployed STARKs batch/fold **base-field** words (the committed trace columns are base-field
BabyBear values) with challenges drawn from a **degree-`r` extension**. This file proves that in
exactly that configuration the correlated-agreement question COLLAPSES:

> if a single challenge `α` outside the base field folds `u₀ + α·u₁` to within a support `T` of the
> extended code, then `u₀` and `u₁` are *each* that close to the base code, on the SAME set `Tᶜ`.

That is the correlated-agreement conclusion (a common agreement set for both words), obtained from
**one** challenge, with **no** Johnson / capacity / list-decoding hypothesis and **no** restriction
on the radius `|T|`.

## Why this matters for a counterexample search

The escape is precisely the base subfield: the hypothesis `SeparatingCoord` is satisfiable *only*
for `α ∉ K` (`separatingCoord_forces_not_base` — the canary below). So the set of challenges that
are good WITHOUT forcing correlated agreement is contained in `K ⊆ L`, of density `|K|/|L| = |K|^{1−r}`
— at the deployed BabyBear parameters (`|K| = 2³¹`, `r = 4`) that is `2^{−93}`. Any correlated-
agreement counterexample must therefore use genuinely **extension-valued** words; base-field words
are unconditionally fine at every radius.

⚠ Scope, stated honestly: this says nothing about words that are already extension-valued (in a
deployed prover, layers past the first batching step). It removes the base-field case from the
search space; it does not touch the open BCIKS line for extension-valued words
(`FriCorrelatedAgreementSharp.CorrelatedAgreementLine`), nor the incidence-design dichotomy of
`FriIncidenceDesign` which applies there.

The mechanism is a coordinate comparison: `u₀ y` and `u₁ y` are BASE scalars, so in an `L/K` basis
the fold's `j`-th coordinate reads `u₀ y · ⟨1⟩ⱼ + u₁ y · ⟨α⟩ⱼ`. At a coordinate `j` where `⟨1⟩ⱼ = 0`
but `⟨α⟩ⱼ ≠ 0` the `u₀` term vanishes, exposing `u₁` alone as a codeword coordinate; `u₀` then falls
out of any coordinate where `⟨1⟩ ≠ 0`.
-/

namespace Dregg2.Circuit.FriExtChallengeCollapse

open Dregg2.Circuit.FriSoundness

variable {K L : Type*} [Field K] [DecidableEq K] [Field L] [DecidableEq L] [Algebra K L]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {r : Type*} [DecidableEq r]

/-- The deployed shape: a base-field affine line `u₀ + α·u₁` evaluated with an EXTENSION challenge
`α`. (This is the batching/folding line with base-field committed words.) -/
def extFold (u₀ u₁ : κ → K) (α : L) : κ → L :=
  fun y => algebraMap K L (u₀ y) + algebraMap K L (u₁ y) * α

/-- The coordinate-wise extension of a base code `C` to `L`: a word over `L` is a codeword iff each
of its `L/K`-basis coordinate functions is a codeword of `C`. (For a free extension this is the
`L`-span of `C`.) -/
def extCode (b : Module.Basis r K L) (C : Submodule K (κ → K)) : Set (κ → L) :=
  {g | ∀ i, (fun y => b.repr (g y) i) ∈ C}

/-- **A separating coordinate for `α`** — a basis coordinate on which `1` vanishes but `α` does not.
This is precisely the statement that `α` is not a base scalar (see
`separatingCoord_forces_not_base` and `separatingCoord_of_ne_base`). -/
def SeparatingCoord (b : Module.Basis r K L) (α : L) (j : r) : Prop :=
  b.repr (1 : L) j = 0 ∧ b.repr α j ≠ 0

/-- The fold's basis coordinates, expanded: because `u₀ y, u₁ y` are BASE scalars they pass through
`b.repr` as plain field multiplications. This is the whole mechanism. -/
theorem repr_extFold (b : Module.Basis r K L) (u₀ u₁ : κ → K) (α : L) (y : κ) (i : r) :
    b.repr (extFold u₀ u₁ α y) i = u₀ y * b.repr (1 : L) i + u₁ y * b.repr α i := by
  have h1 : algebraMap K L (u₀ y) = u₀ y • (1 : L) := Algebra.algebraMap_eq_smul_one _
  have h2 : algebraMap K L (u₁ y) * α = u₁ y • α := (Algebra.smul_def _ _).symm
  simp only [extFold]
  rw [h1, h2, map_add, map_smul, map_smul]
  simp [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]

/-- **THE COLLAPSE.** A single good EXTENSION challenge forces correlated agreement, sharply and at
any radius: if the fold `u₀ + α·u₁` agrees with an extended codeword `g` off `T`, then `u₀` and `u₁`
each agree with a BASE codeword off the SAME `T`.

No Johnson bound, no capacity bound, no list-decoding hypothesis, no constraint on `T.card`. -/
theorem extChallenge_forces_correlatedAgreement (b : Module.Basis r K L) (C : Submodule K (κ → K))
    {u₀ u₁ : κ → K} {α : L} {j : r} (hsep : SeparatingCoord b α j)
    {g : κ → L} (hg : g ∈ extCode b C) {T : Finset κ}
    (hT : disagree (extFold u₀ u₁ α) g ⊆ T) :
    ∃ ge ∈ C, ∃ go ∈ C, disagree u₀ ge ⊆ T ∧ disagree u₁ go ⊆ T := by
  classical
  obtain ⟨h1j, hαj⟩ := hsep
  -- `1 ≠ 0`, so some coordinate `i` of `1` is nonzero; that is where `u₀` is read off.
  obtain ⟨i, h1i⟩ : ∃ i, b.repr (1 : L) i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have h0 : b.repr (1 : L) = 0 := by
      ext i; simpa using hcon i
    have hone : (1 : L) = 0 := by
      apply b.repr.injective
      rw [h0, map_zero]
    exact one_ne_zero hone
  -- the two reconstructed base codewords
  set go : κ → K := (b.repr α j)⁻¹ • (fun y => b.repr (g y) j) with hgo
  set ge : κ → K :=
    (b.repr (1 : L) i)⁻¹ • ((fun y => b.repr (g y) i) - (b.repr α i) • go) with hge
  have hgoC : go ∈ C := C.smul_mem _ (hg j)
  have hgeC : ge ∈ C := C.smul_mem _ (C.sub_mem (hg i) (C.smul_mem _ hgoC))
  -- off `T` the fold equals `g`, and the coordinates pin `u₁` then `u₀`
  have key : ∀ y ∉ T, u₁ y = go y ∧ u₀ y = ge y := by
    intro y hy
    have hfold : extFold u₀ u₁ α y = g y := by
      by_contra hcon
      exact hy (hT (mem_disagree.mpr hcon))
    -- coordinate `j`: the `u₀` term dies, exposing `u₁`
    have hj : u₁ y * b.repr α j = b.repr (g y) j := by
      have := repr_extFold b u₀ u₁ α y j
      rw [hfold] at this
      rw [h1j] at this
      simpa using this.symm
    have hu₁ : u₁ y = go y := by
      rw [hgo]
      simp only [Pi.smul_apply, smul_eq_mul]
      field_simp
      linear_combination hj
    -- coordinate `i`: `u₀` falls out once `u₁` is known
    have hi : u₀ y * b.repr (1 : L) i + u₁ y * b.repr α i = b.repr (g y) i := by
      have := repr_extFold b u₀ u₁ α y i
      rw [hfold] at this
      exact this.symm
    have hu₀ : u₀ y = ge y := by
      rw [hge]
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      rw [← hu₁]
      field_simp
      linear_combination hi
    exact ⟨hu₁, hu₀⟩
  refine ⟨ge, hgeC, go, hgoC, ?_, ?_⟩
  · intro y hy
    by_contra hyT
    exact (mem_disagree.mp hy) ((key y hyT).2)
  · intro y hy
    by_contra hyT
    exact (mem_disagree.mp hy) ((key y hyT).1)

/-! ## Teeth -/

/-- **CANARY — the hypothesis is EXACTLY extension-ness.** A separating coordinate can never exist
for a base scalar: if `α = algebraMap c` then `⟨α⟩ⱼ = c · ⟨1⟩ⱼ`, so `⟨1⟩ⱼ = 0` forces `⟨α⟩ⱼ = 0`.
Hence the collapse theorem says nothing about challenges in `K` — and that is not slack, it is the
真 boundary: the base subfield is precisely where a correlated-agreement counterexample must live. -/
theorem separatingCoord_forces_not_base (b : Module.Basis r K L) (c : K) (j : r) :
    ¬ SeparatingCoord b (algebraMap K L c) j := by
  rintro ⟨h1j, hαj⟩
  apply hαj
  have hc : algebraMap K L c = c • (1 : L) := Algebra.algebraMap_eq_smul_one _
  rw [hc, map_smul]
  simp [Finsupp.smul_apply, h1j]

/-- **FIRE (non-vacuity).** A separating coordinate exists whenever the basis contains `1` at some
index `i₀` and `α` has a nonzero coordinate elsewhere — i.e. for any genuinely non-base `α` in a
basis adapted to `1` (the standard power basis `1, x, x², …` of a field extension). -/
theorem separatingCoord_of_ne_base (b : Module.Basis r K L) {i₀ : r} (hb : b i₀ = 1) {α : L} {j : r}
    (hj : j ≠ i₀) (hαj : b.repr α j ≠ 0) : SeparatingCoord b α j := by
  refine ⟨?_, hαj⟩
  have h1 : b.repr (1 : L) = Finsupp.single i₀ 1 := by
    rw [← hb]; exact b.repr_self i₀
  have hne : i₀ ≠ j := fun h => hj h.symm
  rw [h1, Finsupp.single_apply]
  exact if_neg hne

#assert_axioms repr_extFold
#assert_axioms extChallenge_forces_correlatedAgreement
#assert_axioms separatingCoord_forces_not_base
#assert_axioms separatingCoord_of_ne_base

end Dregg2.Circuit.FriExtChallengeCollapse
