import Mathlib.Tactic
import Mathlib.Algebra.Polynomial.Roots
import Dregg2.Circuit.FriLdtJohnson

/-!
# `FriProximityGapChallenges` at `L > 1` — the BCIKS20 correlated-agreement / proximity-gap
core, reduced to a PRECISELY-NAMED witness polynomial and DISCHARGED at `L = 1` through it.

`FriLdtJohnson.lean` proves `FriProximityGapChallenges S dOut dIn L` at `L = 1`
(`proximityGap_uniqueDecoding`, which *is* `good_alpha_subsingleton`: a `4·dIn`-far word has
`≤ 1` good folding challenge). That is the *unique-decoding* endpoint, proved by the two-point
Vandermonde reconstruction (`fold_close_of_two_alpha`): the FRI fold `Fold α f = E f + α • O f`
is **affine in `α`**, so two good challenges already reconstruct a single codeword `4·dIn`-close
to `f`. The two-point argument caps the good set at `1` and gives no `L > 1` content on its own.

## What this file does.

BCIKS20's proximity gap for an affine line up to the list-decoding (Johnson) radius has the
shape the task names: **the set of "bad" challenges `α` — those whose fold `Fold α f` is
`dIn`-close to the folded code — is contained in the zero-set of a NONZERO polynomial of bounded
degree `≤ L`, hence has size `≤ L`.** This file makes that shape a theorem-generating machine:

* **§1 — the polynomial-method core (FULLY CLOSED, Mathlib).** `good_set_card_le_of_poly`: a set
  contained in the roots of a nonzero `P : F[X]` embeds in a finset of card `≤ P.natDegree`
  (`Polynomial.card_roots'` + `Multiset.toFinset_card_le`). This is the entire quantitative
  content of "bad set bounded by degree".

* **§2 — the named primitive + the reduction (FULLY CLOSED).** `BadChallengePoly S dOut dIn L`
  is the BCIKS20 witness: every `dOut`-far word `f` has a nonzero degree-`≤ L` polynomial `P_f`
  whose roots contain the good-challenge set. `friProximityGap_of_badChallengePoly` derives
  `FriProximityGapChallenges S dOut dIn L` from it, for ANY `L`, via §1.

* **§3 — non-vacuity: the deployed `L = 1` result flows THROUGH the framework.**
  `badChallengePoly_uniqueDecoding` proves `BadChallengePoly S (4·d) d 1` from
  `good_alpha_subsingleton` (empty good set ↦ `P = 1`; singleton `{a}` ↦ `P = X − C a`), and
  `proximityGap_uniqueDecoding_via_poly` re-derives the committed `L = 1` proximity gap purely
  through `friProximityGap_of_badChallengePoly`. So the polynomial-witness framework SUBSUMES the
  deployed unique-decoding bound — it is precisely scoped, not vacuous.

* **§4 — the exact remaining lemma, named as a Lean statement.** The genuine BCIKS20 content
  (`L > 1`, `dOut` up to the Johnson radius `δ_J = 1 − √ρ`) is exactly
  `BadChallengePoly S dOut dIn L` at those parameters: *construct the correlated-agreement witness
  polynomial.* That construction — the one piece Mathlib lacks — is stated, not faked.

No `axiom`, no `sorry`, no `def …Hard` smuggled as a hypothesis. `#assert_axioms` ⊆
{propext, Classical.choice, Quot.sound} throughout. Discharging §4's `BadChallengePoly` at the
Johnson radius (together with `RSListBound` at `L > 1`) drops deployed STARK soundness to `HashCR`.
-/

namespace Dregg2.Circuit.FriProximityGapListDecoding

open Dregg2.Circuit.FriSoundness
open Dregg2.Circuit.FriLdtJohnson
open Polynomial

variable {F : Type*} [Field F] [DecidableEq F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-! ## §1. The polynomial-method core — a root-bounded set is degree-bounded.

The single quantitative fact behind every proximity-gap bound: over an integral domain (here a
field), a set of points on which a NONZERO polynomial `P` vanishes has at most `deg P` elements,
because it embeds in `P.roots.toFinset`. This is `Polynomial.card_roots'` phrased as the finset
cover that `FriProximityGapChallenges` asks for. -/

/-- **The bad-set degree bound.** If `s` is contained in the zero-set of a nonzero polynomial `P`,
then `s` is covered by a finset of card `≤ P.natDegree`. This is exactly the `∃ finset, card ≤ …`
shape of `FriProximityGapChallenges`, with the bound supplied by the polynomial's degree. -/
theorem good_set_card_le_of_poly (P : F[X]) (hP : P ≠ 0) (s : Set F)
    (hs : s ⊆ {α : F | P.eval α = 0}) :
    ∃ t : Finset F, t.card ≤ P.natDegree ∧ s ⊆ ↑t := by
  refine ⟨P.roots.toFinset, ?_, ?_⟩
  · calc P.roots.toFinset.card ≤ Multiset.card P.roots := Multiset.toFinset_card_le _
      _ ≤ P.natDegree := Polynomial.card_roots' P
  · intro α hα
    have hroot : P.IsRoot α := hs hα
    rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hP]
    exact hroot

/-! ## §2. The named BCIKS20 primitive and the reduction to `FriProximityGapChallenges`.

`BadChallengePoly` packages the correlated-agreement witness: for every far word `f`, a nonzero
degree-`≤ L` polynomial `P_f` in the challenge variable whose roots contain the good-challenge set
`{α | Fold α f is dIn-close to C'}`. Given that witness, the proximity gap at list bound `L` is a
corollary of §1 — for ANY `L`, with NO extra hypothesis. -/

/-- **The BCIKS20 witness primitive.** A `dOut`-far word `f` admits a nonzero polynomial `P_f` of
degree `≤ L` in the folding challenge, whose zero-set contains every good challenge (each `α` whose
fold `Fold S.geom α f` is `dIn`-close to the folded code `S.C'`). This is the correlated-agreement
content of BCIKS20: the good challenges are the roots of a low-degree witness. -/
def BadChallengePoly (S : FriSetup F ι κ) (dOut dIn L : ℕ) : Prop :=
  ∀ {f : ι → F}, farN S.C dOut f →
    ∃ P : F[X], P ≠ 0 ∧ P.natDegree ≤ L ∧
      {α : F | closeN S.C' dIn (Fold S.geom α f)} ⊆ {α : F | P.eval α = 0}

/-- **THE REDUCTION.** The BCIKS20 witness polynomial (of degree `≤ L`) yields the proximity gap
at list bound `L`: the good-challenge set is covered by `P_f.roots.toFinset`, of card
`≤ P_f.natDegree ≤ L`. Holds for EVERY `L` — this is where "`L > 1`" is discharged, once the
witness of §4 is supplied. -/
theorem friProximityGap_of_badChallengePoly (S : FriSetup F ι κ) (dOut dIn L : ℕ)
    (h : BadChallengePoly S dOut dIn L) :
    FriProximityGapChallenges S dOut dIn L := by
  intro f hfar
  obtain ⟨P, hP, hdeg, hsub⟩ := h hfar
  obtain ⟨t, hcard, hts⟩ := good_set_card_le_of_poly P hP _ hsub
  exact ⟨t, le_trans hcard hdeg, hts⟩

/-! ## §3. Non-vacuity — the deployed `L = 1` proximity gap flows THROUGH the witness framework.

The committed unique-decoding bound is not merely *compatible* with the polynomial framing: it is
recovered by EXHIBITING the witness. A `4d`-far word has a subsingleton good set
(`good_alpha_subsingleton`); an empty good set is witnessed by `P = 1` (degree `0`, no roots) and a
singleton `{a}` by `P = X − C a` (degree `1`, sole root `a`). So `BadChallengePoly S (4d) d 1`
holds, and re-running the reduction reproduces `proximityGap_uniqueDecoding` — certifying the
`L > 1` residual of §4 is a genuine generalization of a proved theorem, not opaque hardness. -/

/-- **`BadChallengePoly` at `L = 1`, at the unique-decoding radius — a THEOREM.** The witness is
constructed explicitly from `good_alpha_subsingleton`: `P = 1` when no challenge is good, `P = X − C a`
when the sole good challenge is `a`. This certifies the primitive is inhabited and precisely scoped. -/
theorem badChallengePoly_uniqueDecoding (S : FriSetup F ι κ) (d : ℕ) :
    BadChallengePoly S (4 * d) d 1 := by
  intro f hfar
  have hss := good_alpha_subsingleton S (d := d) hfar
  rcases hss.eq_empty_or_singleton with hemp | ⟨a, hsing⟩
  · -- No good challenge: the constant witness `P = 1` (degree 0, empty root-set).
    refine ⟨1, one_ne_zero, by simp, ?_⟩
    rw [hemp]; exact Set.empty_subset _
  · -- Sole good challenge `a`: the witness `P = X − C a` (degree 1, root-set `{a}`).
    refine ⟨X - C a, X_sub_C_ne_zero a, (natDegree_X_sub_C a).le, ?_⟩
    rw [hsing]
    intro α hα
    rw [Set.mem_singleton_iff] at hα
    subst hα
    show (X - C α).eval α = 0
    simp

/-- **The committed `L = 1` proximity gap, re-derived THROUGH the witness framework.** Identical
conclusion to `FriLdtJohnson.proximityGap_uniqueDecoding`, but routed entirely through
`friProximityGap_of_badChallengePoly` and `badChallengePoly_uniqueDecoding` — so the polynomial-
witness reduction is shown to subsume the deployed unique-decoding bound. -/
theorem proximityGap_uniqueDecoding_via_poly (S : FriSetup F ι κ) (d : ℕ) :
    FriProximityGapChallenges S (4 * d) d 1 :=
  friProximityGap_of_badChallengePoly S (4 * d) d 1 (badChallengePoly_uniqueDecoding S d)

/-! ## §4. The exact remaining lemma, as a Lean statement.

Everything above is unconditional. The genuine BCIKS20 correlated-agreement content — the piece
Mathlib lacks — is now a single, precisely-typed obligation:

  **Construct the witness.** For a word `f` that is `dOut`-far from the domain code with `dOut`
  up to the Johnson radius `δ_J = 1 − √ρ` (`dOut < 4·dIn`, past unique decoding), produce a nonzero
  polynomial `P_f : F[X]` of degree `≤ L` whose zero-set contains `{α | Fold α f is dIn-close to C'}`.

That obligation is exactly `BadChallengePoly S dOut dIn L` at Johnson-radius `dOut` and `L > 1`.
`friProximityGap_of_badChallengePoly` turns any proof of it into `FriProximityGapChallenges` at that
`L`. The `L = 1` instance (`badChallengePoly_uniqueDecoding`) is proved; the `L > 1` instance is the
BCIKS20 witness construction, named here as the terminal residual:

  `theorem bciks20_witness {…} (S : FriSetup F ι κ) (dOut dIn L : ℕ)`
  `    (hJohnson : «dOut up to δ_J») (hL : «L = BCIKS20 degree bound for dOut, dIn») :`
  `    BadChallengePoly S dOut dIn L`

No `sorry` stands in for it: it is left as an explicit named `Prop` (`BadChallengePoly`), to be
discharged by the correlated-agreement polynomial construction, exactly as `RSListBound` at `L > 1`
is left as the Johnson list bound. Discharging both drops deployed STARK soundness to `HashCR`. -/

/-! ## §5. Axiom hygiene. -/

#assert_axioms good_set_card_le_of_poly
#assert_axioms friProximityGap_of_badChallengePoly
#assert_axioms badChallengePoly_uniqueDecoding
#assert_axioms proximityGap_uniqueDecoding_via_poly

end Dregg2.Circuit.FriProximityGapListDecoding
