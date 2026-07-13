import Mathlib.Tactic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import Dregg2.Circuit.FriProximityGapWitness

/-!
# `WrapCorrelatedAgreementSharp` — the δ-PRESERVING (Johnson-radius) residual, REDUCED to the
BCIKS20 affine-line correlated-agreement primitive, and the primitive NAMED as a Lean `Prop`.

`FriProximityGapWitness.lean` pushed the Fisher/packing method to its exact ceiling:
`wrap_badChallengePoly_johnson` proves `BadChallengePoly friSetupWrapRate 112 42 26` — `L = 26` at
the Johnson OUTER radius `dOut = 112` but with `dIn = 42` (relative `21/32`), NOT the folded code's
own Johnson radius `dIn = 56` (relative `7/8`). The obstruction is arithmetic and sharp: the packing
quadratic `a² > n·M` (`a = 64 − dIn`, `n = 64`, `M = 7`) FAILS for `dIn ≥ 43` (`a ≤ 21`,
`a² ≤ 441 < 448`). So the packing radius is *dead* at `dIn = 56` (`a = 8`, `a² = 64 ≪ 448`):
farness degrades across the fold (`7/8 → 21/32`) rather than being δ-preserved (`7/8 → 7/8`).

That named residual is `WrapCorrelatedAgreementSharp L := BadChallengePoly friSetupWrapRate 112 56 L`
(`FriProximityGapWitness.lean §F`). This file does not fake it. It does two honest things.

## §1. The exact remaining primitive, NAMED (`CorrelatedAgreementLine`).

BCIKS20's *correlated agreement for an affine line* over a code `C'`: viewing the FRI fold
`Fold α f = E f + α·O f` as the affine line `{u + α·v}` (`u = E f`, `v = O f`) of functions on the
folded domain, if MORE than `L` challenges `α` fold `f` to within `dIn` of `C'`, then there is a
SINGLE common agreement — codewords `ge, go ∈ C'` and a set of fibers `S` with
`|S| ≥ |κ| − dIn` on which `E f = ge` and `O f = go` SIMULTANEOUSLY. The threshold `|κ| − dIn` is the
**δ-preserving** (relative `1 − δ`) agreement — the sharp BCIKS20 statement, beyond the packing reach.
`CorrelatedAgreementLineAt S dIn L agree` carries the agreement threshold as a parameter so the
δ-preserving version (`agree = |κ| − dIn`) and the two-point version (`agree = |κ| − 2·dIn`) share one
shape.

This primitive is NOT assumed anywhere in the deployed chain (which consumes
`wrap_friProximityGap_johnson`, a theorem). It is stated so the residual is a Lean `Prop`, not prose.

## §2. The REDUCTION (`sharp_of_correlatedAgreementLine`) — a THEOREM, no `sorry`.

`CorrelatedAgreementLine friSetupWrapRate 56 L → WrapCorrelatedAgreementSharp L`. The mechanism is
the deployed dimension-`2` collapse already proved in `FriProximityGapWitness.lean`: on the wrap
setup `C'` is the CONSTANTS, so the correlated-agreement codewords are `ge = const a`, `go = const b`,
and their common agreement set is EXACTLY `Φ⁻¹(a, b) = {y | E f y = a ∧ O f y = b}`. δ-preservation
forces `|Φ⁻¹(a,b)| ≥ 64 − 56 = 8`, but `far_fiber_card` / `wrap_fiber_le_seven` cap it at
`(128 − 112 − 1)/2 = 7` for a `112`-far word. `8 ≤ 7` is absurd, so the good set has `≤ L` elements —
and the BCIKS20 witness polynomial `∏_{α good}(X − C α)` (nonzero, degree `≤ L`) is exhibited exactly
as in `wrap_badChallengePoly_johnson`. This is where the sharp `7/8 → 7/8` δ-preservation lives: the
one place `far_fiber_card`'s `M = 7` *beats* the `δ = 7/8` agreement floor of `8`.

## §3. Non-vacuity / genuine-strengthening certificate (`correlatedAgreementLineAt_twoPoint`).

The primitive is not a black box: at `L = 1` its WEAK form (`agree = |κ| − 2·dIn`) is a THEOREM,
proved by the BBHR18 two-point reconstruction (the same Vandermonde solve behind
`fold_close_of_two_alpha`): two good challenges pin `E f = Ge`, `O f = Go` off the union of the two
disagreement sets, giving common agreement on `≥ |κ| − 2·dIn` fibers with `Ge, Go ∈ C'`. So the
`∃ ge go, agree ≤ …` SHAPE is inhabited and provable; the SOLE gap to the sharp statement is the
strengthening of the agreement floor from `|κ| − 2·dIn` (two-point) to `|κ| − dIn` (δ-preserving) —
which is precisely BCIKS20's correlated-agreement content, and precisely what is left open, named,
and NOT `sorry`'d.

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; no `axiom`, no `sorry`.
-/

namespace Dregg2.Circuit.FriCorrelatedAgreementSharp

open Dregg2.Circuit.FriSoundness
open Dregg2.Circuit.FriLdtJohnson
open Dregg2.Circuit.FriProximityGapListDecoding
open Dregg2.Circuit.FriProximityGapWitness
open Dregg2.Circuit.BabyBearFriDeployed
open Dregg2.Circuit.BabyBearFriField (BabyBear)
open Dregg2.Circuit.BabyBearFriDeployedInstance (friSetupWrapRate)
open Polynomial
open scoped BigOperators

variable {F : Type*} [Field F] [DecidableEq F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-! ## §1. The named BCIKS20 affine-line correlated-agreement primitive. -/

/-- **BCIKS20 correlated agreement for the FRI affine line, at agreement floor `agree`.** If more
than `L` folding challenges `α` fold `f` to within `dIn` of the folded code `C'`, then a SINGLE pair
of folded codewords `ge, go ∈ C'` agrees with `(E f, O f)` on at least `agree` fibers SIMULTANEOUSLY.

The δ-preserving (sharp) instance is `agree = |κ| − dIn`; the two-point (unique-decoding) instance is
`agree = |κ| − 2·dIn` (`§3`). -/
def CorrelatedAgreementLineAt (S : FriSetup F ι κ) (dIn L agree : ℕ) : Prop :=
  ∀ {f : ι → F} (Good : Finset F),
    (∀ α ∈ Good, closeN S.C' dIn (Fold S.geom α f)) → L < Good.card →
    ∃ ge ∈ S.C', ∃ go ∈ S.C',
      agree ≤
        (Finset.univ.filter (fun y : κ => E S.geom f y = ge y ∧ O S.geom f y = go y)).card

/-- **The δ-PRESERVING correlated-agreement primitive** — the sharp BCIKS20 statement: the common
agreement set is of relative size `1 − δ` (`|κ| − dIn` fibers), matching the OUTER far-ness's relative
size. This is the exact content beyond the packing quadratic's `21/32` reach. -/
def CorrelatedAgreementLine (S : FriSetup F ι κ) (dIn L : ℕ) : Prop :=
  CorrelatedAgreementLineAt S dIn L (Fintype.card κ - dIn)

/-! ## §3 (stated first — the non-vacuity certificate). The two-point reconstruction gives the WEAK
agreement floor `|κ| − 2·dIn`, so the primitive's `∃ ge go, agree ≤ …` shape is inhabited. -/

/-- **Two good challenges reconstruct a common agreement set of `≥ |κ| − 2·dIn` fibers.** The BBHR18
Vandermonde solve (as in `fold_close_of_two_alpha`): off the union `T` of the two disagreement sets
(`|T| ≤ 2·dIn`), the fold equations `E f + αᵢ·O f = gᵢ` pin `E f = Ge`, `O f = Go`, with
`Ge, Go ∈ C'` the reconstructed folded codewords. So `Tᶜ` (of card `≥ |κ| − 2·dIn`) lies in the
common agreement set. -/
theorem correlatedAgreementLine_twoPoint (S : FriSetup F ι κ) {f : ι → F} {α₁ α₂ : F}
    (hα : α₁ ≠ α₂) {d : ℕ}
    (h1 : closeN S.C' d (Fold S.geom α₁ f)) (h2 : closeN S.C' d (Fold S.geom α₂ f)) :
    ∃ ge ∈ S.C', ∃ go ∈ S.C',
      Fintype.card κ - 2 * d ≤
        (Finset.univ.filter (fun y : κ => E S.geom f y = ge y ∧ O S.geom f y = go y)).card := by
  classical
  obtain ⟨g₁, hg₁, hc₁⟩ := h1
  obtain ⟨g₂, hg₂, hc₂⟩ := h2
  set G := S.geom with hG
  have hne : α₁ - α₂ ≠ 0 := sub_ne_zero.mpr hα
  set inv : F := (α₁ - α₂)⁻¹ with hinv
  set Go : κ → F := inv • (g₁ - g₂) with hGo
  set Ge : κ → F := inv • (α₁ • g₂ - α₂ • g₁) with hGe
  have hGoC : Go ∈ S.C' := S.C'.smul_mem _ (S.C'.sub_mem hg₁ hg₂)
  have hGeC : Ge ∈ S.C' :=
    S.C'.smul_mem _ (S.C'.sub_mem (S.C'.smul_mem _ hg₂) (S.C'.smul_mem _ hg₁))
  set T : Finset κ := disagree (Fold G α₁ f) g₁ ∪ disagree (Fold G α₂ f) g₂ with hT
  refine ⟨Ge, hGeC, Go, hGoC, ?_⟩
  -- `Tᶜ` lies in the common agreement set.
  have hkey : Tᶜ ⊆ Finset.univ.filter (fun y : κ => E G f y = Ge y ∧ O G f y = Go y) := by
    intro y hy
    rw [Finset.mem_compl, hT, Finset.mem_union, not_or] at hy
    obtain ⟨hy1, hy2⟩ := hy
    have e1 : E G f y + α₁ * O G f y = g₁ y := by
      have h := hy1; rw [mem_disagree, not_not] at h; simpa [Fold] using h
    have e2 : E G f y + α₂ * O G f y = g₂ y := by
      have h := hy2; rw [mem_disagree, not_not] at h; simpa [Fold] using h
    have hGoy : Go y = inv * (g₁ y - g₂ y) := by
      simp only [hGo, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    have hGey : Ge y = inv * (α₁ * g₂ y - α₂ * g₁ y) := by
      simp only [hGe, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · rw [hGey, hinv, inv_mul_eq_div, eq_div_iff hne]
      linear_combination α₁ * e2 - α₂ * e1
    · rw [hGoy, hinv, inv_mul_eq_div, eq_div_iff hne]
      linear_combination e1 - e2
  -- `|T| ≤ 2d`, so `|Tᶜ| = |κ| − |T| ≥ |κ| − 2d`, and the agreement set is even bigger.
  have hTcard : T.card ≤ 2 * d := by
    rw [hT]
    calc (disagree (Fold G α₁ f) g₁ ∪ disagree (Fold G α₂ f) g₂).card
        ≤ (disagree (Fold G α₁ f) g₁).card + (disagree (Fold G α₂ f) g₂).card :=
          Finset.card_union_le _ _
      _ ≤ 2 * d := by omega
  have hcompl : Tᶜ.card = Fintype.card κ - T.card := by rw [Finset.card_compl]
  calc Fintype.card κ - 2 * d
      ≤ Tᶜ.card := by rw [hcompl]; omega
    _ ≤ _ := Finset.card_le_card hkey

/-- **The primitive is inhabited at `L = 1` with the WEAK (two-point) agreement floor.** This
certifies the `∃ ge go, agree ≤ …` shape is provable — the sole gap to the sharp `CorrelatedAgreementLine`
is the strengthening of the floor from `|κ| − 2·dIn` to `|κ| − dIn`, i.e. exactly δ-PRESERVATION. -/
theorem correlatedAgreementLineAt_twoPoint (S : FriSetup F ι κ) (dIn : ℕ) :
    CorrelatedAgreementLineAt S dIn 1 (Fintype.card κ - 2 * dIn) := by
  intro f Good hGood hcard
  obtain ⟨α₁, hα₁, α₂, hα₂, hne⟩ := Finset.one_lt_card.mp hcard
  exact correlatedAgreementLine_twoPoint S hne (hGood α₁ hα₁) (hGood α₂ hα₂)

/-! ## §2. The REDUCTION: the δ-preserving primitive discharges `WrapCorrelatedAgreementSharp`. -/

/-- **The good-challenge card bound at the SHARP inner radius, from correlated agreement.** Given the
δ-preserving line-correlated-agreement primitive at `dIn = 56`, a `112`-far word has at most `L`
folding challenges whose fold is `56`-close to the constants. The contradiction is the deployed
dimension-`2` collapse: correlated agreement would force `≥ 8` fibers onto a single point `(a, b)` of
`F²`, but `wrap_fiber_le_seven` caps that at `7`. -/
theorem wrap_good_challenge_card_le_sharp {f : Fin (2 ^ 7) → BabyBear} {L : ℕ}
    (hCA : CorrelatedAgreementLine friSetupWrapRate 56 L)
    (hfar : farN friSetupWrapRate.C 112 f)
    (Good : Finset BabyBear)
    (hGood : ∀ α ∈ Good, closeN friSetupWrapRate.C' 56 (Fold friSetupWrapRate.geom α f)) :
    Good.card ≤ L := by
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨ge, hge, go, hgo, hbig⟩ := hCA Good hGood hcon
  obtain ⟨a, rfl⟩ := mem_wrap_C'.mp hge
  obtain ⟨b, rfl⟩ := mem_wrap_C'.mp hgo
  have hle7 := wrap_fiber_le_seven hfar a b
  have hn : Fintype.card (Fin (2 ^ 6)) = 64 := by simp
  -- `hbig : |κ| − 56 ≤ |Φ⁻¹(a,b)|`; beta-reduce the constants `(fun _ => a) y ↦ a`.
  simp only at hbig
  rw [hn] at hbig
  omega

/-- **THE REDUCTION — `WrapCorrelatedAgreementSharp L` from the BCIKS20 line primitive.**
`CorrelatedAgreementLine friSetupWrapRate 56 L → BadChallengePoly friSetupWrapRate 112 56 L`. For a
`112`-far `f` the good set has card `≤ L` (`wrap_good_challenge_card_le_sharp`), so the vanishing
polynomial `∏_{α good}(X − C α)` is the nonzero degree-`≤ L` witness whose roots contain every good
challenge — the δ-PRESERVING (`dIn = 56 = (7/8)·64`) proximity-gap witness, at the folded code's OWN
Johnson radius. No `sorry`: the SOLE hypothesis is the precisely-named correlated-agreement `Prop`. -/
theorem sharp_of_correlatedAgreementLine (L : ℕ)
    (hCA : CorrelatedAgreementLine friSetupWrapRate 56 L) :
    WrapCorrelatedAgreementSharp L := by
  classical
  intro f hfar
  set Gd : Set BabyBear :=
    {α : BabyBear | closeN friSetupWrapRate.C' 56 (Fold friSetupWrapRate.geom α f)} with hGd
  have hfin : Gd.Finite := Set.toFinite _
  set Good : Finset BabyBear := hfin.toFinset with hGood
  have hmem : ∀ α, α ∈ Good ↔ α ∈ Gd := by
    intro α; rw [hGood]; simp only [Set.Finite.mem_toFinset]
  have hcard : Good.card ≤ L :=
    wrap_good_challenge_card_le_sharp hCA hfar Good (fun α hα => (hmem α).mp hα)
  refine ⟨∏ α ∈ Good, (X - C α),
    (monic_prod_X_sub_C (fun α : BabyBear => α) Good).ne_zero, ?_, ?_⟩
  · rw [natDegree_finsetProd_X_sub_C_eq_card Good (fun α : BabyBear => α)]
    exact hcard
  · intro α hα
    have hαG : α ∈ Good := (hmem α).mpr hα
    show (∏ β ∈ Good, (X - C β)).eval α = 0
    rw [eval_prod]
    exact Finset.prod_eq_zero hαG (by simp)

/-- **The δ-preserving proximity gap, from the primitive** — routed through the framework's own
reduction `friProximityGap_of_badChallengePoly`. `dIn = 56` is the folded code's Johnson radius
(relative `7/8`), so farness is PRESERVED across the fold (`7/8 → 7/8`), not degraded to the packing
method's `21/32`. -/
theorem wrap_friProximityGap_sharp (L : ℕ)
    (hCA : CorrelatedAgreementLine friSetupWrapRate 56 L) :
    FriProximityGapChallenges friSetupWrapRate 112 56 L :=
  friProximityGap_of_badChallengePoly friSetupWrapRate 112 56 L
    (sharp_of_correlatedAgreementLine L hCA)

/-- **The sharp witness FIRES on the concrete `112`-far `fSqWrap`** (conditional on the primitive):
at most `L` folding challenges fold it `56`-close to the constants, exhibited as the roots of an
actual nonzero degree-`≤ L` polynomial. Non-vacuous: `fSqWrap_far` supplies the hypothesis. -/
theorem wrap_sharp_witness_fires (L : ℕ)
    (hCA : CorrelatedAgreementLine friSetupWrapRate 56 L) :
    ∃ P : BabyBear[X], P ≠ 0 ∧ P.natDegree ≤ L ∧
      {α : BabyBear | closeN friSetupWrapRate.C' 56 (Fold friSetupWrapRate.geom α fSqWrap)}
        ⊆ {α : BabyBear | P.eval α = 0} :=
  sharp_of_correlatedAgreementLine L hCA fSqWrap_far

/-! ## §3b. THE δ-PRESERVING PRIMITIVE, PROVED at LINEAR list size (BCIKS20 correlated-agreement core).

`correlatedAgreementLineAt_twoPoint` gave the primitive only at the *weak* floor `|κ| − 2·dIn`
(vacuous at `dIn = 56`). Here the SHARP floor `|κ| − dIn` is PROVED for the deployed wrap setup —
the exact BCIKS20 correlated-agreement content — by the deployed dimension-`2` collapse, WITHOUT the
general Guruswami–Sudan interpolation machinery, at a LINEAR list size `L = 512 = |κ|²/(|κ| − dIn)`
— the tight BCIKS `n/(1−δ)` scaling, not the quadratic `|κ|²`. The RADIUS is sharp too:
`dIn = 56 = (7/8)·64`, δ-preserving.

**Why single-fibre pinning (Route 1) is IMPOSSIBLE, and how a DUAL count still gives linear.**
Fix `f`. Suppose NO constant point `(a,b) ∈ F²` is rich — every fibre `Φ⁻¹(a,b)` has `< 8` fibres.
Each good `α` folds `f` to a constant `c_α` on `≥ 8` fibres `S_α = {y | E f y + α·O f y = c_α}`, and
`C'` = CONSTANTS forces any `y, y' ∈ S_α` with `Φ y ≠ Φ y'` to obey `O f y ≠ O f y'` and to PIN
`α = (E f y' − E f y)/(O f y − O f y')`. The pin needs BOTH fibres — the free constant `c_α` cancels
only in the DIFFERENCE — so no single distinguished fibre determines `α`, and the naive injection
`α ↦ (y_α, y'_α)` lands in `κ × κ`, giving only the quadratic `|Good| ≤ |κ|² = 4096`.

The linear bound comes from the DUAL of that pin. For `α ≠ β`, a pair `(y, y')` with `Φ y ≠ Φ y'`
lying in BOTH `S_α` and `S_β` folds equal under both, so it pins `α = β` — a contradiction. Hence the
ordered distinct-`Φ` pair sets `Pairs α = {(y,y') ∈ S_α × S_α | Φ y ≠ Φ y'}` are PAIRWISE DISJOINT.
Each is large: every one of `8` fibres `y ∈ S_α` has a partner of a different `Φ`-value (its own
`Φ`-fibre inside `S_α` has `≤ 7 < |S_α|` members), so `y ↦ (y, partner y)` embeds `8` fibres into
`Pairs α`, giving `|Pairs α| ≥ 8`. Disjoint `≥ 8`-subsets of `κ × κ` (card `4096`) number at most
`4096/8 = 512`. That `|κ|²/(|κ| − dIn)` is genuinely linear in `|κ|`: with `dIn = (7/8)|κ|` it is
`8·|κ|`, the BCIKS `n/(1−δ)` list size. (Each `α` consuming only `8 = |κ| − dIn` pairs, rather than
its full `≈ |S_α|²`, is why the constant is `8·|κ|` and not the ideal `|κ|`; the packing/Fisher method
that would sharpen it is DEAD here — `a² = 8² = 64 < |κ|·M = 448`, the very obstruction of §F.) -/

set_option maxRecDepth 4000 in
/-- **THE δ-PRESERVING CORRELATED-AGREEMENT PRIMITIVE, PROVED at the deployed wrap setup, LINEAR list
size.** `CorrelatedAgreementLine friSetupWrapRate 56 512`: for ANY `f`, if more than `512 = 8·|κ|`
folding challenges fold `f` to within `56 = (7/8)·64` of the constants, a SINGLE constant pair `(a,b)`
agrees with `(E f, O f)` on `≥ |κ| − 56 = 8` fibers simultaneously — the sharp `1 − δ` (δ-preserving)
floor, beyond the `|κ| − 2·dIn` two-point reach and beyond the packing method's `21/32` radius. No
`sorry`, no hypothesis. The list size `512 = |κ|²/(|κ| − dIn)` is LINEAR in `|κ|` (the tight BCIKS
scaling `n/(1−δ)`), replacing the loose quadratic `|κ|² = 4096` of the pure ordered-pair injection. -/
theorem wrap_correlatedAgreementLine :
    CorrelatedAgreementLine friSetupWrapRate 56 512 := by
  classical
  intro f Good hclose hL
  set G := friSetupWrapRate.geom with hG
  -- Either some constant point is rich (`≥ 8` fibers) — the conclusion — or none is, and then the
  -- ORDERED distinct-`Φ` pair sets `Pairs α ⊆ κ × κ` are pairwise DISJOINT and each of card `≥ 8`.
  -- Disjoint `≥ 8`-sets inside `κ × κ` (card `4096`) force `|Good| ≤ 4096 / 8 = 512` — LINEAR.
  rcases em (∃ a b : BabyBear,
      8 ≤ (Finset.univ.filter (fun y : Fin (2 ^ 6) => E G f y = a ∧ O G f y = b)).card)
    with hrich | hnorich
  · -- Rich point → the δ-preserving agreement pair.
    obtain ⟨a, b, hab⟩ := hrich
    refine ⟨(fun _ => a), mem_wrap_C'.mpr ⟨a, rfl⟩, (fun _ => b), mem_wrap_C'.mpr ⟨b, rfl⟩, ?_⟩
    have hn : Fintype.card (Fin (2 ^ 6)) = 64 := by simp
    rw [hn]
    simpa using hab
  · -- No rich point: every `Φ`-fibre has `≤ 7` fibres.
    exfalso
    push_neg at hnorich
    -- Pick a fold-constant `cc α` for each good `α`, and its agreement set `S α` (card `≥ 8`).
    have hex : ∀ α ∈ Good, ∃ c : BabyBear,
        (disagree (Fold G α f) (fun _ => c)).card ≤ 56 := by
      intro α hα
      obtain ⟨g, hgC, hcard⟩ := hclose α hα
      obtain ⟨c, rfl⟩ := mem_wrap_C'.mp hgC
      exact ⟨c, hcard⟩
    choose! cc hcc using hex
    set S : BabyBear → Finset (Fin (2 ^ 6)) :=
      fun α => Finset.univ.filter (fun y => Fold G α f y = cc α) with hSdef
    have hmemS : ∀ α y, y ∈ S α ↔ Fold G α f y = cc α := by
      intro α y; simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and]
    have hScard : ∀ α ∈ Good, 8 ≤ (S α).card := by
      intro α hα
      have hcompl : S α = (disagree (Fold G α f) (fun _ => cc α))ᶜ := by
        ext y
        simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl,
          mem_disagree, not_not]
      have hn : Fintype.card (Fin (2 ^ 6)) = 64 := by simp
      have hcard : (S α).card
          = Fintype.card (Fin (2 ^ 6)) - (disagree (Fold G α f) (fun _ => cc α)).card := by
        rw [hcompl, Finset.card_compl]
      have := hcc α hα
      rw [hcard, hn]; omega
    -- The ORDERED distinct-`Φ` pairs drawn from `S α`.
    set Pairs : BabyBear → Finset (Fin (2 ^ 6) × Fin (2 ^ 6)) :=
      fun α => (S α ×ˢ S α).filter
        (fun p => ¬(E G f p.1 = E G f p.2 ∧ O G f p.1 = O G f p.2)) with hPdef
    -- SIZE: `8 ≤ |Pairs α|`. Each of `8` distinct fibres `y ∈ S α` has a partner `pf y ∈ S α` of a
    -- DIFFERENT `Φ`-value (its own `Φ`-fibre inside `S α` has `≤ 7 < 8 ≤ |S α|` members), and
    -- `y ↦ (y, pf y)` injects those `8` fibres into `Pairs α`.
    have hsize : ∀ α ∈ Good, 8 ≤ (Pairs α).card := by
      intro α hα
      obtain ⟨S8, hS8sub, hS8card⟩ := Finset.exists_subset_card_eq (hScard α hα)
      have hpart : ∀ y ∈ S α, ∃ z, z ∈ S α ∧
          ¬(E G f z = E G f y ∧ O G f z = O G f y) := by
        intro y hy
        by_contra hcon
        push_neg at hcon
        have hsub : S α ⊆
            Finset.univ.filter (fun z : Fin (2 ^ 6) => E G f z = E G f y ∧ O G f z = O G f y) := by
          intro z hz
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact hcon z hz
        have h7 := hnorich (E G f y) (O G f y)
        have hle := Finset.card_le_card hsub
        have := hScard α hα
        omega
      choose! pf hpf using hpart
      have hmaps : ∀ y ∈ S8, (fun y => (y, pf y)) y ∈ Pairs α := by
        intro y hy
        have hyS : y ∈ S α := hS8sub hy
        obtain ⟨hpfS, hpfne⟩ := hpf y hyS
        simp only [hPdef, Finset.mem_filter, Finset.mem_product]
        refine ⟨⟨hyS, hpfS⟩, ?_⟩
        intro hΦ
        exact hpfne ⟨hΦ.1.symm, hΦ.2.symm⟩
      have hinj : Set.InjOn (fun y => (y, pf y)) ↑S8 := by
        intro y _ y' _ heq
        exact congrArg Prod.fst heq
      have hcnt := Finset.card_le_card_of_injOn (fun y => (y, pf y)) hmaps hinj
      rw [hS8card] at hcnt
      exact hcnt
    -- DISJOINTNESS: a shared pair `(y, y')` with `Φ y ≠ Φ y'` folds equal under both `α` and `β`,
    -- so `α = (E y' − E y)/(O y − O y') = β`. Hence distinct `α` give disjoint `Pairs α`.
    have hdisj : ∀ α ∈ Good, ∀ β ∈ Good, α ≠ β → Disjoint (Pairs α) (Pairs β) := by
      intro α hα β hβ hαβ
      rw [Finset.disjoint_left]
      intro p hpα hpβ
      simp only [hPdef, Finset.mem_filter, Finset.mem_product] at hpα hpβ
      obtain ⟨⟨hp1α, hp2α⟩, hΦα⟩ := hpα
      obtain ⟨⟨hp1β, hp2β⟩, _⟩ := hpβ
      simp only [hmemS] at hp1α hp2α hp1β hp2β
      have hEα : E G f p.1 + α * O G f p.1 = E G f p.2 + α * O G f p.2 := by
        show Fold G α f p.1 = Fold G α f p.2; rw [hp1α, hp2α]
      have hEβ : E G f p.1 + β * O G f p.1 = E G f p.2 + β * O G f p.2 := by
        show Fold G β f p.1 = Fold G β f p.2; rw [hp1β, hp2β]
      have hmulα : α * (O G f p.1 - O G f p.2) = E G f p.2 - E G f p.1 := by
        linear_combination hEα
      have hmulβ : β * (O G f p.1 - O G f p.2) = E G f p.2 - E G f p.1 := by
        linear_combination hEβ
      have hOne : O G f p.1 ≠ O G f p.2 := by
        intro hOeq
        apply hΦα
        have hz : (0 : BabyBear) = E G f p.2 - E G f p.1 := by rw [← hmulα, hOeq]; ring
        exact ⟨(sub_eq_zero.mp hz.symm).symm, hOeq⟩
      have hDne : O G f p.1 - O G f p.2 ≠ 0 := sub_ne_zero.mpr hOne
      have hcancel : α * (O G f p.1 - O G f p.2) = β * (O G f p.1 - O G f p.2) := by
        rw [hmulα, hmulβ]
      exact hαβ (mul_right_cancel₀ hDne hcancel)
    -- COUNT: `8·|Good| ≤ ∑ |Pairs α| = |⋃ Pairs α| ≤ |κ × κ| = 4096`, so `|Good| ≤ 512`.
    have hsum : 8 * Good.card ≤ ∑ α ∈ Good, (Pairs α).card := by
      calc 8 * Good.card = ∑ _α ∈ Good, 8 := by rw [Finset.sum_const, smul_eq_mul]; ring
        _ ≤ ∑ α ∈ Good, (Pairs α).card := Finset.sum_le_sum hsize
    have hbu : (Good.biUnion Pairs).card = ∑ α ∈ Good, (Pairs α).card :=
      Finset.card_biUnion hdisj
    have huniv : (Finset.univ : Finset (Fin (2 ^ 6) × Fin (2 ^ 6))).card = 4096 := by simp
    have hle : (Good.biUnion Pairs).card ≤ 4096 :=
      le_trans (Finset.card_le_card (Finset.subset_univ _)) (le_of_eq huniv)
    omega

/-- **`WrapCorrelatedAgreementSharp 512`, PROVED (no hypothesis).** The δ-preserving proximity-gap
witness at the folded code's OWN Johnson radius (`dIn = 56 = (7/8)·64`), discharged by feeding the
now-proved line primitive into the reduction. This is `BadChallengePoly friSetupWrapRate 112 56 512`
as an unconditional theorem — the residual named in `FriProximityGapWitness.lean §F`, CLOSED at the
LINEAR list size `512 = |κ|²/(|κ| − dIn)`. -/
theorem wrap_correlatedAgreement_sharp_proved : WrapCorrelatedAgreementSharp 512 :=
  sharp_of_correlatedAgreementLine 512 wrap_correlatedAgreementLine

/-- **The δ-PRESERVING FRI proximity gap, PROVED unconditionally.**
`FriProximityGapChallenges friSetupWrapRate 112 56 512`: a `112`-far word has at most `512` folding
challenges whose fold is `56`-close (relative `7/8`) to the constants — farness PRESERVED across the
fold (`7/8 → 7/8`), the sharp radius the Fisher/packing method (`wrap_friProximityGap_johnson`,
`21/32`) could not reach, at the LINEAR list size. No hypothesis remains. -/
theorem wrap_friProximityGap_sharp_proved :
    FriProximityGapChallenges friSetupWrapRate 112 56 512 :=
  wrap_friProximityGap_sharp 512 wrap_correlatedAgreementLine

/-- **The sharp gap FIRES on the concrete `112`-far `fSqWrap`, unconditionally**: at most `512`
folding challenges fold it `56`-close to the constants, exhibited as the roots of an actual nonzero
polynomial of degree `≤ 512`. Non-vacuous (`fSqWrap_far` supplies the far hypothesis), no
correlated-agreement hypothesis assumed. -/
theorem wrap_sharp_witness_fires_proved :
    ∃ P : BabyBear[X], P ≠ 0 ∧ P.natDegree ≤ 512 ∧
      {α : BabyBear | closeN friSetupWrapRate.C' 56 (Fold friSetupWrapRate.geom α fSqWrap)}
        ⊆ {α : BabyBear | P.eval α = 0} :=
  wrap_correlatedAgreement_sharp_proved fSqWrap_far

/-! ## §4. Axiom hygiene. -/

#assert_axioms correlatedAgreementLine_twoPoint
#assert_axioms correlatedAgreementLineAt_twoPoint
#assert_axioms wrap_good_challenge_card_le_sharp
#assert_axioms sharp_of_correlatedAgreementLine
#assert_axioms wrap_friProximityGap_sharp
#assert_axioms wrap_sharp_witness_fires
#assert_axioms wrap_correlatedAgreementLine
#assert_axioms wrap_correlatedAgreement_sharp_proved
#assert_axioms wrap_friProximityGap_sharp_proved
#assert_axioms wrap_sharp_witness_fires_proved

end Dregg2.Circuit.FriCorrelatedAgreementSharp
