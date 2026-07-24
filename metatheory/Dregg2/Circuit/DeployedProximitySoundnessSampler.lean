/-
# Dregg2.Circuit.DeployedProximitySoundnessSampler — link A over the ACTUAL (non-uniform) deployed
FRI query sampler.

`DeployedProximitySoundness` proves that a `7/16`-far word passes the deployed `38`-query check on
`< 2⁻³¹` of the samples, modelling the `38` queries as UNIFORM independent draws over the domain
`ι = Fin 16` (`FriQuerySoundness §1`'s idealisation). But the DEPLOYED sampler does NOT draw
uniformly over `Fin 16`: `sample_bits(log_height = 4)` (`fri/src/verifier.rs:266-268`) squeezes a
BabyBear field element and reduces it `n % 16` to a domain index. Because `|F| % 16 = 1`
(`FriQueryBiasSharp.babybear_mod_two_pow_eq_one`), that reduction is NON-uniform — residue `0` is
heavier by one preimage — so the honest per-index survival is `(1 − δ) + δ/|F|`, not `(1 − δ)`.

This module re-proves link A over the field-squeeze sample space `Fin 38 → Fin |F|`, inheriting the
RED-TEAMED sharp bias term `FriQueryBiasSharp.biased_query_survival_sharp` in place of the plain
uniform `(1 − δ)^k`. It sits ABOVE both `DeployedProximitySoundness` (the far-word combinatorics) and
`FriQueryBiasSharp` (the sharp sampler bias): those are the two committed, proven results being
composed. The composition needs NO new socket — no `AcceptanceReduction`, no `PointBinding` — because
`FriQuerySoundness.Accepts` is a CONCRETE agreement predicate over fixed oracles, so the far-word
counting closes directly through the sharp query-survival lemma.

## What the composition establishes (soundness, not tightness)
The sharp bound `((1 − δ) + δ/|F|)^k` is LARGER than the uniform `(1 − δ)^k` — it is the HONEST bound
over the actual biased sampler, correcting the optimism in the uniform model, not a tightening. The
bias inflates the uniform `(9/16)^38 ≈ 2⁻³¹·⁵` by `~1.5·10⁻⁸`, and the operational bound `< 2⁻³¹`
still holds with room to spare.

⚠ Scope, stated so it cannot be read up: the sample space here is the SQUEEZE space `Fin |F|` under
the ROM idealisation that `Challenger.sample()` is uniform over `F` (the sponge assumption). This is
the EXACT scope of `FriQueryBiasSharp`, inherited verbatim — NOT re-discharged, and NOT weaker than
what `DeployedProximitySoundness` already relied on. No hardness is smuggled: `δ = 7/16` remains the
rate-`1/8` unique-decoding radius, and `|F| % 16 = 1` is a proved arithmetic fact.

## BUILD STATUS (2026-07-23, updated): GREEN. The upstream break is FIXED.
The former blocker — `SpongeForgeReduction.lean` referencing `effFloor_top_false_babyBear` /
`effFloor_bot_vacuous` without importing `DomainSeparatedCREffRegrounded` (the unpropagated
effFloor-regrounding rename) — was repaired at the FRI base (E1): `SpongeForgeReduction` now imports
and re-exports the Regrounded poles. `FriQueryBiasSharp`'s full import closure elaborates, and this
module builds and pins kernel-clean against it.
-/
import Mathlib.Tactic
import Dregg2.Circuit.FriQueryBiasSharp
import Dregg2.Circuit.DeployedProximitySoundness

set_option autoImplicit false

namespace Dregg2.Circuit.DeployedProximitySoundnessSampler

open Dregg2.Circuit.FriSoundness
open Dregg2.Circuit.FriQuerySoundness
open Dregg2.Circuit.BabyBearFriDeployed
open Dregg2.Circuit.BabyBearFriField (BabyBear)
open Dregg2.Circuit.FriQueryBiasSharp (biased_query_survival_sharp babybear_mod_two_pow_eq_one)
open Dregg2.Circuit.DeployedProximitySoundness (fSq fSq_far)

/-- The deployed FRI query sampler at the size-`16` domain: a BabyBear field squeeze `s : Fin |F|`
reduced modulo the domain size to a query index `s.val % 16 : Fin 16`. This is the `sample_bits(4)`
model committed in `FriQueryBiasSharp` — NOT a uniform draw over `Fin 16`, since `|F| % 16 = 1` makes
residue `0` heavier by one preimage. -/
def sampledQuery (s : Fin 2013265921) : Fin (2 ^ 4) :=
  ⟨s.val % 2 ^ 4, Nat.mod_lt _ (by norm_num)⟩

/-- **DEPLOYED-SAMPLER PROXIMITY SOUNDNESS (link A, honest sampler).** A word `7/16`-FAR from the
deployed rate-`1/8` BabyBear code passes the deployed `38`-query check — with the queries drawn by
the ACTUAL non-uniform `n % 16` field-squeeze reduction, over the squeeze space `Fin 38 → Fin |F|` —
on at most `((1 − 7/16) + (7/16)/|F|)^38` of the samples. Composes `FriQuerySoundness`'s concrete
agreement predicate with `FriQueryBiasSharp.biased_query_survival_sharp` at
`N = |F|, m = 16, k = 38, δ = 7/16`: the `farN … 7` hypothesis gives agreement density
`≤ 8/16 ≤ 9/16 = 1 − δ`, and `|F| % 16 = 1` unlocks the sharp bias base `(1 − δ) + δ/|F|`. -/
theorem far_word_rarely_accepted_deployed_sampler {f g : Fin (2 ^ 4) → BabyBear}
    (hgC : g ∈ friSetupDeployedRate.C) (hfar : farN friSetupDeployedRate.C 7 f) :
    ((Finset.univ.filter (fun Q : Fin 38 → Fin 2013265921 =>
        Accepts f g (fun i => sampledQuery (Q i)))).card : ℝ)
        / ((2013265921 : ℝ) ^ 38)
      ≤ ((1 - 7 / 16 : ℝ) + (7 / 16) / (2013265921 : ℝ)) ^ 38 := by
  classical
  set E : Finset ℕ := (disagree f g)ᶜ.image Fin.val with hE
  -- Farness forces disagreement `> 7`, hence agreement `≤ 8`.
  have hgt : 7 < (disagree f g).card := by
    by_contra hle
    exact hfar ⟨g, hgC, not_lt.mp hle⟩
  have hEcard : E.card ≤ 8 := by
    have hinj : E.card = ((disagree f g)ᶜ).card :=
      Finset.card_image_of_injective _ Fin.val_injective
    have hcompl : ((disagree f g)ᶜ).card
        = Fintype.card (Fin (2 ^ 4)) - (disagree f g).card := Finset.card_compl _
    have hcardfin : Fintype.card (Fin (2 ^ 4)) = 16 := by simp
    rw [hinj, hcompl, hcardfin]
    omega
  -- Agreement density `≤ 1 − δ`.
  have hdensity : (E.card : ℝ) / ((2 ^ 4 : ℕ) : ℝ) ≤ 1 - (7 / 16 : ℝ) := by
    have hle : (E.card : ℝ) ≤ 8 := by exact_mod_cast hEcard
    rw [show (((2 ^ 4 : ℕ)) : ℝ) = 16 by norm_num, div_le_iff₀ (by norm_num : (0 : ℝ) < 16)]
    linarith
  -- `Accepts` over the reduced sampler ⟺ every reduced index lands in the agreement residue set.
  have hbridge : ∀ (Q : Fin 38 → Fin 2013265921),
      Accepts f g (fun i => sampledQuery (Q i)) ↔ (∀ i, (Q i).val % 2 ^ 4 ∈ E) := by
    intro Q
    constructor
    · intro h i
      have hi : f (sampledQuery (Q i)) = g (sampledQuery (Q i)) := h i
      have hmem : sampledQuery (Q i) ∈ (disagree f g)ᶜ := by
        rw [Finset.mem_compl, mem_disagree, not_not]; exact hi
      have himg : (sampledQuery (Q i)).val ∈ E := Finset.mem_image_of_mem Fin.val hmem
      simpa [sampledQuery] using himg
    · intro h i
      have hi : (Q i).val % 2 ^ 4 ∈ E := h i
      have hi' : (sampledQuery (Q i)).val ∈ E := by simpa [sampledQuery] using hi
      obtain ⟨q', hq', hval⟩ := Finset.mem_image.mp hi'
      have hq'eq : q' = sampledQuery (Q i) := Fin.val_injective hval
      rw [hq'eq, Finset.mem_compl, mem_disagree, not_not] at hq'
      exact hq'
  have hfilter :
      (Finset.univ.filter (fun Q : Fin 38 → Fin 2013265921 =>
          Accepts f g (fun i => sampledQuery (Q i))))
        = (Finset.univ.filter (fun Q : Fin 38 → Fin 2013265921 =>
          ∀ i, (Q i).val % 2 ^ 4 ∈ E)) := by
    ext Q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hbridge Q
  rw [hfilter]
  have hmod : (2013265921 : ℕ) % 2 ^ 4 = 1 :=
    babybear_mod_two_pow_eq_one 4 (by norm_num) (by norm_num)
  have h := biased_query_survival_sharp 2013265921 (2 ^ 4) 38 E (7 / 16 : ℝ)
    (by norm_num) (by norm_num) hmod (by norm_num) (by norm_num) hdensity
  have hcast : ((2013265921 : ℕ) : ℝ) = (2013265921 : ℝ) := by norm_num
  rw [hcast] at h
  exact h

/-- **The bias survives the sharpening — still `< 2⁻³¹`.** Even over the ACTUAL non-uniform sampler,
a `7/16`-far word passes the deployed `38`-query check on `< 2⁻³¹` of the squeeze space: the sharp
base `9/16 + (7/16)/|F|` raised to `38` stays below `2⁻³¹` (the uniform `(9/16)^38 ≈ 2⁻³¹·⁵`; the
bias inflation `~1.5·10⁻⁸` sits far inside the `2⁻³¹·⁵ → 2⁻³¹` margin). -/
theorem deployed_sampler_soundness_lt {f g : Fin (2 ^ 4) → BabyBear}
    (hgC : g ∈ friSetupDeployedRate.C) (hfar : farN friSetupDeployedRate.C 7 f) :
    ((Finset.univ.filter (fun Q : Fin 38 → Fin 2013265921 =>
        Accepts f g (fun i => sampledQuery (Q i)))).card : ℝ)
        / ((2013265921 : ℝ) ^ 38)
      < 1 / 2 ^ 31 :=
  lt_of_le_of_lt (far_word_rarely_accepted_deployed_sampler hgC hfar) (by norm_num)

/-- **FIRE over the deployed sampler.** The concrete far word `fSq` (`≥ 14`-far, `fSq_far`) against
the zero codeword passes the deployed `38`-query check — queries drawn by the ACTUAL `n % 16`
field-squeeze reduction — on `< 2⁻³¹` of the squeeze space. Every hypothesis discharged concretely;
nothing carried. -/
theorem deployed_sampler_fires :
    ((Finset.univ.filter (fun Q : Fin 38 → Fin 2013265921 =>
        Accepts fSq (0 : Fin (2 ^ 4) → BabyBear) (fun i => sampledQuery (Q i)))).card : ℝ)
        / ((2013265921 : ℝ) ^ 38)
      < 1 / 2 ^ 31 :=
  deployed_sampler_soundness_lt (Submodule.zero_mem _) fSq_far

#assert_all_clean [
  far_word_rarely_accepted_deployed_sampler,
  deployed_sampler_soundness_lt,
  deployed_sampler_fires
]

end Dregg2.Circuit.DeployedProximitySoundnessSampler
