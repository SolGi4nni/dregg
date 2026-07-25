/-
# `Dregg2.Circuit.FriCloseNUniqueDecode` — L5·R2: the per-layer RS unique decoder,
restated over the `FriSetupK` / `closeN` / `disagree` vocabulary.

## What this file is

The FRI ladder's L5 target `DeployedTraceExtract.PositiveRadiusTraceDecode`
(`DeployedTraceExtract.lean` §3′) consumes proximity as `closeN S.C dRad` — since the
2026-07-24 batched-multi-column retype, PER COMMITTED COLUMN
(`MatrixOracle.ColsClose S.C dRad oracle` = `∀ j, closeN S.C dRad (oracle.col j)`), so this
per-word decoder is applied once per column of the batched commitment — in the
`FriSoundness.lean:90` distance vocabulary (`disagree` at `:76`). The tree's RS
unique-decoding `∃!` lives in POLYNOMIAL vocabulary:
`NearDecodesWitness.near_word_decodes_existsUnique` (`NearDecodesWitness.lean:81`), whose
uniqueness half is `RsUniqueDecoding.unique_nearest_codeword_radius`
(`RsUniqueDecoding.lean:113`). This file is the VOCABULARY WELD between the two — no new
decoding math, only the two near-definitional bridges and the composed restatement:

  * bridge (i)  `mem_rsCode_iff_lowDegree_evalVec` — the coefficient-sum membership form
    (`FriDeployedRateInstance.mem_rsCode`, `FriDeployedRateInstance.lean:145`) IS
    low-degree evaluation: `f ∈ rsCode pts D ↔ ∃ p, p.natDegree < D ∧ f = evalVec pts p`
    (for `0 < D`; at `D = 0` the polynomial side is empty while `rsCode pts 0 = {0}`,
    so the iff is genuinely false there — the weld theorem handles `D = 0` separately);
  * bridge (ii) `disagree_card_eq_hammingDist` — `(disagree f g).card = hammingDist f g`,
    both being the cardinality of the filter-(≠) set;
  * the weld `closeN_rsCode_decode` — a word `closeN (rsCode pts D) e` with
    `2·e < N − D + 1` (the unique-decoding radius) has EXACTLY ONE codeword within `e`.

## Where it fires (and where the radius breaks)

At the deployed instance `friSetupDeployed` (`FriDeployedRateInstance.lean:454` —
`|L| = 2^24`, rate `1/8`, `C = rsCode (pR 8 2^21 ω₂₄) 2^21`), the true UD radius is
`e = ⌊(N − D)/2⌋ = (2^24 − 2^21)/2 = 7340032` — POSITIVE, in contrast with the size-16
toy where the positive-radius payment premises are uninhabited
(`FriPositiveRadiusPayment.positive_radius_payment_vacuous_at_friSetupK8`,
`FriPositiveRadiusPayment.lean:168`). Both polarities are exhibited ON `friSetupDeployed`:

  * FIRE — `deployed_positive_radius_decode_fires`: the all-ones codeword corrupted at
    coordinate 0 (`fireWord24`, corruption REAL by `fireWord24_corrupted`) decodes to
    EXACTLY ONE codeword within `e = 7340032`, and `deployed_decode_pins` forces that
    codeword to be the honest `oneWord` (the `w4`/`fireWord` pattern of
    `NearDecodesWitness` §4 / `DeployedUdrRegime` §5, at the `2^24`-point domain).
  * CANARY — `deployed_radius_plus_one_not_unique`: at radius `e + 1 = 7340033` the
    `∃!` FAILS on `canaryWord`: both `0` and the geometric-sum codeword `geomWord`
    (a MINIMUM-WEIGHT codeword: `Σ_{s<2^21} X^s` vanishes on the nonidentity `2^21`-th
    roots of unity, all of which lie in the `2^24`-point domain) sit within `e + 1`.
    So the UD radius at the deployed parameters is EXACTLY `7340032` — the `2·e < N−D+1`
    hypothesis is load-bearing at the first possible failure point, not decorative.

## Scope (what is NOT claimed)

The `closeN` hypothesis itself (link A, FRI proximity) is CONSUMED, not produced — same
posture as `NearDecodesWitness`. Nothing here touches the `n²`-loss arity cap
(`FriDeployedRateInstance` §6) or the FRI soundness floor; this is the deterministic
decode rung only, in the vocabulary the L5 assembly consumes.

Additive new file; imports read-only.
-/
import Dregg2.Circuit.NearDecodesWitness
import Dregg2.Circuit.FriDeployedRateInstance

namespace Dregg2.Circuit.FriCloseNUniqueDecode

open Polynomial
open Dregg2.Circuit.BabyBearFriField (BabyBear)
open Dregg2.Circuit.FriSoundness (closeN disagree mem_disagree disagree_eq_empty_iff)
open Dregg2.Circuit.RsUniqueDecoding (evalVec)
open Dregg2.Circuit.NearDecodesWitness (near_word_decodes_existsUnique)
open Dregg2.Circuit.FriDeployedRateInstance
  (rsCode mem_rsCode friSetupDeployed pR omega24 pR_deployed_inj omega24_orderOf)

set_option autoImplicit false

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## §1 — The two bridges (near-definitional; stated once, used everywhere). -/

omit [Field F] in
/-- **Bridge (ii): `disagree` cardinality IS Hamming distance.** Both sides are the
cardinality of `univ.filter (fun i => f i ≠ g i)`. -/
theorem disagree_card_eq_hammingDist {ι : Type*} [Fintype ι]
    (f g : ι → F) : (disagree f g).card = hammingDist f g := rfl

/-- **Bridge (i): coefficient-sum membership IS low-degree evaluation.** The
`mem_rsCode` carrier `f = fun x => Σ_{s<D} c_s·pts(x)^s` is exactly `f = evalVec pts p`
for a `natDegree < D` polynomial. Needs `0 < D`: at `D = 0` the right side is empty
(`natDegree < 0` is absurd) while `rsCode pts 0 = {0}` is inhabited. -/
theorem mem_rsCode_iff_lowDegree_evalVec {N D : ℕ} (hD : 0 < D)
    {pts : Fin N → F} {f : Fin N → F} :
    f ∈ rsCode pts D ↔ ∃ p : Polynomial F, p.natDegree < D ∧ f = evalVec pts p := by
  rw [mem_rsCode]
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨∑ s : Fin D, Polynomial.C (c s) * Polynomial.X ^ (s : ℕ), ?_, ?_⟩
    · have hle : (∑ s : Fin D, Polynomial.C (c s) * Polynomial.X ^ (s : ℕ)).natDegree
          ≤ D - 1 :=
        Polynomial.natDegree_sum_le_of_forall_le _ _ fun s _ =>
          le_trans (Polynomial.natDegree_C_mul_X_pow_le (c s) (s : ℕ)) (by omega)
      omega
    · funext x
      simp [evalVec, Polynomial.eval_finsetSum]
  · rintro ⟨p, hdeg, rfl⟩
    refine ⟨fun s => p.coeff (s : ℕ), ?_⟩
    funext x
    show p.eval (pts x) = ∑ s : Fin D, p.coeff (s : ℕ) * pts x ^ (s : ℕ)
    rw [Fin.sum_univ_eq_sum_range (fun i => p.coeff i * pts x ^ i) D]
    exact Polynomial.eval_eq_sum_range' hdeg (pts x)

/-! ## §2 — THE WELD: the RS unique decoder over `closeN` / `disagree`. -/

/-- **⚑ L5·R2 — the per-layer RS unique decoder in the `closeN` vocabulary.** A word
`e`-close to `rsCode pts D` with `e` inside the unique-decoding radius
(`2·e < N − D + 1`) is `e`-close to EXACTLY ONE codeword. Existence is the `closeN`
hypothesis; uniqueness routes through bridges (i)+(ii) into
`near_word_decodes_existsUnique` (whose uniqueness half is
`unique_nearest_codeword_radius`). The degenerate corners (`e = 0`: distance-0 decode;
`D = 0`: the code is `{0}`) are handled directly, so the hypotheses are exactly the two
stated Props plus point-distinctness. -/
theorem closeN_rsCode_decode {N D : ℕ} {pts : Fin N → F} (hinj : Function.Injective pts)
    {f : Fin N → F} {e : ℕ}
    (hclose : closeN (rsCode pts D) e f) (he : 2 * e < N - D + 1) :
    ∃! g : Fin N → F, g ∈ rsCode pts D ∧ (disagree f g).card ≤ e := by
  obtain ⟨g₀, hg₀C, hg₀d⟩ := hclose
  refine ⟨g₀, ⟨hg₀C, hg₀d⟩, ?_⟩
  intro g hg
  obtain ⟨hgC, hgd⟩ := hg
  rcases Nat.eq_zero_or_pos e with rfl | hepos
  · -- `e = 0`: both codewords agree with `f` everywhere.
    have hgf : f = g := disagree_eq_empty_iff.mp
      (Finset.card_eq_zero.mp (Nat.le_zero.mp hgd))
    have hg₀f : f = g₀ := disagree_eq_empty_iff.mp
      (Finset.card_eq_zero.mp (Nat.le_zero.mp hg₀d))
    rw [← hgf, ← hg₀f]
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · -- `D = 0`: the code is `{0}`.
    obtain ⟨c, rfl⟩ := hgC
    obtain ⟨c₀, rfl⟩ := hg₀C
    funext x
    simp
  -- Main branch: `0 < e` forces `D ≤ N` (ℕ-subtraction in `he`), and the polynomial
  -- vocabulary applies.
  have hDN : D ≤ N := by omega
  obtain ⟨p, hpdeg, hpe⟩ := (mem_rsCode_iff_lowDegree_evalVec hD).mp hgC
  obtain ⟨p₀, hp₀deg, hp₀e⟩ := (mem_rsCode_iff_lowDegree_evalVec hD).mp hg₀C
  have hd₀ : 2 * hammingDist f (evalVec pts p₀) < N - D + 1 := by
    rw [← disagree_card_eq_hammingDist, ← hp₀e]
    omega
  have hd : 2 * hammingDist f (evalVec pts p) < N - D + 1 := by
    rw [← disagree_card_eq_hammingDist, ← hpe]
    omega
  obtain ⟨q, _hq, huniq⟩ :=
    near_word_decodes_existsUnique pts hinj f hDN ⟨p₀, hp₀deg, hd₀⟩
  have h1 : p = q := huniq p ⟨hpdeg, hd⟩
  have h2 : p₀ = q := huniq p₀ ⟨hp₀deg, hd₀⟩
  rw [hpe, hp₀e, h1, h2]

/-! ## §3 — FIRE at `friSetupDeployed`: positive radius `e = ⌊(N−D)/2⌋ = 7340032`.

`N = 8·2^21 = 2^24`, `D = 2^18·8 = 2^21`; `(N − D)/2 = 7340032 > 0` and
`2·7340032 = 14680064 < 14680065 = N − D + 1`. The received word is the all-ones
codeword (constant polynomial `1`) corrupted at coordinate `0` — the
`w4`/`fireWord` pattern at the realistic `2^24`-point domain. -/

/-- The deployed radius is the true UD floor, positive, and admissible. -/
theorem deployed_udr_radius_spec :
    7340032 = (8 * 2 ^ 21 - 2 ^ 18 * 8) / 2 ∧ 0 < 7340032
      ∧ 2 * 7340032 < 8 * 2 ^ 21 - 2 ^ 18 * 8 + 1 := by norm_num

/-- **The weld, fired at the deployed instance** — `friSetupDeployed.C` IS
`rsCode (pR 8 2^21 ω₂₄) (2^18·8)` (definitionally, by `friSetupR`), so any
`7340032`-close word decodes to exactly one codeword. -/
theorem friSetupDeployed_closeN_decode {f : Fin (8 * 2 ^ 21) → BabyBear}
    (hclose : closeN friSetupDeployed.C 7340032 f) :
    ∃! g : Fin (8 * 2 ^ 21) → BabyBear,
      g ∈ friSetupDeployed.C ∧ (disagree f g).card ≤ 7340032 := by
  have h : ∃! g : Fin (8 * 2 ^ 21) → BabyBear,
      g ∈ rsCode (pR 8 (2 ^ 21) omega24) (2 ^ 18 * 8) ∧ (disagree f g).card ≤ 7340032 :=
    closeN_rsCode_decode pR_deployed_inj hclose (by norm_num)
  exact h

/-- The honest sent codeword: all-ones (the constant polynomial `1`). -/
noncomputable def oneWord : Fin (8 * 2 ^ 21) → BabyBear := fun _ => 1

theorem oneWord_mem : oneWord ∈ friSetupDeployed.C := by
  have h : oneWord ∈ rsCode (pR 8 (2 ^ 21) omega24) (2 ^ 18 * 8) := by
    refine ⟨fun s => if (s : ℕ) = 0 then 1 else 0, ?_⟩
    funext x
    refine Eq.symm ?_
    rw [Fin.sum_univ_eq_sum_range
      (fun i => (if i = 0 then (1 : BabyBear) else 0) * pR 8 (2 ^ 21) omega24 x ^ i)]
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq' (Finset.range (2 ^ 18 * 8)) 0
      (fun i => pR 8 (2 ^ 21) omega24 x ^ i)]
    rw [if_pos (Finset.mem_range.mpr (by norm_num)), pow_zero]
    rfl
  exact h

/-- The received word: `oneWord` with coordinate `0` flipped to `0`. -/
noncomputable def fireWord24 : Fin (8 * 2 ^ 21) → BabyBear :=
  fun x => if (x : ℕ) = 0 then 0 else 1

/-- The corruption is REAL: the received word differs from the sent codeword. -/
theorem fireWord24_corrupted : fireWord24 ≠ oneWord := by
  intro h
  have h0 := congrFun h ⟨0, by norm_num⟩
  simp [fireWord24, oneWord] at h0

/-- One error: the disagreement with the sent codeword is exactly `{0}` — in particular
`≤ 1`, far inside the budget `7340032`. -/
theorem fireWord24_dist_le : (disagree fireWord24 oneWord).card ≤ 1 := by
  have hsub : disagree fireWord24 oneWord ⊆ {(⟨0, by norm_num⟩ : Fin (8 * 2 ^ 21))} := by
    intro x hx
    rw [mem_disagree] at hx
    rw [Finset.mem_singleton]
    by_contra hne
    have hxn : (x : ℕ) ≠ 0 := fun h0 => hne (Fin.ext h0)
    exact hx (by simp [fireWord24, oneWord, hxn])
  simpa using Finset.card_le_card hsub

theorem fireWord24_close : closeN friSetupDeployed.C 7340032 fireWord24 :=
  ⟨oneWord, oneWord_mem, le_trans fireWord24_dist_le (by norm_num)⟩

/-- **⚑ FIRE — the `∃!` at a POSITIVE deployed radius.** The corrupted word decodes to
exactly one codeword of the deployed rate-`1/8` code within the true UD radius
`7340032` — the non-vacuity `friSetupK8`'s size-16 domain could never exhibit. -/
theorem deployed_positive_radius_decode_fires :
    ∃! g : Fin (8 * 2 ^ 21) → BabyBear,
      g ∈ friSetupDeployed.C ∧ (disagree fireWord24 g).card ≤ 7340032 :=
  friSetupDeployed_closeN_decode fireWord24_close

/-- **The decoded word is PINNED to the honest codeword** — any in-radius codeword IS
`oneWord`; the decoder's answer is forced, not chosen. -/
theorem deployed_decode_pins (g : Fin (8 * 2 ^ 21) → BabyBear)
    (hgC : g ∈ friSetupDeployed.C)
    (hgd : (disagree fireWord24 g).card ≤ 7340032) : g = oneWord := by
  obtain ⟨g', _hg', huniq⟩ := deployed_positive_radius_decode_fires
  rw [huniq g ⟨hgC, hgd⟩,
    huniq oneWord ⟨oneWord_mem, le_trans fireWord24_dist_le (by norm_num)⟩]

/-! ## §4 — CANARY: at `e + 1 = 7340033` uniqueness FAILS on `friSetupDeployed`.

The second codeword is the geometric sum `geomWord = Σ_{s<2^21} p(x)^s` — a
MINIMUM-WEIGHT codeword: it vanishes exactly on the `2^21 − 1` nonidentity `2^21`-th
roots of unity (all in the domain), so its distance to `0` is `N − D + 1 = 14680065`,
the MDS minimum distance. `canaryWord` erases `geomWord` on the residue classes
`x % 8 ∈ {1,2,3}` plus the lower half of class `4` — splitting the support into
`≤ 7340032` and `≤ 7340033` — so BOTH `0` and `geomWord` lie within `7340033`. The
radius `7340032` of §3 is therefore EXACTLY maximal: `e` decodes uniquely, `e + 1`
does not. -/

/-- The counting workhorse: a class of `Fin (8·M)` that fixes the residue `x % 8` and
sends `x / 8` into `T` injects into `T` along `x ↦ x / 8`. -/
theorem card_filter_res_le {M r : ℕ} {p : Fin (8 * M) → Prop} [DecidablePred p]
    {T : Finset ℕ}
    (hres : ∀ x : Fin (8 * M), p x → (x : ℕ) % 8 = r)
    (hdiv : ∀ x : Fin (8 * M), p x → (x : ℕ) / 8 ∈ T) :
    (Finset.univ.filter p).card ≤ T.card := by
  refine Finset.card_le_card_of_injOn (fun x : Fin (8 * M) => (x : ℕ) / 8) ?_ ?_
  · intro x hx
    exact hdiv x (Finset.mem_filter.mp hx).2
  · intro x hx y hy hxy
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx hy
    have hx8 := hres x hx
    have hy8 := hres y hy
    have hd : (x : ℕ) / 8 = (y : ℕ) / 8 := hxy
    exact Fin.ext (by omega)

/-- Each residue class mod 8 in the `2^24`-point domain has `≤ 2^21` elements. -/
theorem card_res_le (r : ℕ) :
    (Finset.univ.filter (fun x : Fin (8 * 2 ^ 21) => (x : ℕ) % 8 = r)).card
      ≤ 2097152 := by
  have h := card_filter_res_le (M := 2 ^ 21) (r := r)
    (p := fun x : Fin (8 * 2 ^ 21) => (x : ℕ) % 8 = r) (T := Finset.range 2097152)
    (fun _ hx => hx)
    (fun x _ => Finset.mem_range.mpr (by
      have hlt := x.isLt
      norm_num at hlt
      omega))
  simpa using h

/-- The lower half of residue class 4 (`x < 2^23`) has `≤ 2^20` elements. -/
theorem card_res4_low_le :
    (Finset.univ.filter (fun x : Fin (8 * 2 ^ 21) =>
      (x : ℕ) % 8 = 4 ∧ (x : ℕ) < 2 ^ 23)).card ≤ 1048576 := by
  have h := card_filter_res_le (M := 2 ^ 21) (r := 4)
    (p := fun x : Fin (8 * 2 ^ 21) => (x : ℕ) % 8 = 4 ∧ (x : ℕ) < 2 ^ 23)
    (T := Finset.range 1048576)
    (fun _ hx => hx.1)
    (fun x hx => Finset.mem_range.mpr (by
      have hlt := hx.2
      norm_num at hlt
      omega))
  simpa using h

/-- The upper half of residue class 4 (`2^23 ≤ x`) has `≤ 2^20` elements. -/
theorem card_res4_high_le :
    (Finset.univ.filter (fun x : Fin (8 * 2 ^ 21) =>
      (x : ℕ) % 8 = 4 ∧ 2 ^ 23 ≤ (x : ℕ))).card ≤ 1048576 := by
  have h := card_filter_res_le (M := 2 ^ 21) (r := 4)
    (p := fun x : Fin (8 * 2 ^ 21) => (x : ℕ) % 8 = 4 ∧ 2 ^ 23 ≤ (x : ℕ))
    (T := Finset.Ico 1048576 2097152)
    (fun _ hx => hx.1)
    (fun x hx => Finset.mem_Ico.mpr (by
      have hge := hx.2
      have hlt := x.isLt
      norm_num at hge hlt
      constructor <;> omega))
  have hIco : (Finset.Ico 1048576 2097152).card = 1048576 := by
    simp [Nat.card_Ico]
  rwa [hIco] at h

/-- The geometric-sum codeword `Σ_{s<2^21} p(x)^s` — coefficient vector all-ones. -/
noncomputable def geomWord : Fin (8 * 2 ^ 21) → BabyBear :=
  fun x => ∑ s : Fin (2 ^ 18 * 8), pR 8 (2 ^ 21) omega24 x ^ (s : ℕ)

theorem geomWord_mem : geomWord ∈ friSetupDeployed.C := by
  have h : geomWord ∈ rsCode (pR 8 (2 ^ 21) omega24) (2 ^ 18 * 8) := by
    refine ⟨fun _ => 1, ?_⟩
    funext x
    simp [geomWord]
  exact h

/-- `geomWord` vanishes at every domain point of the `2^21`-element subgroup other than
the identity: for `8 ∣ x`, `x ≠ 0`, the base `ω₂₄^x` is a nonidentity `2^21`-th root of
unity, so the geometric sum telescopes to `0`. -/
theorem geomWord_eq_zero_of_dvd {x : Fin (8 * 2 ^ 21)} (hdvd : 8 ∣ (x : ℕ))
    (hx : (x : ℕ) ≠ 0) : geomWord x = 0 := by
  have hlt : (x : ℕ) < 2 ^ 24 := by
    have h := x.isLt
    norm_num at h ⊢
    exact h
  have hz1 : pR 8 (2 ^ 21) omega24 x ≠ 1 := by
    intro h1
    have h1' : omega24 ^ (x : ℕ) = 1 := h1
    have hdvd' : orderOf omega24 ∣ (x : ℕ) := orderOf_dvd_of_pow_eq_one h1'
    rw [omega24_orderOf] at hdvd'
    exact hx (Nat.eq_zero_of_dvd_of_lt hdvd' hlt)
  have hzpow : pR 8 (2 ^ 21) omega24 x ^ (2 ^ 18 * 8) = 1 := by
    obtain ⟨y, hy⟩ := hdvd
    have hstep : pR 8 (2 ^ 21) omega24 x ^ (2 ^ 18 * 8) = (omega24 ^ (2 ^ 24)) ^ y := by
      show (omega24 ^ (x : ℕ)) ^ (2 ^ 18 * 8) = _
      rw [← pow_mul, ← pow_mul, hy]
      congr 1
      ring
    rw [hstep, ← omega24_orderOf, pow_orderOf_eq_one, one_pow]
  show (∑ s : Fin (2 ^ 18 * 8), pR 8 (2 ^ 21) omega24 x ^ (s : ℕ)) = 0
  rw [Fin.sum_univ_eq_sum_range (fun i => pR 8 (2 ^ 21) omega24 x ^ i)]
  rw [geom_sum_eq hz1, hzpow, sub_self, zero_div]

/-- `geomWord` is NOT the zero codeword (evaluate at `x = 1`: the geometric sum in
`ω₂₄ ≠ 1` has nonzero numerator `ω₂₄^2^21 − 1`, since `2^24 ∤ 2^21`). -/
theorem geomWord_ne_zero : geomWord ≠ 0 := by
  intro h
  have h1 := congrFun h ⟨1, by norm_num⟩
  have hp1 : pR 8 (2 ^ 21) omega24 (⟨1, by norm_num⟩ : Fin (8 * 2 ^ 21)) = omega24 := by
    show omega24 ^ (1 : ℕ) = omega24
    exact pow_one _
  have hne1 : omega24 ≠ 1 := by
    intro he
    have horder := omega24_orderOf
    rw [he, orderOf_one] at horder
    norm_num at horder
  have hne21 : omega24 ^ (2 ^ 18 * 8) ≠ 1 := by
    intro he
    have hdvd := orderOf_dvd_of_pow_eq_one he
    rw [omega24_orderOf] at hdvd
    norm_num at hdvd
  simp only [geomWord, Pi.zero_apply, hp1] at h1
  rw [Fin.sum_univ_eq_sum_range (fun i => omega24 ^ i), geom_sum_eq hne1] at h1
  have hnum : omega24 ^ (2 ^ 18 * 8) - 1 = 0 := by
    by_contra hnz
    exact (div_ne_zero hnz (sub_ne_zero.mpr hne1)) h1
  exact hne21 (sub_eq_zero.mp hnum)

/-- The canary word: `geomWord` with its support erased on residue classes `{1,2,3}`
and the lower half of class `4` — a word sitting (almost) midway between the codewords
`geomWord` and `0`. -/
noncomputable def canaryWord : Fin (8 * 2 ^ 21) → BabyBear := fun x =>
  if (x : ℕ) % 8 = 1 ∨ (x : ℕ) % 8 = 2 ∨ (x : ℕ) % 8 = 3
      ∨ ((x : ℕ) % 8 = 4 ∧ (x : ℕ) < 2 ^ 23)
  then 0 else geomWord x

/-- `canaryWord` is within `e + 1 = 7340033` of `geomWord`: they differ only where the
erasure happened — `≤ 3·2^21 + 2^20 = 7340032` coordinates. -/
theorem canary_dist_geomWord_le :
    (disagree canaryWord geomWord).card ≤ 7340033 := by
  classical
  set F1 := Finset.univ.filter (fun x : Fin (8 * 2 ^ 21) => (x : ℕ) % 8 = 1) with hF1
  set F2 := Finset.univ.filter (fun x : Fin (8 * 2 ^ 21) => (x : ℕ) % 8 = 2) with hF2
  set F3 := Finset.univ.filter (fun x : Fin (8 * 2 ^ 21) => (x : ℕ) % 8 = 3) with hF3
  set F4 := Finset.univ.filter (fun x : Fin (8 * 2 ^ 21) =>
    (x : ℕ) % 8 = 4 ∧ (x : ℕ) < 2 ^ 23) with hF4
  have hsub : disagree canaryWord geomWord ⊆ F1 ∪ F2 ∪ F3 ∪ F4 := by
    intro x hx
    rw [mem_disagree] at hx
    have hC : (x : ℕ) % 8 = 1 ∨ (x : ℕ) % 8 = 2 ∨ (x : ℕ) % 8 = 3
        ∨ ((x : ℕ) % 8 = 4 ∧ (x : ℕ) < 2 ^ 23) := by
      by_contra hnC
      exact hx (by simp only [canaryWord, if_neg hnC])
    simp only [hF1, hF2, hF3, hF4, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rcases hC with h | h | h | h
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  have h1 : F1.card ≤ 2097152 := hF1 ▸ card_res_le 1
  have h2 : F2.card ≤ 2097152 := hF2 ▸ card_res_le 2
  have h3 : F3.card ≤ 2097152 := hF3 ▸ card_res_le 3
  have h4 : F4.card ≤ 1048576 := hF4 ▸ card_res4_low_le
  have hc := Finset.card_le_card hsub
  have hu1 := Finset.card_union_le (F1 ∪ F2 ∪ F3) F4
  have hu2 := Finset.card_union_le (F1 ∪ F2) F3
  have hu3 := Finset.card_union_le F1 F2
  omega

/-- `canaryWord` is within `e + 1 = 7340033` of the ZERO codeword: outside the erasure
its support is `{0}` plus residue classes `{5,6,7}` plus the upper half of class `4` —
`≤ 1 + 3·2^21 + 2^20 = 7340033` coordinates (`geomWord` vanishes on the rest of the
subgroup by `geomWord_eq_zero_of_dvd`). -/
theorem canary_dist_zero_le :
    (disagree canaryWord (0 : Fin (8 * 2 ^ 21) → BabyBear)).card ≤ 7340033 := by
  classical
  set S0 := ({(⟨0, by norm_num⟩ : Fin (8 * 2 ^ 21))} :
    Finset (Fin (8 * 2 ^ 21))) with hS0
  set F5 := Finset.univ.filter (fun x : Fin (8 * 2 ^ 21) => (x : ℕ) % 8 = 5) with hF5
  set F6 := Finset.univ.filter (fun x : Fin (8 * 2 ^ 21) => (x : ℕ) % 8 = 6) with hF6
  set F7 := Finset.univ.filter (fun x : Fin (8 * 2 ^ 21) => (x : ℕ) % 8 = 7) with hF7
  set F4 := Finset.univ.filter (fun x : Fin (8 * 2 ^ 21) =>
    (x : ℕ) % 8 = 4 ∧ 2 ^ 23 ≤ (x : ℕ)) with hF4
  have hsub : disagree canaryWord (0 : Fin (8 * 2 ^ 21) → BabyBear)
      ⊆ S0 ∪ F5 ∪ F6 ∪ F7 ∪ F4 := by
    intro x hx
    rw [mem_disagree] at hx
    rw [Pi.zero_apply] at hx
    have hnC : ¬ ((x : ℕ) % 8 = 1 ∨ (x : ℕ) % 8 = 2 ∨ (x : ℕ) % 8 = 3
        ∨ ((x : ℕ) % 8 = 4 ∧ (x : ℕ) < 2 ^ 23)) := by
      intro hC
      exact hx (by simp only [canaryWord, if_pos hC])
    have hgx : geomWord x ≠ 0 := by
      intro h0
      exact hx (by rw [canaryWord, if_neg hnC]; exact h0)
    have hx0 : ¬ (8 ∣ (x : ℕ)) ∨ (x : ℕ) = 0 := by
      by_contra hcon
      push Not at hcon
      exact hgx (geomWord_eq_zero_of_dvd hcon.1 hcon.2)
    simp only [hS0, hF5, hF6, hF7, hF4, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_singleton]
    rcases hx0 with hnd | hzero
    · have hn1 : ¬ ((x : ℕ) % 8 = 1) := fun h => hnC (Or.inl h)
      have hn2 : ¬ ((x : ℕ) % 8 = 2) := fun h => hnC (Or.inr (Or.inl h))
      have hn3 : ¬ ((x : ℕ) % 8 = 3) := fun h => hnC (Or.inr (Or.inr (Or.inl h)))
      have h8 : (x : ℕ) % 8 = 4 ∨ (x : ℕ) % 8 = 5 ∨ (x : ℕ) % 8 = 6
          ∨ (x : ℕ) % 8 = 7 := by omega
      rcases h8 with h4 | h5 | h6 | h7
      · have hge : 2 ^ 23 ≤ (x : ℕ) := by
          by_contra hlt
          push Not at hlt
          exact hnC (Or.inr (Or.inr (Or.inr ⟨h4, hlt⟩)))
        exact Or.inr ⟨h4, hge⟩
      · exact Or.inl (Or.inl (Or.inl (Or.inr h5)))
      · exact Or.inl (Or.inl (Or.inr h6))
      · exact Or.inl (Or.inr h7)
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Fin.ext hzero))))
  have h0 : S0.card = 1 := hS0 ▸ Finset.card_singleton _
  have h5 : F5.card ≤ 2097152 := hF5 ▸ card_res_le 5
  have h6 : F6.card ≤ 2097152 := hF6 ▸ card_res_le 6
  have h7 : F7.card ≤ 2097152 := hF7 ▸ card_res_le 7
  have h4 : F4.card ≤ 1048576 := hF4 ▸ card_res4_high_le
  have hc := Finset.card_le_card hsub
  have hu1 := Finset.card_union_le (S0 ∪ F5 ∪ F6 ∪ F7) F4
  have hu2 := Finset.card_union_le (S0 ∪ F5 ∪ F6) F7
  have hu3 := Finset.card_union_le (S0 ∪ F5) F6
  have hu4 := Finset.card_union_le S0 F5
  omega

/-- **⚑ CANARY — at `e + 1` the unique decode FAILS on the deployed instance.** Both
the zero codeword and `geomWord` (distinct, `geomWord_ne_zero`) lie within `7340033` of
`canaryWord`, so no `∃!` holds. With `deployed_positive_radius_decode_fires` this pins
the deployed UD radius at EXACTLY `7340032`: the weld's `2·e < N − D + 1` hypothesis is
load-bearing at the first failure point. -/
theorem deployed_radius_plus_one_not_unique :
    ¬ ∃! g : Fin (8 * 2 ^ 21) → BabyBear,
        g ∈ friSetupDeployed.C ∧ (disagree canaryWord g).card ≤ 7340033 := by
  rintro ⟨g', -, huniq⟩
  have h0 : (0 : Fin (8 * 2 ^ 21) → BabyBear) = g' :=
    huniq 0 ⟨friSetupDeployed.C.zero_mem, canary_dist_zero_le⟩
  have hg : geomWord = g' := huniq geomWord ⟨geomWord_mem, canary_dist_geomWord_le⟩
  exact geomWord_ne_zero (hg.trans h0.symm)

/-- **The R2 headline, both polarities on one instance**: at the deployed parameters
the radius `7340032` decodes uniquely and `7340033` does not. -/
theorem deployed_udr_radius_sharp :
    (∃! g : Fin (8 * 2 ^ 21) → BabyBear,
        g ∈ friSetupDeployed.C ∧ (disagree fireWord24 g).card ≤ 7340032) ∧
    ¬ (∃! g : Fin (8 * 2 ^ 21) → BabyBear,
        g ∈ friSetupDeployed.C ∧ (disagree canaryWord g).card ≤ 7340033) :=
  ⟨deployed_positive_radius_decode_fires, deployed_radius_plus_one_not_unique⟩

/-! ## §5 — Axiom hygiene. -/

#assert_all_clean [disagree_card_eq_hammingDist, mem_rsCode_iff_lowDegree_evalVec,
  closeN_rsCode_decode, deployed_udr_radius_spec, friSetupDeployed_closeN_decode,
  oneWord_mem, fireWord24_corrupted, fireWord24_dist_le, fireWord24_close,
  deployed_positive_radius_decode_fires, deployed_decode_pins,
  card_filter_res_le, card_res_le, card_res4_low_le, card_res4_high_le,
  geomWord_mem, geomWord_eq_zero_of_dvd, geomWord_ne_zero,
  canary_dist_geomWord_le, canary_dist_zero_le,
  deployed_radius_plus_one_not_unique, deployed_udr_radius_sharp]

end Dregg2.Circuit.FriCloseNUniqueDecode
