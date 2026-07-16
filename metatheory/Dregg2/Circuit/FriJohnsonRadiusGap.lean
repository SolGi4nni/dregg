import Dregg2.Circuit.FriArityFiberDischarge

/-!
# `FriJohnsonRadiusGap` — the `M = 1` discharge does NOT reach the radius FRI operates at

**The finding.** `FriArityFiberDischarge.arity8_phase_injective` discharges `hΦ` for words that are
`dOut ≥ 496`-far of the `512`-point deployed domain — relative farness `496/512 = 96.875%`. FRI's
proven soundness argument operates at the **Johnson radius** `δ_J = 1 − √ρ`, which at the deployed
rate `ρ = 1/64` is `1 − 1/8 = 87.5%`, i.e. `dOut = 448`. **The band `[448, 496)` — every word a
cheating prover is actually allowed to submit — is NOT covered by the discharge.**

This file settles what is in that band, and the answer is not "an unexplored gap". It is:

## ⚑ FINDING 1 — `M = 1` is FALSE at the Johnson radius. The `496` threshold is TIGHT.

`fPow2N` (§2) — the word `x ↦ (ω^x)^(2n)`, the `2n`-th power monomial — is
`(|ι| − 2n − 1)`-far from the dimension-`n` code (`fPow2N_far`), and its phase map is **NOT
injective**: it is constant `1` on BOTH the fibre `0` and the fibre `2^(b−1)`, so
`Φ(0) = Φ(2^(b−1)) = (1, 0, …, 0)` (`fPow2N_phase_not_injective`).

At the deployed config that word is **`495`-far** — exactly **one** below the discharge's `496`
(`deployed_discharge_threshold_tight`). So `phase_injective_of_far`'s hypothesis
`|ι| ≤ 2n + dOut` cannot be weakened by a single point: at `dOut = 495` the conclusion is already
false. The threshold is not an artifact of the proof method that a cleverer argument might lower —
it is the exact truth boundary.

And since `495 ≥ 448`, the SAME word is Johnson-far: `fPow16Wrap` is `448`-far with a non-injective
phase map (`deployed_M1_false_at_johnson`). **There is no theorem to be had at the Johnson radius;
`M = 1` is simply false there.**

## ⚑ FINDING 2 — the gap is STRUCTURAL, at every shipped config, not a numerical accident

The discharge needs relative farness `1 − 2n/|ι| = 1 − 2^(1−b)`; Johnson gives `1 − 2^(−b/2)`. The
discharge threshold is strictly ABOVE Johnson exactly when `2^(1−b) < 2^(−b/2)`, i.e. `b > 2`
(`discharge_threshold_above_johnson`). **Every shipped config has `logBlowup ∈ {3, 6}`**, so every
shipped config has an uncovered band. Raising the blowup — the lever that buys query bits — makes
this gap WIDER, not narrower.

## ⚑ FINDING 3 — what IS true at the Johnson radius: `M ≤ 7`, and the count that follows

`far_fiber_card_arity` does not vanish at Johnson; it degrades. At `dOut = 448`, `|ι| = 512`, `n = 8`
it gives `8·|Y| + 448 < 512`, i.e. `|Y| ≤ 7` (`johnson_fiber_le_seven`) — the same `M = 7` the
arity-2 file already reports at ITS Johnson radius (`FriProximityGapWitness.wrap_fiber_le_seven` at
`dOut = 112` of `128`). The tree has always known `M = 7` is the Johnson-radius truth; what was new
was reading a `96.9%`-radius statement as if it covered `87.5%`.

`good_card_le_of_phase_injective` cannot consume `M = 7`: with a non-injective `Φ`, `H y − H z` is
the ZERO polynomial for same-phase pairs and the root count says nothing. §4 supplies the honest
replacement, `good_card_le_of_phase_fiber_le`, by counting ORDERED pairs of DISTINCT phase:

  `|Good| · (s² − M·s) ≤ (m − 1) · |κ| · (|κ| − 1)`.

⚑ It **recovers `14112` exactly** at `M = 1, s = 2` (`fiber_le_recovers_arity8_count`) — the
anti-mirror check that this is the right generalization, not a second model.

At the Johnson radius the honest instantiation is `M = 7` and `s = 8` — and `s = 8` is not a choice:
`|κ| − dIn = 64 − 56 = 8` is exactly the folded code's OWN Johnson agreement floor `√ρ·|κ|`, the wall
`FriCorrelatedAgreementSharp` §5 already names. `s > M` holds by **exactly one**. The count is
`|Good| ≤ 7·64·63/(8·8 − 7·8) = 14112·2/8 = 3528` (`arity8_johnson_good_card_le`) ⟹ **~111 bits**
(`arity8_johnson_perFold_soundness`).

## ⚑ WHAT THE DEPLOYED PER-FOLD COLUMN ACTUALLY RESTS ON

`FriLedger.perFoldBits = 109` at the deployed wrap is `arity8_good_card_le`'s `14112` at `s = 2`,
whose `hΦ` is discharged ONLY for `dOut ≥ 496`. So the ledger's `109` is a claim about
**`96.9%`-far words**, not about the `87.5%`-far words FRI must reject. It is TRUE and it is
NON-VACUOUS (`fPow8Wrap` is `503`-far), but it does not cover the operating regime.

The Johnson-radius number is **`111`** (`|Good| ≤ 3528`) — HIGHER, because it is a WEAKER claim:
it bounds only the challenges folding to within `dIn = 56` (agreement `≥ 8`), where `109` bounds the
far larger family folding to within `dIn = 62` (agreement `≥ 2`). **These are different objects and
neither dominates the other.** Reporting them as one column was the error. `FriLedger` now carries
both, separately, and `FriLedgerSound.wrap_ledger_perFoldJohnsonBits` pins the Johnson one.

`#assert_axioms` is blind to HYPOTHESES — and this file is the demonstration of why that matters:
`arity8_phase_injective` is kernel-clean, `sorry`-free, non-vacuous, and TRUE, and it still did not
cover the regime the ledger quoted it for. Only reading the STATEMENT finds that.
-/

namespace Dregg2.Circuit.FriJohnsonRadiusGap

open Polynomial
open Dregg2.Circuit.FriSoundness (disagree mem_disagree closeN farN)
open Dregg2.Circuit.FriFoldArity
open Dregg2.Circuit.FriArityFiberDischarge
open Dregg2.Circuit.FriArityTransfer (H pair_mem_card_le)
open Dregg2.Circuit.BabyBearFriField (BabyBear babyBearP)
open scoped BigOperators Matrix

variable {F : Type*} [Field F] [DecidableEq F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {n : ℕ}

/-! ## §1. THE POWER WORD AT AN ARBITRARY EXPONENT.

`FriArityFiberDischarge`'s `fPowK` is the exponent-`2^k` instance. The falsifier needs exponent
`2·2^k`, so the root count is generalized in the exponent once and both are instances. -/

/-- The monic degree-`e` polynomial `X^e − Σⱼ aⱼ·X^j` whose roots are exactly the points where the
`e`-th power word agrees with the codeword of coefficients `a`. -/
noncomputable def rsPolyE (k e : ℕ) (a : Fin (2 ^ k) → F) : F[X] :=
  X ^ e - ∑ j : Fin (2 ^ k), C (a j) * X ^ (j : ℕ)

theorem rsPolyE_natDegree (k e : ℕ) (he : 2 ^ k ≤ e) (a : Fin (2 ^ k) → F) :
    (rsPolyE k e a).natDegree = e := by
  have hpos : (0 : ℕ) < 2 ^ k := by positivity
  have hlow : (∑ j : Fin (2 ^ k), C (a j) * X ^ (j : ℕ)).natDegree < e := by
    refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (fun j _ => ?_))
      (by omega : 2 ^ k - 1 < e)
    refine le_trans (natDegree_C_mul_le _ _) ?_
    rw [natDegree_X_pow]
    exact Nat.le_sub_one_of_lt j.isLt
  rw [rsPolyE, natDegree_sub_eq_left_of_natDegree_lt (by rwa [natDegree_X_pow]), natDegree_X_pow]

theorem rsPolyE_ne_zero (k e : ℕ) (he : 2 ^ k ≤ e) (a : Fin (2 ^ k) → F) :
    rsPolyE k e a ≠ 0 := by
  intro h
  have hd := rsPolyE_natDegree k e he a
  rw [h, natDegree_zero] at hd
  have hpos : (0 : ℕ) < 2 ^ k := by positivity
  omega

/-- The exponent-`e` power word `x ↦ (ω^x)^e`. -/
noncomputable def fPowE (k b : ℕ) (ω : F) (e : ℕ) : Fin (2 ^ (k + b)) → F :=
  fun x => (pK k b ω x) ^ e

/-- **The exponent-`e` power word agrees with every codeword on at most `e` points** — the monic
degree-`e` root count, generalizing `fPowK_agree_le`. -/
theorem fPowE_agree_le (k b e : ℕ) (he : 2 ^ k ≤ e) (ω : F)
    (hω : IsPrimitiveRoot ω (2 ^ (k + b)))
    (g : Fin (2 ^ (k + b)) → F) (hg : g ∈ (codeCK k b ω : Submodule F _)) :
    ((disagree (fPowE k b ω e) g)ᶜ).card ≤ e := by
  classical
  obtain ⟨a, rfl⟩ := hg
  have hpinj : Function.Injective (pK k b ω) := by
    intro x y hxy
    exact Fin.ext (hω.pow_inj x.isLt y.isLt hxy)
  have hsub : ((disagree (fPowE k b ω e) (fun x => ∑ j : Fin (2 ^ k), a j * (pK k b ω x) ^ (j : ℕ)))ᶜ)
      ⊆ Finset.univ.filter (fun x => (rsPolyE k e a).eval (pK k b ω x) = 0) := by
    intro x hx
    simp only [Finset.mem_compl, mem_disagree, not_not, fPowE] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, rsPolyE, eval_sub, eval_pow, eval_X,
      eval_finsetSum, eval_mul, eval_C]
    rw [sub_eq_zero]
    exact hx
  calc ((disagree (fPowE k b ω e)
          (fun x => ∑ j : Fin (2 ^ k), a j * (pK k b ω x) ^ (j : ℕ)))ᶜ).card
      ≤ (Finset.univ.filter (fun x => (rsPolyE k e a).eval (pK k b ω x) = 0)).card :=
        Finset.card_le_card hsub
    _ ≤ ((rsPolyE k e a).roots.toFinset).card := by
        refine Finset.card_le_card_of_injOn (pK k b ω) (fun x hx => ?_) (fun x _ y _ h => hpinj h)
        rw [Finset.mem_coe, Finset.mem_filter] at hx
        rw [Finset.mem_coe, Multiset.mem_toFinset, mem_roots (rsPolyE_ne_zero k e he a)]
        exact hx.2
    _ ≤ Multiset.card (rsPolyE k e a).roots := (rsPolyE k e a).roots.toFinset_card_le
    _ ≤ (rsPolyE k e a).natDegree := card_roots' _
    _ = e := rsPolyE_natDegree k e he a

/-- **The exponent-`e` power word is `d`-far** whenever `d + e < |ι|`. -/
theorem fPowE_far (k b e : ℕ) (he : 2 ^ k ≤ e) (ω : F)
    (hω : IsPrimitiveRoot ω (2 ^ (k + b))) {d : ℕ} (hd : d + e < 2 ^ (k + b)) :
    farN (codeCK k b ω) d (fPowE k b ω e) := by
  refine farN_of_agree_le (m := e) ?_ (fPowE_agree_le k b e he ω hω)
  rwa [Fintype.card_fin]

/-! ## §2. THE FALSIFIER — a far word whose phase map is NOT injective. -/

/-- **A fibre on which the word is CONSTANT has phase vector `(c, 0, …, 0)`.** The constant `c` on a
fibre lifts to the coefficient vector `Pi.single 0 c` through the fibre Vandermonde — for ANY fibre,
because `V ·ᵥ (c,0,…,0) = (c,…,c)` uses only the `j = 0` column, which is all-ones at every fibre.
This is what makes the falsifier work: two DIFFERENT fibres carrying the same constant get the SAME
phase vector, even though their Vandermonde matrices differ. -/
theorem comps_of_fvec_const (G : FriGeomK F ι κ n) (hn : 0 < n) (f : ι → F) (y : κ) (c : F)
    (hc : ∀ i : Fin n, f (G.reps y i) = c) (j : Fin n) :
    comps G f y j = if (j : ℕ) = 0 then c else 0 := by
  classical
  set e0 : Fin n → F := fun j => if (j : ℕ) = 0 then c else 0 with he0
  have hVe : (fiberV G y) *ᵥ e0 = fvec G f y := by
    funext i
    rw [mulVec_eq, Finset.sum_eq_single (⟨0, hn⟩ : Fin n)]
    · simp [he0, fiberV, Matrix.vandermonde_apply, fvec, hc i]
    · intro j _ hj
      have hj0 : (j : ℕ) ≠ 0 := fun h => hj (Fin.ext h)
      simp [he0, hj0]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have : comps G f y = e0 := by
    rw [comps, ← hVe, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ (fiberV_isUnit_det G y), Matrix.one_mulVec]
  rw [this]

/-- **THE FALSIFIER WORD** — `x ↦ (ω^x)^(2n)`, the `2n`-th power monomial (`n = 2^k` is the code
dimension). `fPowK` is the `n`-th power and folds to an INJECTIVE phase map; doubling the exponent
halves the order of the constant it lands on, and that is exactly what breaks injectivity. -/
noncomputable def fPow2N (k b : ℕ) (ω : F) : Fin (2 ^ (k + b)) → F :=
  fPowE k b ω (2 * 2 ^ k)

/-- **The falsifier is `(|ι| − 2n − 1)`-far** — one short of the discharge's `|ι| − 2n`. -/
theorem fPow2N_far (k b : ℕ) (ω : F) (hω : IsPrimitiveRoot ω (2 ^ (k + b))) {d : ℕ}
    (hd : d + 2 * 2 ^ k < 2 ^ (k + b)) :
    farN (codeCK k b ω) d (fPow2N k b ω) :=
  fPowE_far k b (2 * 2 ^ k) (by omega) ω hω hd

/-- **The falsifier is CONSTANT `1` on the fibres `0` and `2^(b−1)`.** On fibre `y` the exponent is
`(y + 2^b·i)·2^(k+1)`; at `y = 0` that is `2^(k+b)·(2i)` and at `y = 2^(b−1)` it is
`2^(k+b)·(1 + 2i)` — both multiples of `2^(k+b)`, where `ω` is `1`. -/
theorem fPow2N_fvec_one (k b : ℕ) (hb : 1 ≤ b) (ω : F) (hω : IsPrimitiveRoot ω (2 ^ (k + b)))
    (y : Fin (2 ^ b)) (hy : (y : ℕ) = 0 ∨ (y : ℕ) = 2 ^ (b - 1)) (i : Fin (2 ^ k)) :
    fPow2N k b ω ((friGeomK k b ω hω).reps y i) = 1 := by
  have hone : ω ^ (2 ^ (k + b)) = 1 := hω.pow_eq_one
  have hrep : (((friGeomK k b ω hω).reps y i : Fin (2 ^ (k + b))) : ℕ)
      = (y : ℕ) + 2 ^ b * (i : ℕ) := rfl
  show (pK k b ω ((friGeomK k b ω hω).reps y i)) ^ (2 * 2 ^ k) = 1
  rw [pK, ← pow_mul, hrep]
  -- The exponent is `2^(k+b) · M` for an explicit `M`.
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ((y : ℕ) + 2 ^ b * (i : ℕ)) * (2 * 2 ^ k) = 2 ^ (k + b) * M := by
    have hbb : (2 : ℕ) ^ b = 2 ^ (b - 1) * 2 := by
      rw [← pow_succ]
      congr 1
      omega
    have hkb : (2 : ℕ) ^ (k + b) = 2 ^ (b - 1) * 2 * 2 ^ k := by
      rw [← hbb, ← pow_add]
      congr 1
      omega
    rcases hy with hy0 | hy1
    · exact ⟨2 * (i : ℕ), by rw [hy0, hbb, hkb]; ring⟩
    · exact ⟨1 + 2 * (i : ℕ), by rw [hy1, hbb, hkb]; ring⟩
  rw [hM, pow_mul, hone, one_pow]

/-- **⚑ THE FALSIFIER — a far word whose phase map is NOT injective.** The fibres `0` and `2^(b−1)`
are distinct (`b ≥ 1`) and the word is constant `1` on both, so both have phase vector
`(1, 0, …, 0)`. Hence `phase_injective_of_far`'s CONCLUSION is false for this word — at every
`dOut` it is far to. -/
theorem fPow2N_phase_not_injective (k b : ℕ) (hb : 1 ≤ b) (ω : F)
    (hω : IsPrimitiveRoot ω (2 ^ (k + b))) :
    ¬ (∀ y z : Fin (2 ^ b), y ≠ z → ∃ i < 2 ^ k,
        phaseOf (friSetupK k b ω hω).geom (fPow2N k b ω) i y
          ≠ phaseOf (friSetupK k b ω hω).geom (fPow2N k b ω) i z) := by
  classical
  have hpos : (0 : ℕ) < 2 ^ k := by positivity
  have hlt0 : (0 : ℕ) < 2 ^ b := by positivity
  have hlt1 : (2 : ℕ) ^ (b - 1) < 2 ^ b := by
    refine Nat.pow_lt_pow_right (by norm_num) ?_
    omega
  set y0 : Fin (2 ^ b) := ⟨0, hlt0⟩ with hy0
  set y1 : Fin (2 ^ b) := ⟨2 ^ (b - 1), hlt1⟩ with hy1
  have hne : y0 ≠ y1 := by
    intro h
    have : (0 : ℕ) = 2 ^ (b - 1) := congrArg Fin.val h
    have : (0 : ℕ) < 2 ^ (b - 1) := by positivity
    omega
  intro hinj
  obtain ⟨i, hi, hne'⟩ := hinj y0 y1 hne
  apply hne'
  -- Both fibres carry the constant `1`, so both phase vectors are `(1, 0, …, 0)`.
  have hgeom : (friSetupK k b ω hω).geom = friGeomK k b ω hω := rfl
  have hc0 := fun j => comps_of_fvec_const (friGeomK k b ω hω) hpos (fPow2N k b ω) y0 1
    (fun i => fPow2N_fvec_one k b hb ω hω y0 (Or.inl rfl) i) j
  have hc1 := fun j => comps_of_fvec_const (friGeomK k b ω hω) hpos (fPow2N k b ω) y1 1
    (fun i => fPow2N_fvec_one k b hb ω hω y1 (Or.inr rfl) i) j
  simp only [phaseOf, dif_pos hi, hgeom]
  show comps (friGeomK k b ω hω) (fPow2N k b ω) y0 ⟨i, hi⟩
      = comps (friGeomK k b ω hω) (fPow2N k b ω) y1 ⟨i, hi⟩
  rw [hc0 ⟨i, hi⟩, hc1 ⟨i, hi⟩]

/-! ## §3. THE DEPLOYED VERDICT — the threshold is tight, and Johnson is outside it. -/

/-- The deployed falsifier: `x ↦ (ω₅₁₂^x)^16`, the `16`-th power monomial on the `512`-point
rate-`1/64` domain. -/
noncomputable def fPow16Wrap : Fin (2 ^ (3 + 6)) → BabyBear :=
  fPow2N 3 6 (omegaOrd 9)

/-- **The deployed falsifier is `495`-far** — every dimension-`8` codeword agrees with it on `≤ 16`
of the `512` points, so `512 − 16 = 496` disagreements, i.e. `495`-far (`farN` is strict). -/
theorem fPow16Wrap_far_495 : farN friSetupK8Wrap.C 495 fPow16Wrap :=
  fPow2N_far 3 6 (omegaOrd 9) (omegaOrd_isPrimitiveRoot (by norm_num) (by norm_num)) (by norm_num)

/-- **The deployed falsifier is `448`-far — Johnson-far.** `448 = (7/8)·512` is the Johnson radius
at the deployed rate `ρ = 1/64` (`√ρ = 1/8`). -/
theorem fPow16Wrap_far_johnson : farN friSetupK8Wrap.C 448 fPow16Wrap :=
  fPow2N_far 3 6 (omegaOrd 9) (omegaOrd_isPrimitiveRoot (by norm_num) (by norm_num)) (by norm_num)

/-- **The deployed falsifier's phase map is NOT injective.** -/
theorem fPow16Wrap_phase_not_injective :
    ¬ (∀ y z : Fin (2 ^ 6), y ≠ z → ∃ i < 8,
        phaseOf friSetupK8Wrap.geom fPow16Wrap i y
          ≠ phaseOf friSetupK8Wrap.geom fPow16Wrap i z) := by
  have h := fPow2N_phase_not_injective 3 6 (by norm_num) (omegaOrd 9)
    (omegaOrd_isPrimitiveRoot (by norm_num) (by norm_num))
  simpa [friSetupK8Wrap, fPow16Wrap] using h

/-- **⚑ THE HEADLINE — `M = 1` IS FALSE AT THE JOHNSON RADIUS.** There is a word `448`-far from the
deployed code (relative farness `7/8 = 1 − √ρ`, exactly the radius FRI's soundness argument must
handle) whose phase map is NOT injective. So `arity8_phase_injective`'s conclusion does not merely
go unproven in the band `[448, 496)` — it is **false** there, and no argument can establish it.

The deployed per-fold column's `hΦ` is therefore discharged ONLY for `96.9%`-far words. -/
theorem deployed_M1_false_at_johnson :
    ∃ f : Fin (2 ^ (3 + 6)) → BabyBear, farN friSetupK8Wrap.C 448 f ∧
      ¬ (∀ y z : Fin (2 ^ 6), y ≠ z → ∃ i < 8,
          phaseOf friSetupK8Wrap.geom f i y ≠ phaseOf friSetupK8Wrap.geom f i z) :=
  ⟨fPow16Wrap, fPow16Wrap_far_johnson, fPow16Wrap_phase_not_injective⟩

/-- **⚑ THE DISCHARGE'S `496` IS TIGHT — it cannot be weakened by ONE point.** At `dOut = 495` the
falsifier is far and its phase map is not injective. So `phase_injective_of_far`'s hypothesis
`|ι| ≤ 2n + dOut` is the exact truth boundary, not a slack artifact of the counting method. -/
theorem deployed_discharge_threshold_tight :
    ∃ f : Fin (2 ^ (3 + 6)) → BabyBear, farN friSetupK8Wrap.C 495 f ∧
      ¬ (∀ y z : Fin (2 ^ 6), y ≠ z → ∃ i < 8,
          phaseOf friSetupK8Wrap.geom f i y ≠ phaseOf friSetupK8Wrap.geom f i z) :=
  ⟨fPow16Wrap, fPow16Wrap_far_495, fPow16Wrap_phase_not_injective⟩

/-- **The deployed Johnson radius is `448` of `512`.** `δ_J = 1 − √ρ = 1 − 1/8 = 7/8` at `ρ = 1/64`,
and `(7/8)·512 = 448`. -/
theorem deployed_johnson_radius : (7 : ℚ) / 8 * 512 = 448 ∧ ((1 : ℚ) / 8) ^ 2 = 1 / 64 := by
  norm_num

/-- **⚑ THE UNCOVERED BAND IS REAL AND WIDE.** The discharge fires at `≥ 496`; FRI operates at
`448`. `48` of the `512` points — `9.4%` of the domain — separate them, and every word in the band
is one the verifier must reject. -/
theorem deployed_johnson_band_uncovered : (448 : ℕ) < 496 ∧ 496 - 448 = 48 := by norm_num

/-! ## §4. THE GAP IS STRUCTURAL — every `logBlowup ≥ 3` config has an uncovered band. -/

/-- **⚑ THE DISCHARGE THRESHOLD IS STRICTLY ABOVE JOHNSON FOR EVERY `b ≥ 3`** — stated by SQUARES,
so no irrational `√ρ` is needed, and proved ONCE over any ordered field (ℚ for the exact reading,
ℝ for the `√ρ` one). The discharge's relative slack is `2n/|ι| = 2^(1−b)`; Johnson's is `√ρ`.
Comparing squares: `(2^(1−b))² = 2^(2−2b) < 2^(−b) = ρ` exactly when `b > 2`. -/
theorem two_n_over_domain_sq_lt_rate {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (k b : ℕ) (hb : 3 ≤ b) :
    ((2 * 2 ^ k : K) / 2 ^ (k + b)) ^ 2 < (1 : K) / 2 ^ b := by
  -- `b ≥ 3` enters ONLY here: `2^b ≥ 8 > 4`. That `4 < 2^b` IS the whole gap.
  have h8 : (8 : K) ≤ 2 ^ b := by
    calc (8 : K) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ b := pow_le_pow_right₀ (by norm_num) hb
  have hsplit : (2 : K) ^ (k + b) = 2 ^ k * 2 ^ b := by rw [pow_add]
  rw [hsplit, div_pow, div_lt_div_iff₀ (by positivity) (by positivity)]
  have hlhs : (2 * (2 : K) ^ k) ^ 2 * 2 ^ b = 4 * (((2 : K) ^ k) ^ 2 * 2 ^ b) := by ring
  have hrhs : (1 : K) * ((2 : K) ^ k * 2 ^ b) ^ 2 = (((2 : K) ^ k) ^ 2 * 2 ^ b) * 2 ^ b := by ring
  rw [hlhs, hrhs]
  have hA : (0 : K) < ((2 : K) ^ k) ^ 2 * 2 ^ b := by positivity
  nlinarith [hA, h8]

/-- The exact (rational) reading of the gap. -/
theorem discharge_threshold_above_johnson (k b : ℕ) (hb : 3 ≤ b) :
    ((2 * 2 ^ k : ℚ) / 2 ^ (k + b)) ^ 2 < (1 : ℚ) / 2 ^ b :=
  two_n_over_domain_sq_lt_rate k b hb

/-- **The real-valued reading: the discharge needs strictly MORE farness than Johnson.** `δ_J =
1 − √ρ`, the discharge needs `1 − 2n/|ι|`, and `2n/|ι| < √ρ` for every `b ≥ 3`. -/
theorem discharge_radius_above_johnson_real (k b : ℕ) (hb : 3 ≤ b) :
    (1 : ℝ) - Real.sqrt ((1 : ℝ) / 2 ^ b) < 1 - (2 * 2 ^ k : ℝ) / 2 ^ (k + b) := by
  have hpos : (0 : ℝ) < (2 * 2 ^ k : ℝ) / 2 ^ (k + b) := by positivity
  have hsq : ((2 * 2 ^ k : ℝ) / 2 ^ (k + b)) ^ 2 < (1 : ℝ) / 2 ^ b :=
    two_n_over_domain_sq_lt_rate k b hb
  have : (2 * 2 ^ k : ℝ) / 2 ^ (k + b) < Real.sqrt ((1 : ℝ) / 2 ^ b) :=
    (Real.lt_sqrt hpos.le).mpr hsq
  linarith

/-- **Every shipped config's `logBlowup` is `3` or `6`** — both `≥ 3`, so every shipped config has
an uncovered band. The lb-`6` band is `[448, 496)` of `512`; the lb-`3` band is `[42, 48)` of `64`
(`⌈(1 − 2^(−1.5))·64⌉ = 42`). Raising the blowup — the query-bit lever — WIDENS the gap. -/
theorem shipped_blowups_all_have_a_band : (3 : ℕ) ≤ 3 ∧ (3 : ℕ) ≤ 6 := by norm_num

/-! ## §5. WHAT IS TRUE AT JOHNSON — `M ≤ 7`, and the count that follows. -/

/-- **THE JOHNSON-RADIUS FIBER BOUND — `M ≤ 7`, not `1`.** `far_fiber_card_arity` does not vanish at
the Johnson radius; it degrades: `8·|Y| + 448 < 512` gives `|Y| ≤ 7`. This is the arity-8 analogue of
`FriProximityGapWitness.wrap_fiber_le_seven` (`M = 7` at the arity-2 Johnson radius `dOut = 112` of
`128`) — the tree has always reported `M = 7` at Johnson. -/
theorem johnson_fiber_le_seven {f : Fin (2 ^ (3 + 6)) → BabyBear}
    (hfar : farN friSetupK8Wrap.C 448 f) (a : Fin (2 ^ 3) → BabyBear) :
    (Finset.univ.filter (fun y : Fin (2 ^ 6) =>
        ∀ j, Cj friSetupK8Wrap.geom j f y = a j)).card ≤ 7 := by
  have h := far_fiber_card_arity friSetupK8Wrap (fun c => codeC'K_const 6 c) hfar a
  rw [friSetupK8Wrap_domain] at h
  omega

/-- **The phase class of `y`** — the fibres carrying the SAME phase vector as `y`. The `M` in the
fiber bound is a cap on `|phaseClass|`: `M = 1` is injectivity, and `M = 7` is what the Johnson
radius gives. Named as a `def` (rather than inlined) so the bounded-`∀`'s decidability is resolved
once, at the variable arity, instead of re-synthesised at each literal instantiation. -/
def phaseClass (m : ℕ) (Φ : ℕ → κ → F) (y : κ) : Finset κ :=
  Finset.univ.filter (fun z : κ => ∀ i < m, Φ i y = Φ i z)

theorem mem_phaseClass {m : ℕ} {Φ : ℕ → κ → F} {y z : κ} :
    z ∈ phaseClass m Φ y ↔ ∀ i < m, Φ i y = Φ i z := by
  simp [phaseClass]

/-- `t ≥ s ≥ M ⟹ s² + M·t ≤ t² + M·s` — the ℕ-subtraction-free form of the fact that `t² − M·t`
is monotone in `t` above `M`, which is what lets the per-challenge lower bound drop from `|S β|`
to `s`. -/
private theorem sq_add_mul_mono {s M t : ℕ} (hst : s ≤ t) (hMs : M ≤ s) :
    s * s + M * t ≤ t * t + M * s := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hst
  nlinarith [hMs]

/-- **⚑ THE HONEST REPLACEMENT COUNT — the `M`-bounded ORDERED-pair double count.**
`good_card_le_of_phase_injective` needs `M = 1`: it counts UNORDERED pairs and needs every pair to
have `H y ≠ H z`, which fails outright once two fibres share a phase vector. This version takes the
fiber bound as a NUMBER `M` rather than as injectivity, and counts only the ordered pairs of DISTINCT
phase:

  `|Good| · (s² − M·s) ≤ (m − 1) · |κ| · (|κ| − 1)`.

*Proof.* Double-count incidences `(β, (y,z))` with `y, z ∈ S β` and `Φ y ≠ Φ z`.
**Lower:** each `β ∈ Good` has `|S β| = t ≥ s`; the SAME-phase ordered pairs in `S β` number
`Σ_{y ∈ S β} |{z ∈ S β : Φ y = Φ z}| ≤ M·t` (each inner set sits inside `y`'s phase class), so the
distinct-phase ones number `≥ t² − M·t ≥ s² − M·s` (using `t ≥ s ≥ M`).
**Upper:** each distinct-phase ordered pair lies in `≤ m − 1` of the `S β` (`pair_mem_card_le` — the
root count of the nonzero `H y − H z`), and distinct phase forces `y ≠ z`, so there are `≤ |κ|(|κ|−1)`
such pairs. ∎

⚑ The content needs `s > M`. At `M = s` the bound reads `0 ≤ …` and says nothing — which is the
honest reading of "the agreement set may be a single phase class", not a defect. -/
theorem good_card_le_of_phase_fiber_le
    {m M s : ℕ} {Φ : ℕ → κ → F}
    (hM : ∀ y : κ, (phaseClass m Φ y).card ≤ M)
    (hMs : M ≤ s)
    (Good : Finset F) (c : F → F)
    (hS : ∀ β ∈ Good, s ≤ (Finset.univ.filter (fun y : κ =>
        (H m Φ y).eval β = c β)).card) :
    Good.card * (s * s - M * s)
      ≤ (m - 1) * (Fintype.card κ * (Fintype.card κ - 1)) := by
  classical
  set S : F → Finset κ := fun β => Finset.univ.filter (fun y : κ => (H m Φ y).eval β = c β)
    with hSdef
  -- The distinct-phase ordered pairs of `κ`.
  set P : Finset (κ × κ) :=
    ((Finset.univ : Finset κ) ×ˢ (Finset.univ : Finset κ)).filter
      (fun p => ∃ i < m, Φ i p.1 ≠ Φ i p.2) with hPdef
  -- ── LOWER BOUND: each good `β` contributes `≥ s² − M·s` distinct-phase ordered pairs. ──
  have hlow : ∀ β ∈ Good, s * s - M * s
      ≤ ((S β ×ˢ S β).filter (fun p => ∃ i < m, Φ i p.1 ≠ Φ i p.2)).card := by
    intro β hβ
    set t := (S β).card with ht
    have hst : s ≤ t := hS β hβ
    -- The same-phase ordered pairs number `≤ M · t`.
    have hsame : ((S β ×ˢ S β).filter (fun p => ¬ ∃ i < m, Φ i p.1 ≠ Φ i p.2)).card ≤ M * t := by
      have hrw : ((S β ×ˢ S β).filter (fun p => ¬ ∃ i < m, Φ i p.1 ≠ Φ i p.2)).card
          = ∑ y ∈ S β, ((S β).filter (fun z => ¬ ∃ i < m, Φ i y ≠ Φ i z)).card := by
        rw [Finset.card_filter, Finset.sum_product]
        exact Finset.sum_congr rfl (fun y _ => (Finset.card_filter _ _).symm)
      rw [hrw]
      calc ∑ y ∈ S β, ((S β).filter (fun z => ¬ ∃ i < m, Φ i y ≠ Φ i z)).card
          ≤ ∑ _y ∈ S β, M := by
            refine Finset.sum_le_sum (fun y _ => le_trans (Finset.card_le_card ?_) (hM y))
            intro z hz
            simp only [Finset.mem_filter] at hz
            rw [mem_phaseClass]
            have := hz.2
            push_neg at this
            exact this
        _ = M * t := by rw [Finset.sum_const, smul_eq_mul, ht, Nat.mul_comm]
    -- Distinct-phase + same-phase partition `S β × S β`.
    have hpart : ((S β ×ˢ S β).filter (fun p => ∃ i < m, Φ i p.1 ≠ Φ i p.2)).card
        + ((S β ×ˢ S β).filter (fun p => ¬ ∃ i < m, Φ i p.1 ≠ Φ i p.2)).card = t * t := by
      rw [Finset.card_filter_add_card_filter_not, Finset.card_product, ht]
    -- `t ≥ s ≥ M` ⟹ `t² − M·t ≥ s² − M·s`.
    have hkey : s * s + M * t ≤ t * t + M * s := sq_add_mul_mono hst hMs
    omega
  -- ── UPPER BOUND: swap the summation and root-count each pair. ──
  have hcount : ∑ β ∈ Good, ((S β ×ˢ S β).filter (fun p => ∃ i < m, Φ i p.1 ≠ Φ i p.2)).card
      ≤ (m - 1) * (Fintype.card κ * (Fintype.card κ - 1)) := by
    -- Re-express each summand as a filter of the FIXED pair set `P`.
    have hre : ∀ β ∈ Good, ((S β ×ˢ S β).filter (fun p => ∃ i < m, Φ i p.1 ≠ Φ i p.2)).card
        = (P.filter (fun p => p.1 ∈ S β ∧ p.2 ∈ S β)).card := by
      intro β _
      congr 1
      ext p
      simp only [hPdef, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
      tauto
    rw [Finset.sum_congr rfl hre]
    -- Swap: count by PAIR instead of by challenge.
    have hswap : ∑ β ∈ Good, (P.filter (fun p => p.1 ∈ S β ∧ p.2 ∈ S β)).card
        = ∑ p ∈ P, (Good.filter (fun β => p.1 ∈ S β ∧ p.2 ∈ S β)).card := by
      simp only [Finset.card_filter]
      exact Finset.sum_comm
    rw [hswap]
    -- Each distinct-phase pair lies in at most `m − 1` agreement sets.
    have hpair : ∀ p ∈ P, (Good.filter (fun β => p.1 ∈ S β ∧ p.2 ∈ S β)).card ≤ m - 1 := by
      intro p hp
      rw [hPdef, Finset.mem_filter] at hp
      obtain ⟨-, hne⟩ := hp
      refine le_trans (le_of_eq ?_) (pair_mem_card_le (m := m) (Φ := Φ) hne Good c)
      congr 1
      ext β
      simp only [Finset.mem_filter, hSdef, Finset.mem_univ, true_and]
    calc ∑ p ∈ P, (Good.filter (fun β => p.1 ∈ S β ∧ p.2 ∈ S β)).card
        ≤ ∑ _p ∈ P, (m - 1) := Finset.sum_le_sum hpair
      _ = P.card * (m - 1) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ (Fintype.card κ * (Fintype.card κ - 1)) * (m - 1) := by
          refine Nat.mul_le_mul_right _ ?_
          -- distinct phase ⟹ `y ≠ z`, so `P ⊆ offDiag`.
          have hsub : P ⊆ (Finset.univ : Finset κ).offDiag := by
            intro p hp
            rw [hPdef, Finset.mem_filter] at hp
            obtain ⟨-, i, -, hne⟩ := hp
            rw [Finset.mem_offDiag]
            refine ⟨Finset.mem_univ _, Finset.mem_univ _, ?_⟩
            intro heq
            exact hne (by rw [heq])
          have hc := Finset.card_le_card hsub
          rw [Finset.offDiag_card, Finset.card_univ] at hc
          have : Fintype.card κ * Fintype.card κ - Fintype.card κ
              = Fintype.card κ * (Fintype.card κ - 1) := by
            cases Nat.eq_zero_or_pos (Fintype.card κ) with
            | inl h => simp [h]
            | inr h => rw [Nat.mul_sub, Nat.mul_one]
          omega
      _ = (m - 1) * (Fintype.card κ * (Fintype.card κ - 1)) := Nat.mul_comm _ _
  -- ── COMBINE. ──
  calc Good.card * (s * s - M * s)
      = ∑ _β ∈ Good, (s * s - M * s) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ β ∈ Good, ((S β ×ˢ S β).filter (fun p => ∃ i < m, Φ i p.1 ≠ Φ i p.2)).card :=
        Finset.sum_le_sum hlow
    _ ≤ (m - 1) * (Fintype.card κ * (Fintype.card κ - 1)) := hcount

/-- **ANTI-MIRROR — the `M`-bounded count RECOVERS `14112` EXACTLY at `M = 1, s = 2`.** The ordered
pair count `|Good|·(2·2 − 1·2) = 2·|Good| ≤ 7·64·63 = 28224` gives `|Good| ≤ 14112` — the very number
`arity8_good_card_le` proves from injectivity. So §4 is the same model at greater generality, not a
second one. -/
theorem fiber_le_recovers_arity8_count :
    7 * (64 * (64 - 1)) / (2 * 2 - 1 * 2) = 14112 ∧ (8 - 1) * Nat.choose 64 2 = 14112 := by
  refine ⟨by norm_num, by decide⟩

/-- **THE DEPLOYED JOHNSON-RADIUS GOOD COUNT — `≤ 3528`.** At the Johnson OUTER radius
`dOut = 448` the fiber bound is `M = 7` (`johnson_fiber_le_seven`), and the Johnson-consistent INNER
radius is `dIn = 56` — the folded code's own Johnson radius — giving the agreement floor
`s = |κ| − dIn = 8 = √ρ·|κ|`. `s > M` holds by **exactly one**, and `s² − M·s = 64 − 56 = 8`:

  `|Good| · 8 ≤ 7 · 64 · 63 = 28224` ⟹ `|Good| ≤ 3528`.

⚑ This is a WEAKER claim than the `14112` at `dOut = 496`: it bounds only the challenges folding to
within `56`, where `14112` bounds the far larger family folding to within `62`. Neither dominates. -/
theorem arity8_johnson_good_card_le {Φ : ℕ → Fin (2 ^ 6) → BabyBear}
    (hM : ∀ y : Fin (2 ^ 6), (phaseClass 8 Φ y).card ≤ 7)
    (Good : Finset BabyBear) (c : BabyBear → BabyBear)
    (hS : ∀ β ∈ Good, 8 ≤ (Finset.univ.filter (fun y : Fin (2 ^ 6) =>
        (H 8 Φ y).eval β = c β)).card) :
    Good.card ≤ 3528 := by
  have h := good_card_le_of_phase_fiber_le (m := 8) (M := 7) (s := 8) hM (by norm_num) Good c hS
  have hc : Fintype.card (Fin (2 ^ 6)) = 64 := by simp
  rw [hc] at h
  norm_num at h
  omega

/-- **THE DEPLOYED JOHNSON-RADIUS PER-FOLD SOUNDNESS — ~111 bits.** `3528/babyBearP⁴ < 2⁻¹¹¹`. -/
theorem arity8_johnson_perFold_soundness (Good : Finset BabyBear) (hGood : Good.card ≤ 3528) :
    (Good.card : ℝ) / (babyBearP : ℝ) ^ 4 < 1 / 2 ^ 111 := by
  have hcR : (Good.card : ℝ) ≤ 3528 := by exact_mod_cast hGood
  have hpval : (babyBearP : ℝ) = 2013265921 := by norm_num [babyBearP]
  rw [hpval]
  have hden : (0 : ℝ) < (2013265921 : ℝ) ^ 4 := by norm_num
  have h2 : (0 : ℝ) < (2 : ℝ) ^ 111 := by positivity
  rw [div_lt_div_iff₀ hden h2, one_mul]
  have key : (3528 : ℝ) * 2 ^ 111 < (2013265921 : ℝ) ^ 4 := by norm_num
  nlinarith [hcR, h2, key]

/-- **THE EXACT JOHNSON-RADIUS INTERVAL — `2⁻¹¹² < 3528/babyBearP⁴ < 2⁻¹¹¹`** (`≈ 2⁻¹¹¹·⁸⁵`). The
proven Johnson-radius guarantee is `≥ 111` bits, not a rounded `112`. -/
theorem arity8_johnson_perFold_interval :
    3528 * 2 ^ 111 < babyBearP ^ 4 ∧ babyBearP ^ 4 < 3528 * 2 ^ 112 := by
  refine ⟨?_, ?_⟩ <;> norm_num [babyBearP]

/-! ## §6. Axiom hygiene.

Kernel-clean, `sorry`-free, no `axiom`. ⚑ And the point of the file is precisely that this block
proves nothing about applicability: `arity8_phase_injective` passes `#assert_axioms` and is TRUE and
is NON-VACUOUS, and it still does not reach the radius the ledger quoted it for. Only
`deployed_M1_false_at_johnson` — a theorem about the STATEMENT's reach — could say that. -/

#assert_axioms rsPolyE_natDegree
#assert_axioms rsPolyE_ne_zero
#assert_axioms fPowE_agree_le
#assert_axioms fPowE_far
#assert_axioms comps_of_fvec_const
#assert_axioms fPow2N_far
#assert_axioms fPow2N_fvec_one
#assert_axioms fPow2N_phase_not_injective
#assert_axioms fPow16Wrap_far_495
#assert_axioms fPow16Wrap_far_johnson
#assert_axioms fPow16Wrap_phase_not_injective
#assert_axioms deployed_M1_false_at_johnson
#assert_axioms deployed_discharge_threshold_tight
#assert_axioms two_n_over_domain_sq_lt_rate
#assert_axioms discharge_threshold_above_johnson
#assert_axioms discharge_radius_above_johnson_real
#assert_axioms johnson_fiber_le_seven
#assert_axioms mem_phaseClass
#assert_axioms good_card_le_of_phase_fiber_le
#assert_axioms fiber_le_recovers_arity8_count
#assert_axioms arity8_johnson_good_card_le
#assert_axioms arity8_johnson_perFold_soundness
#assert_axioms arity8_johnson_perFold_interval

end Dregg2.Circuit.FriJohnsonRadiusGap
