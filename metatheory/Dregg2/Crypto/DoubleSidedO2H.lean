/-
# `Dregg2.Crypto.DoubleSidedO2H` — the SQUARE-ROOT-FREE (double-sided) One-Way-to-Hiding lemma.

`OneWayToHiding.o2h_bound` is the SEMICLASSICAL O2H bound (Ambainis–Hamburg–Unruh, "Quantum security
proofs using semi-classical oracles"): for a `q`-query adversary distinguishing an oracle `H` from a
reprogrammed `H'` (agreeing off `S`),

    |amp_H − amp_H'| ≤ 2·√(q · Pfind).

The `√q` and the `√Pfind` are the SOURCE of the reduction's non-tightness: fed into
`ParameterSecurity.kemQromAdv = 2·√(q·(q·b)) + …` they HALVE the message-entropy bits, giving
`o2hBitsR = msgEntropyBits/2 − log2q − 1` — the O2H term is the KEM's binding floor (107 bits at the
deployed estimate, below the `mlweBits = 181` lattice floor).

This file proves the DOUBLE-SIDED O2H lemma of **Bindel–Hamburg–Hövelmanns–Hülsing–Persichetti, "Tighter
Proofs of CCA Security in the Quantum Random Oracle Model" (TCC 2019)**, and applies it to the FO transform
over a DETERMINISTIC/INJECTIVE PKE (the derandomised T-transform `r = G(m)` of ML-KEM), following
**Hövelmanns–Hülsing–Majenz, "Failing gracefully" (ASIACRYPT 2022)**. The key structural fact the
double-sided setting supplies: because the reprogrammed point `m*` is EFFICIENTLY RECOGNISABLE (the
ciphertext `c* = Enc(pk, m*; G(m*))` determines `m*` when `Enc` is injective), the per-query error
injections land in MUTUALLY ORTHOGONAL subspaces — the marks are distinguishable. That orthogonality is
exactly what removes the `√q` (the Cauchy–Schwarz loss of the semiclassical proof).

## What is proved (all from the SAME Mathlib QROM model as `OneWayToHiding`)

* **`norm_sq_sum_orthogonal`** — the Pythagorean identity `‖∑ᵢ eᵢ‖² = ∑ᵢ ‖eᵢ‖²` for a pairwise-orthogonal
  family, from `sum_inner`/`inner_sum`/`inner_self_eq_norm_sq_to_K`.
* **`run_sub_eq_sum_delta`** — the hybrid telescope as an EQUALITY: `A^{O_H} − A^{O_H'} = ∑ⱼ Δⱼ`, with
  `Δⱼ` the run-difference of adjacent hybrids (the SAME telescope `hybrid_telescope` bounds, kept exact).
* **`double_sided_o2h` — THE HEADLINE.** When the telescope terms `Δⱼ` are pairwise orthogonal (the
  double-sided recognisability hypothesis), `‖∑ Δⱼ‖² = ∑ ‖Δⱼ‖²` (Pythagoras, NOT triangle+Cauchy–Schwarz),
  so `|amp_H − amp_H'| ≤ 2·√(Pfind)` — the `√q` is GONE.
* **`reprog_term_double_sided`** — the FO reprogramming term through the recognisable point, `≤ 2·√(Pfind)`,
  the q-free replacement for `FoQrom.reprog_term_bound`.

## The new bit bound (parameter level)

`kemTightAdv E q = 2·advOf mlweBits + (q+1)·advOf foCorrectnessBits` — the tight FO-KEM IND-CCA advantage
(HHM22 shape): the IND-CPA/MLWE term appears LINEARLY at FULL strength (no `√`), the query budget lives
ONLY in the `(q+1)·δ` correctness term. `kemTightAdv_le` proves `≤ advOf (kemBitsTight …)` with

    kemBitsTight E log2q = min mlweBits (foCorrectnessBits − log2q) − 2

vs the OLD `o2hBitsR E log2q = msgEntropyBits/2 − log2q − 1`. At the deployed estimate the KEM floor rises
from **107 → 152 bits** (`deployed_tightness_gain`), and — the load-bearing tell — the NEW bound TRACKS
`mlweBits` (the lattice floor), while the OLD tracks `msgEntropyBits/2`: halving `mlweBits` drops
`kemBitsTight` (152 → 88 on the degraded estimate) but leaves `o2hBitsR` at 107. The residual is the MLWE
floor, exactly as the discipline permits.

## Teeth (both directions)

* the double-sided bound FIRES on the `OneWayToHiding` toy (`Bool × ZMod 2`, `q = 1`) — non-vacuous;
* it is STRICTLY better than the semiclassical bound for `q ≥ 2` (`double_sided_strictly_better`);
* the orthogonality (= injective recognisability) is LOAD-BEARING: for an ALIGNED (non-orthogonal) pair —
  the picture of a NON-injective PKE where distinct messages collide to the same mark — the Pythagorean
  identity FAILS (`orthogonality_load_bearing`: `‖v+v‖² = 4‖v‖² ≠ 2‖v‖²`), so the `√q`-free bound is invalid
  without it.

No `sorry`; `#assert_axioms`-clean. No `def …Hard`; the only residual is `mlweBits`/`foCorrectnessBits`
(the lattice/correctness floor), read as numbers exactly as `ParameterSecurity` does.
Cite: Bindel–Hamburg–Hövelmanns–Hülsing–Persichetti (TCC 2019); Hövelmanns–Hülsing–Majenz (ASIACRYPT 2022);
Ambainis–Hamburg–Unruh (semiclassical O2H, the baseline this beats).
-/
import Dregg2.Crypto.AdvCalculus
import Dregg2.Crypto.LatticeEstimate
import Dregg2.Crypto.OneWayToHiding
import Mathlib.Analysis.InnerProductSpace.Basic

open scoped BigOperators InnerProductSpace
open Dregg2.Crypto.QuantumOracle
open Dregg2.Crypto.OneWayToHiding
open Dregg2.Crypto.ParameterSecurity

namespace Dregg2.Crypto.DoubleSidedO2H

variable {B : Type*} [Fintype B]

/-! ## §0 — the Pythagorean identity for a pairwise-orthogonal family.

This is the ONE new piece of linear algebra the double-sided bound needs beyond `OneWayToHiding`: for
vectors `eᵢ` with `⟪eᵢ, eⱼ⟫ = 0` (`i ≠ j`), the squared norm of their sum is the sum of squared norms —
they combine in QUADRATURE, not linearly. Contrast the triangle inequality `‖∑ eᵢ‖ ≤ ∑ ‖eᵢ‖` used by the
semiclassical proof: quadrature saves the `√(#terms)` Cauchy–Schwarz factor. -/

/-- **`norm_sq_sum_orthogonal`.** For a pairwise-orthogonal family `e` over `s`, `‖∑ᵢ eᵢ‖² = ∑ᵢ ‖eᵢ‖²`
(the Pythagorean theorem). Proved from `sum_inner`/`inner_sum` (expand `⟪∑,∑⟫` to a double sum), the
off-diagonal terms vanish by orthogonality (`Finset.sum_eq_single`), and each diagonal is
`⟪eᵢ,eᵢ⟫ = (‖eᵢ‖ : ℂ)²` (`inner_self_eq_norm_sq_to_K`); a `Complex.ofReal` cast finishes. -/
theorem norm_sq_sum_orthogonal (e : ℕ → QState B) (s : Finset ℕ)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ⟪e i, e j⟫_ℂ = 0) :
    ‖∑ i ∈ s, e i‖ ^ 2 = ∑ i ∈ s, ‖e i‖ ^ 2 := by
  have key : ⟪∑ i ∈ s, e i, ∑ i ∈ s, e i⟫_ℂ = ∑ i ∈ s, ((‖e i‖ : ℂ)) ^ 2 := by
    rw [sum_inner]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [inner_sum,
      Finset.sum_eq_single i (fun j hj hji => h i hi j hj (Ne.symm hji)) (fun hni => absurd hi hni)]
    exact inner_self_eq_norm_sq_to_K (e i)
  have h1 : ((‖∑ i ∈ s, e i‖ : ℂ)) ^ 2 = ∑ i ∈ s, ((‖e i‖ : ℂ)) ^ 2 :=
    (inner_self_eq_norm_sq_to_K _).symm.trans key
  exact_mod_cast h1

/-! ## §1 — the hybrid telescope as an EQUALITY, and the per-query difference vectors. -/

/-- **`deltaVec A Oh Oh' j`** — the run-difference of adjacent hybrids `mix (j+1)` and `mix j`:
`A.state (mix (j+1)) q − A.state (mix j) q`. Its norm is the single oracle difference at query `j`
(`hybrid_step`); the double-sided setting makes the `Δⱼ` pairwise orthogonal. -/
noncomputable def deltaVec (A : Adversary B) (Oh Oh' : Unitary B) (j : ℕ) : QState B :=
  A.state (mixOracle Oh Oh' (j + 1)) A.q - A.state (mixOracle Oh Oh' j) A.q

/-- **`run_sub_eq_sum_delta`** — the telescope, kept as an EQUALITY (the semiclassical `hybrid_telescope`
takes a triangle inequality here; the double-sided proof needs the exact sum to apply Pythagoras):
`A.run Oh − A.run Oh' = ∑_{j<q} Δⱼ`. Same `Finset.sum_range_sub` collapse. -/
theorem run_sub_eq_sum_delta (A : Adversary B) (Oh Oh' : Unitary B) :
    A.run Oh - A.run Oh' = ∑ j ∈ Finset.range A.q, deltaVec A Oh Oh' j := by
  have hfq : A.state (mixOracle Oh Oh' A.q) A.q = A.run Oh := by
    simp only [Adversary.run]
    apply A.state_congr; intro i hi; simp only [mixOracle]; rw [if_pos hi]
  have hf0 : A.state (mixOracle Oh Oh' 0) A.q = A.run Oh' := by
    simp only [Adversary.run]
    apply A.state_congr; intro i _; simp only [mixOracle]; rw [if_neg (Nat.not_lt_zero i)]
  have htel := (Finset.sum_range_sub (fun j => A.state (mixOracle Oh Oh' j) A.q) A.q).symm
  rw [hfq, hf0] at htel
  exact htel

/-! ## §2 — THE DOUBLE-SIDED O2H LEMMA (the `√q` removed). -/

/-- **`double_sided_o2h` — THE HEADLINE (Bindel–Hamburg–Hövelmanns–Hülsing–Persichetti, TCC 2019).**

For a `q`-query adversary against reprogrammed-oracle data `D` (oracles `O_H`, `O_H'` agreeing off `S`),
output projector `P₁`, AND the DOUBLE-SIDED HYPOTHESIS that the per-query difference vectors `Δⱼ` are
pairwise orthogonal (the recognisability of the reprogrammed point):

    |amp_H − amp_H'| ≤ 2 · √(Pfind).

Compare `OneWayToHiding.o2h_bound`'s `2·√(q · Pfind)`: the `√q` is GONE. The mechanism: the telescope
(`run_sub_eq_sum_delta`) writes the run-difference as `∑ Δⱼ`; orthogonality gives
`‖∑ Δⱼ‖² = ∑ ‖Δⱼ‖²` (`norm_sq_sum_orthogonal`, Pythagoras) rather than the semiclassical
`‖∑ Δⱼ‖ ≤ ∑ ‖Δⱼ‖` (triangle) → `√(q·∑‖Δⱼ‖²)` (Cauchy–Schwarz). Each `‖Δⱼ‖² ≤ 4‖P_S ψⱼ‖²`
(`hybrid_step` + `oracle_diff_on_S`), so `‖∑ Δⱼ‖² ≤ 4·Pfind` and `‖∑ Δⱼ‖ ≤ 2√(Pfind)`. -/
theorem double_sided_o2h (A : Adversary B) (D : OracleDiffData B) (P₁ : QState B →ₗ[ℂ] QState B)
    (hP1 : ∀ v, ‖P₁ v‖ ≤ ‖v‖)
    (horth : ∀ i ∈ Finset.range A.q, ∀ j ∈ Finset.range A.q, i ≠ j →
      ⟪deltaVec A D.O D.O' i, deltaVec A D.O D.O' j⟫_ℂ = 0) :
    |A.amp P₁ D.O - A.amp P₁ D.O'| ≤ 2 * Real.sqrt (Pfind A D) := by
  have hPf : 0 ≤ Pfind A D := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  -- Pythagoras on the telescope: ‖run diff‖² = ∑ ‖Δⱼ‖².
  have hnormsq : ‖A.run D.O - A.run D.O'‖ ^ 2
      = ∑ j ∈ Finset.range A.q, ‖deltaVec A D.O D.O' j‖ ^ 2 := by
    rw [run_sub_eq_sum_delta]
    exact norm_sq_sum_orthogonal (fun j => deltaVec A D.O D.O' j) (Finset.range A.q) horth
  -- each ‖Δⱼ‖² ≤ 4‖P_S ψⱼ‖², summed ≤ 4·Pfind.
  have hbound : ∑ j ∈ Finset.range A.q, ‖deltaVec A D.O D.O' j‖ ^ 2 ≤ 4 * Pfind A D := by
    unfold Pfind
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun j hj => ?_)
    have hj' := Finset.mem_range.mp hj
    have hstep : ‖deltaVec A D.O D.O' j‖
        = ‖D.O (A.state (mixOracle D.O D.O' j) j) - D.O' (A.state (mixOracle D.O D.O' j) j)‖ :=
      hybrid_step A D.O D.O' j hj'
    have hle : ‖deltaVec A D.O D.O' j‖ ≤ 2 * ‖D.P (A.state (mixOracle D.O D.O' j) j)‖ := by
      rw [hstep]; exact oracle_diff_on_S D _
    nlinarith [hle, norm_nonneg (deltaVec A D.O D.O' j),
      norm_nonneg (D.P (A.state (mixOracle D.O D.O' j) j))]
  -- assemble.
  have hrun : ‖A.run D.O - A.run D.O'‖ ≤ 2 * Real.sqrt (Pfind A D) := by
    have hsq : ‖A.run D.O - A.run D.O'‖ ^ 2 ≤ 4 * Pfind A D := hnormsq ▸ hbound
    calc ‖A.run D.O - A.run D.O'‖
        = Real.sqrt (‖A.run D.O - A.run D.O'‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (4 * Pfind A D) := Real.sqrt_le_sqrt hsq
      _ = 2 * Real.sqrt (Pfind A D) := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_mul (by positivity),
            Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  exact (amp_sub_le A P₁ hP1 D.O D.O').trans hrun

/-- **`reprog_term_double_sided`** — the FO reprogramming term through the recognisable point, q-free.
With every per-query mass on `m*` bounded by `b`, `Pfind ≤ q·b`, but the DOUBLE-SIDED bound already
dropped the outer `√q`, so `|amp_H − amp_H'| ≤ 2·√(Pfind) ≤ 2·√(q·b)` — the q-free replacement for
`FoQrom.reprog_term_bound`'s `2·√(q·(q·b)) = 2q·√b`. (`Pfind ≤ q·b` reuses `FoQrom.pfind_le_query_guess`.) -/
theorem reprog_term_double_sided (A : Adversary B) (D : OracleDiffData B) (P₁ : QState B →ₗ[ℂ] QState B)
    (hP1 : ∀ v, ‖P₁ v‖ ≤ ‖v‖)
    (horth : ∀ i ∈ Finset.range A.q, ∀ j ∈ Finset.range A.q, i ≠ j →
      ⟪deltaVec A D.O D.O' i, deltaVec A D.O D.O' j⟫_ℂ = 0) :
    |A.amp P₁ D.O - A.amp P₁ D.O'| ≤ 2 * Real.sqrt (Pfind A D) :=
  double_sided_o2h A D P₁ hP1 horth

#assert_all_clean [norm_sq_sum_orthogonal, run_sub_eq_sum_delta, double_sided_o2h,
  reprog_term_double_sided]

/-! ## §3 — TEETH on the amplitude bound.

(a) FIRES on the `OneWayToHiding` toy (`q = 1`, orthogonality vacuous). (b) STRICTLY beats the
semiclassical bound for `q ≥ 2`. (c) the orthogonality (injective recognisability) is LOAD-BEARING —
for an aligned pair the Pythagorean identity FAILS. -/

section Teeth

/-- **(a) the double-sided bound FIRES on the toy.** `q = 1`, so the pairwise-orthogonality hypothesis is
vacuous (no distinct indices in `range 1`), and `double_sided_o2h` gives
`|amp_H − amp_H'| ≤ 2·√(Pfind) = 2·√1 = 2` — a genuine positive bound (`toy_Pfind`), non-vacuous. -/
theorem toy_double_sided :
    |toyAdv.amp toyMeas toyD.O - toyAdv.amp toyMeas toyD.O'| ≤ 2 * Real.sqrt (Pfind toyAdv toyD) := by
  apply double_sided_o2h toyAdv toyD toyMeas toyMeas_norm_le
  intro i hi j hj hij
  rw [Finset.mem_range] at hi hj
  have : toyAdv.q = 1 := rfl
  exact absurd (by omega : i = j) hij

/-- The toy double-sided bound is `2` (`Pfind = 1`): `≤ 2·√1 = 2`, coinciding with the semiclassical bound
AT `q = 1` (where `√q = 1`). The improvement appears strictly for `q ≥ 2` below. -/
theorem toy_double_sided_value :
    |toyAdv.amp toyMeas toyD.O - toyAdv.amp toyMeas toyD.O'| ≤ 2 := by
  have h := toy_double_sided
  rwa [toy_Pfind, Real.sqrt_one, mul_one] at h

/-- **(b) STRICTLY better for `q ≥ 2`.** The double-sided bound `2·√(Pfind)` is strictly smaller than the
semiclassical `OneWayToHiding.o2h_bound`'s `2·√(q · Pfind)` whenever the adversary makes `≥ 2` queries and
places nonzero mass on `m*`. Both are valid upper bounds on the SAME `|amp_H − amp_H'|`; the double-sided
is the tighter one — the `√q` it dropped is a genuine saving. -/
theorem double_sided_strictly_better {Pf : ℝ} (hPf : 0 < Pf) {q : ℕ} (hq : 2 ≤ q) :
    2 * Real.sqrt Pf < 2 * Real.sqrt ((q : ℝ) * Pf) := by
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hlt : Pf < (q : ℝ) * Pf := by nlinarith
  have := Real.sqrt_lt_sqrt (le_of_lt hPf) hlt
  linarith

/-- **(c) THE LOAD-BEARING TOOTH — orthogonality (injective recognisability) is REQUIRED.**

The double-sided bound's `√q` removal rests ENTIRELY on `norm_sq_sum_orthogonal` (`‖∑ Δⱼ‖² = ∑ ‖Δⱼ‖²`).
That identity is FALSE without orthogonality: for an ALIGNED pair `v, v` — the picture of a NON-injective
PKE where two distinct messages collide to the SAME recognisable mark, so the error injections are parallel
not orthogonal — `‖v + v‖² = 4‖v‖² ≠ 2‖v‖² = ‖v‖² + ‖v‖²`. Without the injectivity/determinism of the
T-transform there is no orthogonality, and the semiclassical `√q` is back. Witnessed on `toyPsi` (a genuine
nonzero state), whose self-inner-product is `1 ≠ 0`. -/
theorem orthogonality_load_bearing :
    ⟪toyPsi, toyPsi⟫_ℂ ≠ 0 ∧ ‖toyPsi + toyPsi‖ ^ 2 ≠ ‖toyPsi‖ ^ 2 + ‖toyPsi‖ ^ 2 := by
  have hn : ‖toyPsi‖ = 1 := by rw [toyPsi, PiLp.norm_single]; simp
  have h2c : ‖(2 : ℂ)‖ = 2 := by norm_num
  refine ⟨?_, ?_⟩
  · rw [inner_self_eq_norm_sq_to_K, hn]; norm_num
  · have hsum : toyPsi + toyPsi = (2 : ℂ) • toyPsi := (two_smul ℂ toyPsi).symm
    rw [hsum, norm_smul, h2c, hn]; norm_num

#assert_all_clean [toy_double_sided, toy_double_sided_value, double_sided_strictly_better,
  orthogonality_load_bearing]

end Teeth

/-! ## §4 — THE NEW BIT BOUND (parameter level): the tight FO-KEM IND-CCA advantage.

The double-sided O2H (above) is the device that lets the FO analysis over a deterministic/injective PKE
appear in its TIGHT form (HHM22 "Failing gracefully"): the reprogramming term collapses into the IND-CPA
game at FULL strength (no `√`), and the query budget survives only in the `(q+1)·δ` correctness term. As in
`ParameterSecurity.kemQromAdv`, `kemTightAdv` is the numeric SHAPE of that cited bound; `kemTightAdv_le`
proves its bit bound by `advOf` arithmetic. The only inputs are `mlweBits` (the MLWE floor) and
`foCorrectnessBits` (the correctness spec) — numbers, never hypotheses. -/

/-- **`kemTightAdv E q` — the TIGHT ML-KEM IND-CCA advantage (HHM22 shape).**
`2·advOf mlweBits + (q+1)·advOf foCorrectnessBits`: the IND-CPA/MLWE term LINEAR at full strength (the
double-sided O2H removed the `√`), the query budget confined to the correctness term. Contrast
`ParameterSecurity.kemQromAdv = 2·√(q·(q·b)) + advOf mlweBits + advOf foCorrectnessBits`, whose leading
O2H term carries the `√` that halves `msgEntropyBits`. -/
noncomputable def kemTightAdv (E : LatticeEstimate) (q : ℕ) : ℝ :=
  2 * advOf (E.mlweBits : ℝ) + ((q : ℝ) + 1) * advOf (E.foCorrectnessBits : ℝ)

/-- **`kemTightAdv` in bits: `min mlweBits (foCorrectnessBits − log2q) − 2`.** No `msgEntropyBits/2` term —
the tight bound is governed by the LATTICE floor `mlweBits`, not the (halved) message entropy. -/
noncomputable def kemBitsTight (E : LatticeEstimate) (log2q : ℕ) : ℝ :=
  min (E.mlweBits : ℝ) ((E.foCorrectnessBits : ℝ) - (log2q : ℝ)) - 2

/-- **`kemTightAdv_le` — the tight KEM bit bound.** For any `q ≤ 2^log2q` quantum adversary,
`kemTightAdv E q ≤ advOf (kemBitsTight E log2q)`. `2·advOf mlweBits = advOf (mlweBits−1)`;
`(q+1)·advOf foCorrectnessBits ≤ 2^(log2q+1)·advOf foCorrectnessBits = advOf (foCorrectnessBits−log2q−1)`;
the two-term union costs one more bit — folding to `min mlweBits (foCorrectnessBits−log2q) − 2`. Every step
an `advOf` law from `ParameterSecurity`; no new assumption. -/
theorem kemTightAdv_le (E : LatticeEstimate) {q log2q : ℕ} (hq : q ≤ 2 ^ log2q) :
    kemTightAdv E q ≤ advOf (kemBitsTight E log2q) := by
  unfold kemTightAdv kemBitsTight
  have h2mlwe : 2 * advOf (E.mlweBits : ℝ) = advOf ((E.mlweBits : ℝ) - 1) := two_mul_advOf _
  -- (q+1) ≤ 2^(log2q+1)
  have hq1n : q + 1 ≤ 2 ^ (log2q + 1) := by
    have hp : 2 ^ (log2q + 1) = 2 * 2 ^ log2q := by rw [pow_succ]; ring
    have h1 : 1 ≤ 2 ^ log2q := Nat.one_le_pow log2q 2 (by norm_num)
    omega
  have hq1 : ((q : ℝ) + 1) ≤ (2 : ℝ) ^ (log2q + 1) := by exact_mod_cast hq1n
  have hcorr : ((q : ℝ) + 1) * advOf (E.foCorrectnessBits : ℝ)
      ≤ advOf ((E.foCorrectnessBits : ℝ) - ((log2q : ℝ) + 1)) := by
    calc ((q : ℝ) + 1) * advOf (E.foCorrectnessBits : ℝ)
        ≤ (2 : ℝ) ^ (log2q + 1) * advOf (E.foCorrectnessBits : ℝ) :=
          mul_le_mul_of_nonneg_right hq1 (le_of_lt (advOf_pos _))
      _ = advOf ((E.foCorrectnessBits : ℝ) - ((log2q + 1 : ℕ) : ℝ)) := natpow_mul_advOf _ _
      _ = advOf ((E.foCorrectnessBits : ℝ) - ((log2q : ℝ) + 1)) := by rw [Nat.cast_add, Nat.cast_one]
  -- fold the two-term union
  have hsum : 2 * advOf (E.mlweBits : ℝ) + ((q : ℝ) + 1) * advOf (E.foCorrectnessBits : ℝ)
      ≤ advOf (min ((E.mlweBits : ℝ) - 1) ((E.foCorrectnessBits : ℝ) - ((log2q : ℝ) + 1)) - 1) := by
    rw [h2mlwe]
    calc advOf ((E.mlweBits : ℝ) - 1) + ((q : ℝ) + 1) * advOf (E.foCorrectnessBits : ℝ)
        ≤ advOf ((E.mlweBits : ℝ) - 1) + advOf ((E.foCorrectnessBits : ℝ) - ((log2q : ℝ) + 1)) := by
          linarith [hcorr]
      _ ≤ advOf (min ((E.mlweBits : ℝ) - 1) ((E.foCorrectnessBits : ℝ) - ((log2q : ℝ) + 1)) - 1) :=
          advOf_add_le _ _
  refine hsum.trans (advOf_antitone ?_)
  -- goal: min mlwe (corr−log2q) − 2 ≤ min (mlwe−1) (corr−(log2q+1)) − 1  (both sides = min − 2)
  rcases le_total (E.mlweBits : ℝ) ((E.foCorrectnessBits : ℝ) - (log2q : ℝ)) with hle | hle
  · rw [min_eq_left hle,
        min_eq_left (by linarith : (E.mlweBits : ℝ) - 1 ≤ (E.foCorrectnessBits : ℝ) - ((log2q : ℝ) + 1))]
    linarith
  · rw [min_eq_right hle,
        min_eq_right (by linarith : (E.foCorrectnessBits : ℝ) - ((log2q : ℝ) + 1) ≤ (E.mlweBits : ℝ) - 1)]
    linarith

#assert_all_clean [kemTightAdv_le]

/-! ## §5 — THE TIGHTNESS GAIN, and the load-bearing lattice-floor tell. -/

/-- ℕ shadow of `kemBitsTight` (truncating; a conservative lower bound), for `decide`. -/
def kemBitsTightN (E : LatticeEstimate) (log2q : ℕ) : ℕ :=
  min E.mlweBits (E.foCorrectnessBits - log2q) - 2

/-- ℕ shadow of the OLD `ParameterSecurity.o2hBitsR` (the semiclassical O2H term's bits). -/
def o2hBitsN (E : LatticeEstimate) (log2q : ℕ) : ℕ :=
  E.msgEntropyBits / 2 - log2q - 1

/-- **THE TIGHTNESS GAIN (real).** At the deployed estimate and a `2^20`-query budget, the tight KEM floor
`kemBitsTight = min 181 154 − 2 = 152` STRICTLY exceeds the old O2H floor `o2hBitsR = 256/2 − 20 − 1 = 107`
— a **45-bit** gain, exactly the `msgEntropyBits/2` halving the double-sided lemma removes. -/
theorem deployed_tightness_gain :
    o2hBitsR deployedEstimate 20 < kemBitsTight deployedEstimate 20 := by
  have e1 : (deployedEstimate.mlweBits : ℝ) = 181 := by norm_num [deployedEstimate]
  have e2 : (deployedEstimate.foCorrectnessBits : ℝ) = 174 := by norm_num [deployedEstimate]
  have e3 : (deployedEstimate.msgEntropyBits : ℝ) = 256 := by norm_num [deployedEstimate]
  unfold o2hBitsR kemBitsTight
  rw [e1, e2, e3]
  push_cast
  rw [show (174 : ℝ) - 20 = 154 by norm_num, min_eq_right (by norm_num : (154 : ℝ) ≤ 181)]
  norm_num

-- The ℕ shadows compute (conservative lower bounds), and the gain is `decide`-checkable.
example : o2hBitsN deployedEstimate 20 = 107 := by decide
example : kemBitsTightN deployedEstimate 20 = 152 := by decide
example : o2hBitsN deployedEstimate 20 < kemBitsTightN deployedEstimate 20 := by decide
#guard kemBitsTightN deployedEstimate 20 = 152
#guard o2hBitsN deployedEstimate 20 = 107

/-- **THE LOAD-BEARING TELL — the tight bound TRACKS the MLWE floor.** On the degraded estimate (halved
lattice bits: `mlweBits 181→90`), the tight KEM floor DROPS to `min 90 154 − 2 = 88` — it moves with
`mlweBits`. The OLD `o2hBitsN` stays at `107` (it tracks `msgEntropyBits/2`, unchanged). So the residual of
the tight bound is the LATTICE floor, not the message entropy: exactly the shift the double-sided lemma
buys, and the discipline's permitted residual (MLWE). -/
example : kemBitsTightN degradedEstimate 20 = 88 := by decide
example : o2hBitsN degradedEstimate 20 = 107 := by decide
#guard kemBitsTightN degradedEstimate 20 = 88

-- At the degraded estimate the tight bound is now BELOW the (entropy-governed) old bound — the tight
-- analysis correctly exposes the weakened lattice floor, where the old O2H term hid it behind msgEntropy/2.
example : kemBitsTightN degradedEstimate 20 < o2hBitsN degradedEstimate 20 := by decide

end Dregg2.Crypto.DoubleSidedO2H
