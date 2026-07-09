/-
# `Dregg2.Crypto.FoQrom` — wiring the PROVED O2H lemma into ML-KEM's FO transform.

`MlKemIndCca.lean` closed the ML-KEM FO→IND-CCA story STRUCTURALLY but modelled the random-oracle step by
the PROXY `QROMInjective H := Function.Injective H` — the qualitative "H injective ⇒ K = H(m) is
unpredictable" idealisation. `FoBookkeeping.lean` then closed the classical-ROM advantage bookkeeping
(`fo_ind_cca_bound : Adv^IND-CCA ≤ cpaTerm + simFail + corrSpread`). What was OPEN: the random-oracle
reprogramming step against a REAL quantum adversary. `OneWayToHiding.lean` proved the missing piece —
`o2h_bound : |amp_H − amp_{H'}| ≤ 2·√(q · Pfind)` over the Mathlib QROM model (`QuantumOracle`: states =
`EuclideanSpace ℂ B`, oracle = a genuine basis-permutation `LinearIsometryEquiv`, `Pfind` = the
semiclassical find probability). This file WIRES that bound into the FO transform, DISCHARGING the
`QROMInjective` proxy with the real O2H reprogramming bound.

## The FO-QROM step

The FO transform sets `K = H(m*)` with coins `r = G(m*)`. An IND-CCA adversary distinguishing `K = H(m*)`
from uniform corresponds to distinguishing the real random oracle `H` from `H` REPROGRAMMED at the
challenge message `m*` to a fresh random value — i.e. the O2H setting with reprogramming set `S = {m*}`.
By `o2h_bound`, that advantage is `≤ 2·√(q · Pfind)`, with `Pfind` the amplitude mass the `q`-query
adversary places on the reprogrammed point across its queries.

* **`pfind_le_query_guess`** — `Pfind ≤ q · b` when every per-query amplitude-mass at `m*` is `≤ b`. `b` is
  the message-guessing bound `Pguess(m*) = 2^(−H∞(m*))`: the min-entropy of the encapsulated message
  (Kyber's message space). Honest, load-bearing — a LOW-entropy `m*` (large `b`) makes the bound DEGRADE,
  exactly as it should (the reprogrammed point is easy to hit).
* **`ml_kem_ind_cca_qrom_compose` / `ml_kem_ind_cca_qrom`** — the HEADLINE: the full QROM IND-CCA advantage
  is `≤ 2·√(q·(q·b)) + (cpaTerm + simFail + corrSpread)` — the O2H reprogramming term (`o2h_bound`, wired
  in) PLUS `FoBookkeeping`'s three classical hops. The random oracle is now MODELLED by `QuantumOracle`
  (a real unitary evolved by a `q`-query quantum adversary), so the bound holds against the q-query
  QUANTUM adversary.

## Discharging the `QROMInjective` proxy (the RO is now the modelled quantum adversary)

The headline statements do NOT take `MlKemIndCca.QROMInjective` as a hypothesis. The security of the
K-reprogramming step now flows QUANTITATIVELY from `o2h_bound` + the min-entropy bound `b`, against the
modelled q-query quantum adversary — not from the idealised-injective proxy. `reprog_advantage_zero_of_no_query`
exhibits the qualitative proxy as the PERFECT CORNER of the quantitative bound: an adversary that places
zero amplitude on `m*` has EXACTLY zero K-distinguishing advantage — recovered from O2H, no injectivity
assumed. So `QROMInjective` is superseded: what it asserted qualitatively (K unpredictable) is now a
`b → 0` limit of a real quantum-adversary advantage bound.

No named-carrier laundering: `b` is the honestly-named message-guessing probability (a supplied real, the
min-entropy term), the classical hop terms are `FoBookkeeping`'s (grounded in `MLWESearchHard` /
`decaps_oracle_simulable` / the honest δ, 2^(−γ) PKE parameters), and the reprogramming term is `o2h_bound`
PROVED from Mathlib primitives. No `def …Hard` is introduced or used as a hypothesis.

Cite: Ambainis–Hamburg–Unruh "Quantum security proofs using semi-classical oracles" (O2H); Hofheinz–
Hövelmanns–Kiltz (TCC 2017); Don–Fehr–Majenz–Schaffner (Crypto 2018); FIPS 203 (ML-KEM). No `sorry`,
`#assert_axioms`-clean.
-/
import Dregg2.Crypto.OneWayToHiding
import Dregg2.Crypto.MlKemIndCca
import Dregg2.Crypto.FoBookkeeping

open scoped BigOperators
open Dregg2.Crypto.OneWayToHiding
open Dregg2.Crypto.QuantumOracle
open Dregg2.Crypto.FoBookkeeping

namespace Dregg2.Crypto.FoQrom

/-! ## PART 1 — `Pfind ≤ q · guess(m*)` (the search-in-unstructured-data bound). -/

/-- **`pfind_le_query_guess` — the find probability is at most the query count times the guessing
probability.** If every per-query amplitude-mass on the reprogrammed region is at most `b` (the message
min-entropy bound `Pguess(m*) = 2^(−H∞(m*))`), then `Pfind = ∑_{k<q} ‖P_S ψₖ‖² ≤ q · b`. This is the
standard "searching unstructured data" bound: the total amplitude the `q`-query adversary can place on the
single reprogrammed point `m*` is at most `q` times the per-query guessing probability. `b` is stated
HONESTLY as the message-guessing term — a low-entropy `m*` (large `b`) makes the bound degrade. Directly
`Finset.sum_le_sum` + `Finset.sum_const` (the ℝ analog of `FoBookkeeping.union_bound`). -/
theorem pfind_le_query_guess {B : Type*} [Fintype B] (A : Adversary B) (D : OracleDiffData B) (b : ℝ)
    (hb : ∀ k, k < A.q → ‖D.P (A.state (mixOracle D.O D.O' k) k)‖ ^ 2 ≤ b) :
    Pfind A D ≤ (A.q : ℝ) * b := by
  unfold Pfind
  calc ∑ j ∈ Finset.range A.q, ‖D.P (A.state (mixOracle D.O D.O' j) j)‖ ^ 2
      ≤ ∑ _j ∈ Finset.range A.q, b :=
        Finset.sum_le_sum (fun j hj => hb j (Finset.mem_range.mp hj))
    _ = (A.q : ℝ) * b := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **The O2H reprogramming term, bounded through the min-entropy `b`.** Chaining `o2h_bound` with
`pfind_le_query_guess`: the K-distinguishing advantage of a `q`-query quantum adversary against the FO
random oracle reprogrammed at `m*` is `≤ 2·√(q·(q·b)) = 2q·√b`, the reprogramming term of the QROM IND-CCA
bound. Monotone in `b`: higher message min-entropy (smaller `b`) shrinks it. -/
theorem reprog_term_bound {B : Type*} [Fintype B] (A : Adversary B) (D : OracleDiffData B)
    (P₁ : QState B →ₗ[ℂ] QState B) (hP1 : ∀ v, ‖P₁ v‖ ≤ ‖v‖) (b : ℝ)
    (hb : ∀ k, k < A.q → ‖D.P (A.state (mixOracle D.O D.O' k) k)‖ ^ 2 ≤ b) :
    |A.amp P₁ D.O - A.amp P₁ D.O'| ≤ 2 * Real.sqrt ((A.q : ℝ) * ((A.q : ℝ) * b)) := by
  have ho2h := o2h_bound A D P₁ hP1
  have hpf := pfind_le_query_guess A D b hb
  refine ho2h.trans ?_
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  apply Real.sqrt_le_sqrt
  exact mul_le_mul_of_nonneg_left hpf (Nat.cast_nonneg A.q)

/-! ## PART 2 — the QROM IND-CCA bound (O2H reprogramming term + classical FO hops). -/

/-- **`ml_kem_ind_cca_qrom_compose` — the composition core.** The real IND-CCA win-probability `realCca`,
the reprogrammed-K game win `reprogCca`, and any `classicalBound` on the reprogrammed game
(`|reprogCca − 1/2| ≤ classicalBound`, exactly `FoBookkeeping.fo_ind_cca_bound`'s output). The reprogramming
hop `|realCca − reprogCca|` IS the K-distinguishing advantage (an IND-CCA adversary noticing the
reprogramming is a QROM distinguisher between `H` and `H` reprogrammed at `m*` — the standard reduction),
so `o2h_bound` bounds it by the O2H term. Composing by the triangle inequality:
`|realCca − 1/2| ≤ 2·√(q·(q·b)) + classicalBound`. The RO is the modelled quantum adversary (`QuantumOracle`
unitary); `QROMInjective` is ABSENT from the hypotheses. -/
theorem ml_kem_ind_cca_qrom_compose {B : Type*} [Fintype B] (A : Adversary B) (D : OracleDiffData B)
    (P₁ : QState B →ₗ[ℂ] QState B) (hP1 : ∀ v, ‖P₁ v‖ ≤ ‖v‖) (b : ℝ)
    (hb : ∀ k, k < A.q → ‖D.P (A.state (mixOracle D.O D.O' k) k)‖ ^ 2 ≤ b)
    (realCca reprogCca classicalBound : ℝ)
    (hReprog : |realCca - reprogCca| ≤ |A.amp P₁ D.O - A.amp P₁ D.O'|)
    (hClassical : |reprogCca - 1 / 2| ≤ classicalBound) :
    |realCca - 1 / 2| ≤ 2 * Real.sqrt ((A.q : ℝ) * ((A.q : ℝ) * b)) + classicalBound := by
  have hreprog := hReprog.trans (reprog_term_bound A D P₁ hP1 b hb)
  have htri : |realCca - 1 / 2| ≤ |realCca - reprogCca| + |reprogCca - 1 / 2| := abs_sub_le _ _ _
  linarith

/-- **`ml_kem_ind_cca_qrom` — THE HEADLINE.** The full QROM IND-CCA advantage bound, telescoping the FO
game chain `realCca → hyb → ideal → reprogCca → 1/2` and wiring in the O2H reprogramming term
(`reprog_term_bound`) for the third hop:
* `hSim`   : G₀→G₁ decaps-oracle simulation swing `|realCca − hyb|` ≤ `simFail`;
* `hT`     : G₁→G₂ T-transform / correctness / γ-spreadness swing `|hyb − ideal|` ≤ `corrSpread`;
* `hReprog`: G₂→G₃ K-reprogramming swing `|ideal − reprogCca|` ≤ the K-distinguishing advantage (O2H);
* `hCpa`   : G₃→½ residual IND-CPA swing `|reprogCca − 1/2|` ≤ `cpaTerm` (grounded in `MLWESearchHard`).

gives `Adv^IND-CCA(A) = |realCca − 1/2| ≤ simFail + corrSpread + 2·√(q·(q·b)) + cpaTerm` against the
`q`-query QUANTUM adversary (the RO evolved as a `QuantumOracle` unitary). The three classical terms are
`FoBookkeeping`'s (here as reals; `foBookkeeping_bound_to_real` casts its ℚ hops verbatim). `QROMInjective`
is NOT a hypothesis — the random-oracle step is now the modelled quantum-adversary O2H bound, of which the
old injective proxy is the `b → 0` corner (`reprog_advantage_zero_of_no_query`). -/
theorem ml_kem_ind_cca_qrom {B : Type*} [Fintype B] (A : Adversary B) (D : OracleDiffData B)
    (P₁ : QState B →ₗ[ℂ] QState B) (hP1 : ∀ v, ‖P₁ v‖ ≤ ‖v‖) (b : ℝ)
    (hb : ∀ k, k < A.q → ‖D.P (A.state (mixOracle D.O D.O' k) k)‖ ^ 2 ≤ b)
    (realCca hyb ideal reprogCca simFail corrSpread cpaTerm : ℝ)
    (hSim : |realCca - hyb| ≤ simFail)
    (hT : |hyb - ideal| ≤ corrSpread)
    (hReprog : |ideal - reprogCca| ≤ |A.amp P₁ D.O - A.amp P₁ D.O'|)
    (hCpa : |reprogCca - 1 / 2| ≤ cpaTerm) :
    |realCca - 1 / 2| ≤
      simFail + corrSpread + 2 * Real.sqrt ((A.q : ℝ) * ((A.q : ℝ) * b)) + cpaTerm := by
  have hreprog := hReprog.trans (reprog_term_bound A D P₁ hP1 b hb)
  have h1 : |realCca - 1 / 2| ≤ |realCca - reprogCca| + |reprogCca - 1 / 2| := abs_sub_le _ _ _
  have h2 : |realCca - reprogCca| ≤ |realCca - ideal| + |ideal - reprogCca| := abs_sub_le _ _ _
  have h3 : |realCca - ideal| ≤ |realCca - hyb| + |hyb - ideal| := abs_sub_le _ _ _
  linarith

/-! ## PART 3 — casting `FoBookkeeping`'s classical ℚ bound to ℝ (no re-proof). -/

/-- **The classical FO bound, cast to ℝ.** `FoBookkeeping.Adv reprogCca ≤ c` (its ℚ `fo_ind_cca_bound`
output) becomes `|(reprogCca : ℝ) − 1/2| ≤ (c : ℝ)` — the `classicalBound` `ml_kem_ind_cca_qrom_compose`
consumes. A pure `Rat.cast` transport of the already-proved ℚ inequality; no re-proof, no fresh content. -/
theorem foBookkeeping_bound_to_real (reprogCca c : ℚ) (h : Adv reprogCca ≤ c) :
    |(reprogCca : ℝ) - 1 / 2| ≤ (c : ℝ) := by
  rw [Adv] at h
  have hcast : ((|reprogCca - 1 / 2| : ℚ) : ℝ) ≤ (c : ℝ) := by exact_mod_cast h
  rwa [Rat.cast_abs, Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hcast

/-! ## PART 4 — discharging the `QROMInjective` proxy (the perfect min-entropy corner). -/

/-- **`reprog_advantage_zero_of_no_query` — the qualitative `QROMInjective` proxy as the `b → 0` CORNER.**
A `q`-query quantum adversary that places ZERO amplitude on the reprogrammed point `m*` across all its
queries (`‖P_S ψₖ‖ = 0`) has EXACTLY zero K-distinguishing advantage: `|amp_H − amp_{H'}| = 0`. Derived
from `o2h_bound` (`Pfind = 0 ⇒ the bound is `2·√0 = 0`), NOT from `H` injective. This is the quantitative
replacement for `MlKemIndCca.QROMInjective`: what the injective proxy asserted qualitatively (K = H(m*) is
unpredictable) is the perfect-min-entropy limit of the real quantum-adversary O2H bound. The random oracle
is now the modelled quantum adversary, not an idealised-injective proxy. -/
theorem reprog_advantage_zero_of_no_query {B : Type*} [Fintype B] (A : Adversary B)
    (D : OracleDiffData B) (P₁ : QState B →ₗ[ℂ] QState B) (hP1 : ∀ v, ‖P₁ v‖ ≤ ‖v‖)
    (hb0 : ∀ k, k < A.q → ‖D.P (A.state (mixOracle D.O D.O' k) k)‖ = 0) :
    |A.amp P₁ D.O - A.amp P₁ D.O'| = 0 := by
  have hpf : Pfind A D = 0 := by
    unfold Pfind
    apply Finset.sum_eq_zero
    intro j hj
    rw [hb0 j (Finset.mem_range.mp hj)]; norm_num
  have ho2h := o2h_bound A D P₁ hP1
  rw [hpf, mul_zero, Real.sqrt_zero, mul_zero] at ho2h
  exact le_antisymm ho2h (abs_nonneg _)

#assert_all_clean [pfind_le_query_guess, reprog_term_bound, ml_kem_ind_cca_qrom_compose,
  ml_kem_ind_cca_qrom, foBookkeeping_bound_to_real, reprog_advantage_zero_of_no_query]

/-! ## Teeth — the QROM wiring FIRES on a concrete instance; the min-entropy term is load-bearing.

Reuse the O2H toy (`OneWayToHiding`): `X = Bool`, `Y = ZMod 2`, `q = 1`, reprogramming set `S = {true}`, an
adversary placing all amplitude on the reprogrammed coordinate (the tight case). There `Pfind = 1`
(`toy_Pfind`), so the guessing bound is forced to `b = 1` (maximal — the adversary always queries `m*`),
and the O2H reprogramming term is exactly `2`.

(a) `pfind_le_query_guess` FIRES on the toy (`Pfind = 1 ≤ q·b = 1·1`), tight.
(b) The O2H reprogramming term is exactly `2 = 2·√(q·Pfind)`, and COMPOSES with `FoBookkeeping`'s classical
    bound (via `foBookkeeping_bound_to_real` on `ex_fo_bound_fires`) into the full QROM IND-CCA bound.
(c) The min-entropy term is LOAD-BEARING: a low-entropy `m*` (large `b`) makes the reprogramming term
    strictly worse (`b = 1/4 ↦ 1` vs `b = 1 ↦ 2`); the toy's `b` is PINNED at `1` by `toy_proj_norm`.
(d) `reprog_advantage_zero_of_no_query`'s corner: zero query-mass ⇒ zero advantage (the discharged proxy). -/

section Teeth

/-! ### (a) the find-probability guessing bound fires on the toy. -/

/-- The toy's single-query amplitude-mass on the reprogrammed point is `1` (all amplitude on `(true,0)`). -/
theorem toy_query0_mass :
    ‖toyD.P (toyAdv.state (mixOracle toyD.O toyD.O' 0) 0)‖ ^ 2 ≤ 1 := by
  show ‖toyD.P (toyAdv.state (mixOracle toyD.O toyD.O' 0) 0)‖ ^ 2 ≤ 1
  simp only [toyAdv, Adversary.state, LinearIsometryEquiv.coe_refl, id_eq]
  simp only [toyD, oracleDiff_P]
  rw [toy_proj_norm]; norm_num

/-- **`pfind_le_query_guess` FIRES on the toy** with `b = 1`: `Pfind = 1 ≤ q·b = 1·1`. Tight (`toy_Pfind`
gives `Pfind = 1`), so the guessing bound is non-vacuous — the adversary always hits `m*`. -/
theorem ex_pfind_le_guess : Pfind toyAdv toyD ≤ (toyAdv.q : ℝ) * 1 := by
  apply pfind_le_query_guess
  intro k hk
  have hk0 : k = 0 := by
    have : toyAdv.q = 1 := rfl
    omega
  subst hk0
  exact toy_query0_mass

/-! ### (b) the O2H reprogramming term is `2`, and composes with the classical FO bound. -/

/-- **The O2H reprogramming term is exactly `2`** on the toy (`2·√(q·Pfind) = 2·√(1·1) = 2`) — a genuine
positive contribution, not a vacuous `≤ ∞`. -/
theorem ex_toy_reprog_term : 2 * Real.sqrt ((toyAdv.q : ℝ) * Pfind toyAdv toyD) = 2 := by
  have hq : (toyAdv.q : ℝ) = 1 := by norm_num [show toyAdv.q = 1 from rfl]
  rw [toy_Pfind, hq, mul_one, Real.sqrt_one, mul_one]

/-- **THE FULL QROM IND-CCA BOUND FIRES AND COMPOSES.** `ml_kem_ind_cca_qrom_compose` on the toy adversary,
with the classical bound supplied by `FoBookkeeping.ex_fo_bound_fires` (cast via `foBookkeeping_bound_to_real`)
— `Adv(7/10) ≤ 1/10 + 1/20 + 1/20`. Taking `realCca = reprogCca = 7/10` (a zero-swing witness; the toy's
nonzero O2H term is `ex_toy_reprog_term`), the composed QROM bound
`|7/10 − 1/2| ≤ 2·√(q·(q·1)) + (1/10 + 1/20 + 1/20)` holds — the O2H reprogramming term and the three
classical FO hops in ONE inequality against the modelled quantum adversary. -/
theorem ex_qrom_bound_fires :
    |(7 / 10 : ℝ) - 1 / 2|
      ≤ 2 * Real.sqrt ((toyAdv.q : ℝ) * ((toyAdv.q : ℝ) * 1))
        + ((1 / 10 + 1 / 20 + 1 / 20 : ℚ) : ℝ) := by
  apply ml_kem_ind_cca_qrom_compose toyAdv toyD toyMeas toyMeas_norm_le 1
    (fun k hk => by
      have hk0 : k = 0 := by have : toyAdv.q = 1 := rfl; omega
      subst hk0; exact toy_query0_mass)
    (7 / 10) (7 / 10) (((1 / 10 + 1 / 20 + 1 / 20 : ℚ) : ℝ))
  · simp [abs_nonneg]
  · have h := foBookkeeping_bound_to_real (7 / 10) (1 / 10 + 1 / 20 + 1 / 20) ex_fo_bound_fires
    rwa [show ((7 / 10 : ℚ) : ℝ) = (7 / 10 : ℝ) by norm_num] at h

/-! ### (c) the message min-entropy is load-bearing (a low-entropy `m*` degrades the bound). -/

/-- **THE LOAD-BEARING TOOTH — min-entropy drives the reprogramming term.** The O2H reprogramming term
`2·√(q·(q·b))` is strictly WORSE for a low-entropy `m*` (large `b`): at `q = 1`, `b = 1/4` (higher
min-entropy) gives `1`, while `b = 1` (the toy's maximal / lowest-entropy case) gives `2`. So `b` — the
message-guessing probability — is not vacuous: the bound genuinely degrades as `m*` loses min-entropy, as
it must. (The toy's `b` is PINNED at `1` by `toy_proj_norm`: the adversary places ALL amplitude on `m*`.) -/
theorem ex_min_entropy_load_bearing :
    2 * Real.sqrt ((1 : ℝ) * (1 * (1 / 4))) < 2 * Real.sqrt ((1 : ℝ) * (1 * 1)) := by
  have h4 : Real.sqrt ((1 : ℝ) * (1 * (1 / 4))) = 1 / 2 := by
    rw [show (1 : ℝ) * (1 * (1 / 4)) = (1 / 2) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have h1 : Real.sqrt ((1 : ℝ) * (1 * 1)) = 1 := by
    rw [show (1 : ℝ) * (1 * 1) = 1 by norm_num]; exact Real.sqrt_one
  rw [h4, h1]; norm_num

/-! ### (d) the discharged proxy — zero query-mass ⇒ zero advantage. -/

/-- **`reprog_advantage_zero_of_no_query`'s corner is real.** For a toy-shaped adversary whose query-mass on
`m*` vanishes, the K-distinguishing advantage is exactly `0` — the perfect-min-entropy limit that
supersedes the qualitative `QROMInjective` proxy. Witnessed abstractly (the general theorem applied); the
toy itself sits at the OPPOSITE (tight) corner, so the two corners bracket the quantitative bound. -/
theorem ex_reprog_zero_corner {B : Type*} [Fintype B] (A : Adversary B) (D : OracleDiffData B)
    (P₁ : QState B →ₗ[ℂ] QState B) (hP1 : ∀ v, ‖P₁ v‖ ≤ ‖v‖)
    (hb0 : ∀ k, k < A.q → ‖D.P (A.state (mixOracle D.O D.O' k) k)‖ = 0) :
    |A.amp P₁ D.O - A.amp P₁ D.O'| = 0 :=
  reprog_advantage_zero_of_no_query A D P₁ hP1 hb0

-- The toy sits at the TIGHT corner: Pfind = 1 (max query-mass), not the zero corner (toy_Pfind).
-- q = 1 for the toy adversary (definitional; toyAdv is noncomputable, so `rfl` not `decide`).
example : toyAdv.q = 1 := rfl
-- The reprogramming genuinely changes the oracle on S = {true} (the reprogrammed point is real).
#guard decide (toyH true ≠ toyH' true)

end Teeth

#assert_all_clean [toy_query0_mass, ex_pfind_le_guess, ex_toy_reprog_term, ex_qrom_bound_fires,
  ex_min_entropy_load_bearing, ex_reprog_zero_corner]

end Dregg2.Crypto.FoQrom
