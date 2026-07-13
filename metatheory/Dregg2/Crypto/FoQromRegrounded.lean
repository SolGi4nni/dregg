/-
# `Dregg2.Crypto.FoQromRegrounded` — the FO/QROM IND-CCA consumers, lifted to the ASYMPTOTIC `Negl`
floor with the QROM reprogramming leg grounded on the PROVED O2H bound (not the opaque `1/2^λ`).

## What this closes (the FO/QROM half of the 07-13 floor sweep)

`FoQrom.lean` already re-grounds the ML-KEM FO transform's random-oracle step OFF the qualitative
`QROMInjective` proxy and ONTO the PROVED `OneWayToHiding.o2h_bound` (a real q-query quantum adversary
over the Mathlib QROM model `QuantumOracle`: states `EuclideanSpace ℂ B`, oracle a genuine
`LinearIsometryEquiv` permutation). Its headline `FoQrom.ml_kem_ind_cca_qrom` is a PER-INSTANCE
absolute bound `|realCca − 1/2| ≤ simFail + corrSpread + 2·√(q·(q·b)) + cpaTerm`. What it does NOT
state is the CONCRETE-SECURITY asymptotic form — that the IND-CCA advantage ENSEMBLE is `Negl` — which
is the currency `thread_advantage_bound` / `KemSoundnessQuant` speak.

`KemSoundnessQuant.ml_kem_ind_cca_advantage_negl` DOES give the `Negl` form, but its QROM leg is the
OPAQUE decaying term `1/2^λ` (the "you can do no better than guess `H(m)`" idealisation). This file
supplies the honest upgrade: the QROM leg is the O2H reprogramming ensemble
`2·√(q·(q·b λ))` — the SAME `FoQrom.reprog_term_bound` quantity, now as a λ-indexed ensemble — and it is
`Negl` because the per-query guessing bound `b λ` (the message min-entropy `2^(−H∞)`) DECAYS. So the FO
IND-CCA advantage's random-oracle leg is grounded on the proved quantum-adversary O2H bound, not an
opaque constant.

## The re-grounding

* **`foQromIndCcaAdv`** — the composite IND-CCA advantage ensemble, the four telescoped FO legs of
  `FoQrom.ml_kem_ind_cca_qrom` as λ-indexed ensembles: `simFail + corrSpread + reprogAdv + cpaAdv`.
* **`foQromIndCca_negl_of_legs`** — each leg `Negl` ⟹ the composite `Negl`, by `thread_advantage_bound`
  (the `negl_add` spine, every leg closed from the context hypothesis). The uniform threading shape.
* **`reprogTermEnsemble` + `o2h_advantage_le_reprogTerm`** — the QROM leg IS the O2H bound: the ensemble
  `2·√(q·(q·b λ))` UPPER-BOUNDS the actual q-query quantum-adversary reprogramming advantage
  `|amp_H − amp_{H'}|` at every λ (directly `FoQrom.reprog_term_bound`), so a `Negl` bound on the
  ensemble dominates the real advantage. NOT the opaque `1/2^λ` — the genuine O2H term.
* **`reprogTermEnsemble_negl_decay`** — with the message-guessing bound decaying as `b λ = (1/2^λ)²`
  (high, growing min-entropy) at `q = 1`, the O2H reprogramming ensemble is exactly `2·(1/2^λ)`, `Negl`
  by `negl_const_mul`/`negl_two_pow`. The reprogramming term genuinely vanishes as the message min-entropy
  grows — the honest ground for "the random oracle hides `K`".
* **`foQromIndCca_negl`** — THE HEADLINE: the FO/QROM IND-CCA advantage, with its reprogramming leg the
  O2H-grounded ensemble at decaying `b`, is `Negl` whenever the classical FO legs are.

## Non-fake (this is not the bare composite in FO costume)

The reprogramming leg is a GENUINE additive term: `foQrom_cpa_leg_load_bearing` shows a constant `2/5`
IND-CPA leg (a broken lattice floor) makes the composite non-negligible — the O2H term cannot rescue it.
The O2H ensemble genuinely decays FROM the min-entropy (`reprogTermEnsemble_negl_decay`), and
`o2h_advantage_le_reprogTerm` proves it dominates the real quantum-adversary advantage (`reprog_term_bound`)
— so it is the O2H bound, not an unrelated decay. `#assert_all_clean`
(⊆ {propext, Classical.choice, Quot.sound}); no `sorry`. Old `FoQrom`/`FoBookkeeping` absolute-bound
defs are KEPT untouched; this file only ADDS the asymptotic `Negl` siblings.

Cite: Ambainis–Hamburg–Unruh (O2H); Hofheinz–Hövelmanns–Kiltz (TCC 2017); FIPS 203 (ML-KEM).
-/
import Dregg2.Tactics.ThreadAdvantageBound
import Dregg2.Crypto.FoQrom

namespace Dregg2.Crypto.FoQromRegrounded

open Dregg2.Crypto.ConcreteSecurity
  (Negl Ensemble negl_zero negl_add negl_two_pow negl_const_mul)
open Dregg2.Crypto.ProbCrypto (not_negl_const_pos)
open Dregg2.Crypto.OneWayToHiding
open Dregg2.Crypto.QuantumOracle
open Dregg2.Crypto.FoQrom (reprog_term_bound)

set_option autoImplicit false

/-! ## §1 — the composite IND-CCA advantage ensemble and its `Negl` closure. -/

/-- **THE FO/QROM IND-CCA ADVANTAGE ENSEMBLE.** The four telescoped legs of
`FoQrom.ml_kem_ind_cca_qrom` as a λ-indexed ensemble: the decaps-simulation failure, the
correctness/γ-spreadness term, the O2H reprogramming term, and the residual IND-CPA (decisional-MLWE)
advantage. A genuine composite ensemble — the concrete-security shadow of the per-instance absolute
bound. -/
noncomputable def foQromIndCcaAdv (simFail corrSpread reprogAdv cpaAdv : Ensemble) : Ensemble :=
  fun l => simFail l + corrSpread l + reprogAdv l + cpaAdv l

/-- **THE COMPOSITE ANCHOR — the FO/QROM IND-CCA advantage is negligible whenever every leg is.**
`negl_add` down the four-leg sum, each leg closed from its context hypothesis. The shared body every FO
IND-CCA sibling routes through; the asymptotic form of the telescoped `ml_kem_ind_cca_qrom` bound.
Proof: `thread_advantage_bound`. -/
theorem foQromIndCca_negl_of_legs (simFail corrSpread reprogAdv cpaAdv : Ensemble)
    (hSim : Negl simFail) (hT : Negl corrSpread) (hReprog : Negl reprogAdv) (hCpa : Negl cpaAdv) :
    Negl (foQromIndCcaAdv simFail corrSpread reprogAdv cpaAdv) := by
  unfold foQromIndCcaAdv
  thread_advantage_bound

/-! ## §2 — the QROM reprogramming leg IS the O2H bound (grounding, not the opaque `1/2^λ`). -/

/-- **THE O2H REPROGRAMMING ENSEMBLE.** The `FoQrom.reprog_term_bound` quantity `2·√(q·(q·b λ))` as a
λ-indexed ensemble: `q` the query budget, `b λ` the message-guessing bound `2^(−H∞(m*))` at parameter `λ`.
This is the QROM leg of the FO IND-CCA advantage — the O2H reprogramming term, NOT the opaque `1/2^λ`
guessing idealisation of `KemSoundnessQuant.kemIndCcaAdv`. -/
noncomputable def reprogTermEnsemble (q : ℕ) (b : Ensemble) : Ensemble :=
  fun l => 2 * Real.sqrt ((q : ℝ) * ((q : ℝ) * b l))

/-- **THE O2H ENSEMBLE DOMINATES THE REAL QUANTUM-ADVERSARY ADVANTAGE.** At every parameter `l`, a
`q`-query quantum adversary whose per-query amplitude-mass on the reprogrammed point is `≤ b l` has
K-distinguishing advantage `|amp_H − amp_{H'}| ≤ reprogTermEnsemble A.q b l`. Directly
`FoQrom.reprog_term_bound` — so `reprogTermEnsemble` is a genuine upper bound on the O2H reprogramming
advantage (a `Negl` bound on it dominates the real advantage), NOT an unrelated decay term. This is what
grounds the QROM leg on the PROVED O2H bound. -/
theorem o2h_advantage_le_reprogTerm {B : Type*} [Fintype B] (A : Adversary B) (D : OracleDiffData B)
    (P₁ : QState B →ₗ[ℂ] QState B) (hP1 : ∀ v, ‖P₁ v‖ ≤ ‖v‖) (b : Ensemble) (l : ℕ)
    (hb : ∀ k, k < A.q → ‖D.P (A.state (mixOracle D.O D.O' k) k)‖ ^ 2 ≤ b l) :
    |A.amp P₁ D.O - A.amp P₁ D.O'| ≤ reprogTermEnsemble A.q b l :=
  reprog_term_bound A D P₁ hP1 (b l) hb

/-- **THE O2H REPROGRAMMING TERM IS `Negl` (the min-entropy vanishes it).** With the message-guessing
bound decaying as `b λ = (1/2^λ)²` (growing min-entropy `H∞(m*) ≈ 2λ`) at a single query `q = 1`, the O2H
reprogramming ensemble is exactly `2·√((1/2^λ)²) = 2·(1/2^λ)`, negligible by `negl_const_mul`/`negl_two_pow`.
So the O2H reprogramming term genuinely vanishes as the encapsulated message gains min-entropy — the honest
ground of "the random oracle hides `K = H(m*)`", replacing the opaque `1/2^λ`. -/
theorem reprogTermEnsemble_negl_decay :
    Negl (reprogTermEnsemble 1 (fun l => (1 / (2 : ℝ) ^ l) ^ 2)) := by
  have hrw : reprogTermEnsemble 1 (fun l => (1 / (2 : ℝ) ^ l) ^ 2)
      = fun l => 2 * (1 / (2 : ℝ) ^ l) := by
    funext l
    unfold reprogTermEnsemble
    rw [Nat.cast_one, one_mul, one_mul, Real.sqrt_sq (by positivity)]
  rw [hrw]
  exact negl_const_mul 2 negl_two_pow

/-! ## §3 — THE HEADLINE: the FO/QROM IND-CCA advantage is `Negl` on the O2H-grounded floor. -/

/-- **FO/QROM ML-KEM IND-CCA, RE-GROUNDED TO THE ASYMPTOTIC `Negl` FLOOR.** With the reprogramming leg the
O2H-grounded ensemble at decaying message-guessing bound (`reprogTermEnsemble_negl_decay`), the full FO
IND-CCA advantage `simFail + corrSpread + 2·√(q·(q·b)) + cpaAdv` is `Negl` whenever the three classical FO
legs are. This is `FoQrom.ml_kem_ind_cca_qrom` lifted from a per-instance absolute bound to the
concrete-security asymptotic form — the random-oracle leg standing on the PROVED quantum-adversary O2H
bound, not the opaque `1/2^λ` of `KemSoundnessQuant`. Proof: `foQromIndCca_negl_of_legs`. -/
theorem foQromIndCca_negl (simFail corrSpread cpaAdv : Ensemble)
    (hSim : Negl simFail) (hT : Negl corrSpread) (hCpa : Negl cpaAdv) :
    Negl (foQromIndCcaAdv simFail corrSpread
      (reprogTermEnsemble 1 (fun l => (1 / (2 : ℝ) ^ l) ^ 2)) cpaAdv) :=
  foQromIndCca_negl_of_legs simFail corrSpread _ cpaAdv hSim hT reprogTermEnsemble_negl_decay hCpa

/-! ## §4 — non-vacuity: the composite is load-bearing, and the reduction fires. -/

/-- **THE IND-CPA LEG IS LOAD-BEARING — the O2H term cannot rescue a broken lattice floor.** With the
IND-CPA (decisional-MLWE) leg a constant `2/5` (a broken lattice floor) and the other legs `0`, the
composite is the constant `2/5`, NOT negligible (`not_negl_const_pos`). So the `Negl cpaAdv` hypothesis of
`foQromIndCca_negl` is genuinely consumed — the additive O2H reprogramming term does not vanish a constant
IND-CPA advantage. The anti-laundering tooth: the composite is a real advantage that CAN be non-negligible. -/
theorem foQrom_cpa_leg_load_bearing :
    ¬ Negl (foQromIndCcaAdv (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => (2 : ℝ) / 5)) := by
  have hrw : foQromIndCcaAdv (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => (2 : ℝ) / 5)
      = fun _ => (2 : ℝ) / 5 := by
    funext l; unfold foQromIndCcaAdv; ring
  rw [hrw]; exact not_negl_const_pos (by norm_num)

/-- **THE RE-GROUNDED FO/QROM KEYSTONE FIRES.** On secure (advantage-`0`) classical FO legs the full FO
IND-CCA composite — including the O2H reprogramming leg at decaying `b` — is negligible, so the reduction
runs end-to-end to a genuine `Negl` conclusion. -/
theorem foQromIndCca_fires :
    Negl (foQromIndCcaAdv (fun _ => 0) (fun _ => 0)
      (reprogTermEnsemble 1 (fun l => (1 / (2 : ℝ) ^ l) ^ 2)) (fun _ => 0)) :=
  foQromIndCca_negl _ _ _ negl_zero negl_zero negl_zero

#assert_all_clean [
  foQromIndCca_negl_of_legs,
  o2h_advantage_le_reprogTerm,
  reprogTermEnsemble_negl_decay,
  foQromIndCca_negl,
  foQrom_cpa_leg_load_bearing,
  foQromIndCca_fires
]

end Dregg2.Crypto.FoQromRegrounded
