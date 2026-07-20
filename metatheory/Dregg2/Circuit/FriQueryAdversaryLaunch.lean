/-
# `Dregg2.Circuit.FriQueryAdversaryLaunch` — the NEW `(q, pow)` that buys REAL, PROVEN query-leg
# bits, as an in-tree THEOREM of the exact shape as the wave-1 vacuity refutation.

`FriQueryAdversary.lean` §5 proved the DEPLOYED query leg VACUOUS: at
`v1 (lb=3, q=38, pow=16)` / `IR-v2 (lb=6, q=19, pow=16)`, the adversary-quantified bound
`epsQueryAdv Q cardF k δ = Q · (1/cardF + (1−δ)^k)` hits `≥ 1` already at `Q = 2^31`
(`epsQueryAdv_deployed_vacuous_at_2_31`) — `~31` real bits at the proved radius `δ = 7/16`.

This file COMPUTES, as a machine-checked theorem over the SAME machinery (`epsQueryAdv`,
`epsQueryAdv_mono`, `epsQuery_nonneg` — reused, not re-derived), the honest `(q, pow)` that makes the
same leg NON-vacuous, and states exactly what it buys and where it STILL caps. Nothing here is a
calculator: every bit count below is a `norm_num` decision over the shipped field constant
`|F| = 2013265921` and its degree-4 extension.

## What moved, and why it is the honest lever

Two things are wrong with the deployed leg, and only one of them is a genuine parameter lever:

1. **The field.** `FriQueryAdversary:304` instantiates the fold term `1/cardF` at the BASE field
   `|F| = 2013265921 ≈ 2^30.9`. The deployed folding challenge `α` is drawn from the DEGREE-4
   EXTENSION (`plonky3_prover.PROD_EXT_DEGREE = 4`, `EF = BinomialExtensionField<BabyBear, 4>`,
   `|EF| = 2013265921^4 ≈ 2^123.63`, "the denominator of every per-fold proximity-gap bound"). Using
   `cardF = 2013265921^4` is a CORRECTION toward the deployed object, not a new assumption — wave-1
   already instantiated it there (`epsQueryAdv_ext_still_vacuous_at_2_32`). It moves the FOLD ceiling
   from `~31` to `~123.63` bits. It is NOT a `(q, pow)` change.

2. **The query count `q`.** At `δ = 7/16` each FRI spot-check buys only `−log₂(9/16) ≈ 0.83` bits, so
   `q = 38` buys `~31.5` bits of query term `(9/16)^38 ≈ 2^−31.54`. Once the field is corrected, THIS
   term is the binding one (`epsQueryAdv_ext_still_vacuous_at_2_32`: at ext field, `q = 38` is STILL
   vacuous at `2^32`). Raising `q` is the real lever. `q = 150` drives the query term to
   `(9/16)^150 ≈ 2^−124.5`, just below the fold term — so the leg reaches the field ceiling and the
   query count is no longer what caps it.

`q_isolates_the_lever_at_2_40` is the clean demonstration: at the SAME ext field and the SAME budget
`2^40`, `q = 38` is VACUOUS (`≥ 1`) while `q = 150` is `≤ 2^−80`. The `~80`-bit swing is `q` alone.

## ⚑ THE HONEST STATEMENT — a HARD field ceiling `q` cannot pass

`epsQueryAdv Q cardF k δ ≥ Q/cardF` unconditionally (`epsQueryAdv_ge_fold`). So the adversary-
quantified query leg is VACUOUS at `Q = cardF`, i.e. at `2^123.63`, NO MATTER how large `q` is —
`field_ceiling_vacuous_at_2_124`. The lever that moves THAT is `extDeg` (`+30.91` bits per degree),
which is NOT in scope here. The consequence is a TRADEOFF, not a free `100` bits:

    proven query-leg security  λ  against a  `Q ≤ 2^Qmax`  adversary  requires  λ + Qmax ≤ ~122.

So there is NO honest `"100 bits against a 2^128 adversary"` at BabyBear degree-4: `100 + 128 = 228 ≫ 122`.
What IS provable, and is proved here, is the split:

  * `launch_100bits_vs_2_22_adv`  — `100` bits against a `Q ≤ 2^22` query adversary.
  * `launch_60bits_vs_2_62_adv`   — `60`  bits against a `Q ≤ 2^62` query adversary (the strong-adversary
    reading; `2^62` is already `~half` the ext field, near the ceiling).

Both are the SAME `q = 150` config read at two operating points — pick the `(λ, Qmax)` split the
launch wants; the field caps their SUM.

## ⚑ AND THE `q`-INVARIANT SYSTEM CEILING SITS BELOW THIS LEG ANYWAY

This is ONE of four union-bound legs, and it is NOT the binding one for the deployed SYSTEM. The
commit-phase proximity error `ε_C ∝ |D⁰|²/|F|` (`FriLedger.friCommitLedger`, `commitBits`) reads
`~61` bits at the deployed worst-case height and carries NO `numQueries`/`powBits`, so no `q` or `pow`
bump can pass it (`fri_params_soundness_budget.rs::no_query_or_pow_bump_moves_the_eps_c_ceiling`).
`q = 150` is therefore chosen to lift THIS leg to the `~61`-bit `ε_C` ceiling — self-consistently
(`launch_at_2_62` gives `2^−61` against `2^62`) — so the query leg stops being the binding constraint,
NOT to claim the system is `100`-bit. The system posture remains `~61` bits, ceilinged by `ε_C`; the
lever for THAT is `extDeg`.

## ⚑ THE GRINDING KNOB `pow` — why it stays `16`, stated as arithmetic

In THIS union-bound model the grinding leg is a SEPARATE additive term `epsGrind Q pow = Q/2^pow`
(`FriVerifierCompose:323`), and at the deployed `pow = 16` it is ITSELF vacuous already at `Q = 2^16`
(`grind_pow16_vacuous_at_2_16`) — it carries no security above a `2^16` adversary. To make the grind
leg match the query leg's `2^22`/`100`-bit point you would need `pow ≥ 122`
(`grind_needs_pow122_for_2_22_100bit`), and `2^122` hashes is INFEASIBLE for the HONEST prover (grinding
costs the prover `2^pow`). So `pow` cannot carry union-bound security, and the proven bits here come
ENTIRELY from `q`; `pow` stays `16`. (Its real, un-modeled job is gating query-phase RETRIES — a
different accounting this file does not credit, so as not to overclaim.)

## Axiom hygiene
`#assert_all_clean` ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`, no fresh `axiom`,
no `native_decide`. ADDITIVE: no existing file is modified; the wave-1 lemmas are imported and reused.
-/
import Dregg2.Circuit.FriQueryAdversary

set_option autoImplicit false

namespace Dregg2.Circuit.FriQueryAdversaryLaunch

open Dregg2.Circuit.FriQueryAdversary (epsQueryAdv epsQueryAdv_mono epsQuery_nonneg)
open Dregg2.Circuit.FriVerifierCompose (epsQuery epsGrind)

/-! ## §1 — THE FIELD CEILING, `q`/`pow`-invariant.

The adversary-quantified query leg is bounded BELOW by the fold term `Q/cardF`. This is the ceiling
no query count and no grinding can move — only the field (`extDeg`) can. -/

/-- **`epsQueryAdv` DOMINATES its fold term `Q/cardF`.** The query term `Q·(1−δ)^k` is non-negative at
any radius `δ ≤ 1`, so the leg is at least the fold-collision density `Q/cardF`. This is the exact
sense in which the FIELD, not `q`, is the ceiling: raising `q` shrinks `(1−δ)^k`, never `1/cardF`. -/
theorem epsQueryAdv_ge_fold (Q cardF k : ℕ) (δ : ℝ) (hδ1 : δ ≤ 1) :
    (Q : ℝ) / (cardF : ℝ) ≤ epsQueryAdv Q cardF k δ := by
  unfold epsQueryAdv epsQuery
  have hq : (0 : ℝ) ≤ (Q : ℝ) := Nat.cast_nonneg Q
  have hpow : (0 : ℝ) ≤ (1 - δ) ^ k := pow_nonneg (by linarith) k
  have hexpand : (Q : ℝ) * (1 / (cardF : ℝ) + (1 - δ) ^ k)
      = (Q : ℝ) / (cardF : ℝ) + (Q : ℝ) * (1 - δ) ^ k := by ring
  rw [hexpand]
  nlinarith [mul_nonneg hq hpow]

/-- **⚑ THE HARD CEILING — vacuous at `2^124`, at ANY `q`, ANY `pow`.** Even at the correct extension
field and the raised `q = 150`, a `Q = 2^124`-query adversary drives the leg `≥ 1` — because
`2^124 / 2013265921^4 ≥ 1` already (`2013265921^4 ≈ 2^123.63`). The bound is written at `q = 150` to
make the point concrete, but by `epsQueryAdv_ge_fold` it holds at every `k`: the ceiling is the size of
the degree-4 extension field the folding challenge is drawn from, `~123.63` bits, and only `extDeg`
moves it. **This is why there is no honest `100` bits against a `2^128` adversary here.** -/
theorem field_ceiling_vacuous_at_2_124 :
    (1 : ℝ) ≤ epsQueryAdv (2 ^ 124) (2013265921 ^ 4) 150 (7 / 16) := by
  refine le_trans ?_ (epsQueryAdv_ge_fold (2 ^ 124) (2013265921 ^ 4) 150 (7 / 16) (by norm_num))
  norm_num

/-! ## §2 — ⚑ THE DELIVERABLE: the NON-vacuous adversary-quantified leg at the NEW `q = 150`.

Exact shape of the wave-1 vacuity theorem (`epsQueryAdv Q cardF k δ`), now bounded ABOVE by a real
target instead of below by `1`. The universally-quantified `∀ Q ≤ 2^Qmax` forms are the deliverable;
they follow from the value at the top of the range by `epsQueryAdv_mono` (reused). -/

/-- The core value: `100` bits at budget `2^22`. `2^22·(1/2013265921^4 + (9/16)^150) ≤ 2^−100`, decided
by `norm_num` over exact rationals. (Margin `~1` bit: the value is `≈ 2^−101`.) -/
theorem launch_at_2_22 :
    epsQueryAdv (2 ^ 22) (2013265921 ^ 4) 150 (7 / 16) ≤ 1 / 2 ^ 100 := by
  unfold epsQueryAdv epsQuery
  norm_num

/-- **⚑⚑ `100` BITS AGAINST A `Q ≤ 2^22` ADVERSARY.** For EVERY `Q`-query oracle adversary with
`Q ≤ 2^22`, the adversary-quantified query leg at `q = 150`, the extension field, and the proved
radius `δ = 7/16` is at most `2^−100`. Adversary-quantified (`epsQueryAdv` carries the `Q`), explicit
`ε`, NON-vacuous — the exact converse of `epsQueryAdv_deployed_vacuous_at_2_31`. -/
theorem launch_100bits_vs_2_22_adv (Q : ℕ) (hQ : Q ≤ 2 ^ 22) :
    epsQueryAdv Q (2013265921 ^ 4) 150 (7 / 16) ≤ 1 / 2 ^ 100 :=
  (epsQueryAdv_mono (2013265921 ^ 4) 150 (7 / 16) (by norm_num) hQ).trans launch_at_2_22

/-- The strong-adversary value: `60` bits at budget `2^62`. `2^62` is already `~half` the extension
field, near the ceiling — so this is close to the most a strong adversary can be charged here. -/
theorem launch_at_2_62 :
    epsQueryAdv (2 ^ 62) (2013265921 ^ 4) 150 (7 / 16) ≤ 1 / 2 ^ 60 := by
  unfold epsQueryAdv epsQuery
  norm_num

/-- **⚑ `60` BITS AGAINST A `Q ≤ 2^62` ADVERSARY** — the strong-adversary reading of the SAME `q = 150`
config. With the `100`-bit reading above it exhibits the field tradeoff `λ + Qmax ≤ ~122`: `100 + 22`
and `60 + 62` are two points on the same line, and their sum cannot exceed `~log₂|EF| − 1`. -/
theorem launch_60bits_vs_2_62_adv (Q : ℕ) (hQ : Q ≤ 2 ^ 62) :
    epsQueryAdv Q (2013265921 ^ 4) 150 (7 / 16) ≤ 1 / 2 ^ 60 :=
  (epsQueryAdv_mono (2013265921 ^ 4) 150 (7 / 16) (by norm_num) hQ).trans launch_at_2_62

/-! ## §3 — ⚑ `q` IS THE LEVER: same field, same budget, `38` vacuous vs `150` tiny. -/

/-- **The OLD `q = 38` is vacuous at `2^40`, EVEN at the corrected extension field.** The field
correction alone does not save `q = 38`: the surviving query term `(9/16)^38 ≈ 2^−31.54` dominates, so
`2^40·(9/16)^38 ≈ 2^8.46 ≥ 1`. (This is the ext-field companion of
`epsQueryAdv_ext_still_vacuous_at_2_32`, pushed to `2^40` to line up with the `q = 150` reading below.) -/
theorem q_lever_old38_vacuous_at_2_40 :
    (1 : ℝ) ≤ epsQueryAdv (2 ^ 40) (2013265921 ^ 4) 38 (7 / 16) := by
  unfold epsQueryAdv epsQuery
  norm_num

/-- **The NEW `q = 150` is `≤ 2^−80` at the SAME `2^40`, SAME field.** `2^40·(9/16)^150 ≈ 2^−84`. The
only thing that changed from the vacuous line above is `q : 38 → 150`, so the whole swing — bounded by
these two theorems as `≥ 1` down to `≤ 2^−80` (a `≥ 80`-bit move; the true values are `~2^8.5` and
`~2^−84`) — is attributable to `q` and nothing else: not the field, not `pow`. -/
theorem q_lever_new150_tiny_at_2_40 :
    epsQueryAdv (2 ^ 40) (2013265921 ^ 4) 150 (7 / 16) ≤ 1 / 2 ^ 80 := by
  unfold epsQueryAdv epsQuery
  norm_num

/-! ## §4 — ⚑ THE GRINDING KNOB `pow`: why `16` stays, as arithmetic (not prose). -/

/-- **The grind leg is vacuous at `2^16` with the deployed `pow = 16`.** `epsGrind Q 16 = Q/2^16`, so
`epsGrind (2^16) 16 = 1`. In the union-bound model grinding carries no security above a `2^16`
adversary — it is not what the launch bits rest on. -/
theorem grind_pow16_vacuous_at_2_16 :
    (1 : ℝ) ≤ epsGrind (2 ^ 16) 16 := by
  unfold epsGrind
  norm_num

/-- **`pow = 16` cannot even reach the `2^22` adversary the QUERY leg defeats.** `epsGrind (2^22) 16 =
2^6 = 64 ≥ 1`. So the query-leg `100`-bit statement above stands ENTIRELY on `q`; if grinding were
load-bearing at these budgets the leg would already be vacuous. -/
theorem grind_pow16_vacuous_at_2_22 :
    (1 : ℝ) ≤ epsGrind (2 ^ 22) 16 := by
  unfold epsGrind
  norm_num

/-- **What `pow` WOULD have to be — and why it is infeasible.** To match the query leg's
`(Qmax, λ) = (22, 100)` point through the grinding leg alone you need `pow ≥ 122`: `epsGrind (2^22) 122
= 2^−100`. But grinding costs the HONEST prover `2^pow` hashes, and `2^122` is not a thing a prover can
do. This is the arithmetic reason the union-bound grind leg cannot carry security and `pow` stays at
its cheap deployed `16`. -/
theorem grind_needs_pow122_for_2_22_100bit :
    epsGrind (2 ^ 22) 122 ≤ 1 / 2 ^ 100 := by
  unfold epsGrind
  norm_num

/-! ## Kernel-clean keystones. -/

#assert_all_clean [
  epsQueryAdv_ge_fold,
  field_ceiling_vacuous_at_2_124,
  launch_at_2_22,
  launch_100bits_vs_2_22_adv,
  launch_at_2_62,
  launch_60bits_vs_2_62_adv,
  q_lever_old38_vacuous_at_2_40,
  q_lever_new150_tiny_at_2_40,
  grind_pow16_vacuous_at_2_16,
  grind_pow16_vacuous_at_2_22,
  grind_needs_pow122_for_2_22_100bit
]

end Dregg2.Circuit.FriQueryAdversaryLaunch
