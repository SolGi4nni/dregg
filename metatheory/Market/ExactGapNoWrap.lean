/-
# Market.ExactGapNoWrap — Weld B: the in-STARK exact gap is no-wrap-faithful.

**"The ε the keystone reads is the TRUE gap, never a modular wrap."** This module closes the loop
between the no-wrap refinement (`Market.MintSafeQuantization.field_gate_refines_nat_eq`,
`Dregg2.Bignum.legs_noWrap_conservation`) and the exact-disposes architecture
(`Market.MintSafeQuantization.exact_gap_feeds_keystone`, `Market.CertF.certifies_epsilon_optimal`).

The STARK recomputes the `Cert-F` duality gap `G = cᵀs − wᵀf` as a FIELD (`ZMod p`) quantity. On its own
a field-recomputed gap is a *modular* quantity: a wrap of `p` mints a phantom gap (a value-minting
discrepancy the keystone would then read as ε). The `VALUE_BITS` no-wrap discipline pins both totals
below `p`; under it the field-recomputed gap `fieldGap` provably equals the EXACT integer gap
`dualVal − primalVal`, and feeding it to the keystone certifies ε-optimality with ε = the true gap.

## What is proved (honest scope)

  1. **`fieldGap_refines`** — model `dualVal = cᵀs` and `primalVal = wᵀf` as no-wrap-bounded ℕ totals.
     If the STARK's field-recomputed gap `fieldGap : ℕ` satisfies the field agreement
     `dualVal ≡ primalVal + fieldGap [mod p]` and BOTH `primalVal + fieldGap < p`, `dualVal < p`, then
     `dualVal = primalVal + fieldGap` over ℕ — the recomputed gap is the exact integer gap, no wrap.
     A direct instance of `field_gate_refines_nat_eq` (`outSum := primalVal`, `burn := fieldGap`,
     `inSum := dualVal`). `dualVal ≥ primalVal` (so the exact gap is a genuine ℕ) is `gap_nonneg`.

  2. **`fieldGap_refines_via_bignum`** — the SAME refinement re-derived through the anti-wraparound
     keystone `Dregg2.Bignum.legs_noWrap_conservation` on the legs `[primalVal, fieldGap]` vs `[dualVal]`,
     with the `VALUE_BITS` bound `x < 2ⁿ` per limb and `k·2ⁿ ≤ p`. Ties the gap refinement to the deployed
     `shielded_ring_clearing_air.rs::VALUE_BITS` limb discipline.

  3. **`dualVal_ge_primalVal`** — from `gap_nonneg`: the certified gap `cᵀs − wᵀf ≥ 0`, so the ℕ
     `fieldGap = dualVal − primalVal` never underflows. This is why the totals can be modeled in ℕ.

  4. **`exact_gap_noWrap_feeds_keystone` (THE LOOP CLOSED)** — compose (1) with `exact_gap_feeds_keystone`.
     Given the no-wrap bounds + field agreement making `fieldGap` exact, and the LP witness whose exact
     integer totals are `dualVal`, `primalVal` (with ε set to `fieldGap`), EVERY primal-feasible `f'`
     obeys `wᵀf' ≤ wᵀf + fieldGap` AND `fieldGap = exactGap lp f π s`. So the keystone's ε-optimality
     holds with ε = the EXACT gap, never a wrapped value.

  5. **Non-vacuity, both polarities.** (a) `worked_fieldGap_refines` / `worked_fieldGap_noWrap` — the
     `ringLP` optimum (`dualVal = 3`, `primalVal = 3`, `fieldGap = 0`) refines exactly and feeds the
     keystone. (b) `fieldGap_without_range_mints` — WITHOUT the range bound, at `p = 5`, a field-equal gap
     `fieldGap = 5` mints where the true gap is `0` (`primalVal + fieldGap = dualVal + p`): a value-minting
     wrapped gap. The no-wrap bound is genuinely load-bearing.

Pure. Nothing charged to ε: the field recomputation, once pinned below `p`, IS the exact gap.
-/
import Market.MintSafeQuantization
import Dregg2.Bignum
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith

namespace Market

open Matrix

/-! ## 1. `fieldGap_refines` — the field-recomputed gap is the exact integer gap (no wrap).

`dualVal = cᵀs` and `primalVal = wᵀf` are the two duality-gap components, each pinned `< p` by the
`VALUE_BITS` no-wrap bound. The STARK recomputes the gap as a field element `fieldGap : ℕ` satisfying the
field agreement `dualVal ≡ primalVal + fieldGap [mod p]`. With both sides `< p` the congruence IS an
integer equality: `dualVal = primalVal + fieldGap`, i.e. `fieldGap` is exactly `dualVal − primalVal`. -/

/-- **`fieldGap_refines` — the no-wrap-faithful gap.** Model the gap components as no-wrap-bounded ℕ
totals `dualVal = cᵀs`, `primalVal = wᵀf`. If the STARK's field-recomputed gap `fieldGap : ℕ` satisfies
the field agreement `((primalVal + fieldGap : ℕ) : ZMod p) = ((dualVal : ℕ) : ZMod p)` AND both
`primalVal + fieldGap < p`, `dualVal < p` (the `VALUE_BITS` no-wrap discipline), then the recomputed gap
is the EXACT integer gap: `dualVal = primalVal + fieldGap`. Direct use of `field_gate_refines_nat_eq`
with `outSum := primalVal`, `burn := fieldGap`, `inSum := dualVal`. Without the bounds it mints
(`fieldGap_without_range_mints`). -/
theorem fieldGap_refines {p primalVal dualVal fieldGap : ℕ}
    (hleft : primalVal + fieldGap < p) (hright : dualVal < p)
    (hfield : ((primalVal + fieldGap : ℕ) : ZMod p) = ((dualVal : ℕ) : ZMod p)) :
    dualVal = primalVal + fieldGap :=
  (field_gate_refines_nat_eq hleft hright hfield).symm

/-- **`fieldGap_refines_via_bignum` — the same refinement through the anti-wraparound keystone.** The gap
components are the two limbs `[primalVal, fieldGap]` conserved against `[dualVal]`; each limb obeys the
`VALUE_BITS` bound `x < 2ⁿ` and `k·2ⁿ ≤ p` bounds the total range. `Dregg2.Bignum.legs_noWrap_conservation`
then upgrades the modular congruence `(primalVal + fieldGap) % p = dualVal % p` to the exact ℕ equality.
This ties the field-gap refinement to the deployed limb discipline (`shielded_ring_clearing_air.rs`). -/
theorem fieldGap_refines_via_bignum {n p primalVal dualVal fieldGap : ℕ}
    (hp : 0 < p)
    (hpr : primalVal < 2 ^ n) (hfg : fieldGap < 2 ^ n) (hdu : dualVal < 2 ^ n)
    (hlenOut : 2 * 2 ^ n ≤ p) (hlenIn : 1 * 2 ^ n ≤ p)
    (hcong : (primalVal + fieldGap) % p = dualVal % p) :
    dualVal = primalVal + fieldGap := by
  have h := Dregg2.Bignum.legs_noWrap_conservation (n := n) (p := p)
      (as := [primalVal, fieldGap]) (bs := [dualVal]) hp
      (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with h | h <;> subst h <;> assumption)
      (by intro x hx; simp only [List.mem_singleton] at hx; subst hx; exact hdu)
      (by simpa using hlenOut)
      (by simpa using hlenIn)
      (by simpa using hcong)
  simpa using h.symm

/-! ## 2. `dualVal_ge_primalVal` — `gap_nonneg` keeps the exact gap in ℕ.

Modeling `fieldGap = dualVal − primalVal` in ℕ is sound precisely because the certified gap is
`≥ 0` (`Market.CertF.gap_nonneg`): weak duality forces `cᵀs ≥ wᵀf`, so `dualVal ≥ primalVal` and the ℕ
subtraction never underflows. -/

/-- **`dualVal_ge_primalVal` — the exact gap is a genuine ℕ.** For a feasible LP witness whose integer
totals are `cᵀs = dualVal`, `wᵀf = primalVal`, `gap_nonneg` (`cᵀs − wᵀf ≥ 0`) gives `primalVal ≤ dualVal`.
So `fieldGap = dualVal − primalVal ≥ 0` — the totals are legitimately modeled in ℕ. -/
theorem dualVal_ge_primalVal {V E : Type*} [Fintype V] [Fintype E]
    (lp : FlowLP V E ℤ) {f : E → ℤ} {π : V → ℤ} {s : E → ℤ} {primalVal dualVal : ℕ}
    (hf : PrimalFeasible lp f) (hd : DualFeasible lp π s)
    (hdual : lp.c ⬝ᵥ s = (dualVal : ℤ)) (hprimal : lp.w ⬝ᵥ f = (primalVal : ℤ)) :
    (primalVal : ℤ) ≤ (dualVal : ℤ) := by
  have hnn := gap_nonneg lp hf hd
  rw [hdual, hprimal] at hnn
  linarith

/-! ## 3. `exact_gap_noWrap_feeds_keystone` — THE LOOP CLOSED (no-wrap refinement ⇒ keystone on the true gap).

Compose §1 with `Market.MintSafeQuantization.exact_gap_feeds_keystone`. Under the no-wrap bounds the
field-recomputed `fieldGap` equals the exact integer gap `exactGap lp f π s`; feeding it as ε certifies
ε-optimality with ε = the TRUE gap. The STARK never reads a wrapped value. -/

/-- **`exact_gap_noWrap_feeds_keystone` — the closed loop.** Given the no-wrap bounds + field agreement
(`fieldGap` is exact, §1) and an LP witness `(f, π, s)` whose exact integer totals are `cᵀs = dualVal`,
`wᵀf = primalVal`, with the LP's accuracy target set to the recomputed gap `ε = fieldGap`: EVERY
primal-feasible `f'` obeys `wᵀf' ≤ wᵀf + fieldGap`, AND `fieldGap = exactGap lp f π s`. So the keystone's
ε-optimality holds with ε = the EXACT gap — the field recomputation, pinned below `p`, feeds the true
gap, never a modular wrap. -/
theorem exact_gap_noWrap_feeds_keystone {V E : Type*} [Fintype V] [Fintype E]
    {p primalVal dualVal fieldGap : ℕ}
    (hleft : primalVal + fieldGap < p) (hright : dualVal < p)
    (hfield : ((primalVal + fieldGap : ℕ) : ZMod p) = ((dualVal : ℕ) : ZMod p))
    (lp : FlowLP V E ℤ) {f : E → ℤ} {π : V → ℤ} {s : E → ℤ}
    (hf : PrimalFeasible lp f) (hd : DualFeasible lp π s)
    (hdual : lp.c ⬝ᵥ s = (dualVal : ℤ)) (hprimal : lp.w ⬝ᵥ f = (primalVal : ℤ))
    (hε : lp.ε = (fieldGap : ℤ))
    {f' : E → ℤ} (hf' : PrimalFeasible lp f') :
    lp.w ⬝ᵥ f' ≤ lp.w ⬝ᵥ f + (fieldGap : ℤ)
      ∧ (fieldGap : ℤ) = exactGap lp f π s := by
  -- §1: the field-recomputed gap is the exact integer gap
  have hnat : dualVal = primalVal + fieldGap := fieldGap_refines hleft hright hfield
  -- the exact gap over ℤ equals the recomputed fieldGap
  have hgapexact : exactGap lp f π s = (fieldGap : ℤ) := by
    unfold exactGap
    rw [hdual, hprimal]
    have hz : (dualVal : ℤ) = (primalVal : ℤ) + (fieldGap : ℤ) := by exact_mod_cast hnat
    linarith
  -- the gap clause holds with equality once ε := fieldGap
  have hgap : lp.c ⬝ᵥ s - lp.w ⬝ᵥ f ≤ lp.ε := by
    have heq : lp.c ⬝ᵥ s - lp.w ⬝ᵥ f = lp.ε := by
      have : exactGap lp f π s = lp.ε := by rw [hgapexact, hε]
      simpa [exactGap] using this
    exact le_of_eq heq
  refine ⟨?_, hgapexact.symm⟩
  have hkey := exact_gap_feeds_keystone lp hf hd hgap hf'
  rwa [hε] at hkey

/-! ## 4. Non-vacuity, POSITIVE polarity — the `ringLP` optimum refines exactly and feeds the keystone.

The verified 3-cycle (`Market.CertF.ringLP`): `cᵀs = 3` (`dualVal`), `wᵀf = 3` (`primalVal`), so the exact
gap is `0` (`fieldGap = 0`). At the BabyBear prime `p = 2013265921` both totals are far below `p`; the
field agreement `(3 + 0 : ZMod p) = (3 : ZMod p)` holds, and the refinement recovers `3 = 3 + 0`. -/

/-- **`worked_fieldGap_refines` — the refinement, worked.** The `ringLP` optimum's gap components
(`primalVal = 3`, `fieldGap = 0`, `dualVal = 3`) refine through `fieldGap_refines` at `p = 2013265921`:
the field-recomputed gap `0` is exactly the integer gap `3 − 3`. -/
theorem worked_fieldGap_refines : (3 : ℕ) = 3 + 0 :=
  fieldGap_refines (p := 2013265921) (by norm_num) (by norm_num) (by norm_num)

/-- **`worked_fieldGap_noWrap` — the closed loop, worked on `ringLP`.** The full composition: under the
no-wrap bounds the field-recomputed gap `0` is exact, and the keystone certifies EVERY feasible `f'` at
`wᵀf' ≤ wᵀringF + 0 = 3` — with ε read as the TRUE gap `exactGap ringLP ringF ringπ ringS = 0`, never a
wrapped value. `approximation proposes, exact no-wrap disposes`, end to end. -/
theorem worked_fieldGap_noWrap {f' : Fin 3 → ℤ} (hf' : PrimalFeasible ringLP f') :
    ringLP.w ⬝ᵥ f' ≤ ringLP.w ⬝ᵥ ringF + ((0 : ℕ) : ℤ)
      ∧ ((0 : ℕ) : ℤ) = exactGap ringLP ringF ringπ ringS :=
  exact_gap_noWrap_feeds_keystone
    (p := 2013265921) (primalVal := 3) (dualVal := 3) (fieldGap := 0)
    (by norm_num) (by norm_num) (by norm_num)
    ringLP ringCert_valid.1 ringCert_valid.2.1
    (by simp [ringLP, ringS, dotProduct])
    (by simp [ringLP, ringF, dotProduct])
    (by simp [ringLP])
    hf'

/-! ## 5. Non-vacuity, NEGATIVE polarity — WITHOUT the range bound a wrapped gap MINTS.

The no-wrap bound is load-bearing. At `p = 5`, `primalVal = 0`, `dualVal = 0`: the true gap is `0`. But a
field-recomputed `fieldGap = 5` is FIELD-EQUAL (`(0 + 5 : ZMod 5) = 0 = (0 : ZMod 5)`) while the integer
relation reads `primalVal + fieldGap = dualVal + p` — a phantom gap of a whole `p`, the value-minting
wrap. Exactly the discrepancy `fieldGap_refines`' bound `primalVal + fieldGap < p` forbids. -/

/-- **`fieldGap_without_range_mints` — the wrapped gap mints without the bound.** At `p = 5`,
`primalVal = 0`, `dualVal = 0`, `fieldGap = 5`: the field agreement
`((primalVal + fieldGap : ℕ) : ZMod p) = ((dualVal : ℕ) : ZMod p)` holds, yet `dualVal ≠ primalVal +
fieldGap` and precisely `primalVal + fieldGap = dualVal + p` — a value-minting gap of a full `p` that the
STARK would read as ε. This is why `fieldGap_refines` requires `primalVal + fieldGap < p`: the no-wrap
bound is genuinely load-bearing. -/
theorem fieldGap_without_range_mints :
    ∃ (p primalVal dualVal fieldGap : ℕ),
      ((primalVal + fieldGap : ℕ) : ZMod p) = ((dualVal : ℕ) : ZMod p) ∧
      dualVal ≠ primalVal + fieldGap ∧
      primalVal + fieldGap = dualVal + p :=
  ⟨5, 0, 0, 5, by decide, by decide, by decide⟩

/-! ### `#guard` smoke — the gap components + the wrap are COMPUTED, not asserted. -/

-- the ringLP optimum's exact gap components: cᵀs = 3 (dualVal), wᵀf = 3 (primalVal), gap = 0:
#guard (ringLP.c ⬝ᵥ ringS) == 3
#guard (ringLP.w ⬝ᵥ ringF) == 3
#guard exactGap ringLP ringF ringπ ringS == 0
-- the field-recomputed gap of the optimum is exact: dualVal = primalVal + fieldGap (3 = 3 + 0):
#guard (3 : ℕ) == 3 + 0
-- the negative polarity: fieldGap = 5 is FIELD-equal to gap 0 mod 5 …
#guard ((0 + 5) % 5) == (0 % 5)
-- … yet mints a full p over ℕ (5 ≠ 0) — the wrap the no-wrap bound forbids:
#guard ((0 + 5 : ℕ) == 0) == false

/-! ### Axiom hygiene — the no-wrap-faithful exact-gap weld pinned kernel-clean. -/

#assert_all_clean [Market.fieldGap_refines, Market.fieldGap_refines_via_bignum,
  Market.dualVal_ge_primalVal, Market.exact_gap_noWrap_feeds_keystone,
  Market.worked_fieldGap_refines, Market.worked_fieldGap_noWrap,
  Market.fieldGap_without_range_mints]

end Market
