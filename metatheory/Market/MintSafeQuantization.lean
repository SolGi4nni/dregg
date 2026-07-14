/-
# Market.MintSafeQuantization — the sound-quantized Tier-0 foundation: mint-safety + the no-wrap refinement.

**"Approximation PROPOSES; exact quantized translation-validation DISPOSES."** This is codex Round-3 Q1
made real (`docs/deos/FHEGG-CODEX-ROUND3.md`, headline + §B/Q1). The correction codex forced on the
brief's own ε-absorption premise: you **cannot** charge approximate feasibility to `ε` and reuse
`Market.CertF.certifies_epsilon_optimal`, because the deployed `Certified` predicate
(`Market/CertF.lean:97`) demands **exact** primal + dual feasibility (`A f = 0`, `0 ≤ f ≤ c`,
`Aᵀπ + s ≥ w`). The sound architecture instead:

  1. runs the cheap **approximate** encrypted solver (CKKS/BFV, carry-free adds) as an *untrusted search*;
  2. **EXACTIFIES** the candidate onto the integer grid → an exactly-feasible `(f, π, s)`;
  3. the checker recomputes the **exact** gap `G_q = cᵀs − wᵀf` and feeds it VERBATIM to the
     already-proven keystone — the honest certified target is literally `ε_cert = G_q`.

**Quantization / FHE / iteration noise governs COMPLETENESS (does the candidate pass, how large is `G_q`)
and PARAMETER SIZING — never SOUNDNESS.** The keystone only ever sees the exact recomputed gap.

## What is proved (honest scope)

This module proves the two lemmas that make the *soundness discipline* of the quantized fold real, and
wires them to the keystone. It is deliberately kept SEPARATE from the ε-optimality core:

  * **soundness = conservation** = `mint_safe_quantization` (this file) — a cheap INTEGER gate provably
    forbids a mint of the true rational values, *within tolerance*, via **directional rounding**;
  * **optimality = ε** = `Market.CertF.certifies_epsilon_optimal` (the keystone) — the exact recomputed
    gap bounds suboptimality.

  1. **`mint_safe_quantization`.** With outputs OVER-approximated by their integer proxy
     (`vout ≤ Δ·qout`) and inputs UNDER-approximated (`Δ·qin ≤ vin`), the cheap integer gate
     `Σ qout ≤ Σ qin` PROVABLY implies `Σ vout ≤ Σ vin` — no mint within the quantization tolerance. The
     rounding directionality is the load-bearing subtlety: flip it and the gate no longer forbids a mint.
  2. **`field_gate_refines_nat_eq`.** A field / modular equality WITHOUT range bounds does NOT imply the
     ℕ equality — that discrepancy of `p` is exactly a modular mint. WITH the no-wrap range bounds (the
     `VALUE_BITS` discipline, cf. `Dregg2.Bignum.legs_noWrap_conservation`) it does. This is the
     exactify step's soundness: the exact gap recomputed on the integer grid is the REAL gap, no wrap.
  3. **The architecture tie** (`exactGap` / `exactified_certified` / `exact_gap_feeds_keystone`) — the
     exactified candidate's EXACT gap is fed to `certifies_epsilon_optimal` verbatim; the keystone never
     sees a noise term. Non-vacuity at both polarities: an honest quantized clearing passes the gate; a
     genuine mint (with the correct directional rounding) is REJECTED by it.

**Honest scope.** This is the SOUNDNESS FOUNDATION for the quantized Tier-0 fold — the mint-safety
discipline + the no-wrap refinement + the exact-disposes tie. The concrete FHE scheme (BDLOP additive
commitment for binding, exact-quantized BFV/BGV for the carry-free fold, CHIMERA/PEGASUS scheme-switch
to TFHE for the crossing) is the separate hardware/crypto build, NOT this Lean. Nothing here is charged
to ε: soundness stays exact.

Pure.
-/
import Market.CertF
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith

namespace Market

open Matrix

/-! ## 1. `mint_safe_quantization` — the mint-safe conservative-rounding rule (soundness = conservation).

The cheap check the encrypted fold performs is the INTEGER gate `Σ qout ≤ Σ qin`. To make that gate a
sound refusal of a real (rational-valued) mint, the quantization must round in the mint-safe direction:
**outputs OVER, inputs UNDER**. Then the integer gate provably sandwiches the true totals:

    Σ vout  ≤  Σ Δ·qout  =  Δ·Σ qout  ≤  Δ·Σ qin  =  Σ Δ·qin  ≤  Σ vin.

The middle inequality is the gate, scaled by `Δ ≥ 0`; the two ends are the rounding directions. This is
strictly the CONSERVATION half — it says nothing about optimality (that is `ε`, the keystone's job). -/

/-- **`mint_safe_quantization` — the mint-safe rule.** Outputs over-approximated by their integer proxy
(`hout : vout j ≤ Δ · qout j`), inputs under-approximated (`hin : Δ · qin i ≤ vin i`), step `Δ ≥ 0`. Then
the cheap INTEGER gate `Σ qout ≤ Σ qin` (`hgate`) PROVABLY forbids a mint: `Σ vout ≤ Σ vin`. The
directionality is load-bearing — flip either rounding and the gate no longer bounds the true totals. -/
theorem mint_safe_quantization
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Δ : ℚ) (hΔ : 0 ≤ Δ)
    (vin : ι → ℚ) (vout : κ → ℚ) (qin : ι → ℕ) (qout : κ → ℕ)
    (hin  : ∀ i, Δ * (qin i : ℚ) ≤ vin i)
    (hout : ∀ j, vout j ≤ Δ * (qout j : ℚ))
    (hgate : (∑ j, qout j) ≤ ∑ i, qin i) :
    (∑ j, vout j) ≤ ∑ i, vin i := by
  -- cast the integer gate into ℚ
  have hcast : (∑ j, (qout j : ℚ)) ≤ ∑ i, (qin i : ℚ) := by exact_mod_cast hgate
  calc ∑ j, vout j
      ≤ ∑ j, Δ * (qout j : ℚ) := Finset.sum_le_sum (fun j _ => hout j)
    _ = Δ * ∑ j, (qout j : ℚ) := by rw [Finset.mul_sum]
    _ ≤ Δ * ∑ i, (qin i : ℚ) := mul_le_mul_of_nonneg_left hcast hΔ
    _ = ∑ i, Δ * (qin i : ℚ) := by rw [Finset.mul_sum]
    _ ≤ ∑ i, vin i := Finset.sum_le_sum (fun i _ => hin i)

/-- **The directionality is essential (a tooth on the rule itself).** If one instead rounds outputs DOWN
— `qout` UNDER-approximating `vout` — the integer gate `Σ qout ≤ Σ qin` can hold while the true outputs
mint. Concretely (`Δ = 1`): true `vout = (2, 2)` summing `4`, true `vin = (3, 0)` summing `3` — a real
mint (`4 > 3`) — yet a wrong-direction proxy `qout = (1, 1)` (each `< vout`, the forbidden direction)
passes `Σ qout = 2 ≤ 3 = Σ qin`. So `mint_safe_quantization`'s `hout` (outputs OVER) cannot be dropped. -/
theorem wrong_direction_admits_mint :
    ∃ (vin vout : Fin 2 → ℚ) (qin qout : Fin 2 → ℕ),
      -- the mint-safe INPUT rounding still holds
      (∀ i, (1 : ℚ) * (qin i : ℚ) ≤ vin i) ∧
      -- but outputs are rounded the WRONG way (down): qout under-approximates vout
      (∀ j, (qout j : ℚ) ≤ vout j) ∧
      -- the cheap integer gate PASSES
      (∑ j, qout j) ≤ (∑ i, qin i) ∧
      -- yet the true values MINT
      (∑ i, vin i) < ∑ j, vout j :=
  ⟨![3, 0], ![2, 2], ![3, 0], ![1, 1],
    by intro i; fin_cases i <;> norm_num,
    by intro j; fin_cases j <;> norm_num,
    by norm_num [Fin.sum_univ_two],
    by norm_num [Fin.sum_univ_two]⟩

/-! ## 2. `field_gate_refines_nat_eq` — the no-wrap refinement (the exactify step's soundness).

The exactification settles on the integer grid and the conservation gate is checked as a FIELD equality
(mod `p`). A field equality *without* range bounds admits a discrepancy of exactly `p` — a modular mint.
The `VALUE_BITS` no-wrap discipline (`Dregg2.Bignum.legs_noWrap_conservation`,
`shielded_ring_clearing_air.rs::VALUE_BITS`) closes it: with both sides pinned below `p`, the field
equality IS the integer equality, so the exact gap recomputed on the grid is the REAL gap. -/

/-- **`field_gate_refines_nat_eq` — the no-wrap refinement.** A field (`ZMod p`) equality of the
conservation gate, together with the range bounds `outSum + burn < p` and `inSum < p` (the no-wrap
discipline), refines to the ℕ equality `outSum + burn = inSum`. Without the bounds the field equality is
a *modular mint* — it permits a discrepancy of `p` (see `field_gate_without_range_mints`). -/
theorem field_gate_refines_nat_eq {p outSum burn inSum : ℕ}
    (hleft : outSum + burn < p) (hright : inSum < p)
    (hfield : ((outSum + burn : ℕ) : ZMod p) = ((inSum : ℕ) : ZMod p)) :
    outSum + burn = inSum := by
  -- the field equality is a congruence mod p …
  have hmod : (outSum + burn) % p = inSum % p :=
    (ZMod.natCast_eq_natCast_iff' _ _ _).mp hfield
  -- … and both sides live in [0, p), so it is an integer equality
  rwa [Nat.mod_eq_of_lt hleft, Nat.mod_eq_of_lt hright] at hmod

/-- **Without the range bounds a field equality MINTS (the bounds are load-bearing).** At `p = 5`, the
gate `outSum + burn = 5` (`5 : ZMod 5 = 0`) is field-equal to `inSum = 0`, yet `5 ≠ 0` over ℕ — a
mint of `p` conserved by the modular gate alone. This is why `field_gate_refines_nat_eq` needs
`hleft`/`hright`; it is exactly as load-bearing as `mint_safe_quantization`. -/
theorem field_gate_without_range_mints :
    ∃ (p outSum burn inSum : ℕ),
      ((outSum + burn : ℕ) : ZMod p) = ((inSum : ℕ) : ZMod p) ∧ outSum + burn ≠ inSum :=
  ⟨5, 5, 0, 0, by decide, by decide⟩

/-! ## 3. The architecture tie — the exact gap feeds the keystone VERBATIM (exact-disposes).

`exactGap` is the gap `cᵀs − wᵀf` recomputed on the exactified integer-grid witness. `exactified_certified`
shows an exactly-feasible candidate is `Certified` for the LP re-targeted to its OWN exact gap — so the
keystone `certifies_epsilon_optimal` fires with `ε = G_q`, a genuine gap, never a noise term. The
approximate solver PROPOSED the candidate (untrusted); exactification DISPOSED it onto the grid; the
keystone reads only the exact gap. -/

variable {V E : Type*} [Fintype V] [Fintype E]
variable {R : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R]

/-- **`exactGap` — the exact recomputed duality gap of an exactified candidate**, `G_q = cᵀs − wᵀf`,
computed on the integer grid. This is the honest `ε_cert`: everything the keystone consumes. -/
def exactGap (lp : FlowLP V E R) (f : E → R) (_π : V → R) (s : E → R) : R :=
  lp.c ⬝ᵥ s - lp.w ⬝ᵥ f

omit [IsOrderedRing R] in
/-- **`exactified_certified` — approximation proposes, exactification disposes.** An exactified candidate
`(f, π, s)` that is EXACTLY primal- and dual-feasible is `Certified` for the LP whose accuracy target is
set to its own exact gap `exactGap`. No approximation error enters: the gap clause holds with equality.
So `certifies_epsilon_optimal` can be invoked with `ε = G_q` — the exact-disposes step, verbatim. -/
theorem exactified_certified
    (lp : FlowLP V E R) {f : E → R} {π : V → R} {s : E → R}
    (hf : PrimalFeasible lp f) (hd : DualFeasible lp π s) :
    Certified { A := lp.A, w := lp.w, c := lp.c, ε := exactGap lp f π s } f π s :=
  ⟨hf, hd, le_of_eq rfl⟩

/-- **`exact_gap_feeds_keystone` — the keystone fires on the exact gap.** Given an exactified feasible
candidate and its exact gap `≤ ε` (after exactification, `ε := G_q` makes this hold with equality), EVERY
primal-feasible `f'` obeys `wᵀf' ≤ wᵀf + ε`. This is `certifies_epsilon_optimal` reading ONLY the exact
gap — the soundness path is entirely independent of how `(f, π, s)` was approximately searched. -/
theorem exact_gap_feeds_keystone
    (lp : FlowLP V E R) {f : E → R} {π : V → R} {s : E → R}
    (hf : PrimalFeasible lp f) (hd : DualFeasible lp π s)
    (hgap : lp.c ⬝ᵥ s - lp.w ⬝ᵥ f ≤ lp.ε)
    {f' : E → R} (hf' : PrimalFeasible lp f') :
    lp.w ⬝ᵥ f' ≤ lp.w ⬝ᵥ f + lp.ε :=
  certifies_epsilon_optimal lp ⟨hf, hd, hgap⟩ hf'

/-! ## 4. Non-vacuity — a concrete quantized clearing (positive) and a concrete mint (negative). -/

/-! ### 4a. An honest quantized clearing PASSES the gate and is mint-safe.

Rational values (`Δ = 1`): true outputs `vout = (7.5, 8.5)` (sum `16`), true inputs `vin = (10, 10)`
(sum `20`). Mint-safe rounding: outputs UP `qout = (8, 9)` (sum `17`), inputs DOWN `qin = (10, 10)`
(sum `20`). The integer gate `17 ≤ 20` holds, and `mint_safe_quantization` concludes the true clearing
`16 ≤ 20` — an honest clearing accepted. -/

/-- Honest clearing: true inputs (fixed-point rationals). -/
def exVin : Fin 2 → ℚ := ![10, 10]
/-- Honest clearing: true outputs (genuinely fractional — the point of quantization). -/
def exVout : Fin 2 → ℚ := ![15 / 2, 17 / 2]
/-- Honest clearing: inputs rounded DOWN to their integer proxy (mint-safe direction). -/
def exQin : Fin 2 → ℕ := ![10, 10]
/-- Honest clearing: outputs rounded UP to their integer proxy (mint-safe direction). -/
def exQout : Fin 2 → ℕ := ![8, 9]

/-- **THE HONEST QUANTIZED CLEARING PASSES.** The mint-safe rounding of a genuine clearing satisfies the
cheap integer gate `Σ qout = 17 ≤ 20 = Σ qin`, and `mint_safe_quantization` certifies the true rational
clearing `Σ vout ≤ Σ vin`. Non-vacuous positive polarity: the hypotheses are all satisfiable and the
conclusion is a real conservation fact. -/
theorem honest_clearing_passes : (∑ j, exVout j) ≤ ∑ i, exVin i :=
  mint_safe_quantization 1 (by norm_num) exVin exVout exQin exQout
    (by intro i; fin_cases i <;> norm_num [exVin, exQin])
    (by intro j; fin_cases j <;> norm_num [exVout, exQout])
    (by decide)

/-! ### 4b. A genuine mint is REJECTED by the gate.

The architecture-level tooth: a real mint (`Σ vin < Σ vout`) with the CORRECT directional rounding must
fail the integer gate — the contrapositive of `mint_safe_quantization`. Concretely: true outputs
`(10, 10)` (sum `20`) vs true inputs `(9, 9)` (sum `18`) — a mint of `2` — with mint-safe proxies
`qout = (10, 10)`, `qin = (9, 9)`; the gate `20 ≤ 18` is FALSE. -/

/-- **`genuine_mint_fails_gate` — the contrapositive tooth.** Under the mint-safe rounding (`hin`/`hout`)
and `Δ ≥ 0`, a genuine mint of the true values (`Σ vin < Σ vout`) PROVABLY fails the cheap integer gate:
`¬ (Σ qout ≤ Σ qin)`. So the gate can never launder a real mint — it is the honest refusal, derived from
`mint_safe_quantization` itself. -/
theorem genuine_mint_fails_gate
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Δ : ℚ) (hΔ : 0 ≤ Δ)
    (vin : ι → ℚ) (vout : κ → ℚ) (qin : ι → ℕ) (qout : κ → ℕ)
    (hin  : ∀ i, Δ * (qin i : ℚ) ≤ vin i)
    (hout : ∀ j, vout j ≤ Δ * (qout j : ℚ))
    (hmint : (∑ i, vin i) < ∑ j, vout j) :
    ¬ ((∑ j, qout j) ≤ ∑ i, qin i) := by
  intro hgate
  have hconserve := mint_safe_quantization Δ hΔ vin vout qin qout hin hout hgate
  linarith

/-- Mint attempt: true inputs (sum `18`). -/
def mintVin : Fin 2 → ℚ := ![9, 9]
/-- Mint attempt: true outputs (sum `20` — a mint of `2`). -/
def mintVout : Fin 2 → ℚ := ![10, 10]
/-- Mint attempt: inputs rounded DOWN (mint-safe direction). -/
def mintQin : Fin 2 → ℕ := ![9, 9]
/-- Mint attempt: outputs rounded UP (mint-safe direction). -/
def mintQout : Fin 2 → ℕ := ![10, 10]

/-- **THE MINT IS REJECTED.** With the correct directional rounding of a genuine mint
(`Σ mintVin = 18 < 20 = Σ mintVout`), the cheap integer gate `Σ mintQout = 20 ≤ 18 = Σ mintQin` is
provably FALSE. Negative polarity via the architecture tooth `genuine_mint_fails_gate`. -/
theorem mint_attempt_rejected : ¬ ((∑ j, mintQout j) ≤ ∑ i, mintQin i) :=
  genuine_mint_fails_gate 1 (by norm_num) mintVin mintVout mintQin mintQout
    (by intro i; fin_cases i <;> norm_num [mintVin, mintQin])
    (by intro j; fin_cases j <;> norm_num [mintVout, mintQout])
    (by norm_num [mintVin, mintVout, Fin.sum_univ_two])

/-! ### 4c. The exact-disposes tie, worked on the `CertF` 3-cycle.

Reuse the verified `ringLP` circulation (`Market/CertF.lean`): its optimal circulation `ringF = (1,1,1)`
with dual `(ringπ, ringS)` exactifies onto the integer grid with EXACT gap `0`. `exactified_certified`
re-targets the LP to that exact gap and the keystone certifies optimality — the whole approx-proposes /
exact-disposes pipeline, on a concrete instance, with `ε_cert = G_q = 0` (never a noise term). -/

/-- **THE EXACTIFIED CANDIDATE IS `Certified` AT ITS EXACT GAP.** The `ringLP` optimum is certified for
the LP re-targeted to `exactGap ringLP ringF ringπ ringS` (which is `0`). The exact-disposes step, worked. -/
theorem worked_exact_dispose :
    Certified { A := ringLP.A, w := ringLP.w, c := ringLP.c,
                ε := exactGap ringLP ringF ringπ ringS } ringF ringπ ringS :=
  exactified_certified ringLP ringCert_valid.1 ringCert_valid.2.1

/-- **THE KEYSTONE FIRES ON THE EXACT GAP.** Every primal-feasible `f'` scores `≤ wᵀringF + G_q`; here
`G_q = 0`, so `wᵀf' ≤ 3` — `(1,1,1)` is proven optimal from the exact recomputed gap alone. -/
theorem worked_exact_dispose_optimal {f' : Fin 3 → ℤ} (hf' : PrimalFeasible ringLP f') :
    ringLP.w ⬝ᵥ f' ≤ ringLP.w ⬝ᵥ ringF + exactGap ringLP ringF ringπ ringS :=
  exact_gap_feeds_keystone ringLP ringCert_valid.1 ringCert_valid.2.1 (le_of_eq rfl) hf'

/-! ### `#guard` smoke — the gate arithmetic + exact gap are COMPUTED, not asserted. -/

-- the honest clearing's integer gate passes (17 ≤ 20):
#guard decide ((∑ j, exQout j) ≤ ∑ i, exQin i)
-- the mint attempt's integer gate FAILS (20 ≤ 18 is false):
#guard decide (¬ ((∑ j, mintQout j) ≤ ∑ i, mintQin i))
-- the exactified 3-cycle optimum has exact gap 0 (tight — no noise absorbed):
#guard exactGap ringLP ringF ringπ ringS == 0
-- the honest output proxy sums to 17, its input proxy to 20:
#guard (∑ j, exQout j) == 17
#guard (∑ i, exQin i) == 20

/-! ### Axiom hygiene — the mint-safety foundation pinned kernel-clean. -/

#assert_all_clean [Market.mint_safe_quantization, Market.field_gate_refines_nat_eq,
  Market.wrong_direction_admits_mint, Market.field_gate_without_range_mints,
  Market.exactified_certified, Market.exact_gap_feeds_keystone,
  Market.honest_clearing_passes, Market.genuine_mint_fails_gate, Market.mint_attempt_rejected,
  Market.worked_exact_dispose, Market.worked_exact_dispose_optimal]

end Market
