/-
# Market.PrecisionEnvelope — the Level-B COMPLETENESS / PARAMETER-SIZING envelope (NOT soundness).

**"Quantization + FHE/CKKS + PDHG-iteration noise govern COMPLETENESS and PARAMETER SIZING — never
SOUNDNESS."** This is codex fhEgg Round-3 Q1, the Level-B sizing question, made explicit and kept
strictly OFF the soundness path. It sits directly on top of the soundness foundation
`Market.MintSafeQuantization` and consumes exactly ONE fact from it — the completeness bound
`sufficient_surplus_passes_gate` — plus the deployable mint-safety keystone `mint_safe_floor_ceil`.

## What this file IS (honest scope — read before trusting)

This is an **ENVELOPE MODEL**. Every `def`/`theorem` below is a **COMPLETENESS / PARAMETER-SIZING**
statement: it answers "how much TRUE surplus must an honest clearing carry so the cheap integer gate
does not spuriously REJECT it", and how that budget scales with the quantization step `Δ` and a carried
iteration/encryption error `E_T`. It says the gate ACCEPTS honest clearings — it says NOTHING new about
what the gate REFUSES. Soundness (the gate never mints) is untouched, lives in
`Market.MintSafeQuantization` (`mint_safe_floor_ceil`), and holds for ALL `Δ > 0` regardless of `E_T`
(see `tolerance_split_soundness_untouched` below — proven here, independent of `Δ` and `E_T`).

## The honest planning bound

  * `reserve Δ nIn nOut := Δ·(nOut + nIn)` — the **quantization reserve**: each floor loses `< Δ` and
    each ceil adds `< Δ`, so the integer gate can only reject a clearing whose true surplus is below
    `Δ·(n_in + n_out)`. This is a PROVEN completeness bound (via `sufficient_surplus_passes_gate`).
  * `tolerance Δ nIn nOut E_T := reserve Δ nIn nOut + E_T` — the **honest planning bound**: the
    quantization reserve PLUS a **carried** iteration/encryption error `E_T`. `E_T` is an ABSTRACT
    ENVELOPE PARAMETER (a hypothesis / carried bound modelling PDHG-iteration + CKKS/FHE approximation
    slack) — it is **NOT derived, NOT proven here**. It is the knob the deployment sizes; this file only
    records where it enters the budget and, crucially, that it never enters soundness.

**Parameter vs proven.** `reserve` / `tolerance` are DEFINITIONS (budgets). `E_T` is a CARRIED
PARAMETER. `envelope_admits_clearing`, `reserve_monotone_in_step`,
`tolerance_split_soundness_untouched`, and the worked instance are THEOREMS. Nothing here is charged to
`E_T` on the soundness side: soundness stays exact and `Δ`/`E_T`-independent.

Pure.
-/
import Market.MintSafeQuantization

namespace Market

/-! ## 1. The quantization reserve (COMPLETENESS budget — the tolerance the gate costs). -/

/-- **`reserve` — the quantization reserve (PARAMETER-SIZING budget, not soundness).** `Δ·(nOut + nIn)`:
each ceil of an output can add up to `Δ` and each floor of an input can drop up to `Δ`, so an honest
clearing needs this much TRUE surplus to be sure the cheap integer gate accepts it. This is the
COMPLETENESS tolerance — smaller `Δ` shrinks it (`reserve_monotone_in_step`). It bounds only what the
gate might spuriously REJECT; it changes NOTHING about soundness. -/
def reserve (Δ : ℚ) (nIn nOut : ℕ) : ℚ := Δ * (nOut + nIn)

/-- **`tolerance` — the honest planning bound (COMPLETENESS/SIZING; `E_T` is a CARRIED PARAMETER).**
The quantization `reserve` plus a carried iteration/encryption error `E_T`. `E_T` is an ABSTRACT
envelope parameter (PDHG-iteration + CKKS/FHE approximation slack) — **NOT derived or proven here**, it
is the deployment's sizing knob. `tolerance` records where `E_T` enters the completeness budget; it does
NOT enter soundness. -/
def tolerance (Δ : ℚ) (nIn nOut : ℕ) (E_T : ℚ) : ℚ := reserve Δ nIn nOut + E_T

/-! ## 2. Completeness: enough TRUE surplus (≥ `reserve`) ⇒ the integer gate ACCEPTS. -/

/-- **`envelope_admits_clearing` — the honest COMPLETENESS statement (parameter-sizing, not soundness).**
If the true surplus `Σ vin − Σ vout` is at least `reserve Δ (card ι) (card κ)`, the deployable floor/ceil
integer gate `Σ ⌈vout/Δ⌉ ≤ Σ ⌊vin/Δ⌋` ACCEPTS. This is a clean restatement of
`sufficient_surplus_passes_gate` with the card-sum reserve pinned to `reserve` — `reserve Δ (card ι)
(card κ)` is DEFINITIONALLY `Δ·(card κ + card ι)`. It bounds only spurious rejection (completeness); it
adds nothing to soundness. -/
theorem envelope_admits_clearing
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Δ : ℚ) (hΔ : 0 < Δ)
    (vin : ι → ℚ) (vout : κ → ℚ)
    (hsurplus : reserve Δ (Fintype.card ι) (Fintype.card κ) ≤ (∑ i, vin i) - ∑ j, vout j) :
    (∑ j, ⌈vout j / Δ⌉) ≤ ∑ i, ⌊vin i / Δ⌋ := by
  apply sufficient_surplus_passes_gate Δ hΔ vin vout
  simpa [reserve] using hsurplus

/-! ## 3. The precision knob: the reserve is monotone in `Δ` (finer step ⇒ tighter tolerance). -/

/-- **`reserve_monotone_in_step` — the precision knob (COMPLETENESS/SIZING).** The quantization reserve
is monotone in the step: `0 ≤ Δ₁ ≤ Δ₂ ⇒ reserve Δ₁ ≤ reserve Δ₂`. Sizing `Δ` DOWN shrinks the reserve,
so a finer quantizer tolerates smaller honest surpluses without spurious rejection. A tuning fact about
the completeness budget — it does not touch soundness. -/
theorem reserve_monotone_in_step
    (Δ₁ Δ₂ : ℚ) (nIn nOut : ℕ) (_h₀ : 0 ≤ Δ₁) (h₁₂ : Δ₁ ≤ Δ₂) :
    reserve Δ₁ nIn nOut ≤ reserve Δ₂ nIn nOut := by
  unfold reserve
  exact mul_le_mul_of_nonneg_right h₁₂ (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

/-! ## 4. SOUNDNESS is untouched — independent of `Δ` and the carried `E_T`.

The envelope above is COMPLETENESS-ONLY. The soundness guarantee (the gate never mints) is a separate,
exact fact that quantifies over ALL `Δ > 0` and does not mention `E_T` at all. We re-expose it here to
make the split explicit: whatever the envelope parameters, an accepted clearing cannot mint. -/

/-- **`tolerance_split_soundness_untouched` — SOUNDNESS is `Δ`/`E_T`-independent (the split, proven).**
For EVERY carried error `E_T` and EVERY step `Δ > 0`, if the floor/ceil integer gate accepts
(`Σ ⌈vout/Δ⌉ ≤ Σ ⌊vin/Δ⌋`) then the true rational clearing is mint-safe (`Σ vout ≤ Σ vin`). The bound
`E_T` is taken as an argument and is **never used** — that is precisely the point: soundness does not
depend on the envelope. This is `mint_safe_floor_ceil` (the soundness keystone) re-exposed with the
envelope parameters present but inert. -/
theorem tolerance_split_soundness_untouched
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (_E_T : ℚ) (Δ : ℚ) (hΔ : 0 < Δ)
    (vin : ι → ℚ) (vout : κ → ℚ)
    (hgate : (∑ j, ⌈vout j / Δ⌉) ≤ ∑ i, ⌊vin i / Δ⌋) :
    (∑ j, vout j) ≤ ∑ i, vin i :=
  -- `_E_T` is bound but unused: soundness is independent of the carried envelope error.
  mint_safe_floor_ceil Δ hΔ vin vout hgate

/-! ## 5. Non-vacuity — a concrete worked instance of the completeness envelope.

`ι = κ = Fin 2`, step `Δ = 1`, carried error `E_T = 1/2`. True inputs `envVin = (10, 10)` (sum `20`),
true outputs `envVout = (7.5, 8.5)` (sum `16`) — a genuinely fractional clearing (the point of
quantization). True surplus `= 4`, exactly `reserve 1 2 2 = 4`, so `envelope_admits_clearing` FIRES: the
floor/ceil gate `⌈7.5⌉ + ⌈8.5⌉ = 17 ≤ 20 = ⌊10⌋ + ⌊10⌋` accepts. The carried planning bound is
`tolerance 1 2 2 (1/2) = 9/2`. And the accepted clearing is mint-safe (`16 ≤ 20`). -/

/-- Worked instance: quantization step. -/
def envΔ : ℚ := 1
/-- Worked instance: the carried iteration/encryption error `E_T` (an ABSTRACT parameter, chosen here
only to exhibit `tolerance` concretely — not derived). -/
def envE_T : ℚ := 1 / 2
/-- Worked instance: true inputs (sum `20`). -/
def envVin : Fin 2 → ℚ := ![10, 10]
/-- Worked instance: true outputs (genuinely fractional; sum `16`). -/
def envVout : Fin 2 → ℚ := ![15 / 2, 17 / 2]

/-- **THE COMPLETENESS ENVELOPE FIRES (concrete, non-vacuous).** The honest clearing carries true surplus
`20 − 16 = 4`, meeting `reserve envΔ (card (Fin 2)) (card (Fin 2)) = 4`, so `envelope_admits_clearing`
proves the deployable floor/ceil gate accepts: `Σ ⌈envVout/envΔ⌉ ≤ Σ ⌊envVin/envΔ⌋`. -/
theorem env_concrete_gate :
    (∑ j, ⌈envVout j / envΔ⌉) ≤ ∑ i, ⌊envVin i / envΔ⌋ :=
  envelope_admits_clearing envΔ (by norm_num [envΔ]) envVin envVout
    (by norm_num [reserve, envΔ, envVin, envVout, Fin.sum_univ_two, Fintype.card_fin])

/-- **THE ACCEPTED CLEARING IS MINT-SAFE (soundness, `Δ`/`E_T`-independent).** The same clearing the
envelope admits is refused-of-mint by the soundness keystone: `Σ envVout ≤ Σ envVin` (`16 ≤ 20`), via
`tolerance_split_soundness_untouched` with the carried `envE_T` present but inert. Completeness (the gate
fired) and soundness (no mint) both hold on the concrete instance. -/
theorem env_concrete_mint_safe : (∑ j, envVout j) ≤ ∑ i, envVin i :=
  tolerance_split_soundness_untouched envE_T envΔ (by norm_num [envΔ]) envVin envVout env_concrete_gate

/-! ### `#guard` smoke — the reserve/tolerance budgets and the gate arithmetic are COMPUTED. -/

-- the quantization reserve for 2 inputs + 2 outputs at Δ=1 is 4:
#guard reserve 1 2 2 == (4 : ℚ)
-- the honest planning bound adds the carried E_T = 1/2, giving 9/2:
#guard tolerance 1 2 2 (1 / 2) == (9 / 2 : ℚ)
-- monotone-in-Δ, computed: reserve at Δ=1 is below reserve at Δ=2 (4 ≤ 8):
#guard decide (reserve 1 2 2 ≤ reserve 2 2 2)
-- the worked instance's floor/ceil gate: ⌈7.5⌉+⌈8.5⌉ = 17, ⌊10⌋+⌊10⌋ = 20:
#guard (∑ j, ⌈envVout j / envΔ⌉) == (17 : ℤ)
#guard (∑ i, ⌊envVin i / envΔ⌋) == (20 : ℤ)
-- so the gate accepts (17 ≤ 20), and the true surplus 20 − 16 = 4 meets reserve 1 2 2 = 4:
#guard decide ((∑ j, ⌈envVout j / envΔ⌉) ≤ ∑ i, ⌊envVin i / envΔ⌋)

/-! ### Axiom hygiene — the completeness envelope pinned kernel-clean. -/

#assert_all_clean [Market.envelope_admits_clearing, Market.reserve_monotone_in_step,
  Market.tolerance_split_soundness_untouched, Market.env_concrete_gate,
  Market.env_concrete_mint_safe]

end Market
