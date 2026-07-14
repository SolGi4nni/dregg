/-
# Fhegg.Rtl.Golden.Accumulator — the mint-safe quantized ACCUMULATOR as a hardware golden model.

The Tier-0 dark clear's soundness lives in one small integer gate: after the encrypted fold
quantizes onto the integer grid (`metatheory/Market/MintSafeQuantization.lean`), a datapath
sums the output proxies and the input proxies and asserts `Σ qout ≤ Σ qin` — the mint-safe
conservation gate the F2 accelerator must realize in RTL (`FHEGG-FPGA-ACCELERATOR.md §4`,
the "conservation / mint-safe gate" that is the boundary the Constitution demands be a theorem).

This file is the **hardware-executable golden model** the contributor's accumulator RTL is
co-simulated against: the computable gate (`accGate`) + the integer-domain mint-safety theorem
(`mint_safe_accumulator`) + its contrapositive tooth (`genuine_mint_fails_gate`), all in core
Lean (no mathlib), plus non-vacuity `#guard`s.

## Relation to the deep proof (no double-claim)

The FULL value-domain mint-safety — over ℚ, with a scale `Δ`, directional floor/ceil rounding
discharged as theorems (`quantize_floor_under`/`quantize_ceil_over`), and the no-wrap field
refinement — is already PROVEN under mathlib in `metatheory/Market/MintSafeQuantization.lean`
(`mint_safe_quantization`, `mint_safe_floor_ceil`, `field_gate_refines_nat_eq`). THIS file is
its `Δ = 1` integer restatement in dependency-free Lean, so a hardware contributor has a
self-contained golden model to co-sim against without pulling mathlib. It cites, it does not
re-derive.
-/
import Fhegg.Rtl.Netlist

namespace Fhegg.Rtl.Golden

/-! ## 1. `Nat`-list sum + pointwise monotonicity (the engine, core Lean). -/

/-- Sum a list of `Nat` (the accumulator's reduction — what the datapath's adder tree computes).
Kept local (no `List.sum` dependency) so this file needs only `Init`. -/
def sumN : List Nat → Nat := List.foldr (· + ·) 0

@[simp] theorem sumN_nil : sumN [] = 0 := rfl
@[simp] theorem sumN_cons (x : Nat) (xs : List Nat) : sumN (x :: xs) = x + sumN xs := rfl

/-- **Pointwise monotonicity of the accumulator.** Equal-length lists that dominate pointwise
have dominating sums: `(∀ i, xs[i] ≤ ys[i]) → Σxs ≤ Σys`. The engine of mint-safety — the same
role `Finset.sum_le_sum` plays in the mathlib proof, here by list induction + `omega`. -/
theorem sumN_le_of_forall_le :
    ∀ {xs ys : List Nat}, xs.length = ys.length →
      (∀ i, xs.getD i 0 ≤ ys.getD i 0) → sumN xs ≤ sumN ys
  | [], [], _, _ => Nat.le_refl 0
  | x :: xs, y :: ys, hlen, h => by
    have hhead : x ≤ y := h 0
    have htail : sumN xs ≤ sumN ys :=
      sumN_le_of_forall_le (by simpa using hlen) (fun i => h (i + 1))
    simp only [sumN_cons]
    omega

/-! ## 2. The mint-safe accumulator gate + its soundness. -/

/-- **The cheap integer accumulator gate** the encrypted fold checks: `Σ qout ≤ Σ qin`.
Computable (`decide`-able) — the exact boolean the RTL comparator asserts. -/
def accGate (qout qin : List Nat) : Bool := sumN qout ≤ sumN qin

/-- **`mint_safe_accumulator` — the gate forbids a mint (integer / `Δ = 1` domain).** With the
true output values `vout` OVER-approximated by their integer proxies (`vout[j] ≤ qout[j]`, the
mint-safe ceil direction) and the true inputs `vin` UNDER-approximated (`qin[i] ≤ vin[i]`, the
floor direction), the gate `Σqout ≤ Σqin` PROVABLY gives `Σvout ≤ Σvin` — no value minted. The
sandwich `Σvout ≤ Σqout ≤ Σqin ≤ Σvin`, each `≤` from monotonicity or the gate. This is the
`Δ = 1` shadow of `Market.mint_safe_quantization`. -/
theorem mint_safe_accumulator
    (vin vout qin qout : List Nat)
    (hlout : vout.length = qout.length) (hlin : qin.length = vin.length)
    (hout : ∀ j, vout.getD j 0 ≤ qout.getD j 0)    -- outputs over-approximated (ceil)
    (hin  : ∀ i, qin.getD i 0 ≤ vin.getD i 0)      -- inputs under-approximated (floor)
    (hgate : accGate qout qin = true) :
    sumN vout ≤ sumN vin := by
  have h1 : sumN vout ≤ sumN qout := sumN_le_of_forall_le hlout hout
  have h2 : sumN qout ≤ sumN qin := by simpa [accGate, decide_eq_true_iff] using hgate
  have h3 : sumN qin ≤ sumN vin := sumN_le_of_forall_le hlin hin
  omega

/-- **`genuine_mint_fails_gate` — the contrapositive tooth.** Under the mint-safe rounding, a
genuine mint of the true values (`Σvin < Σvout`) PROVABLY fails the gate: `accGate qout qin =
false`. The accumulator can never launder a real mint. -/
theorem genuine_mint_fails_gate
    (vin vout qin qout : List Nat)
    (hlout : vout.length = qout.length) (hlin : qin.length = vin.length)
    (hout : ∀ j, vout.getD j 0 ≤ qout.getD j 0)
    (hin  : ∀ i, qin.getD i 0 ≤ vin.getD i 0)
    (hmint : sumN vin < sumN vout) :
    accGate qout qin = false := by
  cases hg : accGate qout qin with
  | false => rfl
  | true =>
    exfalso
    have := mint_safe_accumulator vin vout qin qout hlout hlin hout hin hg
    omega

/-! ## 3. Non-vacuity — an honest clearing passes, a mint fails (`#guard`, computed). -/

-- Honest clearing (mirrors `Market.MintSafeQuantization` §4a): outputs ceil'd to (8,9)=17,
-- inputs floor'd to (10,10)=20 → gate 17 ≤ 20 holds.
#guard accGate [8, 9] [10, 10] == true
-- A genuine mint: outputs (10,10)=20 vs inputs (9,9)=18 → gate 20 ≤ 18 is false.
#guard accGate [10, 10] [9, 9] == false
-- boundary: exact conservation (Σqout = Σqin) passes.
#guard accGate [5, 5] [4, 6] == true

/-! ## 4. The accumulator as a NETLIST target (the RTL the golden model gates).

The `Σqout ≤ Σqin` comparator over multi-bit words is exactly the ripple-adder core
(`Examples/RippleAdder.lean`) feeding a magnitude comparator. The golden `accGate` above is
what the emitted Verilog accumulator is co-simulated against (`hardware/cosim/`): a contributor
builds the wide adder-tree + comparator in SpinalHDL, and the co-sim checks it computes
`accGate` on random vectors. The bit-level adder is already verified here; the comparator +
tree is the named productive-bulk work. -/

end Fhegg.Rtl.Golden
