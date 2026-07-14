/-
# Fhegg.Rtl.Examples.RippleAdder — a PARAMETRIC N-bit ripple-carry adder builder, composing
# the verified full-adder cell, with concrete-vector smoke.

Where `FullAdder.lean` carries the sorry-free `eval = spec` on one cell, this file shows the
cell COMPOSING into a parametric datapath — the shape every real FHE datapath has (the NTT
butterfly's `a ± w·b` is a modular adder/subtractor; a TFHE carry-add is a ripple of these).
`rippleAdder n` builds a `2n`-input, `(n+1)`-output combinational adder as a straight-line
netlist of `n` full-adder cells (carry chained, `cin = 0`), and emits real Verilog.

## Honest scope

  * `rippleAdder n` — the builder (real, runs, emits Verilog for any `n`).
  * `#guard` — the netlist adds correctly on concrete vectors (4-bit and 8-bit), checked
    against Lean's own `Nat` addition. Non-vacuous, computed (not asserted).
  * The **parametric** `∀ a b, natOf (eval (rippleAdder n) …) = a + b` proof (induction on the
    bit width, carry-chain invariant) is a NAMED contributor milestone in
    `fhegg-rtl/CONTRIBUTING.md` — the per-cell `eval = spec` (proven, `FullAdder.lean`) is the
    inductive step's core. This file does not overclaim a parametric proof it does not carry.

Core Lean only.
-/
import Fhegg.Rtl.Netlist

namespace Fhegg.Rtl.Examples

open Fhegg.Rtl

/-! ## 1. Bit ↔ Nat helpers (little-endian, LSB first). -/

/-- Little-endian bit decomposition: `bitsOf n x = [x₀, x₁, …, x_{n-1}]`. -/
def bitsOf (n x : Nat) : List Bool := (List.range n).map (fun i => x.testBit i)

/-- Little-endian bit recomposition: `natOf [b₀, b₁, …] = Σ bᵢ · 2ⁱ`. -/
def natOf (bs : List Bool) : Nat :=
  bs.zipIdx.foldl (fun acc (bi : Bool × Nat) => acc + (if bi.1 then 2 ^ bi.2 else 0)) 0

/-! ## 2. The builder. -/

/-- **`rippleAdder n`** — an `n`-bit ripple-carry adder as a straight-line netlist. Input bus:
`in[0..n-1]` = `a` (LSB first), `in[n..2n-1]` = `b`. Output bus: `out[0..n-1]` = sum bits,
`out[n]` = final carry. Built by folding `n` full-adder cells, chaining each cell's carry-out
into the next cell's carry-in (`cin` of bit 0 is the literal `0`). Each cell is the same 5-gate
block proven correct in `FullAdder.lean`; only the input refs and the base index change. -/
def rippleAdder (n : Nat) : Netlist :=
  let step := fun (st : Nat × Ref × List Gate × List Ref) (k : Nat) =>
    let (base, rc, gs, ss) := st
    let ra : Ref := .inp k
    let rb : Ref := .inp (n + k)
    let cell : List Gate :=
      [ .xor ra rb                          -- base+0 : a ⊕ b
      , .xor (.gate base) rc                 -- base+1 : sum
      , .and ra rb                           -- base+2 : a · b
      , .and (.gate base) rc                 -- base+3 : (a⊕b) · cin
      , .or (.gate (base + 2)) (.gate (base + 3)) ]  -- base+4 : carry-out
    (base + 5, Ref.gate (base + 4), gs ++ cell, ss ++ [Ref.gate (base + 1)])
  let (_, cout, gates, sums) :=
    (List.range n).foldl step (0, Ref.lit false, [], [])
  { nInputs := 2 * n, gates := gates, outputs := sums ++ [cout] }

/-! ## 3. Smoke — the builder adds correctly on concrete vectors (`#guard`, computed). -/

/-- Run the `n`-bit adder on `(a, b)` and decode the output bus back to a `Nat`. -/
def runAdd (n a b : Nat) : Nat :=
  natOf (evalNetlist (rippleAdder n) (bitsOf n a ++ bitsOf n b))

-- 4-bit adder: a handful of concrete sums, each checked against Lean's own `+`.
#guard runAdd 4 0 0 == 0
#guard runAdd 4 1 1 == 2
#guard runAdd 4 7 8 == 15
#guard runAdd 4 15 15 == 30      -- overflow into the carry bit (out[4])
#guard runAdd 4 6 9 == 15
#guard runAdd 4 13 2 == 15
-- 8-bit adder: wider carry chain.
#guard runAdd 8 200 55 == 255
#guard runAdd 8 255 255 == 510
#guard runAdd 8 123 45 == 168

-- structural: an 8-bit adder is 8 cells × 5 gates = 40 gates, 16 inputs, 9 outputs.
#guard (rippleAdder 8).gates.length == 40
#guard (rippleAdder 8).nInputs == 16
#guard (rippleAdder 8).outputs.length == 9
-- every ref is in range (the fold's base bookkeeping is correct) and the module is bounded.
#guard WellFormed (rippleAdder 8) == true
#guard emitBounded "ripple_add8" (rippleAdder 8) == true

/-! ## 4. The emitted Verilog for a small width (4-bit). -/

-- `#eval` prints the real 4-bit ripple adder a synthesizer consumes (40→20 gate lines etc.):
#eval IO.println (toVerilog "ripple_add4" (rippleAdder 4))

end Fhegg.Rtl.Examples
