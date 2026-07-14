/-
# Fhegg.Rtl.Examples.FullAdder — the tiny END-TO-END example: a full adder, `eval = spec`
# proven sorry-free, emitting REAL Verilog.

This is the seed a contributor extends: a genuine Lean-spec → verified-netlist → Verilog-text
pipeline on the smallest non-trivial datapath, the full adder (`sum = a⊕b⊕cin`,
`carry = ab ∨ (a⊕b)cin`) — the building block of the ripple-carry adder
(`Examples/RippleAdder.lean`) and, one modular-reduction up, of the NTT butterfly's
`a ± w·b` combiner (`Golden/Butterfly.lean`).

  * `fullAdder`  — the netlist (5 gates: two XORs, two ANDs, one OR).
  * `fullAdderSpec` — the golden Boolean function.
  * `fullAdder_realizes` — **`RealizesSpec fullAdder fullAdderSpec`, PROVEN, sorry-free.**
  * `#eval` / `#guard` — the emitted Verilog is real text and the netlist is well-formed.

The proof is the verified half of translation validation; the emitted Verilog + the co-sim
harness (`hardware/cosim/`) are the other half. Core Lean only.
-/
import Fhegg.Rtl.Netlist

namespace Fhegg.Rtl.Examples

open Fhegg.Rtl

/-! ## 1. The netlist. -/

/-- **The full-adder netlist.** Inputs `a = in[0]`, `b = in[1]`, `cin = in[2]`. Gates:
`w0 = a⊕b`, `w1 = w0⊕cin` (sum), `w2 = a·b`, `w3 = w0·cin`, `w4 = w2∨w3` (carry).
Outputs `[sum, carry] = [w1, w4]`. Note the fanout of `w0` into both `w1` and `w3`. -/
def fullAdder : Netlist where
  nInputs := 3
  gates :=
    [ .xor (.inp 0) (.inp 1)      -- w0 = a ⊕ b
    , .xor (.gate 0) (.inp 2)     -- w1 = w0 ⊕ cin      (sum)
    , .and (.inp 0) (.inp 1)      -- w2 = a · b
    , .and (.gate 0) (.inp 2)     -- w3 = w0 · cin
    , .or  (.gate 2) (.gate 3) ]  -- w4 = w2 ∨ w3       (carry)
  outputs := [ .gate 1, .gate 4 ]

/-! ## 2. The golden spec. -/

/-- **The golden full-adder function.** Reads the three input bits (bits beyond index 2 are
ignored, missing bits default `false` — matching the netlist's `getD` semantics), returns
`[sum, carry]`. -/
def fullAdderSpec (ins : List Bool) : List Bool :=
  let a := ins.getD 0 false
  let b := ins.getD 1 false
  let c := ins.getD 2 false
  [ xor (xor a b) c, (a && b) || (xor a b && c) ]

/-! ## 3. THE PROOF — the netlist realizes the spec, sorry-free. -/

/-- **`fullAdder_realizes` — the verified half of translation validation.** The netlist's
denotation equals the golden function on EVERY input list. Proof: unfold `evalNetlist` /
`evalGates` (the concrete straight-line fold), then case-split the three input bits — 8 cases,
each `rfl`. This is the `eval = spec` obligation a verified-core datapath discharges in Lean. -/
theorem fullAdder_realizes : RealizesSpec fullAdder fullAdderSpec := by
  intro ins
  simp only [evalNetlist, fullAdder, evalGates, List.foldl, evalGate, evalRef,
    List.map, fullAdderSpec]
  cases ins.getD 0 false <;> cases ins.getD 1 false <;> cases ins.getD 2 false <;> rfl

/-! ## 4. Non-vacuity — the netlist actually computes a full adder (`#guard`, not asserted). -/

-- 1 + 0 + 0 = 1: sum 1, carry 0
#guard evalNetlist fullAdder [true, false, false] == [true, false]
-- 1 + 1 + 0 = 10: sum 0, carry 1
#guard evalNetlist fullAdder [true, true, false] == [false, true]
-- 1 + 1 + 1 = 11: sum 1, carry 1
#guard evalNetlist fullAdder [true, true, true] == [true, true]
-- 0 + 0 + 0 = 0: sum 0, carry 0
#guard evalNetlist fullAdder [false, false, false] == [false, false]
-- the netlist is structurally well-formed (every ref in range)
#guard WellFormed fullAdder == true
-- the emitted module is bounded (`module … endmodule`)
#guard emitBounded "full_adder" fullAdder == true

/-! ## 5. THE EMITTED VERILOG — real synthesizable text, printed from the SAME netlist. -/

-- `#eval` prints the actual module a synthesizer would consume:
--
--   module full_adder (
--     input  [2:0] in,
--     output [1:0] out
--   );
--     wire w0; … wire w4;
--     assign w0 = in[0] ^ in[1];
--     assign w1 = w0 ^ in[2];
--     assign w2 = in[0] & in[1];
--     assign w3 = w0 & in[2];
--     assign w4 = w2 | w3;
--     assign out[0] = w1;
--     assign out[1] = w4;
--   endmodule
--
#eval IO.println (toVerilog "full_adder" fullAdder)

-- The emitted Verilog contains the load-bearing gate lines — a cheap emit-faithfulness
-- `#guard` (the seed of a fuller parser/lint gate).
#guard ((toVerilog "full_adder" fullAdder).splitOn "assign w0 = in[0] ^ in[1];").length == 2
#guard ((toVerilog "full_adder" fullAdder).splitOn "assign w4 = w2 | w3;").length == 2
#guard ((toVerilog "full_adder" fullAdder).splitOn "assign out[1] = w4;").length == 2

end Fhegg.Rtl.Examples
