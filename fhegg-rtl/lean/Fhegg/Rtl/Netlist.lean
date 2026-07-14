/-
# Fhegg.Rtl.Netlist — a tiny COMBINATIONAL netlist DSL in Lean, with a denotational
# `eval`, a `toVerilog` emitter, and the translation-validation soundness *shape*.

This is the SEED of the fhEgg verified-RTL spine (`docs/deos/FHEGG-RTL-VERIFIED-HARDWARE.md`,
`docs/deos/FHEGG-FPGA-ACCELERATOR.md §4`). It reuses dregg's own verified-emit discipline —
the one proved for the AIR path in `metatheory/Dregg2/Circuit.lean`
(`Expr`/`Constraint`/`satisfied`) and byte-pinned to Rust by the `*_layout_matches_lean`
twin tests — and REPOINTS it at RTL: a Lean object with a denotational semantics is emitted
to real text (there: `EffectVmDescriptor2`; here: Verilog), and the two are tied by a
byte-pinned / co-simulated twin rather than trusted.

## What this module IS (honest scope)

  * A **straight-line (SSA) combinational netlist** over single-bit signals: gates
    `not / and / or / xor / buf` referencing inputs, earlier gates, or literals. This is
    exactly the shape a synthesizable Verilog `assign` chain has (with fanout — a gate may be
    referenced by many later gates), so it is a faithful RTL seed, not a toy tree.
  * A **denotational semantics** `evalNetlist : Netlist → (inputs) → (outputs)` — the golden
    meaning the emitted hardware must realize.
  * A **`toVerilog` emitter** that prints the SAME netlist as a real synthesizable module.
  * The **soundness shape**: `RealizesSpec nl spec := ∀ ins, evalNetlist nl ins = spec ins`.
    A proof of `RealizesSpec` (see `Examples/FullAdder.lean`) certifies the Lean netlist
    matches its golden spec; the emitter is a pretty-printer of the *same* object `eval`
    interprets, so the remaining gap — "the Verilog SIMULATOR agrees with `evalNetlist`" — is
    the ONE translation-validation seam, discharged by co-simulation (`hardware/cosim/`),
    exactly as the AIR path's remaining seam is the Rust byte-pin twin. Stated, not hidden.

## What this module is NOT (named, not laundered)

  * NOT a formal Verilog semantics. Lean does not here model the Verilog language, so
    `toVerilog` is TRUSTED-by-construction + co-sim-checked, not proven. That is the deliberate
    verified-core / productive-bulk split (`FHEGG-FPGA-ACCELERATOR.md §4`): the small
    soundness-critical datapath is verified in Lean; the bulk NTT/PBS datapath is productive
    SpinalHDL/Hardcaml checked differentially. This DSL is the verified-core seed.
  * NOT sequential (no registers/clock yet). Combinational only — the F2 conservation/crossing
    gate is combinational; sequential lifting is a named contributor milestone
    (`fhegg-rtl/CONTRIBUTING.md`).

Pure. Core Lean only (`Init`) — no mathlib. `decide` / `omega` discharge the tiny proofs.
-/

namespace Fhegg.Rtl

/-! ## 1. The netlist IR. -/

/-- A reference to a single-bit signal: a module **input** by index, a **prior gate**'s output
by index (straight-line / SSA — a gate may only reference gates defined before it), or a
constant **literal** bit. Fanout is free: any signal may be referenced by many later gates. -/
inductive Ref where
  | inp  : Nat → Ref
  | gate : Nat → Ref
  | lit  : Bool → Ref
  deriving Repr, DecidableEq

/-- A combinational **gate** over bit signals — the productive-HDL-portable primitive set.
`buf` is a pass-through (used to name an output wire off an input/literal). -/
inductive Gate where
  | not : Ref → Gate
  | and : Ref → Ref → Gate
  | or  : Ref → Ref → Gate
  | xor : Ref → Ref → Gate
  | buf : Ref → Gate
  deriving Repr, DecidableEq

/-- A combinational **netlist**: `nInputs` module inputs, a straight-line list of `gates`
(gate `i` is the `i`-th element and may reference inputs `< nInputs` and gates `< i`), and the
`outputs` — the refs wired to the module's output bus, in order. -/
structure Netlist where
  nInputs : Nat
  gates   : List Gate
  outputs : List Ref
  deriving Repr

/-! ## 2. Denotational semantics — the golden meaning `eval`. -/

/-- Resolve a `Ref` against the module inputs and the already-computed gate values.
Out-of-range references default to `false` (a well-formed netlist never hits this — see
`WellFormed`). -/
def evalRef (ins : List Bool) (vals : List Bool) : Ref → Bool
  | .inp i  => ins.getD i false
  | .gate i => vals.getD i false
  | .lit b  => b

/-- Evaluate one gate given the inputs and the prior gates' values. -/
def evalGate (ins vals : List Bool) : Gate → Bool
  | .not a   => !(evalRef ins vals a)
  | .and a b => (evalRef ins vals a) && (evalRef ins vals b)
  | .or  a b => (evalRef ins vals a) || (evalRef ins vals b)
  | .xor a b => xor (evalRef ins vals a) (evalRef ins vals b)
  | .buf a   => evalRef ins vals a

/-- Evaluate the straight-line gate list left-to-right, accumulating each gate's output so
later gates can reference earlier ones (SSA). Returns the vector of all gate outputs. -/
def evalGates (ins : List Bool) (gates : List Gate) : List Bool :=
  gates.foldl (fun acc g => acc ++ [evalGate ins acc g]) []

/-- **The netlist denotation** — the module's output bits on the given input bits. This is the
golden semantics `toVerilog` must realize; a `Netlist` "means" this Boolean function. -/
def evalNetlist (nl : Netlist) (ins : List Bool) : List Bool :=
  let vals := evalGates ins nl.gates
  nl.outputs.map (evalRef ins vals)

/-! ## 3. The soundness SHAPE — translation validation, stated honestly.

`RealizesSpec nl spec` says the Lean netlist computes exactly the golden Boolean function
`spec`. A sorry-free proof of it (e.g. `fullAdder_realizes` in `Examples/FullAdder.lean`) is
the verified half. The emitter (§5) prints the SAME `nl` that `evalNetlist` interprets, so the
only remaining obligation is *"the Verilog simulator's output on `toVerilog nl` equals
`evalNetlist nl`"* — the co-simulation seam (`hardware/cosim/`), the RTL analogue of the AIR
path's Rust `*_layout_matches_lean` byte-pin. It is NAMED, not assumed away. -/

/-- **`RealizesSpec`** — the netlist realizes the golden bit-function `spec` on every input.
The proof obligation a verified-core datapath must discharge in Lean. -/
def RealizesSpec (nl : Netlist) (spec : List Bool → List Bool) : Prop :=
  ∀ ins, evalNetlist nl ins = spec ins

/-! ## 4. Well-formedness — every ref is in range (so `eval` never defaults). -/

/-- A `Ref` is in range at gate-position `k` (i.e. only inputs `< nInputs` and gates `< k`). -/
def Ref.inRange (nInputs k : Nat) : Ref → Bool
  | .inp i  => i < nInputs
  | .gate i => i < k
  | .lit _  => true

/-- A gate's refs are all in range at position `k`. -/
def Gate.inRange (nInputs k : Nat) : Gate → Bool
  | .not a   => a.inRange nInputs k
  | .and a b => a.inRange nInputs k && b.inRange nInputs k
  | .or  a b => a.inRange nInputs k && b.inRange nInputs k
  | .xor a b => a.inRange nInputs k && b.inRange nInputs k
  | .buf a   => a.inRange nInputs k

/-- Every gate references only earlier gates / valid inputs, and every output ref is in range.
A `WellFormed` netlist emits to legal Verilog and never hits an `evalRef` default. -/
def WellFormed (nl : Netlist) : Bool :=
  (nl.gates.zipIdx.all (fun (g, k) => g.inRange nl.nInputs k)) &&
  (nl.outputs.all (·.inRange nl.nInputs nl.gates.length))

/-! ## 5. The Verilog emitter — real synthesizable text from the SAME netlist. -/

/-- The Verilog name of a signal: module input bit `in[i]`, internal wire `w{i}`, or a literal
`1'b0` / `1'b1`. -/
def Ref.verilog : Ref → String
  | .inp i  => s!"in[{i}]"
  | .gate i => s!"w{i}"
  | .lit b  => if b then "1'b1" else "1'b0"

/-- The right-hand side of a gate's `assign`, in Verilog. -/
def Gate.verilogRhs : Gate → String
  | .not a   => s!"~{a.verilog}"
  | .and a b => s!"{a.verilog} & {b.verilog}"
  | .or  a b => s!"{a.verilog} | {b.verilog}"
  | .xor a b => s!"{a.verilog} ^ {b.verilog}"
  | .buf a   => a.verilog

/-- Emit the gate `assign`s as one `assign wK = <rhs>;` line each (straight-line order). -/
def emitGateAssigns (gates : List Gate) : String :=
  String.join (gates.zipIdx.map (fun (gk : Gate × Nat) => s!"  assign w{gk.2} = {gk.1.verilogRhs};\n"))

/-- Emit the output-bus `assign`s: `assign out[j] = <ref>;`. -/
def emitOutputAssigns (outs : List Ref) : String :=
  String.join (outs.zipIdx.map (fun (rj : Ref × Nat) => s!"  assign out[{rj.2}] = {rj.1.verilog};\n"))

/-- Declare one scalar `wire wK;` per gate (kept scalar so each `assign` is unambiguous). -/
def emitWireDecls (nGate : Nat) : String :=
  String.join ((List.range nGate).map (fun k => s!"  wire w{k};\n"))

/-- **`toVerilog`** — the SAME `Netlist` object `evalNetlist` interprets, printed as a real
synthesizable combinational Verilog-2001 module: a packed `input [n-1:0] in`, a packed
`output [m-1:0] out`, one `wire` per gate, and continuous `assign`s. This is the emit step of
translation validation; co-simulation (`hardware/cosim/`) ties the SIMULATED output back to
`evalNetlist`, closing the loop the way the Rust byte-pin twin closes the AIR path. -/
def toVerilog (name : String) (nl : Netlist) : String :=
  let header := s!"module {name} (\n  input  [{nl.nInputs - 1}:0] in,\n  output [{nl.outputs.length - 1}:0] out\n);\n"
  header ++ emitWireDecls nl.gates.length
         ++ emitGateAssigns nl.gates
         ++ emitOutputAssigns nl.outputs
         ++ "endmodule\n"

/-! ## 6. Emit well-formedness — a cheap structural check a contributor's CI can `#guard`. -/

/-- The emitted module text contains the module-boundary keywords `module ` and `endmodule`.
A trivial-but-real check that `toVerilog` produced a bounded module — the seed of a fuller
Verilog linter/parser gate a contributor can grow. -/
def emitBounded (name : String) (nl : Netlist) : Bool :=
  let s := toVerilog name nl
  ("module ".isPrefixOf s) && ((s.splitOn "endmodule").length ≥ 2)

end Fhegg.Rtl
