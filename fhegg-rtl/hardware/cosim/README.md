# fhegg-rtl / hardware / cosim — the differential co-simulation harness (scaffold)

This is the tie between the **Lean golden models** (`../../lean/Fhegg/Rtl/Golden/`) and a
contributor's **productive RTL** (`../spinalhdl/`). It is the RTL analogue of dregg's Rust
`*_layout_matches_lean` byte-pin twin (`circuit/src/effect_vm_descriptors.rs`): both sides pin, the
harness asserts equality, and the residual seam ("the simulator faithfully executes the RTL") is
NAMED — no formal Verilog semantics is claimed.

**Status:** scaffold. `cosim_harness.rs` is a commented skeleton with honest TODOs, not a compiling
crate (kept out of the Cargo workspace on purpose). A contributor turns it into a real crate or a
Verilator C++ testbench.

## The three-step contract

1. **Export golden vectors from Lean.** A Lean `main` prints `(input…, expected-output…)` rows for
   a golden `def`. The seed is any `#eval IO.println …` in the examples. A minimal dumper for the
   butterfly (a contributor drops this into `../../lean/` as, say, `DumpButterflyVectors.lean` and
   `lake env lean --run`s it — or adds a `lean_exe` to the lakefile):

   ```lean
   import Fhegg
   open Fhegg.Rtl.Golden

   /-- Deterministic pseudo-random test vectors (a tiny LCG) so Lean and the sim agree. -/
   def lcg (s : Nat) : Nat := (s * 1103515245 + 12345) % 2147483648

   def main : IO Unit := do
     let q : Int := 2013265921        -- BabyBear prime
     let mut s := 1
     for _ in [0:1000] do
       s := lcg s; let a := (s % 2013265921 : Nat)
       s := lcg s; let b := (s % 2013265921 : Nat)
       s := lcg s; let w := (s % 2013265921 : Nat)
       let (hi, lo) := butterfly q a b w
       IO.println s!"{a},{b},{w},{hi},{lo}"
   ```

   giving CSV rows `a,b,w,hi_expected,lo_expected`.

2. **Simulate the RTL** on the same `(a, b, w)`. Options:
   - **Verilator**: elaborate `../spinalhdl/Butterfly.scala` to Verilog (`SpinalVerilog(...)`),
     wrap in a Verilator C++ testbench that reads the CSV and drives the module.
   - **SpinalSim / hardcaml sim**: drive the module directly in Scala/OCaml from the CSV.

3. **Assert equality.** Read golden CSV, drive sim, compare `(hi, lo)` to `(hi_expected,
   lo_expected)`; fail on the first mismatch with the offending row. See `cosim_harness.rs`.

## Scaling up

- For **combinational** cores (butterfly, accumulator gate) vector-based diff-testing is enough.
- For **sequential** datapaths (the full NTT, the PBS pipeline) move to **sequential equivalence
  checking**: a solver-driven equivalence check against the golden model at interface boundaries,
  producing counterexample waveforms — no hand vectors. This is the standard industrial golden-model
  ↔ RTL pattern (Hardcaml co-sims its OCaml model against generated RTL; Verilator co-sim
  differentially tests emitted Verilog against a reference).

## Which golden model gates which milestone

| Milestone | Golden reference (Lean) | Co-sim target (RTL) |
|---|---|---|
| M0 butterfly | `Golden.butterfly` | `spinalhdl/Butterfly.scala` |
| M2 full NTT | `Golden/Ntt.lean` (contributor adds) | staged NTT |
| M3 accumulator gate | `Golden.accGate` (VERIFIED core) | wide adder-tree + comparator |
| M5 fold datapath | `Market/CertF.lean` + `Golden.accGate` | the F2 fold top |
