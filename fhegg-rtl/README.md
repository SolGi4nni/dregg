# fhegg-rtl — a verified Lean→RTL spine for the FHE dark-pool accelerator

Scaffolding so the FPGA dark-pool accelerator (`docs/deos/FHEGG-FPGA-ACCELERATOR.md`, the AWS EC2
F2 node) can be built **in parallel by external contributors** against a machine-checked reference.

**This is scaffolding + a seed example — NOT the FPGA accelerator.** It is a compiling Lean netlist
DSL → Verilog emitter, a worked verified example, FHE-fold golden models, a co-simulation plan, and
productive-HDL stubs. The full NTT/PBS RTL and the bitstream are the named contributor effort.

## Layout

```
fhegg-rtl/
├── README.md                 ← you are here
├── CONTRIBUTING.md           ← the parallel on-ramp: interfaces, milestones, co-sim plan
├── lean/                     ← the verified spine (core Lean, no mathlib, `lake build` ~8 s)
│   ├── lakefile.toml
│   ├── lean-toolchain        (leanprover/lean4:v4.30.0)
│   └── Fhegg/Rtl/
│       ├── Netlist.lean          the DSL: eval + toVerilog + RealizesSpec
│       ├── Examples/
│       │   ├── FullAdder.lean    the worked example: eval = spec PROVEN, real Verilog out
│       │   └── RippleAdder.lean  a parametric n-bit adder builder + smoke
│       └── Golden/
│           ├── Accumulator.lean  the mint-safe conservation gate (golden model)
│           └── Butterfly.lean    the NTT butterfly (golden model)
└── hardware/                 ← productive-bulk stubs (honest TODOs)
    ├── spinalhdl/            SpinalHDL butterfly skeleton + build.sbt stub
    └── cosim/               the differential co-simulation harness scaffold
```

## Build + see it work

```
cd fhegg-rtl/lean
lake build                                   # builds the whole spine, sorry-free

# print the emitted Verilog for the worked example:
lake env lean --run <(printf 'import Fhegg\nopen Fhegg.Rtl Fhegg.Rtl.Examples\ndef main : IO Unit := IO.println (toVerilog "ripple_add4" (rippleAdder 4))')
```

The full adder's `eval = spec` is proven in `Examples/FullAdder.lean`
(`fullAdder_realizes`), and the same file `#eval`s the real Verilog module.

## The idea in one line

dregg already proved "define a circuit in Lean + prove it sound + emit + tie the emit to a byte-pin
twin" for its ZK/AIR path (`metatheory/Dregg2/Circuit.lean` + the Rust `*_layout_matches_lean`
tests). This directory **repoints that discipline at RTL**: the small soundness-critical datapath is
verified in Lean and emitted to Verilog; the large NTT/PBS bulk is productive SpinalHDL/Hardcaml,
tied to the Lean golden models by co-simulation. See `docs/deos/FHEGG-RTL-VERIFIED-HARDWARE.md` for
the landscape survey (including the honest verdict: there is no mature Lean-4 HDL) and the full
strategy.
