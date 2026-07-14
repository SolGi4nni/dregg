# Contributing to fhegg-rtl — the FPGA dark-pool accelerator, in parallel

This directory is **scaffolding**: a verified Lean→RTL spine + FHE-fold golden models + a
co-simulation plan, laid down so the FPGA accelerator effort (`docs/deos/FHEGG-FPGA-ACCELERATOR.md`,
the AWS EC2 F2 dark-pool node) can proceed **in parallel, by external contributors**, against a
machine-checked reference — because the core team does not have the budget to do the full FPGA
build itself.

If you have FPGA / SpinalHDL / Hardcaml experience, you can start **without us**. This file is the
on-ramp: the interfaces, the golden models, the verified-core / productive-bulk split, the co-sim
harness plan, and the milestone ladder.

Read first: `docs/deos/FHEGG-RTL-VERIFIED-HARDWARE.md` (the landscape + strategy) and
`docs/deos/FHEGG-FPGA-ACCELERATOR.md §4` (the split + the F2 target).

---

## 0. The one-paragraph orientation

The dark pool's **soundness** is a *small* datapath — the mint-safe conservation accumulator and
the crossing comparator. Its **throughput** is a *large* datapath — the NTT/PBS pipeline. Those
have opposite engineering needs, so we split them: the small core is **verified in Lean** (golden
models with proven `eval = spec`), the large bulk is **productive SpinalHDL/Hardcaml**, and the two
are tied by **co-simulation** — the bulk RTL is differentially checked against the Lean golden
models on random vectors. You build the bulk; the Lean spine is your reference of truth.

---

## 1. What already exists (your foundation — do not rebuild)

Everything under `fhegg-rtl/lean/` compiles today with just the pinned Lean toolchain
(`lean-toolchain` = `leanprover/lean4:v4.30.0`), **no mathlib, no other dependency**:

```
cd fhegg-rtl/lean && lake build      # ~8 s cold, core Lean only
```

| File | What it gives you |
|---|---|
| `lean/Fhegg/Rtl/Netlist.lean` | the netlist DSL (`Ref`/`Gate`/`Netlist`), `evalNetlist` (golden semantics), `toVerilog` (emitter), `RealizesSpec` (the soundness obligation), `WellFormed`/`emitBounded` (structural checks) |
| `lean/Fhegg/Rtl/Examples/FullAdder.lean` | the worked example: a full adder with `fullAdder_realizes : RealizesSpec …` **proven sorry-free**, emitting real Verilog |
| `lean/Fhegg/Rtl/Examples/RippleAdder.lean` | a parametric `n`-bit ripple-carry adder builder + concrete-width `#guard`s |
| `lean/Fhegg/Rtl/Golden/Accumulator.lean` | **golden model:** the mint-safe conservation gate `Σqout ≤ Σqin` + `mint_safe_accumulator` + the mint-fails-gate tooth |
| `lean/Fhegg/Rtl/Golden/Butterfly.lean` | **golden model:** the NTT butterfly `(a±ωb) mod q` + the invertibility identities `hi±lo` |

The DEEP proofs the golden models shadow live under mathlib in `metatheory/Market/`
(`MintSafeQuantization.lean` — full ℚ mint-safety) and `metatheory/Dregg2/Circuit.lean` (the AIR
emit discipline this RTL path repoints). You do not need mathlib to build the spine.

---

## 2. The interface you build against (the contract)

**Golden model → your RTL.** Each Lean golden `def` is a total computable function. Your RTL
module realizes it iff, on every input vector, the simulated module output equals the golden
function's output. Concretely, for the butterfly:

- Golden: `Fhegg.Rtl.Golden.butterfly (q a b w : Int) : Int × Int` — returns
  `((a + w*b) % q, (a - w*b) % q)`.
- Your RTL: a SpinalHDL `Butterfly(q, width)` component with inputs `a, b, w` and outputs `hi, lo`.
- The tie: co-sim drives random `(a, b, w)` into both, asserts `(hi, lo)` match. See
  `hardware/cosim/README.md`.

**Verified core → your RTL.** For the small soundness-critical blocks (the accumulator gate), the
Lean model is not just a reference but a *proof*: `mint_safe_accumulator` proves the gate forbids a
mint. Your RTL must realize `accGate` exactly; the co-sim is the equivalence check, and the Lean
proof is why realizing it is *sufficient* for soundness.

**Emit path (optional, for the core).** For a block small enough to express in the Lean netlist
DSL, you can `toVerilog` it directly and get a verified-`eval = spec` module for free — then the
only residual is the co-sim seam ("the simulator agrees with `evalNetlist`"). This is the path for
the conservation comparator; the bulk NTT/PBS is too large for the DSL and stays productive-HDL.

---

## 3. The milestone ladder (butterfly → NTT → PBS → fold → bitstream)

Each rung is independently useful and independently co-simulatable. Grades are honest: the early
rungs are buildable today; the late rungs are real engineering with capital/tooling gates.

| # | Milestone | Golden reference | HDL | Grade |
|---|---|---|---|---|
| **M0** | **Single NTT butterfly** — `Butterfly(q,width)` realizing `Golden.butterfly` | `Golden/Butterfly.lean` | SpinalHDL (`hardware/spinalhdl/Butterfly.scala` stub) | Buildable now; the add/sub core is verified |
| **M1** | **Modular reduction** — Barrett/Montgomery reduce mod `q` (BabyBear or the TFHE modulus) | (add a `Golden/ModReduce.lean` spec) | SpinalHDL | Buildable now; standard, well-trodden |
| **M2** | **Full NTT** — log-N stages: twiddle ROM, bit-reversal, negacyclic wrap | extend `Golden/Butterfly.lean` to an `Golden/Ntt.lean` staged spec | SpinalHDL; reference HF-NTT (Chisel, arXiv 2410.04805) | Real datapath work; co-sim vs the staged golden model |
| **M3** | **Wide mint-safe accumulator + comparator** — `Σqout ≤ Σqin` over the batch | `Golden/Accumulator.lean` (`accGate`) — **verified core** | SpinalHDL (adder tree + magnitude comparator); or `toVerilog` from the DSL | Buildable now; this is the soundness gate |
| **M4** | **PBS blind-rotation + external product** — the programmable bootstrap | wrap/port Zama HPU SystemVerilog (`github.com/zama-ai/hpu_fpga`) | SystemVerilog wrap + SpinalHDL glue | Large; wrap, don't rebuild |
| **M5** | **The fold datapath** — CKKS-additive aggregation + TFHE crossing, HBM-fed | `metatheory/Market/CertF.lean` (the clearing certificate) + `Golden/Accumulator.lean` | SpinalHDL top + M2/M3/M4 | Integration; the F2 half of the dark pool |
| **M6** | **The F2 bitstream** — place-and-route on the VU47P, Nitro-attested | the whole spine + `tfhe-rs` differential | Vivado / AWS FPGA dev flow | Capital/tooling-gated; the real accelerator |

Start at **M0** or **M3** — both have a verified golden model in place today and a co-sim contract.

---

## 4. The co-simulation harness plan

The tie between the Lean golden model and your RTL is differential co-simulation
(`hardware/cosim/`, a scaffold today):

1. **Export golden vectors from Lean.** A small Lean `main` prints `(input, expected-output)` rows
   for a golden `def` (JSON or CSV). The seed for this is any `#eval IO.println …` in the examples;
   `hardware/cosim/README.md` sketches a `lake exe`-able vector dumper.
2. **Simulate your RTL** (Verilator for Verilog, or SpinalHDL's built-in sim / `hardcaml`'s
   cycle-accurate sim) on the same input vectors.
3. **Assert equality.** The harness (`hardware/cosim/cosim_harness.rs` stub) reads the golden
   vectors, drives the simulator, and fails on the first mismatch — the RTL analogue of dregg's
   Rust `*_layout_matches_lean` byte-pin twin (`circuit/src/effect_vm_descriptors.rs`).
4. **Scale to sequential equivalence checking** for the wide datapaths (temporal/state differences
   at interfaces): a solver-driven equivalence check against the golden model, counterexample
   waveforms, no hand vectors — the standard industrial pattern.

The residual seam — "the simulator faithfully executes the emitted RTL" — is NAMED, exactly as the
AIR path names its `HashCR` floor. We do not claim a formal Verilog semantics.

---

## 5. Entry points and conventions

- **SpinalHDL:** `hardware/spinalhdl/` — `Butterfly.scala` (commented M0 skeleton), `build.sbt`
  (stub). Elaborate with `SpinalVerilog(...)`; keep module port names matching the golden `def`
  argument order so the co-sim mapping is trivial.
- **Hardcaml alternative:** if you prefer OCaml + SAT property-checking, mirror the same modules;
  `hardcaml_verify` can prove the combinational identities (`butterfly_add`/`butterfly_sub`)
  directly, complementing the Lean proof.
- **New golden models:** add `lean/Fhegg/Rtl/Golden/<Name>.lean`, keep it **core-Lean-only** (no
  mathlib — the spine's fast-build property is load-bearing for contributors), prove the
  correctness property + a non-vacuity `#guard`, and cite any deep mathlib proof it shadows.
- **Do not** modify `metatheory/`, `circuit/`, `circuit-prove/`, `fhegg-fhe/`, or `descriptor_ir2`
  — those are other lanes. This directory is self-contained on purpose.

---

## 6. The north star (why this matters)

The accelerator's primitive — homomorphic linear folds + one bounded nonlinearity — is the *same*
primitive a dark transformer needs (`FHEGG-FPGA-ACCELERATOR.md §5.2`). Building the verified fold
datapath is rung one of the same ladder. And the whole point of the Lean spine is the
Constitution's ethos held down to silicon: **the boundary (conservation, no-mint) is a theorem, and
it stays a theorem through the emit to hardware** — verified core, co-sim-tied bulk, every seam
named. `🥚`
