# fhEgg verified RTL — the landscape, the Lean gap, and the dregg strategy

*Companion to `FHEGG-FPGA-ACCELERATOR.md` (which sizes the F2 dark-pool node and states the
verified-core / productive-bulk split). This doc surveys the verified-RTL landscape honestly and
cited, names the Lean-4 HDL gap, and lays out the concrete dregg strategy that the scaffolding
in `fhegg-rtl/` seeds: a Lean netlist DSL → Verilog emitter reusing dregg's own verified-emit
discipline, golden-model Lean specs for the FHE-fold primitives, and a co-simulation /
translation-validation tie to a productive HDL for the bulk NTT/PBS datapath. What-is, present
tense; every ambitious edge names its grade. This is SCAFFOLDING + a seed example — NOT the FPGA
accelerator.*

---

## 0. Five-line summary

1. **The accelerator target is the FHE fold (the Tier-0 dark clear), not the STARK** — settled in
   `FHEGG-FPGA-ACCELERATOR.md`. Its soundness lives in a *small* datapath (the mint-safe
   conservation gate + the crossing comparator); the *bulk* is the NTT/PBS pipeline.
2. **The verified-RTL landscape is real but Coq-centric.** Kôika, Kami, and Cava/SilverOak give
   machine-checked hardware **in Coq**; Hardcaml (OCaml), Clash (Haskell), and SpinalHDL/Chisel
   (Scala) give productive, type-safe RTL with *lighter* assurance (SAT property-checking or types
   + tests, not a verified compiler).
3. **There is NO mature Lean-4 HDL.** The only Lean-4 HDL that exists is `Verilean/sparkle`, an
   early, unaudited 2026 independent project with extraordinary uncorroborated claims — treat with
   strong skepticism. Unlike Coq/Haskell/OCaml/Scala, **Lean 4 has no credible verified HDL that
   emits synthesizable RTL.** This is the open niche dregg's spine addresses head-on.
4. **The dregg strategy: don't build a general Lean HDL — REPOINT the emit discipline dregg already
   proved.** dregg's AIR path is a Lean circuit object with a denotational semantics, emitted to a
   Rust descriptor and tied by a byte-pinned twin (`*_layout_matches_lean`). `fhegg-rtl/` repoints
   exactly that pattern at RTL: a tiny Lean netlist DSL with `eval` + `toVerilog`, the verified core
   proven `eval = spec` in Lean, the bulk in SpinalHDL, tied by co-simulation.
5. **Concrete split:** the **mint-safe accumulator** (conservation gate) and the **butterfly
   add/sub combiner** are *verified-Lean golden models*; the **NTT schedule, modular reduction
   (Barrett/Montgomery), and the PBS blind-rotation** are *productive SpinalHDL*, differentially
   co-simulated against the Lean golden models. The seed (`fhegg-rtl/lean/`) compiles today with a
   worked full-adder → ripple-adder example emitting real Verilog.

---

## 1. The verified-RTL landscape (cited, not guessed)

### 1.1 The Coq tier — machine-checked, research-grade, small designs

- **Kôika** (MIT PLV/CSG) — a core rule-based HDL (the "essence of Bluespec") embedded in Coq,
  with a **formally-verified compiler** that generates circuits proven to implement the rules'
  one-rule-at-a-time semantics, targeting a minimal subset of synthesizable Verilog (and C++ for
  simulation). This is the strongest "verified" in the list: the compiler itself carries a Coq
  proof. Research-grade (PLDI 2020). <https://github.com/mit-plv/koika> ·
  <https://dl.acm.org/doi/10.1145/3385412.3385965>
- **Kami** (MIT PLV) — a Coq framework to implement, specify, verify, and compile Bluespec-style
  hardware with **modular, component-level proofs**; flagship result is a verified family of
  multicore RISC-V systems with cache coherence. Extraction is *indirect*: Kami → Bluespec →
  Verilog (it does not emit Verilog directly). Has an industrial fork at SiFive. ICFP 2017.
  <https://github.com/mit-plv/kami> · <http://plv.csail.mit.edu/kami/>
- **Cava / SilverOak** (Google, Project Oak) — "Coq + Lava," a Lava-style gate/datapath HDL
  embedded in Coq's Gallina; you write circuits and **prove them correct in Coq**, targeting
  OpenTitan-style security blocks (AES, adders), extracting to SystemVerilog/netlists. The natural
  home for a small soundness-critical datapath. <https://github.com/project-oak/silveroak> ·
  <https://project-oak.github.io/silveroak/>

**Read:** the Coq tier proves the most, on the *smallest* designs — crypto primitives, security
kernels, ISA cores. Nobody has a Coq-verified TFHE bootstrapping pipeline at production throughput.
That is precisely why the verified part must be the *small trusted core*.

### 1.2 The productive tier — industrially mature, lighter assurance

- **Hardcaml** (Jane Street, OCaml) — the most *industrially* mature entry: Jane Street's primary
  production-FPGA tool. Assurance is lighter than Coq — no verified compiler — but `hardcaml_verify`
  offers **SAT-based property proving/formal verification**, plus native cycle-accurate + event
  simulators, and it emits Verilog (and ingests it via Yosys). FPGA 2024, arXiv 2312.15035.
  <https://github.com/janestreet/hardcaml> · <https://arxiv.org/abs/2312.15035>
- **Clash** (QBayLogic, Haskell) — compiles high-level Haskell to synthesizable VHDL/Verilog/
  SystemVerilog; a signals-as-streams model with type-safe clock-domain crossing. Assurance is
  Haskell's type system, **not machine-checked proofs**. Mature, BSD-2. <https://clash-lang.org/>
- **SpinalHDL** and **Chisel** (Scala) — productive HDLs that elaborate to standard Verilog/VHDL
  (SpinalHDL preserves Scala names/hierarchy in the output). *Productivity + parameterizability*
  tools; assurance is type-checking + testing, no formal correctness on the generated RTL. Both
  mature and widely used (Chisel underpins RocketChip/RISC-V silicon).
  <https://spinalhdl.github.io/SpinalDoc-RTD/> · <https://www.chisel-lang.org/>

**Read:** the productive tier iterates fast and scales to real datapaths, but a bug there costs
*speed or a failed proof*, not *soundness* — exactly the right place for the bulk NTT/PBS pipeline.

### 1.3 The Lean-4 gap (the honest verdict)

**There is no mature, credible, verified Lean-4 HDL that emits synthesizable RTL.** The only
Lean-4 HDL located is **`Verilean/sparkle`** — self-described as "a type-safe, formally verifiable
HDL compiler in Lean 4," Clash-inspired, claiming synthesizable SystemVerilog via a
`#synthesizeVerilog` macro and safety/liveness proofs via `bv_decide`/LTL. **Treat with strong
skepticism:** it is an early, unvetted 2026 independent project (~92 stars, no paper, no
institutional backing) whose README makes extraordinary, uncorroborated claims (a RISC-V core that
"boots Linux 6.6.0 with 102 formal proofs," formally-verified YOLOv8/H.264/TLS-1.3 cores) — a
breadth-vs-maturity mismatch characteristic of over-claiming. None of it was independently
verifiable. <https://github.com/Verilean/sparkle> · <https://github.com/Verilean>

Adjacent-but-not-an-HDL: Lean-4 DSLs for **ZK circuits** exist (R1CS/PLONK "clean"-style DSLs in
the verified-zkEVM orbit) — circuit verification, not RTL/Verilog synthesis. And dregg's own AIR
path (`metatheory/Dregg2/Circuit.lean`) is a Lean circuit-constraint object — again ZK/AIR, not
synthesizable hardware.

**So the Lean-4 hardware niche is open.** dregg does not try to fill it with a general HDL (that is
a multi-year project and the wrong bet). It fills the *narrow* slice it needs — a verified core
datapath — by repointing a discipline it already proved.

---

## 2. The dregg strategy — repoint the verified-emit discipline at RTL

### 2.1 The discipline dregg already has (the pattern to reuse)

dregg's AIR/ZK path is a worked instance of **"prove semantics → emit → byte-pin twin"**:

- **A Lean object with a denotational semantics.** `metatheory/Dregg2/Circuit.lean` defines an
  arithmetic constraint IR (`Expr` = var/const/add/mul, `Constraint`, `satisfied`) with an
  `Expr.eval` semantics, and proves `bridge : satisfied kernelCircuit (encode …) ↔ fullStepInv …`
  — the circuit is sound ∧ complete against the verified spec. `Market/CertF.lean` does the same for
  the convex-clearing certificate (`certCircuit_sound`).
- **An emitter to a concrete artifact.** The circuit data extracts to a Rust
  `EffectVmDescriptor2` (`metatheory/Dregg2/Circuit/Emit/*.lean`).
- **A byte-pinned twin ties Lean to Rust.** The Rust `*_layout_matches_lean` tests (e.g.
  `circuit/src/effect_vm_descriptors.rs::rotation_layout_matches_lean`) rebuild the layout literal
  and `assert_eq!` it against the Lean-emitted manifest. **Both sides PIN; neither parses.** A
  layout fact can change only by re-emitting from Lean AND re-anchoring the twin — translation
  validation without trusting a translator.

### 2.2 The repoint (what `fhegg-rtl/` seeds)

The RTL spine is the SAME shape with Verilog as the artifact and co-simulation as the twin:

| AIR/ZK path (exists, proven) | RTL path (`fhegg-rtl/`, seeded) |
|---|---|
| `Expr`/`Constraint` IR + `Expr.eval` | `Netlist` DSL (and/or/xor/not/buf) + `evalNetlist` |
| `bridge`/`certCircuit_sound` (`satisfied ↔ spec`) | `RealizesSpec nl spec` (`∀ ins, evalNetlist nl ins = spec ins`), proven for the worked example |
| emit → `EffectVmDescriptor2` (Rust) | `toVerilog` → synthesizable Verilog text |
| `*_layout_matches_lean` Rust byte-pin twin | co-simulation: Verilator/sim output on `toVerilog nl` vs `evalNetlist nl` (`hardware/cosim/`) |
| residual: `HashCR` (a named floor) | residual: "the Verilog simulator agrees with `evalNetlist`" (a named co-sim seam) |

The honest boundary is identical to the AIR path's: Lean does not model the Verilog *language*, so
`toVerilog` is trusted-by-construction + co-sim-checked, not proven. That single seam is NAMED, not
laundered — exactly as the AIR path names `HashCR`.

### 2.3 The verified-core / productive-bulk split (concrete)

Following `FHEGG-FPGA-ACCELERATOR.md §4`, split the datapath by whether a bug costs *soundness* or
*speed*:

**Verified-Lean (the small trusted core) — `fhegg-rtl/lean/`:**

- **The mint-safe conservation accumulator** (`Golden/Accumulator.lean`). The gate `Σqout ≤ Σqin`
  the encrypted fold checks post-quantization — the boundary the Constitution (Art IX H1) demands
  be a theorem. Its full value-domain mint-safety (over ℚ, directional floor/ceil rounding, no-wrap
  field refinement) is already proven under mathlib in `metatheory/Market/MintSafeQuantization.lean`;
  the golden model here is the dependency-free `Δ = 1` integer restatement + tooth, the co-sim
  reference for the accumulator RTL.
- **The bit-level adder core** (`Examples/FullAdder.lean`, `Examples/RippleAdder.lean`). The
  full-adder cell is proven `eval = spec` sorry-free; the ripple adder composes it. This is the
  add/sub datapath under the butterfly and the accumulator.
- **The butterfly add/sub combiner** (`Golden/Butterfly.lean`). The `a ± ω·b` legs with the
  invertibility identities (`hi + lo = 2a`, `hi − lo = 2ωb`) proven — the golden model the NTT
  butterfly RTL is co-simulated against.

**Productive SpinalHDL/Hardcaml (the large fast bulk) — `fhegg-rtl/hardware/`:**

- The **modular multiplier + Barrett/Montgomery reduction**, the **log-N NTT schedule** (twiddle
  ROM, bit-reversal, negacyclic wrap), the **PBS blind-rotation + external product**, and the **HBM
  streamers**. A bug here fails a proof or loses throughput, not soundness. Differentially
  co-simulated against the Lean golden models and against `tfhe-rs` — never dark-washed as "verified."

**Recommendation (unchanged from the accelerator doc, sharpened):** start the bulk in **SpinalHDL**
(ember's fluency) or **Hardcaml** (one-language, SAT-property-checked), and **wrap Zama's
open-source SystemVerilog HPU** for the PBS core rather than rebuild it. Escalate the *conservation
gate only* toward **Kôika/Cava Coq** if and when a light client relies on it as the load-bearing
soundness artifact; until then the Lean golden model + co-sim is the right assurance/velocity point.

---

## 3. The seed that exists today (`fhegg-rtl/lean/`)

The scaffolding is not a sketch — it compiles (`lake build`, core Lean only, no mathlib, ~8 s cold)
and carries a genuine end-to-end example:

- **`Fhegg/Rtl/Netlist.lean`** — the combinational netlist DSL: `Ref` (input/gate/literal), `Gate`
  (`and/or/xor/not/buf`), `Netlist`, the denotational `evalNetlist`, `WellFormed`, the `toVerilog`
  emitter, and the `RealizesSpec` soundness shape.
- **`Fhegg/Rtl/Examples/FullAdder.lean`** — the full adder as a 5-gate netlist, `fullAdderSpec` the
  golden function, and **`fullAdder_realizes : RealizesSpec fullAdder fullAdderSpec` proven
  sorry-free** (unfold the fold, case-split three bits, `rfl`). `#eval` prints the real module:

  ```verilog
  module full_adder (
    input  [2:0] in,
    output [1:0] out
  );
    wire w0; wire w1; wire w2; wire w3; wire w4;
    assign w0 = in[0] ^ in[1];
    assign w1 = w0 ^ in[2];
    assign w2 = in[0] & in[1];
    assign w3 = w0 & in[2];
    assign w4 = w2 | w3;
    assign out[0] = w1;
    assign out[1] = w4;
  endmodule
  ```

- **`Fhegg/Rtl/Examples/RippleAdder.lean`** — a parametric `n`-bit ripple-carry adder built by
  folding `n` full-adder cells (carry chained), with `#guard`s checking it against Lean's `Nat`
  addition at 4- and 8-bit widths, emitting real Verilog. (The *parametric* `eval = a+b` proof by
  induction on width is a named CONTRIBUTING milestone; the per-cell proof is its inductive core.)
- **`Fhegg/Rtl/Golden/{Accumulator,Butterfly}.lean`** — the FHE-fold golden models above, with
  their soundness/invertibility theorems proven and non-vacuity `#guard`s.

Honest grade: this is a **seed** — a verified bit-datapath + emitter + golden models + the co-sim
plan. It is NOT the NTT, NOT the PBS, NOT a bitstream. Those are the contributor effort
(`fhegg-rtl/CONTRIBUTING.md`), which this spine exists to parallelize.

---

## 4. FHE-on-FPGA datapath anchors (for the bulk contributor)

The NTT butterfly + modular reduction is repeatedly named as *the* FHE bottleneck datapath:

- **Zama HPU** — the first open-source FHE hardware accelerator, a full SystemVerilog TFHE
  processor for AMD Alveo V80 (~350 MHz, ~13k PBS/s, ~200 W). Confirms the datapath: the PBS is a
  blind-rotation whose external product "is implemented using an NTT."
  <https://www.zama.org/post/announcing-hpu-on-fpga-the-first-open-source-hardware-accelerator-for-fhe>
  · <https://github.com/zama-ai/hpu_fpga>
- **FPT** (KU Leuven COSIC, CCS 2023) — a fixed-point TFHE bootstrapping FPGA accelerator on Alveo
  U280 exploiting FHE noise to bootstrap in approximate fixed-point, ~1 bootstrap / 35 µs.
  <https://arxiv.org/abs/2211.13696>
- **FAB** (BU ICSG, HPCA 2023) — an FPGA accelerator for bootstrappable (CKKS-class) FHE.
  <https://bu-icsg.github.io/publications/2023/fhe_accelerator_fpga_hpca2023.pdf>
- **NTT in productive HDLs** — no SpinalHDL NTT located, but a concrete **Chisel** one exists:
  **HF-NTT**, a hazard-free reconfigurable NTT accelerator, Chisel + Vivado 2022.2, parameterized
  over degree/modulus/PE count. <https://arxiv.org/pdf/2410.04805>

**Translation-validation / co-simulation** is the standard industrial tie between a golden reference
and productive RTL: a C/executable golden model checked against RTL by sequential equivalence
checking (counterexample waveforms, no hand vectors). Hardcaml co-sims its OCaml model against
generated RTL; Verilator co-simulation differentially tests emitted Verilog against a source-language
reference. dregg's twist is that the golden model is a *Lean* object with a *proven* `eval = spec`,
so the co-sim ties productive RTL to a machine-checked reference rather than an untrusted C model.

---

## 5. Sources

**Verified / productive HDL:**
- Kôika — <https://github.com/mit-plv/koika> · <https://dl.acm.org/doi/10.1145/3385412.3385965>
- Kami — <https://github.com/mit-plv/kami> · <http://plv.csail.mit.edu/kami/>
- Cava / SilverOak — <https://github.com/project-oak/silveroak> · <https://project-oak.github.io/silveroak/>
- Hardcaml — <https://github.com/janestreet/hardcaml> · <https://arxiv.org/abs/2312.15035>
- Clash — <https://clash-lang.org/>
- SpinalHDL — <https://spinalhdl.github.io/SpinalDoc-RTD/> · Chisel — <https://www.chisel-lang.org/>
- Lean-4 HDL (early, unaudited — flagged) — <https://github.com/Verilean/sparkle>

**FHE-on-FPGA:**
- Zama HPU — <https://github.com/zama-ai/hpu_fpga> · FPT — <https://arxiv.org/abs/2211.13696> ·
  FAB — <https://bu-icsg.github.io/publications/2023/fhe_accelerator_fpga_hpca2023.pdf> ·
  HF-NTT (Chisel) — <https://arxiv.org/pdf/2410.04805>

**dregg (this repo) — the discipline this repoints + the golden models:**
- `metatheory/Dregg2/Circuit.lean` — the AIR circuit IR + `bridge` (the emit-discipline pattern).
- `circuit/src/effect_vm_descriptors.rs::rotation_layout_matches_lean` — the byte-pin twin.
- `metatheory/Market/CertF.lean` — `certCircuit`/`certCircuit_sound` (define a circuit + prove sound).
- `metatheory/Market/MintSafeQuantization.lean` — the full mint-safe quantized accumulator proof.
- `docs/deos/FHEGG-FPGA-ACCELERATOR.md` — the F2 sizing + the verified-core/productive-bulk split.
- `fhegg-rtl/` — the seed (Lean spine + golden models + SpinalHDL/co-sim stubs + CONTRIBUTING).
