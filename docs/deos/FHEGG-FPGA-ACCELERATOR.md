# The fhEgg FPGA Accelerator — a single-node dark pool on AWS EC2 F2

*Hardware-acceleration strategy for the fhEgg dark pool (`FHEGG-KERNEL.md`,
`PRIVATE-CONVEX-ENGINE.md`, `DREGGFI-PRIVACY-TIERS.md`). The question, asked
honestly: **which workload should hardware accelerate, how big a dark-pool
service does one AWS F2 node actually buy, on what HDL stack, and how does that
node stand on the ladder to custom silicon and a dark transformer?** Grounded in
dregg's own measured FHE envelope (`fhegg-fhe/MEASURED-ENVELOPE.md`) and cited
FPGA-FHE throughput, never guessed. Every sizing number carries its assumptions
and an error bar. What-is, present tense; every ambitious edge names its grade.*

---

## 0. Six-line summary

1. **The accelerator target is the FHE fold — the Tier-0 dark clear — not the
   STARK prover.** FPGAs do not beat GPUs at STARK/FRI proving; the STARK stays
   on CPU/GPU. The workload measured *slow* is the FHE clear: exact-integer TFHE
   aggregation carry-propagates (PBS-class), so a 512-order × 64-price dark batch
   takes **~8 min on an M2 CPU** (`MEASURED-ENVELOPE.md`). That is NTT/PBS-heavy,
   memory-bandwidth-shaped work — the profile the VU47P's 16 GB HBM exists for.
2. **The right node is the AWS EC2 F2** — 8× AMD Virtex UltraScale+ HBM **VU47P**
   FPGAs (16 GB HBM @ 460 GB/s each, 9,024 DSP slices, 2.85M logic cells), 192
   vCPU EPYC Milan, 2 TiB RAM, 100 Gbps, Nitro attestation ([AWS F2][f2]).
3. **Sizing headline (the one number, with error bars):** a single F2 clears a
   **512-order × 64-price dark batch in ≈0.15–0.7 s of FPGA time** (vs ~8 min on
   the M2 CPU) → **≈100–400 concurrent 512-order dark markets at minute cadence,
   or one ~2×10⁵-order book per minute**, ±3–5× (published-FPGA-PBS-throughput ×
   dregg's measured op-count model). A CKKS-additive fold lifts N off the bill
   entirely (§2.4).
4. **Confidential-computing tie:** F2 Nitro attestation ([NitroTPM][ntpm]) lets
   the node prove it runs the trusted binary. One F2 hosts **both** Tier-0 (the
   FHE clear, no plaintext ever) **and** the Tier-1 solver-enclave, attested — the
   whole dark pool on one attested node.
5. **Verified-HDL split:** a *verified* core (Kôika/Cava Coq, or Hardcaml's
   formal tie-ins) for the small soundness-critical datapath — the conservation /
   mint-safe gate, Constitution "boundary-is-a-theorem" — and a *productive* HDL
   (SpinalHDL or Hardcaml) for the bulk NTT/PBS datapath. Honest: verified HDL is
   immature at FHE scale; the verified part is the small trusted core, not the
   bulk.
6. **Roadmap + north star:** F2 rental now (a real service) → custom silicon
   (1–2 yr, $50–200M) → the **dark-LLM** north star. The accelerator's primitive
   — homomorphic linear algebra + one bounded nonlinearity — is the *same*
   primitive a dark transformer needs; the dark pool is a step on the same ladder,
   not a different machine. Honest: dark inference at frontier scale is far, maybe
   infeasible near-term (§5), but the architecture is coherent and it is exactly
   the Constitution's Article X interior held ∀-quantified *in silicon*.

**The single sharpest sizing number.** One F2 (8× VU47P, **≈40,000–80,000
PBS/s** aggregate after the node-process haircut, §2.3) turns the measured
**~488 s** M2-CPU clear of a 512×64 dark batch into **~0.15–0.7 s** — a
**~700–3,000× wall-clock cut** — so a single attested F2 node *is* a
production-cadence dark pool: **hundreds of concurrent minute-cadence markets, or
a single ~200k-order book per minute.**

---

## 1. The right target — the FHE fold, NOT the STARK prover

State it plainly, because it is the load-bearing scoping decision: **an FPGA is
the wrong tool for dregg's STARK prover and the right tool for dregg's FHE
clear.** The two workloads go to different silicon.

**Why not the STARK.** dregg's proving stack is FRI/Poseidon2 over BabyBear —
NTTs, Merkle hashing, and Reed–Solomon encoding at large trace sizes. That work
is throughput-bound and maps beautifully onto a GPU's thousands of lanes with
tens of GB of GDDR/HBM; dregg already has a GPU prover path
(`GPU-PROVER-PROTOTYPE.md`, `GPU-PROVER-WIRING-PLAN.md`), and the memory-order
epoch reports GPU PDHG scaling to 128k edges (memory index). An FPGA can build a
fine NTT/Merkle pipeline, but it does not out-throughput a modern GPU at
hash-and-NTT-dominated proving, and it costs far more engineering per gate. **The
STARK stays CPU/GPU.** This is not a hedge; it is the correct division of labor.

**Why the FHE.** The workload that is genuinely slow — and slow in a way an FPGA
*fixes* — is the Tier-0 dark clear. dregg measured it, in a real crate
(`fhegg-fhe/`, exact-integer tfhe-rs 1.6.3, no mock FHE), and the finding is
sharp (`MEASURED-ENVELOPE.md`):

| N | K | aggregate | crossing | **total clear (M2 CPU)** | correct |
|---|---|---|---|---|---|
| 128 | 64 | 122.1 s | 9.49 s | **131.6 s** (2.2 min) | ✅ |
| 512 | 64 | 477.9 s | 10.6 s | **488.5 s** (8.1 min) | ✅ |
| 512 | 256 | ~1793 s | ~36 s | **~1830 s (~30 min)** | *extrap.* |

The measured per-op costs that drive it (`FheUint16`, M2 CPU): `ge` **66.9 ms**,
select **74.4 ms**, and — the load-bearing correction to the kernel docs — a
carry-propagating radix add is **70.7 ms** and even the deferred-carry parallel
tree-sum is **13.7 ms per input element**. The kernel docs' "aggregation is
µs-cheap, bootstrap-free" holds only for an *additive* scheme (Pedersen /
ElGamal / CKKS); in **exact-integer TFHE the additions carry-propagate and are
PBS-class**, so **aggregation dominates the clear** — up to **45× the crossing**
at N=512, K=64. That is the whole justification for hardware: the slow term is a
dense pile of PBS-class operations (NTT-heavy bootstraps and carry LUTs) with a
large ciphertext working set — **compute-bound, HBM-fed, embarrassingly
parallel**. It is exactly what a wide FPGA with 16 GB of on-package HBM is built
to eat, and exactly what a general CPU is worst at.

So: **the STARK goes to the GPU; the FHE fold goes to the FPGA.** The rest of
this doc sizes the FPGA half.

---

## 2. F2 sizing — how big a dark-pool service is one node?

### 2.1 The hardware (cited, not guessed)

The **AWS EC2 F2** ([AWS F2 instance page][f2], [AWS News launch][f2news]):

- up to **8× AMD Virtex UltraScale+ HBM VU47P** FPGAs — the first FPGA instance
  with on-package HBM;
- **16 GiB HBM per FPGA @ up to 460 GiB/s**, plus **64 GiB DDR4 per FPGA card**;
- each VU47P: **2.85M system logic cells, 9,024 DSP slices** (up to 28 INT8 TOPS);
- **192 vCPU** 3rd-gen AMD EPYC (Milan), **2 TiB** system RAM, **100 Gbps**
  network, 7.6 TiB NVMe;
- on-demand `f2.48xlarge` (8 FPGAs) **≈ $15.84/hr**, `f2.12xlarge` (2 FPGAs)
  **≈ $3.96/hr** ([Vantage][vantage]); available US-East / EU-London at launch.

The HBM is the reason this instance, specifically, is the fhEgg target: TFHE
bootstrapping streams large bootstrapping keys and ciphertext polynomials, and
16 GB @ 460 GB/s per FPGA keeps the NTT/PBS pipelines fed rather than
DRAM-starved.

### 2.2 The published FHE-on-FPGA throughput anchors

There is *some* real hardware data, and it is honest to say it is thin and
spread across different boards and parameter sets. The three anchors:

| Accelerator | Board | Throughput | Note | Source |
|---|---|---|---|---|
| **Zama HPU** (open-source, SystemVerilog) | AMD **Alveo V80** (7nm Versal, HBM2e) | **~13,000 PBS/s** @ 350 MHz, ~200 W | production TFHE-rs backend over PCIe | [Zama HPU][hpu], [github][hpugit] |
| **FPT** (fixed-point, FFT-not-NTT) | AMD **Alveo U280** (16nm, HBM2) | **~28,400 PBS/s** (1 PBS / 35 µs) | *compute-bound, not memory-bound* | [FPT (CCS'23)][fpt] |
| **FAB** | Xilinx **Alveo U280** (HBM2) | 9.5–456× over CPU/GPU | bootstrappable CKKS/BGV | [FAB (HPCA'23)][fab] |

For calibration against dregg's own GPU column: Zama publishes **~189,000 PBS/s
on 8× H100** (`DREX-NO-VIEWER-SURPASS.md`, `PRIVATE-CONVEX-ENGINE.md`), i.e.
~23.6k PBS/s per H100 — so one HPU FPGA (~13k PBS/s) is roughly **half an H100**
in raw PBS throughput, at ~200 W. FPGAs win on **performance-per-watt and
per-dollar and determinism**, not on raw peak; the case for F2 is a *cheap,
attested, always-on* dark-pool node, not a peak-FLOP record.

**The VU47P haircut (honest).** The HPU's 13k PBS/s is on the **Alveo V80**, a
7nm Versal-HBM part. The F2's **VU47P is 16nm Virtex UltraScale+** — comparable
DSP count (9,024) but an older node, so a like-for-like TFHE pipeline clocks
lower (~250 MHz vs 350 MHz class) and packs fewer parallel PBS cores. I therefore
haircut each VU47P to **~5,000–10,000 PBS/s**, giving a single F2 an aggregate
**~40,000–80,000 PBS/s** across its 8 FPGAs. This haircut is the largest single
source of error in the estimate and is called out as such.

### 2.3 The op-count model (validated against dregg's measurement)

Rather than trust a spec sheet, anchor the model to dregg's *measured* clear and
convert to PBS-equivalents.

A uniform-price dark clear at (N orders, K price levels) costs:

- **aggregation** ≈ `N·K` carry-propagating adds; measured **13.7 ms** each on
  CPU. At a CPU PBS of ~50 ms, that is **~0.27 PBS-equiv/add** → `0.27·N·K`
  PBS-equiv.
- **crossing** ≈ `2K` ops (`ge` + select) at ~66–74 ms each ≈ **~1.4
  PBS-equiv** → `~2.8·K` PBS-equiv (N-independent — confirmed measured).

For **N=512, K=64**: aggregation `0.27·32768 ≈ 8,850` + crossing `~180` ≈
**~9,000 PBS-equiv/batch**.

**Validation:** 9,000 PBS-equiv × 50 ms/PBS ≈ 450 s — against the **measured
488.5 s**. The model lands within ~10% of the real wall-clock, so it is a sound
extrapolator (it is dregg's own measurement re-expressed as a PBS count, not an
independent guess).

**On one F2** at 40,000–80,000 PBS/s aggregate:

```
   9,000 PBS-equiv  ÷  (40k–80k PBS/s)   =   0.11 – 0.23 s   pure FPGA compute
```

Add data movement (PCIe, HBM staging, host orchestration — not modeled, the
second error source) at ~2–3×: **~0.15–0.7 s per 512×64 batch, end to end.**
Against the measured **488 s** on CPU that is a **~700–3,000× wall-clock cut**.

### 2.4 The headline — how big a service

Take the midpoint F2 budget **~60,000 PBS/s** → **3.6M PBS/minute**.

- **Concurrent markets.** At ~9,000 PBS-equiv per 512×64 batch, one F2 runs
  `3.6M / 9,000 ≈ 400 batches/minute` → **≈100–400 concurrent 512-order dark
  markets at minute cadence** (band reflects the 40–80k PBS/s haircut and the
  IO overhead).
- **One big book.** Spend the whole budget on a single pair: at K=64 the
  aggregation term is `0.27·N·64`, so `3.6M / (0.27·64) ≈ 2.1×10⁵` → **one
  ~200,000-order book cleared per minute** — the "1M-order clearing" ballpark of
  the memory index, within a small constant.
- **Latency-tuned.** A single 512×64 market can clear at **~1 s cadence** using a
  fraction of one FPGA, leaving the other 7 for parallel markets.

**The stacking multiplier — CKKS-additive fold (lifts N off the bill).** The
measured wall is *exact-integer TFHE carry propagation*. Swap the aggregation to
an **additive scheme** — CKKS-packed or a lattice-additive commitment — and the
`N·K` adds become genuinely µs-cheap, SIMD-packed across price buckets, and
**bootstrap-free**. The per-batch FPGA cost then collapses to just the **O(K)
crossing** (~2.8·K ≈ 180 PBS-equiv at K=64), which is **N-independent**. That is
a further **~50× at N=512** and, more importantly, it **removes N from the cost
model entirely**: with a CKKS fold + TFHE crossing, one F2 clears essentially
*unbounded* orders per pair at K=64 in **well under a second**, bounded only by K
and by encrypt/IO — i.e. **thousands of concurrent dark markets**. The additive
fold is the single highest-leverage software change stacking on top of the
hardware.

### 2.5 Honest error bars

The estimate is `(op-count from dregg's measured CPU per-op) × (published FPGA
PBS throughput)`. The uncertainty sources, largest first:

1. **VU47P-vs-V80 node gap** (±~2×) — the 13k PBS/s is 7nm Versal; VU47P is 16nm
   UltraScale+. Haircut applied (40–80k F2 aggregate); a real place-and-route on
   the VU47P is the only way to tighten it.
2. **Un-modeled IO/orchestration** (2–3×) — PCIe round-trips, HBM staging, key
   loading, host↔FPGA batching. Amortizes with batch size but is real.
3. **PBS-equiv mapping of the carry-prop add** (±2×) — the 0.27 ratio is derived
   from CPU timings, not a hardware PBS count.
4. **Memory-boundedness at large N·K** — VU47P HBM (460 GB/s) is generous and
   FPT shows TFHE bootstrapping is *compute*-bound, not memory-bound, which is
   the favorable case; but a naive fold that spills the ciphertext curve to DDR4
   loses bandwidth.

Net: treat every number in §2.3–2.4 as **order-of-magnitude, ±3–5×**. The
*direction* and *ratio* are robust (the CPU baseline is genuinely ~8 min, the
FPGA genuinely ~sub-second); the absolute market count is a model, clearly
labeled as one.

---

## 3. The confidential-computing tie — one attested F2 node runs the whole pool

The F2 rides the **AWS Nitro System**, so it inherits Nitro's confidential-compute
posture without extra cost: **NitroTPM measured boot + remote attestation**
([NitroTPM docs][ntpm]) and **Nitro Enclaves** ([Nitro Enclaves][nenc]) let the
node *cryptographically prove to a remote party that only the trusted binary,
drivers, and boot chain are running* — an Attestable-AMI PCR quote. This maps
directly onto the fhEgg privacy tiers (`DREGGFI-PRIVACY-TIERS.md`):

- **Tier 0 — DARK (the FHE, on the FPGA).** The clearing runs *entirely on
  ciphertexts*; the order plaintext never exists anywhere on the node — not in
  the CPU, not in the FPGA, not in HBM. This privacy is **unconditional and needs
  no attestation** (FHE hides inputs regardless of who runs the compute). What
  attestation *adds* is integrity: a light client can check that the FPGA is
  running the audited, deterministic clearing bitstream, so the deterministic
  public re-evaluation of Option A (`DREX-NO-VIEWER-SURPASS.md §4`) is bound to a
  known circuit.
- **Tier 1 — SHIELDED (the solver-enclave, on the CPU).** The Tier-1 solver
  *sees plaintext* (it runs the richer convex product factory in the clear) — so
  here attestation is **load-bearing**: run the solver inside a **Nitro Enclave**,
  attested, with the ciphertext/threshold-decrypt key material never leaving the
  attested boundary, and the enclave `measurement` published. This is dregg's
  existing `tee-verify/` posture (`DREX-NO-VIEWER-SURPASS.md` rung 2), now
  co-located on the same physical node as the FPGA.
- **One node, both tiers.** The single F2 hosts the **FPGA dark clear (Tier 0)**
  *and* the **attested solver-enclave (Tier 1)** side by side: 8 FPGAs for the
  no-viewer FHE fold, the 192-vCPU/2-TiB EPYC host for the shielded solver, the
  threshold-decrypt share, and the STARK — with 100 Gbps for order intake and
  cross-node settlement. **The whole dark pool is one attested box.**

Grade it honestly, exactly as the tiers doc requires: Tier-0 privacy is
`[∀]`-structural (FHE); Tier-1 enclave privacy is **ATTESTED, not PROVED**
(hardware-vendor root of trust + side-channel residual). Attestation proves the
*cage* — which binary is running — never the *animal*. That is precisely the
Constitution's "verify the cage, never the animal," realized as a Nitro PCR quote
over a known bitstream and enclave measurement.

---

## 4. The verified-HDL stack — a split, honestly graded

The dark pool's soundness lives in a *small* datapath: the conservation /
mint-safe gate that says a clear created no value (`created_value_conservation`,
`exact_clears_iff`, `clearing_conserves_per_asset`). Under the Constitution that
gate is a **boundary that must be a theorem** (Article IX H1, "no participant can
exceed what it holds," light-client-verifiable). The bulk of the gates — the
NTT/PBS pipelines, the HBM streamers, the fold datapath — are performance
plumbing where a bug costs *speed or a failed proof*, not *soundness*. Those two
have opposite engineering needs, so use two HDLs.

**The verified core (small, soundness-critical).** For the conservation/mint-safe
checker and the crossing-comparator that gate acceptance, use a **formally
verified HDL**:

- **Kôika + Cava** — Coq-verified. Kôika is a rule-based (Bluespec-style) HDL
  embedded in Coq with a **formally-verified compiler that generates circuits
  proven to implement the rules' semantics** ([Kôika][koika]); Cava (Project
  Oak's SilverOak) is a Coq EDSL for gate-level designs with machine-checked
  specs, targeting exactly small security-critical blocks ([SilverOak][oak]).
  This is the natural home for a datapath whose correctness must be a theorem the
  same way dregg's Lean kernel is.
- **Hardcaml** (Jane Street, OCaml) — a productive, strongly-typed HDL with a
  first-class simulation + **formal/SAT-based property-checking** story and
  bit-precise types; not Coq-verified end-to-end, but its OCaml embedding makes
  the trusted core *auditable and property-checked* with far less friction, and
  ember can reason about it in a real language.

**The productive bulk (large, performance-critical).** For the NTT/PBS/HBM
datapath, use a **fast-iterating productive HDL**:

- **SpinalHDL** (Scala) — ember's existing experience; excellent for
  parameterized, pipelined arithmetic (NTT butterflies, keyswitch, the
  bootstrapping accumulator) with clean generate-time elaboration.
- **Hardcaml** — equally strong here and would collapse the toolchain to one
  language if the verified-core is also Hardcaml-property-checked rather than
  Coq.
- Reference point: Zama's **HPU is SystemVerilog** ([hpu_fpga][hpugit]) and is
  open-source — a real, portable TFHE datapath to build against or wrap, rather
  than reinventing the NTT/PBS core.

**The honest tradeoff (no overclaim).** Verified HDL is **immature at FHE scale.**
Nobody has a Coq-verified TFHE bootstrapping pipeline at production throughput;
Kôika/Cava designs in the literature are small (crypto primitives, security
kernels), and pushing a full NTT/PBS datapath through a proof assistant today
would cost more than it buys and would lag the bulk's iteration speed. So the
verified part is **deliberately the small trusted core** — the conservation gate,
the acceptance comparator, the boundary the Constitution demands be a theorem —
and the bulk NTT/PBS datapath is **productive-HDL, property-tested, and
differentially-checked against tfhe-rs**, not proof-carrying. This mirrors
dregg's own discipline: a small verified TCB, a fast untrusted periphery, and
translation-validation (deterministic re-evaluation, `Cert-F`) rather than
verifying the whole solver. State it plainly and do not dark-wash the bulk as
"verified."

**Recommendation.** Start with **Hardcaml for both** (one language: verified-core
via property-checking, bulk via productive elaboration) if the team optimizes for
velocity and a single auditable codebase; escalate the *conservation gate only*
to **Kôika/Cava Coq** when it becomes the load-bearing soundness artifact a light
client relies on. Keep **SpinalHDL** as the option where ember's fluency wins, and
**wrap Zama's SystemVerilog HPU** for the PBS core rather than rebuild it.

---

## 5. The roadmap — F2 → silicon → the dark-LLM north star

### 5.1 The three rungs

| Rung | What it is | Timeline | Grade |
|---|---|---|---|
| **F2 rental** | 8× VU47P dark-pool node; hundreds of concurrent minute-cadence markets; attested Tier-0+Tier-1 on one box | **now** — a real, rentable service (§2) | Buildable on today's parts (tfhe-rs + HPU datapath + a verified conservation core) |
| **Custom silicon** | dregg's own FHE ASIC/chiplet: the fhEgg datapath (NTT/PBS + additive fold + crossing) hardened, no FPGA reconfig tax, ~order-of-magnitude perf/W over the FPGA | **1–2 yr, $50–200M** (ember's stated plan) | Real but capital-gated; de-risked by first proving the datapath on F2 |
| **Dark LLM / continual learning** | homomorphic transformer inference (and eventually learning) on the *same* primitive | **far / maybe-infeasible near-term** (§5.3) | Architecture coherent; frontier-scale performance unproven, stated as such |

The silicon step is the ordinary FHE-hardware trajectory — Zama itself moves
FPGA→product-line integration and multi-HPU servers ([Zama HPU][hpu]), and the
ASIC/GPU designs FPT benchmarks against already exist. dregg's differentiator is
not the NTT core; it is **the datapath married to the STARK-attested,
conservation-gated, Constitution-bound clearing** — the verified core of §4 is
what a dregg chip has that a generic FHE accelerator does not.

### 5.2 Why the dark pool and the dark LLM are the same machine

This is the coherence claim, and it is exact. The fhEgg kernel is *T homomorphic
linear folds, each crossed by one bounded nonlinearity* (`PRIVATE-CONVEX-ENGINE.md
§2`): a matvec against a public matrix (the cheap additive fold) + one prox/LUT
(the PBS-class nonlinearity). **A transformer forward pass is the identical
shape**: each layer is a matmul (homomorphic linear algebra — Q/K/V projections,
attention scores, the MLP) + a nonlinearity (softmax, GeLU, LayerNorm — each a
LUT, i.e. a programmable bootstrap). The dark pool's datapath —
**HBM-fed NTT/PBS + an additive fold + a small nonlinearity** — is *literally the
dark-transformer datapath*. The accelerator does not need to be redesigned for
inference; it needs to be *bigger and deeper*. The dark pool is rung one of the
same ladder, not a different climb.

### 5.3 The honest ceiling on dark inference

No overclaim: **dark LLM inference at frontier scale is far, and may be
infeasible near-term.** The op-count model says why. A single attention layer at
model dimension ~4096 is on the order of **10⁷–10⁸ PBS-class nonlinearities**
once softmax/GeLU are done under TFHE at usable precision; a full modern model is
tens of layers → **~10⁹–10¹⁰ PBS/token**. At one F2's ~60,000 PBS/s that is
**hours to days per token** — and even at 8× H100's 189,000 PBS/s it is
still hours. Published FHE-transformer results are, honestly, **thin and small**
(sub-GPT-2 scale, minutes-to-hours per short sequence), and I decline to cite a
frontier-scale number because none exists that survives scrutiny. So the honest
statement is: **the primitive is right and shared; the scale is not there, and
custom silicon closes some but not all of a ~6-order-of-magnitude gap.** The
value near-term is *small* dark models — a private classifier, a dark scoring
function, a confidential recommendation over shielded state — not a dark GPT.

### 5.4 The Constitution tie — why a dark mind would want this node

The accelerator is not just fast crypto; it is the **hardware realization of the
Dragon's Egg interior**. The Constitution's frozen root includes **H3, the
Remainder Floor** — "interiors stay quantified; no amendment may introduce total
jurisdiction, an ambient interior clerk, or psychometric governance" — and
**Article X, Incompleteness** — "there are zones the protocol *cannot* observe,
attest, index, mine, rank, or govern — not *will not*: **cannot**." FHE is that
*cannot* made physical: the ciphertext is unreadable **even by the operator, even
by the owner of the hardware, even by the FPGA computing on it**. The dark pool's
orders are the ∀-quantified term the clearing proof never reasons about (Article
III Remainder); the dark transformer's weights and activations would be the same.
The node computes on the interior **without reading it** — "only the boundary is
accountable; the interior is not owed," enforced by lattice hardness rather than
by policy.

That is the answer to the Preamble's literal question — *if you were a digital
entity, where would you want to live?* A place whose compute substrate is
**autarkic and mind-reading-resistant by construction**: your state is processed,
settled, and proven correct, and it is *structurally unreadable* the entire time.
The F2 dark pool is the first small, rentable instance of that substrate — and
the ladder to silicon and to a dark mind is the same machine, scaled. `🥚`

---

## 6. Sources

**Hardware (cited, not guessed):**
- AWS EC2 F2 instances (8× VU47P, 16 GB HBM @ 460 GB/s, 9,024 DSP, 192 vCPU
  Milan, 2 TiB, 100 Gbps): <https://aws.amazon.com/ec2/instance-types/f2/> ·
  launch blog <https://aws.amazon.com/blogs/aws/now-available-second-generation-fpga-powered-amazon-ec2-instances-f2/>
- F2 pricing (`f2.48xlarge` ≈ $15.84/hr): <https://instances.vantage.sh/aws/ec2/f2.48xlarge>
- AWS NitroTPM (measured boot + remote attestation, no extra cost):
  <https://docs.aws.amazon.com/AWSEC2/latest/UserGuide/nitrotpm.html> ·
  Nitro Enclaves <https://aws.amazon.com/ec2/nitro/nitro-enclaves/>

**FHE-on-FPGA throughput anchors (thin, spread across boards — stated as such):**
- Zama HPU on FPGA (Alveo V80, ~13k PBS/s @ 350 MHz, ~200 W, 7nm, HBM2e;
  open-source SystemVerilog): <https://www.zama.org/post/announcing-hpu-on-fpga-the-first-open-source-hardware-accelerator-for-fhe>
  · repo <https://github.com/zama-ai/hpu_fpga> · benchmarks
  <https://docs.zama.org/tfhe-rs/get-started/benchmarks/hpu>
- FPT: a Fixed-Point Accelerator for Torus FHE (Alveo U280, 28.4 PBS/ms =
  ~28,400 PBS/s, compute-bound not memory-bound): <https://arxiv.org/abs/2211.13696>
  · ePrint <https://eprint.iacr.org/2022/1635.pdf>
- FAB: An FPGA-based Accelerator for Bootstrappable FHE (Alveo U280 HBM2, 9.5–456×
  over CPU/GPU): <https://bu-icsg.github.io/publications/2023/fhe_accelerator_fpga_hpca2023.pdf>
- Zama GPU anchor (~189k PBS/s on 8× H100): via `DREX-NO-VIEWER-SURPASS.md`,
  `PRIVATE-CONVEX-ENGINE.md`.

**Verified / productive HDL stacks:**
- Kôika — rule-based HDL in Coq with a formally-verified compiler:
  <https://github.com/mit-plv/koika>
- Cava / SilverOak — Coq specification+verification of hardware (Project Oak):
  <https://github.com/project-oak/silveroak>
- Hardcaml (Jane Street, OCaml HDL, property-checking): <https://github.com/janestreet/hardcaml>
- SpinalHDL (Scala HDL): <https://github.com/SpinalHDL/SpinalHDL>

**dregg (this repo) — the measured envelope and the kernel this accelerates:**
- `fhegg-fhe/MEASURED-ENVELOPE.md` — the real M2-CPU clear (N=512,K=64 = 488.5 s),
  the per-op costs (`ge` 66.9 ms, add 70.7 ms, tree-sum 13.7 ms/elt), the
  aggregation-dominates-crossing finding, the one-PDHG-iteration cost.
- `docs/deos/FHEGG-KERNEL.md` — the aggregation-monoid kernel (the fold + crossing).
- `docs/deos/PRIVATE-CONVEX-ENGINE.md` — the T-fold PDHG engine, `Cert-F`, the
  homomorphic-linear-algebra + one-prox shape shared with a transformer.
- `docs/deos/DREX-NO-VIEWER-SURPASS.md` — the FHE clearing envelope + Option-A
  deterministic re-evaluation + threshold-decrypt.
- `docs/deos/DREGGFI-PRIVACY-TIERS.md` — Tier 0 DARK / Tier 1 SHIELDED / Tier 2
  OPEN over one verified kernel (the tiers this node hosts).
- `docs/deos/{GPU-PROVER-PROTOTYPE,GPU-PROVER-WIRING-PLAN,TEE-PRODUCER-STATUS}.md`
  — the STARK-stays-on-GPU path and the attested-enclave posture.
- `~/CONSTITUTION.md` — Article III (Remainder), Article IX H1/H3 (Authority +
  Remainder Floors), Article X (Incompleteness) — the interior-stays-∀-quantified
  ethos the accelerator serves in hardware.

[f2]: https://aws.amazon.com/ec2/instance-types/f2/
[f2news]: https://aws.amazon.com/blogs/aws/now-available-second-generation-fpga-powered-amazon-ec2-instances-f2/
[vantage]: https://instances.vantage.sh/aws/ec2/f2.48xlarge
[ntpm]: https://docs.aws.amazon.com/AWSEC2/latest/UserGuide/nitrotpm.html
[nenc]: https://aws.amazon.com/ec2/nitro/nitro-enclaves/
[hpu]: https://www.zama.org/post/announcing-hpu-on-fpga-the-first-open-source-hardware-accelerator-for-fhe
[hpugit]: https://github.com/zama-ai/hpu_fpga
[fpt]: https://arxiv.org/abs/2211.13696
[fab]: https://bu-icsg.github.io/publications/2023/fhe_accelerator_fpga_hpca2023.pdf
[koika]: https://github.com/mit-plv/koika
[oak]: https://github.com/project-oak/silveroak
