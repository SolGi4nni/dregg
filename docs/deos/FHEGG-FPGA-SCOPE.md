# fhEgg on AWS F2 — an honest FPGA scoping (feasibility + first stone, NOT an implementation)

*Written 2026-07-24 (lane fpga-scope). This is a SCOPING deliverable: no HDL exists, no HDL is
written here, and no feasibility number below is a measurement of an FPGA. Every claim cites a
file:line, a number measured in this tree, or a named external reference. Positioned against the
two prior FPGA documents — `FHEGG-FPGA-ACCELERATOR.md` (the all-TFHE PBS-engine sizing, F2
hardware citations, TEE scoping, verified-HDL split) and `FHEGG-CODEX-ROUND4-RAW.md` Q2 (the
"crossing appliance, not a generic FHE company" analysis) — and updated with what is new since
they were written: today's real AMD GPU numbers, the built portable RNS-NTT engine, and the
Lean-proven NTT root orders.*

**The substrate, out loud (ember's rule): the AIR / relation / spec is AUTHORED IN LEAN.** The
FPGA scoped here is a *datapath accelerator* that must refine an already-stated Lean contract
(`NttRefines`, `metatheory/Dregg2/Crypto/WgpuBfvNttSpec.lean:234`), exactly the way the wgpu
backend does today. RTL has the same epistemic status as WGSL: an untrusted implementation held
to the Lean spec by strict interpreters and differential gates — never a second spec, never a
place where constraints are hand-authored (roadmap `FHEGG-MATURITY-ROADMAP.md` §3.5).

---

## 0. Verdict in five lines

1. **The RNS fold-add is NOT an FPGA target.** Measured today on the deployed AMD hardware: the
   resident fold is 2.65–2.72× CPU and **72–75% of its wall-clock is PCIe upload**
   (`FHEGG-GPU-AMD-NUMBERS-2026-07-24.md`). An F2 card sits behind the same PCIe boundary and its
   HBM (~460 GB/s) does not out-run the 6750 XT's GDDR6 (432 GB/s spec). Nothing to win.
2. **The negacyclic RNS-NTT (under ct×ct multiply) IS the FPGA sweet spot** — architecturally,
   because our portable GPU kernel must *emulate* the 36–37-bit modular multiply in u32 limbs
   (`fhegg-fhe/src/bfv_ntt_gpu.rs:5-13`), while FPGA DSP slices do it natively at pipeline rate.
3. **The crossing/argmax is NOT a first-stone target.** The adopted Tier-0 crossing is
   output-boundary MPC at ~1–7 ms on CPU (`fhegg-fhe/src/mpc.rs:17,37-39`,
   `docs/deos/OUTPUT-BOUNDARY-MPC.md`); the PBS crossing is the all-TFHE *fallback*, and a PBS
   engine is the Zama-HPU-scale build already sized in `FHEGG-FPGA-ACCELERATOR.md` §2.
4. **The first stone is one RNS-NTT unit on one VU47P**, differentially validated against the
   SAME Lean contract and the SAME proved root tables the wgpu backend is held to
   (`metatheory/Market/PrivateBookBfvRootOrder.lean:69` — exact order 8192 for all three
   deployed moduli).
5. **The named blocker before any RTL: no measured wgpu NTT wall-clock exists in this tree.**
   The validation matrix proves the NTT *correct* on hardware, not *fast*
   (`FHEGG-WGPU-VALIDATION-MATRIX.md` rows 23–24). An FPGA win over an unmeasured baseline is
   not a claim anyone gets to make; measuring the hbox 6750 XT NTT multiply is step 0.

---

## 1. Which fhEgg ops an FPGA wins vs the AMD GPU — op by op, from the real code

### 1.1 RNS fold-add — NO (memory- and transfer-bound; the FPGA fixes neither)

The fold is coefficient-wise conditional-subtract addition over three RNS rows
(`fhegg-core/src/bfv_lean.rs:497` `add_row`; shader `fhegg-fhe/src/shaders/bfv_fold.wgsl` does the
identical `s = a+b; if s>=q { s-q }` per lane). There is no multiply anywhere on the path — it is
pure memory bandwidth. Today's measurement on the deployed hardware
(`FHEGG-GPU-AMD-NUMBERS-2026-07-24.md`):

- resident fold on hbox RX 6750 XT: 2.65–2.72× CPU at K=8, N=1000..8192 — and **upload is
  34/47 ms (72%) to 282/374 ms (75%)** of the resident wall-clock;
- effective host→device throughput implied by those rows: ~197 MB / 34 ms ≈ **5.8 GB/s** at
  N=1000 and ~1.6 GB / 282 ms ≈ 5.7 GB/s at N=8192 — the PCIe/driver floor, not compute.

An F2 FPGA is on the same side of the same bus (QDMA over PCIe; the AWS shell). It cannot beat
the transfer term, and on the compute term the VU47P's 16 GiB HBM at up to ~460 GB/s
(`FHEGG-FPGA-ACCELERATOR.md` §2.1, citing AWS) is at parity with the 6750 XT's 432 GB/s GDDR6
(spec sheet, not measured). Codex reached the same conclusion from the other direction:
"Native RLWE additions may be cheap enough on CPU/GPU that shipping them to F2 is
counterproductive" (`FHEGG-CODEX-ROUND4-RAW.md` Q2 §1). **The fold stays on the GPU arena**
(chunked-arena + full-pipeline residency are the named levers, same doc §"two performance
levers").

### 1.2 Negacyclic RNS-NTT / ct×ct multiply — YES (this is the FPGA's honest sweet spot)

`bfv_mul.rs` names the hot path exactly: "the multiply cost is the negacyclic polynomial
multiplication in the EXTENDED RNS basis — (I)NTT + pointwise mul. That is the NTT the convex
engine will hammer" (`fhegg-fhe/src/bfv_mul.rs:35-38`). The portable engine for it exists
(`fhegg-fhe/src/bfv_ntt_gpu.rs`), and its own module doc states the structural handicap the FPGA
removes:

- WGSL has no `u64`, so every 36–37-bit modular multiply is an **exact three-limb radix-2^16
  Montgomery product** built from u32 operations (`bfv_ntt_gpu.rs:8-12`,
  `GPU_MONTGOMERY_RADIX = 2^48` at `bfv_ntt_gpu.rs:37`; the shader's seven-limb REDC carrier in
  `shaders/bfv_ntt.wgsl`). One butterfly = dozens of u32 multiply/add/carry instructions.
- A VU47P DSP48E2 datapath computes the same 37×37-bit product natively: ~4–6 DSP48E2 per
  full-width product (27×18 hardened multipliers, standard decomposition), ~3 products per
  Montgomery/Barrett modmul → **~12–18 DSPs per fully-pipelined modular multiplier producing one
  result per cycle**. Against 9,024 DSP slices that is capacity for **several hundred butterfly
  PEs** before routing/clock pressure — this is capacity arithmetic from the DSP inventory
  (`FHEGG-FPGA-ACCELERATOR.md` §2.1), NOT a performance claim; timing closure at the 16nm
  UltraScale+ ~250–300 MHz class is exactly what the first stone must establish.
- The transform is small and fixed: deg-4096 radix-2 = 2048×12 = **24,576 butterflies per
  transform** (the Lean geometry pins this: `BUTTERFLIES_PER_TRANSFORM := (DEGREE/2) * LOG_DEGREE`,
  `metatheory/Market/PrivateBookBfvNttFamily.lean:60`); one RnsPoly product = 9 transforms +
  3×4096 pointwise products (2 forward + 1 inverse per row × 3 rows). The working set (a few MB
  of coefficients + fixed root/twist tables) fits entirely in on-chip URAM/BRAM — the classic
  FPGA regime: deep pipeline, zero instruction overhead, exact custom-width arithmetic.

Honest counterweight, so the sweet spot is not oversold: the GPU handicap is instruction
amplification, not impossibility — and **no measured wgpu NTT wall-clock exists in this tree**
(§0.5). If the measured hbox NTT multiply turns out fast enough for the DrEX clearing cadence,
this whole program stays dormant (§5, decision gates).

### 1.3 Crossing / argmax — NO for the first stone

The adopted Tier-0 crossing computes `p* = argmax_j min(D[j],S[j])` as an **oblivious tournament
in secret shares** after partial decryption of only the aggregate — measured ~1–7 ms on CPU,
revealing only `(p*, V*)` (`fhegg-fhe/src/mpc.rs:17,37-39`; `docs/deos/OUTPUT-BOUNDARY-MPC.md`;
adopted-correction banner of `FHEGG-FPGA-ACCELERATOR.md`). Milliseconds on a CPU does not buy an
FPGA. The in-ciphertext PBS crossing is the *fallback* path, and accelerating PBS is the Zama
HPU's whole reason to exist — a multi-year engine build (blind rotation, key-switch, HBM-resident
bootstrapping keys) already sized with error bars in `FHEGG-FPGA-ACCELERATOR.md` §2.2–2.5
(~5–10k PBS/s per VU47P after the V80→VU47P node haircut). Out of first-stone scope.

### 1.4 Key-switch / relinearization — named, second stone at the earliest

Full BFV ct×ct multiply is tensor (4 polynomial products from `(c0,c1)⊗(d0,d1)`) + basis
extension + relinearization (`fhegg-fhe/src/bfv_mul.rs:31-34` names the fhe-math machinery;
today the semantic oracle is fhe.rs itself). Relin/key-switch is large streaming key material —
the op where HBM residency genuinely matters and where the HPU's memory hierarchy is the thing
to study. It only becomes an FPGA question after the NTT unit exists and after the from-scratch
tensor+relin stone (named in `bfv_mul.rs:31-34`) is built on the CPU/GPU side.

---

## 2. The AWS F2 shape (with one correction to this lane's own brief)

Per `FHEGG-FPGA-ACCELERATOR.md` §2.1 (citing the AWS F2 pages directly):

- **The F2 FPGA is the AMD Virtex UltraScale+ HBM VU47P — 16nm UltraScale+, NOT Versal.** (The
  lane brief said "Versal / UltraScale+"; the Versal part in this story is the **Alveo V80** the
  Zama HPU runs on — which is precisely why HPU reuse is a *port*, not a wrap: different
  generation, different hardened DSP/NoC resources, different shell/clocking, no bitstream
  portability. `FHEGG-CODEX-ROUND4-RAW.md` Q2 §2.)
- Per FPGA: **16 GiB HBM @ up to 460 GB/s + 64 GiB DDR4**, 2.85 M logic cells, **9,024 DSP48E2**;
  up to 8 FPGAs per instance (f2.48xlarge ≈ $15.84/hr on-demand, f2.12xlarge ≈ $3.96/hr).
- Host interface: the AWS shell with **QDMA over PCIe** — host↔card DMA + register access; the
  developer flow is the AWS FPGA developer kit (Vivado/Vitis → AFI). The shell, HBM streamers,
  and QDMA integration are in-house work by definition (AWS's shell is the fixed boundary);
  codex's build/buy split (`FHEGG-CODEX-ROUND4-RAW.md` Q2 §2 "Build in-house") stands.
- Nitro attestation exists at the instance level, and Tier-0 needs **no TEE at all** — the FPGA
  computes on ciphertext (`FHEGG-FPGA-ACCELERATOR.md` §3, unchanged; not re-argued here).

What this shape means for us, concretely: the F2 gives exactly one thing our GPUs do not — a
sea of exact-width hardened multipliers with a deep on-chip SRAM hierarchy next to HBM. It does
NOT give us a faster bus (PCIe both ways), NOT more bandwidth than the 6750 XT, and NOT the 7nm
clocks the HPU's published numbers were achieved on.

---

## 3. The first fhEgg-on-F2 stone: ONE RNS-NTT unit, held to the Lean contract

The smallest honest cut that produces a decision-grade number, defined so that every gate is
already stated in this tree:

**Scope.** One negacyclic odd-NTT compute unit on one VU47P: forward transform, pointwise
modular multiply, inverse transform, for degree 4096 over exactly the three deployed RNS moduli
`FOLD_MODULI = [0xffffee001, 0xffffc4001, 0x1ffffe0001]` (`fhegg-core/src/bfv_lean.rs:72`) —
which are the same numbers, in decimal, that the Lean root-order proofs pin: 68719403009,
68719230977, 137438822401. Root and twist tables are *generated from the proved family*, not
re-derived: `deployedPsi_isPrimitiveRoot` proves each deployed ψ has exact order 8192 = 2N
(`metatheory/Market/PrivateBookBfvRootOrder.lean:39-77`, `#assert_axioms` at :93), closing the
root-table premise so an FPGA root ROM with a wrong or non-primitive root is a *caught*
divergence, not a silent one.

**The spec it must refine (Lean-authored, already stated).** `NttRefines`
(`metatheory/Dregg2/Crypto/WgpuBfvNttSpec.lean:234`):
`∀ a b row k, impl a b row k = rnsNegacyclicMul a b row k` — the exact proposition the file's
header says the parity/mutation tests target (`WgpuBfvNttSpec.lean:10-14`), with the scheduled
odd-NTT form (`oddNtt`/`oddNttMul`, `metatheory/Market/PrivateBookBfvNttFamily.lean:160,171`;
`OddNttRefines` at :279). The theorem boundary stays exactly as that header states it: Lean
proves the reference algebra; "a device executed the RTL faithfully" is discharged by
differential + mutation testing, the same way it is for WGSL today. No claim of verified RTL is
made or planned for this stone — verified-HDL escalation for a *small soundness core* is the
separate, already-graded discussion in `FHEGG-FPGA-ACCELERATOR.md` §4.

**Integration seam.** A fifth labeled backend of `RnsNttEngine`
(`fhegg-fhe/src/bfv_ntt_gpu.rs:104-121`: today `Wgpu | CpuPolicy | CpuUnavailable |
CpuAdapterLimits`), holding the engine's existing discipline: invalid shapes, non-canonical
residues, and execution failures are refused loudly and **never relabeled as a successful
accelerator result** (`bfv_ntt_gpu.rs:20-23`). The FPGA path inherits the identical preflight,
error taxonomy, and backend-labeling so a fallback can never masquerade as an F2 green.

**Validation, in order (each gate cites its harness):**
1. **Step 0 — measure the baseline that does not exist yet:** the hbox 6750 XT wall-clock for
   the deg-4096 3-row NTT multiply via `bfv_ntt_gpu` (bench scaffold exists:
   `fhegg-fhe/src/bin/private_book_bfv_wgpu_bench.rs`). No FPGA claim is meaningful before this
   number is on record in `TESTQALOG.md`.
2. **RTL simulation bit-exact** against `transform_odd_rns_cpu` / `multiply_rns_cpu` on the full
   existing differential corpus — the same corpus rows the validation matrix pins for wgpu
   (`docs/deos/FHEGG-WGPU-VALIDATION-MATRIX.md` rows "BFV RNS NTT multiply" and "BFV scheduled
   odd NTT": zero, q−1, u32 carry boundary, wrong root/stage/modulus refusals), plus the Lean
   direct-sum checks (`oddNtt`/`oddIntt` sums, matrix row 24).
3. **Placed-and-routed timing closure on the VU47P** with the real memory plan — codex's stop/go
   gate verbatim: "a placed-and-routed single-card subset with real key sizes — not a cycle
   model" (`FHEGG-CODEX-ROUND4-RAW.md` Q2 §2).
4. **On-F2 end-to-end**: host → QDMA → HBM/URAM → PE → host, measured residue-for-residue
   bit-exact vs the CPU reference AND wall-clock vs the step-0 GPU baseline on identical inputs
   — the roadmap §3.4 exit criterion ("exact residue-for-residue whole-operation win ... with
   cold, warm, fallback, and failure behavior") applied to this unit.

**Decision output.** The stone yields one number: measured F2 NTT-multiply throughput/latency vs
the measured 6750 XT baseline, both bit-exact under the same Lean contract. That number, not a
model, decides whether key-switch/relin (stone 2) is worth RTL.

---

## 4. Honest cost, and the Zama HPU relationship

**This is a large HDL build, stated plainly.** The reference point for a *full* FHE FPGA
accelerator is the Zama HPU: an open SystemVerilog TFHE coprocessor (NTT units, modular-mul PEs,
key-switch, HBM-fed memory hierarchy, a tfhe-rs integration) that a funded company built over
years and reports ~13k PBS/s @ 350 MHz on the 7nm Alveo V80 (`FHEGG-FPGA-ACCELERATOR.md` §2.2
and its cited announcement/repo; `github.com/zama-ai/hpu_fpga` — NOT fetchable from this
session, reasoned about only through the already-cited docs).

- **Study it, do not copy it blindly — technical reasons:** the HPU is a *TFHE PBS* engine
  (torus arithmetic, blind rotation, its own parameter formats); our first stone is a *BFV
  RNS-NTT* over 36–37-bit prime moduli with root tables pinned by Lean proofs. Datapath widths,
  twiddle organization, and the memory plan all differ. What transfers is architecture-level:
  butterfly PE organization, HBM banking discipline, PBS/NTT scheduling ideas, known-answer
  vector methodology (codex's "Reuse/port" list, `FHEGG-CODEX-ROUND4-RAW.md` Q2 §2). What does
  not transfer: the bitstream, the shell, the clocks (V80 Versal vs VU47P UltraScale+ — the
  ~2× node haircut `FHEGG-FPGA-ACCELERATOR.md` §2.5 names as its largest error source).
- **License — NAMED, not verified:** I cannot read `hpu_fpga`'s LICENSE file from this session.
  Zama's open-source stack (tfhe-rs) ships BSD-3-Clause-Clear; whether hpu_fpga carries the
  same terms, and what they permit for RTL-level reuse in an AGPL-adjacent verified stack, MUST
  be read from the repo's actual license text before a single line of its SystemVerilog is
  studied for reuse rather than for architecture. Until then the HPU is a *published
  architecture reference*, nothing more.
- **Ethos:** even at full maturity the FPGA never authors constraints. The AIR stays Lean; the
  emitted descriptors stay the byte-pinned Lean artifacts (`FHEGG-SAME-OPENING-APEX.md` §3
  residual 1); the FPGA — like the GPU arena and the WGSL kernels — is a callee under the
  verified emit, held by differentials and strict interpreters (roadmap §3.5's exit criterion
  applies to it verbatim).

**Effort, order-of-magnitude (a model, labeled as one):** the first stone (one NTT unit, no
key-switch, no PBS, no relin, single card) is weeks-to-months of RTL + testbench for someone
fluent in pipelined arithmetic, PLUS the AWS shell/AFI learning curve — the largest single
engineering line item currently on the fhEgg board outside the Lean apex work. The full
crossing-appliance / PBS engine is the HPU-scale build: person-years. Renting the target is
cheap (≈$4/hr for 2 FPGAs); the cost is entirely engineering time and the opportunity cost
against the GPU levers that are already measured to have headroom.

---

## 5. Decision gates — when NOT to build this

The FPGA program stays dormant unless ALL of these fire:

1. **The GPU levers saturate first.** Chunked arena + full-pipeline residency are measured,
   named, and unfinished (`FHEGG-GPU-AMD-NUMBERS-2026-07-24.md` "two performance levers"); the
   2.7× at K=8 is a floor. If the resident GPU pipeline meets the DrEX clearing cadence, no
   FPGA.
2. **The measured (step-0) GPU NTT baseline shows the multiply is the wall** for a product that
   actually needs ct×ct multiply at rate (quadratic objectives / AMM invariants,
   `fhegg-fhe/src/bfv_mul.rs:6-9`). Today no product path is measurably NTT-bound because no
   NTT wall-clock has been measured — that absence is the point of step 0.
3. **The all-TFHE fallback matters commercially** — only then does the PBS engine (the real
   HPU-shaped build) enter scope, with `FHEGG-FPGA-ACCELERATOR.md` §2's ±3–5× sizing as the
   prior.

## 6. Out of scope of this document, named

- Any HDL, any cycle model, any FPGA measurement (none exists; none is claimed).
- The PBS/blind-rotation engine and BFV→TFHE scheme switch (fallback path;
  `FHEGG-FPGA-ACCELERATOR.md` §2 sized it; codex Round-4 §3 corrected its latency model).
- Key-switch/relinearization RTL (stone 2, gated on stone 1's number).
- Multi-FPGA fabrics (codex: distribute independent markets first, never one ciphertext across
  cards — `FHEGG-CODEX-ROUND4-RAW.md` Q2 §1).
- The STARK prover on FPGA (rejected with reasons in `FHEGG-FPGA-ACCELERATOR.md` §1: stays
  CPU/GPU).
- TEE/attestation architecture (scoped in `FHEGG-FPGA-ACCELERATOR.md` §3; unchanged).
- Verified-HDL selection (Kôika/Cava vs Hardcaml vs SpinalHDL — graded in
  `FHEGG-FPGA-ACCELERATOR.md` §4; nothing new to add until a soundness-critical datapath
  actually exists in RTL).
- Custom silicon (rung 3 of `FHEGG-FPGA-ACCELERATOR.md` §5).
