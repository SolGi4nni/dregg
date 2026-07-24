# fhEgg — session capstone: what was proved/measured, and the prioritized next builds

*Decision-grade summary of the 2026-07-24 autonomous session. Everything below is a committed artifact
(`lake env lean`-verified proof, or a bit-exact wall-clock measurement) — no aspiration. This is the map for
whoever (codex or the next session) picks up the frontier.*

## 1. What is now established (measured or proved)

**Theory — the same-opening apex (Tier-0 keystone codex named as unclosed): a 9-file kernel-clean Lean family.**
Gap-theorem → sound+complete gadget → decrypt uniqueness → polynomial lift → polynomial master soundness →
EMITTED descriptor that discharges it → collective (no-single-viewer) opening, made TWO-SIDED (quorum
necessity: any n−1 cannot decrypt; hiding: any n−1 learn nothing) → RNS-polynomial collective lift. Every
level has a biting failing-side; the emit avoids a mod-p wrap-forgery via an exact base-2¹² limb system.
`FHEGG-SAME-OPENING-APEX.md` indexes it.

**Performance — the fold/multiply GPU picture, measured on the real AMD hardware + Metal, bit-exact:**
- the FOLD **loses** on GPU (memory-bound, 1 add/coeff): hbox 6750 XT 0.22–0.33×, persvati iGPU ~0.34×.
- the NTT **wins** (compute-bound): iGPU up to 2.05×, Metal up to 5.56×, crossover at batch 16.
- the **full multiply** (the convex/dark-AMM op) **wins big**: **iGPU up to 3.35×, Metal ~10×**, crossover at
  batch 4–16, batch-scaling. The correction that matters: *GPU the batched multiply, not the fold.*
- the batch lever is hardware-bounded (iGPU multiply peaks batch 1024; NTT batch 256) — size the market batch
  to the adapter's cache. `FHEGG-GPU-ARCHITECTURE-RECONSIDERED.md` + `FHEGG-GPU-AMD-NUMBERS-2026-07-24.md`.

**Product — the honest DrEX tier map:** `DREX-TIER-STATUS-2026-07-24.md` — the CLEAR flagship
list→clear→settle is BROKEN (prove-shielded is structurally absent for any real order: no UI book matches the
fixed ring3/market4 descriptors); SHIELDED mechanism-route LIVE for peers; DARK is a SEAM. The crossing is
CPU+MPC (`FHEGG-RESIDENT-CROSSING-ANALYSIS.md`), so GPU-residency is a clear-tier lever, not dark.

**FPGA:** `FHEGG-FPGA-SCOPE.md` — honest AWS F2/zama-hpu_fpga scoping; the FPGA targets the compute-bound NTT
(not the memory-bound fold, not more bandwidth than the 6750 XT); AIR stays Lean, FPGA is a datapath.

## 2. The prioritized next builds (evidence-derived)

1. **Wire the batched GPU multiply into the multiply consumers** (dark-AMM; future convex-with-multiplication).
   Evidence: the multiply wins ~10×/3.35× at batch. The op exists (`bfv_ntt_gpu::multiply_batch`); the lever is
   feeding it batched work and keeping it resident. HIGHEST perf ROI. (Touches codex's NTT area — coordinate.)
2. **Measure the TFHE blind-rotation (PBS bootstrap) crossover** — the dark-tier bombshell. If the bootstrap
   wins on GPU like the BFV multiply does, the dark oblivious-argmax crossing gets an order of magnitude
   faster, changing the dark-tier feasibility. BLOCKED today: needs `--features tfhe-integer` (multi-GB build)
   and both AMD boxes are 100% disk. Do it first on a fresh box / the F2.
3. **Close the CLEAR flagship** = the runtime same-opening emitter (the apex family's remaining residual): bind
   a real order book privately without per-book descriptor leakage. The apex relation + emitted gadget are
   the foundation; the runtime/twin emitter is the build. This unblocks a working DrEX clear tier (and its UX).
4. **NTT kernel tuning** (radix-4 butterflies, shared-memory twiddles) + **fusion** (forward→pointwise→inverse
   resident) — push the 3.35×/10× higher. Codex's active area; the measurement says it is worth it.

## 3. The honest blockers (named, not hidden)

- Both AMD boxes at 100% disk (co-tenant with codex) → the heavy `tfhe-integer` crossovers (bootstrap) and the
  hbox 6750 XT numbers are infra-blocked. Need disk freed or a fresh box.
- The NTT/threshold/metatheory tree is codex's active area → Lean apex work and kernel tuning contend with its
  live builds; yield the build to codex and verify when the tree settles.
- The DARK Tier-0 product is a SEAM: same-opening is a proved relation + emitted descriptor, not wired live;
  malicious-share validity + distributed witness production remain (roadmap §3.2/§3.3).

## 4. The one-line lesson

*One honest negative measurement is not a thesis about a system.* The fold losing on GPU almost shipped as
"GPU is marginal for fhEgg" — when the operation DrEX actually spends its time on (the multiply) wins an order
of magnitude. Measure the real op, on the real hardware, before concluding.

---

## 5. Continuation (Opus 5, after disk cleanup + ember "keep pursuing visions")

- **Disk unblocked** (ember's ask): removed 297 stale build dirs → hbox 26G→255G, persvati 12G→784G free
  (codex's `breadstuffs`/`datacake` untouched). This reopened the `tfhe-integer` crossover frontier.
- **The dark-tier bombshell, MEASURED:** the TFHE bootstrap core op (external product) crosses over to GPU at
  **N=4096, the deployed degree** — persvati iGPU exact-RNS-NTT path **2.55× vs CPU**, bit-exact. So the
  dark-tier oblivious-argmax crossing CAN be GPU-accelerated at the size that matters; "house-blind AND fast"
  is a measured possibility. (hbox 6750 XT discrete number pending — expected higher.) Below N=4096 the op is
  too small (launch overhead), consistent with every kernel here.
- **§3.2 malicious-share security, now theorems** (`DarkBazaarShareValidity.lean`, 5 keystones): `ShareValid`
  (a share must be its VSS-committed contribution + safe noise); `unvalidated_shift_breaks_opening` (an
  UNvalidated share can move the message — the ZK check is necessary); `valid_shares_reconstruct_honest_key`
  (validated shares reconstruct the honest collective key `(Σsᵢ)·c1` — a malicious party bound by validity
  can only inject bounded noise, never shift the key). The same-opening apex is now **10 files**.

**Revised priority given the measurements:** the dark tier is perf-viable (bootstrap wins at deployed size)
AND theory-complete (soundness + hiding + necessity + malicious-security are theorems). The gap is the LIVE
construction — the runtime same-opening emitter + the distributed prover (§3.3) + wiring — which is codex's
circuit-prove/product turf. Two dragons: the theory + perf foundation is proved and measured on our lane; the
live wiring is codex's. When they meet, the dark clearing is real.
