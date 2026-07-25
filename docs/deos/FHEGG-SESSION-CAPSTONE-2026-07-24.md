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

---

## 6. The halls RUN — all four, oracle-validated (the tangible outcome)

After the theory + perf foundation, all four Dark Bazaar halls were driven to RUNNING, oracle-validated FHE
code (test files in `fhegg-fhe/tests/`, no `lib.rs` touch, non-colliding with codex's lanes). `cargo test -p
fhegg-fhe --test oracle_pit_pricing --test netting_vault_running --test dark_pool_invariant --test
e2e_private_derivative` → **17 passed together**:

| hall | running artifact | tests |
|---|---|---|
| **Oracle Pit** | complete tradeable quadratic prediction market: arbitrary cost matrix (pricing), marginal price (public odds over hidden positions), batched-SIMD pricing, wrap guard | 5 |
| **Netting Vault** | homomorphic multilateral netting, reveal-only-the-net; **guild scale** (8 parties, 56 hidden obligations → 8 nets), conservation holds | 3 |
| **Dark Pool** | constant-product invariant on hidden reserves; **batched** 6-pool verification (the GPU-favorable shape); unfair swaps caught | 3 |
| **Sealed Exchange** | end-to-end private derivative: collective-key encrypt → convex solve → threshold decrypt | 6 |

Each is the running witness of a proved Lean relation (OraclePitQuadratic / NettingVault / DarkAmm / the apex),
validated bit-for-bit against real fhe.rs — agreement with a real BFV library cannot be faked. Every hall's
compute rides the ct×ct multiply / additive fold that MEASURES its own GPU numbers (multiply 5.13×/10× batched).

**Net state of the vision:** proved (14 Lean files) + measured (compute-bound wins on real AMD) + RUNNING (all
four halls, 17 tests). The Dark Bazaar is no longer a design with proofs — it executes, all four corners.

**The honest remaining frontier is the directed LEAPS (each needs a strategic pick / codex-convergence):**
1. Host a hall as a LIVE product (wire a running demo into cells/receipts/finality + a UX) — codex's turf.
2. Wire the batched GPU multiply into the running multiply consumers (the fhe.rs↔RnsPoly bridge is codex's
   additive area) — turns the measured 5-10× into a running throughput win.
3. The distributed prover (§3.3) — protocol-level, real design.
4. The F2 FPGA — needs an F2 instance + HDL build; scope is written.

The proved + measured + running layer is complete on our lane; the leaps are where the two dragons converge.

---

## 7. The whole Dark Bazaar runs HOUSE-BLIND — Tier-0, no single viewer (the culmination)

Beyond the single-key demos (§6), all four halls were driven to TIER-0 DARK: priced/cleared under an n-of-n
COLLECTIVE key that NO single party — and no `n−1` coalition — can open. `cargo test -p fhegg-fhe --test
dark_netting_threshold --test dark_oracle_pit_threshold --test dark_pool_threshold --test e2e_private_derivative`
→ **10 passed**, the whole house-blind Dark Bazaar:

| hall | Tier-0 dark artifact | no-single-viewer tooth |
|---|---|---|
| **Netting Vault** | signed multilateral net under collective key (additive) | n−1 combine REFUSED |
| **Oracle Pit** | quadratic pricing under collective key + **threshold relin** (ct×ct multiply) | n−1 REFUSED |
| **Dark Pool** | constant-product invariant under collective key + threshold relin; unfair swap caught house-blind | n−1 REFUSED |
| **Sealed Exchange** | convex clearing under collective key (e2e private derivative) | n−1 REFUSED |

Each composes this session's proved theory (NettingVault / OraclePitQuadratic / DarkBazaarCollectiveOpening /
DarkBazaarQuorumNecessity) with the FROZEN threshold + threshold::relin ceremonies, and asserts the n−1
refusal — the running witness that any coalition below n cannot open any position, price, net, or reserve.

**This is the north star as running code:** "the dealer cannot see the cards, the players cannot see each
other, and every deal carries a proof" — executing, across the WHOLE Dark Bazaar, at maximum privacy. The
session's arc: proved (14 Lean files) → measured (compute-bound wins on real AMD) → running (all four halls
single-key, §6) → HOUSE-BLIND (all four halls Tier-0 dark, no single viewer, this section).

The remaining frontier is now purely the LIVE / throughput leaps: host a dark hall as a real product (wire
into cells/receipts/finality + UX, codex's turf), the GPU-multiply throughput on the dark path (the measured
5-10× multiply win, via the fhe.rs↔RnsPoly bridge), and the F2 FPGA. The proved + measured + running +
house-blind layer is complete on our lane.
