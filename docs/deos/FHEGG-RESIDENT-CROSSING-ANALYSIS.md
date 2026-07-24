# fhEgg resident crossing — can the crossing/argmax compose resident with the fold, or does it round-trip?

*2026-07-24 pm, lane resident-crossing. READ-ONLY analysis (no gpu_arena/shader/clearing code edited)
plus one real measurement run of the EXISTING bench on this box. Every claim cites file:line, a
measured number, or is labeled **derived** (arithmetic on measured rows). Companions:
`FHEGG-GPU-AMD-NUMBERS-2026-07-24.md` (the AMD authority rows), `DREX-GPU-RESIDENCY-PLAN.md` (R1-R5).*

---

## 0. The one-line answer

**There are two different "crossings" and they have opposite answers.** The PLAINTEXT-tier crossing
(transparent books, `fhegg-solver`) can compose fully resident with the histogram fold on the same
device buffers — the kernel just doesn't exist yet, and it is straightforwardly wgsl-shaped. The
ENCRYPTED-path crossing (the DrEX dark clear) can NEVER compose resident: the exit from the
ciphertext domain is the protocol itself (masked threshold decrypt across n parties), not a missing
kernel. The "fold output stays on device → crossing reads it resident → only (p\*,V\*) downloads"
shape is real and buildable for the plaintext tier only; for the encrypted path the last possible
resident op is the mask-add (R2), after which 2 masked ciphertexts (393 KB) must leave the device
by design.

## 1. Is the crossing a GPU kernel today? (question 1)

**Encrypted path: no — it is CPU + network MPC, and structurally so.**

- The crossing is `mpc_crossing` (`fhegg-fhe/src/mpc.rs:433-488`): per-bucket
  `secure_min(D[p],S[p])` (`mpc.rs:302-322`) + a balanced oblivious argmax tournament
  (`mpc.rs:454-475`), over GF(2) boolean secret shares with Beaver-triple AND gates
  (`and_gate`, `mpc.rs:213-226`). One-process PoC in that file; the distributed runtime is
  `run_party` (`mpc_party.rs:2128`) and `coordinate` (`mpc_party.rs:2458`), whose online phase
  opens every Beaver gate over party channels — an interactive network protocol, not a dispatch.
- Its cost is LATENCY, not compute: modeled rounds `(geq_rounds(b)+1)·(1+⌈log₂K⌉)`
  (`mpc.rs:370-374`) — e.g. b=16, K=4096 → 221 network rounds; the per-round local work is XORs
  over n-length bit vectors (`mpc.rs:182-205`). A GPU on any party or the coordinator is
  irrelevant to this phase.
- The only encrypted GPU comparison in the tree is the TFHE tier:
  `fhegg-fhe/src/shaders/torus_scalar_gt_chain.wgsl` (driven by `tfhe_blind_rotation_ntt_wgpu.rs`)
  — the PBS-class exact-integer path the additive fold was BUILT to escape (`additive.rs:1-27`:
  carry propagation is PBS-class, the additive fold is ~10^5× cheaper). It is explicitly not on
  the additive DrEX path (`mpc.rs:1-48`). A "resident encrypted crossing" via TFHE would be a
  return to the abandoned cost model, not a win.

**Plaintext tier: the FOLD is a GPU kernel; the crossing is CPU after a K-bucket readback.**

- Fold = `histogram` (`fhegg-solver/src/gpu.rs:118-183`): u32 atomic scatter into K buckets.
- The histogram is then read back in full (`gpu.rs:181`, `read_back(&buf_hist, k*4)`) and the
  crossing runs on host: `scan_curves` (`fhegg-solver/src/clearing.rs:143-160` — suffix scan for
  demand, prefix scan for supply) + `crossing` (`clearing.rs:165-179` — per-bucket `min`, argmax,
  ties to lowest index). The bench states the composition outright: "GPU: histogram the fold on
  device, scan+cross on CPU" (`fhegg-solver/src/bin/bench.rs:77`, calls at `:89-96`).
- So the measured 11.4× at N=1M (TESTQALOG:2929, hbox 6750 XT, 38.9→3.4 ms) is histogram-kernel
  time INCLUDING the per-call dispatch+readback (`bench.rs:118`) — the crossing itself was never
  on the GPU anywhere.

## 2. What a RESIDENT crossing kernel needs (question 2) — and yes, it is wgsl-shaped

The arithmetic, exactly as the CPU reference computes it (`clearing.rs:143-179`):

1. `D[j] = Σ_{i≥j} bid_hist[i]` — a suffix scan over K u32/u64 values;
2. `S[j] = Σ_{i≤j} ask_hist[i]` — a prefix scan;
3. `v[j] = min(D[j], S[j])` — elementwise;
4. `(p*, V*) = argmax_j v[j]`, ties to the LOWEST j — a max-reduction over (value, index) pairs
   whose combine keeps the left operand on `≥` (the exact associative rule the oblivious MPC
   tournament already uses, `mpc.rs:459-474`, so the tie semantics are already pinned by tests on
   both sides).

Every op is integer add/compare/min plus two scans and one reduction — standard workgroup-shared
-memory material. At the deployed grid sizes (K=100/1000 in the bench, K ≤ 4096 in the MPC round
ledger) the WHOLE thing fits ONE workgroup: a 256-thread Hillis-Steele/Blelchel scan over K
elements in shared memory, the min, and a log₂K tournament, in a single dispatch of a few µs. No
atomics beyond the histogram's existing ones; no new buffer formats.

**The composition is already structurally admitted by the existing buffers:** `buf_hist` is
created `STORAGE | COPY_SRC | COPY_DST` (`storage_rw`, `gpu.rs:78-92`, used at `:121`), so a
second pipeline can bind the SAME buffer read-only with zero copies. Output: one 3-u32 buffer
`(crossed, p*, V*)` — an 8-12 byte download replacing today's 2×K×4-byte readback + host scan.

**Named non-existence (nothing faked):** no scan/min/argmax wgsl kernel exists anywhere in the
tree today. Shader inventory (`fhegg-fhe/src/shaders/`): `bfv_fold.wgsl` (add-only), `bfv_ntt.wgsl`,
`private_book_signed_dot.wgsl`, and the seven `torus_*` TFHE shaders; `fhegg-solver/src/gpu.rs`
contains only the histogram and PDHG pipelines. The resident crossing kernel is a TO-BUILD
(~100 lines of wgsl + one pipeline + one bind group in `fhegg-solver/src/gpu.rs`, which this lane
does not own and did not edit).

Also worth copying from the histogram path's OWN defect list: `histogram` re-creates its shader
module and compute pipeline on EVERY call (`gpu.rs:136-151`) and runs one full submit + map-wait
per side (`gpu.rs:94-110`). A resident clearing pass (pipeline created once, both histograms +
scan + cross in one submission) removes 2 pipeline creations, 1 of 2 submits, and both K-vector
readbacks per book.

## 3. The exact residency composition (question 3), split by tier

### 3a. Plaintext tier — the composition that EXISTS to be built

```
upload limits/qtys (bids, asks)            [N·8 B total — 8 MB at N=1M]
  → histogram(bids), histogram(asks)       [existing kernel, buffers stay STORAGE]
  → clearing_cross kernel (scan+min+argmax) [NEW — reads buf_hist resident]
  → download (crossed, p*, V*)             [8-12 B]
```

One pipeline set, one submission, one map-wait; batches M books by binding M histogram pairs.
This is the true "fold→crossing resident, only (p\*,V\*) downloads" shape — available ONLY here.

### 3b. Encrypted path — the composition that is FORBIDDEN by protocol, with the honest maximum

The additive-BFV curves cannot be compared on device: additive homomorphism has no comparison
(`additive.rs:29-36`), and decryption needs secret-key shares that live on OTHER machines
(`threshold.rs:508`; the no-viewer property is the product). The honest maximal resident chain:

```
upload N order rows (196608 B/ct)                      [the dominant cost, 72-75% measured]
  → fold_pair: fold_resident_many, outputs STORAGE|COPY_SRC (gpu_arena.rs:850; composable
    "fold-of-folds or downloaded later" by design, gpu_arena.rs:815-817)
  → [R2, buildable] mask-add resident: n small Enc(rᵢ) uploads + the same RNS add as
    bfv_fold.wgsl, keeping the deliberately-ungated [0,t) mod-t pad (boundary.rs:426-428).
    TODAY this op instead breaks residency on host BOTH ways: finish() re-parses the folded
    curve through wire bytes (Ciphertext::from_bytes(to_fhe_bytes) boundary.rs:439-448, then
    to_bytes→from_fhe_bytes :450-456)
  → download 2 MASKED ciphertexts (393 KB — download/download_many, gpu_arena.rs:944/:954)
  → [protocol, off-device forever] n parties partial-decrypt (threshold.rs:508), combine
    (threshold.rs:935), derive mod-t shares (boundary.rs:370), interactive Beaver crossing
    (mpc_party.rs:2458 gate loop; 221 rounds at b=16/K=4096)
  → (p*, V*) appear at the PARTIES, not on any device
```

"Only (p\*,V\*) downloads" is unreachable here — (p\*,V\*) is jointly computed across parties;
the coordinator device computing it would BE the no-viewer violation. What downloads is already
minimal (2 masked cts); the encrypted GPU win is therefore exactly what the residency plan says:
amortize the one big upload over more resident COMPUTE (R1 batched books, R3 convex, ct×ct
multiply) — never fold→crossing fusion.

### 3c. The load-bearing derived fact connecting the two measured findings

Why does the plaintext fold+crossing WIN one-shot (11.4× at N=1M) while the encrypted fold LOSES
one-shot (0.22-0.33×)? **Bytes-per-row**: a plaintext order uploads 8 B; an encrypted order row
uploads 196608 B — 24576× more bytes for the same one logical add (derived from the two benches'
input formats, `bench.rs:79-88` vs `FHEGG-GPU-AMD-NUMBERS` 196608 B/ct). The plaintext pass is
compute/atomic-bound after a trivial upload; the encrypted pass is a PCIe stream with one add per
196 KB. Same hardware, same "single clear" shape, opposite verdicts — arithmetic intensity, not
"the crossing is magic".

## 4. Measurement (real, run today on this box — labeled; AMD rows remain the deploy authority)

`cargo build --release -p fhegg-solver --bin fhegg-bench` → exit 0; ran `./target/release/fhegg-bench`
(clearing section; full output `scratchpad/fhegg_bench_mac.txt`). **Apple M2 Max, Metal** — NOT the
deploy hardware; quoted to size the round-trip overhead the resident composition removes, not to
re-litigate the AMD verdict:

| N | K | CPU (fold+scan+cross+allocate) | GPU-hist + CPU scan/cross | note |
|---|---|---|---|---|
| 100 | 100 | 1.71 µs | 5539 µs | GPU floor is fixed |
| 1000 | 1000 | 13.08 µs | 5723 µs | " |
| 10000 | 1000 | 196.08 µs | 5536 µs | " |
| 100000 | 1000 | 3.13 ms | 5.93 ms | GPU still loses |
| 1000000 | 1000 | 32.14 ms | 7.01 ms | **GPU 4.6×** |

- The ~5.5 ms floor, flat from N=100 to N=10⁴, is pure per-call composition overhead: 2× (pipeline
  creation + submit + K-vector map-wait readback) (`gpu.rs:136-151`, `:94-110`, `:181`). That floor —
  not the 4 KB of histogram bytes — is what a resident crossing pass deletes; it is also why small-N
  books can never win under the current per-call shape on any adapter.
- Honesty notes: biggest-book CPU rows include `allocate` (`bench.rs:128`) while the GPU path does
  hist+scan+cross only — the N=1M ratio is slightly flattered (allocate is O(N)); small-table rows
  are best-of-50, biggest-book rows single-shot (`bench.rs:69`, `:126-149`). The hbox authority
  numbers for this same bench: N=1M 38.9→3.4 ms (11.4×), N=100k 3.56→1.86 ms (TESTQALOG:2929).
- NOT measured (does not exist to measure): the resident crossing kernel itself, and any batched
  M-book resident clear. No number is claimed for them.

## 5. What to build, in dispatch order (named, none started here)

1. **`clearing_cross` wgsl kernel + single-submission clearing pass** (plaintext tier,
   `fhegg-solver/src/gpu.rs` owner): scan+min+argmax reading the resident histograms; pipeline
   cached across calls; (crossed, p\*, V\*) readback. Unblocks the M-book batched clear and kills
   the fixed per-call floor. Exit criterion per roadmap discipline: release-mode hbox, bit-exact
   vs `clearing::clear` including tie-to-lowest witnesses (`mpc.rs` tests carry the tie vectors).
2. **R2 resident mask-add** (encrypted, supervisor's arena file): the only remaining resident
   extension on the dark path; must carry the `[0,t)` declaration, not the fold's wrap gate.
3. **Nothing else crossing-shaped for the encrypted path** — further GPU leverage there is R1/R3/
   ct×ct per `DREX-GPU-RESIDENCY-PLAN.md`, and the MPC online phase stays a network protocol.

## 6. What this analysis does NOT claim

- No GPU crossing win is claimed anywhere — the kernel does not exist; only the current
  composition's overhead was measured (§4) and the AMD fold verdicts are quoted, not extended.
- The Metal rows are not deploy numbers; the 6750 XT/iGPU rows in `FHEGG-GPU-AMD-NUMBERS` govern.
- Nothing here changes the security boundary: the encrypted path's host/network round-trip at the
  crossing is the no-viewer construction itself, and every residency statement above leaves the
  masked-decrypt/MPC protocol untouched.
