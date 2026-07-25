# fhEgg GPU-multiply integration — the build plan for throughput on the dark path

*Written 2026-07-24. Turns the #1 perf leap from a vague "wire the GPU multiply" into a concrete, validated
build. Grounded in this session's measurements (`FHEGG-GPU-ARCHITECTURE-RECONSIDERED.md`) and the current code
structure. The running dark halls (Oracle Pit, Dark Pool) price/verify via a ct×ct multiply on CPU; this is
how to make that multiply run on the GPU where it measured 5.13×/10× batched.*

## 0. The measured motivation

The BFV ct×ct multiply is the op the Oracle Pit and Dark Pool spend their time on. Measured, bit-exact, on the
real hardware: the poly multiply (forward NTT + pointwise + inverse NTT) that the ct×ct is built from wins
**iGPU 3.35× / 6750 XT 5.13× / Metal ~10×** at batch (crossover at batch 4–16). The fold loses; the multiply
wins. So GPU throughput for the dark market path = GPU the batched multiply.

## 1. The exact gap (why it isn't already wired)

- `bfv_mul::MulEngine::multiply` calls `self.mult.multiply(&a.ct, &b.ct)` — **fhe.rs's `Multiplicator`**, which
  does the FULL BFV ct×ct (the degree-2 tensor `(c0·c0, c0·c1+c1·c0, c1·c1)` + relinearization back to
  degree-1) **on CPU, as an external black box**. We cannot route its internal poly muls to the GPU without
  forking fhe.rs.
- `bfv_ntt_gpu::{multiply, multiply_batch}` is a **poly** multiply over `RnsPoly` (negacyclic, NTT-based) —
  exactly the primitive the tensor + relin are made of, and the thing that MEASURES the win. But it is not a
  BFV ct×ct.
- There is **no GPU BFV ct×ct** in the tree today (grep-confirmed). So the build is a from-scratch,
  Dregg-owned GPU BFV multiply on top of the measured `bfv_ntt_gpu` poly multiply.

## 2. The build — a Dregg GPU BFV ct×ct (`bfv_gpu_mul`)

A new module (Lean-authored where it's a relation; Rust where it's the crypto datapath calling `bfv_ntt_gpu`):

1. **Bridge.** Parse the two operand ciphertexts into their component `RnsPoly`s (fhe.rs `Ciphertext` → the
   `c0, c1` polynomials in RNS; the `LeanCiphertext::from_fhe_bytes` path already crosses this boundary — reuse
   it, extend to expose the raw component polys).
2. **Tensor on GPU.** The degree-2 product needs three poly muls: `d0 = c0a·c0b`, `d1 = c0a·c1b + c1a·c0b`,
   `d2 = c1a·c1b`. Batch them: one `bfv_ntt_gpu::multiply_batch` over `[c0a, c0a, c1a, c1a]×[c0b, c1b, c0b, c1b]`
   (4 poly muls; d1 = the two cross terms summed). Across K markets → `4K` poly muls in ONE `multiply_batch` →
   the measured batch win.
3. **Relinearize on GPU.** `d2` (the degree-2 term) is relinearized with the relin key: RNS-decompose `d2` and
   multiply each limb by the corresponding relin-key polys — more poly muls, all batchable through
   `multiply_batch`. (For the THRESHOLD/dark path, the relin key is the n-of-n `generate_relinearization_key`
   output — same key, GPU-accelerated application.)
4. **Assemble + reduce.** Combine `d0 + relin(d2)` and `d1` into the degree-1 product ciphertext, back across
   the bridge to the `LeanCiphertext`/fhe.rs form the threshold decrypt consumes.

## 3. Validation (the discipline this whole session runs on)

BIT-EXACT differential vs `bfv_mul::MulEngine::multiply` (the fhe.rs Multiplicator), exactly like
`bfv_mul_oracle`: the GPU product must decrypt to the same value as the CPU product for random operands, at
the deployed params. A single mismatch is RED. The Lean anchor is `Bfv.Mul.mul_relin_decrypts_exact` (the
relation the emitted GPU datapath must refine); the AIR/relation stays Lean-authored, the GPU is a datapath
that calls it — per the ember rule.

## 4. Expected win + honest caveats

- **Win:** the ct×ct is dominated by the poly muls (the tensor's 4 + the relin's ~2·decomp-levels), all of
  which are the op that wins 3.35×–10× batched. Batched across markets (SIMD already packs slots; batch packs
  markets), the whole dark-market pricing/verification pass rides the measured win. Size the market batch to
  the adapter cache (iGPU peaks ~batch 1024; the batch-to-cache lever, measured).
- **Caveats, named:** (a) the RNS↔fhe.rs conversion has overhead — keep operands RESIDENT across the tensor +
  relin (one upload, many poly muls) so it amortizes, exactly like the resident-fold lesson; (b) the relin key
  RNS decomposition adds poly muls — count them, they are all batchable; (c) at batch 1 the multiply LOSES
  (launch overhead) — this is a BATCHED-throughput win, never a single-op win; (d) this is a real from-scratch
  BFV multiply — the effort is in the tensor+relin bookkeeping, not the poly mul (which exists and is measured).

## 5. Why this is the right next perf build

The dark halls RUN (house-blind, guarded) but on CPU. This is the single change that makes the confidential
market path fast on the deployed AMD hardware — the mandate's "as-good-as-possible performance thru DrEX on
the hbox AMD GPU," made concrete: a batched, resident, bit-exact GPU BFV multiply feeding the dark pricing
pass. It is codex's `bfv_ntt_gpu` kernel turf to build; this spec is the plan + the measured evidence + the
validation gate.
