# DrEX GPU residency plan — the full clearing hot path, what is resident, what round-trips, and what turns 2.7× into a whole-clear win

*2026-07-24, lane drex-residency. READ-ONLY analysis: no clearing/GPU code was edited (the supervisor
owns `fhegg-fhe/src/gpu_arena.rs` — the chunked arena). Every measured number below is quoted from
`FHEGG-GPU-AMD-NUMBERS-2026-07-24.md` or `TESTQALOG.md`; numbers I computed FROM those rows are labeled
**derived** and are arithmetic, not measurement. Nothing here was re-benchmarked by this lane.*

---

## 1. The exact op sequence of one DrEX dark clear

The canonical composition is `fhegg-fhe/tests/dark_clearing_e2e.rs:106-372` (and the Shamir `t<n`
variant `dark_clearing_quorum_e2e.rs`): authenticated traders → threshold BFV → party MPC → attested
receipt. Per-phase, with scale and where it runs today:

| # | op | code | scale | device today |
|---|---|---|---|---|
| 0a | collective keygen (n-of-n CRP, per session) | `threshold.rs` `KeygenSession`/`ThresholdParty::join`/`KeygenCoordinator` (e2e:48-64) | O(n), amortized | host |
| 0b | ingress session | `order_ingress.rs` `OrderIngressSession` (e2e:145) | O(1) | host |
| 1a | trader-side: unary expand + SIMD encode + encrypt under collective pk + sign | `additive.rs:509-540` (`encrypt_collective_row`), `order_ingress.rs:649` (`encrypt_and_sign`) | O(N) | trader hosts (not ours) |
| 1b | coordinator ingress: strict wire parse + Ed25519 verify + book order | `order_ingress.rs:1067` (`accept`), `:1217` (`finish`); strict parse `bfv_lean.rs:391` (`from_fhe_bytes`) | **O(N)** | host |
| 2 | **THE FOLD** — demand/supply curves from N rows | `additive.rs:206-266` (`fold_rows`) → `gpu_arena.rs:250-348` (`FoldEngine::fold_pair`): `upload` :750, `fold_resident_many` :826, `download_many` :954 | **O(N) — the only N-scale compute** | **GPU-resident** (the one real resident consumer, `HANDOFF-FHEGG-CODEX-SWARM-RESULTS.md` §5); labelled CPU fallback |
| 3a | per-party mask: sample rᵢ, encrypt under collective pk | `boundary.rs:319` (`MaskedBoundaryParty::prepare`) | O(n·K) | party hosts |
| 3b | homomorphic mask-add: target + Σ Enc(rᵢ) | `boundary.rs:424-457` (`MaskedDecryptCoordinator::finish`); host fhe.rs `aggregate += &encrypted_mask` :448, with `to_fhe_bytes`/`from_bytes` round-trips both directions :440-441, :450-456 | O(n) ct-adds, 2 curves | host (fhe.rs) |
| 3c | smudged partial decrypt per party (secret share + ≥2^80 smudge) | `threshold.rs:508` (`partial_decrypt`), `MIN_SMUDGE_BITS` :88 | O(n) | party hosts — **structurally host** (secret key shares) |
| 3d | combine `c0' = c0 + Σ hᵢ` + zero-key decrypt/decode | `threshold.rs:935` (`combine`), :987 | O(n) row-adds | host |
| 3e | party-local share derivation mod t | `boundary.rs:370` (`derive_mod_t_share`) | O(n·K) | party hosts |
| 4 | **MPC crossing/argmax** — A2B, per-bucket `secure_min`, balanced oblivious argmax, reveal only (p*,V*) | model `mpc.rs:433-488` (`mpc_crossing`), `:643-687` (`secure_add`/`a2b`); distributed runtime `mpc_party.rs:2128` (`run_party`), `:2458` (`coordinate`) | O(K·b) AND gates = `K·4b + (K−1)(4b+idx)` (`mpc.rs:337-339`); rounds `(geq_rounds(b)+1)(1+⌈log₂K⌉)` (`mpc.rs:370-374`) | host + **network** (interactive Beaver openings) |
| 5 | attested receipt (bind inputs/transcript/output, committee sigs, replay guard) | `attestation.rs` (`AttestedClearingReceipt`, e2e:332-371) | O(n) sigs | host |

Extended DrEX organs beyond the classic call auction (the "clearing does more than fold" ops):

| op | code | device today |
|---|---|---|
| convex engine (private derivative/rebalance, T-iteration PDHG `x ← prox(x − τAx)`) | `convex_step.rs:246-310` (`signed_neg`/`signed_add`/`signed_scale`), `convex_engine.rs:301` (`convex_solve`); Lean-emitted plan `fhegg-fhe/src/fhir/clearing_plan.rs`; e2e `fhegg-fhe/tests/e2e_private_derivative.rs` | **CPU only — no GPU kernel** |
| ct×ct multiply (Dark-AMM invariant `x·y = k`, one wrap-guarded multiply) | `dark_amm.rs:1064-1069` (`try_swap_proposed`) → `bfv_mul.rs:156` (`MulEngine::multiply`), `:183` (`product_sum`) = fhe.rs `Multiplicator` | **CPU only** — GPU NTT organ exists (`bfv_ntt_gpu.rs`, `RnsNttEngine`) but is *below* full ct×ct: no RNS basis extension, no tensor assembly, no relin on device (`bfv_ntt_gpu.rs:16-19`; named in `bfv_mul.rs:33-38`) |
| plaintext-tier solver (transparent books): GPU histogram + resident PDHG | `fhegg-solver/src/gpu.rs:118` (`histogram`), `:190` (`solve_pdhg`) | GPU; measured 11.4× at N=1M on the 6750 XT (TESTQALOG:2929) — **plaintext**, cited as the shape the encrypted path should copy, not as an encrypted-path win |

Not on the additive DrEX clear path: the TFHE/PBS machinery (`tfhe_wgpu.rs`,
`tfhe_blind_rotation*_wgpu.rs`) — the crossing is output-boundary MPC, not TFHE
(`mpc.rs:1-48`); the legacy TFHE clear is the older exact-integer path.

## 2. The cost model on the measured AMD rows — and the uncomfortable derived fact

Measured (hbox RX 6750 XT, bit-exact vs CPU `bfv_lean::fold`, K=8 folds per upload,
196608 B/ct — `FHEGG-GPU-AMD-NUMBERS-2026-07-24.md`):

| N | upload | resident e2e (K=8) | CPU (K=8 folds) | res/CPU |
|---|---|---|---|---|
| 1000 | 34 ms (72%) | 47.3 ms | 126.4 ms | 2.67× |
| 4096 | 137 ms (74%) | 185 ms | 504 ms | 2.72× |
| 8192 | 282 ms (75%) | 374 ms | 990 ms | 2.65× |

**Derived** (arithmetic on those rows; per-fold GPU cost `f = (resident − upload)/8`, per-fold CPU
cost `c = CPU/8`):

| N | f (GPU/fold, non-upload) | c (CPU/fold) | K=1 e2e GPU ≈ upload+f | K=1 GPU/CPU | breakeven K* = upload/(c−f) |
|---|---|---|---|---|---|
| 1000 | ≈1.7 ms | 15.8 ms | ≈35.7 ms | **loses ≈2.3×** | ≈2.4 |
| 4096 | ≈6.0 ms | 63.0 ms | ≈143 ms | **loses ≈2.3×** | ≈2.4 |
| 8192 | ≈11.5 ms | 123.8 ms | ≈294 ms | **loses ≈2.4×** | ≈2.5 |

The production call profile today is **K=1**: one DrEX clear uploads each side's rows once and folds
them **once** (`additive.rs:238-241` → `fold_pair`, one dispatch per side, `reduction_rounds: 0` in
the one-chunk plan, `gpu_arena.rs:305-310`). The bench's K=8 amortization has **no production analog
yet**. So on discrete AMD, the GPU fold as currently driven by a single classic clear is on the
LOSING side of the measured envelope (≈2.3× slower than CPU, derived above); the measured 2.7× only
exists at ≥3 fold-scale resident ops per upload. That is the number this plan must turn: **get ≥3
fold-equivalents of on-device work per upload, or don't dispatch the GPU for that clear.**
(`FoldEngine` already labels backends explicitly — `gpu_arena.rs:152-158` — so a measured per-adapter
policy is wireable without hiding anything.)

Also load-bearing: the N-scale bytes only flow **into** the device. What comes back from phase 2 is
2 folded ciphertexts (393 KB, `download_many` gpu_arena.rs:954); everything downstream (mask-add,
open, MPC) is O(n·K) — three orders below the upload. The whole-clear residency question is therefore
NOT "avoid downloading the book" (it never comes back) but "amortize the one big upload across more
resident compute."

## 3. The residency plan — what must stay on device so the upload amortizes

Ordered by leverage, each with its blocker named:

**R1. Batch independent books per upload (the direct K>1).** Roadmap §3.4 names batching
independent books/shares. M markets clearing in one batch = one upload, M×2 fold dispatches over
disjoint ranges; M≥2 (4 sides ≈ K=4 fold-equivalents... precisely: 2M sides each folding N/M rows —
the upload is shared, so effective K scales with M) crosses the derived breakeven; the measured 2.7×
is the K=8 floor. `fold_resident_many` (gpu_arena.rs:826) already encodes several independent folds
in one compute pass — the missing piece is CAPACITY: a resident set is one buffer.
*Blocked on:* the chunked arena (supervisor, in flight) — see §4 ceiling.

**R2. Keep the folded curves resident through the mask-add.** Today `finish`
(boundary.rs:429-457) pulls the folded curve back through fhe.rs wire bytes twice
(`to_fhe_bytes`→`from_bytes` :440-441, then `to_bytes`→`from_fhe_bytes` :450-456) to do n+1
ct-adds on host. That add is exactly the RNS add `bfv_fold.wgsl` already computes; the n `Enc(rᵢ)`
are n small uploads against a curve already on device. Wins: removes the double wire re-encode of
the curve and keeps residency unbroken from fold to masked ciphertext. It is O(n), so the ms win is
small — the point is structural (residency continuity for R1's batches, where 2M curves × n masks
start to add up). *Constraint, not blocker:* the mask-add is deliberately wrap-UNgated (mod-t wrap
IS the one-time pad, boundary.rs:426-428) — the resident path must carry the `[0,t)` bound
declaration exactly as `finish` does, and `fold_resident`'s host-side bound bookkeeping
(gpu_arena.rs:22-28) must be overridden accordingly, not reused blindly.

**R3. Convex-engine residency — the native K≫1 workload.** `convex_solve`
(convex_engine.rs:301) runs T iterations of the fused map `C = tau_den·I − tau_num·A` over d
ciphertexts: T×d² scalar-scale+add ops on the SAME resident data, plus interval bookkeeping on
host scalars. This is the workload whose shape actually matches "upload once, compute many" — for
the private-derivative organ it is the whole game. *Blocked on:* **no GPU kernel exists for
scalar-mul (or fused scale-add / matvec)** — `bfv_fold.wgsl` is add-only. NAMED: a
`signed_scale`-equivalent WGSL kernel (public-constant scalar multiply per RNS lane, plus the neg)
does not exist anywhere in the tree today.

**R4. Overlap upload with compute (double-buffered streaming).** Upload is a synchronous mapped
write completing before any dispatch (`upload`, gpu_arena.rs:750-797; bench doc
gpu_resident_bench.rs:14-16). At 72-75% upload share, perfect chunk-overlap bounds resident e2e by
max(upload, compute): **derived** ceiling ≈1.35× further at K=8 (47.3→34 ms shape), converging to
compute-bound as K grows. Natural to fold into the chunked arena's chunk loop
(`fold_streaming` already iterates upload-chunk→fold-chunk, gpu_arena.rs:584-694, currently
serial). *Blocked on:* chunked-arena design (supervisor's file).

**R5. Ingress-to-mapped-buffer (minor, named for completeness).** Rows arrive as wire bytes and
are strict-parsed to host `LeanCiphertext` (`bfv_lean.rs:391`) then memcpy'd into the mapped buffer
(gpu_arena.rs:783-795). Parsing straight into the mapped region would skip one 196 KB/ct host
copy. The one-shot path's killer (the pack loop, 56% — TESTQALOG 2026-07-18 gpu_saturate section)
is already gone; this is the last host copy, not a first-order cost.

**Per-adapter policy, stated once:** on the persvati iGPU the upload is shared-memory-cheap and
the net is the same ≈2.7× today; the breakeven-K argument is discrete-AMD-specific. Keep the
dispatch decision measured per adapter (FoldCapacity/backend are already reported,
additive.rs:145-159), never assumed.

## 4. The honest blocker list

**Ops with NO GPU kernel today (in dispatch-priority order):**
1. Public-scalar multiply / fused scale-add over RNS rows (convex engine, R3) — nothing in
   `fhegg-fhe/src/shaders/` computes it; `bfv_fold.wgsl` adds only.
2. Full ct×ct multiply — the NTT organ is real and bit-exact (`bfv_ntt_gpu.rs`) but RNS basis
   extension (`Scaler`), tensor assembly, and relinearization are host/fhe.rs only
   (`bfv_mul.rs:33-38` names this; `bfv_ntt_gpu.rs:16-19` scopes itself below full BFV multiply).
3. Ed25519 batch verification at ingress (O(N) host; not measured as a bottleneck — named, not
   sized).

**Structural host round-trips — protocol, not kernel gaps (GPU work cannot remove them):**
- **The crossing forces the exit from BFV by design.** Additive homomorphism has no comparison
  (`additive.rs:29-36`); the curves leave the ciphertext domain only as one-time-padded threshold
  openings (`boundary.rs`), and the argmax runs as an interactive Beaver-triple MPC across parties
  (`mpc_party.rs:2128,2458`) — latency-bound (rounds = `(geq_rounds(b)+1)(1+⌈log₂K⌉)`,
  `mpc.rs:370-374`; e.g. b=16, K=4096 → 221 network rounds), not compute-bound. A GPU on the
  coordinator is irrelevant to it. What residency CAN do is deliver the masked ciphertext without
  breaking residency until the last possible op (R2).
- **Partial decrypt lives on other machines.** Each party's smudged share needs its secret key
  share (`threshold.rs:508`); in deployment those are separate processes/hosts. The masked
  ciphertext download (2 cts/curve) is irreducible and cheap.

**The buffer-cap N ceiling (what the supervisor's chunked arena addresses):**
- Per-binding cap = `min(max_buffer_size, max_storage_buffer_binding_size)`
  (gpu_arena.rs:374-376) = 2^31 B on both AMD boxes → ⌊2^31/196608⌋ = **10922 cts per
  chunk/binding** (`capacity_from_limits`, gpu_arena.rs:437-458). A raw `upload` past it panics
  with a named message (gpu_arena.rs:771-775).
- `fold_streaming` already processes arbitrary N through bounded upload-chunks with on-device
  recursive reduction (gpu_arena.rs:584-694) — large-N *single folds* are not blocked. What IS
  capped is a **resident set**: `ResidentHandle` is one pool buffer (gpu_arena.rs:117-131), so no
  data set >10922 cts can STAY on device across multiple ops — exactly what R1/R3/R4 need. That is
  the `GpuResidentArenaChunking` residual the AMD doc names.
- Above the binding cap sits VRAM: 12 GB on the 6750 XT → ≈61k cts fully resident
  (**derived**: 12·2^30/196608); beyond that only streamed amortization exists. The N=1M "histogram
  regime" 11.4× (TESTQALOG:2929) is a *plaintext-solver* measurement (`fhegg-solver/src/gpu.rs`),
  not an encrypted-fold result — for the encrypted path at N=1M (196 GB of rows) only chunk-streamed
  residency is physically possible on this hardware.

**Gates that must survive any residency change (fail-closed inventory):**
- Wrap gate: resident folds cannot gate at fold time; the summed `plain_bound` rides host-side in
  u128 and bites downstream (gpu_arena.rs:22-28) — R1's batched books must keep per-book bounds
  separate (`ResidentHandle.bounds` is already per-ciphertext, gpu_arena.rs:128-130).
- Shape pin: the fold shader accepts exactly `FOLD_MODULI` (gpu_arena.rs:460-465); everything else
  is a labelled CPU fallback, never a silent one (`FoldBackend`, gpu_arena.rs:152-158).
- Bit-exactness: every resident result must stay byte-equal to `bfv_lean::fold`
  (bfv_lean.rs:558-565) — the parity discipline the bench enforces (gpu_resident_bench.rs:22-26).

## 5. What this plan does NOT claim

- No whole-clear GPU win exists today; none is claimed. The measured 2.7× is a K=8 fold-only
  envelope; the classic single clear currently derives to a ≈2.3× GPU *loss* on discrete AMD (§2).
- The K=1 derivation and breakeven K*≈2.4-2.5 are arithmetic on measured rows, not new
  measurements; the chunk-overlap ceiling (R4) and the 61k-ct VRAM ceiling are likewise derived.
  §3.4's exit criterion (release-mode hbox, residue-for-residue whole-operation, cold/warm/
  fallback/failure) has not been run for any of R1-R5.
- Nothing here verifies security properties; residency changes phases 2-3b only and must not move
  any secret-key or smudge operation onto a coordinator device (§4 structural list).
