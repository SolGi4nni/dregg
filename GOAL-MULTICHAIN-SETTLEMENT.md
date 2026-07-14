<!-- ⚑ One of MANY concurrent /goal lanes — see GOALS-INDEX.md. This is the
     multichain-settlement lane ONLY. Edit only this file; never clobber another lane's.
     COORDINATION: stark-kill owns trace_rotated.rs + the AIR/rotated-proof pipeline + the
     Rung-3 fold ladder in circuit/. THIS lane owns chain/gnark (the EVM-settlement wrap),
     the bridge/light-client crates, dregg-governance's cross-chain spine, dregg-deploy. -->

# GOAL — MULTICHAIN SETTLEMENT: dregg as the trustless plug for every chain

North star: proof-carrying settlement + non-custodial proof-of-holdings governance across
Solana/EVM/Cosmos, the STARK→EVM wrap made actually-efficient, verified light-client rules
progressing toward folded (rung-3) verified light clients.

## Threads (priority; reassess as I learn)
1. **THE WRAP** (linchpin) — BN254-native-hash re-arch (docs/deos/WRAP-NATIVE-HASH-DECISION.md).
   Landed: native poseidon2_bn254 / merkle_bn254 / challenger_bn254 (measured ~61×). Next:
   MultiField challenger pack/split → Rust shrink layer (DreggOuterConfig) → Rust↔gnark transcript
   differential → residual levers (blowup↓queries @130-bit; cut w24's 452 cols; GKR-batch openings)
   → drive ~5M toward ~1-2M. Measure each step. (End-to-end apex proof blocked on the rotated-proof
   pipeline break — stark-kill's, NOT mine.)
2. **VERIFIED LC → FOLDED (rung 3)** — pilot folding ONE chain's verified verification as a
   recursion-foldable CellProgram leaf via DECO machinery (VERIFIED-LIGHTCLIENT-FOLD-PATH.md),
   cheapest-crypto-first. Upgrade a chain's no-forgery toward the DecoUnforgeable game-reduction.
3. **CROSS-CHAIN COMPLETION** — gov-spine residuals (EVM/Cosmos edge conversions; u128→u64
   fail-closed narrow; multi-network ChainId); widen sockets (post-Electra rotation dual-depth;
   Base OP-stack finality; Cosmos bisection).
4. **Opportunistic** — deploy-gate policies; workspace-vs-target consolidation (member-not-default
   for the light-client crates IF the dep graph joins cleanly — check, don't guess).

## Disciplines (these ARE the goal)
adversarial-auditor per lane · verify myself (lake/cargo/go) · commit by NAMED files · Fable
subagents model:'fable' · commits sign Opus 4.8 · honest scoping (rung-2≠rung-3; verified-RULES ≠
verified-chain) · NEVER touch trace_rotated.rs / files another terminal edits · maintained libs for
foreign crypto · HORIZONLOG every follow-up · measure before believing a lever · disjoint waves.

## Current thrust (07-12 ~3am: unblocked scope COMPLETE; pacing on circuit-prove for the wrap)
Wave 1 LAUNCHED (Fable): gnark-multifield [wrap] · eth-edge (EVM U256>u128 refuse + post-Electra
rotation) · cosmos-edge (bank decode + bisection) · gov-narrow-tag (u128→u64 fail-closed +
multi-network ChainId) — each adversarially audited. + rung-3 fold-pilot grounding scout.
Deferred: workspace consolidation (root Cargo.toml churned by other terminals — do when quiet;
edge conversions use minimal-primitive-fields at the crate edge, so they DON'T need it).

## Next 3 moves
1. Commit gov-narrow-tag (Evm→u64 widening; test compiling). Wave 1 then fully integrated.
2. Wave 2 (clean-and-mine): governance-side `from_foreign_fields` constructor (completes the
   cross-chain edge→ProvenForeignHolding wire, with cross-crate tag-consistency tests) + Base
   OP-stack finality source (eth-lightclient) + opportunistic deploy-gate/socket widening.
3. Pick up the Rust shrink layer + fold-P0 the moment circuit-prove goes quiet (currently churned).

## ⚠ Collision map (checked 07-12)
circuit-prove/ is ACTIVELY churned by stark-kill/vk-epoch (ivc_turn_chain.rs uncommitted-modified now;
many test files mid-edit). So BOTH the rung-3 fold-P0 build AND the Rust shrink-layer config
(DreggOuterConfig lives in circuit-prove/plonky3_recursion_impl.rs) are collision-BLOCKED there — defer
until quiet or coordinate. CLEAN-AND-MINE: chain/gnark, eth-lightclient, cosmos-lightclient,
dregg-governance, dregg-deploy, docs/. Drive the wrap via chain/gnark (the gnark verifier side); the
Rust shrink layer waits on circuit-prove going quiet.

## Done-log
- (init 07-12) lane adopted. Baseline green: native-hash gnark gadgets (~61×), verified-LC rules
  CR-floored, cross-chain gov spine, deploy-gate policies.
- 07-12 rung-3 fold-pilot PLAN committed (VERIFIED-LIGHTCLIENT-FOLD-PILOT.md): EVM-MPT/keccak cheapest;
  folds through deployed CarrierWitness::Custom (verified citations). Build DEFERRED (circuit-prove churn).
- 07-12 Wave 1 landed (4 Fable lanes + audits, all fail-open=false/vacuity=false):
  · gnark-multifield: BabyBear→BN254 pack/split, MEASURED 32.3× (984 vs 31,747 R1CS), fork-executed KAT. Committed.
  · cosmos-edge: bank-balance decode + bisection, real on-chain ATOM KAT. Committed.
  · eth-edge: EVM holding→foreign-fields (U256>u128 refuse) + Electra rotation. AUDIT MINOR fixed:
    FinalizedExecution made genuinely unforgeable (private fields + accessors, not just a sealed literal —
    the pub fields still allowed mutation). Committed (2 commits: lane + hardening).
  · gov-narrow-tag: u128→u64 fail-closed narrow + multi-network ChainId(Evm(u64)/Cosmos(hash)). Committed;
    fixed the lane's own stale 5-byte wire test + added the Palm(>2³²) representability test. WAVE 1 DONE.
  Audit pattern held: caught the mutation-hole in my own first seal; fixed before final commit.
- 07-12 CROSS-CHAIN WIRE done: ProvenForeignHolding::from_foreign_fields(chain, chain_tag,...) pairs the standalone
  edges' fields with the full ChainId, fail-closed on family-tag mismatch; cross-crate tags pinned. Thread-3 core DONE.
- 07-12 Wave 2: secp256k1 EVM-address owner binding COMMITTED (dregg-governance) — EVM holders now bind→vote
  (EvmOwnerBinding + HolderBinding trait; Ed25519/Solana path byte-unchanged; low-S + address-recovery verified
  myself; k256+sha3). EVM-family voting works end-to-end. Residual: Cosmos bech32/secp256k1 binding.
- 07-12 Base OP-stack finality COMMITTED (eth-lightclient): L1 finalized state → L2 output root (EIP-1186 storage
  proof, l2Outputs array + length-bounds check = the deleteL2Outputs defense) → keccak output-root preimage
  (TRIPLE-verified: OP spec + kona KAT + LIVE Base-mainnet recompute of output 12086) → L2 ERC-20 MPT. REAL-EXTERNAL
  fixture (public-node captured). 86 crate tests green. RESIDUAL named loudly: live Base uses FAULT PROOFS
  (FaultDisputeGame), not the L2OutputOracle model — not implemented. WAVE 2 DONE (secp256k1 + Base).
- 07-12 Wave 3: Cosmos secp256k1/bech32 binding COMMITTED — THE BINDING TRILOGY IS COMPLETE
  (Solana Ed25519 · EVM secp256k1-addr · Cosmos secp256k1-addr). Any holder on all 3 families binds→votes
  non-custodially. ripemd160(sha256(pubkey)) derivation KAT-pinned + verified myself; low-S 2 layers; Ed25519/EVM
  byte-unchanged. Honest: dregg-specific sign-doc, NOT ADR-036 wallet-native (named follow-up). Base-fault-proof
  grounding scout running (docs).

## ⚑ STATUS (07-12): THREAD 3 (cross-chain completion) DONE.
Edges(Sol/EVM/Cosmos)✓ · from_foreign_fields wire✓ · multi-network ChainId✓ · u128→u64 narrow✓ · binding
trilogy✓ · Base finality(L2OutputOracle)✓ · Cosmos bisection✓ · Electra rotation✓.
BLOCKED (circuit-prove churn — stark-kill's carrier flag-day): thread 1 (wrap shrink-layer) + thread 2 (rung-3
fold-P0). These are the marquee remaining value; pick up the moment circuit-prove goes quiet.
UNBLOCKED work: Base fault-proof anchor BUILD LAUNCHED (Fable, eth-lightclient) from the committed plan
(BASE-FAULT-PROOF-ANCHOR.md, live-validated type-621 AggregateVerifier) — the honest live-Base completion, 8-link
trust chain + verify_evm_storage_slot_absent (MPT exclusion), reuses verify_op_output_root. Waiting.
Other unblocked refinements: Base finalization-window, real e2e LightClientUpdate→holding chain, ADR-036 Cosmos.
Op-note: use `git commit -F` for messages containing quotes (hit a nested-double-quote break).
- 07-12 Live-Base fault-proof anchor BUILT (eth-lightclient/src/base_fault_proof.rs): 8-link type-621 trust chain,
  REAL-EXTERNAL live fixture (game 17049), 132 crate tests. FOUND + defended a real alloy-trie 0.9.5 exclusion-proof
  hole (truncated inclusion accepted as absence -> blacklist bypass); strict re-walk + pinning test. ⚑ report upstream.
  execution_timestamp added (consensus-verified airgap clock). LIVE-BASE proof-of-holdings is now REAL.
- 07-12 Real e2e ETH light-client→holding validation LAUNCHED (Fable): chain a genuine sync-committee-signed
  mainnet update all the way to a holding (the composed-chain validation the isolated KATs miss). Honest-labeling
  required (real-external vs round-trip). Waiting.
- 07-12 Real e2e ETH validation COMMITTED: GOLD result — every link real-external live mainnet data (real BLS over
  the real 512-key committee 397/512 → real Electra finality/execution branch → real WETH eth_getProof →
  ConsensusProven). 8 reject tests on real data. 142 crate tests. The ETH light client (underpins ETH+Base) is now
  empirically validated end-to-end.
- 07-12 Base fault-proof R3 CLOSED: CWIA code-hash recomputation reproduces the LIVE game code-hash byte-exactly
  (KAT-passed, verified myself); a look-alike game (same slot-0, non-CWIA bytecode) is refused. 145 crate tests.
  The live-Base fault-proof anchor is hardened to the semantics-pin level.

## ⚑⚑ MEANINGFUL UNBLOCKED SCOPE EXHAUSTED (07-12 ~3:55am).
Everything achievable WITHOUT the wrap is shipped + verified to a high standard: thread 3 complete (binding TRILOGY,
3-chain edges/wire/multi-network/narrowing), ETH light client validated E2E on REAL mainnet data, live-Base
fault-proof anchor BUILT + R3-hardened, a real alloy-trie security finding, gnark MultiField (32.3×).
ONLY high-value remaining = thread 1 (wrap shrink-layer) + thread 2 (rung-3 fold) — BLOCKED on circuit-prove
(stark-kill carrier flag-day + vk-epoch weld, both persistently active ~2h). I can't unblock it (another terminal's
work; collision risk). Marginal polish left (ADR-036 Cosmos wallet-native framing; legacy finalization-window) —
NOT forcing it. PACING purely on the wrap: re-poll circuit-prove each wakeup, SEIZE it the instant it quiets.
ember lever: coordinate/land stark-kill's flag-day to free circuit-prove, OR say to proceed despite churn (advise against).

## ⚑ CORRECTION (07-12 ~4:36am): I'd been MISREADING circuit-prove churn.
The 9 "uncommitted" circuit-prove files are ALL pre-existing STALE test files (the exact *_audit_*.rs set in the
git status at SESSION START) — NOT a terminal mid-editing. The real churn was the COMMITS (carrier flag-day,
vk-epoch weld), which have STOPPED (no commits 45min). My target src/ files (plonky3_recursion_impl.rs, ivc_turn_
chain.rs) are clean+stable. So the WRAP is more advanceable than I'd been treating it. SEIZED it on the side I
FULLY OWN (zero circuit-prove collision): the gnark VERIFIER. Native-hash VerifyFriNative lane LAUNCHED (chain/gnark)
— composes MultiFieldChallenger + merkle_bn254 in the fork-faithful order, MEASURES its constraint count vs the
emulated VerifyFri (empirical validation of the ~1-6M native premise vs ~30-70M emulated). Verifies a SYNTHETIC
native-hash FRI (real-apex verify awaits the Rust shrink layer). NEXT: if circuit-prove stays quiet, the Rust shrink
layer (DreggOuterConfig) is the disjoint parallel piece — but gnark-side first (safest, validates premise).

## ⚑ PLATEAU NOTE (07-12 ~3am): unblocked multichain work is COMPREHENSIVELY done.
Thread 3 + all its refinements shipped (edges, wire, multi-network, narrowing, binding TRILOGY, Base legacy +
LIVE fault-proof finality, Cosmos bisection, Electra rotation, + a real alloy-trie security finding). The MARQUEE
remaining value — thread 1 (wrap shrink-layer, ~5M→~1-2M) + thread 2 (rung-3 fold) — is BLOCKED on circuit-prove
(stark-kill's carrier flag-day, now 10 uncommitted files, ~90min ongoing). I CANNOT unblock it (another terminal's
active work; proceeding despite churn = collision risk, against discipline). Pacing: re-poll circuit-prove each
wakeup; seize the wrap the instant it quiets. Meanwhile: e2e-eth validation + remaining small refinements
(finalization-window, ADR-036 Cosmos, upstream the alloy-trie fix — the last is outward-facing, ember-gated).

## ⚑ LATEST (07-12 ~5am) — wrap moving on BOTH sides
- CHURN MISREAD CORRECTED: the 9 "uncommitted" circuit-prove files are pre-existing STALE tests/*_audit_*.rs (in
  the git status at session START), NOT active work. Real churn = the COMMITS, which stopped. circuit-prove/src QUIET.
- gnark NATIVE VerifyFri MEASURED + committed (ef2b2f6d1): emulated 40,938,030 → native 1,018,263 R1CS (40.2×);
  HASHING 40.7M→0.8M (51×); fold residual byte-IDENTICAL (shared friFoldRowArity2, code-guaranteed). The
  re-architecture's central hashing bet is CONFIRMED. Single-matrix scope (full ~5.2M awaits reduced-opening + shrink).
- GIT HYGIENE FIX: poseidon2_bn254*.go were UNTRACKED since session start (prior-session Exp-2); my committed gnark
  work depends on them → committed so chain/gnark builds from a clean checkout. (Watch: the shared tree has heavy
  multi-terminal churn — only ever commit MY named files.)
- Rust SHRINK LAYER (DreggOuterConfig = Poseidon2Bn254 MMCS + MultiField32Challenger) LAUNCHED (additive, circuit-prove,
  self-contained synthetic prove/verify; real-apex shrink = named residual, needs the apex-verifier AIR + the blocked
  apex pipeline). This + the gnark native VerifyFri = the wrap's two sides meeting. Waiting.
NEXT: harvest the shrink layer; if it needs the apex-verifier AIR / real apex, that's the blocked end-to-end piece.
The wrap's MEASURED + ASSEMBLED (gnark) + CONFIG (rust) are the achievable pieces; end-to-end real-apex verify awaits
the (other-terminal) apex pipeline fix.

## ⚑ WRAP BOTH SIDES BUILT (07-12 ~5:14am)
DreggOuterConfig shrink layer COMMITTED + verified (4/4: synthetic STARK round-trips; Rust perm == gnark KAT
exactly; challenger/compress agree). gnark native VerifyFri already committed+measured. The wrap's two sides
KAT-AGREE (perm/challenger/compress). One seam: gnark leaf-hash port to the Rust shifted-radix MMCS layout —
IN FLIGHT. End-to-end real-apex verify still awaits the apex-verifier AIR + a producible apex (blocked pipeline).
Achievable wrap pieces = DONE/near-done; the blocked piece is the real-apex plumbing.

## ⚑ WRAP CAPSTONE IN FLIGHT (07-12 ~8:25am)
- gnark LEAF-HASH PORT committed: the wrap's two sides now FULLY agree (permutation gold-KAT + challenger
  pack/split + compress + LEAF HASH). Real cross-side KAT (gnark == the Rust MMCS's OWN digests, incl. a genuine
  MerkleTreeMmcs::commit root; shift canary proves +1 encoding load-bearing). Verified myself, non-vacuous.
- circuit-prove is now QUIET (no src mods, no commits 3h) and the CARRIER FLAG-DAY LANDED (trace_rotated documents
  59 carriers — the old 59!=56 panic mismatch is FIXED). So a REAL APEX may be producible → end-to-end wrap reachable.
- LAUNCHED the CAPSTONE: apex-verifier AIR under DreggOuterConfig (the field-generic recursion verifier instantiated
  BN254-native) — the piece that SHRINKS a real apex into a BN254-native STARK that gnark's VerifyFriNative verifies.
  Adaptive: goes end-to-end if a real apex is producible; else validates the shrink mechanism on a synthetic inner proof.
- Probing the real-apex production myself in parallel (the deployed_tooth tests are #[ignore]'d; running --ignored).
NEXT: if the apex proves → shrink it BN254-native → (stretch) export its FRI data to gnark = THE WRAP END-TO-END.

## ⚑⚑ APEX PIPELINE FIXED (07-12 ~8:33am) — wrap end-to-end reachable
Verified myself: the #[ignore]d real-apex tests PASS (2/2, 344s, no panic) — the carrier flag-day fixed the
59!=56 mismatch. A real ir2_leaf_wrap apex IS producible (~5-6min). Capstone lane (apex-verifier AIR under
DreggOuterConfig) redirected to the REAL ladder: real apex → BN254-native shrink → (stretch) gnark VerifyFriNative.
THREAD 2 (rung-3 fold-P0) also unblocked (same pipeline) — QUEUED after the capstone (both are heavy circuit-prove
lanes; two concurrent cargo test -p dregg-circuit-prove thrash the build lock, so SEQUENCE not parallelize).
NEXT: harvest capstone (verify "real apex shrunk" myself — strong claim); then launch fold-P0; then the gnark
end-to-end fixture (gnark verifies a real dregg apex's shrink proof) if the capstone leaves it as the increment.

## ⚑ CAPSTONE LANDED (both threads) — VERIFYING before commit (07-12 ~9:05am)
The capstone lane did BOTH marquee threads in one: (1) apex_shrink.rs + apex_shrink_bn254_tooth.rs = THREAD 1
(a REAL 2-turn fold → apex → shrink under DreggOuterConfig → verify; #[ignore]d, ~minutes); (2) mpt_holding_leaf.rs
= THREAD 2 fold-P0 (the EVM-MPT holding-commitment CellProgram leaf via CarrierWitness::Custom). circuit-prove
cargo check GREEN.
⚠ RISK: it MODIFIED SHARED fold machinery — custom_leaf_adapter.rs +184/-95 (REWROTE incircuit_custom_pi_commitment,
the PI-commitment sponge the DEPLOYED DECO/custom-leaf teeth fold through), custom_proof_bind.rs +55,
joint_turn_recursive.rs +15. A commitment-VALUE change would shift VKs → break deployed teeth (the "shared-struct
reds the umbrella" hazard). NOT COMMITTING until: (a) the REAL shrink test passes (--ignored, running now — the
headline), AND (b) a REGRESSION check: the deployed custom-leaf teeth + recursion_vk_determinism still pass with the
modified adapter. Verify BOTH myself before any commit. (Sequenced — both heavy circuit-prove, one build lock.)

## ⚑⚑⚑ WRAP CONFIRMED (07-12 ~9:20am): REAL apex shrunk BN254-native + verified (Rust side, 1333s).
apex fold 258s/399KB → shrink prove 1076s → shrink proof 263KB → verify 68ms. The wrap works end-to-end (Rust).
Shrink prove ~18min = red-team cost (2^15-row shrink tables) → optimization target, not blocker. FINAL: gnark
VerifyFriNative verifies the exported real shrink proof = wrap FULLY end-to-end. Launched.

## ⚑ Perf lane (07-12): shrink-prover optimization (ember asked). Ranked: (1) blowup rebalance [SWEEP LAUNCHED —
config-only, the measurement inverted the optimal: native-hash made queries cheap so lower-blowup/more-queries is
now faster prove], (2) forge not laptop (free ~3-5×), (3) GPU/ICICLE (10-100× on NTT+Poseidon2+Merkle — the deploy-
a-GPU answer), (4) shrink the apex-verifier AIR trace (decision doc's 3 levers), (5) folding-recursion frontier.
Two lanes running: gnark-verifies-real-shrink-proof (final wrap increment) + the blowup sweep.

## ⚑ PERF + PLATFORM EPOCH (07-12 ~9:40am) — attacking the ~18min shrink prove
Wrap CONFIRMED end-to-end (Rust): real apex shrunk BN254-native + verified. Now optimizing:
- BLOWUP REBALANCE (ember's Q): the measurement that proved the wrap inverted the optimal (native-hash made
  queries cheap). GNARK SIDE MEASURED: blowup 64→4 grows gnark verify only 1.0M→1.9M R1CS (<<5M ceiling), all
  130-bit. Rust shrink-PROVE-time sweep RUNNING (does lower blowup slash 18min? the load-bearing half). Committed harness.
- CROSS-PLATFORM PROVER (ember: hbox is AMD, want Apple Silicon too, maybe NOT ICICLE): redirected the GPU lane to
  a cross-platform STRATEGY (ICICLE CUDA-first/AMD-weak → wrong for us; compare Futhark [AMD/NVIDIA, no Metal] vs
  wgpu/WGSL [Rust-native, Apple+AMD+NVIDIA one source] vs HIP vs raw). KEY INSIGHT: BabyBear inner proving (31-bit,
  simple kernels) = CLIENT-SIDE proving on Apple Silicon = dregg's non-custodial soul; BN254 shrink (256-bit) =
  server. My lean: wgpu/WGSL BabyBear-first PoC (behind Plonky3's DFT/hash traits). Strategy doc in flight.
- AIR REDUCTION analysis running (shrink the 2^15-row apex-verifier AIR tables; levers tagged mine vs stark-kill's apex config).
- FOLDING RECURSION primer WRITTEN + committed (docs/deos/FOLDING-RECURSION-PRIMER.md): the crux for dregg = curve-
  folding is NOT PQ (breaks dregg's quantum-safe thesis) + wants a big field (re-imports the emulation tax). Verdict:
  optimize hash-based wrap NOW (PQ-preserving); WATCH LatticeFold (PQ folding) as the future; not a now-migration.
NEXT: harvest the Rust sweep (prove-time tradeoff → set the production shrink blowup); the cross-platform strategy
(→ green-light a wgpu BabyBear PoC for a MEASURED Apple Silicon number); AIR reduction; the gnark end-to-end.

## note (07-12 ~9:55am): AIR-reduction lane BLOCKED on the cargo lock (my sweep holds it), didn't write its doc —
re-issue fresh later with "write doc FIRST before compile checks". Lowest-priority lever; blowup+GPU are the big
ones + running. circuit-prove/src is HEAVILY churned by the sibling 74→78-PI flag-day right now (custom_leaf_adapter,
ivc_turn_chain, joint_turn_*, dsl_leaf_adapter, carrier_pin_twin, custom_binding_deployed_tooth all modified) — my
committed apex_shrink/mpt_holding/dregg_outer sit in that churn; per ember commit-and-move-forward, fine. RUNNING:
Rust blowup-prove sweep (baseline phase, long), wgpu NTT efficiency PoC (measures %-of-peak-bandwidth — the answer
to ember's max-perf wariness), gnark-verify-real-shrink. APPLE SILICON wgpu = VERIFIED 107 Gmul/s bit-exact.

## ⚑⚑ BLOWUP REBALANCE WON — MEASURED ~8× faster shrink prove (07-12 ~10am)
The perf lever ember asked for, DONE on measured data. Real-apex sweep (one apex reused):
  blowup 64 (19q): prove 760s, gnark 1.02M R1CS   →  blowup 8 (38q): prove 95s (8×), gnark 1.46M
Set production shrink config OUTER_FRI_LOG_BLOWUP 6→3, NUM_QUERIES 19→38 (130-bit held). The ~12-18min
shrink is now ~1.6min BEFORE any GPU. gnark verify 1.0M→1.5M R1CS (trivial, <<5M Groth16). blowup 8
verified a real apex in the sweep = validated end-to-end. (blowup 4 panicked — config edge, deferred.)
So the wrap prover: apex fold ~4-6min + shrink ~1.6min. Next perf tiers: wgpu BabyBear GPU (NTT PoC running,
measuring %-peak-bandwidth for ember's max-perf question) + AIR-trace reduction (re-issue). Committed.

## ⚑ APPLE-SILICON PROVER ARCHITECTURE (07-12, ember's call): ALL-METAL backend, not wgpu+Metal hybrid
Decision: ONE backend per platform behind the Plonky3 trait seams (TwoAdicSubgroupDft + hasher) — NO cross-runtime
interop. Apple Silicon = an ALL-METAL backend (every kernel NTT+Poseidon2+Merkle+eval in MSL, one Metal runtime,
native ulong everywhere — simpler + native-perf across the board). AMD hbox/NVIDIA = wgpu(Vulkan)/Futhark(HIP/CUDA).
wgpu's role was (1) portability proof + (2) baseline to beat; Apple PRODUCTION goes all-Metal (drops the wgpu-for-
Poseidon2 hedge). M4 available for testing → parameterize tuning knobs (tile/threadgroup/radix/occupancy), auto-tune
or per-uarch table → "well-optimized across the Apple Silicon family since M2" (M2/M3/M4 differ in cores/bandwidth/
SIMD). Payoff = fully-GPU-resident BabyBear prover on any Apple Silicon Mac = CLIENT-SIDE proving (dregg's soul).
RUNNING: native Metal NTT lane (kernel #1 of the all-Metal backend — native ulong + threadgroup tiling + SIMD-group,
targeting 50-70% bandwidth vs wgpu's ~20%); gnark-verify-real-shrink (waiting in the build-lock line — LEAVE IT).
NEXT (autonomy, ember pre-approved): after the NTT number → full all-Metal backend (Poseidon2+Merkle) + auto-tune
knobs from the start (M4-measured not assumed). Is the M4 ssh-reachable? (ember Q pending — run the probe on both).

## ⚑ GPU BACKEND SETTLED (07-12, measured both kernel classes): PORTABLE wgpu, no native seam
NTT (bandwidth-bound) native≈wgpu tie; Poseidon2/Merkle (COMPUTE-bound, the dominant cost) native only 1.2-1.35x
(my "3x ALU win" was a microprobe artifact — Poseidon2 is 1/3 mul + 2/3 add/sub-at-equal-rate, and wgpu's in-context
mul is ~185 not 60-106). Whole-prover native seam capped 1.27x → not worth it. ONE wgpu/Vulkan+Metal backend,
auto-tune per device (split-twiddle helps both). THE REAL PRIZE: GPU offload = 38-64x over CPU (2^21 Merkle 12-15ms
GPU vs 485ms CPU) → wire the wgpu prover behind Plonky3 DFT+hash trait seams → the ~95s shrink → seconds → client-side.
NEXT (item 2, the ultimate measurement): the GPU-PROVER WIRING — TwoAdicSubgroupDft(NTT) + MMCS hasher(Poseidon2)
behind DreggOuterConfig, measure REAL end-to-end shrink prove GPU-vs-CPU on M2 Max (unified memory = no copy tax).

## ⚑⚑⚑ WRAP END-TO-END (FRI-core) ON REAL DATA — DONE (07-12 ~1:16pm)
gnark VerifyFriNative gadget verifies a REAL dregg apex's BN254-native shrink proof (fold→shrink→export→gnark-verify;
verified myself; 10 reject canaries). SCOPE FRI-core; residual = full-STARK verify → Groth16 → EVM. THE WRAP WORKS.
The multichain goal: thread 1 (wrap) core DONE end-to-end on real data; thread 2 (fold-P0 leaf) done; thread 3 done.
Perf: blowup 8x free; GPU-wiring Amdahl-capped ~2-2.5x (BN254-t3 microprobe decides). GPU value Q → ember.

## ⚑ EVM SETTLEMENT PATH (07-12, ember: keep the EVM stuff moving) — grounded + last-mile launched
STATE: gnark FRI-core verifies a REAL shrink proof ✓. fri_verifier.go's FULL verify = a documented STUB
(TODO(milestone 2): trace/quotient + per-table constraint+quotient = "multi-week assembly"). bridge/ethereum.rs:
"the crypto core NOT in this repo is the Groth16 circuit that IS the STARK verifier." DreggSettlement.sol EXISTS
(verifies a Groth16 proof over 25 lanes via IGroth16Verifier25; honest residual = the message→root leg is
OPERATOR-ATTESTED not proof-bound, a named 26th-public-input dregg-circuit obligation). chain/src/verify.rs +
bridge/ethereum.rs = the submission side (assume a Groth16 proof exists). GAP = native full-STARK verify
(constraint-eval + quotient-identity on top of VerifyFriNative's FRI-core) → Groth16 wrap → DreggSettlement VK.
LAUNCHED: the native full-STARK-verify last-mile (constraint-eval + quotient framework on the real fixture, honest
partial — it's the multi-week assembly). NEXT after it: the Groth16 wrap + the settlement VK; then the message-root
proof-binding residual (26th PI). GPU de-prioritized (banked: shrink ~2x via BN254 wgpu, Amdahl-capped; ember value call).

## ⚑⚑⚑ NATIVE FULL-STARK-VERIFY (metaprogrammed) — VERIFIED ON REAL SHRINK PROOF (07-12 ~2pm)
The EVM last mile, built the dregg way (ember: metaprogram from the verified AIR). gnark now does the FULL STARK
algebra on the REAL shrink proof (5/5 instances incl. heavy ALU 146 + Poseidon2 337 constraints): constraint-eval
GENERATED from the AIRs via get_symbolic_constraints (correct-by-construction) → generic gnark interpreter over
BBApi → 5 quotient identities + global LogUp balance + VerifyFriNative FRI core → ACCEPTS the real proof (verified
myself, FullVerifyGadgetAccepts 2.18s); 22 tamper canaries reject; symbolic-vs-hand differential pinned. THIS IS
the Lean AirChecksSatisfied "half (ii)" (constraint/quotient soundness) realized in-circuit. FRI-core = half (i).
REMAINING EVM PATH: (1) the reduced-opening-BINDING seam (open_input in-circuit: per-query input-batch Merkle
openings + the α-combination — binds opened-values-at-zeta to the actual COMMITMENTS; currently host-computed;
the last SOUNDNESS piece; needs an exporter extension) → (2) VK baking (DAG as circuit constants) → (3) Groth16
wrap → DreggSettlement.sol VK pin → real on-chain settlement. Then the message→root proof-binding residual (26th PI).

## ⚑ open_input SEAM CLOSED + self-verified (07-12 ~2:32pm) — CRITIC AUDITING the whole claim set
The last soundness seam: opened values now COMMITMENT-bound (open_input: per-query native-BN254 multi-height batch
Merkle + α-reduction == FRI InitialEval/RollIns). Verified myself: 9 ref + gadget tampers reject (input-row,
merkle-path, commitment-root, opened-at-zeta, initial-eval, roll-in, α, ζ); assembled FullVerify rejects a tampered
opening. So the native STARK verify on the real proof = transcript + FRI + opening-binding + constraint/quotient(5/5).
HELD (not celebrating): (a) FRI low-degree still ASSUMED (StarkSound half (i)); (b) "gnark==Lean AirChecksSatisfied"
is ANALOGY not a differential-to-Lean (TODO); (c) VK not baked (trusts fixture), Groth16 wrap DOES NOT EXIST,
DreggSettlement VK not pinned → "near settlement" optimistic. An OPUS adversarial CRITIC is auditing all of this
(a6826754db48c1dd0) — its findings become the work-list; scope will be corrected to what it survives.

## ⚑ POST-CRITIC WORK-LIST (07-12 ~2:45pm)
EVM: lane af979acc02de112c6 running — bind the 25-lane statement to the REAL verifier (reject wrong root) + the
actual Groth16 (early output shows a ~898M-ish number — likely the R1CS count → Groth16 on the laptop probably
INFEASIBLE = an honest blocker, will confirm) + replace the MOCK verifier + neuter the vacuous hand mode.
SOLANA: launched an opus adversarial critic (a6dd0464bd2ef3cce) on the ≥2/3-supermajority proof-of-holdings claim
(is verify_supermajority real crypto or a trusted stake-table/number? is the accounts-hash-inclusion owner-checked?
any ConsensusVerified-without-supermajority path?) — same discipline the EVM critic applied. solana-lock settle =
M-of-N oracle-attested (honest); succinct wrapper reuses the recursive-STARK verify surface (the wrap unlocks it).
DISCIPLINE MINTED: send an adversarial critic at EVERY completion claim; never report R1CS-satisfiability as a proof
or a mock as a verifier.

## ⚑ SOLANA FORGERY CLOSED + VERIFIED MYSELF (07-12 ~3:52pm)
The critic-found stake-table forgery is FIXED (committed). All production ConsensusVerified paths now route through
the anchored provenance closure (from_anchor + tally_authorized + governance-PINNED WeakSubjectivityAnchor); the
bare-table path is #[cfg(test)]-gated. VERIFIED MYSELF: the attacker's 1-key stake table REJECTS (AnchorRootMismatch)
on BOTH the bridge path AND the production watcher; honest anchored holding ACCEPTS; fails closed without a pinned
anchor; plain build has no bare-table→ConsensusVerified path. Corrected claim: Solana holdings now genuinely trustless
over a governance-pinned weak-subjectivity anchor (the standard light-client trust model), NOT "trusted-table arithmetic".
RESIDUAL (operator, named): deployed config must pin the real governance-chosen (epoch, stake_table_root).
SCORECARD: 2 critics → 2 real holes (EVM verifier binds no state root; Solana trusted stake table) → EVM being fixed,
SOLANA FIXED+VERIFIED. Critics-at-completion = standing practice. EVM lane (binding + Groth16) still running.

## ⚑ APEX-VK PIN — forgery CLOSED + verified (07-12 ~8:12am)
The 3rd critic's same-shape-malicious-apex forgery is CLOSED: SettlementCircuit now bakes the deployed apex's VK-core
(ApexVkLanes, re-exposed via the expose_claim channel) as constants + asserts equality, like the shrink-VK pin.
VERIFIED MYSELF: mismatched apex VK-core lanes REJECT; unpinned-control ACCEPTS the same mismatch (pin is load-bearing,
non-vacuous). So EVM settlement binds BOTH shrink VK + apex VK → only the deployed dregg apex+shrink proves. Trust: the
constant is fixture-lifted (trust-on-compile, = shrink-pin level, consistent w/ the dev ceremony); strengthening =
derive from RecursionVk (accumulator.rs) independently.
SCORECARD: 3 critics → 3 real holes, ALL CLOSED+verified (EVM no-SNARK/no-binding, EVM unpinned-apex, Solana trusted-table).
REMAINING (named, honest): (a) bridge submitter EthSettlementProof 256→384-byte blob [item 2, doing now]; (b) message→root
26th-PI (outboundMessageRoot proof-bound not operator-attested — a real soundness gap); (c) RecursionVk-derive the apex
constant; (d) prod MPC trusted setup (standard Groth16 caveat, needs a ceremony).
NEXT: bridge submitter blob → message→root 26th-PI (the last operator-trust soundness gap).

## ⚑ QUALITY WAVE (07-12 ~8:26am) — status
DONE+verified: bridge submitter 384-byte blob (calldata BYTE-IDENTICAL to Foundry ground truth, 25/25); sketches
README index; hygiene clean (no dead code / dangling refs / go-vet clean). RUNNING: docs-honesty-sweep, RecursionVk-
derive apex-constant (converging on the apex-pin's uncommitted chain/gnark v4 state → commit combined). NAMED GAP
(loud): the apex-pin changed the circuit (ClaimLen 25→33) → the on-chain Groth16 artifacts (verifier + proof +
Foundry test) are STALE (pre-pin) → re-run DREGG_SNARK=1 (~13min) to make on-chain match the pinned/sound circuit.
MESSAGE→ROOT 26th-PI — ASSESSED: NOT a quick bind. The apex does NOT currently compute/expose an outbound message
root (grep-empty in circuit-prove/src + turn/src); DreggSettlement.sol keeps outboundMessageRoot OPERATOR-ATTESTED.
Closing it is a DEEPER cross-layer feature: the turn/apex must compute the outbound-message commitment + expose it
(as a 26th lane OR folded into chain_digest — a design decision), touching the recursion/turn layer (possibly shared/
stark-kill territory). Deferred with honest scope, NOT pretended-next. NEXT quality: RecursionVk-derive harvest +
combined commit → Groth16-regen for the pinned circuit → a comprehensive 4th settlement-soundness critic.

## ⚡ SWARM MODE (07-12, ember: "none of this needs gating, swarm over ALL of it") — un-parked, un-gated
Correcting the recent timidity. LIVE PARALLEL LANES:
- GPU PROVER WIRING (a21064dd4b9b88d29) — UNPARKED: real wgpu DFT + Poseidon2/BN254 MMCS behind DreggOuterConfig's
  traits, measure REAL end-to-end shrink prove GPU-vs-CPU (M2 unified memory). The real prover-accel, not a park.
- MESSAGE→ROOT 26th-PI (a38b37ec8c55d5799) — the last operator-trust gap: turn/apex computes+exposes an outbound-
  message commitment → SettlementCircuit binds → contract drops the operator attestation. Assess+build (deep, cross-layer).
- 4th COMPREHENSIVE CRITIC (a5b2e7ae22adae2a6, opus) — audit the WHOLE completed path for a residual forgery /
  a composition seam between the 3 fixes / whether the RecursionVk anchor is authoritative-or-circular / on-chain staleness.
- GROTH16-REGEN (abb099a6c93b15d61) — mid-setup for the PINNED circuit (R1CS 12.87M, 25 public, ClaimLen 33). Closes on-chain staleness.
TRUSTED-SETUP ANSWER (ember's Q — why re-run each time?): Groth16 setup is PER-CIRCUIT; the re-runs were because the
CIRCUIT kept changing (binding → apex-pin → ClaimLen 25→33), NOT fresh-randomness-for-its-own-sake. FIX (next, after
regen): FREEZE the circuit + cache the params keyed by circuit-hash — save the pk locally (huge, gitignored) + commit
the vk (small, it's in the verifier contract) + SKIP setup when the circuit hash is unchanged → dev proving REUSES the
params, no re-ceremony. Toxic-waste caveat only bites PRODUCTION (an MPC). NEXT after regen: trusted-setup param-cache
+ Lean-tie differential (chain/gnark frees). NOT gating build work on ember; only deploy/MPC/alloy-trie go outward.

## ⚡ SWARM CYCLE WINS (07-13, verified) — GPU 6.6×, on-chain shrunk circuit, trusted-setup cache
- SettlementCircuit SHRUNK 12.87M→4.98M (−61%, verification-preserving open_input hoist) DEPLOYED on-chain: fresh
  4.98M verifier, Foundry RealProof 7/7 (real proof settles 626k gas, forgeries reject), prove 70s→17.7s.
- TRUSTED-SETUP CACHE (groth16_cache.go — ember's fix): content-hash the R1CS → skip groth16.Setup on unchanged
  circuit. DEMONSTRATED 7m27s(miss)→1.24s(hit). No more re-ceremony. pk gitignored (2GB), vk committed.
- GPU PROVER 6.60× MEASURED + VERIFIED: CPU shrink 95.48s (= exact baseline, fair) → GPU shrink 14.46s. Proofs
  BYTE-IDENTICAL (430565B) + cross-verifier round-trip + reject-polarity. Beat the ~2-2.5× Amdahl floor because the
  FRI-fold commit hashing is ALSO GPU-resident. Committed gpu_backend + the e2e test.
NEXT-WAVE (chain/gnark, sequenced): RecursionVk fingerprint-CHECK (Finding 2 — make the anchor real, RUNNING);
GKR-batched Poseidon2 (next shrink ~−2.5M, verification-preserving protocol); GPU byte-identical-test teardown flake
(wgpu buffer-drop lifecycle, test-hygiene followup — correctness confirmed by the e2e byte-identity). GPU is UNPARKED +
delivering; the client-side-proving payoff (fast turn/shrink proving on a Mac) is now measured-real.

## ⚑⚑⚑ FRONTIER SUBSTANTIALLY COMPLETE (07-13) — the clean-and-mine scope is done + verified
EVM SETTLEMENT: real Groth16 proof settles on-chain (Foundry 7/7); 25-lane state root bound to the verified apex
output; BOTH shrink+apex VK pinned; apex constant RecursionVk-DERIVED + a REAL fail-closed anchor CHECK; open_input
FRI-binding; metaprogrammed (correct-by-construction) constraint-eval. Circuit 4.98M (−61% verification-preserving),
prove 17.7s, setup CACHED (skip on unchanged). 4/4 adversarial critics → all findings CLOSED. GPU prover 6.60×
verified (byte-identical). SOLANA: proof-of-holdings anchored (forgery fixed); settle = M-of-N attested. CROSS-CHAIN:
binding trilogy + gov spine. Docs honesty-swept. GKR-Poseidon2 measured MARGINAL (banked).
HONEST REMAINING (none clean-and-mine-trivial):
- DEEP-DEFERRED (cross-layer / sibling territory): message→root FULL proof-binding (turn/apex must expose an
  outbound-message commitment — currently fail-closed, not forgeable); IncrementNonce→Transfer full-wrap path (awaits
  the sibling wide-registry flag-day); the Lean-tie differential (recursion-AIR vs effect-vm-AIR layering).
- HYGIENE: GPU byte-identical-test wgpu-teardown flake (correctness already confirmed by the e2e byte-identity).
- MARGINAL: GKR-Poseidon2 integration (−14/−30%, deliberate 2nd shrink wave only if justified).
- EMBER-OUTWARD (gated on ember, not build): prod MPC ceremony; deploy/testnet timing; alloy-trie upstream; the
  in-repo governance anchor constants (update at deploy).
The swarm drove the achievable clean-and-mine scope to completion; the remaining needs sibling coordination or ember's
outward decisions.

## ⚡ TESTNET-DEPLOY + DrEX-FRONTIER (07-13, live)
- **TESTNET DEPLOY greenlit + funding in progress:** throwaway EVM key `0x8b251ADF19a78C6f9e9217E07CD3468C40F00343` (seed+key in session scratchpad, never committed). ember funding via Superchain/CDP faucet. On funds → `forge script chain/script/DeploySettlement.s.sol --rpc-url base_sepolia --broadcast` (fixture-genesis default → real Groth16 `settle()` in-tx = the whale-reply centerpiece: "a dregg proof settled on Base-Sepolia"). Balance-poll armed.
- **B_IROOT FIXED** — scope issue, const back at trace_rotated.rs:303; dregg-circuit compiles; circuit side UNBLOCKED (real matcher / shielded weld / caveat-in-circuit all buildable).
- **DrEX tower = 7 rungs** (1 fairness · 2 aggregation · 4 uniform-price optimality · 5 priced/partial/multi-pair · 6 never-insolvent liquidity · 7 cross-margin-via-mandate), all kernel-clean; LedgerRealization welds rung-1 + rung-5-full-fill to the REAL recKExec (kernel-real). Shielded-pool ABI `_refines_` PROVEN.
- **DrEX CLICKABLE** (drex-web/): REAL extension-wasm wallet proving (PQ signed turn + conservation proof bound to order + tamper-reject) — verified. Matcher mirror being replaced with the REAL solver→verified_settle→recKExec pipeline.
- Replyable distance ≈ one broadcast (funding) + host/record the demo. DrEX/OCIP buildout bar MET.

## ⚡ REPLY-GATE CLEARED + WHALE REPLY POSTED (07-13, late)
- **All 3 reply-gate welds DONE + verified:** shielded-pool circuit weld (e020e717e, 6/6 teeth, forged→UNSAT); caveat-in-circuit BIGNUM-hardened (6b3f9e64d — 130-bit u128-safe, CaveatBignumCompare Lean-proven borrowSub_iff, real-scale); real DrEX matcher (2045770ec — mirror DELETED, real solver.rs→verified_settle→recKExec via POST /clear, verified fixture-only clearside).
- **The moat** (41c25eb1c): solvency leaf + {note-spend ⊕ solvency} structured-product fold, 7/7, reusable-as-a-leaf.
- **bs-vk wire-codec RECOVERED onto main** (7b1343314): the vk-epoch-nullifier stage-E shadow-executor nullifier-root ADVANCE (insert_witness_aafi — MORE faithful than bs-vk's raw insert), 5/5. NOT a merge. Stage-F VK-regen = ember-gated tail.
- **Nullifier freshness IS proven in-circuit** (main): RotatedKernelRefinementNotesFresh + SortedTreeNonMembership + NullifierAccumulator bridge — the 'PHASE-D not available' comments were STALE, REWRITTEN true. Stale-comment sweep (e548ac087): 8 fixed, 5+ open left accurate.
- **WHALE REPLY POSTED by ember** — honest, graded, points at the live Base-Sepolia tx + real-matcher clickable DrEX + shielded/mandate proofs + Robinhood TSLA inbound.
- **NOW SWARMING:** launchpad MVP for Robinhood Chain (NOXA down = the gap; fair-by-theorem differentiator); GPU-fold (re-dispatch, local Metal, contention down); DrEX rung-3 private matching (ring over shielded notes — unblocked by the shielded weld); provably-solvent lending (undercollateralization-impossible).
- Robinhood: inbound REAL (TSLA proven in, weak-subjectivity); launchpad MVP building; deploy key funded, held on ember. Base-Sepolia settlement LIVE (tx 0xbd2cac6a…).

## ⚡ dreggfi WAVE (07-13, very late) — 4 more landed + verified
- **DrEX RUNG-3 private matching** (d23c0c2ee): shielded_ring_clears — a ring clears CONSERVING+FAIR+PRIVATE+NO-DOUBLE-SPEND over HIDDEN notes; hidden-conservation weld (ΣC_in−ΣC_out=0 over Pedersen commits, no value revealed). DELETES the decrypt committee. Lean spec; circuit fold = named finishing step. DrEX tower now 1-7.
- **Provably-solvent LENDING** (271cb8ac1): undercollateralization-IMPOSSIBLE — BadDebt (underwater ∧ ¬liquidatable) UNCONSTRUCTABLE (Liquidatable defined THROUGH the liquidate transition); solvency composes pool_solvent_forever + stripe_reserve verbatim; liquidation total. 25 keystones clean. Conditional on the mark (oracle weld = next).
- **LAUNCHPAD MVP** for Robinhood Chain (chain/contracts/launchpad/): disclosed-mint+sealed-bid+uniform-clear+settle; 11/11 both polarities (hidden-supply/snipe/peek/late-switch/dev-dump all REVERT); DeployLaunchpad dry-run vs live chainId-46630 RPC; one-ember-command broadcast. Fair-by-theorem, PROVED off-chain + REPLAYABLE on-chain; clearing-attestor + bonded-conduct = named welds.
- **GPU-FOLD** (f809baa33): GpuBabyBearMmcs + GpuDft — fold's Merkle+DFT commit stages GPU'd 6-11× / 2.9-3.8× BYTE-IDENTICAL on M2 Max Metal (MEASURED). End-to-end 288s→~60-85s = PROJECTION (blocked on a concurrent effect_vm descriptor-regen flag-day; not faked).
- Report v2 building. NEXT: the ORACLE WELD (price-as-witness — closes the "given the mark" edge for lending+solvency).

## ⚡ ALL-AXES WAVE (07-13, late) — verified + committed
- **LEDGER-REALIZATION → the toy-model answer** (107504fb8, LedgerRealizationExt): rung-5 PARTIAL-fill kernel-real (all valid cycles); rung-3 shielded FUSED (LegFused ties matcher offer↔hidden note asset/value) + kernel-real; rung-6 pool per-fill kernel-real. DrEX now KERNEL-REAL for rungs 1/3/5/6; rung-4 intrinsically model (optimality over prices, no ledger). VERIFIED.
- **REAL-CRYPTO** (31a7b0fe3): toys retired — rung-3 on real 2-gen Pedersen (DLog) + real Poseidon2 (SpongeCR).
- **COSMOS outbound DEMONSTRATED** (3a3b42c73): CosmWasm verifies the SAME BN254 proof, 5/5, cross-validated; no native-field needed (wasm runs BN254).
- **SOLANA home-chain parity** (9afee4ae5 + 85d6de2d5): on-chain settlement program (alt_bn128 Groth16, verifies the real proof, 91KB .so) + proven-root registry (isProvenRoot PDA) + AssertProvenRoot CPI gate (DreggProofISM analog, Nomad-law) + keccak-Merkle inclusion. Lock → consensus-verified (9bdcba4fd, ≥2/3-stake, 7 tests). Dev-ceremony, local-test.
- **GPU FOLD end-to-end** (6fb805da4 + 638788e99): GpuDreggRecursionConfig; MEASURED byte-identical CPU==GPU, cross-vendor — leaf-wrap 2.60× (Metal), tower-2^16 3.62× (Metal) / 7.12× (AMD Navi22/Vulkan). ⚠ FLAG: rotated fold fixture BROKEN AT HEAD (transfer descriptor trace_width 47 vs refuse-weld's 48 — a geometry off-by-one from the heterogeneous-refuse-weld rework 5e84c5dd4/aa282f8c0; apex_shrink_bn254_tooth broken but #[ignore]). Deployed proof unaffected; regen blocked.
- **DATA-LOSS bug** (03dde2241): acute 32→8 truncation was ALREADY-CLOSED same-day (76f7a6603); regression test added. RESIDUAL: SetField of a NEW 32-byte value into a scalar slot loses high 24B (wire low-8 projection) — reachable (supply-chain TIP/collective-choice ELECTORATE); the v13 faithful-fields widening, sequenced with v13, HORIZONLOG'd (NOT a thin-context fix).
- **cv-patch** (9501774): subagent search-surface fixed (bare agentId + ⤷tag); verified cv search hits the real af56cb4f transcript.
- **DESIGNS**: ZK-AUCTION-SUITE (comprehensive, starbridge-apps foundation, top-1 = the 2-leg ring-clearing AIR); SHIELDED-AUCTIONS; RECOVERED-THREADS.
- NOW FIRING: the rotated-fixture geometry FIX (pipeline broken at HEAD, careful) + the 2-leg shielded RING-CLEARING AIR (the marquee — rung-3 now fused + real-crypto'd, so the AIR realizes it).

## ⚡ ROUTING/CUSTODY ARC COMPLETE + marquee AIR (07-13, v-late) — verified
- **INTERCHAIN-CUSTODY MODELED+PROVEN** (92aaa9dd1, InterchainCustody.lean): run_backed (Rust live_supply≤currently_locked LIFTED to inductive invariant) + custody_cross_boundary_conserves (end-to-end lock→mirror→clear→release conservation, composes DrEX clearing) + ringRelease_atomic. 21 keystones clean. THE answer to "modeling too naive" — Lean now crosses the vault boundary. VERIFIED.
- **TIMEOUT/REFUND ESCROW on ALL 3 custody chains** (4bfc3de9e EVM+Solana, 1c0f1f212 cosmos-lock NEW): two-branch exactly-once (release-on-proof XOR refund-on-timeout), Released XOR Refunded never-both-never-stuck; escrow custody DISJOINT from mirror pool. forge 146 / solana 54 / cosmos 12. Locking into DrEX is SAFE. Residual: cross-vault ATOMIC release across a permanently-down chain = named RESEARCH.
- **ROUTING DESIGN** (e1ca1be44, DREX-ROUTING.md): ring-of-locks (counterparties' locks ARE liquidity, no LP, no bridge validators); 3 custody modes; docs fixed (prove-don't-lock=governance-only). ember caught this gap; now designed+proven+safe.
- **RING-CLEARING AIR** (34ae42157): rung-3 shielded_ring_clears SPEC→BUILT (2-leg, in-AIR Pedersen conservation + Poseidon2 fusion; 8/8 GENUINE circuit-UNSAT teeth). The marquee private-auction primitive runs.
- **LAUNCHPAD GRADUATION** (d4ae11725): fair-launch→proven-solvent x·y=k pool (floor-drain reverts, refines rung-6); forge 16/16 + web 29/29 live-anvil e2e.
- **FIXTURE-FIX** (60e49265a + swept 97a56a0ed): geometry off-by-one FIXED (exclusion subtracted stale 48; weld adds 45=REFUSE_WELD_WIDEN; verified vs 5e84c5dd4 intent + committed bytes). Fixture MINTS again; proof-regen UNBLOCKED. ⚠ FLAGGED (not green-hacked): deployed_cohort_bytes_carry_the_refuse stale (36→35 rows, custom base 1619→1623 = aa282f8c0 debt) — honest follow-up.
- NOW FIRING: DrEX-VAULT WIRING (route end-to-end: lock→mirror→DrEX-clear→clearing-proof-gated escrow-release, now unblocked) + the stale-cohort-test HONEST resolve.

## ⚡ NUMERICS BEDROCK + PIPELINE KEYSTONE (07-13, night) — verified
- **Dregg2.Bignum** (35bef2d7a): unified proven bignum — compare/add/sub/mul/mod/range, each _iff soundness+completeness + the 4 anti-exploit theorems (no-underflow-wrap / no-overflow / field-vs-integer / canonical) UNCONSTRUCTABLE, emittable-Constraint. lake clean, #assert_axioms clean. VERIFIED. (vault+shielded re-point = named follow-up, no cycle.)
- **NUMERICS AUDIT** (adc69d2d): money paths MOSTLY WELL-HARDENED (transfers/mirror/escrows/CFMM/launchpad/ERC4626/fees/in-AIR-conservation all SAFE, verified per-site). FIXED: DischargeObligation wrap → checked_add (5301f3a19, teeth 3/0). ⚑ CRITICAL NAMED: game-economy FieldDelta underflow-wrap MINT (~2^31 gold/hp — new==old+delta wrapping, no range check on result, game slots unranged-in-AIR; honest-executor .max(0) clamp bypassed by a post-state supplying the wrap value). ✅ DEPLOYED (no longer staged): transfer/burn debit-wrap avail-weld materialized into the re-keyed VK epoch (GAP 1-6 flip, 1e12d8886/764225f0c; 72469afd0 "deployed VK IS vkOfRegistry RfixAvail") — over-debit is structurally UNSAT on the live wire.
- **FOLD RECONCILIATION** (764225f0c) — THE PIPELINE KEYSTONE UNBLOCKED. 2 breaks fixed: (1) per-member refuse_weld_widen (45 for 2 avail members, 48 for other 34 — verified vs committed bytes, not a constant); (2) custom-table-84 (15-bit range) realized (range_bits_for decodes width from tid). 3 GATES GREEN: fresh fold MINTS both turn bodies (IncrementNonce+Transfer); fresh-folded proof settles toward deployed verifier (apex_shrink 3/3, deployed apex VK); NO soundness regression (7 refuse teeth). Node prove_pool can now STARK-prove fresh turns → unblocks node-onchain + demos→node STARK-attach. ⚠ NAMED (not green-hacked): deployed_cohort_bytes 1/8 fail = pre-existing GAP1-6 flip artifact (revokeDelegation-v2 wide-vs-1felt incoherence + custom V1Face base shift GRAD−28→−24) — needs flip-author intent.
- **make-it-real status**: demos→node DONE (real turns, executor-signed); node-on-hbox DONE (running private, verified executor, dag climbing) — both STARK-attach was blocked on the fold, NOW unblocked → node needs REBUILD to pick up 764225f0c.
- NOW FIRING: node-rebuild→STARK-verify (the milestone); the CRITICAL FieldDelta-mint fix; pbuild build-ergonomics guard (prevent catastrophic fresh-lane mathlib rebuild).

## ⚡ MILESTONE: CLICKABLE PRIVATE DrEX + VK-FLIPS VERIFIED-DONE (07-13, v.late)
- **drex-web LIVE + clickable** (ce153c7ee): http://192.168.50.39:8781 (LAN) — a real trade STARK-proves on the private node (turn 3eb0dd7f…, has_proof:True, verified). Settles as a value Transfer→pool + ring-leg events (the full per-trader SetField allocation is UNATTESTED at HEAD — the setFieldVmDescriptor cohort selector ambiguity, prover fail-closes; named residual = the SetField-attestation VK-flip).
- **TAILSCALE: ember authenticated** — hbox-dregg = 100.95.240.73 on ember's tailnet (ufw allows tailscale0). The AWS-gateway channel + ember's from-anywhere access. drex-web being rebound for tailnet reach.
- **VK-FLIP #1 (debit-wrap)** = ALREADY-LANDED, verified gate-for-gate (over-debit UNSAT, avail-weld deployed). No churn.
- **VK-FLIP #2 (nullifier freshness)** = ALREADY-LANDED, verified gate-for-gate (2f451a20c 47→51 test-currency fix): deployed noteSpendVmDescriptor2R24 forces nf∉pre.nullifiers via absent+aafi_insert map-ops; both-polarity green. No churn.
- ✅ RESOLVED (was a TEST-BOUNDARY bug, not a soundness gap): ir2_umem_double_spend_refuses. The umem cohort forces freshness in-circuit via its Blum offline-memory-check; a double-spend is REJECTED BY THE VERIFIER (GlobalCumulativeMismatch on `ir2_umem_check`). The old failing test asserted the raw `prove_vm_descriptor2_inner` return under `check=false`, which in release emits an UNVERIFIED proof (self-verify skipped) — so reading its return as "accepted" was the bug. FIXED in 9b293037b: the tooth now asserts the VERIFIER (`assert_umem_forgery_refused`). (Separately, vk_epoch_misc_light_client_binding had a Faithful8 vs [u8;32] compile drift — a distinct in-flight test-target item, not the umem soundness.)
- NOW: drex-tailscale-rebind (from-anywhere URL) + SetField-attestation VK-flip (unblock SetField proving → DrEX settles full clearing attested).

## ⚡ OVERNIGHT WAVE (07-14) — verified
- **dregg-site LIVE** (dregg.net): /drex/ (fair-exchange explainer, general-audience) + /markets/ hub + /launchpad/ (fair-launch, scams graded proven-impossible) + The Descent leads /build/; nav why·try·build·markets·coin; 4 blog posts held as drafts (preview-drafts.sh). Honest-graded, brand-law held, deployed (CloudFront invalidated).
- **turn_hash DETERMINISTIC** (53c598957): was nondeterministic (hedged ML-DSA sig bound into Action::hash). Fixed Option A (FIPS-204 deterministic sign rnd=0), anti-strip byte-identical, verified same-turn-same-hash + stripped-sig-rejected (15/15 pq, 5/5 SDK). Unblocks pip SDK. VERIFIED.
- **DrEX-vault routing e2e** (fefcd200d): ring-of-locks wired END-TO-END — lock→mirror→clear→clearing-proof→escrow-release, real run (Rust 4/4 clearing root 0x7e7a5a01, Foundry 6/6, mirror+ring conserve, refund/over-release/wrong-recipient teeth). DATA-real, proof-MOCKED (SP1/Groth16 = named §4(e) residual). RUNS end-to-end.
- **GAUNTLET red-umbrella reconciled** (302307460): arity-3 geometry drift (CAVEAT_BASE 642→666, B_SPAN 227→239) — teeth reconciled (alignment still bites), bridge fixture regen'd (Foundry-cast-verified, not vacuous), turn test 7th-arg. ⚑ GENUINE RESIDUAL flagged NOT laundered: revokeDelegation-v2 dropped-weld.
- **help-the-next-guy sweep** (13c2a871a): 10 stale "staged/frozen/open" artifacts rewritten to DEPLOYED truth (avail-weld, emit files, census docs, GOAL trail, memory); real residuals kept accurate.
- ⚠ codex drex-web UX redesign DID NOT SHIP (stuck on stdin). ⚠ intent lib-tests + dregg-turn test-bin independently broken (circuit prove-API drift — separate fixup).
- NOW: close the revokeDelegation-v2 dropped-weld (soundness residual, VK-change, ember-un-gated).

## ⚡ fhEgg KERNEL + CONVEX-ENGINE FRONTIER (07-14)
- **FHEGG-KERNEL.md** (e19e0a2ad): aggregation-monoid CONFIRMED as the kernel (clearing = homomorphic fold of order-curves + one crossing; O(N·K) bootstrap-free vs O(N log²N) matching). ⚑ MULTILATERAL RING VINDICATED (ember's coequalizer instinct): it's a CIRCULATION in ker ∂ (linear, public basis) → free conservation check for exact intents, poly-time oblivious-LP only for scaled partial-fill — NOT graph-hard. Privacy STRONGER than Penumbra (decrypt-nothing vs threshold-decrypt). Residual: DLog homomorphic layer → PQ lattice-additive fold cutover.
- **N-leg ring-clearing AIR** (49d05235d): variable cycle + partial-fill inequality, transcript [nf,root,vb]ⁿ, 12/12 genuine teeth.
- **currency-fixup** (a40b15bd5): 3 stark-kill/revoked-root test drifts green; ⚑ REAL BREAK flagged = dsl_rc transfer avail-weld (wire 188 15-bit vs 30-bit producer = GAP#4 dropped weld, VK-regen reconcile needed); teasting/* + demo-agent same-class fallout named; persvati disk-full reclaimed ~35G.
- NOW: (1) PRIVATE-CONVEX-ENGINE research+design (first-order/operator-splitting = oblivious + homomorphic-linear; the products suite); (2) dsl_rc avail-weld reconcile (VK-regen, real break); pending: PQ-value cutover (DLog→hash), teasting-fallout cleanup, SetField-attestation.

## ⚡ CODEX (GPT-5.6-sol) HARVEST + corrections (07-14)
- **FHEGG-CODEX-INSIGHTS.md** (0b4c1f07a): brief→codex→curate/assess pattern WORKED. Codex (291k tokens, ~40 searches, 7 opening corrections — adversarial as wanted).
- ⚑ GOLD (independent hit, deeper than our doc): **Cert-F = certificate-carrying PDHG** — prove the primal-dual DUALITY GAP not the iteration trace; exact Cert-F inequalities for the flow LP; Fenchel-gap generalization → a private-convex COMPILER IR; proof-size O(Tm)→O(m+nnz A). Triangulates with PRIVATE-CONVEX-ENGINE.md.
- Q1 real contributions: **topology-only preconditioner** (oblivious step sizes from PUBLIC graph via normalized-Laplacian ρ≤2 — sharp) + **modulus/opening discipline** ("commit only endpoints, keep iterates under the STARK PCS" — additive homomorphism does NOT survive a T-fold; keep the fold inside the STARK). Correction: "one bootstrap/iter" false for heterogeneous caps (~2-3 PBS/pack).
- Q2: real categorical skeleton — **decorated cospans + guarded trace + resource-grading + convex-cost-by-infimal-convolution + proof/privacy functors (ZKOpenRel_R)**; recovers turn/auction/circulation/convex-engine as instances; resource-defect d_M = strong monoidal functor to (R,+,0), conservation=d⁻¹(0) (matches the Lean). HONEST: the compositionality/closure theorem (feedback+adaptive) is NOT proved = a well-posed research TARGET, not done.
- ⚑ IMPORTANT CORRECTIONS to thread: (a) exact all-or-nothing SELECTION is NP-hard (0-1 balancing/subset-sum) — tractability is the [0,1] partial-fill RELAXATION, NOT "exact intents free" (fixes FHEGG-KERNEL overclaim); (b) use incidence A directly, NOT a dense cycle basis B; (c) crossing needs the operator defined (monotone curves ≠ monotone operator); (d) commitment functor can't be both faithful-on-conservation + trivial-on-values.
- NOW: (1) PQ-value cutover (retire DLog from shielded TCB); (2) thread codex corrections + gold into the fhEgg docs.

## ⚡ fhEgg ENGINE — Stage-1 near-complete + FHE no-viewer MEASURED (07-14)
- **RevealNothing.lean** (e1571ac92, VERIFIED-by-me clean+sorry-free): reveal-nothing = `View ≈ Sim∘Q` over leakage functor Q (codex framing); PROVEN core (reveal_nothing, same_leakage_indistinguishable non-vacuous, value-hiding, simulator shell, leaky_no_simulator teeth, PerfectZK bridge); NAMED FLOOR = reveal_law bundle-field (HidingFriPcs statistical-ZK, graded like HashCR — NOT sorry). Honest grade: zk-clearing conditional-on-the-floor, tractable-core-proven. The differentiator made rigorous+honest.
- **fhegg-solver** (all 4 milestones, VERIFIED-by-me 26/26): exact Af=0 (1e-14 machine-zero via max-slack forest), QP/Markowitz product + CertQp (the factory), perf (1M orders 10.2ms GPU; 131k-edge PDHG 90ms 19.5× GPU sublinear; rayon net-negative REPORTED), Cert-F STARK-bridge AIR (n+4m+1 constraints, emit-agrees-with-checker).
- **CertF.lean + FhEggClearing.lean** (cefbecf14, VERIFIED-by-me sorry-free): the verified checker (certifies_epsilon_optimal + weak_duality) + aggregation (monotone-operator crossing, the sorry CAUGHT+discharged honestly).
- ⚑ **FHE NO-VIEWER PoC MEASURED** (fhegg-fhe, real tfhe-rs 1.6.3, no mock): correctness FHE=plaintext at every N/K; envelope N32/K64=46s, N128=2.2min, N512=8.1min, N512/K256~30min — MINUTES-to-TENS, not seconds, on exact-integer TFHE CPU. ⚑ KEY HONEST FINDING: "aggregation is bootstrap-free/cheap" REFUTED for exact-integer TFHE (radix-add carry-propagates, PBS-class 13-70ms not µs → aggregation DOMINATES, 45× the crossing). Confirmed: crossing O(K) N-indep (~10s); prox 2-3 PBS/pack. ⚑ CORRECTED TIER-0 DIRECTION: the µs-add premise holds ONLY in an ADDITIVE scheme (CKKS/Pedersen/LATTICE-ADDITIVE) — so the fold wants a lattice-additive (RLWE/Module-SIS) scheme (cheap-adds + PQ), TFHE/small-compare only for the O(K) crossing. This ALIGNS the fhEgg-fold PQ-lattice-commitment residual with the FHE-speed fix. Levers: additive-fold + GPU(H100 10-30×) + coarse K + per-pair shard.
- ⚠ Stage-1 wiring (aa6baedc) STALLED (watchdog) after clean-compiling the Cert-F AIR — resume to finish the native-eval + real STARK.
- NOW: finish Stage-1 wiring; then fhIR-0; the corrected lattice-additive Tier-0 fold (= PQ-commitment + FHE-speed); Price-Cert.

## ⚡ fhEgg — STARK soundness RESOLVED + mechanism FAMILY + product surface (07-14)
- ⚑ STARK bad-cert-refusal: RESOLVED + RE-VERIFIED-BY-ME (--release --lib cert_f_air = 13/13, negatives pass). Was TEST-INCOMPLETENESS not a hole: prove_cert_f mints optimistically in release (self-verify is debug-only, descriptor_ir2.rs:5573), but verify_cert_f REJECTS the bad cert (the AIR bites at VERIFY = the deployed soundness gate). Fix (2b708b862): prove_cert_f_refused now checks verify; + stark_bad_cert_proof_does_not_verify profile-independent guard. LESSON: 2 lanes claimed 12/12 from DEBUG; verify in the DEPLOYED --release config. AIR IS sound (verifier rejects bad certs).
- ⚑ ENGINE IS A MECHANISM FAMILY (b88df10e): uniform-price + circulation + Fisher-welfare-max/Eisenberg-Gale (CertEq, the general competitive clearing, uniform-price=its linear case) + discriminatory/pay-as-bid (CertF reuse) + CFMM-routing (CertRoute). fhegg-solver 42/42, fhir 29/29. Fisher 157ms, pay-as-bid 25ms, CFMM 27µs. Integer/combinatorial exact = NP-hard Tier-2 boundary (named).
- Lean product surface (b88df10e, sorry-free kernel-clean): CertQp (QP verify-not-find), PriceCert (ONE cert for derivatives: state-price LP + Snell upper-bound for American), FhIRAdmissible (compiles⇒runnable PROVEN; admissible⇒compiles named-open with a counterexample).
- Stage-1 engine COMPLETE + verified: verified Cert-F (Lean) + fast exact multi-product solver + real-STARK-sound (--release, my re-verify). Tier-1 = private-from-world, PQ, committee-free, fair — beats Zama on trust/fairness/verification/PQ (ECLIPSE-ZAMA doc).
- HONEST LEDGER (verified-by-me): fhegg-solver 42/42, fhir 29/29, Lean cores 7 files sorry-free, Stage-1 native-eval, real-STARK 13/13 --release incl negatives.
- Running: codex-round-3 (quantization/lattice-additive Tier-0 unlock), hbox-FHE (24-core CPU honest number, no GPU).

## ⚡ CODEX ROUND-3 GOLD (07-14, 90d911919) — being made real
- ⚑ Q1 GOLD (corrected ember+me): ε cannot absorb quantization noise (Certified needs EXACT feasibility). Right arch = "approx PROPOSES, exact quantized translation-validation DISPOSES": cheap approximate solver as untrusted search → exactify onto integer grid → recompute EXACT gap → feed certifies_epsilon_optimal verbatim. Noise = completeness/param, NEVER soundness. Concrete PQ scheme: 3-layer (FHE ct + BDLOP/MSIS additive commitment + link proof), BFV/BGV exact-quantized fold + TFHE scheme-switch crossing + CKKS PDHG. → firing MintSafeQuantization.lean (mint_safe_quantization: Σvout≤Δ·Σqout≤Δ·Σqin≤Σvin; field_gate_refines_nat_eq = the no-wrap refinement). a446f750.
- ⚑ Q3 GOLD (sharpest): GuardedTraceClosure REFUTED (counterexample X=Y=1,U=Bool,f=neg) — the ZKUnification conjecture field is FALSE/uninhabitable, R1 guarded a false statement. Replacement: finite-box Tarski feedback on the crossing operator (matches Fstep_monotone/crossing_fixed), TraceAdmissible→Guarded(gtrace) = verify-not-find lifted to feedback. → firing ZKOpenRel.lean fix (refute-and-replace). af6a2cf5.
- Q5 novel: coefficient-difference-polynomial O(N+K) prefix scan (one plaintext multiply). codex forced ~6 adversarial corrections (real 2nd mind, 497k tokens). brief→codex→curate WORKED 3×.
- FPGA-accelerator spec firing (affe77ad): F2 = FHE-fold accelerator NOT STARK-prover; verified-HDL split (Coq/Hardcaml core + SpinalHDL bulk); confidential-VM→tee-verify; roadmap→silicon→dark-LLM north star (Constitution Art III/IX-H3/X = the Remainder Floor in silicon).
- ⚠ HONEST: codex gold = ASSESSED-BUILDABLE proposals, NOT yet discharged — the 2 Lean lanes are discharging them; re-verify myself after.

## ⚡ codex-gold DISCHARGED + full-tree verified (07-14)
- ⚑ FULL Market BUILD GREEN (3082 jobs, my own run) — the night's Lean COMPOSES: Q1 sound-quantized Tier-0 (MintSafeQuantization + QuantizedConservation + ExactGapNoWrap + AggregateBinding + StreamingCert + PrecisionEnvelope; approx-proposes/exact-disposes, soundness never eps-absorbed) + Q3 ZKOpenRel (guardedTraceClosure_refuted PROOF + traceAdmissible_guarded Tarski replacement + comp/tensor/iterate closure; ZKUnification now INHABITED). No red umbrella.
- FPGA spec (61bd1a3cc): F2 = FHE-fold accel (~0.15-0.7s/512x64 batch vs 488s M2; ~100-400 dark markets; medium-confidence error bars); verified-HDL split; Constitution Art-X-in-silicon.
- hbox-FHE (dcfe6cdd6): 24-core = ~1.0-1.6x M2 (NOT 2x; no GPU; radix caps ~8 threads). Real levers = quantized fold + cloud H100. Node undisturbed (minted 12 blocks).
- ⚑ EMBER CATCH (right): we HAVE a Lean->EffectVmDescriptor2 emitter (all effect_vm circuits, export+byte-twins). cert_f_air.rs HAND-BUILT the Cert-F descriptor + only TESTED agreement — a shortcut, not the frontier I implied. Lane ad719a49 routing Cert-F through the real emitter (Lean certFDescriptor + Satisfied2-iff-valid proof + byte-twin), retiring the hand-write.
- fhIR-1 Price-Cert RUNNER (d6c105fc9, VERIFIED-BY-ME): fhegg-solver 50/50 + fhir 32/32; european_price_cert_runs_and_certifies + american_snell_runs_and_certifies pass. State-price LP (two-phase simplex, gap ~1e-13) + Snell-envelope tree (American put → ~6.09, 525k nodes ~12ms); both polarities (arbitrage/tampered rejected). Derivatives EXECUTABLE through the same engine. American 153-node tree → Shielded (tree-cliff biting, honest).
- LAUNCHED: quantized Tier-0 crypto PoC (a9acd11e — carry-free additive fold vs exact-integer TFHE, mint-safe rounding applied; the honest speed-unlock measurement). Cert-F verified-emit (ad719a49) still cooking.
- ⚑ Cert-F VERIFIED-EMIT (01d9595f8, VERIFIED-BY-ME --release --lib cert_f = 14/14 incl negatives + cert_f_descriptor_matches_lean byte-twin): ember's catch paid off. CertFDescriptor.lean (8 keystones) — certFDescriptor_emit_sound (Satisfied2 → all 5 families, the theorem the Rust could only TEST) + rangeGadget_forces_range (the range tooth CertF deferred, now PROVEN). Lean authors the descriptor; Rust is the byte-checked twin; @[export] archive is the deploy step. "tested to agree" → "proven to emit."
- FPGA-TEE fix (46c40161a): ember's Nitro catch confirmed — F2 = Nitro-ONLY (no SEV-SNP; M6a/C6a/R6a only), Nitro enclaves can't drive FPGA (no PCIe), SEV-TIO absent. Reframe: Tier-0 needs NO TEE (FHE = ciphertext confidentiality); TEE scoped to Tier-1 plaintext + key custody (separate SEV-SNP host or named boundary).
- FHEGG-KERNEL.md updated (sober present-tense what-is, graded status column, verify-not-find + mechanism family + honest FHE + exactify-then-check, boundary-safe).
- LAUNCHED: launchpad-opportunity investigator (aa7fe962 — recall prior NOXA/launchpad thread via cv + synthesize the anti-rug thesis: fairness-as-theorem, "verify me not trust me", NOXA-rug moment; buildable-product vs Robinhood-BD-speculative). Quantized Tier-0 PoC (a9acd11e) + FPGA scaffolding (ac30a600) still cooking.
- FPGA scaffolding (2893cda82, VERIFIED-BY-ME lake build 8 jobs clean): fhegg-rtl/ — WORKING Lean→Verilog (fullAdder_realizes proven sorry-free, emits real synthesizable Verilog) + golden models (mint-safe accumulator + NTT butterfly) + CONTRIBUTING M0→M6 + SpinalHDL scaffolds. Landscape verdict: NO mature verified Lean-4 HDL (Verilean/sparkle early/dubious) — we seeded the niche via repointing dregg's verified-emit at RTL. Named seam: toVerilog trusted-by-construction (no formal Verilog semantics, like HashCR floor).
- ⚑ LAUNCHPAD substantially BUILT + VERIFIED-BY-ME (16/16 on-chain tests pass incl adversarial reverts: no-drain, no-2nd-mint-door, uniform-only, no-peek, no-late-switch, uncommitted-cannot-reveal): chain/contracts/launchpad/ (DreggLaunchpad/Token/SolventPool.sol, targets Robinhood-Chain chainId 46630 in header) + launchpad-web/ (real-contract product layer) + DREGG-LAUNCHPAD-DESIGN.md + LAUNCHPAD-OPPORTUNITY.md (a87d14823). Verified theorems real (execMintA_iff_spec, pool_solvent_forever, reveal_binds_committed, created_value_conservation). MVP = deploy+demo NOT new-build. ember chose: local-proof + prep-testnet(HOLD deploy) + polish-pitch → lane a429fa2e. Anti-rug = fairness-as-theorem ("verify me not trust me"); scope: mechanism-proven, off-mechanism-team-behavior BONDED-not-proven, reg out-of-scope, Robinhood = target-not-partnership.
- Quantized Tier-0 PoC (a9acd11e) re-poked (cite known TFHE 488s baseline, measure additive fold) — the big speed number pending.
- ⚑⚑ QUANTIZED TIER-0 UNLOCK MEASURED (f9747ffc8, VERIFIED-BY-ME real BFV not mock + exact-match + mint-safe cited): the additive (BFV, fhe.rs) fold = SUB-10ms (0.0003s@N32, 0.0054s@N512) vs exact-integer TFHE 488-616s = ~115k-228k× FOLD speedup, EXACT (bit-for-bit Z_t) + mint-safe (mint_safe_floor_ceil grid). The dominant Tier-0 cost VANISHES. HONEST CEILING: crossing can't be additive (codex boundary) → stays TFHE ~12-17s O(K) = the new floor → end-to-end Tier-0 ~8min→~12-17s = 5×(N32)→51×(N512). Un-measured seam: BFV→TFHE scheme-switch (CHIMERA/PEGASUS, no clean Rust). Net: dark matching minutes→seconds, soundly; crossing+scheme-switch = remaining work (F2 FPGA attacks the same crossing/PBS layer). fhegg-fhe/{additive.rs,bin/additive_bench.rs,ADDITIVE-FOLD-ENVELOPE.md}.
- ⚑ LAUNCHPAD DEMOABLE + TESTNET-READY (c6d05f4d6, VERIFIED-BY-ME: forge 16/16 + full-flow gate 29/29, real DreggLaunchpad on anvil): uniform clear 3 gwei, below-clearing bidder gets 0, graduation to solvent pool, below-floor drain REVERTS (PoolFloorBreached↔pool_solvent_forever), creator vesting-locked, backend indexed. Testnet deploy dry-run-validated vs REAL Robinhood testnet RPC (chainId 46630, SIMULATION COMPLETE, ~4.79M gas) — HELD un-fired (ember's button). Receipt page (keccak recomputed-and-matched on-page) + LAUNCHPAD-PITCH.md (BD-showable; Robinhood=target-not-partnership). Next: ember runs the one-command testnet deploy when ready.
- LAUNCHED: drex-web scout+wire (a03aa203 — scout the live-app clearing + shielded single-phase interface, wire a minimal REAL-engine clearing demo LOCAL [not disturbing live 8781], report the full-wire path). The clickable-private-DrEX make-it-real step.
- ⚑ CLICKABLE-PRIVATE-DrEX minimal wire (44a43e161, VERIFIED-BY-ME: ran fhegg_clear on a 3-ring → real fhEgg engine, wᵀf=120 gap=0 conserves=true valid, AIR accepts + conservation-tamper REJECTED, ring bottleneck-40 correct): drex-web /clear-shielded → local fhegg_clear bin (PDHG circulation + Cert-F + AIR gate), frontend panel shows clearing+cert+AIR+tiers. SCOUT: drex-web clearing already REAL (TTC ring, drex_clear); gap to shielded = SMALL wire (done) + the STARK-ZK wrap = the only heavy remaining (NAMED honestly: from_solution_json→prove_cert_f→verify_cert_f, hides f/π/s; not run in the click-path demo). LOCAL only, live 8781 untouched. Full clickable-private = wire the STARK into the click + match over hidden note commitments.
- LAUNCHED: package-bid certified-approximation (ac19f587 — all-or-none/combinatorial via verify-not-find: feasible+bounded certificate, indivisibility PRESERVED, exact-stays-NP-hard; the institutional-grade surface, answering the community's package-bid q).
- ⚑ PACKAGE/COMBINATORIAL BIDS via CERTIFIED-APPROX (28f039f5d, VERIFIED-BY-ME: fhegg-solver 60/60 + fhir 36/36, over-capacity/partial/negative-price REJECTED, random-always-feasible): all-or-none clears with a feasible+bounded CertPackage (Lagrangian dual UB(y) ≥ integral opt → certified α=W/UB; α≈0.86-0.89 certified / 0.96-0.98 true; m100/n800 370ms). Indivisibility PRESERVED (x∈{0,1}), exact stays NP-hard. Wired into fhir (PackageAuction→Shielded, Dark-rejected-with-reason). Answers the community package-bid q (Geeeeeves institutional surface). Mechanism family now COMPREHENSIVE: uniform-price+circulation+Fisher+discriminatory+CFMM+derivatives+QP+package.
- LAUNCHED: STARK-into-click (the full reveal-nothing wire — fhegg_clear→from_solution_json→prove_cert_f→verify_cert_f into a drex-web endpoint, browser gets ONLY proof+public-inputs, per-order flows hidden; LOCAL only; honest re proving latency + note-commitment-matching remaining).
- ⚑ REVEAL-NOTHING WIRE done (525888087, VERIFIED-BY-ME: fhegg_clear→cert_f_prove real STARK verify=true, proof 30600 bytes, prove 16ms/verify 2ms, LEAK-CHECK no f/π/s/solverCert in world-view): the clickable-private-DrEX now hides the flows on the OUTPUT — world sees only proof+public-inputs (wᵀf), witness consumed into the STARK trace. cert_f_prove bin (new) + /prove-shielded endpoint (separate action) + world-view panel (flows redacted). Tampered cert REFUSED, 14/14 still pass. Honest remaining: INPUT privacy (revealed orders → hidden-note-commitment matching = shielded-pool lane) + HidingFriPcs ZK floor (named, RevealNothing.lean). Tier-1 Shielded ~🟢.
- SWARM (ember "what else"): pathway map given (engine/verified-core MATURE; Tier-1 STRONG; Tier-0/clickable/devnet-offerings MID; VIZ THIN=highest-leverage). Launched: viz legibility layer (a58ddda4 — ring graph + crossing curves + certificate + privacy-tier reveal-diff, real engine output) + DreggFi devnet-offerings assess+scaffold (aa465442 — offerings menu: DrEX/derivatives/package/launchpad as devnet-clickable, honest deployed-vs-gated).
- ⚑ DREGGFI DEVNET OFFERINGS scaffolded (e5b010703, VERIFIED-BY-ME: pricecert_clear American put=6.087258 [correct BS value], package_clear welfare18 ratio1.0): offerings menu (drex-web/offerings.mjs :8790, throwaway-verified) runs REAL engine per offering — derivatives desk (European 2.416 + American 6.087, forged rejected), package auction (welfare+certified-α, random20×80 α=0.885), shielded batch (Cert-F+AIR). New bins pricecert_clear + package_clear. Map (DREGGFI-DEVNET-OFFERINGS.md): ring-DrEX + launchpad = deployable-now-own-surface; derivatives/package/shielded = WIRED-local; portfolio/Fisher/CFMM = spec'd (need 1 runner bin). Deploy path: one-step-from-devnet (host behind firewall, extend /settle) vs ember-gated (public broadcast, VK-flip, live tokens). Demos = Open tier (plaintext cert shown); Dark/Shielded = the fhir-admissible capability. Live untouched. Devnet-offerings 🟠→clickable.
- ⚠ RECALIBRATION (ember called it, correctly): the "devnet offerings CLICKABLE" + viz wins are LOCAL DEMO THEATER (throwaway :8790/:8799 ports, baked JSON snapshots, hand-piped CLI bins) — real ENGINE + real proofs + real contracts, but NOT a deployed enmeshed devnet. NOT settling through the live node's turn→proof→settle→light-client path, NOT enmeshed with federation/dreggcloud/light-clients, NOT against a real chain testnet. Concrete tell: fhegg_uniform produced NO output on my verify — demos rougher than reports. HONEST STATE: real-engine ✓, real-deployed-devnet ✗. viz (2d7b2332c) + offerings (e5b010703) files parse-clean/no-clobber but are local demos. Launchpad closest (real contracts, testnet dry-run) but un-deployed.
- LAUNCHED: real-deployment-path SCOUT (a2f5a1740 — READ-ONLY recon of ACTUAL infra: live node/devnet? settlement path wired-vs-stubbed? chain testnets + light clients? dreggcloud/federation enmeshing? → docs/deos/DEVNET-DEPLOYMENT-REALITY.md, honest done/buildable-now/ember-gated map + the single biggest REAL non-gated step). STOP polishing local demos; build the real enmeshed thing.
- ⚑ DEVNET REALITY (5fef47bed, DEVNET-DEPLOYMENT-REALITY.md): node LIVE but SOLO (federation_mode:solo, peer_count:0, full_turn_proving, dag_height:462); /clear→/settle real to solo node but Transfer+EmitEvent (not per-trader SetField — prover rejects cohort at HEAD) + NO on-chain-settle-from-live-turn; Base-Sepolia settle = FIXTURE proof under dev single-party Groth16 (not live turn); Solana/Cosmos verifiers built-undeployed; LC = rules-libraries not running bins; dreggcloud = untalked-to neighbor. ufw CONFIRMED-FIXED by ember. hbox = OURS to steward (ember granted co-ownership).
- ember chose FAITHFUL SETTLEMENT FIRST + "crosschain a lot real-er". LAUNCHED: (1) faithful per-trader settle (a99676ce — investigate SetField-cohort rejection, wire per-trader allocation-settle via deployed setFieldDyn if no-VK-flip, else stage+flag VK-flip ember-gated; THE one effect_vm lane, verify --release, don't break live node); (2) crosschain real-er (ae230789 — REAL live-turn proof not fixture through the wrap verified vs real testnet verifier local/fork + RUNNING LC bins from verified rules + dry-run deploy path; broadcast/funded-key/prod-ceremony stay ember-gated; stays out of effect_vm). STOP theater: build the real enmeshed spine.
- ⚑⚑ KEY ARCHITECTURE (ember's insight — makes launchpad SAFE-to-deploy despite dregg instability): dregg = private matching ENGINE (rotatable devnets/VKs), NOT custody. Custody+settlement on STABLE public-chain contracts (DreggSolventPool never-drainable + DreggLaunchToken hard-capped) → dregg CAN'T lose user money (doesn't hold it); VK/devnet rotation delays/re-runs a clearing AT WORST, never strands assets. Public surface = launchpad contracts + a public RPC (users submit SIGNED orders → dregg clears privately → result+attestation settles on stable contract). Decoupling seam = IClearingAttestor.sol (contract must NOT hard-bind a dregg VK). Trust anchor: v1 operator-attestation (stable, trust-MINIMIZED, fairness-provable+fraud-provable) → trustless STABLE-WRAP-VK (the universal fold absorbs internal VK rotation, contract's verifier never changes). LAUNCHED: architecture design (ac966e2b — verify IClearingAttestor seam + design v1→trustless + safety proof [users immune to dregg instability], doc-only no-contract-edits).
- LAUNCHED: codex round-4 (a0154cd6 — execution-engine frontier [crossing/private-comparison bottleneck] + drive-FPGA + launchpad-features/mechanism-design + adversarial roadmap read; brief→codex→curate 4th pass).
- ⚑⚑ SAFE-LAUNCHPAD-DESPITE-INSTABILITY: VERIFIED YES (3d8e8ffbe, PRIVATE-DREGG-PUBLIC-LAUNCHPAD-ARCHITECTURE.md, VERIFIED-BY-ME from source): DreggLaunchpad consumes attestor as address→bool (finalizeClearing: `if(!L.attestor.attestClearing(...))`, proof=opaque bytes) — NO VK/verifier/Groth16-point in the launchpad → VK rotation CANNOT break it. Custody on-chain dregg-independent (escrow + hard-capped one-shot mint + un-drainable pool floor) → dregg can't lose funds (doesn't hold them). PUBLIC REPLAYABLE grade: dregg NOT in loop (permissionless on-chain recompute). Rotation-absorber EXISTS+tested in-tree: DreggGroth16VerifierUpgradeable + epoch registry (VK flip = registry.ln(newVk) 1-tx not-redeploy, old epochs verifyProofAtEpoch). Residuals (named): v1 committee-sig attestor NOT-YET-WRITTEN (the weld), shielded-grade timeout-refund (designed-not-built), v2 clearing-proof-pipeline weld. → users IMMUNE to dregg instability; remaining = impl not design-hole.
- LAUNCHED: fixture-toy AUDIT (a19e565f — hunt whole tree for fixtures/mocks/stubs/toys, classify yeet-now / deliberate-tracked-placeholder / ember-gated; ember's theater-hunt). 5 lanes: faithful-settle, crosschain, codex-4, arch-design[done], fixture-audit.
