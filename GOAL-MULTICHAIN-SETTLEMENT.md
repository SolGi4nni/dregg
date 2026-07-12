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
