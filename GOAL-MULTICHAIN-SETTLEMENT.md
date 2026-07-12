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
- 07-12 ~3:40am: circuit-prove STILL churned (9 uncommitted; vk-epoch availability-weld commit aa282f8c0 35min ago;
  stark-kill carrier flag-day). Wrap/fold stay blocked. Doing directed genuine progress: CWIA code-hash hardening
  for the Base fault-proof anchor (reconstruct the game proxy code-hash from the AggregateVerifier impl + immutable
  args vs the fixture constant; KAT bar = reproduce the LIVE game code-hash, else honest residual). Fable running.

## ⚑ PLATEAU NOTE (07-12 ~3am): unblocked multichain work is COMPREHENSIVELY done.
Thread 3 + all its refinements shipped (edges, wire, multi-network, narrowing, binding TRILOGY, Base legacy +
LIVE fault-proof finality, Cosmos bisection, Electra rotation, + a real alloy-trie security finding). The MARQUEE
remaining value — thread 1 (wrap shrink-layer, ~5M→~1-2M) + thread 2 (rung-3 fold) — is BLOCKED on circuit-prove
(stark-kill's carrier flag-day, now 10 uncommitted files, ~90min ongoing). I CANNOT unblock it (another terminal's
active work; proceeding despite churn = collision risk, against discipline). Pacing: re-poll circuit-prove each
wakeup; seize the wrap the instant it quiets. Meanwhile: e2e-eth validation + remaining small refinements
(finalization-window, ADR-036 Cosmos, upstream the alloy-trie fix — the last is outward-facing, ember-gated).
