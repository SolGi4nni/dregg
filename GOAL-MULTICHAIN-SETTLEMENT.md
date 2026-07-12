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

## Current thrust
Wave 1 LAUNCHED (Fable): gnark-multifield [wrap] · eth-edge (EVM U256>u128 refuse + post-Electra
rotation) · cosmos-edge (bank decode + bisection) · gov-narrow-tag (u128→u64 fail-closed +
multi-network ChainId) — each adversarially audited. + rung-3 fold-pilot grounding scout.
Deferred: workspace consolidation (root Cargo.toml churned by other terminals — do when quiet;
edge conversions use minimal-primitive-fields at the crate edge, so they DON'T need it).

## Next 3 moves
1. Launch gnark MultiField challenger (Fable) + rung-3 fold-pilot grounding scout (Fable).
2. Dep-check: can eth-lightclient/cosmos-lightclient join the workspace (member-not-default)? →
   decides the cross-chain edge-conversion shape.
3. Launch cross-chain edge lanes (shaped by #2) + widen-sockets.

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
- 07-12 Wave 1 launched (4 Fable lanes + audits): gnark-multifield, eth-edge, cosmos-edge, gov-narrow-tag.
  Waiting on completion.
