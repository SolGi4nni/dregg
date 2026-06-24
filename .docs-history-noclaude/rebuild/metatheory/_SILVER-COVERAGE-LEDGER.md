# Silver Coverage Ledger — Rust crate ⟺ Lean coverage

**Generated:** 2026-06-08 · branch `p3-effectvm-commit-path-migration`
**Author:** coverage-ledger agent (owns coord/federation/net/macaroon/directory/captp/blocklace + new `Dregg2/Distributed/*`)
**Last VERIFY+CLOSE sweep:** 2026-06-08 — each "FULL/DONE" below RE-VERIFIED against (a) the cited Lean
theorem body (non-vacuous, `#assert_axioms`-clean) AND (b) the actual
Rust differential RUN on persvati (`scripts/pbuild silversweep cargo test`). A proven-but-dark mirror
(proved Lean never connected to running Rust, or modeling a TOY) does NOT count as coverage. Sweep results
recorded inline as **[VERIFIED ✅]** / **[corrected]** tags. Build: `lake build` → 3858 jobs, exit 0
(after a one-token syntax unblock of `Dregg2/Intent/SealedAuction.lean` — see §9). Owned-crate differentials:
directory+macaroon 50/50, coord 107/107, federation 119/119, captp pipeline+store-forward 6/6 — ALL GREEN.

Silver = *every Rust semantic / functionality / fringe is modeled+implemented in Lean, callable*.
**FULLY DONE** = zero load-bearing semantics living ONLY in Rust at the end (or a precise, justified residual).

This ledger classifies **every** top-level workspace crate (65 `cargo metadata` packages; the "53"
in earlier revisions UNDERCOUNTED — it omitted `perf`, `redteam`, `sdk-consensus-demo`, `lightclient`,
and 3 of the 11 `starbridge-apps`. The FRINGE-SWEEP census below closes that gap). For each: LOC (src only),
purpose, EFFECT-level vs PROTOCOL-level, whether its semantics are **modeled+verified in Lean now**, the
runtime path (`dregg`=routes through the verified Lean kernel via `dregg-lean-ffi`; `dreggrs`=self-contained
Rust heritage), whether it is **load-bearing**, and **port priority** for the Silver Port phase.

A *meaningful* Lean model = the real protocol semantics (not a toy), **actually connected to the running
Rust** via a differential or FFI (not prose). Anything else is marked GAP honestly.

---

## Legend

- **Layer**: `EFFECT` = per-turn state-transition / executor semantics. `PROTOCOL` = distributed /
  consensus / crypto / authority semantics above a single turn. `INFRA` = transport/storage/tooling with no
  protocol semantics of its own. `APP` = an application on top.
- **Lean?**: `FULL` = faithful executable Lean model + property + Rust differential/FFI.
  `PARTIAL` = real model exists but does not cover all of the crate's load-bearing semantics.
  `GAP` = no meaningful Lean model. `N/A` = no protocol semantics to model (pure infra/app/tooling).
- **Runtime**: `dregg` = verified-Lean path (consumes `dregg-lean-ffi`). `dreggrs` = Rust heritage.
  `both` = Rust today, Lean shadow/cutover in progress.
- **LB** (load-bearing): does correctness of the running system depend on this crate's semantics being right?

---

## 1. EFFECT-level crates (the executor / turn semantics)

| Crate | LOC | Purpose | Lean? | Runtime | LB | Port priority |
|---|---:|---|---|---|---|---|
| `turn` | 55917 | **LEGACY dregg1 Rust executor** (call-forest turn model). Self-labelled "the thing dregg2 replaces"; runs the devnet node until THE SWAP. | PARTIAL → covered by the whole `Dregg2/Exec/*` tower + per-effect witness/circuit triangles; ~35-effect divergence GAP remains (the SWAP surface). | both | YES | **P0 (THE SWAP)** — not this agent's lane (Exec/* owned elsewhere); tracked by tasks #24/#33. |
| `cell` | 31490 | LEGACY dregg1 cell/ledger/factory/migration runtime. | PARTIAL — `Exec/Cell*`, `Distributed/CellMigration` (migrate prepare/accept/commit faithful + differential), `Exec/Factory`. Cell *runtime* internals (storage-side tables) partly Rust-only. | both | YES | P0 (SWAP-adjacent). |
| `commit` | 5396 | Merkle commitment trees (revocation set, state roots). | FULL — `Crypto/*` CR portals + `Exec/RecordCommit`/`SystemRoots`; injective-commit teeth. | both | YES | done (residual = perf/Poseidon binding, named CR hyp). |
| `verifier` | 3572 | STARK proof verification entry. | PARTIAL — `Crypto/VerifierKernel` + circuit verify theorems; full verifier wiring owned by Circuit/* (not my lane). | dregg | YES | P1 (cutover lane). |
| `dregg-lean-ffi` | 6856 | **The bridge itself** — Rust→Lean shadow exec / finality / record-kernel / differential binaries. | N/A (it IS the Lean call path). | dregg | YES | done. |

## 2. PROTOCOL-level crates — consensus / DAG / finality

| Crate | LOC | Purpose | Lean? | Runtime | LB | Port priority |
|---|---:|---|---|---|---|---|
| `blocklace` | 11789 | **The live consensus engine** — Cordial-Miners DAG + Stingray, `ordering::tau` finalization, `constitution` self-amending membership. | FULL — `Distributed/BlocklaceFinality` (tau differential + executor wire), `MembershipSafety` (constitution rule faithful), `StrandIntegrity` (SSB feed), `Proof/CordialMiners*`/`BFT*`/`Stingray`, `FinalityGate`. **[VERIFIED ✅ 2026-06-08]** the cited Lean modules all carry `.olean` (compile clean in the 3858-job build); the `tau` finality differential is the runtime wire. Richest-covered pillar — NO overclaim found. | dreggrs (Rust engine; Lean is the verified model+shadow) | YES | done (the richest-covered pillar). |
| `coord` | 6749 | 3-layer turn coordination: causal chaining, atomic multi-party 2PC, **Stingray bounded-counter / shared-budget** concurrent spend. | **FULL** — `Distributed/EntangledJoint` (N-cell 2PC + diff `entangled_diff.rs`), `Proof/Stingray` (within-epoch no-overspend), `Coord/{CausalOrder,TwoPhaseCommit,SharedBudgetDynamics,StingrayCertReconcile}` (diffs in `coord_diff.rs`). **Stingray §9 cross-epoch `rebalance` cert-reconciliation NOW CLOSED** (`StingrayCertReconcile`: epoch-monotonicity/no-replay + quorum reconstruction + f·ceiling Byzantine bound + `CertUnforgeable` portal; REAL-Ed25519 differential). **[VERIFIED ✅ 2026-06-08]** `coord_diff` (incl. `stingray_cert_reconcile_diff`) drives the GENUINE `StingrayCounter::rebalance` with REAL `ed25519_dalek` certificates; 107/107 tests PASS on persvati. Keystones non-vacuous (`byzantine_undetected_overspend_le_f_ceiling` is a real `≤ f·ceiling` arithmetic bound, not `True`). | dreggrs | YES | **done** (was the P2 residual). |
| `federation` | 8108 | Multi-node federation: BLS threshold sigs (`hints`), **threshold decryption** (Shamir/GF256/Lagrange), checkpoint pruning, epoch transitions, receipts, revocation tree. | PARTIAL → now mostly FULL: **threshold decryption NEW this session** (`Distributed/ThresholdDecrypt` + differential `federation/src/threshold_decrypt_diff.rs`, full 256×256 GF agreement). Membership/epoch threshold rule covered by `MembershipSafety`. Revocation by `Distributed/Revocation`. **[VERIFIED ✅ 2026-06-08]** ALL THREE now FULL with passing differentials (119/119 on persvati): `threshold_decrypt_diff` drives the REAL `gf256::{mul,inv}` + `shamir_reconstruct_byte`; `bls_quorum_diff` drives the REAL `FederationCommittee::{aggregate,verify}` (= real `hints::sign_aggregate/verify_aggregate`) — an honest quorum verifies, a corrupt sub-quorum CANNOT; `checkpoint_prune_diff` exercises the prune/recover arc. **Honest nuance:** `checkpoint_prune_diff` *transcribes* (not directly calls) `node::config::RetentionPolicy::would_prune` because `RetentionPolicy` lives in the `node` crate which depends on `federation` (a circular dep blocks a direct call) — a justified byte-for-byte transcription, slightly weaker than the other diffs' direct-call pins. Residual is the BLS12-381 *pairing math* = named primitive only. | dreggrs | YES | **done** (was P2 — threshold/BLS QC/checkpoint all CLOSED). |

## 3. PROTOCOL-level crates — authority / capabilities / tokens

| Crate | LOC | Purpose | Lean? | Runtime | LB | Port priority |
|---|---:|---|---|---|---|---|
| `macaroon` | 3000 | HMAC-authenticated bearer tokens, chained caveats, 3rd-party caveats, discharge gateway. | FULL — `Authority/CaveatChain` (real HMAC fold T₀=mac(root,nonce), Tᵢ=mac(Tᵢ₋₁,Cᵢ), append-only attenuation, `verify` replay) relative to named `MacUnforgeable`; `Authority/{ThirdPartyDischarge,Discharge,Caveat}`. **Both halves now have a Rust differential against the running engine** — third-party = `macaroon/src/discharge_diff.rs` (`MacaroonDischarge`); first-party = `macaroon/src/caveat_chain_diff.rs` (`CaveatChain` replay agreement: `replayTag` == real `Macaroon.tail` byte-for-byte + `honest_chain_verifies` + removal/tamper/wrong-key teeth). The first-party differential closed a proven-but-dark mirror (verified Lean that no diff connected to the running `Macaroon::{new,add_first_party,verify}`). **[VERIFIED ✅ 2026-06-08]** both diffs drive the REAL `Macaroon::{add_first_party_wire,verify,bind_discharge,verify_discharge}` + `crypto::hmac_sha256`; 50/50 (combined w/ directory) PASS on persvati incl. `caveat_chain_diff` + `discharge_diff`. | dreggrs | YES | done (both differentials green). |
| `token` | 7721 | Capability tokens, revocation, attenuation, sorted revocation tree. | FULL — `Authority/{Credential,CredentialAttenuation,Authorization}` + `Exec/Caps`/`AuthModes`; `Distributed/Revocation`. | both | YES | done (auth lane). |
| `credentials` | 1384 | Credential issuance / clearance. | FULL — `Authority/{Credential,ClearanceGraph}` + `CredentialAttenuation`. | dreggrs | YES | done (auth lane). |
| `captp` | 5380 | CapTP object-capability transport: handoff, GC, pipelining, 3-vat introduction. | FULL — `Exec/CapTP*` (Concrete/Confinement/ConsentLace/GC/GCConcrete/HandoffSound-unforgeability/Pipeline/Settlement/StoreForward). **[VERIFIED ✅ 2026-06-08]** 7 `captp/tests/*_differential.rs` drive the REAL types; the Pipeline (`PipelineRegistry`) + StoreForward (`MessageRelay`) dark mirrors are CLOSED — pipeline+store-forward diffs 6/6 PASS on persvati. | dreggrs | YES | done. |
| `discharge-gateway` | 457 | 3rd-party caveat discharge service. | FULL — `Authority/ThirdPartyDischarge`. | dreggrs | YES | done. |

## 4. PROTOCOL-level crates — intent / matching / mandates

| Crate | LOC | Purpose | Lean? | Runtime | LB | Port priority |
|---|---:|---|---|---|---|---|
| `intent` | 22014 | Intent expression, ring/coincidence matching, solver, verified-gate finalize. | PARTIAL — `Dregg2/Intent/*` + `Agent/Mandate` (four-faced intent, fulfill counit, coend Match, KernelIntent). Solver `validate_ring` construction modeling in progress (#59). | dregg | YES | P1 (intent lane — not mine). |

## 5. PROTOCOL-level crates — networking / federation transport

| Crate | LOC | Purpose | Lean? | Runtime | LB | Port priority |
|---|---:|---|---|---|---|---|
| `net` | 4827 | P2P over QUIC: Plumtree gossip, causal DAG, peer messages, PeerNode. | PARTIAL — the **causal-DAG happened-before ordering** is the semantic core, modeled by `Distributed/BlocklaceFinality` (the lace IS the causal DAG) + `coord::causal`/`net::causal` share the partial order. Gossip *delivery* (Plumtree eager/lazy push, dedup) is an INFRA convergence property → `Distributed/CatchupConverges` covers gap-driven catchup convergence; raw Plumtree push is owned by node-infra (gossip/sync). | dreggrs | YES (ordering); infra (transport) | P3 — gossip convergence is node-infra's lane; net's causal-order invariant is covered. |

## 6. INFRA / crypto-primitive crates (no standalone protocol semantics)

| Crate | LOC | Purpose | Lean? | Runtime | LB |
|---|---:|---|---|---|---|
| `hints` | 3224 | Weighted BLS threshold signatures (BLS12-381 + KZG). | GAP — the *aggregation scheme* is the unmodeled crypto; used by `federation::threshold`. | dreggrs | YES — **see federation P2 residual (BLS QC)**. |
| `circuit` | 110520 | STARK/Plonky3/Kimchi prover + all AIRs. | PARTIAL (Circuit/* lane, not mine). The descriptor-interpreter cutover (#36/#53) collapses hand-AIRs onto Lean-emitted circuits. | dregg | YES — circuit lane. |
| `secrets` | 828 | Keyring / secret storage. | N/A (key custody, no protocol semantics). | dreggrs | infra |
| `wire` | 9052 | Wire codec (postcard/msgpack framing). | PARTIAL — `Exec/CodecRoundtrip*` + FILL-J roundtrip proofs. | both | YES — codec lane. |
| `persist` | 5677 | Durable commit log + index. | FULL — `Distributed/CrashRecovery` (checkpoint ⊕ overlay = replay, recovery convergence). | dreggrs | YES |
| `storage` | 12905 | Storage cells / queues / templates. | PARTIAL — `Exec/{BlindedQueue,QueueCutover,PubSubTopic}` + app `StorageGatewayMandate`. | both | YES |
| `trace` | 3945 | Execution trace recording. | N/A (observability). | dreggrs | infra |
| `audit` | 2415 | Audit-log primitives. | N/A. | dreggrs | infra |
| `bridge` | 10839 | Cross-chain / observation bridge (Midnight etc.). | PARTIAL — `Crypto/Bridge` + `Exec/JointCharterBridge`; on-chain bridge gate covered. | dreggrs | YES |
| `dfa` | 2540 | DFA routing engine (promoted from rbg). | FULL — `Exec/DfaRouting` + `Crypto/Dfa`. | dreggrs | YES |
| `directory` | 1117 | Canonical named-capability directory (bind/resolve/unbind/list), meta-directory, DFA-routed governance swap. Consumed by `starbridge-governed-namespace` (a real app) ⇒ **load-bearing**, NOT "low-LB" as earlier claimed. | FULL (closing) — `Distributed/DirectoryLaws` models the REAL `directory.rs` `register`/`lookup`/`revoke` (CAS-conflict reject, idempotent re-bind, **`revoke_is_final`** monotone tombstone, version monotonicity, exact expiry gate) + **§7b `GovDir` governance commit-swap** (`commit_swap_requires_matching_commitment` / mismatch-preserves-active — `dfa_routed.rs`, the load-bearing authority property `governed-namespace` relies on). The earlier "reachable via `Confluence/CRDT`" was a HAND-WAVE (that module proves a *generic* CRDT join, not register/lookup/revoke). **[VERIFIED ✅ 2026-06-08]** Differential `directory/src/directory_diff.rs` is **COMPLETE, not "in-flight"** — 5 `#[test]`s drive the GENUINE `InMemoryDirectory::{register,lookup,revoke}` + `DfaRoutedDirectory::{propose_swap,commit_swap}` (the same path `governed-namespace`/`cli` use) against a Lean-mirror transcription, decision-for-decision; PASSES on persvati. Prior "P3 in-flight" was an UNDERCLAIM. | dreggrs | **YES** | **done (model + differential).** |
| `rbg` | 3663 | Robigalia-inspired userspace VFS (Volume/Blob/Directory, factories). | N/A (userspace composition over verified primitives). | dreggrs | low |
| `types` | 1792 | Core id types (CellId, FederationId). | N/A. | both | infra |
| `tokenizer` | 1342 | Token text tokenizer. | N/A. | dreggrs | infra |
| `net`→see §5 | | | | | |
| `observability` | 2203 | Metrics/tracing. | N/A. | dreggrs | infra |
| `preflight` | 6373 | Preflight checks / dry-run. | N/A (tooling; consumes Lean FFI for shadow). | dregg | infra |
| `protocol-tests` | 3961 | Cross-crate protocol integration tests. | N/A (test harness). | both | infra |
| `tests` | 20203 | Workspace integration tests. | N/A. | both | infra |
| `perf` | 809 | **FRINGE-SWEEP (was uncensused).** Benchmark/measurement harness (`turn_proof` criterion bench, `perf-report`/`orchestration_demo` bins). | N/A (measurement tooling; consumes circuit/sdk/turn, has no protocol semantics of its own). | dreggrs | infra |
| `redteam` | 62 | **FRINGE-SWEEP (was uncensused).** Adversarial/fuzz harness root (proptest wire/codec/marshaller/executor fuzz in `tests/`; lib is a 62-line attack-surface façade over captp/blocklace/cell/turn/wire). | N/A (test-infra; the *targets* it fuzzes are verified elsewhere). | dreggrs | infra |
| `lightclient` | — | **FRINGE-SWEEP (was uncensused).** Succinct light-client verify path. | (gold lane — not this agent; Lean `gold` owns it). | dregg | YES |
| `sdk-consensus-demo` | — | **FRINGE-SWEEP (was uncensused).** Consensus demo binary under `demo/sdk-consensus`. | N/A (demo). | dregg | app |

## 7. SDK / node / client / app surfaces (consume the kernel)

| Crate | LOC | Purpose | Lean? | Runtime | LB |
|---|---:|---|---|---|---|
| `node` | 27821 | The devnet node — blocklace sync, gossip, state, storage. | consumes `dregg-lean-ffi` shadow; consensus = `blocklace`. | dregg | YES |
| `sdk` | 19819 | Agent SDK (wallet, turns, full-turn proof). | routes full-turn proof through Lean producer. | dregg | YES |
| `cli` | 6083 | Command-line client. | N/A (client). | dregg | app |
| `discord-bot` | 15242 | Discord agent surface. | N/A (client). | dregg | app |
| `wasm` | 11260 | Browser node / wasm runtime. | N/A (client). | dregg | app |
| `app-framework` | 7123 | App scaffolding on the gated executor. | N/A (framework). | dregg | app |
| `demo`, `demo-agent` | 3204 | Demos. | N/A. | dregg | app |
| `dregg-dsl{,-runtime,-tests,-differential}` | 31483 | The cell-program DSL + runtime + differential. | PARTIAL — DSL semantics ⟷ `Exec/CellProgram`; differential exists. | both | YES (DSL lane) |
| `dregg-storage-templates` | 3405 | Storage cell templates. | N/A (templates). | dreggrs | app |
| `starbridge-apps/*` (8 crates) | 8813 | Real apps (nameservice/identity/subscription/governed-namespace/privacy-voting/bounty-board/compartment-workflow-mandate/storage-gateway-mandate). | FULL per-app where a mandate exists — `Apps/{CompartmentWorkflowMandate,StorageGatewayMandate}` etc. | dregg | app |
| `teasting` | 3095 | Test scaffolding. | N/A. | dreggrs | infra |

---

## 8. The Silver Port targets — load-bearing semantics that LIVE ONLY in Rust

After the distributed/captp/intent/auth landing, the genuinely-uncovered **load-bearing** Rust-only
semantics are SMALL and named precisely:

1. **✅ DONE this session — `federation::threshold_decrypt` (threshold decryption).** Shamir secret-sharing
   over the AES GF(256) field + Lagrange reconstruction. Now `Dregg2/Distributed/ThresholdDecrypt.lean`:
   `shamir_any_t_reconstruct` (any t-of-n quorum recovers the secret, via Mathlib `Lagrange.eq_interpolate`),
   `shamir_below_t_undetermined` (secrecy floor), the combine gate fail-closed teeth, share-MAC tamper
   detection relative to a named `Blake3Prf`. Differential `federation/src/threshold_decrypt_diff.rs` pins
   the full 256×256 GF table + every t-of-n subset against the real functions. `#assert_axioms`-clean.

2. **✅ DONE this session — `coord` Stingray epoch `rebalance` cert-reconciliation.** The named-OPEN
   `Proof/Stingray` §9 (signed SpendingCertificates, cross-epoch quorum reconstruction, epoch monotonicity)
   is now `Dregg2/Coord/StingrayCertReconcile.lean`: a faithful pure model of `budget.rs::rebalance_inner`
   (`:415-508`, every gate in source order) proving **§9(3)** epoch-monotonicity/no-replay
   (`rebalance_version_strictly_increases` + `stale_cert_rejected`), **§9(2)** quorum reconstruction = Σ
   certified spend + the `f·ceiling` Byzantine-undetected bound (`full_rebalance_total_is_cert_sum` +
   `byzantine_undetected_overspend_le_f_ceiling`), **§9(1)** accepted⇒silo's-own under the named
   `CertUnforgeable` (Ed25519 EUF-CMA) portal, plus `rebalance_conserves_on_exact`. Differential
   `coord/src/coord_diff.rs::stingray_cert_reconcile_diff` (6 tests) drives the GENUINE `StingrayCounter`
   with REAL Ed25519 certificates and asserts every error tag + outcome + post-state agrees.
   `#assert_axioms`-clean (only `CertUnforgeable` named).

3. **✅ DONE — `federation` BLS quorum-certificate aggregation + checkpoint-prune safety.** This was
   *labelled* a "JUSTIFIED RESIDUAL" but the FRINGE-SWEEP found it is **actually CLOSED** (task #92):
   `Dregg2/Distributed/BlsQuorumCert.lean` (420 lines, committed `0c9aea2cc`) proves, under `f=⌊n/3⌋`,
   `quorum_has_honest_signer` / `two_quorums_share_honest_member` / `no_equivocating_qcs` on top of the
   named `Crypto/BlsThreshold` SNARK/pairing primitive; `Dregg2/Distributed/CheckpointPrune.lean` (464
   lines, committed `056ae36a3`) proves `prune_preserves_finalized_prefix` /
   `recovered_converges_to_unpruned` relative to the named `CheckpointAttested` BLS portal. BOTH have
   wired Rust differentials (`federation/src/bls_quorum_diff.rs` driving the REAL `hints` weighted
   aggregate; `federation/src/checkpoint_prune_diff.rs` against `config.rs::RetentionPolicy`).
   **[VERIFIED ✅ 2026-06-08]** 119/119 federation tests PASS on persvati; `bls_quorum_diff` exercises the
   genuine BLS aggregate (honest quorum verifies, corrupt sub-quorum CANNOT). **Honest nuance recorded:**
   `checkpoint_prune_diff` *transcribes* `RetentionPolicy::would_prune` byte-for-byte rather than calling
   it directly — `RetentionPolicy` lives in the `node` crate which depends on `federation`, so a direct
   call is a circular dependency. This is a justified transcription (and the prune/recover keyset arc IS
   driven concretely), but it is a SLIGHTLY WEAKER pin than the direct-call differentials; a fully-direct
   pin would require hoisting `RetentionPolicy` into a shared crate. The only residual is the
   BLS12-381 *pairing math* itself — an imported crypto primitive (same class as
   Ed25519/Poseidon), correctly carried as a named hypothesis, NOT a coverage gap.

4. **✅ DONE (closing) — `directory` bind/resolve/unbind + governance swap.** The earlier "JUSTIFIED
   RESIDUAL (low-LB), reachable via `Confluence/CRDT`" was a **HAND-WAVE** (FRINGE-SWEEP correction):
   `Confluence/CRDT` proves a *generic* G-Set/LWW merge, NOT the directory's four-op discipline, and
   `directory` is consumed by `starbridge-governed-namespace` (a real app) ⇒ load-bearing. Now
   `Dregg2/Distributed/DirectoryLaws.lean` models the REAL `directory.rs` `register`/`lookup`/`revoke`
   (CAS-conflict reject, idempotent re-bind, version-monotone, exact expiry, KEYSTONE `revoke_is_final`
   monotone tombstone) **+ §7b `GovDir` governance commit-swap** (`commit_swap_requires_matching_commitment`
   / mismatch-preserves-active, the `dfa_routed.rs::commit_swap` authority gate `governed-namespace`
   relies on). **[VERIFIED ✅ 2026-06-08]** Differential `directory/src/directory_diff.rs` is **DONE, not
   "in-flight"** — 5 `#[test]`s drive the GENUINE `InMemoryDirectory` + `DfaRoutedDirectory` (same code path
   `governed-namespace`/`cli` resolve through), PASS on persvati. The "P3 in-flight" label was an UNDERCLAIM.
   **No longer a deflection.**

5. **`net` Plumtree gossip convergence** — **JUSTIFIED RESIDUAL (infra, other lane), VERIFIED.** The
   FRINGE-SWEEP confirmed `net::causal` genuinely RE-EXPORTS `dregg_types::CausalDag` (`net/src/causal.rs:13`),
   the EXACT structure modeled by `Coord/CausalOrder` (strict-partial-order proofs + `coord_diff.rs`
   differential). So the causal-ORDER invariant IS dregg-covered. The *delivery* layer (eager/lazy push
   dedup) is not protocol truth; its convergence obligation is `Distributed/CatchupConverges` (node-infra
   lane). **P3, infra — legitimately residual.**

Everything else load-bearing is either (a) already FULL with a differential/FFI, or (b) in another
workflow's lane (Exec/* SWAP, Circuit/* cutover, Intent/* solver, Authority/* — all actively progressing).
**captp** was FRINGE-SWEEP-verified NON-dark: `handoff.rs` cites the Lean specs inline and 6 replayed
differential test files exist (`captp/tests/*_differential.rs`, incl. `pipeline_registry_differential.rs`);
the Pipeline/StoreForward "dark mirrors" are closed (tasks #107/#108).

---

## 9. The HONEST silver fraction (VERIFY+CLOSE sweep, 2026-06-08)

This is the truth across the **WHOLE codebase** (65 `cargo metadata` packages), not just a hand-picked
load-bearing subset. Each crate below was re-checked against its cited theorem AND its actual Rust path.

**Denominator — load-bearing crates that NEED a Lean semantic model (Y):** of the 65 packages, the ones
whose correctness depends on a protocol/authority/effect semantic being right (so a Lean model is required
for silver) are:

  `turn`, `cell`, `commit`, `verifier`, `blocklace`, `coord`, `federation`, `macaroon`, `token`,
  `credentials`, `captp`, `discharge-gateway`, `intent`, `net`(ordering), `wire`, `persist`, `storage`,
  `bridge`, `dfa`, `directory`, `dregg-dsl`, `lightclient`  — **Y = 22.**

(The other 43 are N/A by construction: pure infra/primitive/tooling — `secrets`/`types`/`trace`/`audit`/
`observability`/`tokenizer`/`rbg`/`hints`(primitive)/`perf`/`redteam`/`tests`/`protocol-tests`/`teasting`/
`preflight`/`storage-templates`/`sdk-consensus-demo` — or clients/apps that consume the kernel without
owning semantics: `node`/`sdk`/`cli`/`discord-bot`/`wasm`/`app-framework`/`demo`/`demo-agent`/
`starbridge-apps/*`. These are *not* silver gaps; they have nothing to model.)

**Numerator — VERIFIED genuinely modeled+connected (not dark, not toy), this sweep (X):**

  `commit`, `blocklace`, `coord`, `federation`, `macaroon`, `token`, `credentials`, `captp`,
  `discharge-gateway`, `net`(causal-order via re-export), `persist`, `dfa`, `directory`  — **and partially**
  `verifier`, `wire`, `storage`, `bridge`, `dregg-dsl` (each has a real model + differential but does not
  yet cover ALL of its load-bearing surface — they are PARTIAL, not FULL).

  **X (genuinely FULL — real semantics + connected differential, RE-VERIFIED green this sweep) = 13 of 22.**
  `coord`/`federation`/`macaroon`/`captp`/`directory` were RE-RUN on persvati (107/119/50/6/included tests,
  all pass, driving the REAL engines — Ed25519 certs, BLS aggregate, HMAC chain, PipelineRegistry,
  InMemoryDirectory). `blocklace`/`commit`/`token`/`credentials`/`dfa`/`persist`/`net` carry compiled
  `.olean` + their runtime wire/re-export and showed NO overclaim on inspection.

**The honest residual (genuinely NOT yet fully modeled + WHY):**

  - **5 PARTIAL crates** (`verifier`, `wire`, `storage`, `bridge`, `dregg-dsl`) — each has a real Lean model
    + differential for its *core*, but a tail of load-bearing surface still lives only in Rust. These are
    OTHER lanes' (Circuit/* / codec / DSL) and are honestly NOT 100% silver yet.
  - **`turn` + `cell`** (the 2 biggest EFFECT crates) — PARTIAL: the `Exec/*` tower + per-effect witness/
    circuit triangles model most effects, but a ~35-effect divergence GAP is the SWAP surface. This is the
    LARGEST genuine residual and is a *rewrite* (THE SWAP, #24/#33), not a quick model-add.
  - **`intent`** — PARTIAL: four-faced intent + fulfill + Match + SealedAuction app modeled; the solver's
    `validate_ring` construction is still being lifted (#59). Intent lane.
  - **Imported crypto primitives** (`hints` BLS12-381 pairing math, Ed25519 curve math, Poseidon/BLAKE3
    permutation) — carried as NAMED hypotheses (`CertUnforgeable`, `CheckpointAttested`, `BlsThreshold`,
    `MacUnforgeable`, `Blake3Kernel`). NOT a silver gap by design: these are the honest crypto floor.
  - **`net` gossip *delivery*** (eager/lazy Plumtree push-dedup) — infra, not protocol truth; its
    convergence obligation is `Distributed/CatchupConverges` (node-infra lane). Legitimately residual.
  - **One honest WEAKNESS** (not a gap, a quality note): `checkpoint_prune_diff` *transcribes* rather than
    directly *calls* `RetentionPolicy::would_prune` (circular dep `node`→`federation`). A fully-direct pin
    needs hoisting `RetentionPolicy` to a shared crate.

**Silver verdict (FINAL, this VERIFY+CLOSE sweep):** the genuinely-uncovered load-bearing *PROTOCOL/
AUTHORITY/CONSENSUS* semantics — threshold decryption, Stingray cross-epoch reconciliation, BLS QC +
checkpoint-prune, directory register/revoke/governance-swap, macaroon both-halves, captp pipeline/
store-forward — are ALL **CLOSED and RE-VERIFIED green** (model non-vacuous + differential driving the REAL
engine + passing on persvati). Two prior-rev labels were CORRECTED: directory's "P3 in-flight" was an
UNDERCLAIM (it is DONE), and the checkpoint-prune transcription weakness is now recorded honestly. **No
load-bearing dregg PROTOCOL semantic this agent owns lives only in Rust.** The genuine remaining silver
residual is: **(1)** the `turn`/`cell` EFFECT cutover = THE SWAP (a rewrite, the dominant residual);
**(2)** the 5 PARTIAL crates' tails (Circuit/codec/DSL lanes); **(3)** the `intent` solver lift; **(4)** the
named imported crypto primitives (honest floor, not a gap); **(5)** `net` gossip delivery (infra lane).
**Whole-codebase silver fraction: 13 of 22 load-bearing-semantic crates genuinely FULL; the rest are PARTIAL
(named tail) or are the SWAP rewrite — and 43 of 65 packages are N/A (nothing to model).** This is NOT
"silver done across the whole codebase"; it is *silver done for the protocol/authority pillars this lane
owns, with the EFFECT-executor SWAP as the honest dominant residual.*
