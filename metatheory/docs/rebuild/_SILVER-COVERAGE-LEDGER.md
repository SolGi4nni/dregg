# Silver Coverage Ledger — Rust crate ⟺ Lean coverage

**Generated:** 2026-06-08 · branch `p3-effectvm-commit-path-migration`
**Author:** coverage-ledger agent (owns coord/federation/net/macaroon/directory + new `Dregg2/Distributed/*`)

Silver = *every Rust semantic / functionality / fringe is modeled+implemented in Lean, callable*.
**FULLY DONE** = zero load-bearing semantics living ONLY in Rust at the end (or a precise, justified residual).

This ledger classifies **every** top-level workspace crate (53 members). For each: LOC (src only),
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
| `blocklace` | 11789 | **The live consensus engine** — Cordial-Miners DAG + Stingray, `ordering::tau` finalization, `constitution` self-amending membership. | FULL — `Distributed/BlocklaceFinality` (tau differential + executor wire), `MembershipSafety` (constitution rule faithful), `StrandIntegrity` (SSB feed), `Proof/CordialMiners*`/`BFT*`/`Stingray`, `FinalityGate`. | dreggrs (Rust engine; Lean is the verified model+shadow) | YES | done (the richest-covered pillar). |
| `coord` | 6749 | 3-layer turn coordination: causal chaining, atomic multi-party 2PC, **Stingray bounded-counter / shared-budget** concurrent spend. | FULL — `Distributed/EntangledJoint` (N-cell 2PC + differential `coord/src/entangled_diff.rs`), `Proof/Stingray` (`budget.rs`/`shared_budget.rs` faithful, no-overspend). **Residual:** per-epoch `rebalance` reconciliation (SpendingCertificate quorum) named-open in `Proof/Stingray` §9. | dreggrs | YES | **P2 (this agent's residual)** — rebalance epoch boundary. |
| `federation` | 8108 | Multi-node federation: BLS threshold sigs (`hints`), **threshold decryption** (Shamir/GF256/Lagrange), checkpoint pruning, epoch transitions, receipts, revocation tree. | PARTIAL → now mostly FULL: **threshold decryption NEW this session** (`Distributed/ThresholdDecrypt` + differential `federation/src/threshold_decrypt_diff.rs`, full 256×256 GF agreement). Membership/epoch threshold rule covered by `MembershipSafety`. Revocation by `Distributed/Revocation`. **Residual GAP:** BLS quorum-cert aggregation (`threshold.rs`/`receipt.rs` over `hints` KZG) + checkpoint-prune safety. | dreggrs | YES | **P2 (this agent)** — threshold decrypt DONE; BLS QC + checkpoint next. |

## 3. PROTOCOL-level crates — authority / capabilities / tokens

| Crate | LOC | Purpose | Lean? | Runtime | LB | Port priority |
|---|---:|---|---|---|---|---|
| `macaroon` | 3000 | HMAC-authenticated bearer tokens, chained caveats, 3rd-party caveats, discharge gateway. | FULL — `Authority/CaveatChain` (real HMAC fold T₀=mac(root,nonce), Tᵢ=mac(Tᵢ₋₁,Cᵢ), append-only attenuation, `verify` replay) relative to named `MacUnforgeable`; `Authority/{ThirdPartyDischarge,Discharge,Caveat}`. | dreggrs | YES | done (CaveatChain owned by auth lane). |
| `token` | 7721 | Capability tokens, revocation, attenuation, sorted revocation tree. | FULL — `Authority/{Credential,CredentialAttenuation,Authorization}` + `Exec/Caps`/`AuthModes`; `Distributed/Revocation`. | both | YES | done (auth lane). |
| `credentials` | 1384 | Credential issuance / clearance. | FULL — `Authority/{Credential,ClearanceGraph}` + `CredentialAttenuation`. | dreggrs | YES | done (auth lane). |
| `captp` | 5380 | CapTP object-capability transport: handoff, GC, pipelining, 3-vat introduction. | FULL — `Exec/CapTP*` (Concrete/Confinement/ConsentLace/GC/GCConcrete/HandoffSound-unforgeability/Pipeline/Settlement/StoreForward). | dreggrs | YES | done. |
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
| `directory` | 1117 | Canonical named-capability directory (bind/resolve/unbind/list), meta-directory, DFA-routed. | GAP (small) — the directory is a CRDT-flavored key→cap map; the **monotone/last-writer semantics** are reachable via `Confluence/CRDT` but no directory-specific model exists. Low LB (a lookup primitive over already-verified caps). | dreggrs | low | **P3 (this agent, optional)** — small; bind/resolve laws. |
| `rbg` | 3663 | Robigalia-inspired userspace VFS (Volume/Blob/Directory, factories). | N/A (userspace composition over verified primitives). | dreggrs | low |
| `types` | 1792 | Core id types (CellId, FederationId). | N/A. | both | infra |
| `tokenizer` | 1342 | Token text tokenizer. | N/A. | dreggrs | infra |
| `net`→see §5 | | | | | |
| `observability` | 2203 | Metrics/tracing. | N/A. | dreggrs | infra |
| `preflight` | 6373 | Preflight checks / dry-run. | N/A (tooling; consumes Lean FFI for shadow). | dregg | infra |
| `protocol-tests` | 3961 | Cross-crate protocol integration tests. | N/A (test harness). | both | infra |
| `tests` | 20203 | Workspace integration tests. | N/A. | both | infra |

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

2. **`coord` Stingray epoch `rebalance` reconciliation.** Within-epoch concurrent-spend safety is PROVEN
   (`Proof/Stingray`); the cross-epoch SpendingCertificate quorum reconstruction + epoch monotonicity is the
   named-open residue (`Proof/Stingray` §9). **P2.**

3. **`federation` BLS quorum-certificate aggregation** (`threshold.rs`/`receipt.rs` over `hints` KZG) and
   **checkpoint-prune safety** (`checkpoint.rs`: a checkpoint below a finalized height is safe to discard).
   The threshold-*signature* aggregation is the unmodeled crypto; the prune-safety is a finality corollary
   reachable from `BlocklaceFinality` + `CrashRecovery`. **P2.**

4. **`directory` bind/resolve monotone laws** — small, low-LB; a CRDT-flavored key→cap map. **P3 optional.**

5. **`net` Plumtree gossip convergence** — the *delivery* layer (eager/lazy push dedup). The causal-ORDER
   invariant is covered (the lace = the causal DAG); raw gossip convergence is node-infra's lane (`CatchupConverges`
   covers gap-driven catchup). **P3, infra.**

Everything else load-bearing is either (a) already FULL with a differential/FFI, or (b) in another
workflow's lane (Exec/* SWAP, Circuit/* cutover, Intent/* solver, Authority/* — all actively progressing).

**Silver verdict:** the protocol-semantic surface is ~90% covered with meaningful, connected Lean. The
residual load-bearing Rust-only semantics are the 5 items above; #1 is now closed. The big remaining
non-this-agent item is **THE SWAP** (turn/cell executor cutover) — a large rewrite, not a coverage gap.
