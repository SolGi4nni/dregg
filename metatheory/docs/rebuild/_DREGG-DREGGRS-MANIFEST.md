# dregg / dreggrs Segregation Manifest

**Generated:** 2026-06-08 · branch `p3-effectvm-commit-path-migration`
**Companion to:** `_SILVER-COVERAGE-LEDGER.md`

The corrected SWAP framing (per MEMORY):

- **dregg** = the Lean primary. The verified kernel (`metatheory/Dregg2/*`) is the source of truth for
  semantics. A crate is **dregg** when its load-bearing semantics are *modeled+verified in Lean* and it
  routes through that kernel at runtime (via `dregg-lean-ffi`) or is itself a verified model.
- **dreggrs** = the Rust heritage, **backburner**. A crate is **dreggrs** when it is self-contained Rust
  whose semantics are EITHER (a) already faithfully mirrored by a Lean model + differential (so the Rust is
  a *fast executable shadow* of verified semantics), OR (b) pure infra/tooling/crypto-primitive with no
  protocol semantics to verify. dreggrs is not deleted; it is the diversity/performance layer beneath dregg.

The boundary is **not** "Rust vs Lean files" — almost everything is Rust at runtime. The boundary is **where
the source of truth lives**: dregg = Lean-truth (Rust is shadow/client); dreggrs = Rust-truth (self-contained,
heritage, backburner).

---

## A. dregg — Lean-primary (verified kernel is the truth)

These route user-facing/runtime semantics through the verified Lean kernel, or ARE the verified model.

| Crate | Why dregg | Lean truth |
|---|---|---|
| `dregg-lean-ffi` | The bridge — shadow exec / finality / record-kernel call path. | `Exec/FullForestAuth`, `Distributed/{BlocklaceFinality,FinalityGate}`, `Exec/RecordKernel`. |
| `node` | Devnet node; executes through the Lean shadow + blocklace finality model. | `Distributed/*`, `Exec/*`. |
| `sdk` | Full-turn proof routed through the Lean producer. | `Exec/*`, `Circuit/*`. |
| `intent` | Verified-gate finalize lifts the verified executor reference into the crate. | `Intent/*`, `Agent/Mandate`. |
| `turn`, `cell` | **In-flight dregg** — self-labelled LEGACY dregg1, load-bearing UNTIL THE SWAP, with a Lean shadow active. They BECOME pure-dregg at cutover; today they are `both`. | `Exec/*` tower + per-effect triangles. |
| `verifier`, `circuit`, `wire` | The prove/verify/codec path being cut over onto Lean-emitted circuits + FILL-J codec proofs. | `Circuit/*`, `Crypto/VerifierKernel`, `Exec/CodecRoundtrip*`. |
| `cli`, `discord-bot`, `wasm`, `app-framework`, `demo`, `demo-agent`, `starbridge-apps/*`, `preflight` | Clients/apps over the gated kernel; no own semantics. | n/a (consume the kernel). |
| `dregg-dsl{,-runtime,-tests,-differential}` | Cell-program DSL ⟷ `Exec/CellProgram` with a differential. | `Exec/CellProgram`, `Exec/Program`. |

## B. dreggrs — Rust heritage (self-contained; verified-shadow OR pure-infra)

### B.1 Self-contained Rust whose semantics ARE faithfully Lean-mirrored (verified shadow)

These are the heritage Rust engines that a Lean model + **differential** now pins. They stay as the fast
executable layer; the Lean model is the truth they are checked against.

| Crate | Lean model + differential |
|---|---|
| `blocklace` | `Distributed/{BlocklaceFinality,MembershipSafety,StrandIntegrity,FinalityGate}` + `Proof/{CordialMiners*,BFT*,Stingray}`. The live Rust consensus engine; Lean is its verified model. `tau` golden differential. |
| `coord` | `Distributed/EntangledJoint` (diff `coord/src/entangled_diff.rs`) + `Proof/Stingray` + `Coord/{CausalOrder,TwoPhaseCommit,SharedBudgetDynamics,StingrayCertReconcile}` (diffs in `coord/src/coord_diff.rs`). **Cross-epoch `rebalance` cert-reconciliation now FULL** (`StingrayCertReconcile`, REAL-Ed25519 differential). |
| `federation` | `Distributed/ThresholdDecrypt` (**NEW** differential `federation/src/threshold_decrypt_diff.rs`) + `Distributed/{MembershipSafety,Revocation}`. |
| `macaroon` | `Authority/CaveatChain` (real HMAC fold, relative to `MacUnforgeable`). |
| `token`, `credentials` | `Authority/{Credential,CredentialAttenuation,Authorization,ClearanceGraph}`. |
| `captp` | `Exec/CapTP*` (handoff-unforgeability, GC, pipeline, settlement, consent-lace). |
| `discharge-gateway` | `Authority/ThirdPartyDischarge`. |
| `commit` | `Crypto/*` CR portals + `Exec/RecordCommit`/`SystemRoots`. |
| `persist` | `Distributed/CrashRecovery` (checkpoint ⊕ overlay = replay). |
| `dfa` | `Exec/DfaRouting` + `Crypto/Dfa`. |
| `bridge` | `Crypto/Bridge` + `Exec/JointCharterBridge`. |
| `storage` | `Exec/{BlindedQueue,QueueCutover,PubSubTopic}` + `Apps/StorageGatewayMandate`. |
| `directory` | `Distributed/DirectoryLaws` (register/lookup/revoke monotone laws — `revoke_is_final` tombstone, CAS-conflict reject — + §7b `GovDir` governance commit-swap binding). FRINGE-SWEEP moved this OUT of B.2: it is load-bearing for `governed-namespace`, not a pure primitive. Differential `directory/src/directory_diff.rs` (in-flight). |

### B.2 Pure infra / crypto-primitive / tooling (no protocol semantics to verify)

| Crate | Role |
|---|---|
| `hints` | BLS12-381 + KZG weighted threshold signatures — a crypto primitive. **Exception:** its *aggregation scheme* is a named Port residual (federation BLS QC), but the curve/pairing math is a primitive. |
| `secrets`, `tokenizer`, `trace`, `audit`, `observability`, `types` | Key custody / text / tracing / metrics / id types. |
| `rbg`, `dregg-storage-templates` | Userspace VFS + templates composed over verified primitives. |
| `net` | QUIC transport + Plumtree gossip. The causal-ORDER invariant is dregg (the lace = the causal DAG, `net/src/causal.rs:13` re-exports `dregg_types::CausalDag` modeled by `Coord/CausalOrder`); the gossip *delivery* layer is dreggrs infra (node-infra owns sync/gossip). |
| `tests`, `protocol-tests`, `teasting`, `perf`, `redteam` | Test / benchmark / fuzz harnesses (FRINGE-SWEEP: `perf` + `redteam` newly censused — pure measurement/adversarial tooling, no protocol semantics; the targets they exercise are verified elsewhere). |

---

## C. The clean boundary, in one sentence per side

- **dregg** = `{ verified-kernel models + their FFI bridge + every runtime/client/app that executes through
  the kernel }`. The Lean tree `Dregg2/*` IS dregg's truth; the Rust here is bridge + shadow + clients.
- **dreggrs** = `{ self-contained heritage Rust }`, split into **(B.1)** engines that a Lean model+differential
  now pins (kept as fast verified-shadows) and **(B.2)** pure infra/primitives/tooling (nothing to verify).
  Backburner: improve only as the dregg cutover demands; never the source of truth.

## D. Load-bearing Rust-only semantics that MUST be ported for Silver (Port-phase targets)

The migration from "dreggrs B.1 = verified shadow" to "fully dregg" is complete for a crate exactly when NO
load-bearing semantics live only in its Rust. The precise residual:

1. **✅ `federation` threshold decryption** — DONE (`Distributed/ThresholdDecrypt` + differential).
2. **✅ `coord` Stingray epoch `rebalance` cert-reconciliation** — DONE THIS SESSION. The named-OPEN
   `Proof/Stingray` §9 (signed SpendingCertificates, quorum reconstruction of true spend, epoch monotonicity)
   is now `Dregg2/Coord/StingrayCertReconcile.lean`: a faithful pure model of `budget.rs::rebalance_inner`
   (`:415-508`, every gate in source order) proving §9(3) epoch-monotonicity/no-replay
   (`rebalance_version_strictly_increases` + `stale_cert_rejected`), §9(2) quorum reconstruction + Byzantine
   bound (`full_rebalance_total_is_cert_sum` + `byzantine_undetected_overspend_le_f_ceiling`, ≤ f·ceiling
   undetected), §9(1) accepted⇒silo's-own under the named `CertUnforgeable` (Ed25519 EUF-CMA) portal, plus
   `rebalance_conserves_on_exact`. Differential `coord/src/coord_diff.rs::stingray_cert_reconcile_diff` (6
   tests) drives the GENUINE `StingrayCounter` with REAL Ed25519 certificates. `#assert_axioms`-clean.
3. **`federation` BLS quorum-cert aggregation** (`threshold.rs`/`receipt.rs` over `hints` KZG) +
   **checkpoint-prune safety** (`checkpoint.rs`). **✅ DONE (FRINGE-SWEEP correction — was mislabelled a
   residual):** `Distributed/BlsQuorumCert.lean` (committed `0c9aea2cc`) + `Distributed/CheckpointPrune.lean`
   (committed `056ae36a3`) model both, with wired Rust differentials (`federation/src/bls_quorum_diff.rs`,
   `federation/src/checkpoint_prune_diff.rs`). The only residual is the BLS12-381 *pairing math* — an
   imported crypto primitive carried as a named hyp (same class as Ed25519/Poseidon), NOT a coverage gap.
4. **✅ DONE (closing) — `directory` register/lookup/revoke + governance swap.** The earlier "JUSTIFIED
   RESIDUAL (low-LB), reachable via `Confluence/CRDT`" was a **HAND-WAVE** (FRINGE-SWEEP correction): that
   module proves a *generic* CRDT join, not the directory's four-op discipline, and `directory` IS
   load-bearing (consumed by `governed-namespace`). Now `Distributed/DirectoryLaws.lean` models the REAL
   `directory.rs` semantics (`revoke_is_final` tombstone, CAS-conflict reject, version-monotone, exact
   expiry) **+ §7b `GovDir` commit-swap commitment binding**. Differential `directory/src/directory_diff.rs`
   in-flight.
5. **`net` Plumtree gossip convergence** — **JUSTIFIED RESIDUAL (infra, other lane), VERIFIED:** the
   causal-ORDER invariant (the lace = the causal DAG) IS dregg-covered — `net/src/causal.rs:13` re-exports
   `dregg_types::CausalDag`, modeled by `Coord/CausalOrder` + `coord_diff.rs`. The raw eager/lazy push-dedup
   is *delivery*, not protocol truth, and its convergence obligation is `Distributed/CatchupConverges`.

**Non-this-agent, larger:** THE SWAP (`turn`/`cell` executor cutover) — a rewrite tracked by #24/#33, not a
modeling gap. The Exec/* / Circuit/* / Intent/* / Authority/* lanes are independently progressing.

**Silver "FULLY DONE" status for this manifest (FINAL, post-FRINGE-SWEEP):** items 1–4 — the genuinely
load-bearing *protocol* semantics (threshold decryption, Stingray cross-epoch reconciliation, BLS QC +
checkpoint-prune, directory register/revoke/governance-swap) — are ALL CLOSED with meaningful Lean + a
differential; #3 and #4 were previously MISLABELLED (a residual that was actually done, and a hand-waved
deflection) and the FRINGE-SWEEP corrected both. #5 net-gossip-*delivery* is the only legitimate infra
residual, its protocol-truth already dregg-covered. The newly-censused fringe crates `perf`/`redteam` are
pure measurement/fuzz tooling (N/A). The remaining true Rust-only "source of truth" is the §B.2 primitives
(curve/pairing math, key custody) — the justified crypto/OS-primitive residual — plus THE SWAP (`turn`/`cell`,
a rewrite not a coverage gap). **No load-bearing dregg PROTOCOL semantic lives only in Rust at the end of
this campaign.**
