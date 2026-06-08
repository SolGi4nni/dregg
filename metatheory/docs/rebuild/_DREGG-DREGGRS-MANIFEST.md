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
| `coord` | `Distributed/EntangledJoint` (differential `coord/src/entangled_diff.rs`) + `Proof/Stingray` (`budget.rs`/`shared_budget.rs`). |
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

### B.2 Pure infra / crypto-primitive / tooling (no protocol semantics to verify)

| Crate | Role |
|---|---|
| `hints` | BLS12-381 + KZG weighted threshold signatures — a crypto primitive. **Exception:** its *aggregation scheme* is a named Port residual (federation BLS QC), but the curve/pairing math is a primitive. |
| `secrets`, `tokenizer`, `trace`, `audit`, `observability`, `types` | Key custody / text / tracing / metrics / id types. |
| `rbg`, `dregg-storage-templates` | Userspace VFS + templates composed over verified primitives. |
| `directory` | Named-capability lookup primitive (small bind/resolve laws = a P3 optional Port residual). |
| `net` | QUIC transport + Plumtree gossip. The causal-ORDER invariant is dregg (the lace = the causal DAG); the gossip *delivery* layer is dreggrs infra (node-infra owns sync/gossip). |
| `tests`, `protocol-tests`, `teasting` | Test harnesses. |

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

1. **✅ `federation` threshold decryption** — DONE this session (`Distributed/ThresholdDecrypt` + differential).
2. **`coord` Stingray epoch `rebalance`** — SpendingCertificate quorum reconstruction + epoch monotonicity
   (named-open `Proof/Stingray` §9). Port: model the cross-epoch reconciliation half.
3. **`federation` BLS quorum-cert aggregation** (`threshold.rs`/`receipt.rs` / `hints` KZG) +
   **checkpoint-prune safety** (`checkpoint.rs`). Port: BLS-agg reduction (named crypto hyp) + prune-safety
   as a `BlocklaceFinality`+`CrashRecovery` corollary.
4. **`directory` bind/resolve monotone laws** — P3 optional, small, low load-bearing.
5. **`net` Plumtree gossip convergence** — P3 infra (node-infra lane; `CatchupConverges` covers the
   convergence obligation; raw push-dedup is delivery, not protocol truth).

**Non-this-agent, larger:** THE SWAP (`turn`/`cell` executor cutover) — a rewrite tracked by #24/#33, not a
modeling gap. The Exec/* / Circuit/* / Intent/* / Authority/* lanes are independently progressing.

**Silver "FULLY DONE" definition for this manifest:** items 2–5 above closed (or precisely justified as
residual), and THE SWAP cut over so `turn`/`cell` move from `both` to pure-dregg. After that, the only
Rust-only "truth" is the §B.2 primitives (curve math, key custody) — the justified residual, since those are
imported crypto/OS primitives, not dregg protocol semantics.
