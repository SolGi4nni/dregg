# DREGGRS SEGREGATION MANIFEST

**Date:** 2026-06-10 · **Method:** read Cargo.tomls + lib.rs headers + grepped every
`dregg-lean-ffi` dependency and `produce_via_lean` / `lean_shadow` / `dregg_*_str` call site.
Code was trusted over .md docs. Snapshot taken mid-flight on the 52→8 verb reduction;
metatheory/, turn/, sdk/, cell/ were in active edit while this was surveyed.

**The question:** which Rust is a self-contained implementation (and of what), and which Rust
exists to invoke the verified Lean semantics (`metatheory/Dregg2/` via `libdregg_lean.a`)?

## Classes

- **L — LEAN-INVOKING**: links `libdregg_lean.a` (directly or via a feature chain) and routes
  decisions/state through a `dregg_*_str` export.
- **R-load — SELF-CONTAINED RUST, load-bearing**: in the runtime path, no Lean; transport,
  storage, crypto, codecs, prover machinery.
- **R-herit — SELF-CONTAINED RUST, heritage/dreggrs**: the legacy dregg1 semantics lineage
  THE SWAP and the verb reduction delete.
- **T — LEAF/TOOLING**: tests, benches, demos, deploy, clients.

**TCB?** = a soundness claim depends on this crate's Rust being correct *today*.
`yes→swap` = in the TCB only until the swap/cutover removes its authority.

## Summary table

| crate | class | TCB? | trajectory |
|---|---|---|---|
| `dregg-lean-ffi` | **L** (the bridge itself) | **yes** (marshal + link closure) | stays; shrinks as codec moves into Lean |
| `node` | **L** (hub: producer + 4 gates) | **yes** (hosts the gates) | stays; shrinks to host shell |
| `turn` | **L** (lean-shadow) + **R-herit** (executor arms) | **yes→swap** (fallback authority on uncovered set; marshaller permanent TCB) | shrinks hard: marshal stays, `executor/apply.rs` arms die with the 8-verb reduction |
| `sdk` | **L** (opt-in `lean-producer`) + R-load | edge (client-side signer, not verifier TCB) | shrinks; producer default-ON via env |
| `federation` | **L** (`lean-admission`) + R-load (revocation accumulator) | yes (revocation quorum verify) | stays; sim heritage already excised |
| `captp` | **L** (`lean-gate`) + R-load (sessions/transport) | yes (handoff non-amp verdict when ungated) | shrinks; bridge/seal verbs dissolve into factories |
| `coord` | **L-dormant** (feature exists, nobody enables it) + R-load | yes when ungated | shrinks; node-side gate is the live one |
| `intent` | **L-dormant** (`verified-settle` enabled by no crate) + R-load | yes→swap (matcher executor-trusted) | shrinks; settlement → verified path |
| `blocklace` | R-load (consensus engine) | yes (safety) — finality Lean-gated at node | stays |
| `cell` | **R-herit** (self-labeled LEGACY dregg1) | **yes→swap** (`compute_canonical_state_commitment` live) | deleted after swap; cap_root already cell≡circuit |
| `circuit` | split: descriptor path = Lean-derived; hand-AIRs = **R-herit**; p3 glue = R-load | yes (verifier + non-graduated AIRs) | hand-AIRs deleted with reduction; registry 47→~8+factories; prover/verifier glue stays |
| `lightclient` | R-load (succinct verifier) | **yes** | stays |
| `verifier` | R-load (standalone verifier) | **yes** | stays |
| `types` | R-load (canonical types/codecs) | **yes** | stays |
| `wire` | R-load (transport, self-declared NOT a trust boundary) | no | stays |
| `net` | R-load (QUIC p2p/gossip) | no | stays |
| `persist` | R-load (redb storage) | no (commitments catch tamper) | stays |
| `secrets`, `tokenizer` | R-load (key custody crypto) | yes (confidentiality, not soundness) | stays |
| `macaroon`, `token` | R-load (bearer-token crypto) | **yes** (HMAC/biscuit verify) | stays |
| `commit`, `trace` | R-load (ZK-token Merkle + Datalog) | yes (token-proof semantics) | stays |
| `bridge`, `audit`, `hints`, `credentials` | R-load (presentation/audit/threshold-sig/VC) | yes where their proofs are accepted | stays |
| `dregg-auth` | R-load (offline grant verifier product) | yes (its own guarantee) | stays |
| `dregg-dsl`, `dregg-dsl-runtime` | R-load (multi-backend predicate compiler) | yes for DSL-verified predicates | **shrinks/AMBIGUOUS**: per-effect circuit role superseded by Lean descriptors; caveat-predicate role stays |
| `storage` | **R-herit** (deprecated in its own header) | no | dissolves into `dregg-storage-templates` factories |
| `dregg-storage-templates` | R-load (factory cell-programs) | no (programs run under verified executor) | **grows** — the reduction's landing zone |
| `dfa`, `rbg`, `directory`, `observability`, `discharge-gateway`, `app-framework` | R-load (userspace/app layer) | no | stays (app-framework has opt-in `lean-producer` passthrough) |
| `wasm` | **R-herit** demo (browser sim on legacy executor, `circuit/mock`) | no | rebind to verified path or deleted |
| `demo`, `demo-agent`, `demo/sdk-consensus` | T | no | deleted/refresh eventually |
| `cli`, `discord-bot` | T (HTTP/bot clients of node) | no | stays |
| `tests`, `protocol-tests`, `teasting`, `dregg-dsl-tests`, `dregg-dsl-differential` | T | no | stays |
| `preflight`, `redteam`, `perf` | T (redteam links lean-ffi as differential oracle) | no | stays |
| `starbridge-apps/*` (11 members) | T (apps; nameservice has Lean-correspondence test) | no | stays |
| `chain/` (excluded workspace) | **R-herit** (SP1/EVM wrap, self-declared incompatible) | no | regenerate-or-delete |
| `apps/` (NOT workspace members) | **R-herit** (dead pre-starbridge apps) | no | **delete** |
| `uc-crypthol/`, `dreggscript/` | not Rust (Isabelle theories / notes) | n/a | stays |

## Evidence per non-obvious crate

### dregg-lean-ffi — the bridge, and a permanent TCB hotspot
The only crate that declares the extern surface: `dregg-lean-ffi/src/lib.rs:188-206` declares
`dregg_ffi_init`, `dregg_exec_full_forest_auth_str`, `dregg_record_kernel_step_str`,
`dregg_exec_handler_turn_str`, `dregg_blocklace_finalize_str`; `src/distributed_ffi.rs:134-360`
adds `dregg_strand_admit_str`, `dregg_tau_order_str`, `dregg_captp_validate_handoff_str`,
`dregg_captp_process_drop_str`, `dregg_captp_pipeline_resolve_str`, `dregg_coord_2pc_decide_str`,
`dregg_coord_causal_order_str`, `dregg_coord_shared_budget_str`. `build.rs` performs the
self-linking-archive closure over `libdregg_lean.a` and gates `cfg(lean_lib_present)`
(build.rs:932-935: never falsely advertises the kernel). The Rust here that must be correct
forever: the wire marshal (`marshal.rs`) and the link machinery. Note the codec direction is
already being shrunk (commit `e9dc8b738` moved the FFI state codec INTO Lean).

### node — where every Lean gate actually lives
Links the archive unconditionally (`node/Cargo.toml:20` regular dep, `lean-lib`), and enables
`dregg-turn/lean-shadow` (`:15`), `dregg-federation/lean-admission` (`:27`),
`dregg-captp/lean-gate` (`:40`). Live gates: producer mode — `node/src/blocklace_sync.rs:1950`
calls `dregg_turn::lean_apply::produce_via_lean`, **default ON** unless `DREGG_LEAN_PRODUCER=0`
(`node/src/state.rs:39`, `blocklace_sync.rs:1938-1939`); finality —
`node/src/finality_gate.rs:154,174` (`verified_tau_order`, `shadow_blocklace_finalize`); strand
admission — `node/src/strand_admission_gate.rs:64`; 2PC — `node/src/coord_gate.rs:100`
(`verified_2pc_decide`).

### turn — three crates wearing one trenchcoat
(1) `turn/src/lean_apply.rs:1023 produce_via_lean` + `lean_shadow.rs` = the **L** marshaller that
makes Lean the authoritative producer on the covered set (Rust runs as differential; unexpected
covered-path divergence VETOES the turn, `lean_apply.rs:1017-1023`). (2) `turn/src/executor/`
(`apply.rs`, `execute.rs`, ...) = the **R-herit** dregg1 executor, self-labeled
"LEGACY dregg1 — pending the verified-Lean SWAP. NOT the source of truth" (`turn/src/lib.rs`
header). It retains authority on uncovered/unmappable effects (`lean_apply.rs:357,381` names the
offending effect on fallback) — so it is TCB **until** coverage closes. The verb reduction
deletes most of its arms outright. (3) misc forest/codec plumbing the marshaller needs (stays).

### cell — heritage but live-load-bearing, plus the dependency inversion
Self-labeled LEGACY dregg1 (`cell/src/lib.rs` header), yet `cell/Cargo.toml:15-19` makes
`dregg-circuit` an **always-present** dependency because the canonical capability-root scheme
`dregg_circuit::cap_root` is load-bearing in the always-on `compute_canonical_state_commitment`.
That is the known inversion: the state-model crate pulls the entire proving crate to hash a cap
table. Classification: R-herit with a live TCB tail.

### circuit — the cleanest internal split in the workspace
Its own header says it (`circuit/src/lib.rs:3-21`): "Most AIRs in this crate are hand-written,
UNVERIFIED dregg1 circuits... NOT the source of truth." Three populations:
**Lean-derived** — `effect_vm_descriptors.rs` embeds byte-exact JSON emitted by
`Dregg2/Circuit/Emit/EmitAllJson.lean` (SHA-256 anti-drift fingerprints, 47 unique descriptors)
and `lean_descriptor_air.rs` interprets them on the real p3-uni-stark prover;
**R-herit** — the per-effect hand-AIRs (`bridge_action_air.rs`, `note_spending_air.rs`,
`effect_vm_p3_full_air.rs` hand-rows, ...) which the descriptor cutover + verb reduction delete;
**R-load forever** — plonky3/field/FRI/recursion glue (`plonky3_prover.rs`, `ivc_turn_chain.rs`),
which is acceptable permanent Rust (field arithmetic + a maintained external prover).
Note: circuit does not LINK Lean — it consumes committed Lean *output*; the differential that
checks live agreement lives in `dregg-lean-ffi/src/circuit_differential.rs`.

### federation / captp / coord / intent — gated organs, two of them dormant
- federation: `federation/src/admission.rs:336,394` — admission verdicts via
  `dregg_lean_ffi::verified_admits` under `lean-admission` (node enables it). The crate header
  confirms the old Morpheus BFT sim is gone; the live remainder is the revocation accumulator.
- captp: `captp/src/handoff.rs:465` (`verified_handoff_non_amplifying`), `gc.rs:81`
  (`shadow_captp_process_drop`), `pipeline.rs:61` (`shadow_captp_pipeline_resolve`) under
  `lean-gate` (node enables, `node/Cargo.toml:40`).
- **coord (AMBIGUOUS):** `coord/src/atomic.rs:276`, `causal.rs:83`, `shared_budget.rs:834` call
  the verified deciders under `lean-gate`, and `coord/Cargo.toml:24` claims "Enabled by the node"
  — but **no crate in the workspace enables `dregg-coord/lean-gate`** (grep over all Cargo.tomls).
  The live coord gating happens node-side in `node/src/coord_gate.rs` via node's own ffi dep.
  Either enable the feature from node or delete the in-crate gate; today it is dead code wearing
  a load-bearing comment.
- **intent (AMBIGUOUS):** `intent/src/verified_settle.rs:497` routes ring settlement through
  `shadow_record_kernel_step`, but `verified-settle` is in **no** downstream Cargo.toml — only
  intent's own tests exercise it. The verified settlement path is built, proven... and unreached
  from production. Same fix shape as coord.

### sdk / app-framework — the opt-in producer chain
`sdk/Cargo.toml:74 lean-producer = ["dregg-turn/lean-shadow", ...]`; `sdk/src/runtime.rs:386`
calls `lean_apply::produce_via_lean`, default mirrors `DREGG_LEAN_PRODUCER` (ON unless =0,
`runtime.rs:27-37`). `app-framework/Cargo.toml:45` forwards `lean-producer` →
`dregg-sdk/lean-producer`; `app-framework/src/cipherclerk.rs:387 set_lean_producer`. So the SDK
default build is Lean-free (wasm constraint, `sdk/Cargo.toml:21`) and the node is always-Lean.

### blocklace — self-contained consensus, Lean-checked at the rim
No Lean dep; the Cordial-Miners DAG + tau ordering engine. The node wraps its finality decisions
in `dregg_blocklace_finalize` / `dregg_tau_order` (finality_gate.rs above), so the *decision* is
Lean-gated while the *engine* (storage, gossip integration, block assembly) remains Rust. That is
the right boundary for it: keep the engine, keep the gate.

### The ZK-token "System B" line (macaroon→token→commit→trace→bridge→audit + credentials, dregg-auth, discharge-gateway)
A coherent, genuinely self-contained Rust product line — bearer tokens, fact commitments, Datalog
derivation traces, presentation proofs, offline grant verification (`dregg-auth/Cargo.toml:14-22`
deliberately wedges itself off from circuit/plonky3). No Lean anywhere in it. This is the part of
"dreggrs" that is **not** heritage: it's a parallel product whose TCB is conventional crypto
(HMAC, ed25519, Merkle) rather than the verified executor. It should be named and segregated as
such rather than lumped with the dying executor lineage.

### storage → dregg-storage-templates — the reduction's prototype
`storage/src/lib.rs` header carries the deprecation table: every module (inbox, pubsub, blinded,
programmable, operator, relay) maps to a `dregg_storage_templates` factory cell-program. This is
the verb-reduction pattern executed early — heritage operator-side Rust dissolving into
`FactoryDescriptor` + `CellProgram::Cases` data that the *verified* executor runs. Expect the
escrow/queue/bridge/seal effect families to follow exactly this shape tonight.

### wasm, demo*, apps/, chain/ — the museum wing
`wasm/Cargo.toml:26-31` builds the browser sim on `circuit/mock` + default-featureless
turn/cell/sdk — i.e. the legacy executor, no Lean (the lean-lib can't link to wasm32 anyway).
`apps/` (bounty-board, lending, orderbook, stablecoin, compute-exchange, gallery) is not in the
workspace `members` list at all — dead pre-starbridge code. `chain/` self-declares its SP1 guest
incompatible with the current circuit crate. All deletable or rebuild-from-verified.

## FFI entry-point inventory (who reaches what)

| export | reached by |
|---|---|
| `dregg_exec_full_forest_auth_str` | turn `lean_shadow.rs`/`lean_apply.rs` → node `blocklace_sync.rs:1950`, sdk `runtime.rs:386` (lean-producer), ffi marshal_roundtrip |
| `dregg_record_kernel_step_str` | ffi `state_differential.rs`; intent `verified_settle.rs:497` (dormant feature) |
| `dregg_exec_handler_turn_str` | ffi lib.rs wrapper (optional export) |
| `dregg_blocklace_finalize_str` / `dregg_tau_order_str` | node `finality_gate.rs:154,174` |
| `dregg_strand_admit_str` | federation `admission.rs:394`, node `strand_admission_gate.rs:64` |
| `dregg_captp_validate_handoff_str` / `_process_drop_str` / `_pipeline_resolve_str` | captp `handoff.rs:465` / `gc.rs:81` / `pipeline.rs:61` |
| `dregg_coord_2pc_decide_str` / `_causal_order_str` / `_shared_budget_str` | node `coord_gate.rs:100`; coord `atomic.rs:276`/`causal.rs:83`/`shared_budget.rs:834` (dormant feature) |
| `dregg_kernel_transfer_total` / `dregg_kernel_authorized` | ffi differential.rs/main.rs (early-probe relics) |

## The segregation boundary as it should be

**Rust that remains forever, and why that is acceptable:**
1. **Transport & storage** — `net`, `wire`, `persist`, `secrets`/`tokenizer`: wire is explicitly
   not a trust boundary; tampering with persist is caught by commitments. Lean has nothing to say
   about QUIC.
2. **Field arithmetic & the prover** — plonky3 glue in `circuit`, `lightclient`, `verifier`:
   the named-crypto-primitive terminus. The verified statement comes from Lean descriptors; the
   polynomial machinery executing it is a maintained external prover, exactly the "named
   assumption bridging verified-Lean → fast prover" we accepted.
3. **Conventional-crypto products** — the macaroon/token/commit/trace/auth line: its guarantees
   are HMAC/signature-shaped, independently testable, and not claims about executor semantics.
4. **The marshal** — `dregg-lean-ffi` wire codec + link closure: irreducible, but shrinkable
   (keep moving codec into Lean; keep the round-trip + drift gates).
5. **Consensus engine body** — `blocklace`, with its finality decisions Lean-gated at the node.

**Rust that is transitional (must die or be demoted):** `turn/src/executor/*` arms, `cell`'s
state model, every hand-AIR in `circuit`, `storage`'s deprecated modules, `wasm`'s legacy sim,
`apps/`, `chain/`. None of these should survive the verb reduction + swap completion.

**Concrete moves to sharpen the boundary (ordered):**
1. **Split `dregg-hash` out of `circuit`** (cap_root + Poseidon2 + commitment schemes) and point
   `cell` (and later its replacement) at it — kills the cell→circuit inversion
   (`cell/Cargo.toml:15-19`) and lets state-model code stop linking a prover.
2. **Wire up or delete the dormant gates**: enable `dregg-coord/lean-gate` and
   `dregg-intent/verified-settle` from the node (one line each) or remove the in-crate paths;
   today both carry comments claiming a wiring that does not exist.
3. **Split `turn` into `dregg-lean-producer` (lean_apply/lean_shadow marshal, L-class, permanent)
   and `dregg-turn-legacy` (the executor arms, R-herit, delete-on-coverage)** — the single move
   that makes "dreggrs vs lean-using" a crate boundary instead of a module boundary, and makes
   the eventual deletion a `members` edit.
4. **Invert the default**: make `lean-shadow`/`lean-producer` *default* features and a
   `rust-fallback` feature the opt-in, once the covered set closes — so a default build of the
   stack cannot silently run heritage semantics.
5. **Delete the museum now**: `apps/` (not even workspace members), `chain/` (self-declared
   broken), and `storage`'s deprecated modules once the templates' parity tests pass — each is a
   place a reader can mistake dreggrs for dregg.
