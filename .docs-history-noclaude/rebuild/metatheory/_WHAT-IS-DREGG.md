# What Is Dregg

Code-grounded: quotes are `file:line` or live commands. This is the what-is map of
the runtime, what runs, and the verification story. When this doc and the code
disagree, the code wins.

---

## The one-line answer

dregg is a **capability-secure, object-capability distributed runtime** with a deep
Lean metatheory and a plonky3 STARK layer. Cells (objects) own balances and
capabilities; state advances in *turns* (effect bundles) authorized by an
object-capability/credential model. Three layers compose: a Rust executor that runs
the turns, a leaderless DAG transport that orders and finalizes them, and a
verification program — a Lean 4 metatheory that proves the executor's laws plus a
STARK prover for ZK/privacy. The thing it is *for*: agent-to-agent value/credential
exchange where each party can verify the others' turns rather than trust them.

---

## What dregg is, structurally

dregg ("Dragon's Egg") is in the vat/E-rights lineage: cells own balances and
capabilities, and state advances in *turns* (effect bundles) authorized by an
object-capability/credential model (a 10-variant `Authorization` with
attenuation/revocation). The transport layer is a **blocklace** — a leaderless DAG
with total ordering via a `tau` function, from the Cordial Miners paper
(`node/src/blocklace_sync.rs:1`; `use dregg_blocklace::ordering::tau`). It is **not**
a classical-BFT propose/vote/commit chain, and **not** a smart-contract VM in the EVM
sense. The third layer is verification: a Lean 4 metatheory (`metatheory/`) that
proves the executor sound and extracts verifiable circuits, plus a plonky3 STARK layer
for ZK/privacy (notes, nullifiers).

---

## What runs

### Devnet node — live (solo regime)
`curl https://devnet.dregg.fg-goose.online/status` returns
`{"healthy":true,"dag_height":1107,"block_count":1773,"consensus_live":true,
"federation_mode":"solo", …}`. A node is live, produces blocks, reports
`consensus_live:true`. The deployment is a single node (`peer_count:0`,
`federation_mode:"solo"`); the *distributed* and *privacy* claims are exercised by the
N=3 testnet path, not this solo deployment. Consensus liveness in a one-node DAG is the
trivial case (the strong single-machine bounds collapse here).

### Rust executor — the runtime
The node executes turns through the Rust `dregg_turn::TurnExecutor`
(`node/src/executor_setup.rs:6,70`), invoked at `node/src/blocklace_sync.rs:55`
`executor.execute(&signed_turn.turn, &mut s.ledger)` inside `execute_finalized_turn`.
The ledger is HashMap/BTreeMap-backed (`cell/src/ledger.rs:1`), so live state access is
O(1)-ish. This is the working execution engine.

### Verified Lean executor — the source-of-truth model, and the producer for the covered set
`execFullForestG` / `dregg_exec_full_forest_auth` is the single credential-gated entry
(`metatheory/Dregg2/Exec/GatedForestCfg.lean:84`). `HandlerExecutor.lean` maps the
`FullActionA` variants to closed effects, with `#guard` adversarial tests (forged-cred
and false-caveat forests are rejected: `GatedForestCfg.lean:272,275` both `== false`).
For the swap-safe covered effect set the Lean executor *produces* the committed state
via `dregg_turn::lean_apply::produce_via_lean` (default-on, `DREGG_LEAN_PRODUCER`); the
Rust executor runs as a demoted differential. The covered/residual boundary lives in
`_SWAP-COMPLETE-STATUS.md`; `_DREGG1-DREGG2-UNIFICATION-LEDGER.md` tracks the cutover.

### Circuit / ZK layer — real prover
plonky3 is a real dependency and `p3_uni_stark::{prove,verify}` is used
(`circuit/src/plonky3_prover.rs:45`). Proving is invoked from the API/MCP endpoints
(`node/src/api.rs:1805`, `node/src/mcp.rs:262,479,3576`). There is a generic
"Lean-emitted descriptor" interpreter AIR (`circuit/src/lean_descriptor_air.rs`) with a
LogUp range-check efficiency win (`circuit/src/lean_lookup_air.rs:1`; a shared byte
range-table replacing per-bit decomposition). Kimchi/Mina and an sp1 guest are wired as
optional backends. The consensus commit path emits a best-effort STARK root binding
(`node/src/blocklace_sync.rs:106`); per-finalized-turn proof binding is the open
weld — see `_PRODUCT-POLIS-ASSESSMENT.md` §4 and `TITANIUM-PHASE.md`.

### Apps — verified primitives
Two app surfaces: Lean `metatheory/Dregg2/Apps/` (nameservice, identity, subscription,
governed-namespace, privacy-voting, each with a `*Gated.lean` variant on the gated
executor) and Rust `starbridge-apps/` (each a `lib.rs` face of a verified Lean app,
pinned to the Lean `#guard` by a byte-for-byte differential corpus). The agent-centric
apps (`tool-access-delegation`, `sealed-auction`, `agent-provenance`) carry
machine-checked security theorems over the whole post-state. Web surfaces and CLI verbs
exist for the older five; the three agent apps are headless libraries — see
`_PRODUCT-POLIS-ASSESSMENT.md` §1.

### SDK / node plumbing — real
A real `sdk/`, `cli/`, gossip, websocket, MCP, persistence, multi-group routing,
genesis, blocklace sync/checkpoint. Substantial systems software.

---

## The verification story

### Proven (about the model), axiom-pinned
- **Conservation** across a turn: `execHandlerTurn_conserves`
  (`HandlerExecutor.lean:299`) lifts the generic `turn_conserves` — one keystone, not a
  per-arm matrix — `#assert_axioms`-pinned.
- **Handler refines the kernel** per effect: `handler_refines_execFullA_*`
  (transfer/mint/burn/escrow/obligation/bridge/…, `HandlerExecutor.lean:383+`) tie each
  handler arm to the kernel spec.
- **Capability attenuation / authorization gating**: forged credentials and false
  caveats are rejected (the `#guard … == false` tests), and the gate is the single
  unavoidable entry.
- **Nullifier / no-double-spend**: the Lean privacy kernel (`PrivacyKernel.lean`,
  `Privacy.lean`, `Exec/CellNullifier.lean`) and the Rust AIR (`note_spending_air.rs`).
- **Data refinement to a HashMap kernel**: `ConcreteKernel.lean` is an l4v-style
  abstraction relation (`toAbstract`) with the transfer/writeField squares proved
  (`ConcreteKernel.lean:23`). It covers the hot
  path (transfer/writeField + nullifier/commitment sets); refinement coverage of the
  long tail is the standing extension lane.
- Axiom discipline is enforced: hundreds of files carry `#print axioms`/`assert_axioms`
  footprint guards, and the named crypto carriers each rest "only on the standard axioms"
  (e.g. `Crypto/Bridge.lean:407`).

### Assumed (named hardness, not derived)
Poseidon2 collision-resistance and the named crypto carriers (commitment/digest
injectivity portals) are grounded on Poseidon2 CR — a hardness axiom, tracked in
`_CRYPTO-HYPOTHESIS-LEDGER.md`.

### The open welds (forward pointers, one line each)
- **Execute→prove binding.** The commit path uses a best-effort STARK root binding
  (`blocklace_sync.rs:106`); binding the *committed post-state* per finalized turn is the
  Titanium target (`TITANIUM-PHASE.md`).
- **circuit ⟺ protocol soundness** — the full executor⟺spec + circuit⟺spec triangle per
  effect with a state commitment + anti-ghost tooth — exists for the transfer beachhead;
  uniform coverage is tracked in `_CIRCUIT-ASSURANCE-PER-EFFECT.md` and
  `feedback-conservation-is-not-correctness`.
- **Consensus in Lean** — the Cordial-Miners ordering the live node runs is the Rust
  implementation; the Lean consensus development (`Dregg2/Exec/Consensus.lean`,
  Stingray/Fairness) is partial — see `CONSENSUS-GROUNDING.md`.
- **Open-hole surface.** The proven keystones are axiom-pinned and free of open holes; the broader
  Lean surface is verification-in-progress, with the load-bearing residuals tracked in
  `_PROOF-INTEGRITY-LEDGER.md` and `_VACUITY-SWEEP.md`, and a CI guard forbidding open holes
  in the pinned target set.

What "verified" buys today: the abstract execution laws (value conservation, attenuation
monotonicity, refinement to an efficient kernel) hold for a faithful model of the
executor, with checkable axiom footprints, and the Lean executor *produces* the
committed state for the covered effect set.

---

## Efficiency

- **Running node:** the Rust ledger is HashMap/BTreeMap-backed (`cell/src/ledger.rs:1`);
  live per-effect state access is O(1)-ish.
- **Lean executor (the model):** the abstract kernel state is function-based
  (`RecordKernelState.cell : CellId → Value` + ~15 more fields,
  `Exec/RecordKernel.lean:442`), so abstract updates are O(n) in proof-evaluation terms.
  `ConcreteKernel.lean` is the l4v data-refinement answer: a `Std.HashMap`/`Std.HashSet`
  concrete kernel with a proved abstraction relation, so the efficient representation
  inherits the abstract proofs. It covers the hot path; the long tail is the extension
  lane.
- **Circuit:** the verified-extraction AIR (`lean_descriptor_air`) is a generic
  interpreter (inherently costlier than a hand-rolled per-effect AIR); the LogUp
  range-bus (`lean_lookup_air.rs`) is a measured win. Recursive aggregation to one
  succinct proof per batch (Silver→Gold) is the verification-cost lane —
  `DESIGN-recursion-aggregation-private-joint-turns.md`.

Measured turn-proof latency lives in `_PRODUCT-POLIS-ASSESSMENT.md` §4 (the `perf/`
crate times the production prover entry points).

---

## Maturity

A live node, real DAG consensus ordering, a real executor, a real STARK prover, and a
serious Lean development with proved keystones and disciplined axiom hygiene. The three
layers (execute / order+finalize / prove) work, and the Lean executor is the producer
for the covered set; the binding of every committed turn to a proof, the per-effect
soundness triangle uniformly, and the multi-node + privacy exercise are the live
frontiers — each tracked in the ledger it belongs to (above).
