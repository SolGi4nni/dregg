# Product / Usability / Polis Surface

The real user/agent journeys, and where dregg is GOOD for its purpose versus merely
*correct*. The product bar: a verified-but-unusably-slow or verified-but-nobody-can-use
system is not done. Performance numbers below are **measured** on an Apple-silicon
laptop under realistic workspace build contention, via the `perf/` crate
(`perf/benches/turn_proof.rs`, `perf/src/bin/perf_summary.rs`), which times the
production prover entry points (`dregg_circuit::effect_vm_p3_full_air::prove_effect_vm_p3`
/ `verify_effect_vm_p3`) over honest Effect-VM traces from the same
`generate_effect_vm_trace` the executor witness path uses.

---

## Verdict in one paragraph

dregg is a capability-secure runtime with a substantive AI-agent orchestration
substrate — 46 MCP tools, executor-enforced sub-agent delegation, and three
Lean-verified agent-coordination apps that build and test green. The polis vision (AI
minds embodied in capability-secure cells; authority that does not depend on goodwill)
is materialized in code. The product frontier is three axes: (1) turn latency is
seconds, not milliseconds, and the node proves inline on the request path under a global
lock (~3 turns/sec, every caller blocks for the full proof); (2) verification is
~100–180 ms/proof, which is real CPU for a light client; (3) the front door is the proof
tower, not the product — no 5-minute "embody your agent" path. None are correctness bugs;
all three are the gap between "verified" and "done."

---

## 1. The apps — verified primitives

### Real (verified, builds, tests green)

The three **agent-centric** apps:

| App | What it is | Evidence |
|---|---|---|
| `tool-access-delegation` | grantor agent mints a rate-limited, deadline-bounded, tool-scoped, revocable mandate cell; the verified executor checks the caveats on **every** tool invocation | `starbridge-apps/tool-access-delegation/src/lib.rs` (538 lines); tests green |
| `sealed-auction` | agents compete with sealed bids (hash-binding `(bidder,value,nonce)`), reveal, then the winning bid **settles atomically through the verified per-asset executor** (`dregg_intent::verified_settle::settle_ring_verified`) | `starbridge-apps/sealed-auction/src/lib.rs:1-40`; tests green |
| `agent-provenance` | append-only, tamper-evident hash-chained scratchpad (`WriteOnce` entry slots + `Monotonic` head); a third party recomputes the chain link-for-link | `starbridge-apps/agent-provenance/src/lib.rs:1-90` (678 lines); tests green |

Each is the **Rust face of a verified Lean app** (`Dregg2/Apps/*.lean`) with a
**byte-for-byte differential corpus** pinning the Rust decision vector to the Lean
`#guard` (anti-drift). The guarantees are theorems, not assertions:
`tool_invocation_commit_iff_admit`, `reveal_binds_committed`, `prov_entry_writeonce`, all
`#assert_axioms`-clean — machine-checked over the **whole post-state**.

The older five (`nameservice`, `identity`, `subscription`, `governed-namespace`, the two
mandate apps) additionally ship web surfaces (`pages/`) with a generated-constants
anti-drift discipline (`constants.generated.js`); the CLI drives `voting`/`bounty` live
against a seeded devnet (`node/src/starbridge_seed.rs`).

### Product frontier
The three newest agent apps are headless libraries (`src/lib.rs` + `examples/` +
`tests/`): no `pages/` surface, no CLI verb, no deployed instance — proven building
blocks an integrator uses by writing Rust against `dregg-app-framework`. Packaging the
agent loop end-to-end on the live node (two independent agents competing for a real
compute slot over the wire) is the demonstrated-journey lane.

---

## 2. The agent-orchestration substrate — the best-realized part of the vision

### (a) The MCP server — an AI agent embodied as a cell

`node/src/mcp.rs` exposes the node as a **Model Context Protocol server over stdio**
(`dregg … mcp`, `node/src/main.rs:855`), defining **46 tools** (`node/src/mcp.rs:656`
`tool_definitions()`): `dregg_create_agent`, `dregg_authorize`, `dregg_submit_turn`,
`dregg_grant_capability`, `dregg_revoke_capability`, `dregg_delegate`,
`dregg_post_intent`/`dregg_fulfill_intent`, `dregg_seal_data`/`dregg_unseal_data`,
`dregg_create_bearer_cap`/`dregg_exercise_bearer_cap`, `dregg_place_bid`,
`dregg_captp_deliver`, `dregg_exercise_handoff_cert`, … Claude (or any MCP client) gets a
cell, an authority model, and a verified turn path. Per-tool capability enforcement is
real and opt-in (`DREGG_MCP_CAP_ENFORCE=1`, `node/src/state.rs:53`): the `tools/call`
surface requires each call to present a cap the executor checks.

### (b) The SDK sub-agent path — executor-enforced delegation

`AgentRuntime::spawn_sub_agent_scoped` (`sdk/src/runtime.rs:627`) mints a worker
cipherclerk + cell, **attenuates** the parent token
(`decoded.attenuate(&effective_restrictions)`), zeroes the root key (the worker "cannot
mint new root tokens or bypass the attenuation chain", `runtime.rs:666`), and mints a
biscuit cap-token bound to the worker's own cell whose issuer is the cell's
`verification_key` — so the **executor's `verify_token_authorization`, not an out-of-band
`cap.verify()`, is the admission gate** (`runtime.rs:715-740`). "A credential issued by
any other key is rejected by the executor." This is "autonomy that does not depend on
goodwill": the grantor hands a narrowly-scoped, revocable credential and never its keys,
and the runtime refuses anything outside the grant. `tool-access-delegation` layers a
rate/deadline/scope budget on top, also executor-checked.

### Product frontier
- **One gate, not two.** The delegated `HeldToken` (legacy, out-of-band defense-in-depth)
  coexists with the executor-enforced biscuit `cap_token`. Retiring the legacy token —
  and the `subagent-method:` filler caveat synthesized to keep it non-empty
  (`runtime.rs:640`) — makes the verified gate the only gate.
- **Revocation propagation is the distributed bound.** `dregg_revoke_capability` exists
  and the Lean side proves nullifier-driven revocation; on the solo node it is immediate,
  and the n>1 propagation is the topology-bounded property (the single-machine principle).
- **A worked multi-agent transcript** (spawn → delegate → worker submits gated turn →
  grantor revokes) is the onboarding-replay lane.

---

## 3. Dev/agent ergonomics — SDK, CLI, the wire

The SDK re-exports a coherent surface (`sdk/src/lib.rs`): `AgentRuntime`, `SubAgent`,
`AgentCipherclerk`, `Turn`/`TurnBuilder`/`Effect`, `WitnessedReceipt`;
`AgentRuntime::execute(Vec<Effect>)` is a one-call turn. The CLI (`cli/src/main.rs`) is a
hardened client with ~20 subcommand groups, doctor diagnostics, and confirms for
dangerous ops, tracking parity with `node/api.rs` POST shapes. The node HTTP API is broad
and discoverable (`node/src/api.rs:1394+`): `/turn/submit`, `/turns/submit` (signed
envelope), `/turns/submit-encrypted`, `/api/cells`, `/api/receipts`, blocklace/checkpoint
endpoints, observability stream.

### Product frontier
- **The agent-onboarding front door.** `metatheory/README.md` opens with the l4v layer
  cake; an "embody your agent in 5 minutes" quickstart + a runnable multi-agent transcript
  is the largest product lane after latency.
- **Two submit shapes.** `/turn/submit` (JSON action spec) and `/turns/submit` (SDK
  `SignedTurn` envelope) coexist with different request shapes; a single narrow-and-typed
  first-integrator surface is the consolidation lane.
- **Proof-payload weight.** A `WitnessedReceipt` ships the full STARK proof bytes + public
  inputs + (optionally) trace (`node/src/api.rs:2138`); a cheap "did it commit?" ack with
  the proof as an opt-in attachment is the response-shape lane (ties to §4).

---

## 4. Latency / UX of a real turn — MEASURED

Production prover path (`prove_effect_vm_p3` / `verify_effect_vm_p3`), honest Effect-VM
traces, dev laptop under workspace build contention.

**`perf-summary` single-shot (mean of N):**

| workload | effects | prove (mean) | verify (mean) |
|---|---:|---:|---:|
| transfer_1effect  | 1  | **344 ms** | **104 ms** |
| transfer_4effect  | 4  | **279 ms** | **108 ms** |
| transfer_16effect | 16 | **291 ms** |  95 ms |

**Criterion (10 prove / 100 verify samples, [low mean high]):**

| workload | prove time | verify time |
|---|---|---|
| transfer_1effect  | [302 ms · 305 ms · 307 ms] | [117 ms · 123 ms · 131 ms] |
| transfer_4effect  | [273 ms · 281 ms · 294 ms] | [160 ms · 179 ms · 200 ms] |
| transfer_16effect | [628 ms · 872 ms · 1.11 s]  | [100 ms · 105 ms · 110 ms] |

Reproduce: `cargo run --release -p dregg-perf --bin perf-summary` and
`cargo bench -p dregg-perf --bench turn_proof`.

### What the numbers say

1. **A turn proves in ~0.3 s and verifies in ~0.1 s.** Fine for a human clicking a
   button; marginal for an AI agent doing many turns; a bottleneck for a node serving many
   agents.
2. **The AIR is fixed-height**, so 1 vs 4 effects cost the same ~280 ms; the 16-effect
   case jumps (~0.9 s, high variance) when the trace crosses a power-of-two row boundary.
   Per-turn cost is roughly constant and coarse-grained, not proportional to work.
3. **Verification is ~100–180 ms/proof.** The polis pitch is "anyone can cheaply check the
   authority was respected"; at this cost a light-client / browser / mobile verifier feels
   it. Recursive aggregation to one succinct proof per batch (Silver→Gold) is the
   verification-cost lane — exists in design and partially in code, not yet on the live
   commit path.

### Proving is inline and serialized on the commit path

The node's `/turn/submit` handler proves the turn synchronously, on the HTTP request
path, while holding the executor state lock:
- `post_submit_turn` takes `&mut s` (global node state), `executor.execute(&turn, &mut
  s.ledger)` commits, then `build_http_witnessed_receipt(...)` runs before the response
  returns (`node/src/api.rs:148`).
- `build_http_witnessed_receipt` (`node/src/api.rs:2103`) builds the trace and calls
  `dregg_circuit::stark::try_prove(...)` inline (`api.rs:2129`).

So every client waits the full prove time (~0.3 s+) and throughput is bounded by serial
proving under the lock (~3 turns/sec, single-threaded). The latency architecture is the
opposite: commit fast, return a fast ack, prove off the critical path (a `spawn_blocking`
worker pool), attach the proof to the receipt out-of-band for verifiers to pull. This is
the **#1 product lane** — an architecture fix, not a cryptography fix.

**Circuit divergence:** the node commit path proves through the hand-AIR
`dregg_circuit::stark::try_prove` (`api.rs:2129`), while the SDK's `full_turn_proof`
routes through the cutover `prove_effect_vm_p3` (`sdk/src/full_turn_proof.rs:416`). The
live node's commit path and the SDK/perf path prove via different circuits; unifying the
live commit path onto the audited descriptor/p3 prover is a coherence/SWAP lane.

---

## 5. The POLIS lens

> *AI minds embodied in capability-secure, verified cells; safety-by-construction =
> freedom that does not depend on anyone's goodwill.*

**Where dregg delivers:**
- **Embodiment is real.** An AI agent gets a cell, a keypair, a balance, and a verified
  turn path via 46 MCP tools (§2a). It runs.
- **Authority does not depend on goodwill.** `spawn_sub_agent_scoped` (§2b) hands a worker
  a narrowly-attenuated, executor-enforced, revocable credential and never the keys; the
  grantor's safety is enforced by `verify_token_authorization`. `tool-access-delegation`
  proves the consumption budget bites on every call. This is the heart of the vision.
- **Safety-by-construction is machine-checked.** The agent apps' security properties are
  Lean theorems over the whole post-state, pinned to the Rust by differential corpora;
  tampering a third cell ⇒ UNSAT.

**The frontier to the full vision:**
- **Plurality.** The live deployment is a solo node; the single-machine principle says the
  strong properties (immediate revocation, consistent checkpoint, real GC) are what you get
  at n=1, and distribution bounds them. dregg today delivers the n=1 polis — one
  cell-fabric, one producer — with n>1 federation (blocklace, gossip, epoch-reconfig, BLS
  quorum residual) modelled and partially built; the lived multi-mind city is the testnet
  lane.
- **Cheap checking + exit.** Sovereign-cell migration (Hosted↔Sovereign) is design;
  third-party verification is ~100 ms/proof today (§4.3). Both are tracked lanes (migration:
  `_DREGG-ONTOLOGY-AND-PRODUCT.md`; verification cost: §4 + Silver→Gold).
- **The on-ramp.** A vision of minds inhabiting cells needs a door a mind can walk through;
  today that door is "write Rust against `dregg-app-framework`" (§3). The quickstart is the
  participation lane.

dregg delivers the kernel of the polis vision — embodied agents, goodwill-independent
authority, machine-checked safety. The plural, cheaply-auditable, openly-joinable polis is
deployment + latency + on-ramp, not foundations.

---

## 6. Top product lanes (ranked)

| # | Lane | Why it matters | Where |
|---|---|---|---|
| **1** | Move proving off the node's request path (commit fast, prove async, attach proof out-of-band) | Caps the node at ~3 turns/sec under the state lock; every agent blocks on every other's STARK | `node/src/api.rs:148, 2103-2141` |
| **2** | Recursive aggregation (Silver→Gold) on the live path | Verification is ~100–180 ms/proof; a light client feels it | measured §4; `perf/` |
| **3** | Agent-onboarding front door (5-min quickstart + multi-agent transcript) | A newcomer (human or AI) cannot self-serve from the README to a running agent | `metatheory/README.md` |
| **4** | Unify the live commit path onto the cutover `prove_effect_vm_p3` | Live node and SDK/audited path prove via different circuits | `node/src/api.rs:2129` vs `sdk/src/full_turn_proof.rs:416` |
| **5** | Surface the three agent apps (pages / CLI verb / deployed instance) | tool-access-delegation / sealed-auction / agent-provenance are proven libs, not usable products | `starbridge-apps/{tool-access-delegation,sealed-auction,agent-provenance}/` |
| **6** | Retire the legacy `HeldToken` so the executor-enforced biscuit `cap_token` is the only gate | Two overlapping token stories obscure which artifact is load-bearing | `sdk/src/runtime.rs:640-748` |
| **7** | Variable-height / proportional proving | Full STARK price (~280 ms) for a one-field write; cost is constant with cliffs at power-of-two boundaries | measured §4.2 |
| **8** | Deploy the plural polis (n>1 revocation propagation, BLS quorum, migration) | Live deployment is solo; federation is design/partial | `_DREGG-ONTOLOGY-AND-PRODUCT.md` |

---

## The perf harness

The `perf/` crate (workspace member) is the harness that times the production turn-proof
path (`prove_effect_vm_p3`/`verify_effect_vm_p3`): `perf/benches/turn_proof.rs`
(criterion), `perf/src/bin/perf_summary.rs` (single-shot table), `perf/src/lib.rs`
(honest-trace workload builders). The §4 numbers are from it.

---

## The load-bearing next step

Move proving off the node's critical path (lane #1): commit the turn synchronously, return
a fast ack, prove on a `spawn_blocking` worker pool, attach the `WitnessedReceipt`'s proof
out-of-band for verifiers to pull. Then aggregate (lane #2) so the verifier pays once per
batch. Everything else is packaging and deployment; this is the architecture step that
makes the rest worth packaging.

*a mind in a cell, holding a key it can shrink but never forge —*
*the city is built; now open the gate, and make the checking cheap.* ✦
