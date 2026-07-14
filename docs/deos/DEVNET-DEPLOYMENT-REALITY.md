# DEVNET-DEPLOYMENT-REALITY — the honest infra map (read-only recon, 2026-07-14)

The gap between **"offerings clear through the engine locally"** and **"a real
dregg devnet, deployed against real chain testnets, all infra enmeshed and
flowing."** This is a READ-ONLY recon: what is actually live, what is stubbed,
what is buildable-now (non-gated), what is ember-gated. No demos, no theater —
the real integration truth so the next build is the real thing.

The honest one-line summary: **the ENGINE is real and a solo node is genuinely
LIVE; the DEVNET is not.** What runs on hbox today is one verified `dregg-node`
as a committee-of-ONE with a clickable DrEX in front of it. The federation, the
on-chain settle from a live turn, the light-client processes, and the
Solana/Cosmos deploys are BUILT-and-tested but NOT standing/enmeshed. dreggcloud
is a separate pre-existing service that runs *alongside*, not *woven into*, the
dregg stack.

---

## Layer-by-layer reality (live vs stubbed)

### 1. The live node / devnet — REAL, but SOLO (committee-of-one), not a network

There IS a real, verified `dregg-node` running. Confirmed live over the tailnet
this session (read-only `GET /node/status` via the drex-web proxy at
`http://100.95.240.73:8781/node/status`):

```json
{"up":true,"node":"http://127.0.0.1:8420","status":{
  "healthy":true,"peer_count":0,"latest_height":0,"dag_height":462,
  "block_count":485,"consensus_live":true,"federation_mode":"solo",
  "state_producer":"lean","lean_producer":true,"full_turn_proving":true,
  "producer_covered_effects":21}}
```

What this honestly is (`docs/ops/PRIVATE-NODE.md`):

- **Real + verified.** `state_producer:"lean"` + `lean_producer:true` = the
  node links `libdregg_lean.a` (the compiled Lean executor) and runs the PROVED
  effect-VM, not a marshal-only tripwire. `full_turn_proving:true` = every
  committed turn gets a self-verified full-turn STARK proof via the async
  prove-pool (`has_proof:true`, `witness_count:1` on the receipt). This is not a
  mock. The node is producing blocks (`dag_height:462`, `block_count:485`).
- **Private, not public.** Node binds `127.0.0.1:8420` on hbox; the only
  reachable surface is `drex-web` on `:8781`, exposed to the **LAN + tailnet
  only** behind hbox's firewall. Nothing is on the public internet.
- **SOLO — this is the load-bearing caveat.** `federation_mode:"solo"`,
  `peer_count:0`. It is a **committee-of-ONE**: it produces blocks and finalizes
  them *by itself*. It is NOT the "C3 five-validator" nor the "ember n=4"
  federation. Those are real (see below) but are **not the thing that is
  standing**. `latest_height:0` despite 485 blocks reflects a solo producer
  minting heartbeat/attestation blocks rather than a network super-ratifying
  turn-bearing blocks cross-node.

**The multi-node federation is REAL CODE, proven by EPHEMERAL runs — not
standing.** `docs/deos/DEV-NODE-RUNBOOK.md` documents genuine two-process n=2
runs (shared `genesis.json`, live QUIC gossip + blocklace, byte-identical DAG
convergence, a turn on node A finalizing on node B), a robust late-join/reconnect
prober, and n=3 transitive gossip-of-peers discovery — each pinned by real
in-process QUIC tests (`net/src/gossip.rs`, `node/src/blocklace_sync.rs`). But
these are things you *stand up to demonstrate and tear down*, not a persistent
enmeshed devnet. There is no durable federation running today.

> Caveat surfaced by the docs: a **full-BFT** node needs a Lean seed that also
> splices the consensus/finality/admission exports
> (`Dregg2.Distributed.{FinalityGate,StrandAdmission}`); the solo seed on hbox
> realizes only the executor core (`PRIVATE-NODE.md` "Solo-node caveat").

### 2. The settlement path — WIRED end-to-end on the SOLO node; NOT on-chain

The "dreggicly flowing" spine, traced through `drex-web/serve.mjs`:

```
[browser] place sealed order → cipherclerk wasm sign + solvency/eligibility proofs
   POST /clear   → spawns REAL `drex_clear` (intent/src/bin/drex_clear.rs):
                     rung-2 aggregate → solver.rs multilateral ring match →
                     verified_settle.rs (each leg folded through recKExecAsset kernel)
                     → allocations + conservation + reject-polarity   [REAL, not a JS mirror]
   POST /settle  → settleOnNode(): ONE real turn on the LIVE node (127.0.0.1:8420):
                     /cipherclerk/unlock → bearer → /turn/submit
                     effects = [Transfer(operator→settle-pool de55e771…), EmitEvent per ring leg]
                     → node effect-VM executes → async prove_pool attaches full-turn STARK
                     → GET /api/turn/{h}/proof + /api/starbridge/receipts read back FROM the node
```

What is WIRED (real): the solver is the real Rust pipeline; the settle lands a
real value-bearing turn on the real verified node and gets a self-verified STARK
proof. A separate client would see the receipt over `/api/receipts` + SSE.

What is STUBBED / honestly-narrowed (`serve.mjs:126-160`, `PRIVATE-NODE.md`):

- **The clearing settles as value *MOVED*, not as per-trader allocations.** The
  faithful shape is a multi-`SetField` turn writing each trader's allocation.
  The node's rotated-IR prover currently *rejects its own proof* on that cohort
  (`setFieldVmDescriptor2` per-index selector binds ambiguously), so `serve.mjs`
  settles a single `Transfer` of `legSum` value + `EmitEvent` per leg — which
  proves, but *models* the clearing rather than *materializing* the per-trader
  ledger writes. Named, not hidden.
- **No on-chain settle from this path.** `/settle` lands on the local node only.
  The node turn is NOT wrapped and pushed to any external chain. That is a
  separate lane (§3). `serve.mjs:32-34` says this in-line.
- **Single-node.** The receipt is finalized by a committee-of-one, not
  cross-node BFT-attested.

### 3. Chain testnets + light clients — ONE live EVM settlement (fixture); the rest BUILT-not-DEPLOYED

| Leg | Reality |
|---|---|
| **Base-Sepolia (84532) settlement** | **LIVE on-chain.** A real dregg state-transition proof (STARK apex → BN254 shrink → gnark → Groth16) settled and verified via the Solidity pairing. `DreggSettlement 0x6c87b535…`, settle tx `0xbd2cac6a…`, read-back `provenHeight()=2`. **Honest:** it is a **fixture proof** (pre-generated 2-turn apex, NOT a live user turn) under a **dev single-party Groth16 ceremony** (toxic-waste-known, not production MPC), throwaway deployer. (`chain/DEPLOYMENTS.md`) |
| **Solana settlement program** | **BUILT + tested, NOT deployed.** Native BPF program verifying the SAME BN254 Groth16 proof via `alt_bn128` syscalls (`solana-settlement/src/`). No on-chain program id / devnet deploy record exists. |
| **Cosmos settlement (CosmWasm)** | **BUILT + tested, NOT deployed.** A `.wasm` artifact exists (`cosmos-settlement/artifacts/cosmos_settlement.wasm`) verifying the same BN254 proof via arkworks. No chain deploy record. |
| **ETH L1 / Cosmos light clients** | **Verified RULES as LIBRARIES, no standing process.** `eth-lightclient/` (Altair sync-committee, Base OP-stack L2OutputOracle finality, triple-verified against live Base mainnet output 12086) and `cosmos-lightclient/` (Tendermint validator-set + bisection) are crates with no `[[bin]]` running. `OPS-RUNBOOK.md` names the thin-bin + systemd unit as the wiring step. **Base uses FAULT PROOFS (FaultDisputeGame) on the live chain, not the L2OutputOracle model implemented** — named loudly in `GOAL-MULTICHAIN-SETTLEMENT.md`. |
| **Cross-chain governance spine** | **BUILT.** Non-custodial proof-of-holdings binding trilogy (Solana Ed25519 · EVM secp256k1 · Cosmos secp256k1/bech32), `from_foreign_fields` wire, multi-network `ChainId`, u128→u64 fail-closed narrow — all landed + adversarially audited (`GOAL-MULTICHAIN-SETTLEMENT.md` done-log). This is verified *rules*, not a live cross-chain flow. |
| **Robinhood Chain (46630) launchpad** | **Dry-run-ready, NOT deployed.** `chain/script/DeployLaunchpad.s.sol` + the launchpad contract; the gate runs 29/29 against a *locally-deployed* contract. Testnet broadcast is unperformed. |

**The wrap (the linchpin) is not yet end-to-end from a live turn.** The
STARK→EVM efficient wrap (BN254-native hashing, ~61× measured) exists, but the
full apex-proof pipeline from a *live node turn* is blocked on the rotated-proof
pipeline (`GOAL-MULTICHAIN-SETTLEMENT.md` thread 1). The Base-Sepolia settle used
a *pre-generated fixture*, not a proof minted from `/settle`.

### 4. dreggcloud + federation enmeshing — dreggcloud runs ALONGSIDE, not WOVEN IN

- **dreggcloud is a SEPARATE, pre-existing service** on hbox `:8787`
  ("universe-house-custody"; its custody contract shape is *cribbed* by
  `sandstorm-serve/src/custody.rs:4`). It is healthy and untouched
  (`fhegg-fhe/HBOX-24CORE-ENVELOPE.md`: "the box's live private dregg-node +
  dreggcloud services… stayed healthy"). But the DrEX / offerings / node do
  **not** talk to it — it is a neighbor on the box, **not enmeshed** with the
  dregg settlement stack. There is no wiring from an offering's clearing into
  dreggcloud.
- **The "federation enmeshing" does not exist yet** because there is no standing
  federation to enmesh with (§1). Everything points at the solo node.

### 5. The offerings surface — REAL engine, LOCAL demo, not deployed

The DreggFi offerings (`drex-web/offerings.mjs` on `:8790`, sibling of
`serve.mjs`) run the REAL `fhegg-solver` engine (derivatives price-cert, package
auction, shielded ring clearing) per pickable offering — real clearings + real
certificates, no mock. But `offerings.mjs:20-24` states it plainly: this is a
**devnet-DEMO surface** (real engine, run locally); actual public devnet
deployment (hosted node, live broadcast, live tokens) is the **ember-gated**
step. The offerings are NOT settled onto the node the way ring-DrEX `/settle` is,
and NOT enmeshed with a federation or a chain.

---

## THE HONEST GAP MAP

### ✅ ACTUALLY DONE (real, verified, running or on-chain)

- A **verified solo `dregg-node`** live on hbox over the Lean executor, STARK-
  proving real turns, reachable LAN+tailnet behind the firewall.
- A **clickable DrEX** that is real end-to-end *to the solo node*: real wasm
  wallet sign → real Rust ring solver → real proven turn on the node.
- **Base-Sepolia on-chain settlement** of a real dregg proof (fixture; dev VK).
- **Solana program + Cosmos CosmWasm verifier** — built + tested (verify the
  same proof), just not deployed.
- **Verified light-client RULES** (ETH Altair + Base finality; Cosmos
  Tendermint) and the **cross-chain non-custodial binding trilogy** — landed,
  audited.
- The **launchpad contract + 29/29 gate**; the **n=2/n=3 federation code** +
  reconnect/discovery, proven by real ephemeral runs and in-process QUIC tests.

### 🔨 BUILDABLE-NOW (non-gated integration — this is the real next work)

1. **Stand up a PERSISTENT multi-node federation** (n=2 → n=4) on private infra
   (hbox + persvati / a second box) as durable `systemd`/tmux units, sharing one
   `genesis.json`, over the reconnect prober + gossip-of-peers discovery. Every
   piece is proven by the ephemeral runs — it just isn't STANDING. Needs a
   **full-BFT Lean seed** (splice `Dregg2.Distributed.{FinalityGate,
   StrandAdmission}`) — a build step, not a gate.
2. **Enmesh DrEX + offerings against that federation** — re-point `serve.mjs` /
   `offerings.mjs` `DREGG_NODE` at a federated node so `/settle` lands a turn
   that finalizes **cross-node**, not committee-of-one. Firewalled, no public
   surface — non-gated.
3. **Fix the per-trader allocation cohort** so `/settle` materializes the real
   `SetField` allocations (not just value-moved Transfer). This is real circuit
   work (the rotated-IR `setFieldVmDescriptor2` selector), NOT a gate — it makes
   the settlement *faithful*, not just *provable*.
4. **Wire the on-chain settle from a LIVE node turn**: node `/settle` turn →
   `chain/` fold→shrink→Groth16 wrap → `DreggSettlement` on Base-Sepolia. Today
   only a *fixture* proof settled; minting the proof from a real turn is the real
   integration (blocked partly on the rotated-proof pipeline — a real dependency,
   not a gate).
5. **Build thin light-client bins** (`eth-lightclient` / `cosmos-lightclient`
   have no `[[bin]]`) and run them read-only as the ETH/Cosmos feeds, replacing
   trusted RPC on those legs.
6. **Keyless testnet dry-runs** of the launchpad + Solana + Cosmos deploys
   (`forge script … DeployLaunchpad` simulates a full fair-launch lifecycle; the
   Cosmos `.wasm` + Solana BPF can be dry-validated) — the *simulation* is
   non-gated; only the `--broadcast` needs a funded key (§gated).

### 🔒 EMBER-GATED (human decisions / outward steps — NOT to be done autonomously)

- **Public broadcast**: the AWS gateway, `demo.dregg.net` DNS, TLS, the
  public reverse-proxy route (`OPS-RUNBOOK.md` "What needs ember").
- **Testnet contract `--broadcast`** with a funded (throwaway) key — the
  launchpad / Solana / Cosmos deploys' outward step (dry-run is keyless & not
  gated; the broadcast is ember's).
- **VK-epoch flip + re-genesis** of the devnet (per MEMORY: ember-gated).
- **Live / real tokens**, **mainnet**, and the **production MPC VK ceremony**
  (today's on-chain proof rides a toxic-waste-known dev ceremony).
- The **security-review sign-off, honest-grade audit, and go-live decision**
  (`OPS-RUNBOOK.md` go-live checklist).

---

## THE single biggest REAL (non-gated) step

**Stand up a persistent n≥2 verified federation on the private infra and
re-point DrEX + offerings + the launchpad indexer at it.**

This is the one move that converts *"real engine + a solo node"* into *"a real,
deployed, enmeshed devnet."* "Devnet" literally means a running network, and
today there is a committee-of-ONE. Everything downstream that ember wants —
offerings enmeshed, cross-node finality, an honest launchpad indexer reading a
federated node, the on-chain settle from a live turn — needs a **durable
federated node to enmesh against**, and that is the only thing missing between
the proven ephemeral runs and a standing devnet.

Crucially it is **fully buildable-now and non-gated**: the federation code, the
shared-genesis committee, the QUIC gossip + blocklace finality, the reconnect
prober, and gossip-of-peers discovery are all landed and pinned by real
two/three-node tests. The remaining work is *operational* (a full-BFT Lean seed +
durable process units + one config re-point of `DREGG_NODE`), inside the
firewall, touching no public surface and no live token. Once it stands, the
on-chain-settle-from-a-live-turn wrap (thread 1) and the testnet deploys become
the *next* real steps — but the standing federation is the foundation they all
enmesh onto.

---

*Recon method: read `drex-web/serve.mjs`, `docs/ops/PRIVATE-NODE.md`,
`docs/ops/OPS-RUNBOOK.md`, `docs/deos/DEV-NODE-RUNBOOK.md`, `chain/DEPLOYMENTS.md`,
`chain/DEPLOY.md`, `GOAL-MULTICHAIN-SETTLEMENT.md`, `solana-settlement/`,
`cosmos-settlement/`, `launchpad-web/README.md`, `drex-web/offerings.mjs`,
`fhegg-fhe/HBOX-24CORE-ENVELOPE.md`. Live state from a single read-only
`GET /node/status`. No mutation, no service disturbed.*
