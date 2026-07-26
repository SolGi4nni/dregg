# DEEP archaeology — the LIVE / DEPLOYMENT reality

*Read-only archaeology, 2026-07-19. What RUNS where a stranger can touch it, made precise.
No code, no commits. Every claim cites file:line or a live probe. Current resolution, no round-up.*

Companion to `deploy/README.md` (the box-inspection ground truth, 2026-07-15) and `deploy/PRACTICES.md`.
Where this doc measured live reachability itself (2026-07-19), it says so.

## The one-sentence answer

The **logic** is real almost everywhere (real axum/Node servers, real redb-durable ledger, real
QUIC consensus, a real on-chain Groth16 verify on Base-Sepolia). What is missing for First Contact is
**durable public exposure of a *verified* node**: today a stranger can reach exactly **one** open web
surface (the games demo behind a Tailscale funnel, verified UP), but the verified ledger it and every
other surface would anchor to is **not durably deployed and not publicly reachable** — the last one was
a hand-run process whose ledger was permanently lost (`deploy/README.md:93-96`), and its replacement
exists only as an *uninstalled* systemd unit.

## Classification legend (current resolution)

- **RUNS-DURABLY** — survives reboot, publicly reachable, no ember-in-the-room needed.
- **RUNS-EPHEMERAL** — runs, but state lost on restart, or hand-run / behind an ember-gated flip.
- **RUNS-ON-EMBERS-LAPTOP** — only works in dev / loopback / local box.
- **NAMED** — a crate/endpoint/id exists by name but is a library, scaffold, or un-broadcast.
- **STUBBED** — returns mock/placeholder/hardcoded data on the served path.

---

## Live reachability, actually probed (2026-07-19, read-only GETs from the audit host)

| Endpoint | Result | Meaning |
|---|---|---|
| `https://hbox-dregg.skunk-emperor.ts.net/` | **200** — `<title>DreggNet Cloud — play + verify</title>` | The games funnel is **UP**. The one open surface. |
| `…/api/receipts`, `…/status`, `…/api/node/identity`, `…/healthz` | **404** | The "verify" half (node-backed receipts/identity/proof) is **not reachable** through it. |
| `https://dregg.commonquant.com/status` and `/api/receipts` | **401** | A server IS there, but behind an **auth wall** — not open First Contact. |
| `https://node.dregg.net/status` (the extension's default host) | **000 (no route)** | The extension's out-of-box node host resolves to **nothing**. |
| `http://34.224.208.52:8420/status` (the edge node's `0.0.0.0` bind) | **000 (no route)** | The "public" bind is **firewalled off** — not actually reachable. |
| `https://devnet.dregg.fg-goose.online/status` | **000 (dead)** | Confirms `deploy/README.md` TODO-5: the advertised devnet hostname is dead. |

Net: **one** freely-reachable surface (the games page), and its verification endpoints are 404.

---

## 1. THE NODE — `node/` (`dregg-node`)

The node binary is real and substantial (`node/src/lib.rs` is 2782 lines; `node/src/api.rs` 11269).

### Durability of the ledger — DURABLE *by code*, but scoped
- **Backing store is redb** (embedded ACID + WAL, fsync at commit boundary): `dregg_persist::PersistentStore`
  opens `<data_dir>/dregg.redb` (`node/src/state.rs:732-734`; `persist/src/lib.rs:1-12,184-195`; `persist/Cargo.toml:11`).
- **Crash recovery** is wired: `recover_to_last_consistent` + a ledger checkpoint + commit-log overlay
  rebuild the exact finalized ledger on boot (`node/src/state.rs:744-748, 840-913`).
- **DURABLE (redb-backed, survives restart):** cell/ledger state, the blocklace DAG, attested roots,
  checkpoints, nullifiers, the equivocation-court ledger, channel rosters, the witnessed-receipt
  anti-omission set (`persist/src/{federation,blocklace_store,checkpoint}.rs`).
- ⚑ **SUPERSEDED 2026-07-26 — the paragraph below is NO LONGER TRUE. Receipts survive a restart.**
  It landed on 07-21 (`7d64c71bb`) and 07-22 (`91247fe3f`), two days after this audit was written.
  Re-measured live on 07-26, not re-read: four serial faucet turns, kill, restart on the same data dir —
  `before: len=4 root=4b847b85…a44605` / `after: len=4 root=4b847b85…a44605`, byte-identical. A light
  client catches up too: SSE `Last-Event-ID: 0` after restart replays `chain_index` 1, 2, 3, and
  `/api/receipts/index/range` still serves the certified opening. `node/src/ws.rs` genuinely has no
  history replay, but that is by design — it is a notification stream; `events.rs` is the resumable one,
  and it resumes correctly now that chain indices are durable.
  ⚠ **A DIFFERENT and worse durability wound was found in the same reproduction, and is also fixed**
  (`e5c92ac80`): before its first checkpoint — 1000 blocks, or a graceful shutdown — a `kill -9` left the
  data dir **unbootable** (`recover_to_last_consistent: NO commit-log prefix reconstructs to its recorded
  root`). The store was fine; the CHECK was wrong (it reconstructs from an empty base and compares
  against roots committing the full ledger). So only a clean SIGTERM was survivable: power loss, OOM-kill
  and `docker kill` all bricked a young node. Six tests in that module already asserted the correct
  design and had been red, unread.
  *Kept verbatim below because the CITATIONS are still the right map of the seam.*
- **~~EPHEMERAL (lost on restart)~~, a sharp and important boundary:** the cipherclerk's **per-turn receipt
  chain** and the **receipt-index MMR head** served at `/api/receipts*`. The receipt chain is an in-memory
  `Vec<TurnReceipt>` initialized empty every boot (`sdk/src/cipherclerk.rs:1189,1263`); the MMR is rebuilt
  empty (`node/src/state.rs:1010,1203`); boot recovery restores the **ledger only** and moves a fresh
  empty-chain cipherclerk into state (`node/src/state.rs:940-943`); already-committed turns are marked
  executed and **skipped** on replay to avoid double-apply (`node/src/blocklace_sync.rs:2134,4918-4920`).
  **After a restart, `/api/receipts/index/head` serves `root = empty-MMR, len = 0`** and the chain
  rebuilds only from post-boot turns. The WS receipt stream (`node/src/ws.rs`) pushes live events with no
  history replay. So the finalized *state* is durable; the receipt *log a light client reads* is not.
- **Operational reality:** the durable data dir is only durable if the process is a real unit with a real
  `--data-dir`. The last live node was **hand-run with an ephemeral `--data-dir`** and its ledger — the
  operator cell + every anchored Descent run — was **permanently lost** on a box crash
  (`deploy/PRACTICES.md:34-37`, `deploy/README.md:93-96`).

### What "finalizes" — solo default is Tentative, not BFT-Final
- The deployed default is `--federation-mode solo` (`node/src/lib.rs:234`), a committee-of-one that
  "processes turns immediately without waiting for peers, skips gossip/consensus, **produces Tentative
  receipts**" (`node/src/lib.rs:228-235`; `solo_consensus` flag `node/src/state.rs:460-465`). BFT-**Final**
  receipts require full mode (n>1 committee) which is not durably deployed anywhere (§4).
- STATUS.md corroborates the single-process honesty caveat: a federation-less receipt has all-zero
  `federation_id` and `null` `executor_signature` (`STATUS.md:35-37`).

### Verified executor — fail-closed tripwire
- A node linked **without** the Lean executor archive (`lean_available()==false`) **refuses to start**
  (`exit(1)`) unless `DREGG_ALLOW_UNVERIFIED_CONSENSUS=1` (`node/src/lib.rs:908-943`). A `--release` build
  defaults `DREGG_REQUIRE_LEAN` on. So a marshal-only node is a deliberate opt-in, not a silent default.
- The PQ crypto cores (ML-DSA verify/sign, ML-KEM encaps/decaps) install the verified-Lean core as the
  authority when the archive exports them, else fall back to the `fips204`/`ml-kem` crates
  (`node/src/lib.rs:945-1097`).

### The light-client re-verify surface — real, and plumbed
- `GET /api/turn/{hash}/proof` serves the **persisted full-turn STARK proof bytes** from redb
  (`node/src/api.rs:2505-2524`), populated only under `--prove-turns`. A light client fetches and
  re-verifies via `dregg_sdk::verify_full_turn_bound` against the canonical revocation root.
- Receipt/verify endpoints exist and are wired: `/api/node/identity` (receipt-chain head,
  `node/src/api.rs:654-661`), `/api/receipts`, `/api/receipts/{hash}/witnesses`,
  `/api/receipts/index/{root,head,range}` (signed index head, `node/src/api.rs:1711-1734, 2354`).
  **Caveat:** per §1 durability, these serve a *per-node, in-memory* view that resets to empty on restart.
- `dregg-node mcp` exposes ~46 tools over **stdio JSON-RPC** (`node/src/lib.rs:327-339`, `node/src/mcp/`)
  — a local AI-assistant vector, **not** a network surface for a stranger.

**Node classification:** the binary is real; the ledger is **DURABLE-by-code**; the receipt log is
**EPHEMERAL**; the deployed posture is **solo/Tentative**; a durably-running instance a stranger can
reach is **absent** (see §2).

---

## 2. DEPLOYMENT TOPOLOGY — what actually runs, where

Two independent threads exist; neither delivers a durable public *verified* node today.

### Thread A — the direct-inspected boxes (`deploy/`, verified 2026-07-15)
- **Three boxes, TWO tailnets that cannot reach each other** (`deploy/README.md:17-37`): `edge`
  (AWS t3.medium, EIP `34.224.208.52`, tailnet `100.64.0.x`), `hbox` (GPU/prove + games, tailnet
  `skunk-emperor.ts.net`), `persvati` (build only, on both). "The edge's Caddy reverse-proxies hbox" is
  **false at the network layer**.
- **edge = a docker-compose stack** (`deploy/aws/README.md:59-94`): one container `dreggnet-dregg-node-1`
  = image `dregg-node:n5`, bound **`0.0.0.0:8420`** + `9420/udp`. **A single node (n=1)** — the observability
  file states it plainly (`deploy/observability/docker-compose.observability.yml:10-14`). But: **no public
  route** (no Caddy; `devnet.dregg.fg-goose.online` → HTTP 000, TODO-5), the image is **~2 weeks old and
  UNREPRODUCIBLE** — nothing in the repo builds the `:n5` tag (TODO-7, `deploy/README.md:140-155`) — and
  the compose file that defines it **exists only on the box** (TODO-4). My live probe of
  `34.224.208.52:8420` returned **000** (firewalled by `dregg-harden-firewall.service`). So the edge node's
  `0.0.0.0` bind is **not actually reachable**. Classification: **RUNS-EPHEMERAL** (running, undiffable,
  unreproducible, unreachable, durability of its docker volume unverifiable-from-repo).
- **hbox durable node unit EXISTS but is a proposed fix, not confirmed installed.**
  `deploy/node/dregg-node.service` is a proper durable user unit (linger, persistent
  `%h/.local/state/dregg-node`, `--prove-turns`, `--dev-unlock`), but it is **loopback-only**, **solo
  committee-of-one**, explicitly **"NOT the multi-node federation, NOT an on-chain settle, NOT a public
  surface"** (`deploy/node/dregg-node.service:21-27, 90-100`). Its RUNBOOK marks the durability check as
  **"needs the box to verify"** (`deploy/node/RUNBOOK.md:51,185-215`), and it is the fix for the **still-open
  TODO-1** — i.e. as of last inspection the hbox `:8420` node was **not durably deployed**. Classification:
  **NAMED** (unit authored; installation unconfirmed) → would be RUNS-DURABLY-but-loopback-and-solo if installed.
- **hbox games web = the one live public edge** (`deploy/games/dregg-web-games-funnel.service:1-11`):
  `dregg-web-games-funnel.service` (durable user unit + linger) binds loopback `:8790`, published by
  `tailscale funnel` at `https://hbox-dregg.skunk-emperor.ts.net`, **verified live + reboot-proof**.
  **Live-probed UP (200) on 2026-07-19.** BUT: the public flip is the ember-gated `tailscale funnel 8790`
  command (`:42-44`); it shares hbox with the prover that hard-killed the box once (`deploy/PRACTICES.md:9-19`);
  and its `DREGG_NODE_URL=:8420` anchor target is **DEAD** (`:7-11`).
- **The multi-node AWS federation topology NEVER RAN.** The systemd/Caddy/Graviton n=3 stack is quarantined
  in `deploy/aws/SUPERSEDED/` because it "does not exist and never ran here" (`deploy/aws/README.md:1-6`,
  `deploy/node/RUNBOOK.md:312-319`).

### Thread B — the GitHub-Actions "federation" + `dregg.commonquant.com` gateway (not in the 07-15 box audit)
- Three scheduled workflows `federation-node-{1,2,3}.yml` run a `dregg-node` on an **ephemeral ubuntu-latest
  runner** every 5h (350-min cap), peering to `GATEWAY_PEER = dregg.commonquant.com:9420`, persisting only
  thin `{node_id, ticket, last_seen}` state to a `federation-state` orphan git branch
  (`.github/workflows/federation-node-1.yml:14-18, 96-155`). A `discovery.yml` cron (every 30 min) advertises
  a discovery.json naming `dregg.commonquant.com` as an **"always-on Graviton"** gateway with
  `url/ws/api/gossip` (`.github/workflows/discovery.yml:95-101`).
- **Critical:** these workflows `cargo build --release -p dregg-node` with **no Lean-seed step**
  (`federation-node-1.yml:65-66`) → `lean_available()==false`. With `DREGG_ALLOW_UNVERIFIED_CONSENSUS`
  unset, the node's fail-closed tripwire (§1) makes the `run` **refuse to start / exit immediately**, and the
  release build likely fails the `DREGG_REQUIRE_LEAN` gate outright. So this cron "federation" is
  **marshal-at-best and likely non-starting**, publishing `{}`-shaped state.
- `dregg.commonquant.com` is **live but behind a 401** (probed 2026-07-19) — a server exists, but is not an
  open, verified, stranger-reachable dregg node. Classification: **NAMED / RUNS-EPHEMERAL** (advertised,
  auth-walled, CI nodes ephemeral + unverified).

---

## 3. THE SURFACES

| Surface | Classification | Note (cited) |
|---|---|---|
| **games web** `dreggnet-web` | **RUNS-EPHEMERAL** | Real axum `dreggnet-web-server`; live at the funnel (200). Sessions in-memory by default, durable only with `DREGGNET_WEB_SESSION_DIR` (`dreggnet-web/src/lib.rs:269, 2296-2380`). Public flip ember-gated; node anchor dead. |
| `dreggnet-web` `/descent/play` | **STUBBED** | Flagship in-tab game: `assets/descent/` (client.js+wasm) **does not exist**; route serves placeholder JS + 503 (`dreggnet-web/src/descent_play.rs:34-53,159-166`). |
| **discord-bot** | **RUNS-DURABLY** (surface+state) | Real serenity gateway, durable sqlite (`discord-bot/src/db.rs:204-210`); deployed as hbox unit (rehosted edge→hbox 2026-07-17, `deploy/hbox/dregg-discord-bot.service`) — "the only live instance." |
| discord-bot **$DREGG pay** | **STUBBED (mock default)** | Falls back to `MockWatcher` with no `DREGG_PAY_*` env (deploy sets none); credits nothing → free tier (`discord-bot/src/pay.rs:21,301,558,592-611`). Drand beacon/RNG is genuinely live-verified BLS (`discord-bot/src/reveal_cron.rs`). |
| **dreggnet-telegram** | **RUNS-EPHEMERAL** | Runnable bin, durable replay sessions, but **"NOT YET INSTALLED ANYWHERE"** — token ember-gated (`deploy/telegram/dregg-telegram-bot.service:3`). |
| **dreggnet-wechat** | **NAMED** | Library only, no bin, only `MockTransport`; token fetch out of scope (`dreggnet-wechat/src/transport.rs:44-96`). |
| **dreggnet-discord-identity** | real library primitive | blake3 seed derivation, byte-pinned; no standalone surface. |
| **extension** (MV3 wallet) | **RUNS-ON-EMBERS-LAPTOP** | Real ed25519+ML-DSA self-custody, real wasm verify (Rust re-exec, **not Lean**, inherits FRI floor); **UNPUBLISHED** to any store (`extension/REVIEWER-NOTES.md:60-87`), sideload-only. Default host `node.dregg.net` probes **000**. |
| **`<dregg-*>` web components** | **EXTENSION-ONLY** | `customElements.define`d only in the extension content-script isolated world (`extension/src/content.ts:8-57`, `extension/src/elements/*.ts`). **No open-web page mounts them**; there is no `<dregg-verify>`. The "sdk"/"server" open-web tiers are dead strings. |
| **deos-web-cells** | **NAMED** | Content-address/attest library; render-to-pixels seam (servo/leptos) unbuilt (`deos-web-cells/src/lib.rs:49-65`). |
| **dreggnet-offerings / -surfaces** | **NAMED** | Consumed libraries; `MockFrontend` is test-only (`dreggnet-offerings/src/mock.rs:1-6`). |
| **launchpad-web** | **RUNS-EPHEMERAL** | Real Node server over real EVM contract / node turn stream; funnel flip ember-gated, not reachable today; `public/receipt.html` is an anvil-31337 snapshot (`launchpad-web/public/receipt.html:42`). rung-1 can run node-free on a testnet contract + user wallet. |
| **drex-web / drex-web-v2** | **RUNS-ON-EMBERS-LAPTOP** | Real Node shelling to real Rust binaries (`drex_clear`/`fhegg_clear`); loopback, no deploy unit; baked snapshot only as offline fallback. |
| **starbridge-web-surface** | **NAMED** | Rust library, no bin; real cap primitives but `MockSurface` (libservo seam not linked) (`starbridge-web-surface/src/lib.rs:141-150`). |
| **site/** (GitHub Pages) | **MIXED** | Deploy is `workflow_dispatch`-only (**push does not publish**), default `*.github.io`, no CNAME (`.github/workflows/pages.yml:30-47`). `light-client/`, `root/`, `dregg-works/` = real in-tab crypto verify over committed snapshots (**RUNS-DURABLY only if ember dispatches Pages**); `explorer/` = **STUBBED** hardcoded arrays; `grain/`,`deos-viewer/` = laptop. |
| **web/**, **web-studio/** | **RUNS-ON-EMBERS-LAPTOP** | Local Lean→wasm / shader PoCs, deployed nowhere. |

**Security flag surfaced by the surfaces lane:** `/Users/ember/dev/breadstuffs/discord-values` is a
**live `DISCORD_APP_ID` + `DISCORD_TOKEN` in plaintext at the repo root** (122 bytes) — the credential
behind "the only live bot instance." Recommend rotating + removing.

---

## 4. FEDERATION / MULTI-NODE

- **The consensus layer is real and in-binary.** Real QUIC transport (quinn/rustls, `node/src/lib.rs:584-587`,
  gossip UDP `:9420`); blocklace Cordial-Miners DAG BFT with tau ordering is the default engine. The real
  service modules run in the deployed binary — `pub mod blocklace_sync, finality_gate, finalization_votes,
  gossip, committee_replay, equivocation_court_service, dkg_service, catchup` (`node/src/lib.rs:13-86`) — as
  distinct from the `#[cfg(test)]` harnesses (`*_e2e.rs`, `node_integrator_e2e`, `epoch_transition_e2e`,
  `shared_world_e2e`, etc.).
- **Does it finalize across independent node PROCESSES?** Yes — the federation lane confirms real in-binary
  multi-node consensus that finalizes across separate node *processes*, **demonstrated on loopback**. But
  the **deployed default is solo n=1** (§1–2), single-turn finality is **timing-fragile**, and
  **fault-tolerant / cross-host production finality is an honestly-labeled open gap**.
- **Durability boundary (federation lane, corrected):** finalized state / DAG / attested roots / checkpoints
  are **DURABLE** (redb: `persist/src/federation.rs:526,567`, `persist/src/blocklace_store.rs:220`,
  `node/src/api.rs:5478,6881`); the **receipt log served to a light client is EPHEMERAL** (§1). `catchup.rs`
  converges the DAG from peers, not the cipherclerk receipt chain.
- **The only multi-node runs on record are ephemeral + private + marshal.** `GOAL-FEDERATION.md:24-33`
  records ember's n=4 federation running on a **home LAN** (`192.168.50.39` + `.130`), **marshal-only**
  (`full_turn_proving=false`), hand-run/"left running", with a "07-07 PAYOFF" that is **SUPERSEDED** and
  must be re-validated on HEAD (PQ hybrid + stark-kill changed the wire; gate-ON round-2 STILL UNPROVEN,
  `GOAL-FEDERATION.md:11-19`). Not durable, not public, not verified.

**Federation classification:** consensus code = real, in-binary; cross-process finality = **RUNS-ON-EMBERS-LAPTOP**
(loopback / home-LAN, ephemeral, marshal); durable public BFT finality = **absent**.

---

## 5. REPRODUCIBLE BUILD / VK FREEZE / CI  (the "green means something?" axis)

The memory's "green is a self-recompute tautology" is **too pessimistic for the current tree** in part,
**exactly right** in part:

- **MEANINGFUL — the bare-clone reproducibility gate.** `repro-gate.yml` + `scripts/bare-clone-repro-gate.sh`
  run on every push/PR: bare clone into an **empty `HOME`/`CARGO_HOME`**, resolve+build **`--locked`**, with a
  **self-arming canary** that injects a sibling-path `[patch]` and requires the resolve to FAIL
  (`repro-gate.yml:41-67`, `bare-clone-repro-gate.sh:78-102,134-164,173,195,210`). A stranger's bare clone
  reproduces this; tampering reds it. (It checks build reproducibility, **not** byte-identical artifact digest;
  covers the root workspace only; the full `--workspace` build is `workflow_dispatch`-only.)
- **TAUTOLOGY — the recursion VK.** `lookup_recursive_vk` returns `Some` iff the hash equals
  `compute_recursive_vk_hash()` — producer and verifier call the same function; nothing pinned externally
  (`circuit-prove/src/recursive_witness_bundle.rs:191-192, 146-183, 313, 374`). Catches a stale-rev proof,
  not a forged VK.
- **FROZEN CONSTANT but NOT CI-exercised — the apex settlement VK.** `DREGG_APEX_RECURSION_VK` is a committed
  hex constant compared against a runtime-derived fingerprint, fail-closed
  (`circuit-prove/src/apex_shrink_gnark_export.rs:216-237`); mirrored in Go (`chain/gnark/settlement_circuit.go:122`).
  A genuine freeze pin — **but its drift-check test is `#[ignore]`** (`circuit-prove/tests/apex_shrink_gnark_fixture.rs:290`)
  and **no CI workflow references it**; `armed-teeth.yml` explicitly excludes the apex probes (`:87-90`). And
  the underlying Groth16 params are a **single-party dev ceremony with KNOWN toxic waste**
  (`chain/gnark/groth16_cache.go:17-25`). So no automated gate catches apex-circuit drift.
- **MEANINGFUL — the Lean seed + faithfulness gate.** CI builds+publishes a content-keyed seed on a
  self-hosted runner (`lean-seed.yml`), and `lean-marshal-gate` fetches it and runs a **denotational
  Lean↔Rust differential**, fail-closed, with anti-vacuity hardening on empty-TAG (`.github/workflows/ci.yml:525-613`).
  Trust residual: the seed binary is built by ember's runner (content key proves asset↔source, not faithful compile).
- **MEANINGFUL — descriptor drift.** `check-descriptor-drift.sh` re-emits from Lean and **diffs** against the
  committed staged TSVs (not a rehash), ack-gated on re-key (`.github/workflows/ci.yml:889-936`). Still
  `-staged`-named; the freeze (rename/retire) is not done.
- **Gaps a stranger should know:** main `ci.yml` build/test is **not `--locked`** (`:49,108,188`); the
  **gnark Go verifier tests run in NO CI workflow**; the `sdk-py` wire-drift gate is **release-tag-gated,
  not PR-gated** (`publish-sdk-py.yml:26-30`); the nightly `armed-teeth.yml` light-client teeth were **RED at
  landing** (8/8 binaries) — a real, non-tautological gate currently reporting a real failure.

---

## 6. ON-CHAIN / SETTLEMENT

- **Exactly one real on-chain deployment in the whole repo: Base-Sepolia (chainId 84532).** A real
  `settle()` tx verified a real Groth16 proof on-chain:
  DreggSettlement `0x6c87b53530c8392F22bab3B004919EBC4E86Bd87`, settle tx
  `0xbd2cac6a54d27ff818c46ad67667412a489001cc4c382193cf7ac757229e963b`, `provenHeight()==2`
  (`chain/DEPLOYMENTS.md`, `chain/broadcast/DeploySettlement.s.sol/84532/run-latest.json`). The gnark
  verifier is a **real R1CS constraint system** (replays FS transcript, batch-STARK algebra, native FRI with
  grinding), not a calculator (`chain/gnark/settlement_circuit.go:205-336`). `emitted_verifier_full.go` is a
  **constraint-counting interpreter**, not the on-chain verifier.
- **HONEST soundness caveats:** it settled a **pre-generated fixture** (a real 2-turn apex, "not yet a live
  user turn", `chain/DEPLOYMENTS.md:19`) via a **hand-run forge script** (no automated node→prove→submit
  path — relayers are observe-only; proof-gen fail-closes `WrapProverMissing`; `bridge/src/ethereum.rs:473-520`).
  The VK is `keccak256("dregg-settlement-vk-dev-setup")` from a **single-party dev ceremony whose toxic waste
  is KNOWN** — no MPC tooling exists (`chain/gnark/groth16_cache.go:17-22`, `settlement_snark_test.go:7-11`).
- **Everything else = real verifier code, RUNS-ON-EMBERS-LAPTOP / NAMED:** Solana settlement + lock (real
  BN254/alt_bn128 verifier, but `solana-program-test` in-process only, program id = a local keypair, never
  broadcast — `solana-settlement/tests/settle_flow.rs:19,28-29`, `DEVNET-DEPLOYMENT-REALITY.md:118`); Cosmos
  settlement + lock (real, `cw-multi-test` only, `cosmos-settlement/src/lib.rs:28`); eth/cosmos light clients
  (real BLS/Tendermint crypto over **captured offline fixtures**, not running services —
  `eth-lightclient/src/bin/verify_holding.rs:20-24`). The DreggVault/CredentialGate stack was **never
  deployed** and is wired to `SP1MockVerifier` (always-accept) for dry-runs (`chain/DEPLOY.md:13-14,42`) — STUBBED.
- **The sharp line:** a stranger CAN independently confirm on basescan that tx `0xbd2cac6a…` called `settle`
  and succeeded. A stranger CANNOT conclude it corresponds to a genuine dregg state transition — the VK is
  toxic-waste-known (forgeable) and the wrapped STARK/FRI carries its own undischarged soundness floor.

---

## 7. ⚑ THE PRECISE FIRST-CONTACT GAP

*"A stranger plays a dregg world AND independently verifies it, on a durable public node, no ember in the room."*
Here is what RUNS today vs what is MISSING, enumerated.

### What already runs (the assets First Contact can build on)
1. A **real durable-by-code node** with redb ACID storage + crash recovery, a fail-closed verified-executor
   tripwire, and a light-client proof endpoint (`/api/turn/{hash}/proof`) — §1.
2. **One live open web surface**: the games demo (200, reboot-proof funnel) — §2. Games are cheat-proof by
   in-process replay even node-free.
3. A **real on-chain settlement verify** on Base-Sepolia and a real bare-clone reproducibility gate — §5, §6.
4. Real in-binary multi-node QUIC consensus that finalizes across processes on loopback — §4.

### What is missing (the First-Contact prerequisites, precise)
1. **A durable, publicly-reachable, VERIFIED node.** Today: the hbox durable unit exists but is
   **loopback-only + solo + possibly uninstalled** (TODO-1); the edge node is **firewalled off + unreproducible**;
   `dregg.commonquant.com` is **401-walled**; `node.dregg.net` **resolves to nothing**. Need: install the
   durable node unit (or a container with a durable volume) **bound to a public interface behind TLS**, running
   the **Lean-linked verified executor**, with a stable DNS name. (`deploy/node/dregg-node.service` +
   `deploy/README.md:107-113` TODO-1; probes in the table above.)
2. **A DURABLE receipt log.** The receipt chain / MMR head a light client verifies against is **in-memory and
   empties to `len=0` on restart** (§1). Need: persist + reload the cipherclerk receipt chain (or serve the
   head from the durable store), so `/api/receipts/index/head` survives a reboot.
3. **BFT-Final, not solo-Tentative.** The deployed default produces **Tentative** receipts (committee-of-one).
   Need: a durably-deployed n≥3 committee (real `genesis.json` + peers + full mode) running the verified
   executor so receipts are BFT-Final and cross-node — the multi-node path has only ever run **ephemerally on a
   home LAN, marshal-only** (§4). The committed devnet genesis material exists (`deploy/genesis/`) but the
   n=3/4 topology **never ran durably**.
4. **A public route + client that points at the durable node.** The games page's verify endpoints 404; the
   extension defaults to a dead host; there is **no open-web `<dregg-verify>`** (components are extension-only).
   Need: wire a public surface's verify UI (or the extension's default host) to the durable node's
   `/api/receipts` + `/api/turn/{hash}/proof`, and ship the extension (unpublished today).
5. **A real value rail (if payment is in scope).** The Discord `$DREGG` pay is a **MockWatcher** (credits
   nothing); on-chain settlement is a **fixture under a toxic-waste-known single-party VK** with **no automated
   node→chain pipeline**. Need: an MPC ceremony VK + a real relayer submit path for value to actually settle.
6. **Reproducible artifact + frozen VK (for "independently verify").** The bare-clone build gate is meaningful,
   but the recursion VK is a tautology, the apex VK freeze is **not CI-exercised**, and no VK is under a real
   ceremony. Need: CI-arm the apex-VK drift check, run the MPC ceremony, and freeze (retire `-staged`).
7. **Off ember's box, unattended.** Every public flip is **ember-gated** (the `tailscale funnel` command, the
   Pages `workflow_dispatch`, the BotFather/ceremony tokens). Need: the durable node + its public route to be a
   unit/container that comes up on reboot with **no human flip**.

---

## 8. DEMOED vs DEPLOYED vs DURABLE (the honest three-way split)

- **DEMOED (works when ember runs it / on ember's box):** the n=4 home-LAN federation (marshal, ephemeral);
  the extension (sideloaded); drex-web / web / web-studio PoCs; the Solana/Cosmos programs + light clients
  (in-process / offline fixtures); `site/light-client` etc. (real verify, but only if Pages is hand-dispatched).
- **DEPLOYED (running where a stranger *could* reach, with caveats):** the games web page
  (`hbox-dregg.skunk-emperor.ts.net`, live 200, but ember-gated funnel + co-tenant box + dead node anchor +
  404 verify endpoints); the Discord bot (live, durable state, but mock pay + dead node); the edge node
  container (running but firewalled-off + unreproducible); the Base-Sepolia settlement contracts (real, but a
  fixture under a toxic-waste VK); `dregg.commonquant.com` (up, but 401-walled).
- **DURABLE (survives reboot, reachable, no ember flip):** **nothing end-to-end.** The redb ledger, the
  blocklace DAG, the games session store (with `DREGGNET_WEB_SESSION_DIR`), and the funnel/units-with-linger
  are each durable *in isolation*; but there is **no durable, public, verified node** for a surface to anchor
  and verify against. That single missing box is the whole First-Contact gap.

---

*Method: careful reading (not grep-and-guess) of `node/`, `persist/`, `deploy/`, `chain/`, the surface crates,
and the CI workflows, plus live read-only endpoint probes on 2026-07-19 and four parallel deep-read lanes
(surfaces, reproducible-build/VK/CI, on-chain settlement, federation durability). Classifications are at
current resolution; nothing is rounded up to intent.*
