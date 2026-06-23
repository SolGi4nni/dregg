# App-layer + Federation census — the wide front (2026-06-23)

Now that the desktop boots and a node runs, this maps the REAL state of the app ecosystem and
federation so build lanes hit genuine gaps. Evidence-based (read the code, not the docs).
Companion to `RECONSTRUCTED-DIRECTIONS-2026-06-23.md`.

## App layer — the gap is WIRING, not building

`app-framework/` (`dregg-app-framework`) is real and **load-bearing**: the `DeosApp` builder folds
six pieces (cell affordances · server · embedded executor · web-of-cells distribution · rehydration ·
persistence seam) into one shape. **All 20 starbridge-apps depend on it and are fully built + tested.**

**The chasm:** `starbridge-v2` does NOT depend on `app-framework` or any starbridge-app. There is no
`AppRegistry`, no app picker UI, no affordance-surface tab. The powerbox can birth a *bare* confined
cell (`AppLauncher::launch`), but cannot open a *pre-built app* (gallery/tussle/…). The 20 apps live
only in their own workspaces (tests/examples), never mounted into the running cockpit.

The 20 apps (all BUILT-NOT-WIRED, all use the framework): first-room · gallery · tussle ·
sealed-auction · identity · polis · bounty-board · escrow-market · compute-exchange ·
agent-orchestration · swarm-orchestration · agent-provenance · supply-chain-provenance ·
tool-access-delegation · nameservice · governed-namespace · privacy-voting · storage-gateway-mandate ·
compartment-workflow-mandate · subscription.

starbridge-v2's own "app-shaped" modules (`mud.rs` `room.rs` `wonder.rs` `scene.rs` `web_cells.rs`
`doc_editor.rs` `snapshot_editor.rs` `simulate.rs` `dreggverse_map.rs`) are REAL but are cockpit
surfaces/tabs/panels — they power the desktop, they are not apps ON it (except wonder/mud, demo-only).

### App gap ladder (ranked; the fix is integration)
1. **AppRegistry + dep**: `starbridge-v2` depends on `app-framework` + the apps; a registry lists each
   (name, what, `*_app(cipherclerk, executor) -> DeosApp` ctor). First move: a new `app_registry.rs`.
2. **Launch a real app into the live World**: pick one (gallery) → call its `*_app()` over the cockpit's
   embedded executor → its affordances fire REAL verified turns on the live ledger. Prove by test.
3. **Affordance-surface tab**: a cockpit surface that opens a launched app's full affordance UI
   (`DeosApp::mount()` HTML / web-component, via `starbridge-web-surface`).
4. **App-launcher UI**: a picker (powerbox/palette) listing the registry; selecting one launches it.
5. **App state + roster persistence**: launched apps + the open-app roster survive logout/relaunch
   (extend `persistence.rs`/`view_cell.rs`, which already persist cells/workspace).
6. Inter-app notify-edge (bridge `swarm.rs`/`coordination.rs` to user apps) · per-app HTTP service for
   remote/federated reach (`app-framework/src/server.rs` + `mount()`) · app discovery via nameservice.

## Federation — the transport is WIRED; agreement is the gap

`federation_mode:"solo"` at n=1 is **real code**, not a stub (`SoloConsensusState` + nullifier log).
`consensus_live:true` = the blocklace task runs and makes blocks unilaterally (quorum(1)=1, self-signed).

**Transport WORKS today**: `net/` QUIC + Plumtree gossip (`GossipNetwork`/`PeerNode`); the blocklace
gossip protocol (`Push`/`Pull`/`Frontier`/`PullResponse`) is wired into `node/blocklace_sync.rs`;
`--federation-peers <addr,addr>` joins topics. Causal catch-up (orphan buffer + pull-on-gap) is
functionally complete. Cross-federation receipt verification (`KnownFederations::verify_receipt`) works
with manual genesis sharing. Full-turn STARK proving is live behind `--prove-turns`.

**DEAD/legacy** (don't touch): Morpheus BFT sim (`federation/node.rs`), `FederationTransport`/`Tcp`/`Local`
transports (gossip is the real path). **Scaffolding** (compiled, not called): threshold-decrypt, DKG,
beacon.

### The missing piece: agreement
Finality is computed **unilaterally per node** — each node decides "I have 2f+1 copies → Attested" with
**no vote message exchanged**. At n=1 that's fine; at n≥2 nodes can't *know* they agree.
Plus: **no peer discovery** (CLI-static only), **no peer retry** (`RequestBackoff` exists, unused for
gossip dial).

### Federation gap ladder
1. **DEMONSTRATE 2-node by running** (wire-existing): two `dregg-node` procs, `--federation-peers`
   cross-pointing → `peer_count>0`, a turn on A gossips to B, both DAGs converge. If it converges,
   federation is REAL; if not, this surfaces the true blocker. (This is rung-0, the proof.)
2. **Quorum vote collection** (Rung 3, the critical soundness gap): a `TOPIC_FINALIZATION_VOTES`
   channel — on local `Attested`, gossip a signed `FinalizationVote{block_id, level, sig}`; receiver
   marks Attested *consensus-wide* at 2f+1 votes. Unblocks genuine agreement.
3. Peer retry/backoff (wire `RequestBackoff` into a `peer_prober` task) · peer discovery bootstrap ·
   epoch rotation / committee reconfig (`blocklace/constitution.rs` scaffolded) · CapTP cross-node
   handoff over gossip · multi-signed attested roots (`AttestedRoot` quorum sigs).
