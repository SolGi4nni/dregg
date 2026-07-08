# GOAL — THE DISTRIBUTED INHABITED WORLD: the sovereign live image, across machines

*(A hyperdreggmedia-epoch north star, distinct from the storage-in-lean GOAL.md — that file is
another campaign's and stays untouched. This one lifts INHABITATION onto the distributed ledger.
Set 2026-07-06, Fable→Opus, with ember: "all four pillars + capstone.")*

## The thesis (load-bearing)

**The consensus layer is already distributed. The inhabitation layer is not — yet.**

The node has blocklace consensus, finality at n≥2, a gossiped shared ledger across boxes (built,
proven, runs). But every inhabitation primitive built this epoch — presence, co-driven cards,
surface migration, the confined soul on the live cockpit — runs SINGLE-PROCESS over an embedded
`Rc<RefCell<World>>`. The inhabited world is trapped on one machine while the ledger under it
already spans three.

So the mission is not "build a network." It is **lift inhabitation onto the ledger that is
already distributed.** The `hbox-persvati-nextop` localnet (and the David homelab when it wakes)
is the iron this validates on.

**THE INVARIANT, one line:** *every cross-machine action is a cap-carried verified turn on the
shared ledger; the network is never trusted, only the proof is.* This is the firmament "one cap
across distance" thesis (proven for seL4, `project-firmament-sel4-boots`) generalized to the
inhabited world.

## STATUS (this IS the goal file — GOAL.md is storage-in-lean's, off-limits; refresh here each landing)

**⚑ A-BAR PHASE COMPLETE (2026-07-07).** Every mechanism of the distributed inhabited world is BUILT
+ GREEN + committed: Pillars 0, 1, 2, 2b, 3, 4a + the shared `test-support` TestNode. The wire is
dumb, the proof is smart — proven in-process / loopback / over a local Conduit, each with two poles.

**"DREGG HOSTS THE COMMUNITY" — two buildable-now sibling threads (NOT iron-gated):**

- **homeserver-as-a-grain** (`docs/deos/GRAIN-HOMESERVER.md`) — makes Pillar 3 self-hosted; the Matrix
  homeserver becomes a confined, metered, R2 grain. Body: a Rust conduit-lineage homeserver embedded
  as a **lib** in the grain body (NOT execve — the census found conduit-family is `[lib]`+thin`[[bin]]`,
  so the execve door DISSOLVES; and `Confinement::with_fds` already hands a pre-bound listener fd, so
  the listen door mostly dissolves too → the "three doors" collapse to ONE: `grant_read_write` for the
  DB dir). `~/src/conduit` is dormant; a LIVE SCOUT (continuwuity/tuwunel/grapevine: alive? lib clean?
  matrix-sdk-compat?) is running to pick the real fork. Non-Rust homeservers (Synapse/Dendrite) ride
  the **sandstorm rail** (execve-in-chroot .spk grain) — both worlds covered.
- **dregg-native forge** (`docs/deos/DREGG-FORGE.md`) — no git; dregg's Pijul patch theory IS the VCS
  (`dregg-doc/depend.rs` = operational Pijul, `cell_git.rs` git-face, branch-and-stitch = PRs,
  `COLL_HISTORY` = owned history). First slice BUILDING: the `PullRequest` object + review-as-stitcher
  (clean→pushout merge; conflict→ConflictRegion refused-until-resolved; non-cap-holder merge refused),
  welded over the existing patch core via executor_drive's cap gate. The forge-grain is the
  homeserver-grain's sibling — a town with a square and a workshop.

**What remains is IRON-GATED (ember): the b-bars + the capstone need real boxes.** Nothing more is
buildable-now without the `hbox-persvati-nextop` localnet. Do NOT invent busywork. When the localnet
is up, the iron pass runs the b-bars box-by-box (each named in its pillar's done-log entry), then the
three-box co-inhabited-room CAPSTONE — a human on one cockpit + a confined agent on another, presence
+ speech + a co-authored card, all ledger-proven. Tag AFTER it runs on iron.

**ADJACENT VISION (recorded, not scheduled — ember via deepfates, 2026-07-07): dregg = the VERIFIED
Semantic Web.** PROV-O (Entity/Agent/Activity · wasDerivedFrom/wasAttributedTo/wasGeneratedBy/used)
is exactly dregg's provenance graph — but ASSERTED triples are why the Semantic Web failed, and
dregg's edges are PROVEN: a receipt chain IS wasDerivedFrom, a turn IS an Activity (wasGeneratedBy),
the signer IS wasAttributedTo. `provenance_navigator.rs` already WALKS this graph (a turn that touched
a cell = its lineage). No PROV-O / RDF face exists yet. The artifact = a PROV projection over the
EXISTING receipt/turn/agent graph (another glass — renderer-independence), giving Semantic-Web-tooling
interop for free; the Org Ontology maps onto dregg governance (org cell · membership = cap-holding ·
roles = attenuated caps · Polis). A future thread, not a swarm.

**The b-bar checklist (for the iron pass):**
1. Pillar 1 — surface migrates hbox→persvati; revoke darkens the far glass one round-trip.
2. Pillar 2b — 3 inhabitants on 3 boxes, one room; each derives its speak cap from its own node's
   ledger crawl (`NodeWorldSink` over a real node); a revoked speaker refused from every view.
3. Pillar 3 — two cockpits on two boxes co-drive one card over a shared homeserver.
4. Pillar 4 — a confined brain on box A commits through its node; the cockpit on box B repaints from
   box B's ledger.
5. Capstone — all four at once, human + confined agent co-inhabiting.

## THE DISCIPLINE (carry it into every pillar)

- **Mechanism now, iron later.** Each pillar splits into (a) the mechanism, built + tested THIS
  session two-process / loopback / over a local Conduit; and (b) the cross-box validation that
  lands when the localnet is confirmed up. Build (a) green now; tag (b) only after seeing it work
  on real boxes (empirical-validation > paper-green, [[feedback-empirical-validation-n3]]).
- **Ride the ledger, don't reinvent it.** Cross-box state travels as cells on the gossiped
  ledger; cross-box authority travels as caps (attenuated, never amplified); cross-box effect is
  a verified turn with a receipt. No pillar invents a trusted side-channel. Where a pillar needs
  a transport (Matrix, a network world-bridge), the transport carries BYTES whose acceptance is
  re-checked against the ledger/root — the wire is dumb, the proof is smart.
- **Two poles or it didn't happen.** Every proof-bar tests the honest path AND the adversary
  (forged cap refused, revoked speaker silenced, substituted envelope rejected). A green that
  can't red when the thing it guards breaks is worthless.
- **Shared-tree hygiene.** Main loop owns shared-manifest edits + commits; agents draft disjoint
  files; NO worktrees ([[feedback-swarm-shared-tree-clobber-hazard]]). Live sibling sessions this
  epoch: the VK/circuit flip (`circuit/**`, `circuit-prove/**`, `sdk/tests/gentian*`,
  registry TSVs), storage-in-lean (`metatheory/Dregg2/Storage/**`, GOAL.md), a localnet driver
  (`node/**`, `deploy/**`). Stay off those.

## PILLAR 0 — THE FOUNDATION: a node-backed WorldSink (the dependency root)

The inhabitation layer speaks `deos_js::WorldSink`:
```rust
pub trait WorldSink {
    fn with_ledger(&self, f: &mut dyn FnMut(&Ledger));
    fn fire_effects(&mut self, agent: CellId, method: &str, effects: Vec<Effect>) -> Result<[u8;32], String>;
    fn mint_open_cell(&mut self, seed: &str, funding: u64) -> Result<CellId, String>;
}
```
Today the only impls are the embedded (cockpit `Rc<RefCell<World>>`) and the socket world-bridge
(same box). **Build a `NodeWorldSink`** that commits `fire_effects` via the local node's
`POST /turns/submit` (a signed turn) and answers `with_ledger` from `GET /api/cells` — so N boxes
each glass their local node and SHARE the gossiped ledger. Precedent already in-tree:
`dregg-tui` is a terminal light client over the node HTTP API (`/api/node/identity`, `/api/cells`,
`/api/receipts`) whose Verify tab independently checks a real STARK — a glass that trusts the
proof, not the server. Generalize that from read-only to read+commit.

- **Proof-bar (a, now):** a `NodeWorldSink` against a single in-process test node commits a turn
  (`fire_effects` → real receipt) and reads it back (`with_ledger` sees the new cell state);
  a forged/over-reaching effect is refused by the node's executor, not by the sink.
- **Proof-bar (b, iron):** two `NodeWorldSink`s on two boxes pointed at two gossiping nodes — a
  turn committed on box A is visible via box B's sink after finality.

Pillars 1/2/4 ride this. Pillar 3 may ride Matrix instead (decided in-pillar).

## PILLAR 1 — THE WORLD CROSSES THE WIRE (distributed surface migration)

Built: `MigrationTarget::{Local,Surface,HostPd}` (`dock/migrate.rs`), `Shell::migrate_surface`
(`shell.rs`), the HostPd endpoint round-trip (`sel4/dregg-firmament/tests/surface_migration_endpoint.rs`),
the CapTP handoff nonces (`sturdy.rs`/`handoff.rs`), the `NetworkBoundary`/`ConsentRequest` seam
(`shared_fork.rs`). Missing: a `Target`-level Distributed re-home + a network transport for the
`SurfaceCapability`.

- **Build (a):** `MigrationTarget::Distributed` + carry the re-homed `SurfaceCapability` over a
  `dregg-sdk-net`/captp transport; the cap is re-minted preserving `SurfaceId`, attenuated, the
  handoff nonce one-shot.
- **Proof-bar (a, now):** two-process — a surface migrates Local→Distributed to a second process's
  Endpoint; input routed, present painted, cap preserved+attenuated; a forged cap refused every op;
  a replayed handoff nonce refused.
- **Proof-bar (b, iron):** a surface opened on hbox re-homes to persvati; revoke darkens the far
  glass in one round-trip; the café-phone tier (display-cap, no input-grant) holds.

## PILLAR 2 — PRESENCE PROVEN FROM THE SHARED LEDGER (multi-node MUD)

Built: MUD phase 2 (`mud.rs`) — `PresenceToken` conserved, `RoomVoice` over the Bus, every absence
polarity refused by `SendCap::admits`. Named seam: speak-cap issuance is host-side, per-Bus.

- **Build (a):** derive the speak cap as an **attenuation of the on-ledger presence token** (so
  issuance is a receipted grant, and ANY box proves the cap from its ledger copy); hearer identity
  becomes the session pubkey, not cell bytes; presence read from the (node-backed) ledger.
- **Proof-bar (a, now):** three inhabitants, three `NodeWorldSink`s on one test node — one room;
  A says, B and C hear in order; the speak cap is provable from each inhabitant's ledger view; a
  revoked/absent speaker refused from every view; presence conserved (never two rooms).
- **Proof-bar (b, iron):** the three inhabitants on hbox/persvati/nextop; the room spans the net;
  presence + speech provable from each box's own ledger; a partition heals without a ghost.

## PILLAR 3 — TWO COCKPITS CO-DRIVE ONE CARD (membrane across a live homeserver)

Built: `distributed_card.rs` (seal_fork→open_envelope→rehydrate_fork→stitch_envelopes, both edits
survive, anti-substitution root tooth); `deos-matrix::membrane.rs` `MembraneEnvelope` (text_fallback).
Seam: the envelope crosses an in-TEST boundary only.

- **Build (a):** carry `CardForkEnvelope` bytes in a `MembraneEnvelope` over a live Conduit
  homeserver (the `./scripts/live-test.sh` Docker Conduit is the local rig); the stitch lands on
  both ends; acceptance re-checked against the root tooth (a substituted envelope refused).
- **Proof-bar (a, now):** two cockpit processes on ONE box, one local Conduit — fork one card,
  each edits, envelopes cross the real server, stitch → both edits survive on both; a true conflict
  is a `ConflictRegion` on both glasses; a forged envelope refused.
- **Proof-bar (b, iron):** the two cockpits on hbox and persvati against a shared homeserver.

## PILLAR 4 — THE SOUL INHABITS THE DISTRIBUTED WORLD (confined brain, cross-box)

Built: the world-bridge cockpit binding (`DEOS_WORLD_BRIDGE_SOCKET`, `ef749253d`) × the jailed brain
(`host.rs::brain_body_serving`, real ACP brain in the confined PD; live-LLM behind `live-brain`).
Today the bridge is a Unix socket (same box).

- **TRANSPORT DECISION — RESOLVED (node-backed, 2026-07-07):** now that Pillar 0's `NodeWorldSink`
  exists, (ii) wins decisively — it composes out of already-built pieces and honours discipline #3
  (ride the ledger). The confined brain gets a `NodeWorldSink` (`run_attached_on` already takes any
  `Box<dyn WorldSink>`) reaching its node ONLY through the jail's granted `grant_provider`
  egress door; run_js commits verified turns to the node; the remote cockpit repaints from the
  gossiped ledger. No new trusted transport — the egress door + the node's executor are the gates.
  (i) the network world-bridge is retired as redundant. Manifest: deos-hermes `node-brain` feature.
- **Build (a):** the chosen transport, so a confined brain in one process drives a live cockpit
  World in another — every run_js a cap-gated verified turn under the agent's `held`, fail-closed.
- **Proof-bar (a, now):** a confined LocalBrain in process A crawls process B's cockpit cells and
  fires a receipted turn that appears on B's World; execve/host-FS/other-net stay denied; over-reach
  refused in-band.
- **Proof-bar (b, iron):** the confined brain on hbox, the painted cockpit on persvati; the
  receipted turn appears on the remote glass.

## THE CAPSTONE — a co-inhabited room across three boxes

A room in the MUD spanning hbox/persvati/nextop; a HUMAN on one cockpit and a CONFINED AGENT on
another co-inhabiting it — presence, speech, and a co-authored card, all ledger-proven, none of it
trusting the wire. When this runs on iron, the sovereign live image is distributed: the same world,
many glasses, many souls, one proof.

## SEQUENCING (dependency-ordered; each step a green-gated commit)

0. **Foundation** — `NodeWorldSink` (a-bar). Everything downstream leans on it.
1. **Pillar 2 mechanism** — speak-cap-from-token over the node-backed ledger (most visceral, rides
   consensus most directly; the natural first pillar once the foundation stands).
2. **Pillar 1 mechanism** — `Target::Distributed` surface migration (two-process).
3. **Pillar 3 mechanism** — card envelope over a local Conduit (independent of Pillar 0 — can run in
   parallel with 1/2 since it rides Matrix, not the NodeWorldSink).
4. **Pillar 4** — transport decision, then the confined brain cross-process.
5. **Iron pass** — the (b)-bars, box by box, as the localnet confirms up.
6. **Capstone** — the three-box co-inhabited room; tag AFTER it runs.

Parallelizable now (disjoint files, no live-sibling collision): Pillar 3's Conduit lane
(`deos-matrix` + `starbridge-v2/src/distributed_card.rs`) alongside Foundation (`deos-js` glass +
a new `NodeWorldSink` home). Serialize Pillars 1/2/4 after the foundation lands.

## HONEST STARTING STATE (what's built vs frontier, grounded at HEAD)

- BUILT single-process: presence+say, distributed_card, surface migration (Local/Surface/HostPd),
  the world-bridge (Unix), the confined brain, the reflective cockpit, the four renderers.
- BUILT + distributed already (ride it): blocklace consensus, finality n≥2, the gossiped ledger,
  the node HTTP API, `dregg-tui` as a read-only node glass.
- FRONTIER (this goal): `NodeWorldSink`, `Target::Distributed`, speak-cap-from-token, the live
  Conduit card carry, the cross-box world-bridge/soul, the three-box capstone.

## Done-log
*(append one line per landing: commit · pillar · the two-pole proof · a-bar or b-bar)*
- test-support (infra) — `dregg_sdk_net::test_support::TestNode` exported (real TurnExecutor, private
  duplicate deleted → one node); closes Pillar 4a's round-trip: `node_backed_round_trip.rs` proves a
  confined brain's run_js commits THROUGH node execution + reads the receipt back. dregg-sdk-net
  70 unit + 4 doc green (stale crate-split doctests fixed). Shared infra for Pillar 2b + the capstone.
- Pillar 4a (a-bar, wiring) — `node_hands.rs` (deos-hermes, `node-brain` feat): a confined brain's
  run_js gets a `NodeWorldSink` reaching its node ONLY through the granted egress door;
  `check_endpoint` gates the endpoint before booting anything; fail-closed on node refusal. 94 green,
  both poles (Pole B admits-layer per provider_egress). Round-trip THROUGH node execution deferred to
  the `test-support` TestNode export (next unit — shared infra for the 4a full proof + 2b).
- homeserver-grain STEP 1 (community thread) — `deos-homeserver/`: continuwuity boots IN-PROCESS as a
  library (`conduwuit::run_with_args`) and serves the CS API — `cs_api_roundtrip` proves versions →
  register → createRoom → send → sync round-trips. Embed PROVEN. Real blockers found+fixed: `[patch]`
  doesn't propagate through git-deps (mirrored continuwuity's 5 fork pins) + an askama 0.16 macro-span
  bug (vendored one-line patch, `vendor/askama_derive/PATCH.md`); `force_disable_first_run_mode` for
  open reg. Doors teed up: `data_dir()` (grant_read_write) + `port()` (with_fds). RocksDB: keep it,
  system-link later. NEXT: card-carry over this homeserver (subprocess), then the confined spawn.
- dregg-forge review-threads (community thread) — `dregg-doc/review.rs`: comments + approvals as
  owned receipted atoms (Op::Add through the cap gate, attributed by blame, immutable; a non-holder
  comment refused in-band); approval-as-required-check wired into the CI gate. Both poles, substrate
  164 green. Forge core now = PR + pushout merge + review-as-stitcher + CI-gate + review threads.
- dregg-forge CI-gate (community thread) — `dregg-doc/check.rs`: a merge gated on a real committed
  check-turn receipt (Ed25519 executor-signed, verified) or a real ProofCondition witness — no bool;
  gate order conflict→base→check→cap, unsatisfied check refuses byte-untouched. 4 poles green
  (substrate 141 lib). Surfaced a real `turn/conditional.rs` TurnExecuted signing-message bug (HORIZONLOG).
- dregg-forge keystone (community thread) — `dregg-doc/pull_request.rs`: the `PullRequest` +
  review-as-stitcher, welded over the existing Pijul core (three_way/pushout/ConflictRegion/resolve_*)
  with the merge routed through executor_drive's REAL cap gate (`check_cross_cell_permission`). Three
  poles green (default 105+/substrate 137+): clean→pushout landed Final; conflict→refused-until-resolved;
  capless merger→in-band CapabilityNotHeld, rolled back. `docs/deos/DREGG-FORGE.md`.
- homeserver-grain body PICKED (community thread) — live scout → **continuwuity** (matrix.org Stable,
  multi-maintainer, rlib workspace, Element-X-proven sync); tuwunel runner-up. Architecture SIMPLIFIED:
  lib-embed (execve door gone) + `with_fds` pre-bound listener (listen door gone) → ONE new firmament
  door, `grant_read_write` for the RocksDB dir. `docs/deos/GRAIN-HOMESERVER.md`.
- Pillar 1 (a-bar) — `MigrationTarget::Distributed` (migrate.rs + shell.rs): a surface re-homes onto a
  federation cell over a real captp handoff, SurfaceId preserved + attenuated (zero change to the
  generic migrate() body); handoff refuses Amplification/TargetMismatch/Replay; present/route resolve
  as real granted⊆held turns via DistributedBacking. 11 green both poles; cockpit gate green. b-bar =
  the cert over a real netlayer + the swiss-table/backing on a second box.
- Pillar 2 (a-bar) — `mud.rs` `speak_cap_for(world, token)`: the speak cap is derived from the
  on-ledger presence token (revoked unless the room c-list hosts it), the host-side speak table
  fully retired. 14/14 mud green (2 new, both poles: enter→admits, leave→same derivation refuses;
  only the leaver's speech stops). native-full gate green. Honest: a ledger-gated projection across
  two cap systems, not a one-call attenuation.
- Pillar 2b (a-bar) — `mud.rs`: `hosts`/`speak_cap_for`/`who_is_here` refactored to take `&Ledger`;
  the derivation is a pure function of ledger state, proven identical across the `WorldSink` boundary
  (`world.ledger()` vs `WorldSinkAdapter::with_ledger`), both poles. 15/15 mud green; cockpit gate
  green. Composes with Pillar 0 → any box derives the identical cap from its own ledger copy.
- Pillar 0 (a-bar) — `NodeWorldSink` (dregg-sdk-net, `world-sink` feat): remote WorldSink commits via
  `/turns/submit` + reads via `/api/cell/{id}`. Both poles vs a real-executor test node (commit+read;
  overreach refused); 70 lib green; no-feature build mozjs-free. Unblocks 1/2/4.
- Pillar 3 (a-bar) — `card_carry` + `card_carry_bridge`: a `CardForkEnvelope` crosses two cockpit
  sessions over a live Conduit; byte-only in deos-matrix, tooth re-fired in starbridge-v2. 42+5
  deos-matrix / 5 starbridge green; forged carry refused, garbage fail-closed; live full-loop keeps
  both edits both sides. native-full gate green. b-bar (two machines) = same wire, deferred to iron.
