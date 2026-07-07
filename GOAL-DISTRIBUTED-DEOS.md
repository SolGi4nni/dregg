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

**Current thrust:** Pillars 0, 2, 3, 4a LANDED + the `test-support` TestNode export (4a round-trip
THROUGH node execution closed) + dregg-sdk-net doctest debt cleared (crate fully green). Building:
Pillar 1 (`Distributed` surface migration, starbridge-v2). Pillar 2b is BLOCKED on Pillar 1 (same
crate).

**Next 3 moves:**
1. Land + commit Pillar 1 (the last surface-mechanism a-bar).
2. Pillar 2b — wire `mud.rs` `speak_cap_for`'s read onto `NodeWorldSink::with_ledger` (+ hearing
   subscriber set from on-ledger presence per box), proven over the new `test_support::TestNode`:
   3 inhabitants, 3 sinks, 1 node, presence provable from each view.
3. The iron pass (b-bars on hbox-persvati-nextop) → the three-box co-inhabited-room CAPSTONE. All
   a-bar mechanisms green; the iron pass is validation on real boxes, tag after it runs.

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
- Pillar 1 (a-bar) — `MigrationTarget::Distributed` (migrate.rs + shell.rs): a surface re-homes onto a
  federation cell over a real captp handoff, SurfaceId preserved + attenuated (zero change to the
  generic migrate() body); handoff refuses Amplification/TargetMismatch/Replay; present/route resolve
  as real granted⊆held turns via DistributedBacking. 11 green both poles; cockpit gate green. b-bar =
  the cert over a real netlayer + the swiss-table/backing on a second box.
- Pillar 2 (a-bar) — `mud.rs` `speak_cap_for(world, token)`: the speak cap is derived from the
  on-ledger presence token (revoked unless the room c-list hosts it), the host-side speak table
  fully retired. 14/14 mud green (2 new, both poles: enter→admits, leave→same derivation refuses;
  only the leaver's speech stops). native-full gate green. Honest: a ledger-gated projection across
  two cap systems, not a one-call attenuation. b-bar (2b) = point the read at `NodeWorldSink`.
- Pillar 0 (a-bar) — `NodeWorldSink` (dregg-sdk-net, `world-sink` feat): remote WorldSink commits via
  `/turns/submit` + reads via `/api/cell/{id}`. Both poles vs a real-executor test node (commit+read;
  overreach refused); 70 lib green; no-feature build mozjs-free. Unblocks 1/2/4.
- Pillar 3 (a-bar) — `card_carry` + `card_carry_bridge`: a `CardForkEnvelope` crosses two cockpit
  sessions over a live Conduit; byte-only in deos-matrix, tooth re-fired in starbridge-v2. 42+5
  deos-matrix / 5 starbridge green; forged carry refused, garbage fail-closed; live full-loop keeps
  both edits both sides. native-full gate green. b-bar (two machines) = same wire, deferred to iron.
