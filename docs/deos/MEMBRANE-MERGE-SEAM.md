# The membrane + merge seam — chat messages that carry rehydratable forks of the deos world

This is the deep deos part of **deos-chat** (the native gpui Matrix client in `deos-matrix/`). It
states, in present tense and against the real in-tree machinery, how a chat message can carry a
**rehydratable membrane** — a frustum-culled, cap-bounded snapshot of the deos world-fork at the
moment of capture — how a recipient **rehydrates** it (opens the fork and drives real turns), and how
a **stitch** merges divergent forks back into mainline. Matrix is the transport that makes these
interactions real and multiplayer.

The companion code is `deos-matrix/src/membrane.rs` (the wire shape + the `MembraneHost` trait) and
`deos-matrix/src/chat.rs` (the composer's `⬡ attach membrane` affordance). This document is the
prose; the module is the typed contract.

## The one-breath shape

A message embeds a **membrane envelope**: an anti-substitution *root*, a `dregg://` *sturdyref* into
the captured fork, the publisher's attenuated *lineage* capability, the *snapshot* of the
frustum-culled cell subgraph, and the *cut* + *cursor* that produced it. The bytes are inert in
transit. A recipient's confined comms-PD **rehydrates** the envelope into a live `World` fork it can
drive turns on — confined by nesting, so its effects stay imaginary — and later **stitches** the
useful divergence back through the one gated settlement door, lossily exactly where dregg's linearity
(Σδ=0 conservation · nullifier non-membership · cap non-amplification) forbids gluing.

## What grounds it (real now)

Every mechanism below already exists in-tree. The seam is *composition*, not invention.

| Seam piece | Grounded in | Type / function |
|---|---|---|
| The fork | `starbridge-v2/src/world.rs` | `World::fork(&self) -> World` — deep-clone ledger, SAME verified executor; a fork turn yields a byte-identical receipt |
| The snapshot | `persist/src/snapshot.rs` | `Snapshot { checkpoint ⊕ overlay, claimed_root: [u8;32] }`; `ship_snapshot(from_height)`, `apply_snapshot_verified(snap, trusted_root)` (fail-closed on root mismatch) |
| The root (anti-substitution tooth) | `world.rs` / `cell/src/ledger.rs` | `World::state_root() -> [u8;32]`, `Ledger::root()` (sorted-Poseidon2/BLAKE3 over canonical cells) |
| The frustum (cap-bounded subgraph) | `cell/src/{cell,ledger}.rs` | `Ledger::iter()` closure over each `Cell::capabilities` (the c-list), depth- + authority-bounded |
| The surface-cap + projection | `starbridge-web-surface/src/rehydrate.rs` | `SurfaceCapability`, `Membrane::project(lineage)` / `reshare(req)` (the anti-amplification meet through the REAL `is_attenuation` lattice) |
| Rehydration (per-viewer) | `starbridge-web-surface/src/rehydrate.rs` | `Sturdyref { uri, lineage, witness_log, sources_reachable }`; `rehydrate(sturdyref, membrane, web) -> Projection`; `Rehydration::{ReplayedDeterministic, ReconstructedApproximate, Live}` (liveness DERIVED, never asserted) |
| The consistent cut | `starbridge-v2/src/replay.rs` | `History::fork_at(k, alt) -> Fork`, `replay_to(k)` (verifies reconstructed root vs recorded tooth, fail-closed); `WitnessCursor` |
| The open holes a fork rides | `turn/src/{pending,eventual,conditional}.rs` | `PendingTurnRegistry::{submit_pending_at, register_dependent, resolve}`, `EventualRef`, `ConditionalTurn`, `ProofCondition` — a hole IS a nullifier; filling it (`resolve`) is a one-shot spend |
| The confinement (nesting IS safety) | `dregg-firmament` + branch-and-stitch | a branch turn can only touch cells the branch holds caps to; no main-cap → no leak |

## The wire shape

`deos-matrix/src/membrane.rs` defines `MembraneEnvelope`, the serializable value that travels in the
`software.ember.deos.membrane` field of an ordinary `m.room.message` (so non-deos clients see a
graceful text fallback — `[deos membrane · N cells · root abcd… · cut@hH]` — and deos clients see the
membrane). Its fields:

- `frustum_root: [u8;32]` — the canonical `Ledger` root of the snapshot (`Snapshot.claimed_root`).
  The recipient verifies the rehydrated ledger reproduces this root before trusting a single cell.
- `sturdyref: String` — a `dregg://` bearer cap into the fork (the publisher's, not the cells').
- `lineage: Vec<u8>` — the publisher's authority, attenuated to exactly what a recipient may exercise
  (the canonical bytes of a `SurfaceCapability`). The recipient's `Membrane::project` MEETS this with
  the recipient's own held cap; the meet can only attenuate (anti-ghost tooth).
- `snapshot: Vec<u8>` — the frustum: a `persist::Snapshot` of only the culled cells.
- `cut: FrustumCut { focus_cell, max_depth, authority_bounded, cell_count }` — the cull that produced
  the frustum, recorded so the recipient audits the cell set against the declared horizon (no smuggled
  cells beyond the cap horizon).
- `cursor: WitnessCursor { height, commit_index }` — the consistent cut the fork branched at.

### What "frustum-culled" means in code

The rendering metaphor is exact. The "camera" is `focus_cell`; the "far plane" is `max_depth`; the
"frustum" is the set of cells *in view* = reachable from the focus along capability edges within the
depth bound (and, if `authority_bounded`, only along attenuated caps). The traversal is a closure over
`Ledger::iter()` following each `Cell::capabilities` target. **Everything outside the cull is absent by
construction** — you cannot rehydrate what is not in the snapshot. The frustum cull and the
confinement boundary are the same boundary: confinement by omission.

## The flow

```
publisher (deos side, comms-PD)                recipient (deos side, comms-PD)
──────────────────────────────                 ───────────────────────────────
World (live)                                    World (their own live mainline)
  │ MembraneHost::mint(focus, cut)
  ├─ World::fork()                              chat message arrives (Matrix sync)
  ├─ walk Ledger::iter() / Cell::capabilities      │  MembraneHost::rehydrate(env)
  │   to the cut horizon  ────────────► frustum    ├─ apply_snapshot_verified(snap, env.frustum_root)  (fail-closed)
  ├─ persist::ship_snapshot(selected cells)        ├─ rehydrate(sturdyref, their Membrane, web)
  └─ wrap Sturdyref(dregg://, attenuated lineage)  ├─ Membrane::project(lineage)  (meet — anti-amplify)
                │                                   └─ World::fork()  → ForkHandle + DERIVED Liveness
        MembraneEnvelope ──── Matrix m.room.message ────►
                                                       │  MembraneHost::drive(fork, turn)
                                                       └─ World::commit_turn on the fork
                                                          (real verified executor, byte-identical
                                                           receipt; NO main-cap → confined)
                                                       │  MembraneHost::stitch(fork)
                                                       └─ pushout vs mainline tip past cursor;
                                                          clean part merges; conflicts lossy-dropped;
                                                          merged turn → mainline settlement gate
```

The `MembraneHost` trait (in `membrane.rs`) is the typed contract the comms-PD implements:
`mint(focus, cut) -> MembraneEnvelope`, `rehydrate(env) -> (ForkHandle, Liveness)`,
`drive(fork, turn_bytes) -> TurnReceiptDigest`, `stitch(fork) -> StitchOutcome`. The chat UI only ever
holds the inert `MembraneEnvelope` and (when a comms-PD is present) a `dyn MembraneHost`.

## The MERGE = branch-and-stitch (built: mechanism landed, proof closed)

The stitch is the one door from a divergent fork back to mainline. It is, precisely, a **pushout in
the event-structure configuration lattice** (`docs/deos/{BRANCH-AND-STITCH-PROTOCOL,DISTRIBUTED-
TIMETRAVEL-SEMANTICS}.md`):

- **Branches are configurations** (Winskel event structures): downward-closed, conflict-free sets of
  events. dregg's blocklace *is* an event structure — blocks are events, causality is `causal_past`
  (transitive predecessor closure), conflict is equivocation + a conservation/nullifier collision.
- **A fork is a divergent configuration off a consistent cut** (`WitnessCursor`); `History::fork_at`
  and `World::fork` leave mainline roots untouched.
- **The clean (I-confluent / rhizomatic) part merges monotonically** — it cannot conflict, so it just
  glues (sheaf-theoretic agreement-on-overlaps).
- **The conflicting part is LOSSY-DROPPED, transparently** — and this is the load-bearing deos move:
  dregg's **linearity forces the drop to be explicit**. Two fork events that would
  - spend the same value → **conservation (Σδ=0) collision**,
  - consume the same nullifier → **double-spend non-membership violation** (the circuit already
    enforces this on mainline),
  - exercise authority the mainline tip has since revoked → **authority-not-live-at-settlement**,
  - amplify the same cap → **cap non-amplification violation**,

  cannot be glued. Linear logic (fare Ch5) means you must *explicitly* drop what you don't keep, so you
  cannot lose information by mistake — the drop is **deliberate, typed loss**, surfaced as a
  first-class `ConflictObject { event, reason: ConflictReason }` (patch theory: conflicts are objects,
  not errors). The author SEES exactly what could not reconcile and can re-author or re-fork from it.
- **The merged turn passes through the mainline settlement gate** (Σδ=0 · current-authority vs the
  finalized-tip revocation set · nullifier non-membership), fail-closed. This is the **Settlement
  Soundness** property — *authority-live-at-settlement* — which extends light-client unfoolability to
  the stitched turn. This is now a **proven, `#assert_axioms`-clean theorem**: `settlement_soundness`
  (`metatheory/Metatheory/SettlementSoundness.lean`) plus its circuit-side module
  (`metatheory/Dregg2/Circuit/SettlementSoundness.lean`) — a stitched turn the light client accepts
  implies a genuine kernel transition. No longer the open frontier it was written as.

**Cross-party stitch = a partial turn with holes the consenting parties fill** (the partial-turn /
promises thread): each hole is a `PendingTurnRegistry` entry; filling it (`resolve`) is a one-shot
spend = the consent point. A hole IS a nullifier; resolution IS a spend; one-shot linearity IS the
double-spend non-membership the circuit already enforces. So promise-pipelined cross-party merges
inherit light-client-unfoolability for free.

## Buildable now vs. built-since

**Buildable now** (compose the listed machinery; no new crypto):
- mint: `World::fork` + the `Ledger::iter()`/`Cell::capabilities` cull + `ship_snapshot` + `Sturdyref`.
- rehydrate: `apply_snapshot_verified` (fail-closed) + `rehydrate` + `Membrane::project` + `World::fork`.
- drive: `World::commit_turn` on the fork (already the real verified executor).
- the wire envelope + the Matrix transport (`MembraneEnvelope`; the namespaced field carried on an
  `m.room.message`).
- the chat affordance: `⬡ attach membrane` is present (`deos-matrix/src/chat.rs`); it calls
  `source.mint_membrane` and reports "membrane minted + sent" — the mint→send path is now wired,
  not merely anticipated.

**Built since** (the roadmap items below have LANDED):
- the stitch pushout + conflict-object surfacing: `ForkMembraneHost::stitch_pair`
  (`starbridge-v2/src/shared_fork.rs`) is the executor-backed impl of `mint`/`rehydrate`/`drive`/`stitch`,
  and `starbridge-v2/src/branch_stitch_session.rs` is the stitch guts wired to the settlement-sound gate
  (the clean-merge auto-part is mechanical; the conflict drop is the typed-loss UX).
- **Settlement Soundness** is a closed, `#assert_axioms`-clean theorem (authority-live-at-settlement
  ⟹ light-client accepts ⟹ genuine kernel transition) — `metatheory/Metatheory/SettlementSoundness.lean`,
  landed in the circuit-soundness apex campaign.
- the confined comms-PD that hosts `MembraneHost`: `ForkMembraneHost` is the real executor-backed host
  (the executor + firmament caps + web-of-cells live there; the chat client stays a pure gpui front-end
  over the `ChatSource` + `MembraneHost` seams).

## Why this is the right seam

A screenshot in a normal chat client is a dead pixel grid. A **membrane** is a *live, cap-bounded,
verifiable* slice of the deos world the recipient can actually drive — and the dregg substrate is
exactly what makes that safe: the snapshot root is fail-closed, the projection cannot amplify, the
liveness type cannot lie, the fork is confined by nesting, and the merge is lossy *precisely* where
conservation and the cap algebra require. Matrix supplies the multiplayer transport; dregg supplies
the soundness. The chat message becomes the unit of shared, forkable, stitchable world-state.
