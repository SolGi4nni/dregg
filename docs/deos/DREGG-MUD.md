# DREGG-MUD — a decentralized, distributed multi-user world on the verified cell graph

## The one-sentence thesis

> A MUD/metaverse on dregg is not a game server with a database — it is a **view
> over the one cap-secure, conserved, provenance-carrying, forkable cell graph**:
> a room IS a cell, an inhabitant IS a cap-rooted session, an item IS a capability,
> an exit IS a cap edge, an action IS a verified turn, the shared world IS a
> rehydratable membrane, and the social layer IS Matrix — so you *cannot* dupe an
> item, enter a room you lack the key to, or claim an action you did not take,
> because those are exactly the linearity and authority properties the substrate
> already proves.

This is the same move `docs/deos/APPS-AS-CELLS.md` makes for the editor / terminal
/ chat room: every MUD primitive already exists in the tree, disconnected. This doc
is a **census-then-weld** map (the WELD METHOD), not a from-scratch design. Every
MUD verb below points at a real `file:line`. The companion type sketch is
`starbridge-v2/src/mud.rs` — a `cargo test`-able first slice (no GPU, no Matrix
server) that proves the load-bearing scenario: *two players in one room, one picks
up an item, the other cannot dupe it.*

---

## 0. The dictionary — every MUD noun/verb is a dregg primitive

| MUD concept | dregg primitive | machinery (file:line) |
|---|---|---|
| **room** | a `Cell` (its contents/exits = state + c-list; its history = receipt chain) | `cell/src/cell.rs`, room-as-cell `deos-matrix/src/cell.rs:70` (`RoomCell`) |
| **inhabitant / player** | a cap-rooted **session** = the c-list reachable from the identity cell | `starbridge-v2/src/session.rs:13` (login = root cap), `Session` `:147` |
| **identity** | `CellId::derive_raw(pubkey, ROOT_TOKEN)` — the content-address of the key | `types/src/lib.rs:683`, `session.rs:53` (`ROOT_TOKEN`), `:72` (`root_cell`) |
| **item / object** | a **capability** to a cell (holding the cap = holding the thing) | `cell/src/capability.rs:44` (`CapabilityRef`), `:126` (`CapabilitySet`) |
| **exit / door** | a cap *edge* to the neighbour room cell; a *locked* door = a cap you lack | `cell/src/capability.rs` (`has_access_at`, height-aware since 2026-08-06), `permissions.rs:5` (`AuthRequired`) |
| **affordance (lever, button, "look")** | a cell-declared, cap-gated effect-template; firing = a verified turn | `starbridge-v2/src/affordance.rs:62` (`CellAffordance`), `:99` (`authorized_for`) |
| **pick up / drop / give** | `Effect::GrantCapability` / `RevokeCapability` (a real attenuated grant) | `turn/src/action.rs` (`GrantCapability`/`RevokeCapability`), powerbox `starbridge-v2/src/powerbox.rs` |
| **trade / pay** | `Effect::Transfer` / `NoteSpend`+`NoteCreate` under Σδ=0 | `turn/src/action.rs` (`Transfer`/`NoteSpend`/`NoteCreate`), conservation in the executor |
| **act (any verb)** | a `Turn` the executor admits iff `required ⊆ held`, leaving a `TurnReceipt` | `turn/src/turn.rs` (`Turn`/`TurnReceipt`), `starbridge-v2/src/world/` (`commit_turn`) |
| **say / emote / shout** | a pub/sub to the room's inbox on the data plane (a no-value turn, Σδ=0 trivially) | `captp/src/data_plane.rs:366` (`Bus`: `publish`/`subscribe`/`enqueue`/`drain`) |
| **the shared world** | a forkable, rehydratable, stitchable cap-bounded membrane | `starbridge-v2/src/shared_fork.rs`, `deos-matrix/src/membrane.rs`, `World::fork` `world.rs:632` |
| **presence / "who is here"** | Matrix membership + typing/presence over the room cell | `deos-matrix/` (room↔cell `cell.rs`, presence `client.rs`) |
| **NPC / mob / bot** | an **agent session** — a principal with a deliberately narrower cap-tree (mandate) | `session.rs:120` (agent template), `docs/SUPERSEDED/HERMES-INTEGRATION.md` |
| **the client** | a deos surface (a room-view) — Third-Room-shaped gpui + Matrix | `starbridge-v2/src/{cockpit,room,scene,world}.rs` |
| **"can't cheat"** | conservation (Σδ=0) + nullifier non-membership + **Settlement Soundness** | `metatheory/Metatheory/SettlementSoundness.lean:153` (`settlement_soundness`) |

The rest of this doc unfolds each row.

---

## 1. The object model

### 1.1 Room = a cell

A room's *durable core* is a `Cell` (`cell/src/cell.rs`): its `CellState`
(`cell/src/state.rs:101`) holds the room's name/description in user fields, its
exits and contained items in the c-list (`CapabilitySet`), and "who may enter /
who may post / who may build" in the permission lattice. Crucially:

- The room's **contents** are the caps it holds (exits to neighbour rooms; caps to
  the item-cells lying on the floor).
- The room's **history is its provenance chain** — every turn committed against the
  room cell leaves a `TurnReceipt` (`turn/src/turn.rs`), foldable by
  `History::replay_to` / `fork_at`. "What happened in this room and who did it" is
  not a log you trust the server to keep; it is the receipt chain a light client
  verifies. This is exactly `deos-matrix/src/cell.rs:70` (`RoomCell`): "the message
  history is the cell's turn history."

Ephemeral view-state (the rendered scene, particle effects, your camera) stays in
app memory; only the *durable* room is a cell — the same split APPS-AS-CELLS draws.

### 1.2 Inhabitant = a cap-rooted session

A player is a **logged-in principal** whose *reach is exactly their cap-tree*
(`starbridge-v2/src/session.rs`): login derives the identity cell
`CellId::derive_raw(pubkey, ROOT_TOKEN)` (`session.rs:72`), grants the per-user
initial cap set (`CapTemplate`, `session.rs:120`) into it, and the **session IS the
resulting c-list** (`Session`, `session.rs:147`). There is no "player object kept
in sync with the world"; there is a c-list, and the world renders exactly what it
authorizes (`Session::reaches`, `session.rs:170`). Logout =
`Effect::RevokeCapability` over the session root → the whole tree goes dark,
synchronous and transitive at `n=1` (`session.rs:35`).

What this buys the MUD:

- **Your inventory IS your c-list.** The items you carry are caps under your
  identity cell. Nothing else.
- **Your reach IS your authority.** You can interact with exactly the rooms and
  objects you hold a cap to — no ambient "you're an admin" flag.
- **Multi-user legitimacy is the polis floor.** When many principals share a world,
  legitimacy is non-regression of exported floors, not a referee's discretion —
  `metatheory/Metatheory/{Polis,DreggPolis}.lean`. A move is legitimate iff it does
  not regress another inhabitant's guaranteed floor.

### 1.3 Item = a capability; exit = a cap edge; lock = an absent cap

There is no separate "item table." An **item** is a `CapabilityRef`
(`cell/src/capability.rs:44`) into an item-cell; *holding* the item is *holding the
cap*. An **exit** is a cap edge from one room cell to the neighbour
(`holds_unfrozen_ref_to(&neighbour)` is "this room connects there"). A **locked door** is the
absence of a cap, or a cap whose `AuthRequired` you cannot satisfy
(`permissions.rs:5`): the key is the cap, and `is_attenuation(held, required)`
(`capability.rs:603`) is the lock mechanism. You don't *check* a lock; you simply
can't form a reaching turn without the key — the executor refuses it.

### 1.4 Action = an affordance = a cap-gated verified turn

Levers, buttons, "examine," "open," "read the sign" are **affordances**
(`starbridge-v2/src/affordance.rs:62`): a cell declares named, typed effect
templates, each with the `AuthRequired` a viewer must hold. `project_for` shows you
only the affordances your held cap authorizes (progressive *attenuation*), and
`fire` (`affordance.rs`) hands the real `Effect` to `World::commit_turn`
(`world.rs:989`) — the embedded verified executor. A disallowed pull is
`FireOutcome::Refused` (the anti-ghost tooth). So "press the button" is not a
message to a server that decides; it is a turn the executor admits or rejects in
front of you, leaving a receipt.

---

## 2. Why you cannot cheat (the soundness story)

The three classic MUD exploits — **dupe an item, walk through a locked door, claim
an action you didn't take** — are each foreclosed by a property the substrate
already proves. This is the whole reason to build a MUD on dregg.

### 2.1 You cannot dupe an item — conservation + linearity

Picking up / giving an item is a `GrantCapability`/`RevokeCapability` pair, and a
*valuable* item rides `Transfer` or a `NoteSpend`+`NoteCreate` note pair, all under
**Σδ=0** (the signed-`i64` balance well, `cell/src/state.rs:111`; conservation
enforced in the executor). A note spend consumes a **nullifier**; the circuit
already enforces nullifier *non-membership* (no double-spend). So:

- Hand the same gold to two people → the second turn's nullifier collides → the
  executor rejects it. The membrane stitch surfaces this as
  `ConflictReason::NullifierCollision` / `ConservationCollision`
  (`deos-matrix/src/membrane.rs:184`), a first-class **conflict object**, never a
  silent dupe.
- The first-slice test `mud.rs` exercises exactly this: player A grants the sword
  cap to B; A's cap is revoked in the same turn; a *replay* of the pickup (the dupe
  attempt) is refused because the source no longer holds it. **Duping is not
  "detected and rolled back"; it is structurally inexpressible.**

### 2.2 You cannot enter a room you lack the key to — the attenuation lattice

Entering a room is forming a turn that reaches its cell. Without a cap to the room
(or with one whose `AuthRequired` you can't satisfy), there is no admissible turn:
`is_attenuation(held, required)` (`capability.rs:603`) is false, and the executor
refuses. A locked door is not a flag the client honors; it is an authority the
executor checks. A *key* is a `GrantCapability` someone with the cap chose to hand
you — attenuated, never amplified (`is_attenuation` is the only way authority
moves).

### 2.3 You cannot claim an action you didn't take — receipts + Settlement Soundness

Every action is a `Turn` leaving a `TurnReceipt` (`turn/src/turn.rs`) chained on
your per-agent receipt chain (`world.rs:989` threads `previous_receipt_hash`). You
cannot fabricate "I slew the dragon" without a receipt the executor signed. And in
the *distributed/forked* world, the keystone is **Settlement Soundness**
(`metatheory/Metatheory/SettlementSoundness.lean:153`):

```
theorem settlement_soundness (hbind : BindsLiveAuthority S) … (hsettled : S … ac) :
    LiveAtTip T log held tip ac
```

A turn that **settles** into the shared world necessarily exercised authority that
was **live at the settlement tip** — held-as-an-attenuation (`reaches`,
`:162`) AND not-yet-revoked (`honors`, `:168`). The contrapositive
(`revoke_before_tip_unsettleable`, `:192`) is the operational face: *a cap I have
since revoked cannot ride a stitch into the shared world.* At `n=1` (the
single-machine dregg world) revocation is immediate (`revoke_unsettleable_immediate`,
`:212`) — darken your house and a guest's in-flight action against it simply cannot
settle.

So a player who forks the world, does anything in their private fork, and tries to
stitch it back **cannot conjure objects** (Σδ=0 blocks it), **cannot amplify
authority** (`ConflictReason::CapAmplification`), and **cannot exercise revoked
authority** (`AuthorityRevoked` / Settlement Soundness). The clean, monotone part
of their play merges; the cheating part is *lossy-dropped as a visible conflict
object* (`StitchOutcome`, `membrane.rs:160`), not silently accepted.

---

## 3. The spatial / navigation model — a cap-addressed room graph across distance

The world is a **graph of room cells joined by cap edges**. Navigation is
cap-following: from your current room cell, the exits are the room caps it holds;
moving is a cap-gated transition to the neighbour. Two consequences:

- **Addressing is content-addressed, not server-addressed.** A room is its `CellId`
  (a 32-byte content address) plus a `dregg://` sturdyref
  (`membrane.rs:73`) — a bearer reference you can pass to a friend ("here's the
  tavern"). No DNS, no shard id.
- **The firmament collapse: one cap across distance.** A room cap is the *same kind
  of object* whether the room is in your local image, on a peer's machine, or
  federated across the network — this is the firmament "one cap across distance"
  principle (`docs/deos/CROSS-DEVICE-FIRMAMENT.md`,
  `project-firmament-sel4-boots`). A `NetworkBoundary` (`shared_fork.rs:108`) marks
  a room whose exits "elaborate elsewhere": stepping through opens a consent
  request (`ConsentRequest`, `shared_fork.rs:161`) to the remote owner, resolved by
  a real grant whose signed receipt is the consent witness — fail-closed if consent
  never arrives. **Federated rooms need no central directory; they need a cap and a
  consent ceremony.**

So the world map is the reachable subgraph of room cells from where you stand — a
*frustum* (`FrustumCut`, `membrane.rs:107`): only what is in view within bounded
depth/authority is loaded. The rest is culled, which is also the confinement
boundary — you cannot load (or exploit) a room beyond your cap horizon.

---

## 4. Presence + comms — Matrix as the social transport, the data plane as movement

Two distinct planes, deliberately:

- **Social / presence = Matrix** (`deos-matrix/`). A Matrix room IS a MUD room: the
  room↔cell mapping (`deos-matrix/src/cell.rs:70`) ties `!room:server` to a
  `CellId`; a *send* is conceptually a *turn* against the room cell
  (`SendReceipt`, `cell.rs:177`). Presence/typing = "who is here and who is
  acting." Identity verification is "verify the person, not the device" — the
  identity cell root under which every device cap hangs (`cell.rs:106`). Non-deos
  Matrix clients see a graceful text fallback (`MembraneEnvelope::text_fallback`,
  `membrane.rs:267`); deos clients see the live semantic object.
- **Movement / exchange / "say" = the data plane** (`captp/src/data_plane.rs:366`,
  `docs/deos/DREGG-DATA-PLANE.md`). The `Bus` gives `publish`/`subscribe` (room
  chat as pub/sub to the room's inbox), `enqueue`/`drain` (cap-gated point-to-point:
  whispering, handing an item), and *wake derived from cursor advance* (not
  asserted) — so "someone said something / something happened here" is a real
  receipt-bearing delivery, cap-gated before enqueue.

The split matters: **Matrix carries the human conversation and rich-object
attachments; the data plane carries the verified semantic events.** A chat message
can *embed* a dregg semantic object — a membrane of the room you're in (the MX
lane's `DreggObject`-over-Matrix). You drop "come see my house" in chat as a
`MembraneEnvelope` (`membrane.rs:59`); a friend rehydrates it
(`MembraneHost::rehydrate`, `membrane.rs:223`) into a live, drivable fork and walks
in.

---

## 5. NPCs / agents as cap-bounded inhabitants

An NPC is not special-cased. It is an **agent session** that differs from a player
session **only in its cap template** (`session.rs:120`): "an agent is born holding
a deliberately narrower cap-tree — its mandate. The ceremony is identical." A
shopkeeper NPC holds caps to its shop cell and a transfer cap; a quest-giver holds
a cap to mint a quest-reward note; a wandering mob holds movement caps over its
patrol subgraph and nothing else.

A *Hermes* agent (`docs/SUPERSEDED/HERMES-INTEGRATION.md`) — an LLM-driven inhabitant —
runs the **controller-blind** loop: its tool-calls are dregg turns authorized by a
cap-gated token; a tool it lacks the cap for returns an in-band refusal
(`TokenInsufficientCapability`); each tool-result carries a `TurnReceipt` proving
execution. So a chatty AI NPC is *structurally* unable to act outside its mandate —
the same gate that bounds a human player bounds the agent. A subagent (a summoned
familiar) is `spawn_sub_agent_scoped(restrictions, …)` — a further attenuation.

The payoff dregg adds over any scripted-NPC system: **you can hand an NPC to an
untrusted operator and it still cannot exceed its caps** — the agent's author and
its runtime can be different parties (the controller-blind payoff).

---

## 6. Third Room — what they do, what dregg adds

[Third Room](https://thirdroom.io) is an open, decentralized 3D virtual-world
client: WebSG scenes, networked via Matrix (state over a Matrix room), an
ECS/WASM scripting runtime, peer-to-peer voice. It is the closest existing shape to
this vision — *and it is the right shape*. What it does well: Matrix as transport,
the world as a shareable room, an open scripting surface, no app-store gatekeeper.

What it does **not** have, and what dregg adds:

| concern | Third Room | dregg-MUD |
|---|---|---|
| **shared state authority** | Matrix room state + client trust; a peer can assert state | a settled turn provably exercised **live authority** (Settlement Soundness, `:153`) |
| **object ownership** | a scene node / convention | a **capability** — ownership IS holding the cap; transfer is attenuated, never amplified |
| **item economy** | none / scripted | **conserved value** (Σδ=0) + nullifiers — items cannot be duped, structurally |
| **"can't cheat"** | client/server trust, anti-cheat heuristics | **proof** — accept ⟹ genuine transition; cheating is inexpressible, not policed |
| **federation** | Matrix federation of room state | **firmament caps** — one cap across distance + consent boundaries; no central directory |
| **time-travel / merge** | live state only | **branch-and-stitch** — fork, play privately, stitch back with conflicts-as-objects |
| **NPCs/agents** | scripts in the client runtime | cap-bounded agent sessions; controller-blind; a rogue NPC cannot exceed its mandate |

The honest framing: Third Room solves *transport and presentation*; dregg solves
*authority, ownership, and sound shared state*. The two compose — a Third-Room-style
gpui+Matrix client over a dregg cell graph is precisely the deos room-view surface.

---

## 7. The phased path

**Phase 1 — a text MUD over Matrix + cells (now).** Rooms are cells; players are
sessions; movement is cap-following; "say" is data-plane pub/sub; items are caps;
the client is a text surface in the cockpit. Everything in §§1–2 is buildable on
today's machinery (the first-slice `mud.rs` proves the core). Matrix carries the
chat; the cell graph carries the truth. *Deliverable: walk between rooms, pick up /
give / drop items provably, chat, with verifiable "who did what."*

**Phase 2 — objects-as-affordances + the shared membrane.** Rooms expose
affordances (levers, signs, buildable structures); the shared world is a drivable
membrane (fork → play → stitch); a chat message can embed a room membrane a friend
rehydrates and walks into. Trading runs on conserved notes. NPCs arrive as agent
sessions; Hermes NPCs become controller-blind. *Deliverable: a living, mutable,
federated text/2D world with a sound economy.*

**Phase 3 — spatial / 3D (later).** A Third-Room-style gpui+WebSG room-view surface
renders the cell-backed scene; presence is spatial; the room graph becomes a
navigable 3D map. The substrate is unchanged — the scene is *ephemeral view-state
over the same cells* (the APPS-AS-CELLS discipline), so the soundness story from
Phase 1 carries forward unbroken. *Deliverable: a metaverse whose every object is
owned, every action is proven, and whose world has no central server.*

---

## 8. The first-slice sketch

`starbridge-v2/src/mud.rs` is the typed, `cargo test`-able first slice over the
real `cell`/`turn`/`world` types. It defines `Room`, `Inhabitant`, and `Item` as
thin wrappers over `CellId` + `World`, and proves the load-bearing scenario:

> **Two players in one room; one picks up an item; the other cannot dupe it.**

The pickup is a real `GrantCapability` (the item cap moves to the picker) paired
with the source losing it; the dupe attempt is a *second* pickup of the same item,
which fails because the source no longer holds the cap to grant — conservation of
the capability itself, enforced by the executor, not by the MUD code. The test also
shows that an inhabitant without the room cap cannot form an entering turn (the
locked-door property) and that every action leaves a verifiable receipt (the
no-false-claim property). The sketch is deliberately periphery (not in the churning
`circuit/`, `turn/`, `cockpit/` crates) — it *welds*, it does not rebuild.
