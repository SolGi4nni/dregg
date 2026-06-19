# AOL-wonder — the warm front door over the live image

The deos desktop has two faces, and they are the same image. One face is the
power-instrument: the cockpit's tabbed rooms (SHELL, AGENT, SWARM, GRAPH, ORGANS,
PROOFS, SIMULATE, OBJECTS, DEBUGGER) — a bottomless live workshop for the adept.
The other face is the warm room: a small set of glowing cells a newcomer clicks
around with no manual, where wonder precedes comprehension. This document
describes that warm face from first principles, present tense, and grounds it in
the modules already in the tree.

The test of any deos surface holds here: a five-year-old clicks it with delight,
**and** an adept inspects and modifies it live like a Pharo object. The warm room
is built so both are the same act on the same object.

## What a newcomer meets

A newcomer who opens the image does not read a page. They see a room of cells.
Some glow brightly; some rest dim. The eye is drawn to the brightest cell,
because the brightest cell is where the image is doing something right now. You
hover a cell and a small ring of commands lights up around it. You poke one and
the cell tells you, in a warm plain sentence, what it is. You grab a glowing cell
and drag it onto another, and value flows between them — and before it flows, the
image shows you what would happen. You never needed to know the words "cell",
"capability", "turn", or "receipt" to do any of this. That is the AOL-wonder: you
click, you absorb, the system rewards exploration.

Nothing in this room is decorative or faked. Every glowing object is a live
protocol object; every command is a real capability; every drag is a real
verified turn. The wonder and the rigor are the same surface seen from two
distances.

## The glow is real activity

The room presents each live ledger cell as a **glowing cell** carrying a
*liveliness* in `[0, 1]`. That liveliness is not an animation loop — it is a
projection of the live transition stream.

`src/dynamics.rs` is the image's nervous system: an append-only log of
`WorldEvent`s the world emits as it commits turns (`CellBorn`, `TurnCommitted`,
`BalanceFlowed`, `CapabilityGranted`, `FieldSet`, `SurfaceDamaged`,
`EventEmitted`, the lifecycle transitions). The warm room reads the recent tail of
that stream (`Dynamics::tail`) and asks, per cell, *how recently did the image
touch you?* A cell the most recent committed turn moved value through glows full;
a cell touched at the edge of the recent window barely glows; a cell the window
never touched is dark. The brightest cell is the image's current hotspot — the
place the eye is rightly drawn.

Because the glow is a function of the real `WorldEvent` stream, it cannot lie. A
cell glows because the verified executor really did something to it. When a turn
commits through `World::commit_turn` (`src/world.rs`) and emits its dynamics, the
next build of the room redistributes the glow accordingly. The room is a live
projection, never a static splash — it grows with the image it describes, exactly
as the landing portal (`src/landing.rs`) does.

This is the same recent-activity signal the cockpit's activity feed already reads;
the warm room simply paints it onto the cells themselves, so liveliness is
something you *see in place* rather than read in a list.

## The landing is the prose front door; the room is the pokeable one

`src/landing.rs` is the warm front door in *prose*: `LandingPortal::build(world)`
projects the live world into titled cards of real text — where you are, the image
right now (its real cell count, height, receipts, total value, last heartbeat),
the verified heart, the receipt nervous system, the organs, and the invitation to
begin. It is gpui-free and `cargo test`-able: the cockpit's HOME tab renders
exactly those strings, so a test that asserts the strings are present and non-empty
proves the rendered tree is non-blank.

The warm room is the same idea one step more direct: instead of *telling* you the
image is alive in prose, it *shows* you the live cells glowing and invites you to
touch them. The two compose — the portal's prose welcomes; the room's glowing
cells are the thing the prose points at. Both are pure projections of the same
`World`, so neither can drift from what the executor actually holds.

## Every glowing object is a live Pharo object

The Pharo-liveness half of the fusion lives in `src/reflect.rs`: the uniform
reflective object model. Every dregg datum — a cell, a capability, a receipt, the
image itself, a factory, a nullifier — projects into one `Inspectable`: a typed
tree of `Field`s any view renders the same way. `reflect_cell(id, cell)` is the
cell's live object; the OBJECTS/inspector tab shows exactly this.

In the warm room, the *inspect* command on a glowing cell opens precisely that
`Inspectable` — the same object the inspector tab opens, byte for byte. There is
no second object model for the room. A child clicks a cell and sees its insides; an
adept clicks the same cell and reads the same live, inspectable fields they would
read in the workshop. The clicked glow and the inspected object are one thing seen
at two distances — which is the whole point of a Pharo-style image: the tools for
the system are objects in the system, reachable by clicking the system.

## The halo — the per-object command ring

Hovering a glowing cell lights a small **halo** ring of commands around it. The
ring is deliberately tiny — three commands — so there is nothing to learn:

- **inspect (○)** — open the cell as its live `Inspectable` object. Maps directly
  to `reflect::reflect_cell` (`src/reflect.rs`). This is the liveness leg.
- **grab (✊)** — pick the cell up as the *source* of a value drag, awaiting a
  drop. This arms the direct-manipulation gesture below.
- **explain (?)** — speak one warm sentence about the cell, drawn from its real
  fields (its balance, its cap reach) and its recent liveliness. A `−supply`
  issuer well is named warmly as a backing well, not a scary negative. No
  comprehension is required to read it; reading it *is* the comprehension
  arriving.

Each halo maps to a real action — a reflective projection, an armed gesture, or a
sentence drawn from real data. The room reuses the cockpit's own machinery
(`reflect`, the simulate/commit path); it does not reinvent a parallel one. The
deos affordance model (`src/affordance.rs`) is the same shape generalized: a cell
publishes named, capability-gated affordances, and firing one is a cap-gated
verified turn through the embedded executor. The halo ring is the wonder-first,
fixed-set presentation of that idea — a ring a four-year-old can poke, backed by
the same real actions an adept fires from the affordance surface.

## The drag is a real verified turn, predicted first

The signature gesture is direct manipulation of value: **grab a cell, drop it on
another, and value flows.** This is modeled, end to end, as a real turn — and it
is wonder-safe because it is *predicted before it commits*.

Grabbing a cell (the *grab* halo) arms a drag whose source is that cell. Dropping
it on a target cell completes a drag-value intent: a source, a target, and the
amount the gesture moves. That intent lowers to the *same* `IntentDraft` the
COMPOSER and SIMULATE panels build (`src/simulate.rs`) — a single
`EffectKind::Transfer` from source to target, authored by the source cell. It does
not invent a turn path; it rides the one already proven.

Resolving the drag follows the simulate panel's discipline exactly:

1. **Predict.** `simulate::simulate` forks the live world (`World::fork` —
   a deep copy running the *same* verified executor over a clone of the live
   ledger, with the same factory registry and per-agent receipt-chain heads) and
   runs the transfer one turn ahead. The live world is untouched. The prediction is
   the real executor's verdict, not a model: an over-drag (moving more than the
   source holds) is refused here, with the executor's own reason, before anything
   moves. A child can drag freely and *see* what would happen first.

2. **Commit, only if predicted.** If — and only if — the prediction commits, the
   *identical* turn runs on the live world through `simulate::commit` →
   `World::commit_turn`. Same executor, same pre-state, same pinned timestamp, so
   the committed receipt equals the one the prediction previewed. The drag never
   commits something the prediction refused.

The same conservation and no-amplification guarantees that gate the COMPOSER gate
the drag. A refusal is surfaced honestly, the same way the executor's turn
rejections are everywhere else — the verification axis made visible on the gesture
itself.

## The verified scene underneath the glass

The room paints onto the same display path the compositor governs.
`src/compositor.rs` is the pure scene-authority model — the three teeth (T1
non-overlap, T2 label-binding, T3 focus-exclusivity) that refuse a surface that
overpaints another's region, labels itself as a cell it is not, or steals the
focused cell's input. `src/scene.rs` makes a `present()` a real verified turn: the
whole scene authority is folded into a `CellProgram` admit-table, and a present is
a caveat-gated `SetField` the executor admits or rejects — and a committed present
emits a `SurfaceDamaged` event on the dynamics stream.

The warm room benefits from this without adding to it: its glowing cells are drawn
on a display whose integrity is the executor's, and `SurfaceDamaged` is one of the
events that can light a cell's glow. The wonder surface does not get to fool the
human at the glass any more than a value turn gets to fool a light client — the
same unfoolability discipline applies one hop out, to the display.

## Why the two faces are one

The warm room is not a simplified *copy* of the image for beginners. It is the
*same* live `World`, the *same* dynamics stream, the *same* reflective objects, and
the *same* predict-then-commit turn path — presented so that the first thing a
newcomer does (poke a glowing cell, drag value between two cells) is already a real
inspection and a real verified turn. A child clicking with delight and an adept
inspecting live are doing the same thing to the same object. That is the fusion:
AOL-wonder and Pharo-liveness are not two surfaces to maintain, but two distances
from one live, self-describing, malleable image.
