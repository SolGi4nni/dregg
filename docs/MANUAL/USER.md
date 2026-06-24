# Using deos — the user manual

← back to [the manual index](README.md)

## What deos is

deos is an **inhabited, verified, sovereign world** you live inside. Everything
you see is a **cell**: a small sovereign object whose state is a cryptographic
commitment and whose behavior you can read. Every action you take — pressing a
button, editing a field, sharing a view — is a **cap-gated verified turn**: it
runs only if you hold a capability that authorizes it, and it leaves a
**receipt** you can inspect and rewind. A window *is* a capability; an
interaction *is* a verified turn. And the world is **renderer-independent** — the
*same* world can be painted by the native cockpit, in a browser tab, or on seL4,
because the world is defined in dregg (cells, caps, turns, documents), not in any
one renderer.

The world has no wall between *using* and *making*: a five-year-old clicks a card
in delight and something happens; an adept halts that same card, inspects its
capability tree, rewinds its receipts, and reshapes it live. Same object, same
image.

## Getting in

**Login = receiving your root capability.** You authenticate a key; deos derives
your root cell and hands you a per-user **capability template**. Your *session*
is the resulting list of capabilities (the "c-list") — there is no ambient
authority floating around, only what you hold. Logging out is a real revocation
turn (`RevokeCapability`), synchronous and transitive on one machine.

Logging back in **reopens the exact durable image you left** — your world is
orthogonally persistent, so you do not rebuild it each time. **If your session
won't open, login recovers to the last-good state** rather than dropping you into
a broken one.

(An AI agent logging in is the *identical* ceremony with a narrower template —
see the agent material in the developer manual. Detail:
[`SESSION-LOGIN.md`](../deos/SESSION-LOGIN.md).)

### The cockpit and the five modes

The native cockpit (`starbridge-v2`) is one stable chrome you learn once: a calm
**top bar** (who you are + your cap-badge, the world clock = ledger height and
the latest receipt, the palette summon), a **left rail** of five modes, a **main
pane**, and a collapsible **dock** at the bottom.

The left rail groups everything into **five modes** — one click switches what the
whole pane is *for*:

1. **Inhabit** — *your living world.* The home garden: your cells as clickable
   cards (balances, documents, rooms, agents), each openable, each *doing*
   something. This is the landing.
2. **Author** — *make things.* The card editor and the hyperdreggmedia authoring
   surfaces, gathered in one place.
3. **Dev** — *the IDE.* A live code editor, a terminal (a real PTY), a shell, and
   devtools as one coherent workspace. (This is where the editor lives.)
4. **Inspect** — *understand.* The moldable inspector (the seven faces), the
   debugger, replay, proofs — point at any object, see it every way, rewind it.
5. **Operate** — *the machinery.* The agent bridge, the powerbox, the
   cipherclerk — the capability / agent / delegation controls.

Two keys you will use constantly:

- **⌘K** — the command palette: a fast finder over *every* action, grouped by the
  five modes, keyboard-first. It is the accelerator, not the only way in — the
  cockpit is navigable without it.
- **⌘J** — toggle the **dev dock** (editor · terminal · shell), available in any
  mode, so code and a PTY are always one keystroke away.

Design reference: [`COCKPIT-UX.md`](../deos/COCKPIT-UX.md).

## Using it

### Make your first card — from "I'm in" to "I made a thing"

The first time you step in, you land on a calm welcome: a few of your own cells,
and two things to *do*. One ("try this") fires a tiny verified turn so you see the
world move. The other — **"make your first card →"** — is the shortest path from
*using* to *making*:

1. **Click it.** A real, editable **card** is minted over your live world — its
   substance is your own home cell, so it is genuinely *yours*, not a demo.
2. **Press its `+1`.** That fires **one cap-gated verified turn** on your cell — a
   real receipt lands on its tape, and the card's live count re-reads and rises.
3. **Edit it live.** "✎ add a button" and "✎ rename the title" each apply a
   **receipted patch with blame** — the card re-folds and repaints immediately.
   The change is an accountable patch, not a recompile; the view is *data*.

That is the whole loop: *a card that is yours → press its button (a real turn) →
edit it live (a receipted patch) → it re-renders.* No internals needed. When you
are ready, "explore everything →" reveals the full cockpit; your card stays minted
on the ledger. From there, **Author** mode is where you keep making and editing
cards.

### Click a cell → its faces

Click any cell and it opens to its **faces** — the moldable inspector shows the
same object many ways: its raw fields, its object-capability graph, a domain
visual, its affordances (what you can *do*), its provenance (its receipt chain),
its invariants, and its source. You "halo" any pretty card down to its sovereign
substance — the inspector and a custom card share one widget vocabulary, so
nothing is opaque. (See [`INSPECTOR-FRAMEWORK.md`](../deos/INSPECTOR-FRAMEWORK.md).)

### Fire an affordance → a verified turn → a receipt

A cell declares **affordances**: named, typed, cap-gated turn templates. An
affordance is "htmx on crack" — the *button* is a cap-gated effect, the
*fragment* it returns is the attested post-state, and *who may press it* is
decided by the capabilities you hold, not by a session cookie. A button **lights
only if both** your capabilities *and* the cell's live state allow it — press an
`approve` button and it goes dark the instant the proposal resolves.

Pressing it fires a **verified turn**. An unauthorized press is refused *in band*
— nothing is submitted, no ghost state. An authorized press commits a real turn
and **leaves a receipt** you can open and inspect.

### Author a card from within

In **Author** mode, the **card editor** lets you edit a card *from inside the
running world*: change its view, its fields, its affordances — and each edit is
a **receipted patch with blame**, not a silent overwrite. The edited card
re-renders to real pixels immediately. Inspection becomes authoring: the gesture
that *looks* at a card is the same machinery that *changes* it.

A view is a function of state: a card's view is a serializable tree
(`vstack`, `row`, `text`, `button`, `input`, `list`, `table`, `bind`) that
re-reads off the live ledger, so a `bind` updates when the cell changes.

### Share via the membrane — a cap-bounded world-fork

To share, you do *not* hand someone raw access. A message can carry a
**membrane**: a **cap-bounded fork** of your world that the recipient
re-attaches to. It is *per-viewer*, *attenuated* (strictly weaker than what you
hold — it can never amplify), and *confined by construction*. Rights are
graduated: granted-in, study-only reference, or a boundary that opens an
owner-consent request. The transport is Matrix chat; merging two diverged forks
back together is a **branch-and-stitch** merge where a conflict is a first-class
object you live in, not a failure.

> **[in flux]** The cockpit's Matrix chat carries the membrane, and the
> cross-user mint → carry → rehydrate → drive → stitch loop runs end-to-end. The
> full *circuit-bound* membrane composition (membrane semantics proven into the
> light-client layer, and the live captp sturdyref path) is still being wired —
> see [`SHARED-FORK-CONSENT.md`](../deos/SHARED-FORK-CONSENT.md) and
> [`MEMBRANE-MERGE-SEAM.md`](../deos/MEMBRANE-MERGE-SEAM.md).

### A rehydratable snapshot

A deos "screenshot" is not a dead pixel grid. It embeds a sturdyref behind a
membrane, so **opening the image re-attaches a live, per-viewer, attenuated
surface** — a paused camera on a witnessed scene that re-expands inside its own
jail. (This is a category only a verified ocap substrate can have.)

### Time-travel the receipt chain

Because every turn leaves a receipt and the chain is root-verified, you can
**rewind**: walk a cell's lineage, open a turn's detail, and go to that point in
its history. The past is **cryptographically the same past for every observer** —
not a local undo buffer, a shared verified history.

## The world to wander — and what's still arriving

The Author and Inhabit modes already hold the keystones: the card editor, the
stitcher (a merge conflict rendered as two live alternatives), the provenance
navigator, the document composer, `dregg://` link-paste transclusions, and
chat-as-a-card. The charter for the whole inhabited world is
[`HYPERDREGGMEDIA.md`](../deos/HYPERDREGGMEDIA.md).

**[in flux] — what is still arriving:**

- **The fully-reflective cockpit.** Today the cockpit *frame* is native (gpui);
  its surfaces are mid-conversion to deos-js **cards**, so that you can edit a
  surface's view live and author new surfaces from within. v1 = a frame you
  navigate; v2 = a frame you rewrite while it runs.
- **Renderer-independence in practice.** The world painting in a *browser tab*
  (web-deos) and on seL4 is on the roadmap; the substrate is renderer-independent
  by design, the alternate glasses are being brought up.
- **The MUD** — a shared cap-secured world you wander collecting gadget-cards, run
  as a privileged "GM" server (rich, not fog-of-war by default) — is a frontier.
  See [`DREGG-MUD.md`](../deos/DREGG-MUD.md).
- **Web interspersing** — `http(s)://` pages rendered inside the cockpit through a
  net-capability gate (libservo) — stands behind a mock surface in places today.

Treat anything marked **[in flux]** as "designed and partly built, not yet the
finished, proven thing." When in doubt, the [ATLAS](../../dregg-atlas/site/index.html)
shows what each surface actually is.
</content>
