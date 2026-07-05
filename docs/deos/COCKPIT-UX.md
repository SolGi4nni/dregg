# COCKPIT-UX — a coherent cockpit (the design)

*The starbridge cockpit accreted ~20 surfaces behind a flat command palette + a scatter of
panels, with no home, no grouping, no flow — "a mess of unusable panels, no coherent UX or
devex" (ember). This is the design that replaces the junk drawer with a frame. The test (the deos
UX vision): a 5-year-old clicks the home with delight, AND an adept hits one key → zed and works.*

## The diagnosis

The surfaces exist and mostly work (Home, Composer, Simulate, Objects, Debugger, Replay,
Cipherclerk, Editor, Shell, Agent, Buffer, Terminal, Swarm, Graph, Organs, Proofs, Powerbox,
Devtools, WebShell, …). What's missing is **structure**: they're peers in a flat `Go<Surface>`
palette, reachable only through a palette that (until just now) didn't even scroll. There is no
spatial memory, no "what is this place," no grouping by intent, no dev workspace — just 20 doors
in a hallway with the lights off.

## The frame (the persistent shell)

One stable chrome around everything, so the cockpit has a *shape* you learn once:

- **Top bar** — who you are (the identity cell + its cap-badge), the world clock (ledger height +
  the latest receipt, always live), and the palette summon (⌘K). Calm, always-present.
- **Left rail — the FIVE MODES** (below). One click switches the whole content pane's intent.
  Not 20 items; five. The rail is the coherence.
- **Main pane** — the active surface for the current mode.
- **Dock (bottom, collapsible)** — the dev workspace (editor · terminal · shell) as ONE
  persistent IDE strip, available in any mode (⌘J toggles it), so code/PTY is always a keystroke
  away instead of a lost surface.

## The five modes (the 20 surfaces, grouped by intent)

1. **Inhabit** — *your living world.* The home garden: your cells as clickable objects (AOL-era
   wonder — click around, no comprehension needed), the ocap Graph, Objects, the world map. This
   is the landing.
2. **Author** — *make things.* The Composer, the card editor, the document surfaces — the
   hyperdreggmedia authoring layer (the 8 surfaces) gathered in one place.
3. **Dev** — *the IDE.* Editor (live deos-zed), Terminal, Shell, Buffer, Devtools — as one
   coherent workspace, not scattered doors. **This is where zed lives**, with a file tree + the
   editor + a terminal, like a real IDE. (The Dock is this mode's strip, surfaced everywhere.)
4. **Inspect** — *understand.* The moldable inspector (the seven faces), Debugger, Replay, Proofs,
   Organs — point at any object, see it every way, rewind it.
5. **Operate** — *the machinery.* Agent, Swarm, Powerbox, Cipherclerk — the cap/agent/delegation
   controls, for when you're running things.

## The home (the landing that earns the wonder)

Not a dashboard of stats — **the living image as a place.** Your cells rendered as a garden of
clickable cards (balances, documents, rooms, agents), each one openable to its moldable faces,
each one *doing something* you can act on. "What can I do here" is surfaced as visible affordances
on the cards themselves, not hidden in a palette. A child clicks a card and something happens; an
adept halts it and inspects it. Same place.

## The palette, demoted to a tool

⌘K stays — but as a *fast command-finder*, not the only way in. Commands grouped under the five
modes (so `editor` finds it under Dev), scrollable (fixed), keyboard-first. It's the power-user
accelerator over a cockpit that's already navigable without it.

## The reflective path (why this isn't just a paint job)

The v1 frame is Rust (gpui) — coherence now. But the surfaces becoming **deos-js cards** (the
fully-reflective-cockpit campaign) is what makes the frame *yours to reshape from within*: drag a
surface between modes, edit a card's view live, author a new surface as a card — Pharo-liveness
over the coherent frame. v1 = a frame you can navigate; v2 = a frame you can rewrite while it
runs. The coherence and the reflectivity are the same campaign from two sides.

## Build order — SHIPPED (`starbridge-v2/src/cockpit/frame.rs`)

The whole ladder is built. `CockpitMode::{Inhabit,Author,Dev,Inspect,Operate}` (`frame.rs`, cites
this doc) is the five-mode rail; the rail order and surface→mode mapping are READ from a live
`deos_js::LayoutCard` cell, and moving a surface between modes dispatches
`deos_js::LayoutCard::reshape(LayoutPatch::MoveSurface)` as a receipted cap-gated turn with blame —
so step 5 (the reflective turn) is real, not just designed.

1. Palette scroll fixed (navigation works at all). ✅ done.
2. **The frame + five modes + the rail** — the structural pass (this doc's core): one chrome, the
   left rail, the mode router, the always-present top bar + dock toggle. Re-home the 20 surfaces
   under the five modes (no surface deleted — regrouped). ✅ done (`CockpitMode`, `frame.rs`).
3. **The home garden** — the Inhabit landing as clickable cells with visible affordances. ✅ done
   (the Inhabit landing hosts Home/Wonder/Objects/Graph).
4. **The Dev workspace** — editor+terminal+shell consolidated into one IDE strip/mode (zed, a
   file tree, a PTY), and the Dock made persistent. ✅ done (the Dev mode).
5. **Surfaces → deos-js cards** — the reflective turn (joins the fully-reflective-cockpit
   campaign): the frame becomes malleable from within. ✅ done — the layout is a live
   `deos_js::LayoutCard` and a reshape-from-within is a receipted `LayoutPatch::MoveSurface` turn.
</content>
