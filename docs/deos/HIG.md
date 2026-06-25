# The deos Human Interface Guidelines

*A UX that doesn't lie.*

Every desktop metaphor before deos was a beautiful fiction — files that aren't in
folders, permissions hidden in dialogs, history gone the instant you act. The genius
of Lisa / Xerox Star / PARC was making a coherent *fiction* you could manipulate.
deos's once-in-a-generation shot is different: its substrate is the rare one where the
truth is already coherent — sovereign cells, visible capabilities, total receipted
history. So the deos interface does **not** paste a metaphor over the machine. It shows
you what is *real*, and what is real turns out to be gorgeous.

This document is the spine. Build every surface against it. When a surface and this
document disagree, the surface is wrong.

## The thesis

The interface is a faithful, beautiful, **direct manipulation of the kernel's own
semantics.** Learn four words — **cell · capability · turn · receipt** — and you
understand the entire OS. Nothing on screen is a fiction; everything is the real
object, the real authority, the real action, the real history.

## The model

- **The noun is the CELL.** Everything you touch — a card, a document, an agent, a
  room, a service, *you*, even a surface of this cockpit — is a cell, drawn the one
  coherent way. Learn one object; you know all of them. (PARC's "everything is an
  object," but the object is sovereign and verifiable.)
- **The verb is the TURN.** Every action commits *visibly* and leaves a receipt. There
  is no invisible mutation; the commit is the feedback.
- **Authority is the CAPABILITY, and it is VISIBLE.** An affordance is live *iff* you
  hold the cap for it — you *see* your power, you never hunt a permissions dialog.
  Granting is handing someone a key: attenuable, in the open.
- **History is the RECEIPT chain, and it is the interface.** "Undo" is not a fragile
  stack — it is *time*, total and real. Scrub the receipts; fork the past; lose nothing.
- **Sharing is the MEMBRANE — a gift, not a copy.** You hand a bounded slice of your
  world across; it stays cap-confined; it doesn't drift.
- **Reflection is one GESTURE.** Flip any cell around → its faces (state · history ·
  caps · links · the seven presentations). The Smalltalk inspector, over verified
  objects, a single motion away.

## The principles

1. **Learnable once.** Four ideas, ruthlessly consistent, explain everything. If a
   surface needs *new* vocabulary to be understood, the surface is wrong.
2. **Calm by default, depth on demand.** A child clicks a glowing cell and something
   delightful happens; the adept flips the *same* cell to its faces and reshapes it
   live. No mode-tax to go deep, no clutter to stay shallow.
3. **Speak human, not compiler.** "Refused — you don't hold that capability," never
   "T1 REJECT." The machine's truth, in a person's words. Systems jargon is an opt-in
   inspector face, never the default surface.
4. **One focused thing per screen.** The rail names the few *rooms*; the content is the
   *one* active cell/surface, clean. Never dump the whole space-of-surfaces into the
   body — that's the rail's and the spotter's job.
5. **Authority and proof always in view, never anxious.** You never have to *trust*:
   the cap is visible, the proof is there, the receipt is the response. (Licklider's
   symbiosis, minus the dread.)
6. **Nothing draws twice.** One object renders in exactly one place per frame. No
   card-over-native overlap, no z-fighting, no redundant grid.
7. **gpui-component is the material.** Real lists, panels, inputs, menus — fluent and
   consistent — not bespoke dense text-grids. The component library is the wood; this
   document is the joinery.

## The visual + interaction language

- **A cell** is one consistent object-representation: an identity badge drawn by the
  shell from the live ledger (anti-spoof — a surface cannot impersonate another cell),
  its substance, its affordances. Same shape whether it's a doc, an agent, or a room.
- **A turn** is an action you *watch*: the affordance fires, the state moves, a receipt
  appears on the lineage.
- **A capability** is a key/badge you can see and hand over. Held caps light their
  affordances; ungranted ones are visibly *dim*, not hidden.
- **Reflection** is a halo/flip on any cell → its faces, the seven presentations, each
  rendered by *one* generic widget. Search every object's every face with the spotter;
  a hit re-focuses.
- **Discovery crawls CELLS.** Surfaces are cells too, so finding a surface is the same
  gesture as finding anything. The rail names the rooms; the spotter finds the rest.
  (We still expose every surface — through one coherent model, not a wall of buttons.)

## The lineage we build from

Lisa / Xerox Star / PARC Smalltalk — *structured semantics made visible*. The original
Macintosh HIG — *a small model, ruthlessly consistent*. Pharo — *the image is its own
IDE, malleable from within*. Licklider — *man-computer symbiosis, augmenting intellect*.
Woz — *elegant, and it works*. Jobs — *delightful, and surprising*. deos's addition the
lineage never had: **the metaphor is true, and the truth is verified.**

## Anti-patterns (what the cockpit must stop doing)

- Showing every surface + every internal at once (the debug-instrument-as-UI).
- Compiler/systems jargon in the default face ("EMIT-EVENT notify edge," "async A2
  inbox seam," "T1 REJECT").
- The same grid/object rendered in two panes (redundancy + overlap).
- A card mounted *over* the native panel it replaces (two things, one bounds — the
  perilous z-fight).
- Fine-grained build-features leaking into the user's experience (a "plain zed tab"
  because zed-full sits behind a flag nobody opted into).

---

*Relates to [[project-deos-ux-vision]] (AOL-wonder × Pharo-liveness — the test this
serves) and `docs/deos/INSPECTOR-FRAMEWORK.md` (the seven presentations / Halo / Spotter
machinery this language renders). The cockpit is rebuilt **against this document,**
surface by surface — calm content, human words, one thing per screen, zed-full default.*
