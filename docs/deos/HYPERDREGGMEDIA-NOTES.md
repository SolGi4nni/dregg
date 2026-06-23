# HYPERDREGGMEDIA — investigation notes

*Pre-charter working notes. "The HyperCard guy on a tab of acid." Investigation captured before
the charter is written — so the charter stands on grounded soul, not vibes. Two sweeps: the
lineage (what the 40-year dream was + why each ancestor fell short) and the substrate census
(what dregg already runs + the HyperCard→dregg mapping + the gaps). Honest built-vs-sketch kept
throughout. Companion to `SCRIPTING-AND-DISTRIBUTED-DOM.md`, `DOCUMENT-LANGUAGE.md`,
`DEOS.md`.*

> **The frame (ember):** the Rust cockpit is the *VM/dev basement*; the inhabited world arises
> **fully inside dregg** as rich live hypermedia — every card a sovereign cell, every button a
> verified turn, every stack forkable/transcludable/mergeable/time-travelable, AI-co-authored
> live. Renderer-independent: the same world paints in the cockpit, the browser, on seL4.

---

## 0. The through-line (one sentence)

Forty years of the lineage chased a single wish — **collapse the wall between *using* software
and *making* it** — and almost every system hit the *same* ceiling: no **ownership**, no
**verifiability**, no **shared substrate**. dregg is built across exactly that seam. So
hyperdreggmedia is not a new idea; it is *the* idea, finally with a spine.

---

## 1. The soul-table — the lineage

| System | The ONE magical idea | The dream | Why it fell short | What HYPERDREGGMEDIA delivers |
|---|---|---|---|---|
| **HyperCard** | Click a button, link a card — you've made a program. The desktop you *browse* is the one you *edit*, live. | "Programming for the rest of us." | **Never networked** (Atkinson: "it might have been the first Web browser"); bundled-free → starved → killed 2004. | A stack is a **cap-secured cell-graph** other sovereigns hold/fork/transclude. Network-native by construction; every button a receipted turn. |
| **Smalltalk / Squeak / Pharo** | The whole running system is one persistent **live image** edited from inside itself. No edit/run wall. | A medium so malleable the system *is* its own construction tools. | No security (ambient authority), no transactions, no provenance, no real multi-user/distribution. | starbridge-v2 **is** that image — plus ocap (no ambient authority), verification (every message a conservation-checked turn), provenance (receipt-chain), distribution (the image is a commitment among sovereigns). |
| **Kay's Dynabook** | A computer is a **medium you author in**, like dynamic paper — not an appliance you consume. | Computation as literacy for "children of all ages." "The revolution hasn't happened yet." | The hardware came; the *medium* didn't. We put paper + TV on glass. | Authorable all the way down + AI-co-authored: a child describes a world, Claude writes `run_js` against live cells, leaving receipts the child can rewind. The medium Kay meant — with a verification spine. |
| **Engelbart NLS/Augment** | The computer as **intelligence amplifier**; **viewspecs** — one structured doc, many views. | Boosting **collective IQ**; humans+tools co-evolving by bootstrapping. | The world kept the mouse, dropped the augmentation philosophy. | Viewspecs become **cap-attenuated projections**: the *same* cell renders per the viewer's capabilities. Collective IQ returns as the **membrane** (a message is a cap-bounded world-fork you drive + stitch). |
| **Nelson's Xanadu** | **Transclusion** — content lives once, appears everywhere by reference; unbreakable two-way links; the docuverse. | A universal library where every quote stays tied to its source. | "Longest-running vaporware in computing." The web won with one-way, ever-breaking, copy-paste. | **Built + proven**: a verified cross-cell quote pinned to an immutable **receipt** — the bytes provably equal what the source committed, the citation *never rots*, `Backlinks` give two-way nav. A forged quote is *inexpressible*. |
| **Boxer (diSessa)** | A **reconstructible medium** — nested boxes, everything visible/inspectable in place, no hidden state. | Programming as literacy; one uniform learnable world. | Stayed academic. | The **moldable inspector** makes every cell/cap/receipt a visible in-place object — "no hidden state" enforced cryptographically (the commitment *is* the state). |
| **LOGO (Papert)** | The turtle as an **"object to think with"**; constructionism — learn by building shareable artifacts. | "Mathland." | Entered schools as turtle-drawing stripped of the pedagogy. | Every artifact a child builds is a **sovereign, shareable, forkable cell** with a receipt-chain — constructionism where the thing is *real, yours, givable* without loss. |
| **Notion** | **Everything is a block** — one recursive composable draggable primitive. | Lego for software; the composable everything-app. | Blocks are rows in *their* Postgres; a block is a record, not a programmable object you own. | Every block is a **cell you own** — programmable (its own `run_js`), cap-bearing, with verifiable history. Composability that bottoms out in *sovereignty*. |
| **Roam / Obsidian** | **Bidirectional links** + block-reference (closest popular tool to transclusion). | Networked thought; a second brain. | Links between *text notes*, not live objects; no verifiable substrate. | Backlinks over **live cells** + **verified transclusion**. A second brain that's *unforgeable and yours*. |
| **tldraw / Figma** | Infinite canvas + **multiplayer direct manipulation**; "make real." | Design as one shared live medium. | Proprietary; "make real" emits throwaway code; substrate you don't own. | The canvas is a **cell-graph**; multiplayer is the **membrane** (cap-bounded forks that *stitch by pushout*, conflicts-as-objects). "Make real" makes a *real cell*. |
| **Observable / Val Town / Jupyter** | Live **reactive** notebooks — cells re-run "like a spreadsheet." | Exploration at the speed of thought. | Jupyter's hidden kernel state → ~36% out-of-order, silently-wrong results. | **No hidden state**: state *is* the commitment, execution *is* a receipt-chain (deterministic, replayable, rewindable). Re-running is *proof*. |
| **Glamorous Toolkit** | **Moldable development** — a bespoke tool/inspector per object, in seconds, from within. | The system explains itself. | Total moldability *inside* one local Pharo membrane; near-zero outside. | Moldability across a **distributed ocap-secured substrate** — the tool you mold is a cell you grant/fork/transclude/prove. |
| **Webstrates** | Web pages as **shareable malleable collaborative substrates**. | Kay's "media that blur documents + applications," reprogrammable from inside. | Fragile research substrate; OT-on-DOM heavy; never durable. | **Renderer-independent** (deos-js is gpui-free) + durable by commitment — the dream with a verified ownable spine, not an OT server. |
| **Ink&Switch / local-first / Cambria** | **You own your data in spite of the cloud**; Cambria **lenses** migrate data across schema versions. | Adaptation "at the point of use, not through distant engineering teams." | Their own verdict: AI codegen alone is "a talented sous chef in a food court" — **the owned, verifiable, shared substrate is the unshipped part.** | **dregg IS that substrate.** Sovereignty + receipts + caps + the patch-core doc language (Cambria lenses → `reprogramCell` + verified migration patches). The food court becomes a kitchen you own. |
| **AI-native (Artifacts / v0 / generative UI)** | **The prompt is the program** — describe it, get a live app inline. | Everyone authors software by describing it. | Generated code is opaque, throwaway, ungoverned, ownerless. | Claude authors **into the sovereign substrate**: writes `run_js` against *your* cells, every action a **cap-gated verified receipted turn** it *provably cannot exceed*. The prompt is the program, and the program is *trustworthy*. |

---

## 2. HYPERDREGGMEDIA, on acid (the maximal grounded vision)

Boot the image. There is no desktop and no apps — there is a **living docuverse of sovereign
cells**, and you are standing inside it. Every card is a cell that *owns itself*: its state is a
cryptographic commitment, its behavior is `run_js` you can read, its authority is a tree of
capabilities you hold like keys. No "file," no "open" — only *what exists* and what you are
*permitted to touch*. HyperCard's gray desktop, except the desktop is a verified universe and
every button press leaves a receipt a stranger across the planet can check without trusting you.

You point at a card — a budget tracker a friend made — and tell Claude, *"make this also chart my
spending, and let my partner add expenses but not delete them."* Claude writes `run_js`, **mints
a capability attenuated to add-only**, and hands it toward your partner through the powerbox. The
chart appears. You didn't get *code*; you got a **turn**, and the turn left a receipt chaining to
the one before, so the whole life of this tool is a navigable causal history you can **rewind**
like videotape. Your partner, three timezones away, opens the same cell — but their **viewspec is
their capability**: they see add-expense and *not* delete, because the projection is
cap-attenuated per viewer. Engelbart's viewspecs and Kay's medium fused into one surface, and the
difference between the two views is not a UI flag — it's *cryptographically enforced authority*.

Now the acid kicks in. You want a wild redesign without breaking the working thing, so you **fork
the world** — not the file, the *world*. A message in your dregg-pilled chat *is* a cap-bounded
fork: you and four friends each drive a counterfactual branch of the same stack, confined so your
experiments **cannot touch the real cells** until you settle. You time-travel to last Tuesday's
receipt and fork *from the past* — a consensual virtualized past, an event-structure branch in
the config lattice. When two of you edit the same paragraph, there is **no conflict-loss and no
last-writer-wins**: the patch-core merges by **pushout**, and the conflict becomes a *first-class
object on the canvas* — two live alternatives, each tagged with its author's provenance, until
someone writes a resolution patch. Xanadu's parallel documents with visible connections —
*shipped, and the connections are proofs.*

And the docuverse is *real*. You quote a number from a public economic cell into your essay — not
a copy, a **transclusion** pinned to that cell's receipt #4471. The author later revises; your
citation **does not rot** — it still shows exactly what they committed when you cited it,
provably. Follow the backlink and you see *every* cell in the world that transcludes that number.
A forged quote is not discouraged — it is *inexpressible*; the circuit will not accept a citation
whose bytes don't match the cited commitment.

The whole thing is **moldable from within** like Pharo, but distributed and verified like nothing
before. Don't like the inspector? Mold a new one — it's a cell; grant it to a friend. Want the
chart to be a 3D garden where each plant is a budget line? Tell Claude; it rewrites the cell's
`run_js`; the renderer is pluggable so the same sovereign substance blooms differently on every
screen. A five-year-old clicks around in delight, absorbing without comprehension (1999-AOL
wonder); an adept halts a running cell, inspects its capability tree, rewinds its receipts, and
reshapes it live (Pharo liveness) — *the same image*, because in hyperdreggmedia there was never a
wall between the one who plays and the one who builds. That wall was the wall the whole lineage
spent forty years trying to tear down. Here it was never poured.

---

## 3. The 5 holy grails — newly possible on dregg, unreachable by any prior system

1. **Unforgeable, never-rotting transclusion** — the docuverse Nelson couldn't ship. A quote
   provably equals what the source committed at a finalized receipt; forgery is *inexpressible*;
   the two-way link is a witness-graph read. *(rests on BUILT primitives: cell commitment +
   transclusion + Backlinks.)*
2. **AI-authored software bounded by capabilities it provably cannot exceed** — `run_js` firing
   cap-gated verified turns; the prompt becomes the program *and* the program is confined +
   rewindable. *(BUILT.)*
3. **Multiplayer as cap-bounded world-forks that stitch by pushout** — fork the whole world
   safely, merge with zero loss, the conflict is a first-class object. *(partly PROTOTYPE: membrane
   composition + branch-and-stitch are executor-side / protocol-designed, not yet circuit-bound.)*
4. **Verified time-travel** — the past is cryptographically the *same* past for every
   participant; fork counterfactuals from a virtualized past. *(rewind/snapshot BUILT;
   cross-device RCCS settlement SPECULATIVE.)*
5. **The sovereign live image** — Pharo-moldable-from-within, simultaneously secure, verified,
   provenanced, distributed — the "owned verifiable shared substrate" Ink&Switch named as the one
   thing nobody shipped. *(BUILT.)*

---

## 4. The substrate census — what already RUNS

All STEEL/WORKING, file-cited (the hyperdreggmedia *loom* is built; the *cloth* — the authoring
surfaces — is §6):

- **Applet** (`deos-js/src/applet.rs`) — a cell IS a program; state = ledger fields; every turn
  cap-gated + receipted.
- **JS binding** (`deos-js/src/js.rs`) — real SpiderMonkey over `deos.world.cells()`; fires are
  real verified turns under the caller's attenuated `held`, never root.
- **Affordance** (`deos-reflect/src/affordances.rs`, `starbridge-v2/src/affordance.rs`) —
  cap-gated typed effect-templates; per-viewer `project_for(held)`; a weaker viewer sees *fewer*
  buttons (attenuation, not enhancement).
- **View-tree** (`deos-view/src/{tree,render}.rs`) — `deos.ui.*` → real gpui-component widgets;
  `bind` re-reads off the live ledger; button click fires a turn; input = ephemeral (no turn).
- **Reflective crawl** (`deos-reflect/src/substance.rs`) — every object → uniform `Inspectable`
  tree; attested read (committed fields show commitment, never cleartext).
- **Whole-cell transclusion** (`starbridge-v2/src/cell_transclusion.rs`) — embed a peer cell by
  reference, receipt-pinned, four proven Xanadu properties (observed-finalized / provenance-
  faithful / no-amplify / stable-under-advance).
- **Shared fork** (`starbridge-v2/src/shared_fork.rs`) — three-tier graduated consent
  (EMBEDDED / STUDYREF / NETWORKBOUNDARY); real grants + conditional turns.
- **Program-source document** (`deos-js/src/program_doc.rs`) — a gadget's source IS a
  `dregg_doc::Doc`; edits are patches, blame per line, merge = pushout, transclude fragments.
- **Desktop-as-document** (`starbridge-v2/src/desktop_doc.rs`) — the scene is a mergeable,
  rewindable, branchable cell-graph; window = `Op::Embed`; multi-device contention = conflict
  state, not silent loss.
- **Time-travel** (`starbridge-v2/src/time_travel.rs`) — root-verified replay; reversible vs
  committed boundary; Live-at-head / ReplayedDeterministic-in-past.
- **run_js agent hands** (`deos-hermes/src/run_js.rs`) — agent runs JS under its OWN attenuated
  mandate; both EMBEDDED + ATTACHED(live World) binding paths.

**HyperCard → dregg:** CARD = a cell-via-a-face · STACK = a doc composed from cells + the
web-of-cells · BUTTON = an affordance (cap-gated turn) · FIELD = a cell slot · HyperTalk = deos-js
/ program-doc · message hierarchy = the turn/event system · HOME = the user's root cell +
desktop-as-document · go-to-card/links = transclusion + `dregg://` addressing · backgrounds =
shared-fork tiers · browse-vs-author = guest-door vs F11-cockpit (same cells, different faces).
**No HyperCard analog:** sovereignty, receipts, caps, time-travel, multiplayer-fork-stitch,
provenanced transclusion, code-as-patch-history, renderer-independence, desktop-as-document.

---

## 5. Honest built-vs-sketch (the discipline holds even on acid)

- **BUILT + proven:** cells · caps · turns · receipts · **transclusion** · reversible turns ·
  deos-js · run_js · deos-view render · program-source-document · desktop-as-document · time-travel
  rewind · starbridge-v2 live image · the patch-core document language.
- **PROTOTYPE (executor-side / protocol-designed, not yet circuit-bound):** membrane composition ·
  branch-and-stitch multiplayer.
- **SPECULATIVE / future:** Golden-Vision recursive-proof aggregation · cross-device RCCS
  settlement · the four named-not-proven verified-deos Lean theorems (surface-as-cap / membrane
  non-amp / liveness-type / affordance-soundness).
- One architectural residual: the app-framework runs on a *separate* ledger from the live World
  (apps over their own substrate). Fold-in OR unify-at-the-view-layer — both work; honest.

---

## 6. The shortest path — the authoring layer (immediate development directions)

The *substrate* is built; what's missing is **authoring** — today you inspect + navigate cards but
can't *edit* them from within. The unifying truth: **every authoring gesture is an affordance;
every affordance is a turn; every turn is a receipt.** So the whole authoring layer is one machinery
pointed at the cells' own schemas. The eight surfaces between us and a HyperCard-of-dregg:

1. **Card editor** (`card_editor.rs`) — edit a card's schema/affordances/fields *as verified turns
   on the cell*. The keystone: turns inspection into authoring.
2. **Multi-cell agent turns** (extend `deos-hermes/run_js`) — the agent authors stories spanning
   cells, cap-tooth-confined across vessels. (Lets a Claude build a whole stack, not one card.)
3. **Stitcher UI** (`stitcher.rs`) — render a conflict antichain as two live alternatives; pick /
   edit / commit a resolution patch. (Conflicts-as-objects, made touchable.)
4. **Fork / consent UI** (`fork_ui.rs`) — show EMBEDDED/STUDYREF/NETWORKBOUNDARY tiers + a consent
   inbox (pending ConditionalTurns, upgrade requests). (Multiplayer you can *see*.)
5. **`dregg://` link-paste** (extend `desktop_doc.rs` + `deos-view`) — select a cell → get a URI →
   paste a live provenanced transclusion + resolve-status. (Xanadu links, usable.)
6. **Desktop authoring** (extend `view_cell.rs`) — drag z-order / open / close as layout-edit
   turns. (The desktop becomes editable, and the edits are receipts.)
7. **Document composer** (`document_composer.rs`) — add/reorder/role embeds (`Op::Embed/Connect/
   Delete`) as turns on the document cell. (Compose a doc from cells, by hand.)
8. **Provenance navigator** (extend `reflect.rs` + `time_travel.rs`) — blame/who-did-what face;
   click a receipt → turn details + author → time-travel there. (The receipt-chain, walkable.)

**Plus the agent-authors-its-own-UI demo** (the Nous flex): a Claude `run_js`-patches a live
applet's view-source (a dregg-doc) → deos-view re-renders → the UI changed, the edit a receipt.
This is #1 + #2 composed, and the first thread of "weave the world."

---

### Sourcing & honesty notes
Atkinson's "first web browser" lament — verified via mirrors of WIRED Aug 2002 (primary
access-blocked). Webstrates = UIST'15 (not CHI). Kay Dynabook lines — via Wikipedia paraphrase of
Kay. LOGO "low floor/no ceiling" = later Resnick/Scratch formulation, not verbatim Papert. GT
"tool per problem" = paraphrase. The acid vision treats prototype/speculative items as the
coherent destination; the holy-grails I–II + V rest on built primitives, III–IV partly on the
prototypes (flagged). Full per-system source lists are in the research-agent task outputs.
</content>
