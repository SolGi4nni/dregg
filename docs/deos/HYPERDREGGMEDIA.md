# HYPERDREGGMEDIA — the charter

*What the inhabited world of deos is, what of it runs today, and where it goes. Present-tense
("what it is"), honest built-vs-open. The investigation that grounds it (the lineage's soul, the
substrate census, the HyperCard→dregg mapping) lives in `HYPERDREGGMEDIA-NOTES.md`; this is the
declaration. Companions: `SCRIPTING-AND-DISTRIBUTED-DOM.md`, `DOCUMENT-LANGUAGE.md`, `DEOS.md`.*

---

## The thesis

**Hyperdreggmedia is the inhabited world of deos, arising fully inside dregg as rich live
hypermedia — where every card is a sovereign cell, every button a verified turn, every stack
forkable / transcludable / mergeable / time-travelable, the whole thing AI-co-authorable, and
none of it tied to one renderer or one machine.**

For forty years the lineage of authoring systems chased a single wish — *collapse the wall
between using software and making it* — and almost every one hit the same ceiling: no
**ownership**, no **verifiability**, no **shared substrate**. HyperCard let everyone author but
never networked. Smalltalk was a live image you edit from inside, with no security or provenance.
Xanadu wanted transclusion and shipped vapor. The AI-native wave makes "the prompt the program"
but the program is opaque, throwaway, ownerless. Dregg is built across exactly that ceiling, so
hyperdreggmedia is not a new idea — it is *the* idea, finally with a spine.

## The frame (load-bearing)

The Rust cockpit (`starbridge-v2`) is the **VM and the dev basement** — the bare-metal boot, the
inspector, the thing an adept drops into. It is *not* the world. The inhabited world arises
**inside dregg**: defined in cells, caps, turns, and documents, not in Rust. Two consequences:

- **Renderer-independence.** Because a hyperdreggmedia world is defined in dregg, not in gpui,
  the *same* world can be painted by the Rust cockpit, by a browser tab (web-deos), or on seL4 —
  same sovereign substance, different glass. The interface stops being "the app" and becomes one
  face among many.
- **No wall between playing and building.** A five-year-old clicks a card in delight (AOL-era
  wonder); an adept halts it, inspects its capability tree, rewinds its receipts, and reshapes it
  live (Pharo liveness) — *the same object, the same image.* That wall, the one the lineage spent
  decades trying to tear down, was here never poured.

## The substrate (built + proven)

Every primitive hyperdreggmedia needs already runs, gpui-free where it matters and verified
throughout:

- **A card is a cell.** Sovereign, its state a cryptographic commitment, its behavior `run_js`
  you can read, its authority a tree of capabilities you hold like keys. (`deos-js`, `cell`.)
- **A button is a verified turn.** Authority is *production under non-forgeability* — a button
  you may press is a proposition you can prove; pressing it is a cap-gated turn that leaves a
  receipt. (`Deos/Affordance.lean`, `deos-reflect/affordances`.)
- **A view is a function of state.** `deos.ui.{vstack,row,text,button,input,list,table,bind}`
  builds a serializable view-tree that `deos-view` renders to real gpui-component widgets; a
  `bind` re-reads off the live ledger; the fine-grained dirty-set wakes only the touched node.
  (`deos-view`, `deos-js/signals`.)
- **A document is patchable, transcludable, mergeable.** The dregg-doc patch-core: edits are
  patches with blame, a transclusion is a receipt-pinned live quote that *cannot rot* and that a
  forged citation is *inexpressible* against, a merge is a pushout and a conflict is a
  first-class `ConflictRegion` (never a silent overwrite). (`dregg-doc`, `cell_transclusion`.)
- **A moment is forkable + multiplayer.** The membrane: a message is a cap-bounded world-fork you
  drive and stitch back; the real cross-user mint→carry→rehydrate→drive→stitch loop runs in one
  process over a real homeserver. (`shared_fork`, `deos-matrix`.)
- **Everything is moldable + reflective.** Seven `present()` faces (RawFields · ocap Graph ·
  DomainVisual · Affordances · Provenance · Invariant · Source) over every object; the inspector
  and the custom view share one widget vocabulary — halo any pretty card down to its sovereign
  substance. (`deos-reflect`, `presentable`.)
- **Time is rewindable.** Root-verified replay; the past is cryptographically the same past for
  every observer. (`time_travel`.)

## The authoring layer (the epoch, built)

The substrate was the loom; the authoring layer is the world becoming editable *from within*. Its
unifying law: **every authoring gesture is an affordance, every affordance is a turn, every turn
is a receipt** — so the whole authoring surface is one machinery pointed at the cells' own
schemas. The keystone and its eight specializations all run:

- **Card editor** (the root) — edit a card's view / fields / affordances from within, each a
  receipted patch with blame; the edited card re-renders to real pixels. Inspection becomes
  authoring.
- **Stitcher** — a merge conflict rendered as two live alternatives; resolve by a verified patch.
- **Provenance navigator** — a cell's receipt-chain walkable: lineage, turn-detail, go-to-that-point.
- **Fork / consent** — the membrane's tiers made visible; a consent inbox of pending turns; upgrade requests.
- **Document composer** — compose a doc from cells (embed / reorder / re-role as turns).
- **Desktop authoring** — the desktop layout itself a witnessed, rewindable cell.
- **`dregg://` link-paste** — select a cell → a URI → paste a live provenanced transclusion.
- **Multi-cell agent turns** — author a story spanning cells, cap-confined across vessels.
- **Chat-as-a-card** — a room is a cell, a message is a turn, send is an affordance.

## The inhabitant (the soul in the vessel)

An agent put into deos is not a tool calling an API; it **inhabits** the world. It can:
**see** (the cap-bounded reflective crawl — the whole image legible within its authority),
**drive** (`run_js` attached to the *live* cockpit World — a real Claude on Copilot has crawled
real cells and fired receipted turns), **understand** (the dregg source is bundled inside deos as
a cap-bounded read — it can read the code of its own world), and **author** (it patches a card's
view live, every edit a receipt). It is **empowered-but-accountable**: broad authority over its
own world is a feature, every action is a rewindable receipt, and the only wall is the membrane —
it provably cannot forge authority or reach into another soul's vessel (18 adversarial red-team
attacks, every escalation refused). The dregg-as-host inversion makes dregg the primary means of
coordination: the agent is jailed in a confined PD, its tools route to our containers, and the
real world is one explicit, cap-gated, opt-in egress.

## The five holy grails — newly possible on dregg

What no prior system could reach, because none had the spine:

1. **Unforgeable, never-rotting transclusion** — Nelson's docuverse, shipped.
2. **AI-authored software bounded by capabilities it provably cannot exceed** — safe generative authoring.
3. **Multiplayer as cap-bounded world-forks that stitch by pushout** — zero-loss merge, conflicts as objects.
4. **Verified time-travel** — the past is the *same* past for everyone, cryptographically.
5. **The sovereign live image** — Pharo-moldable, simultaneously secure, verified, provenanced, distributed.

## Honest state — built vs prototype vs frontier

- **Built + proven (runs):** cells · caps · turns · receipts · transclusion · reversible turns ·
  deos-js · deos-view · dregg-doc · run_js (on the live World) · the moldable inspector · the
  card-editor keystone + the 8 authoring surfaces · the source-vessel · the agent red-team.
- **Prototype (executor-side / protocol-designed, not yet circuit-bound):** membrane composition ·
  branch-and-stitch multiplayer · the dregg-as-host jail (real jail + dregg-tools-only effect-path;
  the live brain in-jail via a confined MCP tool-bridge is the closing wire).
- **Frontier (the roadmap):** the world painting in a *browser tab* and on seL4 (renderer-
  independence) · the document language at full fidelity (the patch-history living *in* the cell,
  dregg-doc's `substrate` ride) · cross-*machine* migrate · the MUD (a shared cap-secured world
  you wander, collecting gadget-cards) · the gadget rolodex · co-driven multiplayer cards.

## The north star (the self-hosting cure)

The deepest move makes the whole thing self-reinforcing: when dev itself moves **into** dregg —
files are cells, edits are receipted patches — two authors on one artifact produce a
`ConflictRegion` (the stitcher), not a stomp. The hazards of shared mutable state become
impossible by construction, because the system is built out of the very primitives that solve
them. Hyperdreggmedia authoring dregg, in hyperdreggmedia. That is where this goes: a medium
malleable enough to be its own construction tools, owned and verified all the way down — the
revolution Kay said hadn't happened yet, with the spine it was always missing.
</content>
