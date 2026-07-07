# HYPERDREGGMEDIA — the charter

*What the inhabited world of deos is, what of it runs today, and where it goes. Present-tense
("what it is"), honest built-vs-open, every open seam CLASSIFIED with its closure lane. The
investigation that grounds it (the lineage's soul, the substrate census, the HyperCard→dregg
mapping) lives in `HYPERDREGGMEDIA-NOTES.md`; this is the declaration. Companions:
`SCRIPTING-AND-DISTRIBUTED-DOM.md`, `DOCUMENT-LANGUAGE.md`, `DEOS.md`, `LOG-A-HERMES-IN.md`
(the live inhabitant), `DREGG-MUD.md`, `WEB-DEOS.md`.*

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
  the *same* world paints through many glasses — the Rust cockpit, a browser tab, a Discord
  embed, a terminal, an seL4 framebuffer, an Android emulator — same sovereign substance,
  different glass. The interface stops being "the app" and becomes one face among many.
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
  receipt. (`metatheory/Dregg2/Deos/Affordance.lean`, `deos-reflect/src/affordances.rs`.)
- **A view is a function of state.** `deos.ui.{vstack,row,text,button,input,list,table,bind}`
  builds a serializable view-tree that `deos-view` renders to real widgets; a `bind` re-reads
  off the live ledger; the fine-grained dirty-set wakes only the touched node. (`deos-view`,
  `deos-js/signals`.)
- **A document is patchable, transcludable, mergeable.** The dregg-doc patch-core: edits are
  patches with blame, a transclusion is a receipt-pinned live quote that *cannot rot* and that a
  forged citation is *inexpressible* against, a merge is a pushout and a conflict is a
  first-class `ConflictRegion` (never a silent overwrite). And the document **rides the cell
  substrate**: a doc commits via the production sorted-Poseidon2 heap root (`dregg-doc`
  `substrate` feature), a document edit runs through the genuine `TurnExecutor` (cap-gated,
  finalized, journaled — `executor_drive.rs`), and a reopened doc re-seeds from the committed
  umem-heap (`doc_heap.rs`). (`dregg-doc`, `cell_transclusion`.)
- **A moment is forkable + multiplayer.** The fork-membrane: a message is a cap-bounded
  world-fork you drive and stitch back; the real cross-user mint→carry→rehydrate→drive→stitch
  loop runs in one process over a real homeserver. (`shared_fork`, `deos-matrix`.)
- **Everything is moldable + reflective.** Four `present()` faces (RawFields · ocap Graph ·
  DomainVisual · Provenance) with three more lenses composed on top (Affordances · Invariant ·
  Source); the inspector and the custom view share one widget vocabulary — halo any pretty card
  down to its sovereign substance. (`deos-reflect`, `presentable`.)
- **Time is rewindable, and a turn is invertible.** Root-verified replay (`time_travel`,
  `History::replay_to`) makes the local past cryptographically checked; first-class
  reversibility (`turn/src/reversible.rs`, three-tier `Inversion::{Clean,Contextual,Committed}`,
  `undo_to` fail-closed at committed walls) makes undo a typed operation, not a hope.

## The glasses (one world, many renderers)

The renderer-independence thesis is code, not aspiration. One `ViewNode` IR paints through:

- **The Rust cockpit** (`starbridge-v2`, gpui) — the dev basement, five modes
  (Inhabit/Author/Dev/Inspect/Operate), layout itself a receipted `LayoutCard` cell.
- **A browser tab** (`WEB-DEOS.md`) — the gpui-web cockpit compiles to wasm, paints a real
  frame, drives real turns in-tab; terminal PTY backend wired + proven. The residual is
  per-surface view mounts on the wasm build (terminal grid / editor pane / chat view).
- **A Discord embed** (`deos-view/src/discord.rs`) — the same view-tree as embed+components.
- **A terminal** (`dregg-tui`) — a ratatui light client over the node HTTP API whose Verify tab
  independently checks a real STARK proof; a glass that trusts the proof, not the server.
- **seL4** — a committed turn drives live-repaint of the framebuffer end-to-end
  (`sel4/dregg-firmament/tests/live_repaint_on_turn.rs`, at semihost fidelity).
- **Android** (`android-cell`, `mobile/`) — the verified core runs real turns on the arm64
  emulator; seven Android-authority gates prototype the cap-confined APK-as-cell; the painted
  gpui frame on real hardware is the named wall (`MOBILE-DEOS.md`).
- **The real Zed** (`deos-zed-full`) — the upstream editor/workspace stack mounted over a
  cell-ledger `FirmamentZedFs`, a recon spike for editor-as-glass.

## The authoring layer (the epoch, built)

The substrate was the loom; the authoring layer is the world becoming editable *from within*. Its
unifying law: **every authoring gesture is an affordance, every affordance is a turn, every turn
is a receipt** — so the whole authoring surface is one machinery pointed at the cells' own
schemas. The keystone and its eight specializations all run:

- **Card editor** (the root, `deos-js/src/card_editor.rs`) — edit a card's view / fields /
  affordances from within, each a receipted patch with blame; the edited card re-renders to real
  pixels. Inspection becomes authoring.
- **Stitcher** — a merge conflict rendered as two live alternatives; resolve by a verified patch.
- **Provenance navigator** — a cell's receipt-chain walkable: lineage, turn-detail, go-to-that-point.
- **Fork / consent** — the membrane's tiers made visible; a consent inbox of pending turns; upgrade requests.
- **Document composer** — compose a doc from cells (embed / reorder / re-role as turns).
- **Desktop authoring** — the desktop layout itself a witnessed, rewindable cell.
- **`dregg://` link-paste** — select a cell → a URI → paste a live provenanced transclusion.
- **Multi-cell agent turns** — author a story spanning cells, cap-confined across vessels.
- **Chat-as-a-card** — a room is a cell, a message is a turn, send is an affordance.

Beyond the nine, the reflective-card family keeps growing — agent / graph / inspector / objects /
organs / proofs / dynamics / home / links / layout cards all mount in the live cockpit through the
same card-surface bridge — and the agent's own authoring tools (`deos-hermes/src/card_authoring.rs`)
speak the same gesture grammar, cap-gated at the same tooth.

## The inhabitant (the soul in the vessel)

An agent put into deos is not a tool calling an API; it **inhabits** the world. It can:

- **see** — the cap-bounded reflective crawl: the whole image legible within its authority, a
  leaf with no caps observes only itself (`deos-reflect/tests/reflective_crawl.rs`).
- **drive** — `run_js` attached to the *live* cockpit World: a real model has crawled real cells
  and fired receipted verified turns, each fire bounded by `held` (an over-reach refused
  in-band). (`deos-hermes/src/run_js.rs`, `starbridge-v2/src/agent_attach.rs`.)
- **understand** — the dregg source is bundled inside deos as a **read-only capability**: the
  `SourceVessel` (a cap over the bundled source and nothing more — no write authority, `..`
  escapes refused), seedable into the same FirmamentFs namespace the editor uses, edit refused
  in-band. It can read the code of its own world. (`starbridge-v2/src/source_vessel.rs`.)
- **author** — it patches a card's view live, every edit a receipt, through the same card-editor
  keystone a human uses.

**And the polarity is inverted: dregg hosts the agent** (`deos-hermes/src/host.rs`, `DreggHost`).
The brain runs INSIDE a confined firmament PD — file/net/exec and every inherited fd denied by
the OS sandbox (Seatbelt / namespaces+seccomp+landlock), the Endpoint its only channel. This is
not a scripted stand-in: a real brain-driven ACP peer is compiled into the PD body and proven in
the default suite (`tests/brain_in_jail.rs` — jailed multi-step turns, real receipts), and a live
HTTP-LLM brain runs jailed behind the `live-brain` feature, reaching its provider through the
**provider-only egress door** — one granted host:port, sealed by default, enforced on both
platforms (macOS SBPL; Linux seccomp connect-notify where the child's net namespace stays empty,
fail-closed). Its tool source is the **dregg MCP server** (`mcp_server.rs`): exactly `run_js` +
`terminal`, the terminal exec'd inside a *nested* confined PD (ambient-authority attempts
physically denied, confinement verdict `0xf`). Every action is a cap-gated, metered, receipted
turn; 18 adversarial red-team attacks (mandate overrun, amplification, confused deputy, replay,
forgery, sandbox escape, cross-vessel reach) are each a test that runs, every escalation refused
(`AGENT-CONFINEMENT-REDTEAM.md`).

The inhabitant also has an **economy**. `agent-host` binds an SSH pubkey to a cap-account with a
budget and a cap-bundle, dropping a visitor straight into a confined `dregg-agent attach` REPL;
`dregg-agent` is itself a full live-LLM agent with metered, receipted sessions and a
`Local`/`Hosted` posture gate; `agent-platform` rents/hosts/meters/reaps confined agent grains
with third-party-verifiable guarantees; and `grain-turn` seals every admitted agent action to a
genuine committed executor turn — the agent's receipt is a typed *view over a real kernel
transition*, never a parallel ledger.

## The five holy grails — newly possible on dregg

What no prior system could reach, because none had the spine:

1. **Unforgeable, never-rotting transclusion** — Nelson's docuverse, shipped.
2. **AI-authored software bounded by capabilities it provably cannot exceed** — safe generative authoring.
3. **Multiplayer as cap-bounded world-forks that stitch by pushout** — zero-loss merge, conflicts as objects.
4. **Verified time-travel** — the past is the *same* past for everyone, cryptographically.
5. **The sovereign live image** — Pharo-moldable, simultaneously secure, verified, provenanced, distributed.

## One word, two things (read before grepping)

Four name-collisions that confuse orientation; the docs use all of them:

- **membrane** — (a) the *ocap forwarder* `{A∧B}⊒C` (`cell/src/membrane.rs`, composes authority
  upward, non-amp proven at the executor rung); (b) the *fork-membrane* (`shared_fork.rs`
  `MembraneFrustum` / `deos-matrix` `MembraneEnvelope`, a carried world-fork). Unrelated mechanisms.
- **stitch** — (a) the Lean-mirroring two-turn *control model* (`branch_stitch.rs`, cell-granular
  `DocGraph`); (b) the *production* per-address umem stitch (`umem_membrane.rs::stitch_projections`
  / `settle_umem_stitch`, what `stitch_pair` and `grain-fork` actually run).
- **gadget** — (a) the guest rolodex's launcher card (`guest.rs::Gadget`); (b) the moldable
  validate→predict→commit turn-gadget spine (`turn_builder.rs::CommittingTurnGadget` et al.).
- **MCP server** — (a) `dregg-mcp` (`starbridge-v2/src/bin/dregg_mcp.rs`, drives the live cockpit
  image, registered as `dregg-image`); (b) `deos-hermes mcp-server` (the confined tool-source a
  jailed model calls). Different object models; a unification lane is named below.

## Honest state — built vs prototype vs frontier

- **Built + proven (runs):** cells · caps · turns · receipts · transclusion · reversible turns
  (M-REV-0) · deos-js · deos-view (four renderer backends) · dregg-doc **including the substrate
  ride** (heap-root commit, executor-driven edits, doc-rides-the-umem-heap) · run_js on the live
  World · the moldable inspector · the card-editor keystone + the 8 authoring surfaces + the
  reflective-card family · the source-vessel · **the brain-in-jail** (real ACP brain in the
  confined PD, live-LLM variant over the provider door) · the dregg MCP tool-source · the agent
  red-team (18/18 refused) · the hosted-agent economy (agent-host / dregg-agent /
  agent-platform / grain-turn R2) · **the MUD first slice** (rooms/items/locked doors as cells
  and caps, `starbridge-v2/src/mud.rs` + the gpui-free `deos-js/src/mud.rs`, real proving in the
  test suite) · **the gadget rolodex** (guest desktop over the 19-app registry) · **co-driven
  multiplayer cards** (fork→envelope→rehydrate→stitch across a membrane boundary, both
  principals' edits survive — `distributed_card.rs` + the runnable branch-stitch-multiplayer
  app) · graduated consent (3-tier, fail-closed compulsion gate) · verified local time-travel.
- **Executor-real, not yet circuit-bound (the one honest shelf):** the fork/stitch settlement
  gate is Lean-proven twice (abstract `settlement_soundness` + circuit-side
  `finalized_commit_binds_revoked`, both sorry-free) and the session machinery runs — but the
  deployed rest-hash does not yet absorb the revocation-registry root, so a pure light client
  cannot witness a stitch's authority drop. The residual is named IN the Lean
  (`Dregg2/Circuit/SettlementSoundness.lean` — a Rust circuit-emit conformance obligation) and
  rides the gated VK epoch. Same shelf: the ocap-membrane's composition tooth (`exposed ⊑ a∧b`
  in-circuit) and its turn-executor routing.
- **Fidelity seams (named, each with its wire):** the MCP world-bridge is BUILT — bridged
  `run_js` lands on a served live World over a fail-closed socket (`with_world_bridge` +
  `SocketWorldSink`, e2e-proven with a real SpiderMonkey turn); the residue is the cockpit
  boot/frame-loop call that binds the serving side (`serve_world_bridge`/`pump` exist,
  uncalled); tool-*exclusivity* against an unpatched `hermes-acp` is one upstream knob (base
  toolset additive today, every base tool still authority-gated); the jailed live brain is
  proven against a hermetic mock provider — the real-provider run is an env swap; the
  standalone `deos-matrix` chat demo defaults to the mock membrane host unless the real
  `ForkMembraneHost` links; distributed time-travel ("the same past for *everyone*") is
  consensus-modeled, not consensus-wired; gpui-web needs its per-surface view mounts (chat's
  renderer-independent card + cockpit mount now exist — the wasm graph + an opener remain);
  the rolodex's possession partition reads the live c-list, but the cockpit host does not yet
  thread its launched cells + session into the guest surface.
- **Frontier (the genuine roadmap):** cross-**machine** migrate (the rails exist — tear-off,
  HostPd endpoint round-trip, CapTP handoff nonces; missing: `Target`-level Distributed re-home
  + a network transport for the surface cap) · `Target::Mirror` (cap-secure reflection depth) ·
  the two MCP surfaces unified (confined AND live-World — the world-bridge socket now makes
  this reachable) · co-driven cards crossing between two *running* cockpits over Matrix ·
  multi-node MUD presence (presence + "say" are BUILT in-process — a conserved presence token
  gates speech through the Bus's own cap verdict; the wire is deriving the speak cap as an
  attenuation of the on-ledger token, which makes presence provable from any box's ledger) ·
  doc-history compaction (the patch chain now lives IN the cell — reopen reconstructs history,
  tamper-refused; the chain grows per edit, and starbridge's desktop still re-seeds text-only).

## The north star (the self-hosting cure)

The deepest move makes the whole thing self-reinforcing: when dev itself moves **into** dregg —
files are cells, edits are receipted patches — two authors on one artifact produce a
`ConflictRegion` (the stitcher), not a stomp. The loop already closes at first fidelity: the
firmament editor's save is a ledger turn, the terminal's `cargo` runs against the same tree
(`SELF-HOSTING-LOOP.md`), and the source-vessel puts the system's own definition inside the
system, read-only, for any inhabitant to study. The hazards of shared mutable state become
impossible by construction, because the system is built out of the very primitives that solve
them. Hyperdreggmedia authoring dregg, in hyperdreggmedia. That is where this goes: a medium
malleable enough to be its own construction tools, owned and verified all the way down — the
revolution Kay said hadn't happened yet, with the spine it was always missing.
