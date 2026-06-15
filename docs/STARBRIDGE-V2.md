# Starbridge v2 — the dregg master interface

Starbridge v2 is dregg's master interface: a fully native, live, visual
environment for a verified object-capability operating system. It embeds the
real verified executor and runs a live local dregg world in-process — a single
image you can see, inspect, and drive, where every action is a verified turn.

This document explains it from first principles, present tense.

## The thesis: surpassing Smalltalk

Smalltalk gave us the *live image*: one persistent world where everything is a
live, inspectable, modifiable object, and the tools are themselves objects in
that same world. Starbridge v2 keeps that — every cell, capability, receipt, and
the image itself is a live `Inspectable` object behind one uniform interface —
and surpasses it on the four axes Smalltalk's image lacked, each made visible
and live in the cockpit:

1. **ocap security.** Objects are capability-secured cells; there is no ambient
   authority. Every action is gated by a held capability and by the target
   cell's permissions. The cockpit shows the capability graph as first-class,
   and an over-grant is *rejected by the real executor* — the no-amplification
   guarantee fires in front of you.
2. **formal verification.** Messages are verified turns carrying guarantees
   (value conservation, no capability amplification, receipt-chain integrity).
   The same verified executor that the federation runs as its authoritative
   state producer runs *here, in this process*. A turn that would violate a
   guarantee does not commit.
3. **provenance.** Every committed turn leaves a `TurnReceipt`. The receipt chain
   is a first-class, navigable causal history — the local blocklace — that you
   browse and time-travel through.
4. **distribution.** The image is a cryptographically-committed verified state
   (`state_root()`), one of a federation of sovereign images. The cockpit
   presents the image's commitment and (as the federation lane lands) its place
   among peers.

The bumper-sticker: *a live image where every object is capability-secured,
every message is a verified turn, every turn leaves a receipt, and the whole
image is a cryptographic commitment among sovereigns.*

## Two builds, one codebase

Starbridge v2 mirrors the `verifier/` `no-lean-link` pattern: one codebase, two
builds selected by feature.

### `native-full` (default) — the master interface

```
cd starbridge-v2 && cargo build
```

Build *from inside* `starbridge-v2/` — not `--manifest-path` from the repo root.
`rust-toolchain.toml` is directory-scoped: this crate pins the rolling `nightly`
because gpui needs `std::hint::cold_path`, which stabilized after the repo root's
`nightly-2026-01-01`. Building from the root selects that older toolchain and
fails to compile gpui with E0658 (`cold_path` unstable). If the rolling nightly
is itself stale, `rustup update nightly` refreshes it — this affects only this
standalone crate (the root + every other lane pin a dated nightly).

The headline build. It **embeds the real verified executor** and runs a live
local dregg world natively:

- The engine is `dregg_turn::executor::TurnExecutor` over a `dregg_cell::Ledger`
  — the exact pair the SDK's `DreggEngine` (`sdk/src/embed.rs`) wraps and that
  THE SWAP makes the federation's authoritative producer. Turns run *locally,
  in-process*; nothing is phoned to a remote node.
- This links the verified Lean archive (`libdregg_lean.a`, multi-MB). That is
  completely fine for a native desktop application — it is the very thing the
  `no-lean-link` crates exist to *avoid*, and exactly what the master interface
  *wants*.
- It renders with gpui (Zed's GPU UI framework). The whole cockpit is the
  visual layer over the embedded world.

**Run the cockpit in `--release`.** Use the Makefile target:

```
cd starbridge-v2 && make run-cockpit          # builds + runs the window in release
```

(equivalently `cd starbridge-v2 && cargo run --release`). The embedded verified
executor is the same code the federation runs as its producer — real conservation
proofs, real ocap checks, real caveat crypto — and in a **debug** build those
turn paths are *pathologically slow* and pin the CPU (exactly the reason `cargo
test` is run in release; see *Tests* below). A debug cockpit grinds; a release
cockpit is snappy. The window itself **opens instantly in either profile** — see
*The landing*: it paints on the at-rest genesis image and seeds the demo turns in
*after* first paint — but every demo/verb turn you then drive runs through the
executor, so release is what keeps those interactions fast.

### `sel4-thin` — the eventual seL4 component

```
cd starbridge-v2 && cargo build --no-default-features --features sel4-thin
```

The Lean-free, gpui-free thin path for the eventual seL4 protection-domain
component (see `docs/SEL4-EMBEDDING.md`, owned by a separate lane). It compiles
*without* the embedded executor and *without* the heavy native UI stack: it
speaks the node's HTTP+SSE wire contract (`src/client.rs` + `src/model.rs`)
against a remote node. The built binary links **zero** Lean symbols and **zero**
Metal/gpui — a clean reads-bytes → verify shape.

The `NodeClient::{Mock,Http}` wire surface is the seed of a native
remote-federation panel too (a designed-pending lane): the master interface can
*additionally* connect to remote nodes/federations, but its headline capability
is the embedded local world.

## Architecture

The headless heart is gpui-free and `cargo test`-able; the visual layer renders
it. The split:

```
starbridge_v2 (lib, feature embedded-executor)
├── world      — World: the embedded executor + live ledger + provenance log.
│               THE COMMIT PATH (`World::commit_turn`) runs the REAL executor.
├── dynamics   — Dynamics: an append-only observation stream of state
│               transitions (cell born, cap granted, turn committed, balance
│               flowed) the visual layer renders. Decoupled from gpui.
├── reflect    — the reflective object model: cell / receipt / image projected
│               into one uniform `Inspectable` (typed Field tree) every view
│               consumes. Reads the live protocol types — never a parallel wire
│               schema — so it cannot drift from what the executor holds.
├── surface    — Surface + SurfaceCapability: a cap-confined cell view
│               (apps-as-cells). A surface is OWNED via an unforgeable cap and
│               re-reads the live ledger — no mock surfaces. gpui-free, testable.
├── shell      — Shell: the cap-first window manager + compositor. Every window
│               op (focus/raise/move/resize/minimize/close) is GATED by the
│               surface's cap; `compose(world)` builds the Scene (z-ordered paint
│               list) with shell-drawn anti-spoof identity chrome. gpui-free.
├── graph      — OcapGraph: the whole-graph ocap delegation layout. Nodes =
│               cells, edges = capability grants; MULTI-HOP reachability (the BFS
│               transitive closure — a cell's blast radius) + a layered
│               delegation-depth layout rooted on any cell. The View tree IS the
│               ocap graph. gpui-free, testable.
├── organs     — OrganSurvey: reflects each organ's LIVE cell-state. Trustline +
│               flash-well positions are decoded from the embedded ledger's state
│               slots (embed-core, LIVE); channel/mailbox/court are surfaced
│               honestly as remote-path (need `captp`). gpui-free, testable.
├── organ_ops  — OrganDriver: the organ OPERATING verbs (open / draw / repay /
│               settle / close) — DRIVES trustline + flash-well organs as REAL
│               turns through the embedded executor (not just reflects them). The
│               REAL `dregg_cell::blueprint` per-organ program is installed on the
│               cell, so an invariant-violating op (over-line draw · fee-evading
│               borrow · touch on a closed organ) is refused IN-PROTOCOL by the
│               executor's predicate gate, not faked. gpui-free, testable.
├── proofs     — ProofBoard: the proof-attach + STARK verification-status view.
│               Each committed turn's tier (verified-by-construction / executor-
│               signed / STARK-attached) + the honest route to the next tier.
│               gpui-free, testable.
├── swarm      — Swarm: the A2 multi-agent coordinator. Async notify edge
│               (EmitEvent→NotifyEdge→drain) + atomic multi-effect bundles
│               (`run_atomic`, all-or-nothing) + per-member cap-confined surfaces
│               (`bind_surface`, each pane a real firmament cap) + the verified
│               shared budget (`attach_stingray_budget`, below). gpui-free.
├── swarm_budget — StingraySwarmBudget: the swarm's VERIFIED shared budget — a real
│               `dregg_coord::StingrayCounter` (the single-image shared pool) wired
│               the way the SDK's `runtime::set_budget_gate` attaches a BudgetSlice.
│               Every dispatch draws against the ONE pool; a draw past the ceiling
│               is refused by the counter's gate (not a summation), and total_drawn
│               CONSERVES (== Σ metered across members), PROVABLY ≤ B. gpui-free.
├── agent      — AgentActivity/AgentSurface: one agent loop's provable activity
│               (mandate · cap-gated turns + receipts · authorization boundary).
├── affordance — the native deos AFFORDANCE surface (htmx-on-crack, the seam CLOSED).
│               A cell publishes named effect-TEMPLATES (`CellAffordance`, a real
│               `Effect` + the `AuthRequired` a viewer must hold); `project_for`
│               is per-viewer progressive ATTENUATION (the REAL `is_attenuation`,
│               `required ⊆ held`); `fire` → `AffordanceIntent` (anti-ghost) →
│               `fire_through_world` hands the effect to `World::commit_turn` so the
│               receipt is the EXECUTOR's own (the seam `starbridge-web-surface` could
│               only model is CLOSED because this process embeds the executor). The
│               gating window cap IS a firmament `Capability{Surface(cell)}`. Plus the
│               FRUSTUM-SNAPSHOT (`AffordanceSnapshot` + `rehydrate_for`): a tiny
│               snapshot (cell + names, not data) that re-expands PER-VIEWER through
│               the same attenuation gate — the deos rehydration thesis. gpui-free.
├── powerbox   — the interactive POWERBOX (CapDesk): the trusted designation flow. A
│               confined app-cell REQUESTS a cap it lacks (`CapabilityRequest`, no
│               ambient authority); `Powerbox::present` filters a picker to what the
│               cockpit principal ACTUALLY HOLDS (the principal's live c-list —
│               `mint_needs_held_factory` made visible); the user designates a target +
│               rights; `Powerbox::grant` runs the real `is_attenuation` (non-amp,
│               `gen_conferral_is_attenuation`) then MINTS a fresh attenuated
│               `CapabilityRef` into the app's c-list via a REAL `Effect::GrantCapability`
│               through `World::commit_turn` — the app gets EXACTLY the designated,
│               attenuated cap, the executor is the no-amplification backstop. gpui-free.
├── model      — the node's wire types (`/status`, `/api/cells`, `/api/events/stream`
│               receipt events, the `/turn/submit` request). Pure serde; single-sourced
│               in the library so the live-node panel + the thin client share one mirror.
├── client     — the wire `NodeClient::{Mock,Http}` + `LiveNode` (the live connection
│               driver: `sync` snapshot reads + `connect_stream`, the background SSE
│               reader feeding the pure parser onto an mpsc channel). The reqwest
│               byte-pull is `live-node`-gated; the Mock backend is always available.
└── live_node  — the LIVE node connection's PURE heart (gpui-free, `cargo test`-able):
                `SseParser` (the `text/event-stream` decoder, fixture-tested),
                `LiveReflection` (remote wire snapshots → the SAME `reflect::Inspectable`
                the embedded world uses), `ReceiptFeed` (the cursor + bounded ring + the
                resume model the cockpit drains under `cx.notify()` — REPLACING the
                snapshot). Only the byte source is `live-node`-gated.

starbridge-v2 (bin)
├── cockpit    — the gpui cockpit (feature gpui-ui): the comprehensive panels
│               (cell world · inspector · blocklace · composer · objects ·
│               dynamics) plus the workspace tabs (SHELL · agent · swarm · GRAPH ·
│               ORGANS · PROOFS · WEB-OF-CELLS · POWERBOX · buffer · terminal ·
│               composer · objects · debugger · replay · cipherclerk · editor), rendering
│               `World` directly. The SHELL tab renders the cap-first compositor
│               scene (surfaces over real cells); the OBJECTS tab projects proofs /
│               nullifiers / cell lifecycle through `reflect`; the GRAPH tab draws
│               the ocap delegation graph (multi-hop); the ORGANS tab reflects
│               live organ cell-state; the PROOFS tab shows the verification-tier
│               board; the WEB-OF-CELLS tab BROWSES the live image as the `dregg://`
│               docuverse (see §"The web-of-cells browser" below). A ⌘K COMMAND
│               PALETTE (`palette`) overlays the whole cockpit: one
│               fuzzy-searchable surface over EVERY action.
└── palette    — the ⌘K command registry + fuzzy matcher + selection model
                (gpui-free, testable). Every cockpit action is one `CommandId`;
                the cockpit dispatches a selected command through the SAME
                `&mut Cockpit` verb the buttons call — no parallel action path.
└── views      — shared gpui palette/primitives.

(`client` + `model` + `live_node` + `affordance` moved into the LIBRARY — see the
lib block above — so the embedded master interface's live-node panel + the deos
affordance surface reuse them, not just the thin bin; the bin re-exports `client`
for the `sel4-thin` `thin_report`.)
```

### The commit path is the whole story

Every state transition flows through `World::commit_turn(turn)`, which:

1. threads the per-agent receipt-chain head the executor enforces,
2. runs `TurnExecutor::execute(&turn, &mut ledger)` — the real verified
   semantics,
3. on commit: records the new chain head, advances the height, appends the
   `TurnReceipt` to the provenance log, and emits the dynamics events for the
   transition,
4. on rejection: surfaces the executor's reason (this is a *feature* — it is the
   ocap/verification guarantees firing).

A rejection is not an error path to hide; it is the cockpit's most important
teaching moment. The "⚠ over-grant" verb exists precisely to make you watch the
no-amplification guarantee reject an illegitimate capability grant.

## The shell — a cap-first multi-surface desktop (the native pillar)

The master interface is not one monolithic panel: it is a **cap-first
multi-surface desktop shell**, the native pillar of the dregg desktop-OS vision.
The same object-capability discipline that gates every *turn* gates every
*window op*. Three modules carry it (the first two gpui-free + `cargo test`-able;
the third is the gpui SHELL tab):

```
surface  (src/surface.rs)  — Surface: a cap-confined cell view (apps-as-cells)
shell    (src/shell.rs)    — Shell: the cap-first window manager + compositor
cockpit SHELL tab          — the visible compositor over the live world
```

### Surfaces are cap-confined cell views (apps-as-cells)

Every dregg CELL can be opened as its own **surface** (a window). A surface is
not a free-floating widget — it is *owned* via an unforgeable
[`SurfaceCapability`], and only the cap-holder may render or drive it. A surface
holds **no copy** of its cell's state: it holds the cell's `CellId` and re-reads
the live ledger when it composes, so it cannot drift from what the executor
holds. There are **no mock surfaces** — every surface body is the real cell's
live state (balance / nonce / caps / lifecycle), and it reacts to real turns
(seal the backing cell through the executor and the surface follows).

### The window manager is cap-first

`Shell` is a window manager where **there is no ambient authority over a
window.** Every op — focus, raise, move, resize, minimize, close — is GATED by
the surface's capability:

- A `SurfaceCapability` names *exactly one* surface and carries a `secret` the
  shell drew at mint time. Authority over a surface is exactly the set of held
  caps; it is obtained only by being *granted* one (the shell hands it back when
  the surface opens) — **never** by naming the surface. Knowing a `SurfaceId` is
  not enough: a forged cap (right id, guessed secret) is *refused on every op*.
  This is the window-manager analogue of the executor's no-amplification rule.
- A refusal is a **feature**, surfaced the same way the executor's turn
  rejections are (the outcome banner colors it red). Trying to act on a surface
  with no held cap is refused — that *is* the no-ambient-authority property.
- The **console** (the cockpit's own surface) is a privileged trusted root: it
  is cap-owned like any surface, but it is *protected from close* (closing it
  would orphan the shell), and it is labelled `SYSTEM`, never a spoofable cell
  identity.

In the cockpit, the operator holds every surface's cap in a vault — but every op
still *presents* the held cap to the shell's gated API, so the discipline is
**demonstrated, not bypassed.** Clicking a surface is only a *hint*; the cap-gated
`focus` is the actual authority.

### The trusted-path framing is anti-spoof

Each surface draws its own *title*, but its **identity badge** — the owning cell
id (abbreviated) plus its lifecycle (`live` / `sealed` / `destroyed` /
`migrated` / `archived`, or `missing`) — is drawn by the **shell** from the live
ledger, never from the surface's self-description. So a surface **cannot
impersonate another cell's identity**: the identity chrome is the shell's,
attested from the ledger. A surface whose backing cell is not in the ledger is
shown as `UNBACKED (cell missing)` — it can't masquerade as live.

### The compositor

`Shell::compose(world)` is the compositor: it turns the owned-surface set + the
live ledger into a [`Scene`] — an ordered (back-to-front) paint list, each item
carrying its surface, its shell-derived identity label, and its focus state. The
SHELL tab renders that scene as a stack of windows (front-most first), each with
a title bar (identity badge · title · z-order · focus · cap chrome) and a body of
real cell state. Three layouts arrange the non-console surfaces — **float** (free
placement; move/resize honored), **tile** (a near-square grid of the work area),
and **stack** (a centered cascade) — all painted in z-order, cycled with one
toolbar button or the ⌘K palette.

The SHELL boots ready (the console plus the three anchor cells — treasury ·
user · service — already open as cap-confined surfaces over the real world) and
is one click away. The cockpit's **boot view** is the HOME landing portal below.

## The web-of-cells browser — browsing the dregg:// docuverse (the native-browser pillar)

The SHELL is the native window-manager pillar; the **WEB-OF-CELLS** tab
(`src/web_cells.rs` + the cockpit's `web_of_cells_panel`) is the native-*browser*
pillar. It fuses the cockpit with the `starbridge-web-surface` crate — the **web
of cells** — so the live verified image is also a browser of the `dregg://`
docuverse. It names + USES the real web-of-cells components (it reinvents none):

- **A `dregg://` link is a capability into a cell; fetching it is a verified,
  attested cross-cell read.** The panel publishes each live `World` cell as a
  `dregg://` page through the real `starbridge_web_surface::WebOfCells` and
  fetches it back: each row carries a real `AttestedResource` (content-addressed +
  receipt-in-stream + a quorum-signed `AttestedRoot`, checked by the genuine
  `AttestedResource::verify`) and a real `OriginChrome` — the **trusted-path
  origin badge drawn from the LEDGER**, never the page (the structural answer to
  browser-chrome phishing).
- **Opening a cell shows its per-viewer affordance surface (progressive
  attenuation).** The surface is the genuine `web_surface::AffordanceSurface`;
  the rows are `AffordanceSurface::project_for` through a real `SurfaceCapability`
  for the cockpit's identity — so a viewer sees **exactly the affordances its caps
  authorize**, gated by the proven `is_attenuation` lattice. The "view as
  root/editor" toggle makes the property tangible: the editor tier sees view /
  comment / edit (3 of 4); the attenuated-away `admin` (which needs the root tier)
  is absent until you lift the viewer's authority.
- **The rehydration liveness-type is DERIVED, not hand-set.** The opened surface
  arrived via a `dregg://` *attested* fetch (witnessed in the graph), so
  `Rehydration::classify` types its reacquisition `REPLAYED-DETERMINISTIC` — the
  confined "every interaction went through the membrane" kind of true.
- **A transcluded field with provenance.** The opened cell transcludes another
  cell's finalized content commitment, with the source's serve-receipt shown — a
  Ted-Nelson inclusion that is *checkable*, not trusted.
- **Firing goes through the REAL embedded executor (the seam the web crate could
  only model is CLOSED here).** An affordance the web-surface surface projects
  carries the SAME real `dregg_turn::Effect` the cockpit's
  `affordance::AffordanceIntent::fire_through_world` runs; `WebCellsBrowser::fire_affordance`
  lifts it across that one-type bridge and commits it as a verified turn through
  the live `World`. The cap-gate that decides whether the affordance may fire AT
  ALL is the real `is_attenuation` (an unauthorized fire is refused **in-band**,
  the anti-ghost tooth); the gate that decides whether the resulting turn commits
  is the real executor (a guarantee firing is surfaced, never hidden). Neither is
  faked.

`src/web_cells.rs` is the panel's pure, gpui-free **text MODEL** (like
`landing.rs`): the cockpit renders exactly its rows, so the `cargo test` that
asserts they are real + attested + cap-projected proves the rendered tree browses
the real web of cells without a GPU.

### The servo layer — the named next increment

The web-of-cells browser renders affordance **surfaces** natively today. Embedding
**servo** to render actual `dregg://` web *content* — the `WebViewDelegate`
cap-gate, where the `starbridge-web-surface` crate's `MockSurface` stands (the
LIBSERVO SEAM in `web-surface/src/delegate.rs`) — is the **named next layer**: the
servo Stage-A renderer lane. The browser states this in the panel itself
(`WebCellsBrowser::servo_layer_note`), so the boundary between *what is integrated*
(the shell browses the web of cells natively) and *what is named-next* (servo
content render) is visible, not buried. A second named increment is the
**verified-transclusion affordance**: hardening the Ted-Nelson inclusion into an
in-circuit cross-cell observation via the protocol's `ObservedFieldEquals`
predicate (which lives below the web-surface crate's public API in
`dregg_cell::predicate`).

## The powerbox — CapDesk, the trusted designation flow (the ocap grant ceremony)

An object-capability system has **no ambient authority**: a confined app-cell holds
exactly the capabilities in its c-list and *cannot name a peer or resource it was
never granted*. So how does a user hand a freshly-launched app the authority to touch
one specific file / peer / cell — without that app getting the power to enumerate or
reach anything else? The **powerbox** (CapDesk — the "open-file dialog *as the grant
ceremony*"), the POWERBOX tab (`src/powerbox.rs` + the cockpit's `powerbox_panel`):

1. the app **requests** a capability it lacks (it holds no power to obtain it — it can
   only *ask*; it does not even get to see whether the user holds the target);
2. the **trusted UI** — the cockpit, the system's own principal, **not** the app —
   presents a **picker of the things the USER actually holds** (filtered from the
   principal's live c-list: a target the user cannot reach simply *is not in the
   picker*);
3. the user **designates** one target + the rights to confer;
4. the powerbox **mints a fresh, attenuated capability into the app's c-list via a
   real grant turn** (`Powerbox::grant` → a genuine `Effect::GrantCapability` through
   `World::commit_turn`), handing back **exactly** that one designated, attenuated cap.

The app never sees the namespace; it gets precisely what the user pointed at, narrowed.
The flow reinvents none of the machinery — it is the user-facing surface over facts the
metatheory already **proves**:

- **The trusted UI holds no ambient authority of its own** — it grants ONLY from the
  cockpit principal's own held caps (exactly the `starbridge_web_surface::delegate`
  thesis: "the delegate callback is the powerbox; holds no ambient authority").
- **You cannot grant what you do not hold** — the proven `mint_needs_held_factory`
  (`Dregg2/Spec/Authority.lean`: "minting needs a held factory cap; the powerbox is
  not ambient"). The picker IS that fact made visible, and the real executor is the
  backstop: a grant from a principal that holds nothing is **rejected by the
  executor** (the same gate `world::over_grant_is_rejected` exercises), never by the
  UI.
- **The grant is strictly attenuating** — the conferred rights are `≤` the held rights
  (the proven `gen_conferral_is_attenuation`). `Powerbox::grant` runs the genuine
  `dregg_cell::is_attenuation` (`granted ⊆ held`) *before* it builds a turn, so a
  request to confer MORE than the user holds is denied in-band (the anti-ghost tooth),
  and the executor's no-amplification rule is the second gate.

`src/powerbox.rs` is the panel's pure, gpui-free **flow MODEL** (like `web_cells.rs` /
`landing.rs`): the cockpit renders exactly its rows (`Powerbox::all_text`), so the
`cargo test` proves the flow without a GPU — the picker shows only held targets; an
empty-c-list principal presents an empty powerbox; designating a held target mints a
real attenuated cap (a real receipt); the app cannot obtain a target the user does not
hold (denied, no turn); the powerbox refuses to amplify past the held ceiling; and the
executor is the backstop even if a UI bug let a designation through.

### Semi-reinteractive transclusion — powerbox × transclusion

The web-of-cells **transclusion** (above) is **read-only**: the verified cross-cell
finalized READ is *free* (a quote is a read, never a key — `TranscludedField::project_for`
hands a viewer at most their own held authority, the membrane non-amp). **Semi-
reinteractive transclusion** (`SemiReinteractiveTransclusion` in `src/web_cells.rs`)
lifts exactly one rung higher, and ONLY through the powerbox: if the user designates
it, the quote carries an **attenuated affordance capability** — the host document can
*fire one of the source's affordances* (attenuated to what the user conferred), not
merely read it. The read stays the free verified observation; the *interact* is a
powerbox-mediated attenuated grant (`upgrade_transclusion_via_powerbox` → a real
`Powerbox::grant` minting a cap reaching the source into the host's c-list). So a plain
transclusion fires nothing; a powerbox-upgraded one fires **exactly** the granted
(attenuated) affordance and no more — a wider affordance than was conferred is refused
in-band by the same real `is_attenuation` the affordance surface gates on. Proven
gpui-free: a plain transclusion is read-only; an upgraded one fires the granted
affordance through the embedded executor (a verified turn) and refuses the wider one;
and the powerbox refuses to upgrade a quote the user lacks source authority over.

## The landing — the warm front door (the boot view)

The first thing the master interface shows is not a sparse window-manager scene:
it is the **HOME landing portal** (`src/landing.rs` + the cockpit's HOME tab) — a
warm, text-rich greeting that names the running system *reflectively*. The feel
is deliberate: loading AOL as a seven-year-old, except this is the Good
Cyberpunk Timeline — a Smalltalk-tier system that is reflectively present to
itself.

The portal is a pure, gpui-free **text model** ([`landing::LandingPortal`])
projected from the LIVE `World` and rendered by the HOME tab as native gpui text:
a big greeting, then titled cards that say where you are, the image *right now*
(its real cell/receipt/value/commitment numbers), the verified heart (named:
`dregg_turn::executor::TurnExecutor`), the receipt nervous system, the organs
(surveyed through [`organs::OrganSurvey`] — live trustlines/flash-wells plus the
catalogued remote-path channel/mailbox/court), and how to begin (⌘K · click a
cell). Because the *content* is built gpui-free, it is `cargo test`-able: tests
assert the portal speaks real, non-empty text about the real image, names the
real executor, reports the live cell count, and *changes after a real turn* — so
"the landing renders abundant real text" is proven without a GPU. On boot the
binary also prints a one-line receipt (`HOME portal: N lines of real text
render …`) so a blank-looking window is immediately diagnosable as a
render/display issue, never an empty UI.

### The window opens INSTANTLY — the demo seeds in live (the AOL-WOW)

The window **opens on the at-rest genesis image** and paints sub-second; the demo
provenance fills in *after* first paint. `main()` builds the cockpit off
[`world::demo_genesis`] — the four cells (treasury · service · user · issuer
well) installed via the *genesis path*, which bypasses the executor, so **no turn
runs before the window is up**. The five demo seed turns (the treasury/user/
service flows, the ocap re-grant, a field write) are then driven *one at a time*
from a foreground gpui async task ([`Cockpit::seed_next_demo_turn`], spawned in
`run_window` after `open_window`), each committing one real verified turn and
`cx.notify()`-ing, with a short beat between so the new cell/receipt paints before
the next turn runs. The HOME portal's height/receipt numbers visibly climb as the
seeding completes; the landing greets you the entire time. This is the difference
between *staring at nothing for seconds while `main()` grinds five executor turns*
and *the cockpit being there immediately, populating live*. The seeded content is
identical — `demo_world` (the `--headless` / `cargo test` path) still runs the
exact same five turns eagerly; only the **window** moves them off the paint path.

Likewise the SWARM tab's **killer demo** (a metered world + factory deploy + the
slow proof-bearing mint/notify/refusal turns) boots **lazily** — on the first
navigation to SWARM, never at window-open — so it too stays off the first frame.

## The window (the Metal path)

gpui renders through Metal on macOS. By default its `gpui_macos` backend
compiles its shaders **at build time** with `xcrun metal` — which needs the
offline *Metal Toolchain* component. On a host whose Metal Toolchain download is
blocked or damaged (`xcodebuild -downloadComponent MetalToolchain` failing on a
broken `DVTDownloads.framework`), that build step fails and no window can open.

Starbridge v2 sidesteps this entirely by enabling gpui's **`runtime_shaders`**
feature (`gpui_platform/runtime_shaders`, wired through this crate's `gpui-ui`
feature). With it, the backend ships the `.metal` *source* and compiles it **at
runtime** via the system Metal framework (`MTLDevice::newLibraryWithSource`) —
no offline toolchain involved. This is the difference between a window that
opens and a build that fails, and it is load-bearing on exactly the kind of host
the prior scaffold stalled on. The window opens; the embedded `Metal.framework`
device is live; runtime shader compilation succeeds.

A `--headless` flag runs the embedded world's self-check (cells, provenance
chain, dynamics) with no window — CI-friendly, and the graceful fallback on a
host with no display.

## Comprehensive coverage — all data & all actions

The master interface is, by design and increasingly by implementation, a cover
over EVERY dregg datum and EVERY action. The coverage is an honest burn-down:

### Data

| Datum | Status | Where |
| --- | --- | --- |
| surfaces (cap-confined cell views) + the z-ordered compositor scene | **live** | `surface`, `shell::Shell::compose`, SHELL tab |
| cells (id/balance/nonce/caps/program/delegate/mode/lifecycle/epoch) | **live** | `reflect::reflect_cell` |
| cell state fields (16 slots) | **live** | inspector `state[i]` rows |
| capabilities + the ocap edges | **live** | `CapEdge` fields per cap |
| receipts + the receipt chain (provenance) | **live** | `reflect::reflect_receipt`, blocklace panel |
| the image commitment (`state_root`) | **live** | `reflect::reflect_image` |
| the dynamics stream (transitions) | **live** | `dynamics`, the feed |
| cell lifecycle (live / sealed / destroyed / migrated / archived) | **live** | OBJECTS panel lifecycle column, `lifecycle_badge` |
| proofs + verification status (STARK) | **live** | `reflect::reflect_proof_status`, OBJECTS panel; the proof-attach + tier board (`proofs::ProofBoard`, PROOFS panel) |
| nullifiers / consumed one-time authorities | **live** | `reflect::reflect_nullifiers`, OBJECTS panel |
| factories (deployed descriptors) | **live** | `reflect::reflect_factory`; deploy + birth path |
| capability delegation *graph* (multi-hop layout) | **live** | `graph::OcapGraph` (nodes/edges + multi-hop reachability + layered delegation-depth layout), GRAPH panel |
| full delegation epochs / revocation channels | partial | epoch shown (per-cell + on graph edges via `stored_epoch`); channel view pending |
| organs (trustline/flash-well) live cell-state | **live** (embed-core) | `organs::OrganSurvey` (trustline + flash-well positions decoded from live state), ORGANS panel |
| organs (channel/mailbox/court) state | designed-pending | need `captp` (network); surfaced honestly as remote-path (kind · seam · route) in `organs::remote_path_organs`, ORGANS panel |
| intents / obligations | designed-pending | node API mapped; panels pending |
| profiles / identities, producer lean-vs-rust | partial (thin path) | surfaced in the thin client; native badge pending |
| federations + sync state | designed-pending | `state_root` is the local half; peer view pending |

### Actions (verbs)

| Verb | Status | Where |
| --- | --- | --- |
| transfer | **live** (runs the real executor) | `world::transfer`, composer |
| grant capability | **live** | `world::grant_capability`, composer |
| over-grant (rejected) | **live** (guarantee fires) | composer "⚠ over-grant" |
| createCell (conservation-enforced) | **live** | `world::create_cell` |
| set state field | **live** | `world::set_field` |
| emit event | **live** | `world::emit_event` |
| revoke capability | wired (helper) | `world::revoke_capability` |
| seal / unseal | **live** (runs the real executor) | `world::seal` / `world::unseal`, composer "seal a fresh cell" |
| destroy (terminal retirement) | **live** | `world::destroy`, headless test |
| burn (supply reduced, `was_burn` bound) | **live** | `world::burn`, composer "burn 1,000" |
| factory-birth (`CreateCellFromFactory`) | **live** | `world::deploy_factory` + `world::create_cell_from_factory` |
| compose multi-action call forests | **live** | `world::forest_turn` (atomic, one receipt), composer "compose multi-action" |
| swarm: async notify edge (EmitEvent → NotifyEdge → drain) | **live** | `swarm::Swarm::run` / `drain_notify`, SWARM tab |
| swarm: atomic multi-effect turn (coordinator bundles N actions, all-or-nothing) | **live** | `swarm::Swarm::run_atomic` (one receipt for the bundle, bounded by the coordinator's mandate) |
| swarm: per-member cap-confined surface (each pane a real firmament `SurfaceCapability`) | **live** | `swarm::Swarm::bind_surface` (the shell gates every window op on the member's cap) |
| shell window ops (open surface · focus/raise · move/resize · minimize · close), all cap-gated | **live** (the cap guarantee fires) | `shell::Shell`, SHELL tab |
| compositor layout (float · tile · stack) | **live** | `shell::Layout`, SHELL tab "cycle layout" |
| the organ operations (open/draw/repay; create/join/remove; send/drain; evidence) | designed-pending | trustline/flash-well live *state* reflected (ORGANS panel); the operating verbs ride the SDK's `AgentRuntime` (trustline/flashwell in embed-core); channel/mailbox/court need `captp` (remote path) |
| fire a cell affordance (htmx-on-crack, the deos interaction) | **live** (runs the real executor) | `affordance::AffordanceSurface::fire` → `AffordanceIntent::fire_through_world` → `World::commit_turn`; the SEAM is CLOSED (the receipt is the executor's own) |
| powerbox designation (the trusted grant ceremony — mint an attenuated cap into an app) | **live** (runs the real executor) | `powerbox::Powerbox::present` (picker = the user's held caps) → `Powerbox::grant` (real `is_attenuation` non-amp, then `Effect::GrantCapability` through `World::commit_turn`); the executor is the `mint_needs_held_factory` backstop, POWERBOX tab |
| semi-reinteractive transclusion (powerbox-upgraded quote: fire the granted affordance, attenuated) | **live** (runs the real executor) | `web_cells::WebCellsBrowser::upgrade_transclusion_via_powerbox` (a real `Powerbox::grant`) → `fire_transcluded_affordance` (the granted affordance through the executor; a wider one refused in-band) |
| connect to a live node + stream its receipts | **live** (headless heart; gpui strip wired) | `client::LiveNode::sync` (snapshot reflections) + `connect_stream` (SSE `/api/events/stream` → `live_node::SseParser` → `ReceiptFeed`, `cx.notify()` per receipt); `--node <url>` |

> **Lifecycle finding — seal/destroy are recorded, the *verbs* enforce
> terminality, but ordinary effects are not yet gated.** The verified executor
> records the `Sealed` / `Destroyed` lifecycle, and the lifecycle verbs
> themselves enforce their own invariants (unseal of a live cell rejects;
> double-destroy rejects; over-burn rejects). But the executor's apply path does
> not yet consult `CellLifecycle::accepts_effects()` before *non-lifecycle*
> effects, so a sealed/destroyed cell does not currently freeze ordinary effects.
> The cockpit surfaces the lifecycle state honestly (the OBJECTS lifecycle
> column); wiring the effect-freeze gate is an executor lane, not the
> interface's to fake.

The "live" rows all run through the embedded verified executor with real
receipts; the "designed-pending" rows are reachable through the same
`World::turn` / `commit_turn` path (every `Effect` variant is constructible) and
are a UI/affordance burn-down, not a semantics gap.

### The developer experience: cipherclerk + ⌘K (live)

Two DX surfaces are first-class and wired to the real engine, not read-only
demos:

**The cipherclerk surface — real macaroon mint · attenuate · delegate ·
discharge.** The CIPHERCLERK tab drives the REAL `dregg_sdk::AgentCipherclerk`
(no reimplemented crypto) through an action layer (`cipherclerk` module):
`mint` forges a root macaroon on the holder's clerk; `attenuate` confines it
(the narrowing is genuine — the attenuated token carries strictly more caveats);
`delegate` produces a real signed, recipient-targeted `DelegatedToken` envelope
and files it; `discharge` runs the real verify verdict (HMAC chain + caveat
evaluation). Two **real-semantics findings** surfaced and are honored by the
surface:

  1. *The macaroon action vocabulary is the atomic letters `r`/`w`/`c`/`d`/`C`*,
     not English words. `dregg_macaroon::action::Action::parse` decomposes a
     request action into those flags and requires EACH to be allowed — so a
     `"read"`-the-word request parses to `{r,d}` and an `r`-only token DENIES it.
     The discharge surface speaks the atomic letters.
  2. *An attenuated `HeldToken` carries a ZEROED root key* (it dropped the
     forging key), so the **holder cannot self-`verify_token`** a confined token
     — only the **verifying service**, which holds the root key, can discharge
     it. The surface exposes both: a holder-side self-check (`discharge`) for a
     root token, and a service-side `discharge_presented(token, root_key, req)`
     for a presented confined token.

**The ⌘K command palette — one searchable surface over ALL actions.** Press ⌘K
(or Ctrl-K) to open a centered, fuzzy-filtered palette over EVERY action in the
cockpit: the composer verbs, the cipherclerk loop, the workspace navigation, the
replay scrubber (step/genesis/head/fork/clear), the debugger retarget, and the
inspector. The palette is honestly comprehensive because a palette command
carries only a stable `CommandId` that the cockpit dispatches through *the exact
same `&mut Cockpit` method the buttons call* — there is no second action path,
so the palette can never drift from what the cockpit can do.

## Tests

The headless heart is fully `cargo test`-able under just `embedded-executor`
(no gpui, no window):

```
cd starbridge-v2 && cargo test --release --no-default-features --features embedded-executor --lib
```

> **Run the suite in `--release`.** The tests exercise the embedded VERIFIED
> executor (the linked Lean archive) and the cipherclerk's real macaroon HMAC /
> caveat crypto. In a debug build those paths are pathologically slow and pin the
> CPU; `--release` makes the suite run in seconds. (Plain `cargo test` without
> `--release` is correct but unbearably slow — prefer release for any iteration.)

The headless tests (green) cover: transfer commits + conserves; **overspend
rejected**; **over-grant rejected** (no-amplification); legitimate grant grows
the ocap graph; createCell grows the ledger under conservation; setField writes
state; emit-event commits; the receipt chain links across turns; the image
commitment moves with history; the dynamics stream observes transitions; the
reflective model projects cells, receipts, the image, **proof/STARK status,
factories, and nullifiers**; the demo world boots with real provenance;
**seal/unseal round-trip the lifecycle, destroy retires a cell terminally, burn
reduces supply (and over-burn rejects), factory-birth installs a child through
the registry (and an unregistered factory rejects), and a multi-action
call-forest commits atomically (all-or-nothing)**.

The DX surfaces are tested too: the **cipherclerk action layer** (mint forges a
real root; attenuate genuinely narrows; delegate files a real recipient
envelope; **discharge runs the real verify verdict** — a service-confined token
authorizes its own service/action and DENIES a wider action, a different
service, or an expired request; the full mint→attenuate→delegate→discharge loop)
and the **⌘K palette** (the registry covers the whole action surface — including
the shell ops; the fuzzy matcher prefers word-starts + contiguous runs; search
finds commands by title AND by keyword concept; the open/type/select/accept
interaction model).

The **cap-first shell / compositor** is tested as its own headless model: a
rect's contain/translate-clamp; a capability names exactly one surface; opening
a surface mints an authorizing cap (over a real ledger cell); **a forged cap is
refused on every op** (the ocap heart — knowing the `SurfaceId` is not enough);
focus raises to the front of the z-order; closing a surface kills its cap; **the
console is protected from close** (even with its real cap); move is cap-gated and
honored under float; **the trusted-path identity badge tracks the live cell
lifecycle** (seal the backing cell through the verified executor and the badge
follows from `live` → `sealed`); **a dangling surface is labelled `missing`, not
spoofable**; the compositor tiles + stacks the non-console surfaces in-bounds;
minimize drops focus to the front and restore refocuses; hit-test finds the
front surface under a point; and the layout cycles float → tile → stack.

## Status

GREEN on the thesis "the master interface is real and growing": the embedded
verified executor runs a live local world, the four axes are all live in the
engine, the headless heart is tested green (105 tests), the native-full build
compiles (gpui included — built from inside the crate on the rolling nightly),
and the headless self-check boots the live image. The coverage matrix above has
moved a full column to **live**: every kernel lifecycle verb (seal/unseal/
destroy/burn), factory-birth, and multi-action call-forests now run through the
embedded executor with real receipts, and the OBJECTS panel reflects proofs,
nullifiers, and cell lifecycle.

The native **cap-first multi-surface shell** is live: each dregg cell can be a
cap-confined surface (apps-as-cells), the window manager gates every op on the
surface's unforgeable capability (a forged cap is refused on every op; the
console is a protected trusted root), the trusted-path identity chrome is
shell-drawn from the live ledger (anti-spoof — a dangling surface reads
`missing`, a sealed cell's badge follows the executor), and the compositor
renders the surfaces over the real world in float / tile / stack. The SHELL tab
boots ready and is one click from the HOME landing portal (the boot view).

The remaining **designed-pending** rows (organ node-services behind `captp`, the
multi-hop delegation graph view, intents/obligations panels, the live federation
connect panel) are the active burn-down.
