# WEB-FORWARD — the firmament's `(target, rights)` handle carried to PIXELS IN THE BROWSER

*Design frontier doc. Present-tense, first-principles. A north star that shapes
intuition, with the buildable shape elaborated: the concrete next slice, the
killer demo, the developer journey, the honest gaps (F1/F2/F3). Companion to
`docs/DREGG-DESKTOP-OS.md` (the native firmament desktop this is the web
sibling of), `docs/FIRMAMENT.md` (the cap-gradation bridge), `docs/PG-DREGG.md`
(postgres as a dregg surface — the same "n is a surface" move on the data side),
and `docs/STARBRIDGE-V2.md` (the native gpui master interface whose surface/shell
model the browser compositor mirrors). dregg is the verified accountability
SUBSTRATE the web app integrates against, NOT the agent runtime: the loop —
perceive/plan/act, the agent's will — lives ABOVE.*

---

## 0. The one-paragraph vision

A dregg **window is a `Capability{ target: Surface(cell), rights }` rendered to a
`<canvas>`** — the firmament's one handle carried, byte-for-byte the same router
arm `sel4/dregg-firmament/src/surface.rs` already proves, out past the seL4
machine, past the native gpui shell, into a browser tab. dregg compiles to wasm:
the `dregg-wasm` `DreggRuntime` already runs a complete cell/turn/capability world
in the tab, the `dregg-lightclient` already verifies a whole finalized history
from one succinct aggregate while re-witnessing nothing, and `@dregg/sdk/browser`
already drives the live devnet over `fetch`+SSE. The web-forward thesis is that
**output-integrity is unfoolability applied to the display path, and the display
is now the DOM**: a browser surface paints only the genuine projection of its
owning cell's verified post-state, its identity chrome is drawn from the live
ledger (never the app's self-description), and a remote collaborator's surface
ships **state + proof, not pixels** — dregg *proves* the determinism Croquet
merely trusts, so an embedded remote surface is **self-attesting** and a light
client at the glass *cannot be fooled by the pale ghost* even when the bytes
arrive over an untrusted network. n=1 is the local tab (immediate revoke,
synchronous present); the same surface handle relaxes its bounds along n to reach
a peer's tab, with nothing in the app code distinguishing the two. We do not
invent a web windowing model; we carry the one capability handle to the glass,
hold every seam to one worthwhile semantics, and label the verified-graphics
frontier (F1 framebuffer attestation, F2 the Lean executor in wasm, F3 GPU/WebGPU
confinement) as severe-problems-with-closure-lanes, never walls.

---

## 1. Why web-forward, and why dregg specifically

The native desktop OS (`DREGG-DESKTOP-OS.md`) carries the surface cap to seL4
pixels through a verified compositor-PD. That is the *deep* end — the verified
graphics destination. The **web-forward** end is the *reach* end: the place a
stranger, an agent, an integrator (pug, buildr, builders, sig, simbi) actually
encounters dregg first is a URL, not a QEMU image. Three facts make the browser a
first-class dregg surface rather than a thin viewer:

1. **dregg already runs in the tab.** `wasm/src/runtime.rs`'s `DreggRuntime` is a
   complete in-browser dregg world: it holds a real `dregg_cell::Ledger` and a
   real `dregg_turn::TurnExecutor`, mints cells via `Effect::CreateCellFromFactory`,
   executes signed multi-agent turns, runs real `Authorization::Custom`
   threshold-sig flows, and exposes the whole thing through ~80 `#[wasm_bindgen]`
   functions (`wasm/src/bindings.rs`). This is not a mock — it is the SAME
   `dregg-turn`/`dregg-cell` crates the node and starbridge-v2 link, compiled to
   wasm32. The browser is a faithful `n = 1` dregg machine today.

2. **dregg already verifies in the tab.** `dregg-lightclient`'s `verify_history`
   checks ONE recursive `WholeChainProof` against a VK trust-anchor and reads off
   the bound commitments — re-witnessing nothing, cost independent of history
   length. Pointed at a devnet root, a browser can *independently confirm* the
   whole finalized history evolved correctly. The unfoolability theorem
   (`AssuranceCase.lean` `unfoolability_guarantee`,
   `Dregg2.Circuit.RecursiveAggregation.light_client_verifies_whole_history`) has
   a Rust embodiment that compiles toward wasm — the anti-pale-ghost tooth, in the
   client.

3. **dregg already drives the wire from the tab.** `@dregg/sdk/browser`
   (`sdk-ts/src/browser.ts`) is a fetch-only organ surface — a faithful
   `BrowserNodeClient` (same devnet headers, JSON + SSE) with the `TrustlineClient`
   and `ChannelsClient` constructed against it; `@dregg/sdk/wasm`
   (`sdk-ts/src/wasm.ts`) wraps the `dregg-wasm` module for STARK verify, token
   ops, predicate proofs, and the full sim. The browser product surface exists; it
   needs a spine and a story, not a green-field build.

The web-forward angle is **welding these three into one model — run, verify,
reach — and carrying the firmament surface cap to the pixels they render.** Per
the WELD method (the capability usually already exists, disconnected; welding
beats building), almost nothing here is new code; it is connection plus one
honest seam at the glass.

---

## 2. The model: a browser surface is a cell's surface capability

The firmament's `(target, rights)` handle has three backings (`FIRMAMENT.md` §3):
`Local{slot}` (seL4 syscall), `Distributed{cell}` (executor turn), and
`Surface{cell}` (`surface.rs` — a window). The web-forward claim is that **a
`<canvas>` / DOM-rendered surface is exactly `Target::Surface{cell}` resolved in
the browser**, with the SAME discipline:

| firmament concept | browser realization | proven by today |
|---|---|---|
| `Capability{ Surface(cell), rights }` | a `SurfaceView` JS object holding a `cellId` + a held cap, re-reading the live ledger on every paint | `surface.rs SurfaceBacking`; `DreggRuntime.get_cell_state` re-reads live |
| `invoke(holder, surface, rights)` (present/draw) | `present(region, contentDigest @ stateRoot)` paints the canvas iff `requested ⊆ held` | `SurfaceBacking::invoke` (real `is_attenuation`) |
| `delegate(granter, recipient, surface, narrower)` (share a window) | "share this pane read-only with agent B" = a real `Effect::GrantCapability` turn; a WIDENING share REJECTS | `SurfaceBacking::delegate` → `DelegationDenied`; starbridge-v2 `Shell::share` |
| identity chrome (the anti-spoof badge) | the pane's title bar `(owningCellId, lifecycle, sourceStateRoot)` drawn by the COMPOSITOR from the live ledger, never the app | starbridge-v2 `Shell` identity chrome; `T2 LABEL-BINDING` |
| `n = 1` collapse | the local tab: revoke darkens the pane THIS frame, present is synchronous | `Bounds::distributed(1) == LOCAL` |
| `n > 1` relaxation | a remote collaborator's pane composited locally over the wire; bounds relax, verbs unchanged | the same `with_distance(n)` knob; §6 |

The compositor (here a small JS/wasm scene-graph module, the browser analogue of
starbridge-v2's gpui-free `shell::Shell::compose`) **multiplexes capabilities; it
does not mint authority.** Its state IS the scene graph — an ordered list of
`(owningCellId, regionRect, contentDigest, sourceStateRoot, zLayer, focusFlag)` —
and compositing is itself a turn against a compositor cell, so the four anti-ghost
teeth from `DREGG-DESKTOP-OS.md` §5 apply unchanged in the browser:

- **T1 NON-OVERLAP** — a surface writes only regions its cap authorizes
  (`granted ⊆ held` with `Rights = region-set`); overpainting another pane is
  **UNSAT**.
- **T2 LABEL-BINDING** — the rendered identity badge is a *function* of
  `owningCellId + sourceStateRoot`, read by the compositor from cell state, not
  the app; a label ≠ owner is **UNSAT**. This is the web answer to phishing
  chrome: the badge a user reads is a verified state-root binding, not a
  `<div>` the page drew.
- **T3 FOCUS-EXCLUSIVITY** — at most one `focusFlag`; keyboard/pointer events
  route only to it; two focus flags or input to a non-focused pane is **UNSAT**
  (EROS *traceability of volition*, in the DOM event layer).
- **T4 NO-INFERENCE** — a `present()` reads only its own region's prior contents
  (a cap-scoped read; double-buffered shared surfaces, per EWS).

The point that makes this *web-forward and not merely web-compatible*: the same
`VerificationToolkit` `AppSpec` that proves these teeth as `app_commit_iff_admit`
+ `app_violation_rejected` for the seL4 compositor is the SAME Lean module the
browser compositor's scene-turns run against (compiled to wasm, or checked by the
node). **"Output-integrity = unfoolability on the scene" is one theorem, two
glasses.**

---

## 3. The web product, layered (what a person/agent actually touches)

Six layers, each specializing a thing that already exists. The through-line:
*nothing is invented that the firmament/lightclient/sdk do not already provide.*

```
┌────────────────────────────────────────────────────────────────────────────┐
│ W6  THE SITE — the front door (site/)                                        │
│     landing · explorer (the live ledger as your-caps-as-rows) · playground   │
│     · the studio inspectors (<dregg-cell>, <dregg-receipt>, <dregg-note>).   │
│     The evaluator's first ten minutes (pug bar). Teaches WHAT-IS.            │
├────────────────────────────────────────────────────────────────────────────┤
│ W5  THE COMPOSITOR — surfaces-as-canvas (NEW, tiny; the keystone)            │
│     a JS/wasm scene-graph module; present() is a turn; T1–T4 anti-ghost      │
│     teeth; identity chrome drawn from the live ledger. The browser sibling   │
│     of starbridge-v2 shell::compose. Surface-cap → pixels.                   │
├────────────────────────────────────────────────────────────────────────────┤
│ W4  THE LIGHT CLIENT IN THE TAB — the anti-pale-ghost tooth                  │
│     dregg-lightclient::verify_history(root, vk_anchor) → AttestedHistory;    │
│     the tab independently confirms the whole finalized history. The state-   │
│     root tooth that makes a remote surface self-attesting (§6).             │
├────────────────────────────────────────────────────────────────────────────┤
│ W3  THE SDK — the acting + reading surface (@dregg/sdk/{browser,wasm})       │
│     Identity → .turn() → .sign() → .submit() → Receipt (the two-noun front   │
│     door); BrowserNodeClient (fetch+SSE) for organs; wasm for verify/proof.  │
├────────────────────────────────────────────────────────────────────────────┤
│ W2  THE IN-TAB WORLD — dregg-wasm DreggRuntime                               │
│     a complete local cell/turn/capability/note/federation world running the  │
│     REAL dregg-turn/dregg-cell crates compiled to wasm32. The n=1 machine.  │
├────────────────────────────────────────────────────────────────────────────┤
│ W1  THE EXECUTOR — Rust today, the verified Lean producer at the frontier    │
│     W2 runs the Rust TurnExecutor (wasm32 cannot link libdregg_lean.a).      │
│     web/spike/build-executor-wasm.sh is the live attempt to compile the      │
│     REAL Lean execFullForestG to wasm32 via emscripten — F2 (§7).           │
├────────────────────────────────────────────────────────────────────────────┤
│ W0  THE WIRE / THE GLASS — fetch, SSE, WebCrypto, <canvas>, the DOM          │
│     browser primitives; the only ambient surface, scoped by caps above.     │
└────────────────────────────────────────────────────────────────────────────┘
```

The honest seam between W1 and W2: **today the browser runs the Rust executor,
not the verified Lean producer** (`wasm/Cargo.toml`: "wasm32 cannot link
libdregg_lean.a"). The Rust `TurnExecutor` and the Lean producer agree by the
deployed differential the rest of the tree runs (the model-finds-the-bug loop),
so the in-tab world is *faithful to the deployed semantics* — but it is not yet
*the verified artifact itself in the tab*. That is F2, and it is a build attempt
already in flight (`web/spike/`), not a research vacancy. Naming this seam loudly
is the whole discipline (Seams Are Work, Not Walls): the in-tab world advertises
"Rust-executor, differential-anchored," NOT "verified-in-browser," until F2 lands.

---

## 4. The killer demo: TWO TABS, ONE SURFACE, the share that REFUSES

**The single runnable end-to-end story that IS the evaluation artifact** (the pug
bar: "two agents, a surface, a share that the executor refuses"):

> Open the dregg playground in two browser tabs (Alice, Bob). Alice creates a
> cell and **opens it as a surface** — a `<canvas>` pane whose title bar shows
> `cell a3f1… · live · root 7c2e…`, all drawn by the compositor from the live
> ledger, not by the pane. Alice **shares the pane read-only with Bob**: a real
> `Effect::GrantCapability` turn commits, and Bob's tab now composites the SAME
> surface — re-reading Alice's cell state, painting the same content, showing the
> same verified identity badge. Bob tries to **share it onward as writable** (a
> widening): the executor **REJECTS** with `DelegationDenied`, and Bob's "share"
> button flashes the `⚠ over-share` teaching banner — *the no-amplification
> guarantee firing at the pixel layer, in front of you.* Alice **revokes** Bob's
> pane: it goes dark THIS frame (n=1, synchronous). Bob's tab runs
> `verify_history` against the devnet root and prints `AttestedHistory ✓ (N
> turns, re-witnessed nothing)` — the pane he saw was the genuine projection of a
> verified history, and he confirmed it himself.

Every clause of that demo is backed by code that exists: surface open/share
(`surface.rs` + `DreggRuntime`), the widening refusal (`SurfaceBacking::delegate`
→ `DelegationDenied`, the `real_executor_rejects_widening_surface_share` test
already green), the identity badge (starbridge-v2 `Shell` chrome, ported to the
DOM), the dark-on-revoke (the `n=1` collapse), the whole-history verify
(`dregg-lightclient`). The demo's *teaching moment* is the refusal — exactly as
starbridge-v2's `⚠ over-grant` makes you watch a transfer get rejected. **The
demo IS the proof that the web surface is a real capability, not a `<div>`.**

A second demo for the agent/integrator audience (the ADOS north star, kept as a
north star not a spec): **the agent's pane.** A coding agent's tool-use loop
renders its working surface as a dregg cell; each tool call it makes is a turn
against a budget cell (Stingray conservation); a human watching the pane sees the
agent's actions land as receipts on the live dynamics feed, cap-gated and
budget-metered, *without trusting the agent's loop* — the seam the four
integrators all hand-rolled (the mutable `tool_calls` row) made tamper-evident at
the glass. This is the web face of the one-seam wedge.

---

## 5. The developer journey (the first ten minutes, web-forward)

The evaluator's path — stranger-usable, zero tribal knowledge:

1. **Read.** Open the site (W6). The landing says what dregg IS (a verified
   object-capability substrate; agents integrate against it). The explorer shows
   a live devnet ledger as *"your capabilities, expressed as the rows you may
   read"* (the PG-DREGG framing, in the browser: a cap *is* a view). No install.

2. **Play, locally.** Open the playground (W2). `create_runtime()` →
   `create_agent("alice", 1000)` → `create_agent("bob", 0)` →
   `execute_turn(transfer 100 alice→bob)`. Watch the receipt, the balance flow,
   the dynamics feed. Try an over-transfer: it REJECTS. This is a complete dregg
   world in the tab, zero backend. (`sdk-ts/examples/` already ships
   `transfer.mjs`, `trustline.mjs`, `channel.mjs`, `attested-query.mjs`,
   `devnet-walkthrough.mjs` — these become the playground's worked snippets.)

3. **Verify, yourself.** Run `verify_history` against the devnet root (W4). The
   tab confirms the whole finalized history with no re-execution. *You did not
   trust the server; you checked it.* This is the moment dregg's thesis becomes
   tactile in a browser.

4. **Act, for real.** Construct an `Identity`, build a `.turn()`, `.sign()` it,
   `.submit()` it to the devnet via `BrowserNodeClient` (W3), receive a
   `Receipt`. The two-noun front door (`Identity` + `.turn()`) is the whole acting
   API; authorization is inescapable (the SDK killed `Unchecked` from the public
   surface, per #166).

5. **Surface it.** Open a cell as a canvas pane (W5). Share it. Watch the
   over-share refuse. This is the killer demo, reachable by copy-paste.

6. **Integrate.** Drop `@dregg/sdk/browser` into your own app; the seam where you
   serialize "an agent did X" becomes a signed, cap-checked, budget-metered turn
   (the one-seam wedge). dregg is the substrate; your loop stays yours.

The developer never learns seL4, Lean, or the circuit. They learn: *a cap is a
view, a turn is an action, a receipt is a record, a surface is a pane, and the
light client is how you know none of it lied.*

---

## 6. The remote-surface SELF-ATTESTING story (Croquet inverted, the state-root tooth)

This is the conceptual heart of the web-forward frontier and dregg's genuinely
novel contribution to it.

**The Croquet model** (David Reed / Croquet OS / Multisynq): collaborative apps
ship *replicated computation*, not pixels — every participant runs the same
deterministic event-stream and arrives at the same state, so a shared world is
bit-identical everywhere. Croquet's correctness REST on an assumption it can only
*trust*: that every replica is honestly running the same deterministic code over
the same ordered events. A malicious or buggy replica can silently diverge; there
is no in-band proof the state you computed is the state your peer computed.

**dregg inverts the trust.** dregg's whole stack is "the proof witnesses the
protocol's correct evolution" — the executor IS the verified semantics, a turn's
post-state is the authenticated fold of the pre-state and the turn
(`recover_eq_replay`, the root tooth `Snapshot.claimed_root`), and
`verify_history` confirms a whole finalized history from one succinct aggregate
re-witnessing nothing. So a remote surface in dregg ships **state + proof**, and:

> **A dregg remote surface is SELF-ATTESTING.** When Alice's tab composites Bob's
> pane, it does not trust Bob's bytes. The pane carries `(cellId, contentDigest,
> sourceStateRoot)`; Alice's compositor checks that `sourceStateRoot` is a state
> the light client attests (chains to a finalized root she verified), and that
> `contentDigest` is the genuine projection of the cell at that root. **dregg
> PROVES the determinism Croquet TRUSTS.** A lying remote replica cannot forge a
> `sourceStateRoot` — a forged `(old_root, new_root)` has no satisfying leaf in
> the recursion (the `ungated_prover_..._cannot_produce_a_root` tamper tests). The
> pale ghost on the network cannot fool the glass.

This is also dregg's answer to **Arcan's** honest complaint that there is "no
visual identity you can safely forward" for a remote surface — Arcan's A12 ships
opaque content + a content-commitment over the wire (waypipe-style), which
authenticates *transport* but not *meaning*. dregg's `sourceStateRoot` IS a
forwardable visual identity: a structured, verified provenance the receiving
compositor checks against a light-client-attested root. Two content classes, both
honest:

- **DETERMINISTIC content (the Croquet class)** ships STATE + the state-root
  binding; the receiver re-derives the projection and checks the root. The pane
  is self-attesting end-to-end. This is the dregg-native, novel path.
- **OPAQUE content (the Arcan class)** ships a content-commitment + bytes over
  the net edge; the receiver authenticates transport (the commitment) but the
  *pixels' meaning* is the sending cell's claim, bound to its `sourceStateRoot`
  but not re-derivable. Honest about the weaker guarantee.

The `n` parameter is exactly the dial: at `n = 1` the remote surface collapses to
a local pane (Alice and Bob in one tab is a degenerate case — synchronous,
immediate). At `n > 1` the bounds relax (the pane's revoke is eventual — the
group-key epoch lift must propagate; an in-flight frame may still land) while the
verbs (`present` / `share` / `revoke`) and the self-attestation are unchanged.
The web-forward remote surface is `SurfaceBacking::with_distance(n)` carried over
the `BrowserNodeClient` wire — the firmament's reach-out, on the glass.

---

## 7. The honest gaps — the verified-graphics / verified-browser frontier (F1/F2/F3)

Named as severe-problems-with-closure-lanes, never walls. Each is a real seam at
the I/O boundary the executor's proof does not yet cover, with the closure lever
stated.

**F1 — THE LAST HOP (browser framebuffer attestation).** dregg proves the surface
content is the genuine projection of the cell's verified post-state (T1–T4 hold
over the scene graph). It does NOT prove the *pixels actually scanned to the
user's monitor* match `contentDigest`. In the browser the last hop is the DOM
compositor + the OS window manager + the GPU + the panel — all outside any dregg
proof. A malicious browser extension or a compromised page CAN overpaint a dregg
pane. Closure lever (partial, browser-shaped): a small **trusted-chrome anchor** —
the identity badge and the secure-attention gesture rendered by a context the page
cannot reach (a browser-extension-drawn overlay, or in a packaged-app shell a
privileged top-zLayer surface the page has no cap to, exactly the
`DREGG-DESKTOP-OS.md` §5 trusted-path PD but realized as the extension's content
script at a z-index no page CSS can exceed + a reserved chord). This narrows F1
from "anyone can spoof" to "only the browser/OS TCB can," matching how sDDF flags
the IOMMU as the named unverified primitive. Full closure (panel-level frame
attestation) is the native desktop's F1/F2, out of reach in a vanilla tab.

**F2 — THE VERIFIED LEAN EXECUTOR IN WASM.** Today the in-tab world runs the Rust
`TurnExecutor` (W1/W2), differential-anchored to the Lean producer but not *the
verified artifact itself*. The closure is **compiling `execFullForestG` to
wasm32** — and this is a build in flight, not a vacancy:
`web/spike/build-executor-wasm.sh` links the v4.30 Lean-emitted `Exec/FFI.c`
(`@[export] dregg_exec_full_forest_auth`) + its full transitive C closure
(Dregg2 + mathlib + batteries + aesop) against a wasm32 Lean runtime
(`build-wasm-runtime.sh`'s emscripten leanrt/stdlib), with `--gc-sections + -flto`
pruning what the executor never reaches and a Node host shim running a real turn.
The named obstacles are characterized (the libuv coupling at runtime init — the
same excision the seL4 executor-PD faces, `FIRMAMENT.md` §6; GMP for the ELF/wasm
target or a fixnum-only shim; the `-flto` bool/i1-vs-i8 signature-lowering hazard
between the closure's bitcode and the non-LTO stdlib). When F2 lands, the tab runs
the SAME verified semantics as the federation's authoritative producer, and the
in-tab world advertises "verified-in-browser" honestly. Until then: "Rust,
differential-anchored," loudly. This is the highest-leverage web-forward frontier
item — it turns "faithful" into "verified" with no new trust.

**F3 — GPU / WebGPU SURFACE CONFINEMENT.** The native desktop's F3 is verified
GPU/servo/webgpu compositing; the browser's F3 is the dual question one rung
softer: can a surface's WebGPU/`<canvas>` rendering be CONFINED to its granted
region against a malicious renderer? In the browser, the answer leans on the
browser's own origin/iframe sandbox, NOT on a dregg proof: a remote/untrusted
surface renders in a sandboxed cross-origin `<iframe>` or an `OffscreenCanvas` in
a worker, whose output is a frame-cap the compositor blits — the CapDesk-style
"thin untrusted renderer holding only the granted facets" pattern, realized as the
iframe sandbox. dregg mediates *authority* (verified: which cell owns the region,
`granted ⊆ held`); the browser mediates *isolation* (the same-origin policy is the
named primitive, the web's IOMMU-equivalent). Honest stance: T1 (non-overlap) is a
dregg theorem over the scene graph AND relies on the browser honoring the iframe's
clip — a named composition assumption, not a single proof. The servo
`OffscreenRenderingContext` confinement story from `DREGG-DESKTOP-OS.md` R2 is the
native version of this exact pattern; the browser gets it for cheaper (the sandbox
exists) but weaker (the sandbox is the browser's, not dregg's).

**The discipline across F1/F2/F3:** never launder them as solved. The buildable-now
slice (§8) is *real* (T1–T4 are theorems over the scene graph; the surface cap is
the real `is_attenuation` gate; the light client really re-witnesses nothing). The
frontier is honestly the I/O edge — the last hop, the executor's wasm artifact,
the GPU isolation — and each names its primitive (browser/OS TCB, the libuv
excision, the same-origin policy) the way the kernel names the crypto floor.

---

## 8. The buildable-now slices (wide-safe, separate-workspace, not blocked on the cutover)

Each is buildable today against existing code, in a workspace that does NOT
contend with the in-flight VK rotation / kernel cutover (the `wasm` and `sdk-ts`
trees are already workspace-excluded; the firmament crate is standalone; the site
is static). Ordered easiest/highest-leverage first.

**S0 — `Target::Surface` is the SAME gate, witnessed (the transfer-triangle, done).**
`sel4/dregg-firmament/src/surface.rs` already proves the surface cap attenuates,
delegates, and refuses a widening through the real executor
(`real_executor_enforces_attenuation_on_surface_share`,
`real_executor_rejects_widening_surface_share`, both green). This is the R0
keystone the whole design rides — *already landed.* The web slices below carry it
to the glass.

**S1 — the surface binding in `dregg-wasm` (small, the keystone for W5).** Add
`#[wasm_bindgen]` functions mirroring `surface.rs` over the existing
`DreggRuntime` ledger+executor: `open_surface(cell) -> SurfaceView`,
`present(surface, region, contentDigest)` (checks `requested ⊆ held`),
`share_surface(from, to, surface, narrower)` (a real `Effect::GrantCapability`
turn; widening REJECTS), `revoke_surface`, `surface_identity(surface)` (returns
`(owningCellId, lifecycle, sourceStateRoot)` from the live ledger — the T2 badge
source). This is the same shape as the ~80 bindings already in `bindings.rs`; it
is the smallest change that makes "a browser surface = a cell's cap" callable from
JS. Wide-safe: it only adds to the wasm crate.

**S2 — the browser compositor module (NEW, tiny; W5).** A gpui-free scene-graph
module — the browser sibling of starbridge-v2's `shell::Shell::compose` — that
holds the ordered surface list, draws each pane to a `<canvas>`/DOM node with its
**compositor-drawn identity chrome** (the T2 badge from S1's `surface_identity`,
NEVER the pane's self-description), routes DOM focus/pointer events to the single
focused pane (T3), and enforces T1 non-overlap on `present`. Port the proven
layouts (float/tile/stack) and the protected-root console from starbridge-v2.
This is the firmament-to-pixels weld in the browser. Wide-safe: pure frontend.

**S3 — the killer-demo playground page (W6, the evaluation artifact).** Wire S1+S2
into the existing `site/playground` as the "two tabs, one surface, the share that
refuses" demo (§4). Two `DreggRuntime`s (or one shared via the devnet),
open/share/over-share/revoke, the `⚠ over-share` teaching banner, the live
dynamics feed. The copy-paste end-to-end story the pug handoff needs. Wide-safe:
static site.

**S4 — `verify_history` in the tab (W4, the anti-pale-ghost tooth).** Compile
`dregg-lightclient`'s `verify_history` to wasm (it depends only on
`dregg-circuit` recursion + `dregg-blocklace`, both wasm-buildable) and expose
`verify_devnet_history(root, vkAnchor) -> AttestedHistory` from the wasm module;
add the "verify the whole history yourself" button to the explorer (W6) and the
playground (S3). The VK anchor is genesis/checkpoint config, never taken from the
artifact under verification (the lightclient already enforces this). Wide-safe:
adds a wasm export + a site button. (Honest scope: carries the lightclient's named
floor — `recursive_sound` + the two fork follow-ups — surfaced in the UI, not
hidden.)

**S5 — the SDK two-noun browser front door (W3, the acting surface).** Finish the
`sdk-browser-ed25519-webcrypto` follow-up named in `sdk-ts/src/browser.ts`: back
`Identity` with WebCrypto/@noble ed25519 so the FULL acting surface (`Identity →
.turn() → .sign() → .submit() → Receipt`) bundles for the browser, not just the
fetch-only organs. Then a `.turn()` from a tab against the devnet is a real signed
turn. Wide-safe: sdk-ts only, no crypto reimplemented (WebCrypto/@noble).

**S6 — the explorer as caps-as-rows (W6, the PG-DREGG framing in the browser).**
Reframe `site/explorer` as *"your capabilities, expressed as the rows/cells you
may read"* — the same "a cap IS a view" insight `PG-DREGG.md` makes for postgres,
realized over the live devnet ledger with the wasm light-client attesting the
state. The explorer becomes the web face of the read side; pairs with S4 (verify)
and S3 (act/surface). Wide-safe: static site + existing devnet API.

**Sequencing.** S1→S2→S3 is the surface-to-pixels spine and the killer demo; S4
is the verify tooth (independent, can land in parallel); S5/S6 round out the
acting+reading product. None touch the kernel/circuit cutover; all ride existing,
proven code. The deep frontier (F1 trusted chrome, F2 Lean-executor-in-wasm, F3
sandbox confinement) sits beyond this slice, honestly named, with F2 already a
build in flight in `web/spike/`.

---

## 9. Where it fits — and what's already DONE

**Already done (the foundation this welds):**

- **`Target::Surface{cell}`** — `sel4/dregg-firmament/src/surface.rs`: the surface
  cap attenuates/delegates/revokes through the real `is_attenuation` gate and the
  real `TurnExecutor`; a widening share REJECTS with `DelegationDenied` (tests
  green). The cap-to-glass seam, proven.
- **The in-tab world** — `wasm/src/runtime.rs` `DreggRuntime` + `bindings.rs`
  (~80 `#[wasm_bindgen]` fns): a complete cell/turn/capability/note/federation
  world running the REAL `dregg-turn`/`dregg-cell` crates in wasm32. The browser
  `n = 1` machine.
- **The light client** — `dregg-lightclient::verify_history`: whole-history
  attestation from one succinct aggregate, re-witnessing nothing, against a VK
  anchor. The anti-pale-ghost tooth, ready to compile to the tab.
- **The browser SDK surface** — `@dregg/sdk/browser` (fetch+SSE organs) +
  `@dregg/sdk/wasm` (verify/proof/sim); `sdk-ts/examples/*` (transfer, trustline,
  channel, attested-query, devnet-walkthrough) as the worked snippets.
- **The native compositor model** — starbridge-v2's gpui-free `surface`/`shell`
  modules (cap-confined surfaces, anti-spoof shell-drawn identity chrome, the
  float/tile/stack compositor, the protected console) — the *exact* model S2 ports
  to the DOM. The browser compositor is starbridge-v2's `Shell::compose` with a
  `<canvas>` backend instead of gpui.
- **The executor-in-wasm attempt** — `web/spike/build-executor-wasm.sh` +
  `build-wasm-runtime.sh`: the live F2 build linking the real Lean executor to
  wasm32. The frontier is in flight, not blank.

**How it fits the larger dregg picture:**

- The web-forward surface is the **same `(target, rights)` handle** as the native
  desktop (`DREGG-DESKTOP-OS.md`), the firmament (`FIRMAMENT.md`), and the data
  surface (`PG-DREGG.md` — "your node IS your postgres" is "a cap IS a view" is "a
  pane IS a cap"). One model, four glasses: seL4 pixels, gpui pixels, postgres
  rows, browser pixels.
- The light client at the glass is the **same unfoolability theorem** the whole
  ARGUS vision is organized around — carried one hop further out, to the human at
  the browser.
- The remote-surface self-attestation is the **single-machine principle**
  (`dregg4-vision`) on the display: `n = 1` is the local tab (strong bounds);
  `n > 1` is the collaborator's tab (relaxed bounds, same verbs, same
  self-attestation). The web is where `n > 1` is *normal*, so it is where the
  gradation earns its keep.

---

*The web is dregg's reach. We carry the one capability handle — the firmament's
`(target, rights)` — out past the verified seL4 glass, past the native gpui shell,
into the tab, and onto the canvas. The browser runs a real dregg world, verifies a
whole history re-witnessing nothing, and paints surfaces that are the genuine
projection of verified cells with identity drawn from the ledger, not the page. A
remote collaborator's pane ships state + proof, not pixels — dregg proves the
determinism Croquet trusts, so the glass cannot be fooled. n=1 is the local tab
today; the same surface reaches a peer tomorrow with only the bounds relaxed. The
frontier — the last hop, the Lean executor in wasm, the GPU sandbox — is honestly
the I/O edge, each seam named with its primitive, none of them a wall.*
