# Surfaces: One Gate, Four Planes — the load-bearing correction

Status: **design synthesis** (2026-07-12), from a 5-agent deep dive (2 scholars: census + dynamic-dimension · 1
external-theory scholar · 1 adversary · 1 constructive ideator), each grounded in the real crates + the `Dregg2.Deos`
Lean. This **supersedes the Surface portion of `docs/DREGGNET-CLEANER-DESIGN.md` §3** (that doc's session/verification/
confinement analyses stand; its "one `AffordanceSurface → lower → ViewNode → backend`, `enabled = is_attenuation`"
Surface move is over-collapsed — corrected here).

## The verdict (all five agents converged)

The clean-design instinct is **directionally right and locally over-collapsed.** "A Surface is a cap-attenuated,
per-viewer projection of the same membrane a Session authoritatively writes, and both leave receipts" is **sound and
already Lean-proven** for its core case (`Deos/Surface.lean:61` `Surface cell rights := Cap.endpoint`, leg 1 of the
crown). But the specific collapse flattens **five independently-proven theorems** into one and gets one arrow backwards.
Two framing corrections and four object corrections:

- **Drop "dual" → "asymmetric derivation."** External theory is unanimous (lenses/optics, CQRS, FRP, moldable dev):
  writes are authoritative + singular; reads are **derived, many, composable, moldable** (one write model fans out to
  many per-viewer, per-question read models). A lens *bundles* read+write and its categorical dual is a *prism*
  (product↔sum), not read↔write. So Surface is a **derived read *facet*** of the membrane, not a symmetric dual.
- **`Offering = Session × Surface` is a fibered/Σ product over one Cell, not a free `×`** — the factors share the cell
  state (the Session writes exactly what the Surface reads).

## The design: ONE gate, FOUR planes, gated-not-lowered

The thing to unify is **the gate**, shared by a small **family of four planes** related by **reference + gating**, not
by lowering into one type.

### The trunk — the frustum gate (unify this; it IS one thing)
Every projection is the same order `is_attenuation` (`required ⊆ held`), gating affordances (`Affordance.fireGate`),
scene cells (`FogOfWar.canSee`), and reshare hops (`Membrane.hop`) — one order, three uses. **But the frustum is
TWO-DIMENSIONAL:** authority **AND** a witness-graph disclosure bit — `membraneShows v aff = fireGate(aff.required,
v.held) ∧ v.permits(aff.name)` (`Reactive.lean:370`), and `membrane_two_viewers_distinct` (`:396`) **proves two viewers
at EQUAL authority see DISTINCT surfaces**. `Viewer::from_read_cap` makes the disclosure bit *cryptographic*, not
advisory. → Unify **one `Frustum`/`Viewer` = {held, permits}** and one `project_membrane` walk; keep it 2-D. (The
original synthesis's "`enabled` = the `is_attenuation` frustum" is right but **half** the frustum.)

### The family — four planes, each bearing a theorem the others cannot
| Plane | Object | Bears (Lean) | Do not fold because |
|---|---|---|---|
| **A — Authority / actuation** | `AffordanceSurface{cell, [CellAffordance{name, required, effect_template: real Effect}]}` | confers-exactly (`Surface.lean:79`), fire-iff-authorized + binds-attested-root (leg 4, `Affordance.lean`), reshare-no-amplify (`Membrane.lean`) | this **is** the read-facet of a Session |
| **B — Presentation IR** | `ViewNode` (26 variants: layout/content/bind/actuation/Host/Adept/Tile) | **content-reactivity functor** `project∘step=step∘project` (`Rerender.lean:102`) — content-only, gate-preserving, fixed-list | B is a **peer** of A, not downstream (most ViewNodes never pass through an AffordanceSurface) |
| **C — Pixel / region** | the compositor + `ViewNode::Tile{handle}` (opaque, **no pixels**) → servo/android `RgbaFrame` | paint-order-free + damage-exact (`Compositor.lean`), **content non-interference** (`FogOfWar.lean:149`) | faithfulness is `blake3(bytes)` under `FrameCommit`, a **different** authority model — not re-projectable |
| **D — Composition operators** | `Host` (mount whole tree) · `Transclusion`=ImportedEq (one finalized value by ref) · `Bind` (one live scalar) | transclusion faithfulness/no-amplify (`Transclusion.lean`); Host DoS fail-safes | three **distinct** provenance semantics the code already separates |

### The crux — A and B are gated peers, not `lower(A) → B`
`ViewNode` carries content+layout an `AffordanceSurface` (a flat set of effect-templates) does not contain, and most
`ViewNode`s are produced *without* any affordance surface (deos-js applets, data cards, the moldable inspector). The
correct relation is a single render entry:

```
render(view: ViewNode, surface: AffordanceSurface, viewer: Viewer, disclosure, ctx) -> BackendOutput
```

The walk: `resolve_mounts` (Host) → `disclose(tree, level)` → for each actuation node whose `{turn,arg}` names an
affordance, set `enabled/present = project_membrane(viewer) ∧ reactive_ok(ctx)`. `lower(surface → default card)` stays
useful as **one direction** (the `/deos` path), a convenience — not the spine. This also keeps the **two dual
reactivity laws** the synthesis fused: B's **content** re-render functor (`Rerender`, render-side) vs A's **transition/
temporal fire** gate (`Reactive`, fire-side, `old→new` inside `[open,close]` — provably unwitnessable from projected
state). Keep both.

## The five over-reaches corrected (each contradicted by the repo's own Lean)
1. **`enabled` is a 4-conjunct gate**, not the `is_attenuation` frustum: `is_attenuation ∧ transition ∧ window ∧
   disclosure`. `Reactive.lean` proves the last three **irreducible** (the dungeon ballot itself is transition+window
   gated). Forcing everything through `is_attenuation` deletes banked proofs. *The most dangerous move.*
2. **`project∘step` covers content-only, gate-preserving, single-cell updates** — NOT reactivity (the enabled set
   changes with the clock) or `Host`-composition (untheorized in Lean). Don't claim "one engine on every backend."
3. **Backends are non-uniform in statefulness** — 1 live stateful (gpui `AppletView`: SharedApplet + glow/bind cache +
   invalidation) + N stateless bake (web/discord/telegram, stateless *only because the caller pre-reads binds*) +
   deos-leptos's frontend signal graph. The retained *render* cache is **licensed by `Rerender`'s functor law**.
4. **Pixels are an opaque `Tile` hole → plane C**, gated by `FrameCommit`/android perms (not `is_attenuation`); native
   panes (`Terminal`/`Editor`) own focus + per-frame repaint. "A read-only projection cannot BE an editor."
5. **`Frontend` ≠ just backend+transport** — it also carries identity derivation, session/thread lifecycle, and
   platform interaction models (Telegram edit-in-place + 64-byte callback cap; Discord 25-button cap).

## ViewNode grows THREE minimal additive ways (make the frustum first-class)
1. Actuation nodes' `enabled` computed from `project_membrane ∧ reactive_ok` (not an author bool) + a per-node
   drop-vs-dim policy.
2. Content/`Bind` nodes carry an optional `slot→read-cap` disclosure key, so `FogOfWar` **content** non-interference
   reaches the IR (a confidential bind renders structurally absent).
3. Recognize `disclose()` (Simple/Adept) as a third frustum dimension in the same `project(tree, viewer)` walk — keep
   the three axes (authority · read-cap · disclosure-level) **distinct inside** one walk.
Do **not** add pixel nodes (`Tile` is the seam to C) or a fourth composition node (Host/Transclusion/Bind are correctly
three).

## What is SAFE to unify now (measured duplications; each independently green, spine untouched)
1. **One affordance-transport codec** — four encodings of the same `{turn,arg}` today (`deosturn:` · `deos:cell:name` ·
   `fiction:vote:` · telegram `turn:arg`). Canonicalize `deos-view::{affordance_custom_id, parse_affordance_id}`,
   transport-parameterized. Cheapest, highest-leverage.
2. **Extract a `SurfaceBackend` trait in `deos-view`** over the existing ad-hoc render functions; move
   `dreggnet-web::view_html` + `dreggnet-telegram::render` *into* deos-view backends and **delete the subset walkers**
   (they silently drop `Host`/`Tabs`/`Grid`/rich leaves — the subsetting IS the evidence they diverged).
3. **Dedupe `AffordanceSurface`** (defined twice: `starbridge-web-surface` + `deos-reflect`) — keep the Lean-mirrored
   one canonical; the other re-exports.
4. **`enabled` = the 2-D frustum ∧ `reactive_ok`** in the render walk (ViewNode growth #1) — the synthesis's correct
   kernel, done *as one conjunct*.
5. **Bridge `deos-reflect::Presentation → ViewNode`** (retire the parallel moldable projection) — makes "liberate any
   surface into a card" lossless.

## Grounding
Lean: `metatheory/Dregg2/Deos/{Surface,Affordance,Reactive,Rerender,FogOfWar,Compositor,Transclusion,Membrane,
Rehydration}.lean` — no `sorry`/`axiom`; one honest seam (receipt-digest CR, named hyps `HInj`/`HFresh`); discount the
`X=X` vacuous lemmas (`rerender_deterministic`, `view_deterministic`, `noninterference`). External: obcap powerbox
(designation=authority), the deep-attenuation membrane/caretaker, lens get/put + CQRS asymmetry (one write, many
reads), DBSP/IVM (`project∘step` = the incremental-view-maintenance correctness law that *earns* "live"), moldable
development (plural per-object views). **Session/Surface is a lens, not a law; a shared *pattern* (the 2-D frustum +
the IR→N-backends fan-out), not one carrier type. Grow the proven core to fit the diversity — do not shrink the
diversity to fit one `AffordanceSurface`.**
