# web cells — live-DOM / JS-bundle web-of-cells cells

*(The frustum-snapshot applied to the DOM. A web-of-cells cell can CONTAIN web
content — a static JS/HTML/CSS bundle, or a snapshot of LIVE DOM / reactive-signal
state — and share it as a content-addressed, cap-gated, transcludable,
rehydratable, liveness-typed `dregg://` cell. The Rust realization is the standalone
`deos-web-cells` crate, a thin layer over the stable `starbridge-web-surface` API.)*

## The thesis

deos already makes a `dregg://` cell a verified container of *attested content* (a
page the origin committed, checkable by any third party — `web_of_cells.rs`), and
makes a *deos screenshot* a sturdyref-behind-a-membrane that re-expands per-viewer
(`REHYDRATABLE-SURFACES.md`, `affordance.rs`'s `AffordanceSnapshot`). A **web cell**
is the union of those two moves at the granularity of a **web bundle**: the unit you
"publish/commit … or even bundles of LIVE DOM state, and share that as part of the
web-of-cells."

A web bundle as a `dregg://` cell is, by construction:

- **content-addressed** — its identity is the `blake3` of a canonical bundle
  encoding; two bundles are the same cell iff they encode the same bytes;
- **cap-gated** — it is published into a real surface cell and fetched through the
  real attested cross-cell read; an unattested / tampered / dead bundle yields a
  refusal, never bytes;
- **transcludable** — another surface includes a *fragment* of it (a named asset)
  carrying the source's receipt-pinned provenance — Ted Nelson's quote, at the DOM
  level;
- **rehydratable** — a tiny DOM snapshot (a sturdyref + a culling boundary, not the
  bytes) re-expands per-viewer through the real membrane: a powerful viewer the full
  bundle, a weaker viewer an attenuated projection, an incomparable identity nothing;
- **liveness-typed** — Live / ReplayedDeterministic / ReconstructedApproximate is
  the rehydration stack's derived confinement readout, surfaced at re-expansion.

The **leptosic angle** is the point of the name: a Leptos app's live signal-graph
state IS a "live DOM bundle." Publishing it as a `LiveDomSnapshot` cell shares your
app's live state as a transcludable, rehydratable, cap-confined artifact. A Leptos
app's SSR→hydrate shape *is* the rehydration shape — serialize the signal graph into
a snapshot asset, publish, re-expand per-viewer through the membrane.

## What this is NOT

It is not a new fetch, a new attestation, a new snapshot, a new membrane, or a new
cap model. Every load-bearing primitive is the genuine one from
`starbridge-web-surface`; this layer only gives those primitives a *web-bundle*
shape. The whole novelty is "the same verified machinery, applied to bundles of
DOM/JS/CSS (or serialized live state)" — nothing here adds authority the kernel does
not already prove.

## The data model

A **`WebBundle`** (`deos-web-cells::bundle`) is a `kind` + an `entrypoint` + named
**assets**:

- **`BundleKind`** is `StaticBundle` (HTML/JS/CSS authored once, served as-is) or
  `LiveDomSnapshot` (the serialized DOM tree / reactive-signal graph captured from a
  running surface). The kind is folded into the content-address, so a static bundle
  and a live-DOM snapshot with identical assets are *distinct cells* — you cannot
  pass one off as the other.
- **`BundleAsset`** is `{ name, content_type, bytes }`. The `name` (`index.html`,
  `app.js`, `theme.css`, `dom-state`) is both the asset's identity within the bundle
  AND the **origin key** the per-viewer membrane gates on.
- **`BundleManifest`** is the small, content-addressed description — the kind, the
  entrypoint, and the per-asset digest table `(name, content_type, blake3(bytes))`
  in canonical (name-sorted) order. Its `digest()` pins the bundle's *shape* in one
  32-byte hash, *without* the asset bytes — so a snapshot can carry the manifest
  digest cheaply.

The bundle's **`content_hash()`** is `blake3` of its **canonical encoding** (a
length-prefixed, name-sorted framing behind a `DEOSWB01` magic). The encoding is
deterministic: identical bundles encode identically and so address identically,
independent of construction order. `content_uri()` renders the
`dregg-bundle://<hex>` content-address as it would appear in a link (distinct from
the per-cell `dregg://<cell>` locator).

## Publishing a bundle as a `dregg://` cell

`publish_bundle(web, seed, bundle, lineage, witness_log, sources_reachable)` commits
the bundle's canonical encoding into a **real surface cell** through the stable
`WebOfCells::publish` — so the cell's committed content hash IS the bundle's content
hash — and returns:

- the **`DreggUri`** (the bearer cap into the cell — the locator others fetch);
- a **`Sturdyref`** over that ref, carrying the publisher's `lineage` (the authority
  the bundle is served under) + the source context's `witness_log` + whether the
  sources are still reachable — the cap-handle behind the membrane that rehydration
  re-expands per-viewer.

There is no bespoke publish path: the content commitment, the attested root, and the
trusted chrome are all the genuine web-of-cells machinery. The committed URL the
publish binds is the bundle's `content_uri()`, so the trusted-path chrome shows the
bundle *identity*, drawn from the ledger, never the page.

## Fetching a bundle (the cap tooth)

`fetch_bundle(web, uri)` resolves the `dregg://` ref through the real
`WebOfCells::fetch`, runs the real client-side `AttestedResource::verify` (the
attestation chain — content-addressed, receipt-in-stream, receipt-stream-root
reconstruction, quorum), and only then decodes the verified bytes back into a
`WebBundle`. **Confinement before content:** the fetch verifies *before* any decode,
so an unattested / tampered / dead bundle yields a `BundleError` and no bundle (the
bytes never decode). A node that drifts the committed bytes is caught at the
serve-turn binding (`ContentDoesNotMatchCommitment`) before the client even
verifies; a forged receipt-stream root fails the reconstruction; a dead ref is
`OriginNotFound`. A `MalformedEncoding` (the attestation held, but the cell committed
something that is not a bundle) is distinct from an attestation failure.

## The DOM frustum-snapshot → per-viewer rehydration

This is the frustum-culled snapshot (`DEOS.md`'s "THE dregg-only novelty") applied
to the DOM. It is the *exact same shape* as `affordance.rs`'s
`AffordanceSnapshot`/`rehydrate_affordances`, with a `WebBundle` as the witnessed
scene.

A **`DomSnapshot`** (`deos-web-cells::rehydrate`) is **tiny by construction**: it
carries a `Sturdyref` (the cap-handle into the witness-graph) + a **`BundleBoundary`**
culling boundary (the cell + the bundle's manifest digest + the asset names) — NOT
the asset bytes, and NOT any viewer's projection. A normal DOM serialization is a
dead byte blob; a deos DOM snapshot is *a paused camera on a witnessed interactive
surface that re-expands inside its own jail*. The snapshot grows with the asset-NAME
count, never the asset payloads.

**`rehydrate_bundle(snapshot, membrane, web)`** re-expands the frustum **per-viewer**,
in three steps — confinement before relation:

1. **fetch = verified turn + the per-viewer projection + the liveness-type.** Run the
   real `rehydrate` over the snapshot's sturdyref + the viewer's `Membrane`. This
   (a) verifies the attested scene (an unattested scene re-expands to *nothing*,
   regardless of caps), (b) derives the viewer's `Projection` = `(held) ∧ (lineage)`
   through the proven `is_attenuation` lattice, and (c) the derived `Rehydration`
   liveness-type. A failure here (an incomparable identity's `Amplification`, a
   tampered scene's `Fetch` error) means no bundle re-expands.
2. **fetch + decode the bundle, cross-check the frustum.** Fetch through the real
   attested `fetch_bundle` and confirm the bundle's manifest digest equals the
   snapshot's boundary digest — the cell did not drift from the frustum the snapshot
   was taken of (`BoundaryDigestMismatch` otherwise).
3. **per-asset attenuation.** Keep exactly the assets the viewer's *projected*
   fetch-allowlist permits, through the genuine `SurfaceCapability::may_fetch` over
   each asset's stable origin (`WebBundle::asset_origin(cell, name) =
   dregg-asset://<hex>/<name>`). A weaker viewer's re-expanded bundle carries fewer
   assets; the culled set is reported. This is the real cap meet, never a parallel
   filter.

So **a powerful viewer re-expands the full bundle; a weaker viewer an attenuated
projection (fewer assets — e.g. the privileged `admin.js` is culled); an
incomparable identity nothing.** Two agents opening "the same" DOM snapshot do not
re-expand identical bundles — each negotiates, across the real membrane, the assets
its capabilities authorize. The re-expansion is liveness-typed: a `LiveDomSnapshot`
whose source context's every external interaction was an attested turn re-expands
`ReplayedDeterministic` (the confined fragment), derived — not asserted.

## Transclusion at the DOM level — the web-level cascade

Ted Nelson's Xanadu promised **transclusion**: include-by-reference where the quoted
material keeps its identity and provenance — never copied-and-cut. dregg already
ships the missing piece — the verified cross-cell finalized read
(`transclusion.rs`'s `TranscludedField`). A web cell makes a *bundle fragment* the
unit of the quote.

`transclude_bundle_fragment(web, source, asset_name)` (`deos-web-cells::cascade`)
performs the real `TranscludedField::include` against the bundle cell — the genuine
`dregg://` attested finalized read + the `content→commitment→receipt→
receipt-stream-root→quorum` verification, which REFUSES a forged / absent /
un-finalized quote — then decodes the verified, attested bundle and extracts the
named asset's bytes. The result **`BundleFragmentQuote`** carries the verified
`TranscludedField` (so its provenance re-verifies at any time) + the asset name + the
fragment bytes + the genuine receipt-pinned `Provenance`. It is the **live quote**:
the honest, dated inclusion of a peer bundle's fragment into another surface. The
quote never rots — the citation pins an immutable receipt, so even after the source
advances, the quote remains the value committed at the cited point.

**This is how transclusion reaches the actual web.** A transcluded `dregg://` bundle
fragment rendered in a page is the live quote, and the pixels come from the
`servo-render` Stage-A cap-gated render pipeline
(`servo-render::fetch_render_present` — the servo Stage-A cap-gated render seam that
just landed). The fragment's bytes flow through the same `WebSurfaceDelegate` cap
gate (`load_web_resource`), so a transcluded fragment is subject to the embedding
surface's caps exactly as any subresource is — and the render→glass step rasterizes
it. The cascade:

```text
  dregg:// bundle cell ──TranscludedField::include──▶ verified attested bundle
        │  (content-addressed + receipt + quorum-signed root)
        ▼
  transclude_bundle_fragment ──▶ BundleFragmentQuote { fragment bytes + Provenance }
        │  (the live quote — honest, dated, recomputable)
        ▼
  embedding surface's cap gate (load_web_resource) ──▶ servo-render::fetch_render_present
        │  (Stage-A: cap-gate IN FRONT of the render)
        ▼
  pixels on the glass — the transcluded fragment rendered in a page
```

## The Leptos live-state-as-bundle angle

A Leptos app is a reactive signal-graph over a DOM. Its live state — the current
signal values + the effect graph — is exactly a "live DOM bundle." Publishing it as
a `LiveDomSnapshot` cell means:

- the **rendered view** (`index.html`) and the **serialized signal state**
  (`dom-state`, `application/dom-snapshot`) are assets of one bundle;
- the bundle is content-addressed, so the *exact* live state at the snapshot instant
  has a stable identity;
- it is cap-gated, so who may fetch/render it is the real cap discipline;
- it is transcludable, so another surface can include the `dom-state` fragment (the
  live quote of your app's state) with provenance;
- it is rehydratable per-viewer, so opening it re-expands the app's surface
  attenuated to what the viewer's caps authorize, liveness-typed.

The `deos-leptos` prototype (the reactive surface — how Leptos signals map to the
reactive rung; the SSR→hydrate shape) is where a *live* binding lands: capturing a
*running* signal-graph into a `LiveDomSnapshot` asset, and reactively re-expanding it
(when the source finalizes a new height, the signal re-fetches and the view
updates — the "live quote" as a Leptos signal). That live binding needs the in-flight
leptos crate and is the **named demonstrable follow-on**; the bundle + snapshot +
rehydrate + transclude core ships today against the stable API, with the
`LiveDomSnapshot` bundle as the concrete carrier the live binding will populate.

## Build status

- **STEEL (built, tested, in `deos-web-cells` — a standalone crate, own target, over
  the stable `starbridge-web-surface` API):**
  - the `WebBundle` data model (kind + entrypoint + assets), content-addressed by a
    canonical encoding (`content_hash`/`content_uri`/`manifest().digest()`);
  - `publish_bundle` (a bundle committed into a real `dregg://` surface cell — the
    cell's committed content hash IS the bundle's content hash) + `fetch_bundle` (the
    real attested cross-cell read + verify + decode); the cap tooth (a tampered / dead
    bundle yields no bytes);
  - the `DomSnapshot` frustum-snapshot (tiny — a `Sturdyref` + the `BundleBoundary`)
    + `rehydrate_bundle` (per-viewer re-expansion through the real `Membrane`, with
    per-asset attenuation via the real `may_fetch`): a powerful viewer the full
    bundle, a weaker viewer an attenuated projection, an incomparable identity
    nothing; the derived `Rehydration` liveness-type carried through;
  - `transclude_bundle_fragment` (a bundle fragment included into another surface,
    carrying the real receipt-pinned `Provenance`, via the real `TranscludedField`);
    a forged / absent / un-finalized / non-bundle source refused.
- **NAMED FOLLOW-ON (the demonstrable next step):** the *live* Leptos-signal binding
  — capturing a running `deos-leptos` signal-graph into a `LiveDomSnapshot` asset and
  reactively re-expanding it (the "live quote" as a Leptos signal). Rides this
  crate's `publish_bundle`/`rehydrate_bundle` + the `Rehydration` liveness-type; needs
  the in-flight leptos crate.
- **SEAM (named, not papered): the render.** Turning a re-expanded, attenuated bundle
  (or a transcluded fragment) into pixels is the `servo-render` Stage-A cap-gated
  pipeline (`servo-render::fetch_render_present`). This crate produces the
  cap-confined, attested, per-viewer bundle/fragment the renderer consumes; it does
  not itself rasterize DOM (the `MockSurface`/libservo seam
  `starbridge_web_surface::delegate` names).

*Cross-refs: `starbridge-web-surface/src/web_of_cells.rs` (the `dregg://` docuverse +
addressing) · `rehydrate.rs` (`Sturdyref`/`Membrane`/`Rehydration` — the
frustum-snapshot stack) · `transclusion.rs` (the verified cross-cell read NAMED as
Nelson's quote) · `DEOS.md` ("the frustum-culled snapshot — THE dregg-only novelty")
· `desktop-os-research/REHYDRATABLE-SURFACES.md` (the membrane model) ·
`servo-render/src/cap_gated_pipeline.rs` (the Stage-A cap-gated render — where the
pixels come from).*
