# The Visitor-Side Verification Weld

*Grounded 2026-07-08 (two scouts, file:line receipts). Goal: make this sentence deployed fact,
not design goal: "a visitor's browser independently checks that bytes served from `*.dregg.works`
match the site's on-ledger commitment; a tampering host cannot strip the check."*

## Ground truth (verified live, 2026-07-08)

- `hello.dregg.works` serves **plain HTML, no verifier** — byte-verbatim from the DreggNet
  gateway's `SiteRegistry` (`~/dev/DreggNet/webapp/src/hosting.rs:221-240`; live-probed).
- Its commitment is the gateway's **off-ledger** ed25519 receipt chain over a Poseidon2
  content-root (`webapp/src/hosting.rs:1036-1096`, `SiteRegistry::signed` :746-767). The
  `/.well-known/dregg-receipt.json` trustless-read exists only in the portable binaries — the
  deployed gateway never dispatches it (live probe: 404).
- The **on-ledger** publish path is real and live in breadstuffs — `publishMinisite`
  (`portal/src/drive-actions.mjs:65-83`): a cap-gated signed turn writing
  `SITE_CONTENT_SLOT(0) = blake3(bytes)` per `starbridge-web-surface/src/web_of_cells.rs:10-21`
  — **but nothing currently served on `*.dregg.works` was published through it.**
- `site/dregg-works/verify-badge.js` has the whole check (verified standalone blake3 →
  `GET /api/cell/{id}` → compare `fields[0]`, refuse-on-mismatch) but is **page-delivered and
  page-configured** — strippable AND cell-swappable. Its default node is the dead devnet.

## The two-sided architecture — one core, two skins

A page cannot verify itself: a tamperer strips (or re-points) anything the host serves. The
checker must live in something the **visitor** installed:

1. **Their browser → the extension** (`extension/` — the MV3 cipherclerk; builds clean, TS
   green, wasm bundle already exports `blake3_hash`; rot is *endpoint defaults only*).
2. **Our browser → the starbridge servo pane** — verification as a property of *loading*:
   bytes hashed at the net-cap choke point, verdict chip in-band, fail-closed option.
   (Servo scout in flight; section below to be grounded when it reports.)

Both consume one verification core: `fetch bytes → blake3 → read committed slot 0 → compare →
verdict`, with the same refusal discipline (a failed check is never a pass).

## The load-bearing security decision: hostname → cell binding

Page-supplied cell ids (`data-cell`, meta tags) are not merely strippable — they are
**swappable**: a tamperer points the check at their own cell whose slot 0 matches the tampered
bytes. verify-badge.js is defeated this way *even when present*. The binding must be
out-of-band: an extension-held mapping seeded from **one pinned registry cell id** shipped in
extension defaults (genesis-anchor pattern), whose slots/events carry `name → site-cell-id`.
The on-ledger vocabulary exists (`starbridge-apps/nameservice`, `starbridge-apps/domains`);
the name→cell *read endpoint* does not yet.

## What already works (don't rebuild)

- Node `GET /api/cell/{id}` is public and returns `fields[]` (`node/src/api.rs:1594`, :4035);
  CORS **always admits `chrome-extension://` / `moz-extension://` origins** (`api.rs:1484-1488`)
  — zero manifest/server changes needed for the extension's commitment read.
- Extension chassis: content script on `<all_urls>` at `document_start`, background node-fetch
  plumbing, settings-page endpoint override (`extension/src/endpoints.ts:19-23`).
- Tab-side LC scaffolding: `verify_slot_opening` (`wasm/src/bindings_lightclient.rs:726-775`)
  reproduces the heap-path fold; the portal cell page already consumes openings gracefully
  (`portal/dist/cell.html:126-141`). Missing half = the node serving per-slot openings.

## The plan, effort-ranked

1. **Endpoint-default sweep (hours).** Kill dead `devnet.dregg.fg-goose.online` defaults:
   `extension/src/endpoints.ts:17`, `extension/manifest.json:19-20`,
   `site/dregg-works/verify-badge.js:142`, `transclude.js:158`, `sdk/src/endpoints.rs:53`.
   Point at the live read surface (portal.dregg.studio/api or a dedicated node host).
2. **The extension verifier module (a day).** On `*.dregg.works`: content script re-fetches
   `location.href` (`cache: "no-store"`, same-origin, no new permissions) → background blake3
   (bundled wasm) → `GET <node>/api/cell/<cell>` (node base from settings, never the page) →
   compare → per-tab action badge ✓/✕ + mismatch overlay. Lift verify-badge.js's check logic
   verbatim; its trust anchoring is exactly what moving into the extension fixes.
3. **Hostname→cell binding (days — the real design work).** Pinned registry cell + name-lookup
   read (node endpoint or client-side registry-event scan). Without this the weld is spoofable.
4. **Publish/serve unification (days).** A breadstuffs-native site-serving path (DreggNet is
   abandoned-as-product; no `SiteRegistry` port exists yet) so the flagship `*.dregg.works`
   sites are the SAME bytes committed by the on-ledger blake3 slot-0 turn. Serve is already
   byte-verbatim, so this is publish-plumbing, not a format change.
5. **LC-verifiable commitment read (a lane).** Node endpoint serving per-slot heap openings;
   tab side is ready. Until then the commitment read is trusted-node — mitigate by querying
   ≥2 nodes and cross-checking, and SAY "trusted-node" in the extension UI.
6. **Multi-asset manifest discipline (later).** Slot 0 = blake3 of a path→blake3 manifest;
   verify manifest, then each fetched asset. DreggNet's content-root/`dregg-deploy` manifest is
   the design reference (but Poseidon2/off-ledger — don't import wholesale).

## The starbridge-native half (grounded 2026-07-08)

**The byte socket is already ours.** The vendored servo-net fork removed http/https from
`FORBIDDEN_SCHEMES`; `CapGatedHttpHandler` (`servo-render/src/netcap_http.rs:75-296`) owns the
whole http(s) fetch — in `load` (:206) the entire response body sits in our hands as
`HttpFetch { status, content_type, body }` (:275-291) *before servo lays anything out*. Hashing
is one `blake3(&body)` line. It already keeps per-fetch audit state to extend into a manifest.

**The gap is one wiring**: the live web-shell pane's `LiveWebView::new` builds servo with **no
`protocol_registry`** (`servo-render/src/webview.rs:1056-1058`), so its bytes still ride servo's
internal hyper. `CapGatedHttpEngine::new` (:556-571) already shows the 6 lines that register the
handler. Mind the one-engine-per-process `OnceCell` (:1049-1051): the registry must be installed
at first engine build — on from the start of the cockpit session.

**dregg:// is the already-closed leg**: `WebCellsBrowser` fetches through `AttestedResource::verify`
(`starbridge-web-surface/src/web_of_cells.rs:138` — blake3 content hash, receipt-in-stream,
Merkle root, quorum sigs) and only then hands bytes to `render_dregg_page` — verify-then-render,
the exact shape wanted everywhere. The "✓ attested / ⚠ unattested" chips exist
(`cockpit/panels_web.rs:249-252`). Remaining: route the *remote* dregg:// fetch (`NodeWorldSink`)
through the same verify.

**Fail-closed is structurally available**: on mismatch, return `Response::network_error(...)`
from the handler — exactly the existing `RefusedByCap` arm (`netcap_http.rs:232-237`) — making a
tampered page **unrenderable**, not merely badged. UX slots all exist: web-shell status line
(`panels_webshell.rs:709-726`), the kept-tile fail-closed precedent (:298-303), the toolbar for
a verdict chip + fail-closed toggle (:646-706), the `OriginChrome` anti-phishing badge pattern.

**The shared core**: `dregg-page-verify` (blake3 content check + node commitment read + verdict
vocabulary; upgrade rungs = `AttestedResource::verify_anchored` quorum leg, then the whole-history
lightclient anchor `lightclient/src/lib.rs:188/:579`), compiled twice — native for the handler,
wasm for the extension — on the exact `grain-verify`/`grain-verify-wasm` precedent ("reimplements
NO check"). verify-badge.js remains the zero-install fallback skin.

**Native effort ladder**: verdict chip (small) → hash-in-handler + manifest (small/medium) →
LiveWebView takes the registry (medium) → dregg-page-verify crate + extension skin (medium) →
in-cockpit trust story for the commitment read: multi-node cross-check → LC anchor (medium/hard)
→ multi-asset manifest (hard design, shared with rung 6 above; `WebBundle::asset_origin` is a
starting shape).

Churn note: `panels_webshell.rs:49-56`'s module doc still says the fork is out of reach — stale;
`netcap_http.rs` landed it. Trust the code.

## Honest UI language (binding, per the register)

Until rung 5: the extension says "checked against a node you chose" (trusted-node), never
"proven". Until rung 4: `*.dregg.works` flagship pages say "commitment: gateway receipt chain"
distinctly from "commitment: public ledger". The site copy at dregg.net/try and /deep already
carries this split (corrected 2026-07-08, twice).
