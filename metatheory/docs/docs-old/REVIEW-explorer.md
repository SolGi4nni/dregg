# REVIEW — Block Explorer web surface

Reviewed: 2026-06-06. Surface: `site/explorer/` (`app.js`, `index.html`,
`style.css`) plus the studio substrate it consumes
(`site/src/_includes/studio/runtime-remote.js` and the `<dregg-*>` inspectors).
Live node probed read-only: `https://devnet.dregg.fg-goose.online` (solo,
`latest_height:0` per `/status`, but with committed faucet events at heights
1–3 and 3 cells).

## TL;DR

The explorer is **structurally sound and honest** — it is a thin chrome over a
`RemoteRuntime` that polls the node API and feeds shared inspectors. Endpoint
paths are correct (verified against `node/src/api.rs` route table and the live
node). Empty/offline states render honestly. **No dead/wrong endpoint paths.**

The real issues are two **contract under-consumption gaps**: the explorer never
calls the dedicated witness endpoint, and never consumes the committed-event
history (`/api/events` with `proof_status`). Both mean correct node data is
silently dropped in the UI. Neither is a crash; both are "the data is there but
the explorer can't show it."

One trivially-safe fix was applied (`pickHeight` missing `latest_height`).

## Architecture (so the findings make sense)

`site/explorer/app.js` mounts one `<dregg-app>` whose `.runtime` is a
read-only `RemoteRuntime` (`createRemoteRuntime`, base URL from localStorage,
default `http://localhost:8420`). Every page is a platform `<dregg-*>`
inspector resolving `dregg://` URIs through that runtime. All node-API
consumption lives in `runtime-remote.js` `pollOnce()` (`site/src/_includes/studio/runtime-remote.js:187`).

Canonical sources are `site/explorer/` and `site/src/_includes/studio/`; the
build (`site/build.js`) copies `explorer/` verbatim and `src/_includes/studio/`
into `dist/`. (`site/_includes/studio/` — the path the import string resolves to
at runtime — is a STALE partial copy missing `runtime-remote.js`; harmless on
the deployed `dist/` tree but a footgun for local `site/`-root serving. See
finding F6.)

## Findings (prioritized)

### F1 — [HIGH] Witnessed-receipt DWR1 view can never trigger from list data
`site/src/_includes/studio/runtime-remote.js:508` (`normalizeReceipts`) derives
`witness_artifacts` / `artifact_format:"DWR1"` from the **receipt-list** payload
(`/api/starbridge/receipts` → `StarbridgeReceiptInfo`, or `/api/receipts` →
`ReceiptInfo`). Those node structs (`node/src/api.rs:129`, `:430`) expose
`has_witness` and `witness_count` but **do NOT inline `witness_artifacts` or
`artifact_format`**. The DWR1 hex blobs live ONLY behind the dedicated endpoint
`GET /api/receipts/{hash}/witnesses` (`node/src/api.rs:1554`), which the
explorer/runtime **never calls**.

Consequence: in `<dregg-witnessed-receipt>` (`witnessed-receipt.js:47`),
`r.artifact_format === 'DWR1' && r.witness_artifacts.length > 0` is always
false, so the scope-2 "Witness Bundle / DWR1 artifacts" pane never renders even
for a receipt that genuinely has persisted witnesses. The fallback
`witness_count > 0 && has_witness` (`:48`) does still flip scope to 2 and shows
"N artifacts" in the summary, but the actual DWR1 artifact list pane
(`WitnessBundlePane`, `:175`) gets `r.witness_artifacts` = `[]` and renders an
empty/placeholder bundle.

Fix (needs build/test — see needsBuild): on opening a single receipt, the
runtime's `getReceipt(hash)` should lazily `getJSON('/api/receipts/${hash}/witnesses')`
and merge `witnessed_receipts` + `artifact_format` + `witness_artifacts` into the
receipt signal. The endpoint returns exactly the inspector's expected shape
(verified live: `{"receipt_hash","witness_count","artifact_format":"DWR1","witness_artifacts":[...],"witnessed_receipts":[...]}`
when non-empty; the DWR1 keys are omitted when `witness_count:0`). This is the
single most contract-relevant gap.

### F2 — [MEDIUM] Activity page ignores `/api/events` history + its `proof_status`
The Activity page binds to `runtime.getTraceEvents()`
(`activity.js:134`), which is fed ONLY by the SSE `/observability/stream`
(`runtime-remote.js:62`) or the extension feed. That stream is **live-only** —
it carries no backlog. On the live solo node the committed activity is at
`/api/events` (verified: heights 1–3, each
`{"status":"committed","proof_status":"not_required","turn_hash",...,"effects":[...]}`),
which the explorer **never fetches**. So a freshly-loaded Activity page shows
"No observability events yet" even when the chain has committed turns, and the
contract field `proof_status` is never surfaced anywhere in the explorer.

Note the two event surfaces have *different shapes*: `/observability/stream`
emits `{kind, envelope, payload}` TraceEvents; `/api/events` emits
`CommittedEvent {height, status, proof_status, turn_hash, cell_id, effects,
timestamp}`. A faithful fix would poll `/api/events` and render committed
history (with a `proof_status` badge) alongside / seeded-before the live SSE
tail. (needsBuild — new rendering path + shape adapter.)

### F3 — [LOW, FIXED] `pickHeight` missing `latest_height`
`runtime-remote.js:455` `pickHeight()` tried `height|block_height|tip_height|head_height|cursor`
but NOT `latest_height` — the field the live `/status` actually returns
(`node/src/api.rs` `StatusResponse`; verified live `{"latest_height":0,...}`).
So the runtime `cursor` signal and the synthesized federation `height`
(`normalizeFederation`, `:585`) never advanced off 0, and the
federation-list/overview "height" derived from the runtime read 0 even at
height>0. (The header chrome was unaffected — `app.js` `updateStatusChrome:154`
already reads `latest_height` first.)
**Applied:** prepended `'latest_height'` to the `pickHeight` candidate list in
both `src/_includes/studio/runtime-remote.js` and the built
`dist/_includes/studio/runtime-remote.js`. Purely additive ordered-fallback;
no behavior change for nodes that used the other field names.

### F4 — [LOW] Stale CORS warnings in code/UI vs. live permissive CORS
`runtime-remote.js:163` and `index.html:60,472` warn that remote nodes "only
allow localhost/extension origins by default (CORS)". The live devnet now
returns `access-control-allow-origin: *` on every response (verified), so a
browser at any origin CAN reach it directly. The warnings are not wrong as a
general statement but are misleading for the actual devnet target and may push
users toward the extension unnecessarily. Cosmetic; left as-is (changing copy is
a judgment call for ember, and the guidance is technically still true for a
default-config node).

### F5 — [LOW] `/api/blocklace/blocks`, `/api/tokens`, `/api/federations` 404 on live node
Verified live: `/api/blocklace/blocks` → 404, `/api/tokens` → 404,
`/api/federations` → 404 on the current devnet build. The runtime handles these
gracefully:
- blocks: `getFirstJSON(['/api/blocklace/blocks','/api/blocks','/federation/roots'])`
  (`:196`) falls through to `/api/blocks` (returns `[]`). OK.
- tokens/federations: 404 → `getJSON` returns null → cached value retained,
  federation list synthesized from `/status` (`normalizeFederations:577`). OK —
  Capabilities page will simply be empty, which is honest for a node with no
  exposed tokens.
No fix needed; noting so the empty Capabilities/Federation pages aren't mistaken
for a bug. (These 404s are a node-deploy/route-gating matter, not an explorer
bug.)

### F6 — [LOW] Stale duplicate `site/_includes/studio/` tree
`site/_includes/studio/` exists as an older partial copy (has `inspectors.js`,
`starbridge.js`, etc. but **no `runtime-remote.js`**). The explorer imports
`../_includes/studio/runtime-remote.js`; on the deployed `dist/` tree this
resolves to the freshly-built copy, but anyone serving the repo `site/` root
directly would get a 404 on the runtime and a dead explorer. Recommend deleting
`site/_includes/studio/` (canonical source is `site/src/_includes/studio/`) or
documenting that only `dist/` is servable. Not touched — deletion is a
repo-hygiene call, not a trivially-safe inline edit.

### F7 — [INFO] Receipt-list endpoint preference is correct
`pollOnce` prefers `/api/starbridge/receipts?limit=100` then `/api/receipts`
then `/api/receipts/recent` (`:192`). All three normalize through
`normalizeReceipts`, which correctly reads `turn_hash`, `receipt_hash`,
`has_witness`, `witness_count` (contract fields all present — verified vs
`ReceiptInfo`/`StarbridgeReceiptInfo`). `/api/receipts/recent` is NOT a real
route (`node/src/api.rs` has `/api/receipts` and `/api/starbridge/receipts`
only) but it's a harmless last-resort fallback that 404s → null. Live
`/api/starbridge/receipts` returned `[]` (no receipts yet); shape unverifiable
against a populated node here, but matches the struct.

## Contract conformance summary (vs deploy/aws/README.md)
- `receipt_hash`, `turn_hash`, `has_witness`, `witness_count`: **consumed
  correctly** by `normalizeReceipts` and surfaced in inspectors. ✓
- `/api/receipts/{hash}/witnesses` → `witnessed_receipts` + `artifact_format:"DWR1"`
  + `witness_artifacts`: endpoint EXISTS and returns the contract shape (verified
  live), but the explorer **never calls it** → DWR1 artifacts unrenderable from
  the network. ✗ (F1)
- committed activity `proof_status`: present on `/api/events` (live-verified) but
  the explorer **does not consume `/api/events`** at all. ✗ (F2)

## Fixes applied (trivially safe)
- F3: `pickHeight` now includes `latest_height` (src + dist).

## Recommendations for ember (need build/test — do NOT apply blind)
- F1: lazy-fetch `/api/receipts/{hash}/witnesses` in `getReceipt`/`getTurn`,
  merge into the receipt signal so `<dregg-witnessed-receipt>` can render real
  DWR1 artifacts. Highest value.
- F2: poll `/api/events`, render committed history (+`proof_status` badge),
  reconcile with the live SSE tail; current Activity page is misleadingly empty
  at height>0.
- F6: remove the stale `site/_includes/studio/` tree (or document dist-only).
- F4: optionally soften the devnet CORS warning copy now that devnet sends `*`.
