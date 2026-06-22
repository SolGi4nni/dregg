# REVIEW — Studio + Starbridge host surfaces

Date: 2026-06-06
Reviewer: subagent (review-first; no risky refactors applied)
Live node consulted read-only: `https://devnet.dregg.fg-goose.online` (solo, height 0,
3 faucet cells, 0 receipts, 3 committed events).

## Scope reviewed

- `web/starbridge-host/` — Rung-A self-contained Lean→wasm demo (index.html, app.js, tiny.mjs, tiny.wasm)
- `metatheory/site/index.html` — static marketing page (no studio/api wiring)
- `site/` (breadstuffs root) — the *real* studio + starbridge shell the proxy serves:
  - `site/src/_includes/studio/` (runtime-remote, starbridge.js, app-boot.js, inspectors barrel + 41 inspectors)
  - `site/src/studio.html`, `site/src/starbridge.html`
  - `site/pkg/` WASM package, `site/dist/` built artifacts
- `starbridge-apps/` (10 app bundles + `shared/`)

## Verdict

**Solid.** The studio runtime, starbridge shell, app-bundle wiring, WASM loading, and
node-API contract handling are all correct and contract-aware. No broken includes, no
stale `site/pkg` reference, no dead docs links, no orphaned/missing inspectors. Two
real issues, both **needs-build / non-trivial** (not blind-fixable):

1. `site/dist/` is **stale** relative to recent `site/src` edits (a rebuild, not a code fix).
2. `RemoteRuntime` cannot populate the live activity feed against the public node
   (relies on an SSE route the deployed node doesn't serve; `/api/events` — which carries
   the contract `proof_status` — is never polled as a fallback).

---

## Findings (prioritized)

### P1 — `site/dist/` is stale vs `site/src/` (needsBuild, MEDIUM)

`site/src/_includes/studio/{starbridge.js,inspectors.js,app-boot.js}` were edited
**2026-06-06 17:37**; `site/dist/_includes/studio/*` and `artifacts-manifest.json` were
built **17:14** — *before* those edits. Confirmed by content diff (not just mtime):

- `site/src/_includes/studio/starbridge.js` vs `site/dist/...` — **differ**
  (src adds the in-memory `installRealSignTurn()` + turn-builders barrel import at ~L2038;
  dist lacks it). file:line `site/src/_includes/studio/starbridge.js:2038`
- `site/src/_includes/studio/inspectors.js` vs dist — **differ**
  (src adds `import('/starbridge-apps/shared/turn-builders/index.js')` at L326)
- `site/src/_includes/studio/app-boot.js` vs dist — **differ**
  (src adds `installRealSignTurn()` block at ~L267)
- `starbridge-apps/shared/runtime-submit.js` and `starbridge-apps/shared/turn-builders/index.js`
  (both dated 17:37) **differ** from their `site/dist/starbridge-apps/shared/...` copies.

Impact: the deployed `dist` serves the *pre-edit* studio. The new real-submit wiring
(`runtime-submit.js` / turn-builders barrel) that the src now imports is absent from the
served bundle. Not a code bug — `dist` simply needs to be rebuilt and re-deployed.

**Fix (needsBuild):** `./scripts/build-web-artifacts.sh` (or `node site/build.js`) then
re-`rsync site/dist/`. Do NOT hand-edit dist. The build copies `_includes/studio/` and
`../starbridge-apps` into dist verbatim (see `site/build.js:61,382`), so a plain rebuild
resolves it.

### P2 — RemoteRuntime never polls `/api/events`; live activity feed stays empty (needsBuild/feature, MEDIUM)

`site/src/_includes/studio/runtime-remote.js:62-73` opens an `EventSource` on
`${base}/observability/stream` to populate `traceEventsSignal` (consumed by
`inspectors/activity.js:134` via `getTraceEvents()`). On the **live public node** that
route returns the static SPA HTML (404 fallthrough) rather than an SSE stream — verified:

```
$ curl -H 'Accept: text/event-stream' .../observability/stream  →  <!doctype html> ...
```

The node *does* expose the route in current source (`node/src/api.rs:1198`), so the
deployed gateway is an older build — but regardless, the contract's `proof_status`-bearing
data is available at `/api/events`, which works live:

```
$ curl '.../api/events?limit=1'
[{"height":3,"status":"committed","proof_status":"not_required","turn_hash":"bbf5…","cell_id":"112b…","effects":["faucet_transfer:1000"],"timestamp":1779848192}]
```

`runtime-remote.js:189-200` polls `/status`, `/api/cells`, receipts, blocks, federations,
intents, tokens — but **not** `/api/events`. So with no extension bridge and no SSE, the
studio's `<dregg-activity>` panel shows nothing even though the node has committed,
`proof_status`-tagged events. The CORS reality note at `runtime-remote.js:19-23` partly
covers this (Caddy CORS), but the missing `/api/events` poll is the structural gap.

**Recommendation (not applied — non-trivial):** add `/api/events?limit=…` to the
`pollOnce()` `Promise.all` and map the array (`{height,status,proof_status,turn_hash,
cell_id,effects,timestamp}`) into the `traceEventsSignal` `{schema_version,event_count,
events}` shape as an SSE/extension fallback. file:line `runtime-remote.js:187`. Verify in
a browser against devnet before shipping (hence needsBuild).

### P3 — `/api/receipts/{hash}/witnesses` is never fetched by the studio (LOW, by-design today)

The contract's canonical witness endpoint (`/api/receipts/{hash}/witnesses` →
`witnessed_receipts[]` + `artifact_format:"DWR1"`/`witness_artifacts[]`) is **not** called
anywhere in the studio. The witnessed-receipt inspector
(`inspectors/witnessed-receipt.js:41-50`) and `normalizeReceipts`
(`runtime-remote.js:503-533`) correctly *consume* `artifact_format`/`witness_artifacts`/
`witness_count`/`has_witness` **inline**, but those fields only arrive if the receipt-list
endpoint already embeds them. Today `/api/receipts` and `/api/starbridge/receipts` return
`[]` (height 0), so nothing is exercised. Scope-2 ("inline WitnessBundle / DWR1 artifacts")
will only light up if the list endpoint inlines the artifacts; otherwise the per-receipt
witnesses endpoint must be fetched on demand.

**Recommendation (not applied):** when a receipt reports `has_witness && witness_count>0`
but carries no inline `witness_artifacts`, lazily GET `/api/receipts/{turn_hash}/witnesses`
and merge `artifact_format`/`witness_artifacts` into the receipt signal. Otherwise Scope-2 /
Golden tiering is unreachable against a node that doesn't inline. file:line
`runtime-remote.js:317` (`getReceipt`). Needs a live node with persisted witnessed receipts
to verify (none on devnet yet).

---

## Things checked that are CORRECT (no action)

- **WASM package reference** — `site/studio.html:135` imports `/pkg/dregg_wasm.js`; the file
  + `dregg_wasm_bg.wasm` (3.99 MB) exist in both `site/pkg/` and `site/dist/pkg/`. Not stale.
- **Height field** — `runtime-remote.js:458` lists `latest_height` **first** in the
  `pickHeight` candidates, matching the live node's `{"latest_height":0,…}` `/status` shape;
  explorer agrees (`site/explorer/app.js:154`).
- **`proof_status`** — live `/api/events` exposes it per contract; explorer + activity
  inspector understand the `ActivityProofStatus` vocabulary.
- **Receipt contract fields** — `normalizeReceipts` synthesizes/forwards `receipt_hash`,
  `turn_hash`, `has_witness`, `witness_count`, `artifact_format:"DWR1"`, `witness_artifacts`
  exactly per the deploy README contract (`runtime-remote.js:503-533`).
- **Starbridge-app bundle wiring** — all 10 app ids in `STARBRIDGE_APP_IDS`
  (`starbridge.js:14`) have a real `manifest.json`; 6 ported apps (nameservice, identity,
  governed-namespace, subscription, compartment-workflow-mandate, storage-gateway-mandate)
  each have `pages/index.html`; the 4 legacy apps (bounty-board, gallery, privacy-voting,
  compute-exchange) declare `page:null` and the host correctly suppresses their href
  (`starbridge.js:470`). Manifest fetch + fallback path are sound (`starbridge.js:441-456`,
  `app-boot.js:87-100`).
- **Shared modules** — `starbridge-apps/shared/{runtime-submit.js,turn-builders/index.js,
  inspectors/index.js,app-runtime-ready.js}` all exist; the new `inspectors.js`/`app-boot.js`/
  `starbridge.js` imports of them are `.catch()`-guarded (`inspectors.js:325-327`).
  nameservice page imports (`pages/index.html:89-104`) all resolve.
- **Inspector barrel** — 41/41 imported inspectors present; none missing, none orphaned
  (`inspectors.js`).
- **Docs links** — every `/learn/*` link in `index.html`, `learn.html`, `docs.html`
  resolves to an existing `site/src/learn/.../*.html`; `/apps.html` exists. No dead links.
- **`runtime-submit.js`** — routes turns through the in-memory WASM `TurnExecutor` (local
  preview), returns `turn_hash`-keyed receipts; consistent with the read-only RemoteRuntime
  (all node-side mutations `notPermitted`).
- **starbridge-host (Rung A)** — `app.js` boots `tiny.mjs`+`tiny.wasm` (both present),
  honest pass/fail (sum===42n && prod===42n), no node-API dependency. Self-contained, fine.
- **metatheory/site/index.html** — pure static marketing; no studio/api/wasm wiring; nothing
  to break.

## Safe fixes applied

None. The two real issues are a rebuild (P1) and a non-trivial feature add (P2/P3); the
rest is already correct. No typos/dead-links/wrong-endpoints were found that warranted a
trivially-safe edit.
