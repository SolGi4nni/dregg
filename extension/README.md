# `dregg` Cipherclerk Extension

Browser extension (Manifest V3, Chrome + Firefox) for capability-based agent
identity in `dregg`: it manages signing keys, capability tokens, and authorization
with zero-knowledge proofs, and signs/submits turns to a `dregg` node.

## What it does

- **Agent identity / keys** — generates a BIP39-style recovery phrase on first
  run, derives an Ed25519 keypair (BLAKE3 seed) via WASM, and stores state
  encrypted at rest (PBKDF2 + AES-256-GCM). Auto-locks after inactivity.
- **Capability tokens** — sites provision tokens (user-confirmed); the
  cipherclerk evaluates authorization against them via a WASM datalog engine.
- **Turn signing** — `signTurnV3(turnBytes)` signs a pre-built postcard-encoded
  Turn with the canonical `AgentCipherclerk::sign_action` path and submits it to
  the node's `/turns/submit` (with a durable offline outbox + retry/backoff).
- **Privacy** — selective disclosure + ZK predicate (range) proofs, stealth
  addresses, committed private transfers.
- **CapTP / directory / storage / federation** — share/accept sturdy refs,
  mount + discover services, content-addressed storage, and federation
  proposals/votes — all routed through the node.
- **Live activity** — subscribes to the node WebSocket (authenticated) for
  receipt/root/revocation/intent/note events, surfaced via `dregg.on(...)`.

## Architecture

```
Page Context               Content Script            Background SW
+-----------------+        +----------------+        +--------------------+
| window.dregg    |        |                |        | Cipherclerk state  |
|   .authorize()  | =====>  | nonce-scoped   | =====>  | - Ed25519 keys     |
|   .signTurnV3() |         | CustomEvent    |         | - capability tokens|
|   .isConnected()| <=====  | bridge +       | <=====  | - receipt chain    |
|   .on(...)      |         | origin allowlist|        | - datalog / ZK     |
+-----------------+         +----------------+         | - WASM crypto      |
   src/page.ts              src/content.ts             | - node WS + outbox |
                                                       +--------------------+
                                                          src/background.ts
```

## Build

The service-worker / content / page / popup logic is TypeScript bundled with
esbuild (IIFE, no ESM — Firefox MV3 background compatibility); the crypto core
is a Rust `wasm32-unknown-unknown` crate compiled with `wasm-bindgen`
(`--target no-modules`, JS snippets inlined for service-worker compatibility).

```sh
npm install              # esbuild + typescript + @types/chrome
npm run typecheck        # tsc --noEmit
npm run build            # esbuild -> dist/{background,content,page,popup-script}.js
./build.sh wasm          # cargo + wasm-bindgen -> dregg_wasm.js + dregg_wasm_bg.wasm
./build.sh package       # validate manifests + zip Chrome .zip / Firefox .xpi
```

`npm run build` is required after any change under `src/`; the committed `dist/`
must match a fresh build. `./build.sh wasm` is only needed when the Rust `wasm/`
crate changes.

## Load unpacked

- **Chrome**: `chrome://extensions` → Developer mode → Load unpacked → this dir.
- **Firefox**: `about:debugging` → This Firefox → Load Temporary Add-on →
  `manifest-firefox.json` (or the packaged `.xpi`).

## Files

- `manifest.json` / `manifest-firefox.json` — MV3 manifests (storage, activeTab,
  contextMenus; `wasm-unsafe-eval` CSP for the WASM module).
- `src/background.ts` — service worker: cipherclerk state, authorization,
  proof/turn building (via WASM), node HTTP + WebSocket, durable outbox.
- `src/content.ts` — bridges page events to the background, enforces the
  per-origin/per-method allowlist.
- `src/page.ts` — defines the `window.dregg` API in page context.
- `src/popup-script.ts` + `popup.html` — toolbar popup UI.
- `settings.html` / `settings-script.js` — node configuration page.
- `provision`/`recovery`/`confirm-intent`/`disclosure-picker`/
  `origin-permission`/`share-capability` `.html` + `.js` — user-decision popups
  (opened by the background with an opaque nonce; PII stays in background memory).
- `dregg_wasm.js` + `dregg_wasm_bg.wasm` — wasm-bindgen glue + compiled crypto.
- `bip39_english.txt` — BIP39 wordlist for the recovery-phrase fallback path.
- `tests/` — Playwright e2e tests (load the unpacked extension in Chromium).

## Page API (selected)

```js
const connected = await window.dregg.isConnected();

// Sign + submit a pre-built postcard-encoded Turn (the canonical path).
const res = await window.dregg.signTurnV3(turnBytes); // { turnId, submitted, queued? }

// Authorize an action against held capability tokens.
const auth = await window.dregg.authorize({
  action: "read",
  resource: "/data/x",
  mode: "private", // "trusted" | "selective" | "private"
});

// Live node events.
window.dregg.on("receipt", ({ hash }) => { /* ... */ });
```
