# `dregg` Cipherclerk Extension

Browser extension (Manifest V3, Chrome + Firefox) that is a citizen's
cipherclerk for `dregg`: it holds named signing identities, shows you exactly
what a turn does before it signs, submits signed turns to a node, and listens
to the node's receipt stream so you can see what committed.

## What it does

- **Named identity profiles** — an identity is a *name you chose*, not a hex
  key you pasted. The popup carries a profile switcher; every signing path
  reads the active profile's Ed25519 key. Key derivation is the same as the
  CLI/SDK profile store (`dregg id create / list / use`):
  `blake3 derive_key("dregg/0", seed)` → Ed25519. The golden derivation vector
  (seed `00..3f` → pubkey `335840a9…8b9a`) is pinned in three places —
  `sdk/src/profiles.rs`, `cli/src/commands/id.rs`, and this extension's
  `test/derivation.test.mjs` — so any drift fails all three test suites.
- **Authorization-first signing** — `signTurnV3(turnBytes, federationId?)`
  never signs blind. The clerk decodes the turn and renders a faithful reading
  of every action and effect (`src/explain.ts`, the same human terms
  `sdk/src/explain.rs` uses, e.g. "transfer 5 computrons from cell … to cell
  …"), bound to the canonical `[turn <hash>]` — the `Turn::hash` the node
  verifies and the receipt commits. The reading is shown in a nonce-bound
  confirmation popup; only explicit acceptance releases the signature. Effects
  the clerk cannot read are surfaced as UNKNOWN with a do-not-sign-blind
  warning, never elided.
- **Federation-domain binding** — the optional second `signTurnV3` argument is
  the exact 32-byte federation domain the v3 action signing message binds
  against (`dregg-action-sig-v2` domain separation; prevents cross-federation
  replay). It is validated twice (page bridge + background, exact type /
  32-byte length / integer 0..=255 elements — `src/federation-domain.ts`)
  before anything is signed; omission keeps the backward-compatible all-zero
  devnet/sim genesis domain. The confirmation popup shows the FULL 64-char
  lowercase hex of the domain that was signed, the nonce-bound decision echoes
  it back (a substituted domain is refused as a decline), and a queued
  submission retains it in outbox metadata so a retry can never silently fall
  back to zero. Advertised as
  `window.dregg.capabilities.signTurnV3FederationDomain ===
  "dregg-sign-turn-v3-federation-domain/v1"` (frozen) — the capability
  DreggCloud requires before handing a nonzero owner-lifecycle domain to a
  browser provider (see DreggCloud `docs/OWNER-LIFECYCLE-BROWSER-SEAM.md`).
- **Receipt as the result noun** — the signed turn travels as the node's
  `SignedTurn` envelope (postcard bytes, `POST /api/turns/submit-signed`,
  with a durable offline outbox + retry/backoff), and the result carries the
  node's receipt fields: turn hash, proof status, witness count.
- **The receipt stream** — the background tails the node's
  `GET /api/events/stream` (SSE), filtered to the active profile's cell when
  derivable. New receipts raise a toolbar badge count and appear in the
  popup's recent-receipts list (hash, effect kinds, finality, height, proof
  bit); opening the list clears the badge. Reconnects send `Last-Event-ID`
  (the receipt-chain index) so nothing is missed across drops.
- **Keys at rest** — a BIP39 recovery phrase per profile, Ed25519 derived via
  WASM, state encrypted with PBKDF2 + AES-256-GCM, auto-lock after inactivity.
  First-run onboarding **requires** setting a passphrase and confirming the
  recovery-phrase backup before any key is created — a wallet is never held
  under an ephemeral key that a browser restart could orphan.
- **Capability tokens** — sites provision tokens (user-confirmed); the
  cipherclerk evaluates authorization against them via a WASM datalog engine.
- **Privacy** — selective disclosure with **ZK range predicate proofs**
  (Bulletproofs over Ristretto, collision-resistant), stealth addresses, and
  committed private transfers. STARK Merkle-*membership* proof composition is
  **disabled**: its current `MerkleStarkAir` hash binding is not
  collision-resistant (forgeable), so it is not shipped as a usable feature
  until the circuit moves to a Poseidon2 Merkle hash.
- **CapTP / directory / storage / federation** — share/accept sturdy refs,
  mount + discover services, content-addressed storage, and federation
  proposals/votes — all routed through the node.
- **Live activity** — subscribes to the node WebSocket (authenticated) for
  revocation/root/intent/note events, surfaced via `dregg.on(...)`; committed
  receipts arrive via the SSE receipt stream.

## Architecture

```
Page Context               Content Script            Background SW
+-----------------+        +----------------+        +--------------------+
| window.dregg    |        |                |        | Profiles (named    |
|   .authorize()  | =====>  | nonce-scoped   | =====>  |  Ed25519 keys)     |
|   .signTurnV3(  |         | CustomEvent    |         | explain + confirm  |
|     turnBytes,  |         | bridge +       |         |  (+ full 64-hex    |
|     federationId?)| <===== | origin allowlist| <=====  |  federation domain)|
|   .capabilities |         |                |        | capability tokens  |
|   .on(...)      |         |                |        | datalog / ZK (WASM)|
+-----------------+         +----------------+         | SSE receipt stream |
   src/page.ts              src/content.ts             | node WS + outbox   |
                                                       +--------------------+
                                                          src/background.ts
```

The node surface the background speaks is the gateway-reachable `/api/`
prefix: `/api/node/status`, `/api/cell/{id}`, `/api/turns/submit-signed`,
`/api/events/stream`, `/api/receipts/{hash}/witnesses`, `/api/faucet`,
`/api/turns/bearer-auth`, `/api/turns/peer-exchange`.

## Build

The service-worker / content / page / popup logic is TypeScript bundled with
esbuild (IIFE, no ESM — Firefox MV3 background compatibility); the crypto core
is a Rust `wasm32-unknown-unknown` crate compiled with `wasm-bindgen`
(`--target no-modules`, JS snippets inlined for service-worker compatibility).

```sh
npm install              # esbuild + typescript + @types/chrome
npm run typecheck        # tsc --noEmit
npm run build            # esbuild -> dist/{background,content,page,popup-script}.js
npm test                 # node --test: explain parity, SSE parser, golden derivation vector
./build.sh wasm          # cargo + wasm-bindgen -> dregg_wasm.js + dregg_wasm_bg.wasm
./build.sh package       # validate manifests + zip Chrome .zip / Firefox .xpi
```

`npm run build` is required after any change under `src/`; the committed `dist/`
must match a fresh build. `./build.sh wasm` is only needed when the Rust `wasm/`
crate changes.

## Store listing

- **Privacy policy:** [`PRIVACY.md`](./PRIVACY.md) — link this (hosted) as the
  privacy-policy URL in both the Chrome Web Store and Firefox AMO listings. It
  states honestly what the code does: keys never leave the device, the only
  network connection is to your configured dregg node, no telemetry, no PII.
- **Icons:** `icons/icon-{16,32,48,128}.png` (rendered from `icons/icon.svg`),
  wired into both manifests' `icons` and `action.default_icon`.
- **Default endpoint:** the dregg devnet over TLS
  (`https://devnet.dregg.fg-goose.online`). Plaintext localhost is **not** a
  default host permission — it is an `optional_host_permissions` developer
  toggle requested only when you point the wallet at a local node.

## Load unpacked

- **Chrome**: `chrome://extensions` → Developer mode → Load unpacked → this dir.
- **Firefox**: `about:debugging` → This Firefox → Load Temporary Add-on →
  `manifest-firefox.json` (or the packaged `.xpi`).

## Files

- `manifest.json` / `manifest-firefox.json` — MV3 manifests (storage, activeTab,
  contextMenus, alarms; `wasm-unsafe-eval` CSP for the WASM module).
- `src/background.ts` — service worker: profiles, cipherclerk state,
  authorization, explain-confirmed signing, SSE receipt stream, node HTTP +
  WebSocket, durable outbox.
- `src/explain.ts` — the clerk's faithful turn reading (port of the
  `sdk/src/explain.rs` rendering shapes; prose parity is test-pinned).
- `src/sse.ts` — incremental SSE parser for the receipt stream.
- `src/content.ts` — bridges page events to the background, enforces the
  per-origin/per-method allowlist.
- `src/page.ts` — defines the `window.dregg` API in page context.
- `src/popup-script.ts` + `popup.html` — toolbar popup UI (profile switcher,
  recent receipts, tokens, account, caps, directory, storage).
- `settings.html` / `settings-script.js` — node configuration page.
- `provision`/`recovery`/`confirm-intent`/`disclosure-picker`/
  `origin-permission`/`share-capability` `.html` + `.js` — user-decision popups
  (opened by the background with an opaque nonce; PII stays in background
  memory). `confirm-intent` doubles as the sign-turn confirmation surface.
- `dregg_wasm.js` + `dregg_wasm_bg.wasm` — wasm-bindgen glue + compiled crypto.
- `bip39_english.txt` — BIP39 wordlist for the recovery-phrase fallback path.
- `test/` — `node --test` unit tests (explain prose parity, SSE parser, the
  golden derivation vector).
- `tests/` — Playwright e2e tests (load the unpacked extension in Chromium).

## Page API (selected)

```js
const connected = await window.dregg.isConnected();

// Sign + submit a pre-built encoded Turn. The user sees the clerk's faithful
// reading of the turn and must accept before the signature is released.
const res = await window.dregg.signTurnV3(turnBytes);
// { turnId, submitted, receipt: { turnHash, proofStatus, witnessCount } }

// Owner-lifecycle (nonzero federation domain): gate on the capability, then
// pass the exact 32-byte domain. Exactly 32 bytes, integers 0..=255 — any
// other value rejects with a TypeError BEFORE any popup or signing. Omitting
// the argument keeps the legacy all-zero devnet/sim genesis domain. The
// confirmation popup shows all 64 lowercase hex chars of the domain signed.
if (window.dregg.capabilities.signTurnV3FederationDomain ===
    "dregg-sign-turn-v3-federation-domain/v1") {
  const res2 = await window.dregg.signTurnV3(turnBytes, federationId /* Uint8Array(32) */);
}

// Authorize an action against held capability tokens.
const auth = await window.dregg.authorize({
  action: "read",
  resource: "/data/x",
  mode: "private", // "trusted" | "selective" | "private"
});

// Live committed receipts (from the node's SSE receipt stream).
window.dregg.on("receipt", ({ hash, kinds, hasProof }) => { /* ... */ });
```
