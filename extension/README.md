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
- **Signed offering turns** — `signOfferingTurn(params)` signs one
  `dreggnet-offerings` move (a dungeon choice, a Hermes prompt, a poll vote)
  with the extension-held identity key: rung 2 of the G1 signed-identity
  ladder, where rung 1 is the server-side verifier
  (`dreggnet-offerings/src/signed.rs`, `OfferingHost::advance_signed`). The
  canonical `dregg-offering-turn-v1:` message is built in
  `src/offering-sign.ts` and pin-tested byte-for-byte against the Rust
  builder's vector (`test/offering-sign.test.mjs`), so the two sides cannot
  drift silently. The confirm popup renders the exact intent — offering,
  session, move, arg, replay counter, signing identity — and the accept is
  bound to the SHA-256 of the exact bytes signed. See "Offering turns" below
  for the wire contract a webapp implements.
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
  **enabled and sound**: the wasm crate moved off the forgeable linear
  `MerkleStarkAir` onto a **real arity-4 Poseidon2 Merkle descriptor**
  (`merkle-membership::poseidon2-4ary-general-depthN`, proven by
  `prove_vm_descriptor2` and checked by the deployed `verify_vm_descriptor2`).
  A genuine member proof verifies and a forged/tampered claim is rejected;
  `composeProofs` discharges each tagged proof against its canonical verifier and
  returns the real boolean composition.
- **EVM signing leg (secp256k1)** — the extension signs both dregg-native
  (Ed25519 + ML-DSA-65) **and** EVM (`secp256k1`). The EVM key is derived from
  the same sealed wallet seed, so one recovery phrase restores both faces.
  `window.dregg.evm.{getAddress, personalSign, signTypedData}` produce EIP-191
  and EIP-712 signatures an on-chain launchpad escrow recovers.
- **fhEgg sealed-bid ceremony** — `window.dregg.sealedBid.commit(...)` hides an
  order behind a keccak256 commitment and EIP-712-escrows it; a later
  `reveal(...)` returns the opening and its `RevealBid` signature. DrEX routes
  **through the installed extension** via `window.dregg.drex.placeOrder(...)`
  (a sealed-key order-turn + optional Bulletproof solvency + blinded ring
  eligibility) rather than loading the wasm standalone.
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
- `tests/` — Playwright e2e tests (`npm run test:e2e`): the unpacked
  extension in HEADLESS full Chromium (`channel: 'chromium'` — the
  headless-shell binary cannot load extensions), one worker-scoped
  browser + one real onboarding for the whole suite, and a per-test
  pristine-wallet state reset (`tests/fixtures/extension.ts`). Full
  suite ~45s; set `HEADED=1` to debug with visible windows.

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

## Offering turns — the wire contract a dregg webapp implements

`dregg.signOfferingTurn` lets any dregg webapp (the live games demo, a
self-hosted offering host) have its moves SIGNED by the key the extension
holds, so the server attributes the move to a **verified** Ed25519 identity
(`Attribution::Signed`) instead of a frontend-asserted label. The verifier is
`dreggnet-offerings/src/signed.rs::verify_signed`, consumed by
`OfferingHost::advance_signed`; the web route that feeds it (`act-signed`) is
the named follow-up — this section is the contract that route consumes.

No host permission is involved: the provider is injected on every origin, the
signing method performs no network fetch, and access is gated by the
extension's own per-origin, per-method grant (the user approves
`dregg:signOfferingTurn` for your origin on first use — a self-hosted webapp
origin works exactly like a known one). The webapp does all the fetching,
same-origin to its own server.

```js
// 1. Detect the provider.
if (!window.dregg) { /* fall back to asserted attribution */ }

// 2. Fetch the next acceptable replay counter from YOUR server (the host
//    tracks the floor per (offering, session, pubkey) and refuses stale
//    counters — replay safety is enforced server-side; the extension
//    displays the counter and refuses malformed values).
const counter = await fetchNextCounter(offeringKey, sessionId);

// 3. Ask the extension to sign. The user confirms the exact intent
//    (offering, session, move, arg, counter, signing identity) in the
//    extension's popup. counter/arg accept a number (safe integer) or a
//    decimal string (u64/i64-safe beyond 2^53 - 1).
const signed = await window.dregg.signOfferingTurn({
  offeringKey,          // e.g. "dungeon"
  sessionId,            // the session the move lands in
  counter,              // from step 2
  turn: action.turn,    // the affordance verb, e.g. "choose"
  arg: action.arg,      // the affordance argument (i64)
  text: action.text,    // optional free-text payload (omit when absent)
});
// -> { actorPubkeyHex, counter, signatureHex }
//    actorPubkeyHex: 64 lowercase hex chars (the verified DreggIdentity)
//    counter:        number, or decimal string beyond 2^53 - 1
//    signatureHex:   128 lowercase hex chars (64-byte Ed25519 signature)

// 4. POST the SignedAction to the server's act-signed route (the follow-up
//    lane), alongside the action fields the message was signed over:
await fetch(`/api/offerings/${offeringKey}/sessions/${sessionId}/act-signed`, {
  method: "POST",
  headers: { "content-type": "application/json" },
  body: JSON.stringify({
    action: { label: action.label, turn: action.turn, arg: action.arg,
              enabled: action.enabled, text: action.text ?? null },
    actor_pubkey_hex: signed.actorPubkeyHex,
    counter: signed.counter,        // route must accept number OR decimal string
    signature_hex: signed.signatureHex,
  }),
});
```

Error paths a webapp distinguishes:

- **Origin not granted** — the promise rejects with the standard
  restricted-method denial (`"Origin not authorized for this method. User
  denied permission."`).
- **User declined the confirm popup** — rejects with an `Error` whose `name`
  is `"DreggUserDeclined"` and `code` is `"user-declined"`.
- **Signature failure / locked custody / wasm unavailable** — rejects with
  `code` `"sign-failed"` / `"custody-locked"` / `"wasm-unavailable"`.
- **Malformed params** — rejects with a `TypeError` before anything is
  dispatched (non-integer / negative / >u64 counters, out-of-i64 args, NUL
  bytes in string fields).

The signature is over exactly
`"dregg-offering-turn-v1:" ‖ offeringKey ‖ 0x00 ‖ sessionId ‖ 0x00 ‖
counter_le(8) ‖ 0x00 ‖ turn ‖ 0x00 ‖ arg_le(8) ‖ 0x00 ‖ text-or-empty` —
`label` and `enabled` are surface decorations and deliberately not signed.
The server reconstructs this message from the claimed fields and verifies
strictly, so any tampering (a different arg, a spliced session or offering, a
shifted counter) fails as `BadSignature`.
