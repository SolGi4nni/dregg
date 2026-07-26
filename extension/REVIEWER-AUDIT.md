# Reviewer-Perspective Audit — Dragon's Egg Cipherclerk

A pre-emptive walkthrough of what an **AMO / Chrome Web Store human reviewer**
checks for a crypto/wallet extension, answered against this extension's actual
manifest and code. Every claim below is grounded in a file the reviewer can open
in the submitted source. Companion docs: `SOURCE-SUBMISSION.md` (reproducible
build), `PRIVACY.md` (data handling), `STORE-READINESS-REVIEW.md` (the deeper
security read this summarizes).

**Verdict:** permissions are minimal and each is justified; there is **no remote
code** (everything loads from the package via `chrome.runtime.getURL`); the CSP
is tight; the data disclosure is accurate (no telemetry, keys never leave the
device). No blocking reviewer red-flag found. The notes below pre-answer the
questions a careful reviewer will still raise.

---

## 1. Permissions — minimal, each justified

From `manifest.json` (Chrome) / `manifest-firefox.json` (Firefox):

### `permissions`

| Permission | Why it is needed | Code reference |
|---|---|---|
| `storage` | Persist the **encrypted** wallet state, profiles, capability tokens, and per-origin grants in `chrome.storage.local`. Nothing leaves the device. | `src/background.ts`, `src/content.ts:58` |
| `activeTab` | Low-privilege; used to open the extension's own pages (`tabs.create` of `recovery.html`/`settings.html`) and to deliver receipt events to the originating tab's content script (`tabs.sendMessage`). No broad host access is requested through it. | `src/popup-script.ts:519,523`, `src/background.ts:550` |
| `contextMenus` | A single "Share capability…" right-click item that opens a confirmation popup when the selection is a 64-hex cell id. | `src/background.ts:4369-4389` |
| `alarms` | One periodic alarm (1 min) to drive the outbox retry/backoff in the MV3 service worker, which is killed/woken frequently. | `src/background.ts:4361,4410` |

No `tabs` (full), no `webRequest`, no `cookies`, no `downloads`, no `clipboard`,
no `<all_urls>` host permission — none of the high-scrutiny permissions are
requested.

### `host_permissions` — specific, not `<all_urls>`

```
https://node.dregg.net/*
wss://node.dregg.net/*
```

Only the configured dregg node (TLS HTTP + secure WebSocket). The WebSocket is
the receipt event stream; the HTTPS host is for submitting signed turns and
reading public chain data. **TLS-only** — no plaintext host is requested at
install time.

### Optional (opt-in, not granted at install)

- Chrome: `optional_host_permissions` — `http(s)`/`ws` `localhost:8420` and
  `127.0.0.1:8420`.
- Firefox: the same hosts under `optional_permissions` (Firefox MV3's location
  for optional host patterns).

These exist so a developer can point the wallet at a **local** dregg node. They
are plaintext localhost only (never a remote plaintext host), and the user must
explicitly grant them — they do nothing until toggled.

### The `<all_urls>` content script — the one item to justify proactively

The content script matches `<all_urls>` at `document_start`
(`manifest.json:31-41`) to inject a `window.dregg` provider into every page. This
is the **standard wallet pattern** (identical in shape to MetaMask's
`window.ethereum`): dApps need a page-context object to *request* an
authorization. Critically, this injected provider exposes **no key-reading
method** and cannot move funds on its own — every sensitive action is gated by an
explicit, nonce-bound confirmation popup the user must approve
(`src/page.ts`, `src/background.ts`). The content script also runs `<all_urls>`
but performs no DOM scraping, no network calls, and no data collection — it only
bridges page↔background messages over a per-injection random channel
(`src/content.ts:8`). This justification belongs in the store listing too.

---

## 2. No remote code — MV3 compliant

Reviewers reject extensions that fetch or evaluate code at runtime. This one does
not:

- **No `eval`, no `new Function`, no `document.write`** anywhere in `src/`
  (grep-clean).
- **No remote script tags / CDN imports / dynamic `import()` of a URL.** No
  `http(s)://` script source appears in `src/`.
- **The WebAssembly is bundled, not fetched.** It is loaded from the package
  only: `chrome.runtime.getURL("dregg_wasm.js")` via `importScripts` and
  `chrome.runtime.getURL("dregg_wasm_bg.wasm")` for the bytes
  (`src/background.ts:147,153,161`). `importScripts` here loads a **packaged,
  reviewable** glue file, not a remote URL.
- Every other resource (`page.js`, `bip39_english.txt`, all popup HTML) is
  loaded via `chrome.runtime.getURL(...)` — all in-package.
- The only network egress is to the user-configured node host (see §1
  host_permissions and `PRIVACY.md`); none of it is code.

The `'wasm-unsafe-eval'` token in the CSP (below) is the **only** reason the CSP
is not the bare default; it exists solely so the browser can compile the
**bundled** `.wasm`. It does not enable `eval` of JavaScript.

---

## 3. Content Security Policy — tight

Both manifests set (`manifest.json:68-70`):

```json
"content_security_policy": {
  "extension_pages": "script-src 'self' 'wasm-unsafe-eval'; object-src 'self'; frame-ancestors 'none'"
}
```

- `script-src 'self'` — scripts only from the package; no inline, no remote.
- `'wasm-unsafe-eval'` — the minimal token required to instantiate the bundled
  WebAssembly module in MV3 (the modern, narrow replacement for
  `'unsafe-eval'`). It does **not** permit JS `eval`.
- `object-src 'self'` and `frame-ancestors 'none'` — no plugins, cannot be
  framed. This is the recommended hardened CSP shape.

---

## 4. Data handling — matches `PRIVACY.md` and `data_collection_permissions: none`

The Firefox manifest declares
`browser_specific_settings.gecko.data_collection_permissions.required = ["none"]`
(`manifest-firefox.json:73-82`). The code backs that up:

- **Keys never leave the device.** Private keys exist only in the background
  service worker's in-memory state while unlocked, and as AES-256-GCM ciphertext
  at rest (PBKDF2-SHA256, 600,000 iterations) in `chrome.storage.local`. Wiped
  on lock/timeout. Never placed in page or content-script context.
- **No telemetry, no analytics, no third-party SDKs/ad networks.** No tracking
  network calls in `src/`.
- **Only the configured node is contacted** (default the TLS devnet): signed
  turns the user explicitly approves, public-chain read requests, and a
  receipt-stream subscription filtered by the user's cell id.
- Removing the extension / clearing storage deletes all local data.

This is exactly what `PRIVACY.md` states; the policy was written to match the
code, not aspirationally.

---

## 5. Key-safety summary (reviewer reassurance, one paragraph)

Private keys are generated on-device and held **only** in the background service
worker's memory while the wallet is unlocked; at rest they are AES-256-GCM
encrypted under a key derived from the user's passphrase via PBKDF2-SHA256
(600,000 iterations), and the in-memory copy is wiped on lock or timeout. Setup
**forces** a passphrase plus a recovery-phrase backup confirmation before any key
is generated — there is no usable wallet protected only by an
ephemeral/restart-clearable key (`STORE-READINESS-REVIEW.md` MF-1, resolved).
Signing is **authorization-first**: every turn is decoded and rendered as
human-readable, effect-by-effect prose bound to the exact `[turn <hash>]` the
node verifies, shown in a nonce-bound confirmation popup, and the signature is
released only on explicit accept; unrecognized effects render as `UNKNOWN` with a
"signing blind — reject unless certain" warning rather than being silently
hidden. The injected `window.dregg` page provider exposes **no** key-reading
method and is frozen on a non-configurable property; web pages cannot read keys
or sign without the user's per-action approval. Full evidence with file:line
citations is in `STORE-READINESS-REVIEW.md` §1.

---

## 6. Other reviewer red-flags — checked

| Red-flag a reviewer looks for | Status here |
|---|---|
| Obfuscated / minified-only code with no source | **Clear.** All JS is bundled (not minified/mangled) from the readable `src/*.ts`; the wasm is reproducible from `wasm/` Rust source. See `SOURCE-SUBMISSION.md`. |
| Remotely hosted code / live updates | **Clear.** Nothing fetched or evaluated at runtime (§2). |
| Over-broad host permissions (`<all_urls>` host access) | **Clear.** Host permissions are the single configured node, TLS-only; localhost is opt-in optional. The `<all_urls>` is a content-script *match*, justified in §1. |
| `externally_connectable` letting any page talk to the background | **Clear.** Not declared; pages reach the background only via the content-script bridge, re-gated by sender class. |
| Undeclared data collection | **Clear.** `data_collection_permissions: ["none"]`; matches `PRIVACY.md` and the code. |
| Background sourcemaps leaking internals | **Clear.** Production builds ship no sourcemap (`build.mjs`: sourcemaps in dev/watch only). |
| Crypto that is stubbed / fake | **Clear.** Real `ed25519_dalek` signing + `blake3` derivation in `wasm/src/privacy.rs`. |
| Manifest redundancy / lint warnings | The Firefox manifest avoids duplicating host perms across `permissions` and `host_permissions` (the LOW item from the readiness review is resolved). |

### Honest disclosures (not blockers, but worth surfacing to the reviewer)

- **Alpha / devnet build.** Version is `0.1.0` and the default node is the dregg
  **devnet**. This is a self-custody wallet for an early network; the listing
  should say so. Not a policy violation — just set expectations.
- **A ZK "membership"-disclosure feature is gated off** until its Merkle hash is
  collision-resistant (`STORE-READINESS-REVIEW.md` MED-3). The advertised,
  *enabled* privacy feature (Bulletproofs range-predicate proofs) is sound; the
  disabled path returns an honest error rather than a forgeable proof. No claim
  in the live UI overstates what is enabled.
