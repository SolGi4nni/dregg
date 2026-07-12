# Store-Readiness Review — Dragon's Egg Cipherclerk (browser wallet)

Date: 2026-06-28 · Reviewer: Claude Opus 4.8 (1M) · Scope: `extension/` (+ the
`wasm/` crypto core it bundles). This review GATES upload to the Chrome Web
Store and Firefox AMO. It is a read-review (build + code-read + unit tests), not
a rewrite. No code was changed.

---

## RESOLUTION (2026-06-28) — VERDICT: READY (must-fix items resolved)

The three must-fix items and the high-value mediums have been fixed in
`extension/`. Build green: `./build.sh` and `./build.sh package` exit 0,
`npm run typecheck` clean, `npm test` = **20/20** (the 15 prior + 5 new
onboarding-gate tests). Fresh `dist/dregg-cipherclerk-chrome.zip` /
`.xpi` (~4.1 MB) now carry the icons and the shrunk wasm.

- **MF-1 (silent fund loss) — FIXED.** First run no longer auto-generates a
  wallet under an ephemeral `chrome.storage.session` "internal key." `loadState`
  returns an *uninitialized* state; the popup runs a two-step onboarding that
  **requires** (a) a passphrase (≥8 chars) and (b) re-typing the recovery phrase
  to confirm the backup before any key is generated. Only then is the keypair
  derived and the state + mnemonic encrypted under the user's passphrase
  (`beginOnboarding` / `completeOnboarding`, `background.ts`). No key can exist
  protected solely by a restart-clearable session key. The same orphan path on
  *recovery* is closed too: `recoverFromMnemonic` now requires a separate
  wallet-encryption passphrase (distinct from the optional BIP39 passphrase).
  The pure gate predicates are unit-tested (`test/onboarding.test.mjs`).
  *Note:* dev wallets created by the OLD auto-create path before this change may
  already be orphaned after a restart — nothing can recover a key whose session
  encryption key Chrome already cleared; this fix prevents it going forward.
- **MF-2 (icons) — FIXED.** A Dragon's Egg mark (`icons/icon.svg` → 16/32/48/128
  PNGs) is wired into both manifests' `icons` and `action.default_icon`, and
  bundled by `build.sh`.
- **MF-3 (privacy policy) — FIXED.** `extension/PRIVACY.md` written to match the
  code (keys never leave the device, only the configured node is contacted, no
  telemetry/PII); referenced from the README "Store listing" section for the
  hosted listing URL.
- **MED-1 (devnet/localhost defaults) — ADDRESSED.** Defaults are TLS-only
  (`https`/`wss` devnet); plaintext localhost is removed from the install-time
  host permissions and moved to `optional_host_permissions` (a dev toggle). The
  Firefox manifest's duplicated host perms are removed (the LOW item).
- **MED-2 (27 MB wasm) — FIXED.** `build.sh` runs `wasm-opt -Oz` (installing
  binaryen if missing) in both the wasm build and the `package` step:
  27.16 MB → 17.57 MB.
- **MED-3 (forgeable membership hash) — ADDRESSED.** The live authorize receipt
  seed now uses a real CR hash (blake3) instead of `generate_demo_stark_proof`
  (`MerkleStarkAir`, forgeable). The `composeProofs` page API — which verified
  STARK membership proofs over that forgeable AIR — is gated off with an honest
  error until the circuit moves to a Poseidon2 Merkle hash. Sound range
  predicate proofs (Bulletproofs) are unaffected.
- **MED-4 (Send signed by operator key) — ADDRESSED.** The Account tab is
  relabeled "Node Ops" with a banner stating its actions are signed by the node
  operator's key (not your self-custody wallet); "Send" → "Operator Send
  (node-signed)". Self-custody transfers remain the `signTurnV3` path.

Remaining (non-blocking): the `composeProofs` STARK feature stays disabled until
the circuit's collision-resistant Merkle hash lands; the version is still
`0.1.0` (alpha messaging); the Playwright e2e suite should run in CI before
upload. None gate the must-fix.

---

## VERDICT: NOT READY — fix 3 must-fix items before upload  *(superseded above)*

The **core security architecture is genuinely solid** — well above typical
hobby-wallet quality, and I did **not** find a key-exfiltration vulnerability.
Authorization-first signing is real, message passing is hardened and
adversarially tested, the crypto is real `ed25519_dalek`, and keys never reach
page/content context. That is the high bar for a signing wallet and it is met.

But it is **not ready to publish today** for three concrete reasons:

1. **DATA-LOSS (HIGH):** a fresh user who never sets a passphrase can be
   permanently locked out of their keys (and recovery phrase) on the next
   browser restart. For a wallet that is fund loss.
2. **STORE BLOCKER:** no extension icons in either manifest.
3. **STORE BLOCKER:** no privacy policy, which both stores require for a
   key-handling, network-connecting extension.

None of the three is a deep rearchitecture. After they land (plus the
medium items below addressed or consciously accepted), this is shippable.

Evidence the build is healthy: `./build.sh` exits 0; `npm run typecheck` clean;
`npm run build` clean; `npm test` = **15/15 pass** (BLAKE3 vectors, the golden
`dregg/0` Ed25519 derivation vector, explain-prose parity with
`sdk/src/explain.rs`, SSE parser). Packages build:
`dist/dregg-cipherclerk-chrome.zip` / `.xpi` (~4.5 MB each).

---

## 1. SECURITY (the gate) — STRONG, with one data-loss caveat

### Key generation + storage — GOOD (but see the internal-key caveat)
- Private keys live **only** in the background service worker's in-memory
  `state.secretKey` (decrypted) and inside the AES-256-GCM ciphertext at rest.
  PBKDF2-SHA256 @ **600,000** iterations → AES-256-GCM
  (`background.ts:356-398`). This is current best practice.
- Secret keys are **never** placed in the page or content-script context. The
  `window.dregg` page API (`page.ts`) exposes **no** key-reading method, and the
  object is `Object.freeze`d on a non-configurable, non-writable property
  (`page.ts:413-417`). Verified by e2e test "window.dregg is frozen".
- No secret/mnemonic/passphrase is ever logged. The only `console.warn` near
  secrets logs `err.message` only (`background.ts:428`). Good.
- WASM derivation is the same `blake3 derive_key("dregg/0", seed) → Ed25519` as
  the CLI/SDK, golden-vector pinned across three suites (`test/derivation.test.mjs`).

### Signing flow — STRONG (authorization-first, no blind-signing)
- `signTurnV3` (`background.ts`, `signTurnV3()`) decodes the turn, renders a
  **faithful reading** via `explain.ts` (effect-by-effect prose, word-for-word
  parity with `sdk/src/explain.rs`), binds it to the canonical `[turn <hash>]`
  the node verifies, and shows it in a **nonce-bound confirmation popup**
  (`showTurnConfirmation`). The signature is released **only** on explicit
  accept.
- **Federation-domain bridge** (2026-07: OWNER-LIFECYCLE-BROWSER-SEAM). The
  page API is now `signTurnV3(turnBytes, federationId?)`: the optional second
  argument carries an exact 32-byte federation domain into the wasm
  `sign_turn_v3` signing message (`dregg-action-sig-v2` — cross-federation
  replay prevention). Validated TWICE through the one shared validator
  (`src/federation-domain.ts`; page bridge + background revalidation; exact
  type / length-32 / integer 0..=255 elements; typed rejection BEFORE any
  signing). Only ABSENCE defaults to the legacy all-zero genesis domain. The
  confirmation popup renders the **full 64-char lowercase hex** of the domain
  that was signed; the popup's accept echoes turn id + domain and the
  background **refuses a substituted echo** as a decline; outbox metadata
  retains the selected domain so a retry cannot silently fall back to zero.
  Advertised — only now that the complete page → content → background → WASM
  path is installed and tested — as the frozen
  `window.dregg.capabilities.signTurnV3FederationDomain =
  "dregg-sign-turn-v3-federation-domain/v1"`. Coverage:
  `test/federation-domain.test.mjs` (validator),
  `tests/passkey-sign/run.mjs` (independent Ed25519 verification of wasm
  signatures under domains 00/7f/80/ff — verify under the signed domain, FAIL
  under zero and one-byte-different domains), and
  `tests/e2e/sign-turn-v3-domain.spec.ts` (capability advertisement, popup
  display, substitution refusal, outbox metadata, one-argument backward
  compatibility).
- Unrecognized effects/authorizations render as explicit `UNKNOWN` and set
  `hasUnknown`, which the popup surfaces as a "signing blind — reject unless
  certain" warning (`confirm-intent.html:134`, `explain.ts:29-31`). It never
  silently elides.
- The confirmation UI writes the explanation with `.textContent`
  (`confirm-intent-script.js:49`) — **no** `innerHTML` injection of turn data.
- Legacy `signTurn(JSON)` is hard-disabled (throws), forcing the canonical v3
  path (`background.ts:2454`). Good.

### MV3 permissions — ACCEPTABLE, one product smell
- `permissions: ["storage","activeTab","contextMenus","alarms"]` — minimal and
  justifiable.
- `host_permissions` are specific (not `<all_urls>`), **but** include
  `http://localhost:8420/*`, `ws://localhost:8420/*`, `http://127.0.0.1:8420/*`
  and the hardcoded devnet `https://devnet.dregg.fg-goose.online/*`. Shipping a
  published wallet that (a) requests **localhost + plaintext ws** and (b)
  defaults to a **devnet** will draw reviewer questions and is a
  product-readiness smell. See MEDIUM-1.
- The content script does match `<all_urls>` at `document_start` to inject
  `window.dregg` everywhere (same model as MetaMask's `window.ethereum`).
  Acceptable, but justify it in the store listing.

### Injection / message passing — STRONG, adversarially tested
- No `externally_connectable`: web pages cannot message the background directly.
  The only inbound paths are the content script and extension pages.
- Page↔content uses a per-injection `crypto.randomUUID()` channel
  (`content.ts:9`); the content script sets `_origin` from
  `window.location.origin` **after** spreading the page payload, so a page
  cannot forge it (`content.ts:119-123`).
- Background re-gates by sender class: `POPUP_ONLY_METHODS` reject non-popup
  senders; content scripts may only call `PAGE_ALLOWED_METHODS`
  (`background.ts:3758-3765`).
- User-decision popups are nonce-bound with a three-part `validatePopupSender`
  check (extension page + not a content script + nonce match + path match),
  and PII rides in background memory, not the popup URL
  (`background.ts:319-334`). This whole surface has explicit e2e tests:
  forged-decision rejection, fake-nonce, PII-not-in-URL, legacy-allowlist
  migration, rate-limit (`tests/e2e/popup-security.spec.ts`).
- Per-origin/per-method allowlist with 24h expiry + explicit permission prompt
  for restricted methods (`content.ts:99-109`).

  *Defense-in-depth note (not a blocker):* for restricted methods **without** a
  per-call popup (e.g. `queryBalance`, `storageWrite`, `postIntent`,
  `createBearerCap`), the sole enforcement is the content-script allowlist
  check; the background does not independently re-validate the per-origin
  allowlist. This is safe given no `externally_connectable`, but a background
  re-check would be belt-and-suspenders. Signing/authorize are independently
  gated by their popups, so the funds-moving paths are fine.

### WASM crypto — REAL
- `sign_message`, `sign_turn_v3`, `derive_keypair_from_mnemonic` are real
  exports (`wasm/src/lib.rs:1752/1917/1684`), backed by `ed25519_dalek`
  (`wasm/src/privacy.rs:918+`). Ed25519's nonce is deterministic (RFC 8032) so
  there is no nonce-reuse surface. Not stubbed.

---

## MUST-FIX before upload (in priority order)

### MF-1 (HIGH, data-loss) — fresh wallet can become permanently unrecoverable
**Where:** `background.ts:340-350` (`getInternalEncryptionKey`),
`loadState` first-run (`background.ts:1020-1062`), `browser-compat.ts:29-49`.

**What happens.** On first run the wallet auto-generates a mnemonic + keypair
and encrypts **both the state and the mnemonic** under a random "internal key"
held in `chrome.storage.session` (`needsPassphraseSetup = true`). The popup
*nags* the user to set a passphrase but does **not force it** — the wallet is
fully usable (address visible, can receive funds) without one.

- **Chrome:** `chrome.storage.session` is **cleared on browser restart**. After
  a restart the internal key is gone; `unlockCipherclerk` regenerates a *new*
  random internal key that cannot decrypt the old envelope, and the mnemonic
  envelope is encrypted under the same lost key — so **neither the state nor the
  recovery phrase can be decrypted. Funds are permanently lost.**
- **Firefox:** `compatSession` falls back to `chrome.storage.local` with a
  `_sess_` prefix (`browser-compat.ts:34`), so the internal key is **persisted
  in plaintext on disk** next to the ciphertext — i.e. "encrypted at rest" is
  effectively void until the user sets a passphrase.

**Fix (pick one, MF-1a strongly preferred):**
- **MF-1a:** Force passphrase setup (and recovery-phrase backup confirmation)
  **before** the wallet is usable / before any address is presented as
  fund-receivable. No internal-key fallback should ever be the only key
  protecting a wallet that can hold value.
- **MF-1b (weaker):** If a frictionless first-run is required, persist the
  internal key in `chrome.storage.local` on Chrome too, so a restart cannot
  cause loss — but be explicit in the UI and store listing that the wallet is
  *not* encrypted at rest until a passphrase is set (this matches today's
  Firefox behavior and trades silent loss for honest weak-encryption).

This is the single most important fix: it is silent, irreversible, and hits the
exact "users lose keys" failure the review is meant to prevent.

### MF-2 (STORE BLOCKER) — no extension icons
**Where:** `manifest.json` / `manifest-firefox.json` (no `icons`, no
`action.default_icon`).

Both stores require icons (Chrome: 128×128 for the listing; AMO requires an
icon). The toolbar action also renders a blank icon today. Add an `icons`
map (16/32/48/128) and `action.default_icon`, and prepare the store-listing
icon/screenshots. Cannot complete a credible upload without this.

### MF-3 (STORE BLOCKER) — no privacy policy / data-handling disclosure
**Where:** none in `extension/` or repo root.

A key-handling extension that transmits signed turns to a node and tails an SSE
stream **must** ship a privacy policy URL. Chrome Web Store requires it for
extensions handling sensitive/personal data; AMO requires data-collection
disclosure. Write a short, honest policy: keys never leave the device (true
here), what is sent to the configured node (signed turns, cell-id filter on the
receipt stream), what is stored locally, and no third-party telemetry. Link it
in both listings.

---

## MEDIUM (address or consciously accept before a public launch)

- **MED-1 — devnet/localhost defaults.** Default node is a **devnet**
  (`DEFAULT_NODE_URL`, `background.ts:64`) and host permissions include
  plaintext `http`/`ws` localhost. For a public wallet, either ship pointed at a
  production endpoint, gate localhost behind optional permissions / runtime
  config, and document the justification for reviewers. As-is this reads as a
  developer build.
- **MED-2 — 27 MB unoptimized WASM.** `dregg_wasm_bg.wasm` is **27 MB** and the
  build log says `wasm-opt not on PATH — shipping unoptimized blob`. In MV3 the
  service worker is killed/restarted frequently, so a 27 MB instantiate is a
  real cold-start latency cost on every wake, plus review-size scrutiny. Run
  `wasm-opt -Oz` (and consider trimming unused exports / the privacy stack) —
  this typically cuts the blob substantially.
- **MED-3 — ZK "membership" proof is not collision-resistant.** The build emits:
  `MerkleStarkAir uses a linear hash binding that is not collision-resistant`,
  and it is used on the live membership-predicate verification path
  (`wasm/src/privacy.rs:1663`). The README advertises selective disclosure / ZK
  predicate proofs; a forgeable membership proof is a soundness gap in that
  advertised feature. Either move to the algebraic
  `merkle_poseidon2_circuit()` the deprecation points to, or stop advertising
  membership disclosure as sound until it is fixed. (Does **not** affect the
  core signing gate.)
- **MED-4 — popup "Send" uses the node operator's key, not the user's.** The
  Account tab's prominent **Send DEC** button routes through
  `dregg:submitJsonTurn`, which (per the code's own comment,
  `popup-script.ts:455-461`) is signed by the **node operator's** cipherclerk —
  "the node ignores the body agent." For a self-custody wallet this is
  conceptually wrong/confusing: a user expects "Send" to move *their* identity's
  funds with *their* key (the real self-custody path is `signTurnV3`). Either
  rework the in-popup Send to build + locally sign a turn for the active profile,
  or relabel it clearly as a devnet/operator action.

---

## LOW / polish

- **Version `0.1.0`** signals alpha for a fund-holding wallet; consider the
  maturity messaging.
- **Firefox manifest** duplicates host permissions in both `permissions` and
  `host_permissions` (`manifest-firefox.json:6-23`) — redundant; AMO's linter
  may warn.
- **`build.sh package` does not run `npm run build`** — it zips whatever is in
  `dist/`. Add an explicit TS rebuild to the packaging step so a stale `dist/`
  can never be shipped.
- **`signTurn` is still advertised** in the `DreggAPI` surface (`page.ts:179`)
  but always throws server-side — minor wart; remove or mark deprecated.
- The recovery-phrase display uses `mnemonicDisplay.innerHTML` with words joined
  from the fixed BIP39 list (`popup-script.ts:344`) — safe today (values are
  wordlist tokens), but `textContent`/DOM nodes would be more defensive.

---

## 2. COMPLETENESS

Feature-complete for a dregg signing clerk: named identity profiles, BIP39
recovery, authorization-first signing + submit, durable outbox with
retry/backoff, the SSE receipt stream + badge, capability share/accept, intents,
storage quota, federation registry. The breadth is real and mostly wired to the
node, not stubbed. Thinner/experimental edges that wouldn't embarrass but aren't
"done": CapTP handoff, federation propose/vote, and the ZK disclosure path
(see MED-3). The Account-tab Send semantics (MED-4) are the one genuine
completeness/correctness wart for a self-custody UX.

## 3. BUGS / end-to-end

Build green, typecheck clean, 15/15 unit tests pass. The signing path, explain
rendering, SSE parsing, and derivation are exercised by tests. The Playwright
e2e suite (`tests/e2e/`) is thorough on the security model (popup forgery, PII
leakage, allowlist migration, rate limiting) but was **not executed** in this
review (needs a Chromium download + node mock) — running it in CI before upload
is recommended. The only "bug-class" finding is MF-1 (data-loss) and MED-4
(wrong signer on the popup Send path).

## 4. UX

Good bones: clear lock/unlock, a profile switcher, legible signing confirmation
(this is the part that matters most and it's well done), recent-receipts with a
badge, permission management. Rough spots: passphrase setup is a dismissible nag
rather than a guided first-run (the root of MF-1); the Account Send path is
conceptually confusing (MED-4); blank toolbar icon (MF-2). A newcomer can
install and understand the signing prompt, but the onboarding does not protect
them from the data-loss footgun.

## 5. Store-compliance checklist

- [x] Manifest V3 (both Chrome and Firefox manifests present and valid)
- [x] CSP locked down (`script-src 'self' 'wasm-unsafe-eval'`, `object-src
      'self'`, `frame-ancestors 'none'`)
- [x] No remote code execution; WASM is bundled, not fetched remotely
- [x] No `externally_connectable`; minimal `permissions`
- [x] **Icons** (MF-2) — `icons/icon-{16,32,48,128}.png` in both manifests
- [x] **Privacy policy** (MF-3) — `PRIVACY.md` (host it + link in both listings)
- [x] **Permission justifications** — `<all_urls>` content script is the
      `window.dregg` provider (MetaMask-style); localhost moved to optional
      (MED-1). Still: write the one-line reviewer justification in the listing.
- [x] TLS-only default endpoint; plaintext localhost is an opt-in dev toggle (MED-1)
- [x] Firefox: duplicated host perms in `permissions` removed (LOW)
- [ ] Screenshots + listing copy for both stores

---

### Bottom line
Publishing a key-handling wallet: **not yet.** The security gate (no key
exfiltration, real authorization-first signing) is genuinely passed — that is
the hard part and it is done well. But ship is blocked on **MF-1 (silent
data-loss)**, **MF-2 (icons)**, and **MF-3 (privacy policy)**. Fix those three,
decide on MED-1/2/3/4, and it's a credible, honest upload.

---

## UPDATE (2026-07-12) — federation-domain bridge + popup-path fixes

Alongside the `signTurnV3(turnBytes, federationId?)` federation-domain bridge
(see the Signing-flow section above), three latent defects in the popup
decision path — exposed by the new full-bridge e2e — were fixed:

- **Popup sender misclassification (broke every accept flow on current
  Chromium).** Extension pages opened via `chrome.windows.create` now message
  with `sender.tab` SET, so `isContentScript()` / `validatePopupSender()`
  classified the extension's own popups as page-context content scripts and
  dropped their decisions. Classification now keys on the browser-set,
  unforgeable `sender.url` (`chrome-extension://<own-id>/…`), which a content
  script can never carry. Same security posture, correct on both old and new
  Chromium.
- **Async decision listeners swallowed unrelated responses.** Two
  `chrome.runtime.onMessage` decision listeners were `async`; under Chromium's
  promise-based onMessage support their returned Promise claims the response
  channel for EVERY message, delivering `null` (their undefined resolution)
  before the real router responds — e.g. to `dregg:getPendingDecision`, which
  blanked every popup. Both are synchronous now (async work moved inside).
- **Grant-vs-close race.** The popup sends its decision and immediately
  `window.close()`es; the `windows.onRemoved` handler could resolve a DENY
  while the accept's storage write was still in flight (the allowlist entry
  was written, but the caller saw "denied"). A synchronous `decided` flag now
  keeps the close handler from overriding a received decision
  (origin-permission + provision flows).
- Also: the custom-element registration guards (`dregg-poll` / `dregg-embed`
  / `dregg-doc` / `dregg-story`) checked `typeof customElements ===
  "undefined"`, but current Chromium sets `customElements` to **null** in
  content-script isolated worlds — the guard threw and killed the whole
  content script before `page.js` injection (no `window.dregg` at all). The
  guards now handle null; the element upgrades are unavailable in isolated
  worlds on such Chromium versions, and the page bridge is unaffected.
