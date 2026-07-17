# Telegram Mini App Identity Integration — Design

**Scope:** how a Telegram Mini App (an HTTPS page opened inside Telegram's web-view) becomes a
fully-trusted dregg frontend: cryptographically verified Telegram identity → the SAME derived
dregg identity the in-chat bot uses → offering sessions on the web `CatalogState` → turns landing
with **verified `Attribution::Signed`** provenance. Design only; component list at the end names
what each lane builds.

**Existing pieces this composes (nothing here re-implements them):**

| Piece | Where | Role |
|---|---|---|
| `@dreggnet_bot` long-poll bot | `dreggnet-telegram/src/bin/dreggnet-telegram-bot.rs` | in-chat frontend, already live |
| `TelegramCipherclerk` / `seed_for` | `dreggnet-telegram/src/cipherclerk.rs` | uid → deterministic Ed25519 dregg identity |
| Web catalog + sessions | `dreggnet-web/src/lib.rs` (`CatalogState`, `catalog_router`) | renders every offering as HTML on the hbox funnel |
| Signed-turn seam (landed 6fa643d05) | `dreggnet-offerings/src/signed.rs`, `OfferingHost::advance_signed` | verified Ed25519 turn attribution + replay counters |
| Signed web route (extension consumer) | `dreggnet-web/src/act_signed.rs` | the wire/status shape this design mirrors |

**Deployment topology:** both the bot process and `dreggnet-web-server` run on hbox; the web
surface is public via `tailscale funnel` at `https://hbox-dregg.skunk-emperor.ts.net`. A Mini App
is just that HTTPS URL registered with @BotFather (menu button or `web_app` inline button); when
Telegram opens it, the page receives **initData** — a query string HMAC-signed by the **bot
token** — which the server validates to recover a cryptographically verified Telegram user id.

---

## 1. THE initData validation (pinned — this is the trust root)

Reference: Telegram Bot API, **"Validating data received via the Mini App"**
(https://core.telegram.org/bots/webapps#validating-data-received-via-the-mini-app).

`initData` is an application/x-www-form-urlencoded query string, e.g.
`query_id=…&user=%7B%22id%22%3A12345%2C…%7D&auth_date=1721234567&hash=abcd…`. The `user` value is
URL-encoded JSON carrying `id` (the Telegram uid, an integer that fits u64), `first_name`,
`username`, etc.

**The algorithm — exactly this, no variation:**

1. Parse the query string into key/value pairs, **URL-decoding the values**.
2. Remove the `hash` pair (and, if present, `signature` — it is part of the third-party Ed25519
   scheme, not the HMAC scheme; see §8). Keep every other received pair, including ones this
   server does not otherwise use — the HMAC covers ALL of them.
3. Build the **data-check-string**: each remaining pair rendered as `key=<decoded value>`,
   sorted lexicographically **by key**, joined by `\n` (a single 0x0A; no trailing newline).
4. `secret_key = HMAC_SHA256(key = "WebAppData", message = bot_token)` — note the constant
   string is the HMAC **key** and the bot token is the **message**.
5. `expected = hex(HMAC_SHA256(key = secret_key, message = data_check_string))` — lowercase hex.
6. Compare `expected` to the provided `hash` in **constant time** (`subtle::ConstantTimeEq` over
   the raw 32 bytes after decoding both sides from hex; a non-hex or wrong-length `hash` is an
   immediate refusal before any comparison).
7. **Freshness:** parse `auth_date` (unix seconds) and refuse when
   `now - auth_date > TELEGRAM_INITDATA_MAX_AGE_SECS` (default **86400** = 24 h — a Mini App
   keeps its launch-time initData for the whole web-view lifetime, so the window must cover a
   long play session; env-tunable) or when `auth_date > now + 300` (clock-skew guard).
8. Only after ALL of the above: parse `user` as JSON and extract `id` → the **verified
   telegram uid**. A missing/unparsable `user` after a valid HMAC is a refusal (there is nothing
   to attribute to).

**Refusal statuses (fail-closed, cheapest first):** missing initData → `401`; malformed query
string / non-hex hash / missing `auth_date` → `400`; HMAC mismatch or stale/future `auth_date` →
`403`. A refused request derives no identity, opens no session, lands no turn.

**Hard rule restated:** the ONLY trusted Telegram identity is the uid recovered from a
validated initData. `initDataUnsafe`, a client-posted uid, a query param, a cookie — all of these
are display-only or refused. There is no fallback path.

initData is bearer-like: anyone holding a valid string can act as that user until the freshness
window closes. Therefore: HTTPS only (the funnel is TLS), never log the raw string (log the
verified uid + `auth_date` instead), and transport it in a header (`X-Telegram-Init-Data`), never
in a URL (URLs leak into logs and Referer headers).

---

## 2. Decision (a): the bot token reaches dreggnet-web via env — the shared-credential coupling, named

`dreggnet-web-server` reads **`TELEGRAM_BOT_TOKEN`** from its environment (exactly the variable
the bot bin already requires) and derives the HMAC `secret_key` from it once at startup. Absent
the variable, the `/tg/*` routes are not mounted and the server logs one line saying so — the
web catalog keeps working; the Mini App surface is ops-gated exactly like the bot is.

**Name the coupling honestly: this is shared-credential co-tenancy.** The web server holding the
bot token can (i) call the Bot API as the bot and (ii) forge a valid initData for ANY uid — i.e.
mint any Telegram-derived identity at will. This is acceptable — and adds **no new power** —
because of the next decision: the same process must also hold the identity **master secret** to
derive uid → key, and whoever holds that secret already custodians every Telegram user's signing
key. Bot and web on the same box (hbox), operated by the same party, are ONE trust domain; the
token env var makes that existing fact visible rather than creating it. The day the web frontend
should NOT be an identity custodian, the fix is not token plumbing — it is the third-party
Ed25519 validation path plus client-held keys (§8).

**Corollary (identity/token separation, recommended at deploy):** the bot bin today derives the
master secret from the token when `TELEGRAM_BOT_SECRET` is unset
(`blake3::derive_key("dregg-telegram-bot identity master secret v1", token)` —
`bot_secret_from_env`, `dreggnet-telegram/src/bin/dreggnet-telegram-bot.rs`). Set an explicit
**`TELEGRAM_BOT_SECRET`** (64 hex chars) in BOTH unit files so (a) a BotFather token rotation
does not silently rotate every custodial identity, and (b) the validation credential (token) and
the identity root (secret) are separable later. Either way, **both processes MUST resolve the
same master secret** — see §3.

---

## 3. Decision (b): verified uid → dregg identity — reuse `TelegramCipherclerk`, byte-for-byte

The Mini App player and the in-chat player must be ONE identity. The bot derives (from
`dreggnet-telegram/src/cipherclerk.rs`):

```text
seed        = BLAKE3_derive_key("dregg-telegram-bot-v1", bot_secret || telegram_user_id_le)
identity    = hex(Ed25519_pubkey(AgentCipherclerk::from_key_bytes(seed)))     // DreggIdentity
```

(`seed_for` + `TelegramCipherclerk::derive`; domain const `TELEGRAM_SEED_DOMAIN =
"dregg-telegram-bot-v1"`, uid little-endian 8 bytes appended to the 32-byte secret.)

**The web lane does not re-implement this — it calls it.** `dreggnet-web` adds a normal
dependency on `dreggnet-telegram` and uses `TelegramCipherclerk::derive(&bot_secret, uid)`
directly. The cipherclerk module is deliberately transport-free (no token, no network — its own
module doc says so), and the lib dependency graph stays acyclic: `dreggnet-telegram` only
*dev*-depends on `dreggnet-web` (the catalog-parity test), which cargo permits alongside
`dreggnet-web → dreggnet-telegram`. Honest cost: the dep rides in `reqwest` +
`dreggnet-catalog`, which the web server's link already tolerates. (Fallback if that ever hurts:
extract `cipherclerk.rs` into a leaf `dreggnet-telegram-identity` crate and have both depend on
it, keeping a `pub use` shim in `dreggnet-telegram` — but do not start there.)

**Master-secret parity is a correctness requirement, not a convention.** If web and bot resolve
different `bot_secret` values, the "same" user forks into two identities. Therefore:
`bot_secret_from_env` moves from the bot **bin** into the **library**
(`dreggnet_telegram::cipherclerk::master_secret_from_env(token) -> Result<[u8;32], String>`,
same precedence: explicit `TELEGRAM_BOT_SECRET` hex else token-derived under the pinned domain),
the bin delegates to it, and the web server calls the same function. One implementation, two
callers, zero drift — plus a pin test asserting the token-derived path's exact output for a
fixture token.

Derived identities are **custodial and reproducible**: the server can re-derive the signing key
whenever it holds the master secret, which is exactly what makes decision (c) possible.

---

## 4. Decision (c): threading the verified identity into offering sessions — custodial `Signed` turns

### 4.1 Per-request verification, no server session state

Every `/tg/*` state-touching request carries the raw initData in `X-Telegram-Init-Data`. The
server validates it **on every request** (two HMAC-SHA256s — cheaper than the offering turn it
gates) rather than exchanging it for a cookie/session token. No new bearer artifact is minted,
nothing to store or expire, and the existing forgeable `dregg_user` cookie path stays untouched
on its own routes with its own (honest, `Asserted`) trust story.

### 4.2 Opening: verified identity as the opener

`GET /tg/offerings/{key}/session/{id}` validates the header, derives
`ident = TelegramCipherclerk::derive(&bot_secret, uid).identity()`, and opens/renders exactly as
the existing catalog GET does — `ensure_open_as(key, sid, Some(&Attribution::Asserted { label:
ident.0 }))`, then `render_for(key, sid, &ident)` (the per-player projection: own hand revealed,
others fogged). The opener attribution stays `Asserted` **on purpose**: the seam's rule is that
only `verify_signed` ever earns `Signed` (see `signed.rs` — `From<DreggIdentity>` deliberately
mints `Asserted`), and the opener lane is an advisory quota key, not a turn attribution. The
label being HMAC-verified upstream makes the quota lane *honest*, but the type does not claim
more than the seam checked.

Session ids: the page links sessions the same way the catalog does. For the "just play" flow the
shell may default to a per-user session id `tg-{offering}-{first 16 hex of ident}` so a user
reopening the Mini App lands in their own session; shared/multiplayer sessions are ordinary URLs
of an existing session id (seat-claiming offerings — `SeatedTug` — already referee seats by
identity).

### 4.3 Advancing: mint a real `Signed` turn custodially

`POST /tg/offerings/{key}/session/{id}/act` (form body identical to the unsigned `/act` twin:
`turn`, `arg`, optional `text`) does, after validation + derivation:

1. Rebuild the full custodial signer:
   `signer = TurnSigner::from_seed(seed_for(&bot_secret, uid))` — `TurnSigner::from_seed` is
   byte-for-byte `AgentCipherclerk::from_key_bytes` (its doc says exactly this), so
   `signer.identity() == TelegramCipherclerk::derive(..).identity()`. Zeroize the transient seed
   as the cipherclerk does.
2. Sign the action over the canonical `signing_message(offering_key, session, counter, action)`
   (`dregg-offering-turn-v1:` domain) at the next acceptable replay counter, and land it via
   **`OfferingHost::advance_signed`** — the turn records with
   `Attribution::Signed { pubkey_hex }`, indistinguishable from (because it IS) a
   verified-signature turn.

This is honest, and the doc-comment on the new seam must say it plainly: **Telegram's HMAC
attested the human; the server signs with the key it custodians for that human.** The signature
proves what signatures prove — the key-holder authorized this exact turn in this exact session
at this counter — and the key-holder is the server, by the frontend's existing custodial design
(rung 1 of the signed.rs module doc's own ladder). The initData gate is what binds the human to
the key on each request. Rung 2 (client-held keys in the web-view, e.g. cipherclerk-in-wasm with
the seed never leaving `localStorage`… or better) slots in later by replacing step 1–2 with the
extension-style client-signed wire from `act_signed.rs` — the verifier does not change.

**The counter seam (one small additive API in `dreggnet-offerings`):** the host's replay ledger
(`signed_counters`, keyed `(offering, session, pubkey)`) is private, and signing at a guessed
counter races. Add
`OfferingHost::advance_custodial(&mut self, key, &SessionId, signer: &TurnSigner, action: Action)
-> Result<Outcome, HostError>`: read the ledger floor, `signer.sign(...)` at exactly
`last_consumed + 1` (or `0` first use), delegate to `advance_signed`. It runs as ONE
`HostThread` job, so floor-read → sign → verify → consume is atomic — no TOCTOU, no counter
bookkeeping in the web layer, and the existing persistence of counter floors through the resume
store keeps working unchanged. (Alternative — exposing `next_signed_counter()` and composing in
the web handler — splits that atomicity across two host jobs; rejected.)

Status mapping: identical to `act_signed.rs`'s table (`400` malformed, `403` refused-by-verifier
— which for a correctly-implemented custodial path indicates a server bug and should also be
logged loudly, `404` routing miss, `429/409` lifecycle, `200` landed/anti-ghost-refused), with
the initData gate's `401/403` in front.

### 4.4 What this buys

Every Mini App turn is a **verified** receipt: `verify` reports and rendered attributions show
`Signed` provenance; per-opener quotas key on a real identity; a council offering's member match
(`public_key_bytes` — already the registration path for Telegram council members via
`council_member_pubkey`) works from the web-view with no extra plumbing, because it is the SAME
key.

---

## 5. Decision (d): the Telegram.WebApp JS surface

The shell page (server-rendered HTML + one inline `<script>`, consistent with the crate's
minimal-JS posture) loads `https://telegram.org/js/telegram-web-app.js` as its FIRST script and
uses exactly this surface:

- **`Telegram.WebApp.ready()`** — immediately after wiring, so Telegram drops its loading
  placeholder. **`Telegram.WebApp.expand()`** — offerings want the full-height view.
- **Theme:** map `Telegram.WebApp.themeParams` onto the page's CSS custom properties at load and
  on the `themeChanged` event (`Telegram.WebApp.onEvent('themeChanged', apply)`):
  `bg_color → --bg`, `secondary_bg_color → --panel`, `text_color → --ink`,
  `hint_color → --muted`, `link_color`/`button_color → --accent`,
  `button_text_color → --accent-ink` (names per the web renderer's existing variable scheme —
  the surface CSS keeps one source of truth; also set `color-scheme` from
  `Telegram.WebApp.colorScheme`). Missing params fall back to the page's own palette.
- **BackButton:** at the catalog root, `Telegram.WebApp.BackButton.hide()`; inside an offering
  session, `.show()` with `onClick` navigating back to the catalog view. (Turn-level undo is NOT
  wired to it — turns are receipts; the back button is navigation only.)
- **`Telegram.WebApp.initData`** — the raw signed string; read once and attached as
  `X-Telegram-Init-Data` on every fetch. The page uses fetch + the existing `X-Fragment: 1`
  fragment-render path for in-place turn updates.
- **`Telegram.WebApp.initDataUnsafe`** — display only (greet by `first_name`), and the page
  comments say so: it is the UNVERIFIED parse; the server never receives or trusts it.

Out of scope (deliberately, v1): `MainButton`, `HapticFeedback`, `CloudStorage`, payments.

---

## 6. HTTP surface (new, additive — a `/tg` scope beside the existing routes)

New router (`tg_miniapp_router(state)`) merged into `make_app` when `TELEGRAM_BOT_TOKEN` is set:

```text
GET  /tg                                    — Mini App shell (static HTML+JS; no auth to serve)
GET  /tg/offerings                          — catalog listing rendered for the VERIFIED viewer
GET  /tg/offerings/{key}/session/{id}       — validate → ensure_open_as(Asserted ident) → render_for(ident)
POST /tg/offerings/{key}/session/{id}/act   — validate → derive signer → advance_custodial → Signed turn
```

All but the shell require `X-Telegram-Init-Data`. The existing `/offerings` cookie-identity
routes are untouched — the two trust stories never share a handler, so no code path can confuse
a cookie label with a verified uid.

---

## 7. Threat model (what each gate refuses)

| Attack | Refused by |
|---|---|
| Forged/absent initData, tampered fields, uid swap | HMAC validation (§1) — `401/403` |
| Replayed captured initData | freshness window (bounded exposure; §1 handling rules) — bearer-like within the window, same as Telegram's own model |
| Client-claimed uid / cookie / `?user=` on `/tg/*` | never read — the header is the only identity input |
| Turn replay / splice across sessions/offerings | `advance_signed`'s canonical message binding + strictly-increasing counter ledger (unchanged) |
| Web server forging identities | out of model — it custodians the keys AND holds the token; one trust domain (§2), documented, with the §8 exit |
| initData leaking via URLs/logs | header transport + log-hygiene rule (§1) |

---

## 8. Future (named, not built now)

- **Token decoupling:** Telegram also signs initData with **Telegram's own Ed25519 key**
  (the `signature` field; "Validating data for Third-Party Use"). Validating that instead of the
  HMAC removes the bot token from the web server entirely — the right move if web and bot ever
  land on different trust domains. The `/tg` handler shape is unchanged by it.
- **Rung-2 client-held keys:** replace the custodial signer with client-side signing in the
  web-view (the `act_signed.rs` wire, already deployed for the extension); initData then only
  gates session *visibility*, not attribution.

---

## 9. Component list

**WEB LANE (`dreggnet-web`) — new module `src/telegram_miniapp.rs` (+ shell assets):**
1. `validate_init_data(secret_key, init_data, now, max_age) -> Result<VerifiedTelegramUser, InitDataError>`
   — pure, no I/O; `VerifiedTelegramUser { user_id: u64, username: Option<String>, auth_date: u64 }`;
   `InitDataError` variants naming each refusing gate (§1). Precompute `secret_key` from the token once.
2. `TgMiniAppState { catalog: Arc<CatalogState>, secret_key: [u8;32], bot_secret: [u8;32], max_age: Duration }`
   + `tg_miniapp_router` with the §6 routes; POST path calls `advance_custodial`.
3. The Mini App shell page: telegram-web-app.js bootstrap, ready/expand, themeParams→CSS vars +
   `themeChanged`, BackButton wiring, header-attaching fetch with `X-Fragment` re-render (§5).
4. `dreggnet-web-server`: mount the router iff `TELEGRAM_BOT_TOKEN` set (resolve `bot_secret`
   via the shared `master_secret_from_env`); read `TELEGRAM_INITDATA_MAX_AGE_SECS`.
5. Manifest edits (main loop owns manifests in a live swarm): `dreggnet-web` deps +=
   `dreggnet-telegram`, `hmac` (workspace), `sha2` (workspace), `subtle`.
6. Tests: (i) initData vector test — construct a valid initData under a fixture token by running
   the pinned algorithm forward, assert accept + exact uid, then flip one byte of each field /
   drop `hash` / stale `auth_date` / future `auth_date` and assert the named refusal; (ii)
   identity-parity — `validate → derive` equals `TelegramCipherclerk::derive(secret, uid).identity()`;
   (iii) end-to-end custodial turn — POST lands `Outcome::Landed` and the recorded attribution
   `is_signed()`; a second POST consumes the next counter.

**OFFERINGS LANE (`dreggnet-offerings`):**
7. `OfferingHost::advance_custodial(key, sid, &TurnSigner, Action)` — atomic floor-read → sign →
   `advance_signed` in one call (§4.3), doc-comment carrying the honest custodial-attestation
   statement; pin test: floor respected across calls, provenance `Signed`, refused executor move
   still burns the counter (delegation means this is inherited, assert it anyway).

**BOT LANE (`dreggnet-telegram`):**
8. Lift `bot_secret_from_env` → `cipherclerk::master_secret_from_env(token)` (lib), bin
   delegates; pin test on the token-derived output for a fixture token.
9. `api.rs`: `WebAppInfo`/`web_app` inline-keyboard button support in the pure request builders +
   a "Play in the app" button (URL = funnel `/tg`, or deep-linked
   `/tg/offerings/{key}/session/{id}`) on offering surfaces; MockTransport tests assert the wire
   shape as the existing builders do.

**OPS (deploy/telegram runbook + unit files; no code):**
10. BotFather: set the menu button / register the Mini App URL
    `https://hbox-dregg.skunk-emperor.ts.net/tg`.
11. Set explicit `TELEGRAM_BOT_SECRET` (64 hex) in BOTH the bot and web unit environments (§2
    corollary); `TELEGRAM_BOT_TOKEN` in both; document the shared-credential co-tenancy in the
    runbook in the §2 terms.
