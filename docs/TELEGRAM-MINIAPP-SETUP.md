# Telegram Mini App — Setup & Go-Live

Ember-facing runbook: the @BotFather steps, the one ops step, and the end-to-end test for
putting the web arcade inside Telegram as a Mini App on `@dreggnet_bot`.

Companion docs — this file is *how to wire it up*; those are *what it is*:

- **`docs/TELEGRAM-MINIAPP-DESIGN.md`** — the identity design (initData HMAC validation →
  verified Telegram uid → the same derived dregg identity the in-chat bot uses → custodial
  `Signed` turns). Referenced below as "the design".
- **`deploy/games/RUNBOOK-FUNNEL.md`** — the funnel deploy this rides on
  (`https://hbox-dregg.skunk-emperor.ts.net`, already live).
- **`deploy/telegram/RUNBOOK-TELEGRAM.md`** — the in-chat bot deploy (already live).

**The trust rule, stated once and load-bearing everywhere below:** the ONLY trusted Telegram
identity is the uid recovered by validating initData's HMAC against the bot token
**server-side** (design §1). A client-claimed uid, `initDataUnsafe`, a cookie, a query param —
all refused or display-only. There is no fallback path.

---

## 1. @BotFather steps

Two separate registrations. The **menu button** (already done) makes the arcade reachable from
the bot's chat header. The **named app** (`/newapp`) additionally gives it a shareable direct
link — `t.me/dreggnet_bot/play` — that opens the Mini App from anywhere in Telegram, and an
entry in Telegram's app surfaces.

### 1a. Menu button — ALREADY SET

`/mybots` → `@dreggnet_bot` → **Bot Settings** → **Menu Button** → set the URL. It currently
points at the funnel arcade:

```
https://hbox-dregg.skunk-emperor.ts.net/offerings
```

**One edit to make now:** the identity lane is landed (§4), so repoint the menu button to

```
https://hbox-dregg.skunk-emperor.ts.net/tg
```

the same way, so it opens the initData-validating shell instead of the cookie-identity catalog.

### 1b. `/newapp` — the named Mini App (`t.me/dreggnet_bot/play`)

Send `/newapp` to `@BotFather`, pick `@dreggnet_bot`, then answer the prompts in order:

| BotFather prompt | What to send |
|---|---|
| **Title** (≤ 30 chars) | `dregg games` |
| **Short description** | `Verifiable games. Every move is a receipt — signed, replayable, checkable by anyone. Honest scope: a live devnet arcade.` |
| **Photo** (exactly 640×360 px) | An arcade screenshot or the dregg mark on a plain field. No asset is committed in-repo yet; a cropped screenshot of the live catalog page is the honest placeholder. |
| **Demo GIF** (optional) | `/empty` to skip, or a short capture of a Descent run. |
| **Web App URL** | `https://hbox-dregg.skunk-emperor.ts.net/tg` (the initData-validating shell; to edit later: `/myapps` → select the app → Edit Web App URL). |
| **Short name** (becomes the link) | `play` → yields `t.me/dreggnet_bot/play` |

Copy register: describe what runs, present tense, no hype. "Verifiable" and "receipt" are the
product claims we can back (every move lands as a checkable turn); do not add "trustless",
"unhackable", or throughput claims.

To edit any field later: `/myapps` → select the app.

---

## 2. The ops step: bot token into the funnel unit's env

`dreggnet-web-server` (the funnel unit) needs **`TELEGRAM_BOT_TOKEN`** in its environment to
derive the HMAC secret and validate initData server-side. Without it the `/tg` routes are not
mounted (fail-closed, one log line: "Telegram Mini App surface NOT mounted") and the rest of
the catalog keeps working — the Mini App identity surface is ops-gated exactly like the bot is.

The unit `deploy/games/dregg-web-games-funnel.service` already reads
`EnvironmentFile=%h/.config/dregg/games-funnel.env` (placed by ember, chmod 600 — secrets live
there, never in the unit file). On hbox, append to that env file:

```
# ~/.config/dregg/games-funnel.env  (chmod 600)
TELEGRAM_BOT_TOKEN=<the same BotFather token the bot unit uses>
TELEGRAM_BOT_SECRET=<64 hex chars — same value as in the bot unit's env>
```

`TELEGRAM_BOT_SECRET` is the design §2 corollary: set it explicitly **in both units** (this
env file and the bot's `~/.config/dregg/telegram.env`) so web and bot resolve the SAME identity
master secret — otherwise one user forks into two identities — and so a future token rotation
does not silently rotate every custodial identity. Mint once: `openssl rand -hex 32`.

Then reload:

```
systemctl --user daemon-reload
systemctl --user restart dregg-web-games-funnel
journalctl --user -u dregg-web-games-funnel -n 20   # expect "Telegram Mini App surface mounted at /tg"
```

If you prefer a drop-in over the env file, `systemctl --user edit dregg-web-games-funnel` with
`[Service]` / `Environment=TELEGRAM_BOT_TOKEN=...` also works — but the chmod-600 env file is
the standing pattern here (unit files are world-readable and committed; tokens are not).

**Named honestly (design §2):** this puts the bot token in the web server's environment —
shared-credential co-tenancy. The web server can then act as the bot and mint any
Telegram-derived identity. That adds no new power: the same process already custodians every
derived signing key, and bot + web on hbox, run by the same party, are one trust domain. The
exit, if that ever changes, is the third-party Ed25519 initData validation path (design §8),
not token plumbing.

---

## 3. Test end-to-end once live

**Basic reachability (works with either URL):**

1. Open `@dreggnet_bot` in Telegram (mobile or desktop), tap the **menu button** (or open
   `t.me/dreggnet_bot/play`, or tap a "🕹 Play in the app" button under a DM'd offering, or
   send `/play` in a DM for the launch menu).
2. Confirm the web arcade opens inside Telegram's web-view over the funnel's TLS — catalog
   renders, an offering opens, a move lands and re-renders.
3. Cross-check from outside: the same session URL in a normal browser shows the same state —
   it is one server, one catalog.

**The identity surface (the `/tg` routes; §4):**

4. Reopen via the menu button / `t.me/dreggnet_bot/play` (pointing at `/tg`). The shell
   greets you by your Telegram `first_name` (display-only, from `initDataUnsafe` — the server
   never trusts it).
5. **Confirm the player is the verified Telegram identity, not a cookie.** Make a move, then
   check its attribution is `Signed { pubkey_hex }` where the pubkey equals
   `TelegramCipherclerk::derive(bot_secret, your_uid).identity()` — the SAME identity the
   in-chat bot derives. Concretely: DM the bot `/verify` (or open the session's verify view)
   and confirm the web-landed turn shows Signed provenance under your identity, not an
   `Asserted` cookie label.
6. **Confirm refusal is real** (this is the test that matters):
   - `curl -X POST https://hbox-dregg.skunk-emperor.ts.net/tg/offerings/<key>/session/<id>/act`
     with **no** `X-Telegram-Init-Data` header → `401`. No turn lands.
   - Same request with a copied initData whose `hash` has one byte flipped → `403`.
   - A `?user=<uid>` query param or `dregg_user` cookie on a `/tg/*` route changes nothing —
     the header is the only identity input.
7. Play the same offering from in-chat bot and Mini App alternately; both surfaces move the
   same session as the same identity, and the replay counter advances monotonically.

**Anchoring caveat while testing:** the funnel unit's `DREGG_NODE_URL` target (`:8420`) is
currently DEAD (ledger lost on the 07-15 hard reboot — see the status banner in
`deploy/games/RUNBOOK-FUNNEL.md`). Games play and rank in-process; submitted runs cannot anchor
until the replacement node unit (persistent data-dir, TODO-1 in `deploy/README.md`) is up. A
`cell not found` on submit during testing is that, not the Mini App.

---

## 4. Current resolution — what is in the tree vs what needs ops

**In the tree (the identity lane, design §9 — landed):**

- `dreggnet-web/src/telegram_miniapp.rs`: `validate_init_data_at` (the §1 HMAC algorithm,
  fail-closed, constant-time compare, `auth_date` freshness), the `/tg` router (shell +
  offerings + session view/act), the Telegram.WebApp shell page. Identity input is ONLY the
  `X-Telegram-Init-Data` header — no cookie/query fallback on `/tg/*`.
- Custodial `Signed` turns: the act handler composes counter-floor read → sign →
  `advance_signed` inside ONE atomic host job (the design's `advance_custodial` atomicity
  requirement, met by composition — no separate API was needed).
- `dreggnet_telegram::cipherclerk::master_secret_from_env` — the ONE secret-resolution
  implementation, called by both the bot binary and the web validator; Mini App player ==
  in-chat player byte-for-byte.
- Bot-side launch tier: DM'd offerings carry a "🕹 Play in the app" `web_app` button;
  `/play` (alias `/webapp`) sends a launch menu; both deep-link
  `{TELEGRAM_WEBAPP_BASE}/tg/offerings/{key}/session/tg:{chat}` (default base = the funnel).
  Groups get no `web_app` buttons (Telegram refuses them there) — the inline-button tier
  remains every group's full surface.

**Needs ops (this doc):** §1a repoint the menu button to `/tg`; §1b `/newapp` if not done;
§2 env into the funnel unit (without it, nothing mounts and the token gate logs once).

**Web identity outside `/tg`** stays the `dregg_user` cookie — honestly `Asserted`, forgeable
by design, and labeled as such. The two trust stories are additive routes on one server.

**Also named:** the `:8420` node replacement (anchoring, §3 caveat) and the rung-2 future —
client-held keys in the web-view, which replaces the custodial signer without changing the
verifier (design §8).

---

## STATUS — 2026-07-17

### What landed

- **Web: initData validation + identity** (`dreggnet-web/src/telegram_miniapp.rs`, §4).
  Server-side HMAC validation against the bot token (fail-closed, constant-time compare,
  `auth_date` freshness); the `/tg` router; custodial `Signed` turns composed atomically in
  one host job; secret resolution shared with the bot via
  `dreggnet_telegram::cipherclerk::master_secret_from_env` (ONE definition — web and bot
  derive the same identity byte-for-byte). Identity input on `/tg/*` is ONLY the validated
  `X-Telegram-Init-Data` header.
- **Bot: launch tier** (§4). DM'd offerings carry a "🕹 Play in the app" `web_app` button;
  `/play` (alias `/webapp`) sends a launch menu; deep links target
  `{base}/tg/offerings/{key}/session/tg:{chat}`. Groups get no `web_app` buttons (Telegram
  refuses them there).
- **Shell + theming.** The `/tg` shell page loads `telegram-web-app.js` and renders inside
  Telegram's web-view themed to the client; `first_name` greeting is display-only
  (`initDataUnsafe` — never trusted server-side).
- **Cold deep-link repair.** The bot's `web_app` buttons open their URL as a plain document
  navigation — no `X-Telegram-Init-Data` header exists at that point (initData only
  materializes in JS). The original handler 401'd that, so every launch button was a dead
  end. Fixed: a header-less, non-fragment GET on a session path now serves the static shell
  with the deep path HTML-escaped into `data-boot` (no state touched, nothing identity-gated
  revealed); the shell JS then re-fetches with the header attached. Header-less fragment
  fetches and ALL POSTs keep the hard 401. Covered by a dedicated test (200 + shell +
  exact `data-boot`, no session opened as a side effect, fragment variant still 401s).

### Build state (gates run 07-16, both exit 0)

- `cargo check -p dreggnet-web -p dreggnet-telegram --all-targets` — clean; only
  pre-existing warnings not from this work (`dreggnet-web/src/descent.rs:90` dead `id`
  field, two dead-code in `dungeon-on-dregg`).
- `cargo test -p dreggnet-web -p dreggnet-telegram` — 28/28 suites ok, 0 failures.
  Includes the 8 `telegram_miniapp` tests (validation, refusal, cold deep-link) plus the
  full pre-existing suites in both crates (act_signed, catalog, lifecycle, persistence,
  federation; driven, dungeon, full-parity, multi-offering, runtime_shell, webapp_launch).

Nothing below is code work. The tree is done; go-live is exactly the two human steps.

### To go live — EXACT remaining steps

**(a) ember — @BotFather (§1):**

1. `/mybots` → `@dreggnet_bot` → Bot Settings → Menu Button → set URL to
   `https://hbox-dregg.skunk-emperor.ts.net/tg` (§1a — currently points at `/offerings`).
2. `/newapp` → follow the §1b table (Web App URL = the same `/tg` URL; short name `play`
   → `t.me/dreggnet_bot/play`).

**(b) ops — on hbox (§2):**

1. Append to `~/.config/dregg/games-funnel.env` (chmod 600):
   `TELEGRAM_BOT_TOKEN=<the bot's token>` and `TELEGRAM_BOT_SECRET=<same 64-hex value as
   the bot unit's env>` — the SECRET must match `~/.config/dregg/telegram.env` in the bot
   unit or web and bot fork one user into two identities.
2. Rebuild and redeploy `dreggnet-web` (the funnel unit's binary), then
   `systemctl --user daemon-reload && systemctl --user restart dregg-web-games-funnel`;
   expect the log line "Telegram Mini App surface mounted at /tg" (without the token it
   logs "NOT mounted" and the `/tg` routes stay off, fail-closed).
3. Restart the telegram bot unit so it picks up the launch-button/`/play` tier:
   `systemctl --user restart` on the bot unit (see `deploy/telegram/RUNBOOK-TELEGRAM.md`).

Then run §3's end-to-end test — step 6 (refusal is real) is the one that matters.

**Standing caveat, unchanged:** the `:8420` anchoring node is still dead (07-15 reboot);
games play and rank in-process, submits cannot anchor until the replacement node unit is up
(§3 caveat). Not a Mini App issue.
