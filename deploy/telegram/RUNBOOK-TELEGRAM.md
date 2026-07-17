# RUNBOOK — dreggnet-telegram-bot (the Telegram runtime shell)

**Status: BUILT + TESTED, NOT DEPLOYED.** The whole shell (long-poll loop, durable
per-`(offering, chat)` sessions, command surface) is driven green over `MockTransport` in
`dreggnet-telegram/tests/`. The one thing no test can supply is the **BotFather token** — the
real run is ops-gated on ember minting one. Nothing else is missing.

## What runs

`target/release/dreggnet-telegram-bot` (crate `dreggnet-telegram`, bin
`src/bin/dreggnet-telegram-bot.rs`):

- **long-polls** `https://api.telegram.org` `getUpdates` (outbound 443 only — no listening
  socket, no funnel, nothing public to expose);
- routes inline-button callbacks + text commands (`/offerings`, `/open <key>`, `/verify`,
  `/act <turn> <arg>`, `/help`) through the ONE `TelegramHost` router — every move is a real
  substrate turn, every `/verify` a real replay re-verification;
- persists every session as a **move-log** (`FileResumeStore`) under `TELEGRAM_SESSION_DIR`
  and **resumes by replay on boot** — a restart drops no game, and a stale button pressed
  after a restart auto-rebinds its chat and still lands;
- persists the consumed `getUpdates` offset beside the sessions (no double-routing across
  restarts).

## Deploy (ops steps, in order)

1. **Mint the token** (ember): talk to `@BotFather`, `/newbot`, copy the token.
2. **Env file** on the target box (`chmod 600`), `~/.config/dregg/telegram-bot.env`:

   ```
   TELEGRAM_BOT_TOKEN=<the BotFather token>
   # Optional but RECOMMENDED for any long-lived deploy: pin the identity master secret so a
   # later token rotation does not remap every user's derived dregg identity.
   # TELEGRAM_BOT_SECRET=<64 hex chars, e.g. `openssl rand -hex 32`>
   # Optional: comma-separated Telegram user ids seated as the council electorate.
   # TELEGRAM_COUNCIL_UIDS=1001,1002
   # Optional: the public HTTPS base the Mini App (dreggnet-web /tg routes) is served from —
   # the "🕹 Play in the app" buttons + /play deep-link {base}/tg/offerings/{key}/session/{id}.
   # Default: the hbox funnel.
   # TELEGRAM_WEBAPP_BASE=https://hbox-dregg.skunk-emperor.ts.net
   ```

3. **Build**: `cargo build --release -p dreggnet-telegram` (on hbox: wrap in `swarm-build`).
4. **Unit**: copy `deploy/telegram/dregg-telegram-bot.service` to
   `~/.config/systemd/user/`, then
   `systemctl --user daemon-reload && systemctl --user enable --now dregg-telegram-bot`,
   and `loginctl enable-linger` if not already on.
5. **Verify live**: journal shows `authenticated as @<botname>`, then DM the bot `/offerings`
   and press a button; `/verify` must answer `… re-verified by replay`.

## Failure modes (all fail-fast / fail-closed)

- **No/bad token** → exit 2 with a clear message (getMe is checked before anything spins).
  Ten fast exits trip the unit's restart-storm brake by design.
- **Tampered session log** → that session REFUSES to resume (executor re-checks every logged
  move on replay); the file is kept on disk as evidence, everything else resumes.
- **Unwritable session dir** → loud warning, sessions degrade to in-memory (bot still runs).
- **Network flap** → the loop backs off 5s and re-polls; sessions are unaffected.

## The Mini App tier (the rich web surface beside the chat buttons)

In a DM, every presented offering surface carries a trailing **"🕹 Play in the app"** `web_app`
button, and `/play` presents a per-offering launch menu — each deep-links
`{TELEGRAM_WEBAPP_BASE}/tg/offerings/{key}/session/{id}` (dreggnet-web's Mini App routes,
docs/TELEGRAM-MINIAPP-DESIGN.md). Groups never get `web_app` buttons (Telegram refuses them
outside private chats); the inline-button tier remains every chat's full, lightweight surface.

Ops steps to arm it fully:

1. **BotFather**: `/setmenubutton` (or `/newapp`) on the bot, registering the Mini App URL
   `https://hbox-dregg.skunk-emperor.ts.net/tg` — this also whitelists the domain for the
   `web_app` buttons.
2. **Identity parity**: set the SAME `TELEGRAM_BOT_SECRET` (and `TELEGRAM_BOT_TOKEN`) in this
   unit's env file AND the dreggnet-web server's — the web validator derives each Telegram
   user's custodial identity through the same `master_secret_from_env`; different secrets fork
   every user into two identities. This is shared-credential co-tenancy (design §2): both
   processes are ONE trust domain on the box.
3. `TELEGRAM_WEBAPP_BASE` only needs setting when the funnel base moves.

A Mini App's `sendData` round-trip (`web_app_data` updates) is routed like any press: payloads
in the affordance codec face the same presented-affordance gate + executor refereeing; anything
else is acknowledged and dropped (client data never names an identity).

## Identity note

Every Telegram user's dregg identity derives from the bot master secret. Default = derived
from the token; **rotating the token therefore remaps identities** unless
`TELEGRAM_BOT_SECRET` is pinned in the env file. Pin it before inviting real users.
