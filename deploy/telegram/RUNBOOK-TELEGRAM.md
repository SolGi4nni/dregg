# RUNBOOK — dreggnet-telegram-bot (the Telegram runtime shell)

**Status: LIVE on hbox as [@dreggnet_bot](https://t.me/dreggnet_bot) — and the running binary is
STALE.** (This file said "NOT DEPLOYED" until 2026-07-25, five days after real users were
already playing on it. Repo-vs-box drift in the runbook itself; state the box's truth here.)

Ground truth, read off the box on 2026-07-25:

| thing | value |
| --- | --- |
| unit | `dregg-telegram-bot.service` (user unit, `enable`d, `Restart=always`) |
| binary | `~/dregg-telegram/dreggnet-telegram-bot`, **built 2026-07-19 06:06** |
| source it was built from | ≈ `59ae56df6f` — it PREDATES `01046f85ac` (per-`(chat, offering)` surfaces) and every telegram commit since |
| sessions | `~/.local/state/dregg-telegram/sessions` (`*.log` move-logs + `updates.offset`) |
| audit | `~/dregg-shared/audit/audit-<date>.telegram-<pid>.NN.jsonl` (shared with web + discord) |
| Mini App base | `https://arcade.dregg.net` |

**A restart does NOT pick up new code** — `ExecStart` points at the copied binary, not at
`target/`. Rebuilding and copying is a deliberate step:

```
ssh hbox 'cd ~/dev/breadstuffs && swarm-build cargo build --release -p dreggnet-telegram \
  && install -m 755 target/release/dreggnet-telegram-bot ~/dregg-telegram/dreggnet-telegram-bot \
  && systemctl --user restart dregg-telegram-bot'
```

Check what is actually running before diagnosing ANY behaviour report: a symptom explained by
code that was never shipped is not the symptom the user hit.

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

## The command surface (generated — do not hand-maintain it)

`dreggnet_telegram::commands::COMMANDS` is the ONE registry. The dispatcher resolves every typed
word through it, `/help` is generated from it, and boot calls `setMyCommands` from it so
Telegram's client-side `/` menu is registered too. `tests/help_is_exhaustive.rs` fails the build
if a registered command is missing from `/help` or does not dispatch. Adding a command anywhere
else does nothing — it will not route.

Check what the live bot advertises: `curl -s "https://api.telegram.org/bot$TOKEN/getMyCommands"`.
An empty `[]` means the running binary predates this registration (the client then shows no `/`
menu at all, and the surface has to be guessed).

## When a chat gets stuck

- **`/cancel`** (aliases `/reset`, `/stop`) — the escape, from ANY state, session or none. Drops
  the chat's surfaces, stale keyboards and any armed free-text slot, and reposts the menu.
  Non-destructive: no move-log is touched, and `/open <key>` brings a session back with its
  receipts intact.
- **`/close <key>`** — the destructive form: ends that session AND forgets its durable move-log.
  Requires the key explicitly.
- An armed free-text slot also expires on its own after `host::TEXT_ARM_TTL` (15 min), so a
  forgotten arm cannot swallow a chat's messages indefinitely.
- The surface message index is IN-MEMORY. After a restart, a press on a pre-restart button
  resumes every offering that chat durably owns, reposts their live surfaces, and says so — it
  is not a dead button. Opening (a `/open`, a menu press, a post-restart rebind) always POSTS a
  fresh message; only a landed turn edits the live surface in place.
- **A surface that cannot be painted now SAYS SO** instead of leaving the chat empty (`open`
  used to answer `Ok` with no message at all when the render exceeded Telegram's 4096-character
  ceiling, a `callback_data` exceeded 64 bytes, or a game's epoch generation could not be
  recovered). `tests/every_offering_paints.rs` holds every catalog offering to "paint something
  visible, or refuse legibly".

### Clearing a wedged session from the box (ops, last resort)

The in-chat escapes above need the NEW binary. On a stale deploy, a session whose every
affordance refuses (a do-once RPG surface at the end of its content, e.g. `craft` once its
benches are spent) can be cleared from the box — reversibly:

```
D=~/.local/state/dregg-telegram/sessions; Q=~/.local/state/dregg-telegram/sessions-quarantine
mkdir -p $Q; head -1 $D/*.log            # line 1 of each log is `key <TAB> session-id <TAB> seed`
mv $D/<the>.log $Q/                      # quarantine, never delete — it is the receipt chain
systemctl --user restart dregg-telegram-bot   # drops it from memory; the rest resume by replay
```

Move the file back and restart to undo.

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
