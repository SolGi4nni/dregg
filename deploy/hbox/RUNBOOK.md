# RUNBOOK — the Dragon's Egg Discord bot on hbox

**Status: LIVE on hbox (2026-07-17).** Rehosted off the AWS edge — AWS is now
caddy/gateway ONLY. Connected to Discord as "Dragon's Egg", 52 global slash
commands, offerings bootstrapped, the daily-Descent cron live (rolls today's
world from a real drand beacon).

## Where it runs
- systemd USER unit `dregg-discord-bot.service` on **hbox** (this dir's unit),
  `enable-linger`ed. Same pattern as the games funnel + kubo units.
- Binary: built ON hbox (glibc 2.40 — a persvati/2.42 binary will NOT run here)
  WITHOUT the Lean archive: `cargo build --release --features dregg-sdk/no-lean-link`
  (the bot submits turns to a node over HTTP; the node proves). ExecStart points
  at `~/dregg-bot/dregg-discord-bot`.
- Secrets: `~/.config/dregg/discord-bot.env` (mode 600) — DISCORD_TOKEN,
  DISCORD_APP_ID, BOT_SECRET, FEDERATION_ID, ADMIN_DISCORD_ID (staged from the
  edge .env), plus DATABASE_URL (persistent sqlite `~/dregg-bot/bot.db`),
  DEVNET_URL (`http://127.0.0.1:8420` — the hbox node), HTTP_HOST/PORT (loopback
  :8081), RUST_LOG.

## One token = one bot
The edge bot is DOWN and stays down (the edge no longer defines it as running).
This hbox unit is the ONLY live instance. Before starting the bot anywhere else,
stop this one, or the gateway double-connects.

## Redeploy (new binary)
1. rsync the tree to `~/dregg-build/games-deploy` on hbox (or a bot-deploy dir).
2. `cd .../discord-bot && swarm-build cargo build --release --features dregg-sdk/no-lean-link`.
3. `systemctl --user restart dregg-discord-bot` (sqlite + resume are durable).
4. `journalctl --user -u dregg-discord-bot -n 30` → "Bot connected as Dragon's Egg".

## The coupled node (TODO-1)
DEVNET_URL points at `127.0.0.1:8420` — the hbox node, not yet up. The bot runs
degraded-but-fine without it (Discord commands work; node-submit / anchoring
features wait on the node). The node rehost on hbox is the other half of leaving
AWS: a basic devnet node is straightforward; a PROVING node (`--prove-turns`)
is gated on a HEAD-matching Lean seed.

## Verify live
`journalctl --user -u dregg-discord-bot -n 40` — connect, 52 commands, the daily
reveal. `curl -s http://127.0.0.1:8081/api/cells | head` (the loopback read
surface). In Discord: `/start`.
