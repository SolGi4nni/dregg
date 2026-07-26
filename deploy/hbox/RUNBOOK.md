# RUNBOOK — the Dragon's Egg Discord bot on hbox

> ## ⚠ 2026-07-25 — REDEPLOY IS CURRENTLY BLOCKED. Read before you rebuild.
>
> A rebuild from HEAD **boots but cannot drive turns**, and the failure mode differs per
> surface. Verified end-to-end on hbox (two live rollbacks). The deployed binaries are
> still the 2026-07-19 build; that is deliberate, not neglect.
>
> 1. **The build line below is WRONG.** `--features dregg-sdk/no-lean-link` yields a binary
>    with no verified PQ cores, which the `dregg-pq` audit gate **fail-closes** on at startup
>    (process exits; `Restart=always` turns it into a crash-loop). The maintained recipe is
>    `deploy/games/deploy-hbox.sh`, which uses **`DREGG_REQUIRE_LEAN=0`** instead — that lets
>    the `dregg-lean-ffi` build script degrade rather than fail.
> 2. **But `DREGG_REQUIRE_LEAN=0` is not sufficient either, as of HEAD.** Those binaries have
>    no **constraint oracle**, so any world-cell turn is refused
>    (`program violation on cell …: no constraint oracle installed`). Observed:
>    - discord — boots and connects, then `reveal_cron: Daily reveal did not fire` (degraded,
>      not obvious from the unit state: `is-active` reports `active`);
>    - telegram — **panics at startup**, `dreggnet-surfaces/src/cheevo.rs:155` (its
>      "the deep winning run drives cleanly" self-check drives a real turn);
>    - web games funnel — **panics at startup**, `today's descent opens: Deploy(... refused)`.
>    `DREGG_ALLOW_UNAUDITED_PQ=1` clears (1) but NOT (2) — it is a different gate.
> 3. **The unblock is a real Lean archive** matching HEAD (`pbuild` is shipping one). Until
>    then a rebuilt game surface cannot serve turns, so do not redeploy one.
> 4. **(2026-07-26) The symptom is now ANNOUNCED, not silent** — the diagnosis above stands
>    unchanged, but you no longer have to infer it from a cron that never fires. The oracles are
>    armed at the derivation point (`dregg_sdk::AgentRuntime::new`, which every world-cell deploy
>    passes through), and the discord bot prints at second zero, at `ERROR`:
>    `GAMES ARE DEAD IN THIS BUILD — NO VERIFIED CONSTRAINT ORACLE in this process …`.
>    Grep the first ten lines of `journalctl --user -u dregg-discord-bot` for `GAMES ARE DEAD`
>    to decide in one command whether a binary can serve a turn. The bot still boots on purpose
>    (identity, wallet, gallery, explorer, payments all work); only the games are dead. And a
>    player who hits it now gets a sentence instead of the name of a Rust function — the internal
>    detail moved to a `tracing::error!` beside the refusal.
>
> **If you deploy anyway:** back up first, install with an atomic rename (`cp` to `.new` then
> `mv -f` — a plain `cp` over the running binary fails `Text file busy`), and after a
> crash-loop clear systemd's start limit with `systemctl --user reset-failed <unit>` before
> starting again. Test a new binary on a spare port *before* installing it — that is how the
> web surface avoided a third outage.

**Status: LIVE on hbox (2026-07-17).** Rehosted off the AWS edge — AWS is now
caddy/gateway ONLY. Connected to Discord as "Dragon's Egg", offerings
bootstrapped, the daily-Descent cron live (rolls today's world from a real drand
beacon).

**The slash surface** is whatever `commands::menus::SLASH_SURFACE` advertises —
`/dregg` `/descent` `/play` `/cipherclerk` `/verify` `/help`, of which `/dregg`
is operator-only (`default_member_permissions: "0"`, so Discord hides it from
members who cannot use it). The boot log prints the exact list; grep
`Registered .* global slash commands` in `journalctl --user -u
dregg-discord-bot` rather than trusting a number written here.

The un-advertised (lab) commands — `/gallery` `/govern` `/identity` `/hermes`
`/federation` `/leaderboard` `/adventure` — are registered ONLY in
`DREGG_LAB_GUILD_ID`. Unset, the boot log warns and names every one of them, and
they are typeable nowhere. Set it to a guild id to get the whole workshop back
inside that one guild without putting it in a stranger's autocomplete.

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
