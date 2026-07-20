> # ⚠ ASPIRATIONAL — THIS PLAN CANNOT BE EXECUTED TODAY
>
> **This is not what runs.** The live games demo is the **funnel** variant:
> [`RUNBOOK-FUNNEL.md`](RUNBOOK-FUNNEL.md) → `https://hbox-dregg.skunk-emperor.ts.net`.
>
> This runbook is **impossible as written**, for two independent reasons verified
> 2026-07-15:
>
> 1. **The gateway and hbox are on DIFFERENT TAILNETS.** The AWS edge is on
>    `100.64.0.x` (it is `100.64.0.1`); hbox is `hbox-dregg` `100.95.240.73` on
>    `skunk-emperor.ts.net`. The edge **cannot reach `100.95.240.73:8790`**. Step (0)
>    below ("add the gateway to the tailnet") is not a small prerequisite — it is the
>    whole plan, and it is unstarted. This is false at the **network layer**, not just
>    unimplemented.
> 2. **There is no Caddy on the edge.** The edge runs a docker compose stack with no
>    caddy container; `devnet.dregg.fg-goose.online/status` returns **HTTP 000**. The
>    "gateway's Caddy terminates TLS" premise has no gateway behind it.
>
> Also stale below: `docs/DEPLOY-PLAN.md` and `docs/ops/OPS-RUNBOOK.md` — cited
> repeatedly as "the real live topology" — **do not exist in this repo**.
>
> Kept because the hbox-side shape (units, health gate, rollback) is sound and the
> funnel variant reuses it. See `deploy/README.md` for the real topology.

# Games deploy runbook — the dregg games stack, public at games.dregg.fg-goose.online

The ordered go-live for the **standalone games public demo** (docs/DEPLOY-PLAN.md
Phase 0 + Phase 1): the `dreggnet-web-server` (all 5 games + the no-cheat-by-REPLAY
Descent leaderboard, node-free) on hbox, fronted by the **AWS gateway's Caddy** over
**Tailscale**, plus the `dregg-discord-bot` Descent daily on hbox. This makes the
go-live a **small, safe flip** — build → install → reload → health — not a new build.

**Honest scope.** AUTOMATED by `deploy-hbox.sh` (run on hbox): build the two binaries,
snapshot a rollback point, install the two user systemd units, reload, health-check
`/health`, and auto-revert on a failed gate. **EMBER-GATED** (this runbook's manual
steps, never touched by the script): add the gateway to the tailnet, DNS, the token
env, stop-the-old-bot, adding the games site block to the **gateway** Caddy, and the
go-live decision itself. The demo verifies by REPLAY; the portable STARK proof is the
labeled Phase-3 upgrade (docs/DEPLOY-PLAN.md), not a go-live blocker.

---

## Topology (the real live one — docs/ops/OPS-RUNBOOK.md)

Caddy lives on the **AWS gateway**, not hbox. The gateway is the sole public surface;
it reaches hbox over **Tailscale** (NOT WireGuard). hbox opens **no** public port.

```
  games.dregg.fg-goose.online  (DNS -> the AWS gateway)
        │  :443 TLS (Let's Encrypt, on the gateway)
  ┌──────▼───────── AWS GATEWAY (public) ─────────┐
  │  Caddy — serves *.dregg.fg-goose.online:      │
  │    • devnet.dregg.fg-goose.online  (existing) │
  │    • games.dregg.fg-goose.online   (NEW block)│  ← deploy/games/caddy/Caddyfile.games
  │         │  reverse_proxy over TAILSCALE       │
  └─────────┼─────────────────────────────────────┘
            │  100.95.240.73:8790   (tailnet node: hbox-dregg)
  ┌─────────▼──────────── hbox (private, tailnet) ─────────┐
  │  dregg-web-games (user unit)  100.95.240.73:8790       │  ← games, board, /health
  │  dregg-games-bot (user unit)  -> Discord + drand       │  ← Descent daily (standalone)
  └────────────────────────────────────────────────────────┘
```

- **The gateway's Caddy** terminates TLS and `reverse_proxy`s to `100.95.240.73:8790`
  over Tailscale — the same site-block + `strip_upstream_cors` pattern as the existing
  `devnet.dregg.fg-goose.online` block (deploy/aws/caddy/Caddyfile). The games block
  is `deploy/games/caddy/Caddyfile.games`, ADDED to the gateway config.
- **hbox** (tailnet node `hbox-dregg`, `100.95.240.73`) runs the two user units. The
  web server binds the **Tailscale interface** (`100.95.240.73:8790`, port 8790 is
  FREE — 8787/8781 are taken), so only tailnet peers (the gateway) can reach it; the
  public internet cannot. **Never** `0.0.0.0` (contrast drex-web wrongly on
  `0.0.0.0:8781`). The bot is standalone — no gateway route; it talks straight to
  Discord + `api.drand.sh` egress.
- **The private channel is Tailscale.** ⚠ The gateway is **NOT yet on the tailnet** —
  adding it is the named prerequisite (step 0). Once it is, `100.95.240.73:8790` (or
  `hbox-dregg:8790`) is reachable from the gateway with no inbound port opened on hbox.

---

## Ordered go-live

### (0) PREREQUISITE — add the AWS gateway to the tailnet  ⟨EMBER⟩
The gateway is **not yet a tailnet node**, so it cannot reach `100.95.240.73:8790`.
Join it to the same tailnet as `hbox-dregg` (e.g. `tailscale up` on the gateway with
an auth key, tagged appropriately), then confirm reachability:
```bash
# on the gateway, after joining the tailnet:
tailscale status | grep hbox-dregg           # hbox-dregg 100.95.240.73 ... active
curl -fsS http://100.95.240.73:8790/health   # once the hbox web unit is up (step d)
```
This is the currently-missing private channel. Nothing public is reachable until it
exists AND the gateway Caddy block is added (step d). This replaces the old WireGuard
plan — the live channel is **Tailscale**.

### (a) DNS — point games.dregg.fg-goose.online -> the gateway  ⟨EMBER⟩
Add an A/AAAA record `games.dregg.fg-goose.online` -> the AWS gateway's public IP
(same gateway that already serves `devnet.dregg.fg-goose.online`). Let's Encrypt (on
the gateway) needs this resolving + the gateway's :80/:443 reachable BEFORE Caddy can
issue a cert.

### (b) Place the env / tokens on hbox  ⟨EMBER⟩
Copy `deploy/games/.env.example` to hbox and fill the real values:
```bash
# on hbox:
mkdir -p ~/.config/dregg ~/.local/state/dregg-games
cp ~/dev/breadstuffs/deploy/games/.env.example ~/.config/dregg/games.env
$EDITOR ~/.config/dregg/games.env      # DISCORD_TOKEN / DISCORD_APP_ID / BOT_SECRET,
                                        # DESCENT_ANNOUNCE_CHANNEL_ID, DATABASE_URL;
                                        # DREGGNET_WEB_BIND=100.95.240.73:8790 (tailnet iface);
                                        # optional fhEgg quorum + strict v3 Dark AMM key/root/
                                        # exact-opening issuer policy
chmod 600 ~/.config/dregg/games.env
```
No prod token is ever committed or placed by an agent — this is ember's hand-placement
(same discipline as deploy/hbox/RUNBOOK.md). The `DREGG_GAMES_DOMAIN` /
`DREGG_GAMES_UPSTREAM` vars in that file are read by the **gateway** Caddy, not hbox.

### (c) ⚠ STOP THE OLD BOT FIRST — the GRAVITON bot  ⟨EMBER⟩
Two bots on one Discord token fire **every command twice**. The token is currently
held by the **graviton** bot (`deploy/aws/dregg-discord-bot.service`); hbox runs **no**
bot today, so there is no hbox bot to stop. Stop graviton's before the hbox games bot
starts:
```bash
# graviton (the deploy/aws unit — the current token holder):
ssh <graviton> 'sudo systemctl stop dregg-discord-bot'      # or disable --now
```
Skip only if you are certain no other process holds this token.

### (d) Run the deploy — hbox side, then the gateway side  ⟨AUTOMATED hbox / EMBER gateway⟩
**On hbox** (builds the 2 bins, installs the 2 user units; no Caddy — SKIP_CADDY=1 is
the default):
```bash
ssh hbox
cd ~/dev/breadstuffs/deploy/games
./deploy-hbox.sh --dry-run     # rehearse — prints every step, no side effects
./deploy-hbox.sh               # build -> snapshot -> install -> reload -> health (+auto-revert)
```
The web build uses the aggregate `public-shielded-games` feature. That is a
deployment invariant, not a default Cargo feature: ordinary library builds stay
lightweight, while the public binary cannot silently compile out the completed
fhEgg, private dungeon, or Dark AMM operation surfaces.
The script installs the two **user** units (with `loginctl enable-linger` so they
survive logout). Its health gate polls `http://100.95.240.73:8790/health` (the tailnet
iface the web unit binds — NOT localhost). Knobs: `SKIP_BOT=1` (web demo only),
`AUTO_REVERT=0`, `HEALTH_TIMEOUT=180`. (`SKIP_CADDY=0` is a legacy on-hbox-Caddy path —
NOT the real topology; leave it at the default 1.)

**On the AWS gateway** (add the games site block to the gateway Caddy + reload THERE —
after step 0):
```bash
# on the gateway (a checkout of deploy/games/caddy/Caddyfile.games available):
./deploy-hbox.sh gateway       # validates the block + prints the ember-gated append+reload
# then, as printed:
sudo sh -c 'cat deploy/games/caddy/Caddyfile.games >> /etc/caddy/Caddyfile'   # or paste it in
sudo caddy validate --adapter caddyfile --config /etc/caddy/Caddyfile          # whole merged config
sudo systemctl reload caddy
```
The block reverse-proxies over Tailscale to `100.95.240.73:8790`. It sits next to the
existing `devnet.dregg.fg-goose.online` block. (Set `DREGG_GAMES_DOMAIN` /
`DREGG_GAMES_UPSTREAM` in the gateway Caddy's environment to override the defaults.)

### (e) Health-check + smoke test  ⟨AUTOMATED gate, then MANUAL smoke⟩
The script's health gate polls `http://100.95.240.73:8790/health` (200 `{"status":"ok"}`)
on hbox. Then, by hand:
```bash
curl -fsS http://100.95.240.73:8790/health              # from the gateway (over Tailscale)
curl -fsS https://games.dregg.fg-goose.online/health    # 200 through the gateway Caddy/TLS
```
- Open `https://games.dregg.fg-goose.online/` — the landing + `/offerings` catalog load.
- Play a game; open `/descent/leaderboard` — the no-cheat board renders.
- Submit a run (`POST /descent/submit`) — it ranks and survives a restart (durable
  sqlite, re-verified by replay).
- In Discord: `/descent play` rolls the daily; confirm the announce channel posts.

### (f) Rollback  ⟨AUTOMATED⟩
A failed health gate **auto-reverts** to the pre-deploy snapshot. Manual:
```bash
./deploy-hbox.sh releases            # list snapshots
./deploy-hbox.sh rollback            # revert binaries to the newest snapshot + restart
./deploy-hbox.sh rollback <stamp>    # to a specific one
```
Take it fully offline instantly:
```bash
# hbox: stop the units
systemctl --user stop dregg-web-games dregg-games-bot
# gateway: ember removes the games.dregg.fg-goose.online block (or reloads without it)
#   -> the public surface is gone even if the hbox units keep running.
```

### (g) Firewall / ports  ⟨EMBER⟩
hbox `ufw` is **INACTIVE** and hbox already listens on `0.0.0.0` for unrelated
services (OPS-RUNBOOK). Because the web server binds the **Tailscale iface**
(`100.95.240.73:8790`), the public internet can never reach it directly; the gateway
holds :443. Before going public:
- Open **no** public port on hbox for the games demo. Allow only the Tailscale
  interface (`tailscale0`) + ssh.
- The node's QUIC **:9420** is only relevant if you also run a testnet node here
  (Phase 2) — the games demo is node-free and does not open it.
```bash
sudo ufw default deny incoming
sudo ufw default allow outgoing
sudo ufw allow 22/tcp
sudo ufw allow in on tailscale0                # the gateway's private channel only
sudo ufw enable
sudo ss -tlnp | grep 8790                      # verify: LISTEN 100.95.240.73:8790, NOT 0.0.0.0
```

### (go-live) The flip  ⟨EMBER⟩
With (0)–(g) green and the health gate passed, the demo is live. The go-live decision
— the honest-grade + stranger-usable bar — is ember's, per OPS-RUNBOOK's go-live
checklist.

---

## What is automated vs ember-gated (the honest cut)

| Step | Who |
|---|---|
| build the web + bot binaries (on hbox) | **script** |
| snapshot a rollback point | **script** |
| install user systemd units + enable-linger | **script** |
| health-check `100.95.240.73:8790/health` + auto-revert on failure | **script** |
| validate the gateway Caddy block (`./deploy-hbox.sh gateway`) | **script** |
| **(0)** add the AWS gateway to the tailnet | ember |
| DNS `games.dregg.fg-goose.online` -> the gateway | ember |
| place `~/.config/dregg/games.env` (tokens) + chmod 600 | ember |
| stop the old **graviton** bot first (double-fire) | ember |
| append the games block to the gateway Caddy + reload caddy | ember |
| the go-live decision | ember |

## Caveats (named, once)
- **Caddy is on the gateway, not hbox.** `SKIP_CADDY=1` is the default; the games site
  block (`caddy/Caddyfile.games`) is ADDED to the gateway's Caddy (next to
  `devnet.dregg.fg-goose.online`) and reloaded THERE. `deploy-hbox.sh gateway` validates
  it; the append+reload are ember's manual steps (they touch the gateway's system Caddy).
- **Tailscale, not WireGuard.** The gateway↔hbox private channel is Tailscale; the
  gateway must be a tailnet node (step 0) before it can reach `100.95.240.73:8790`.
- **Two cargo workspaces.** `dreggnet-web` is a root-workspace member (builds into
  `target/`); `dregg-discord-bot` is a **separate, excluded workspace** (sqlx links-
  conflict; `discord-bot/Cargo.toml`) that builds into `discord-bot/target/`. The
  script + the bot unit account for this (the bot's `ExecStart` points at
  `discord-bot/target/release/...`). A plain `cargo build -p dregg-discord-bot` from
  the repo root FAILS — build it from within `discord-bot/`.
- **Rate limiting** is NOT in Caddy core — it needs the `caddy-ratelimit` plugin baked
  into a custom `xcaddy` build on the GATEWAY (named in `caddy/Caddyfile.games`). Until
  then, per-IP rate limiting is an ember-gated go-live item; the body-size cap (2 MB) is
  active in the block.
- **Live game sessions are ephemeral** — a restart drops in-progress sessions; the
  Descent leaderboard is durable (sqlite, re-verified by replay on boot).
- The **Descent daily needs egress** to `https://api.drand.sh` (BLS-verified round);
  hbox has egress (OPS-RUNBOOK dry-run).
- One combined `games.env` puts the Discord token in the web server's environment too
  (same box, same user). To isolate, split into two `EnvironmentFile`s and point each
  unit at its own.
