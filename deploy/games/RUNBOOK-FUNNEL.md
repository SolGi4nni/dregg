# Games deploy runbook — FUNNEL variant (public via Tailscale Funnel, no gateway)

The fastest path to **games-on-a-devnet live for testing**: expose the
`dreggnet-web-server` publicly **directly from hbox** with `tailscale funnel` —
**no AWS gateway, no gateway↔tailnet join, no DNS, no Caddy**. Tailscale Funnel
serves a local port at `https://hbox-dregg.<tailnet>.ts.net` with auto-TLS, so the
public edge is one command. The games anchor submitted Descent runs on the hbox
solo devnet node (`127.0.0.1:8420`).

Contrast the committed **gateway** variant (`deploy/games/RUNBOOK.md`): that fronts
hbox with the AWS gateway's Caddy over Tailscale and needs the gateway on the tailnet
+ DNS + a Caddy block. This funnel variant drops that whole leg.

**What this gets you** (honest scope):
- Games publicly live from hbox **in minutes** — no EC2 gateway, no DNS record, no
  Caddy config, no Let's Encrypt wait. Tailscale supplies the public hostname + TLS.
- Submitted runs **anchor on a real devnet node** (the hbox solo `:8420` faucet node)
  — `resolve_node_target` → `NodeTarget::Federation`, a real committed turn confirmed
  on the node's `GET /api/receipts`.

**The one-time cost:** the hbox `:8420` node must be **unlocked** and its **operator
cell faucet-materialized once** (step a). After that the funnel flip is a single command.

**The ember-gated flip:** the `tailscale funnel 8790` command **is** the
public-exposure decision. `deploy-hbox.sh --funnel` builds + installs the web unit on
**loopback** and stops there; nothing is public until a human runs that one command.

**The pretty-domain follow-up (later, not needed for testing):** the public URL is
`https://hbox-dregg.<tailnet>.ts.net`. A prettier `games.dregg.fg-goose.online` is a
follow-up — either a `CNAME games.dregg.fg-goose.online → hbox-dregg.<tailnet>.ts.net`
(Tailscale custom-domain / a fronting proxy for the vanity name) or the full **gateway
variant** (`RUNBOOK.md`) once the gateway is on the tailnet. The funnel host works for
testing today without it.

---

## Topology (funnel — no gateway, no Caddy, no DNS)

> `<tailnet>` here is **`skunk-emperor.ts.net`** (Funnel is enabled on it; `nextop`
> already funnels), and `hbox-dregg` is `100.95.240.73`. So the concrete public URL is
> `https://hbox-dregg.skunk-emperor.ts.net`. `tailscale funnel status` prints the exact
> host after the flip.

```
  https://hbox-dregg.<tailnet>.ts.net        ← Tailscale Funnel (public, auto-TLS)
        │  Funnel proxies the PUBLIC :443 → the LOCAL :8790
  ┌─────▼───────────────── hbox (tailnet node hbox-dregg, 100.95.240.73) ─────────┐
  │  tailscale funnel 8790  ── public edge (TLS + hostname), no Caddy needed        │
  │  dregg-web-games-funnel (user unit)   127.0.0.1:8790   ← games, board, /health  │
  │        │  DREGG_NODE_URL=http://127.0.0.1:8420                                   │
  │  dregg-node (solo devnet, --enable-faucet)   127.0.0.1:8420  ← anchors runs      │
  └────────────────────────────────────────────────────────────────────────────────┘
```

- The web server binds **loopback** (`127.0.0.1:8790`) — Funnel serves a **local**
  port, reaching into localhost. (Contrast the gateway variant's tailnet-iface bind
  `100.95.240.73:8790`, which a separate gateway Caddy reverse-proxies.) `8790` is FREE
  on hbox (`8787`/`8781` are taken).
- **Tailscale Funnel is the public edge** — it terminates TLS and owns the public
  hostname `hbox-dregg.<tailnet>.ts.net`. No Caddy, no cert management, no DNS.
- The **hbox solo devnet node** (`127.0.0.1:8420`, `--enable-faucet`) is the anchor
  target — the games settle winning runs onto its ledger.
- Funnel supports only `443` / `8443` / `10000` as the **public** port; we reverse from
  the public `443` to the local `8790`. `tailscale funnel 8790` does exactly this.

---

## Ordered go-live

Mark: ⟨EMBER⟩ = a human does it (includes every public-exposure step);
⟨SCRIPT⟩ = `deploy-hbox.sh --funnel` does it.

### (a) DEVNET BRING-UP — the hbox `:8420` node up + unlocked + operator cell faucet'd  ⟨EMBER⟩

The games need a running node to anchor runs on. **Fast path: use the existing hbox
solo `:8420` faucet node.** (Alternative: spin the fresh n=4 federation — below.)

**a.1 — the node is up.** A solo `dregg-node` with the faucet enabled runs on hbox
`127.0.0.1:8420`. Confirm:
```bash
# on hbox:
curl -fsS http://127.0.0.1:8420/status | jq '{federation_mode, public_key, state_producer}'
```
If it is NOT running, start your devnet node bound `127.0.0.1:8420` with `--enable-faucet`
(the same flag `deploy/aws/dregg-gateway.service` uses). A loopback devnet node needs no
passphrase.

**a.2 — UNLOCK the operator cipherclerk** (so it can sign the anchor turn). Check
whether it is already unlocked, and whether a passphrase is even set:
```bash
curl -fsS http://127.0.0.1:8420/api/node/identity | jq '{public_key, agent_cell, unlocked, agent_balance}'
```
- `unlocked: true` already → nothing to do; skip to a.3.
- `unlocked: false` **and** a passphrase is set → unlock and capture the bearer token:
  ```bash
  curl -fsS -X POST -H 'content-type: application/json' \
    --data '{"passphrase":"<DEVNET_PASSWORD>"}' \
    http://127.0.0.1:8420/cipherclerk/unlock | jq '{success, unlocked, bearer_token}'
  ```
  Put the returned `bearer_token` into `~/.config/dregg/games-funnel.env` as
  `DREGG_NODE_BEARER=<token>` (step b). A **loopback devnet with no passphrase** admits
  loopback callers during the setup window and needs **no** bearer — leave it unset.

**a.3 — FAUCET-MATERIALIZE the operator cell once.** A fresh node's operator agent cell
is not materialized until it receives value, so the games' anchor (an operator
`EmitEvent`) is refused (`cell not found`) until this one-time step. Read the operator
identity, then faucet its cell with `amount: 0` (materialize, no drain):
```bash
ID=$(curl -fsS http://127.0.0.1:8420/api/node/identity)
CELL=$(echo "$ID" | jq -r .agent_cell)
PK=$(echo "$ID" | jq -r .public_key)
curl -fsS -X POST -H 'content-type: application/json' \
  --data "{\"recipient\":\"$CELL\",\"amount\":0,\"public_key\":\"$PK\"}" \
  http://127.0.0.1:8420/api/faucet | jq .
# confirm materialized: agent_balance is now non-null
curl -fsS http://127.0.0.1:8420/api/node/identity | jq '.agent_balance'
```
(This is the same one-time bring-up `dreggnet-web/tests/devnet_settle.rs` documents — its
`print_operator_cell_id` helper reproduces `agent_cell` via
`CellId::derive_raw(pubkey, H("default"))`; `GET /api/node/identity` hands you the same
`agent_cell` directly.)

> **Alternative — spin the fresh n=4 federation** instead of the solo `:8420` node: bring
> up the federation, point `DREGG_NODE_URL` at one member's API port in
> `games-funnel.env`, and run the same a.2/a.3 unlock + faucet against that member. The
> solo `:8420` node is the fast path; use it unless you specifically want multi-node
> finality behind the demo.

### (b) Place the funnel env on hbox  ⟨EMBER⟩
```bash
# on hbox:
mkdir -p ~/.config/dregg ~/.local/state/dregg-games
cp ~/dev/breadstuffs/deploy/games/.env.funnel.example ~/.config/dregg/games-funnel.env
$EDITOR ~/.config/dregg/games-funnel.env
#   DREGGNET_WEB_BIND=127.0.0.1:8790   (loopback — Funnel proxies it)
#   DREGG_NODE_URL=http://127.0.0.1:8420
#   DREGG_NODE_BEARER=<token>          (only if the node has a passphrase; else leave unset)
#   DATABASE_URL=sqlite:/home/hbox/.local/state/dregg-games/leaderboard.db
chmod 600 ~/.config/dregg/games-funnel.env
```
No token is committed or placed by an agent — ember's hand-placement (same discipline as
`deploy/hbox/RUNBOOK.md`).

### (c) Run the deploy — build + install the web unit on LOOPBACK  ⟨SCRIPT⟩
```bash
ssh hbox
cd ~/dev/breadstuffs/deploy/games
./deploy-hbox.sh --funnel --dry-run   # rehearse — prints every step, no side effects
./deploy-hbox.sh --funnel             # build -> snapshot -> install -> reload -> health
```
`--funnel` builds `dreggnet-web-server`, installs the **funnel** user unit
(`dregg-web-games-funnel.service`, bound `127.0.0.1:8790`, `DREGG_NODE_URL=:8420`) with
`loginctl enable-linger` so it survives logout, and **skips the gateway/Caddy leg
entirely**. Its health gate polls `http://127.0.0.1:8790/health`. The funnel fast-path
is **web-only** (`SKIP_BOT=1` by default; the Discord bot is not a funnel surface).
On a passing gate it **prints** the ember-gated `tailscale funnel` flip — it does **not**
run it.

### (d) Health-check localhost, then ⚠ THE PUBLIC-EXPOSURE FLIP  ⟨(c) SCRIPT gate · flip EMBER⟩

The script's gate already confirmed loopback health. By hand (still private):
```bash
curl -fsS http://127.0.0.1:8790/health     # 200 {"status":"ok"} — loopback, NOT public yet
```

**⚠ EMBER-GATED PUBLIC-EXPOSURE FLIP** — this single command makes the demo public:
```bash
tailscale funnel --bg 8790                 # serve 127.0.0.1:8790 publicly (public 443 -> local 8790)
```
Confirm the public URL:
```bash
tailscale funnel status                    # shows https://hbox-dregg.<tailnet>.ts.net -> 127.0.0.1:8790
curl -fsS https://hbox-dregg.<tailnet>.ts.net/health   # 200 through Funnel's TLS
```
(`tailscale serve --bg --https=443 http://127.0.0.1:8790` then `tailscale funnel on` is
the equivalent explicit form.) Nothing is public until this runs; running it **is** the
go-live decision.

### (e) Smoke test  ⟨EMBER⟩
Against the public URL `https://hbox-dregg.<tailnet>.ts.net`:
- Open `/` and `/offerings` — the landing + catalog load.
- Play a game (`/offerings/dungeon/session/demo`, `/offerings/automatafl/...`, …) — a
  move lands a real executor receipt; a crafted illegal move is refused (anti-ghost).
- `/descent/leaderboard` — the no-cheat board renders.
- Submit a run (`POST /descent/submit`) — it ranks in-process AND **anchors on the node**.
  Confirm on the node's ledger:
  ```bash
  curl -fsS http://127.0.0.1:8420/api/receipts | jq '.[-3:]'   # the anchored turn is present
  ```
  (A losing / forged run is refused by the verify-gate before it can settle — the node is
  never touched for a non-win. Fail-closed.)

### (f) Take-down  ⟨EMBER⟩
Remove the public surface instantly (the loopback unit keeps running):
```bash
tailscale funnel --https=443 off           # public URL gone; 127.0.0.1:8790 still serves locally
tailscale funnel status                     # confirm no funnel
```
Stop the web unit entirely / roll back:
```bash
systemctl --user stop dregg-web-games-funnel
./deploy-hbox.sh releases                    # list rollback snapshots
./deploy-hbox.sh --funnel rollback           # revert binaries to newest snapshot + restart
```

---

## What is automated vs ember-gated (the honest cut)

| Step | Who |
|---|---|
| build `dreggnet-web-server` (on hbox) | **script** (`--funnel`) |
| snapshot a rollback point | **script** |
| install the funnel user unit (loopback:8790) + enable-linger | **script** |
| health-check `127.0.0.1:8790/health` + auto-revert on failure | **script** |
| **(a)** devnet node up + **unlock** + **faucet-materialize** the operator cell | ember |
| place `~/.config/dregg/games-funnel.env` + chmod 600 | ember |
| **⚠ `tailscale funnel 8790`** — the PUBLIC-EXPOSURE flip | ember |
| smoke test the public URL / take-down | ember |

## Caveats (named, once)
- **Funnel serves LOOPBACK.** The unit binds `127.0.0.1:8790`; Funnel proxies the local
  port. Never bind `0.0.0.0` / the tailnet iface for the funnel variant.
- **The `:8420` node is the anchor.** The one-time unlock + faucet-materialize (step a) is
  required before runs anchor; until then a submitted run still ranks in-process, but its
  settle is refused (`cell not found`) — fail-closed, not a silent success.
- **Funnel must be enabled on the tailnet** (it is — `nextop` already funnels on this
  tailnet). If `tailscale funnel` reports Funnel is not available, that is an admin
  (tailnet policy) enablement, an ember step.
- **Live game sessions are ephemeral** — a restart drops in-progress sessions; the Descent
  leaderboard is durable (sqlite, re-verified by replay on boot).
- **Public port is 443** — Funnel only supports `443`/`8443`/`10000` publicly; we reverse
  the public `443` to the local `8790`. There is one public surface per tailnet node on
  `443`; if hbox-dregg already funnels something on `443`, use `8443`/`10000` or free it.
- **Pretty domain is a follow-up** (see the honest-scope note above) — not needed for
  testing on `hbox-dregg.<tailnet>.ts.net`.
