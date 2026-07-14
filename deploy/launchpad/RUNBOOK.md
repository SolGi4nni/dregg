# Launchpad deploy runbook — the revenue rehearsal, public at launchpad.dregg.fg-goose.online

The ordered go-live for the **dregg launchpad product layer** on a **public testnet**
— the revenue rehearsal. Two pieces: (1) the **launchpad-web** product surface (create /
bid / token-page / replayable-discovery, `launchpad-web/server.mjs`) on hbox, fronted by
the **AWS gateway's Caddy** over **Tailscale** — the SAME gateway↔Tailscale↔hbox pattern
the games deploy established (`deploy/games/RUNBOOK.md`); and (2) the on-chain
**DreggLaunchpad** contract deployed to a public testnet (Base-Sepolia 84532 or Robinhood
Chain 46630) via `chain/script/DeployLaunchpad.s.sol`. This makes the go-live a **small,
safe flip** — `npm ci` → install → reload → health — not a new build.

**rung-1 needs ZERO dregg.** The launch runs OPEN / REPLAYABLE (attestor = `address(0)`,
permissionless on-chain finalize): the contract clears itself from the public revealed
book, dregg is not even in the settlement loop, and no private node / VK / attestor is
required. The launchpad-web + the on-chain contracts are the **whole thing** for rung-1
(`docs/deos/PRIVATE-DREGG-PUBLIC-LAUNCHPAD-ARCHITECTURE.md` §2.3). This is the shortest
path to real (testnet) revenue.

**Honest scope.** AUTOMATED by `deploy-launchpad.sh` (run on hbox): `npm ci`, snapshot a
rollback point, install the one user systemd unit, reload, health-check `/api/config`,
auto-revert on a failed gate; plus a **keyless** `contract-dryrun` that SIMULATES the
testnet deploy (no `--broadcast`). **EMBER-GATED** (this runbook's manual steps, never
touched by the script): add the gateway to the tailnet, DNS, the env (`LAUNCHPAD_ADDRESS`),
the **funded-key contract broadcast**, adding the launchpad site block to the **gateway**
Caddy, and the go-live decision. This is **PREP + validate only** — nothing here
broadcasts, exposes a surface, or places a secret.

---

## Topology (the real live one — the games pattern, `docs/deos/DEVNET-DEPLOYMENT-REALITY.md`)

Caddy lives on the **AWS gateway**, not hbox. The gateway is the sole public surface; it
reaches hbox over **Tailscale**. hbox opens **no** public port. The launchpad is a **NEW,
SEPARATE** domain + site-block NEXT TO the existing games + devnet blocks — it does not
edit them.

```
  launchpad.dregg.fg-goose.online  (DNS -> the AWS gateway)
        │  :443 TLS (Let's Encrypt, on the gateway)
  ┌──────▼───────── AWS GATEWAY (public) ─────────┐
  │  Caddy — serves *.dregg.fg-goose.online:      │
  │    • devnet.dregg.fg-goose.online   (existing)│
  │    • games.dregg.fg-goose.online    (games)   │  ← deploy/games/caddy/Caddyfile.games
  │    • launchpad.dregg.fg-goose.online (NEW)     │  ← deploy/launchpad/caddy/Caddyfile.launchpad
  │         │  reverse_proxy over TAILSCALE        │
  └─────────┼─────────────────────────────────────┘
            │  100.95.240.73:8785   (tailnet node: hbox-dregg)
  ┌─────────▼──────────── hbox (private, tailnet) ─────────┐
  │  dregg-launchpad-web (user unit)  100.95.240.73:8785   │  ← create / bid / token / discovery / API
  └────────────────────────────────────────────────────────┘
            │ browser drives the REAL DreggLaunchpad with the USER's own wallet
            ▼
  ┌──────── public testnet (Base-Sepolia 84532 / Robinhood Chain 46630) ────────┐
  │  DreggLaunchpad.sol  (escrow + hard-capped token + never-drainable pool)     │
  └──────────────────────────────────────────────────────────────────────────────┘
```

- **The gateway's Caddy** terminates TLS and `reverse_proxy`s to `100.95.240.73:8785` over
  Tailscale — the same site-block + strip-upstream-CORS pattern as the games block. The
  launchpad block is `deploy/launchpad/caddy/Caddyfile.launchpad`, ADDED to the gateway
  config next to the games block (its own snippet name `strip_upstream_cors_launchpad`, so
  the two coexist).
- **hbox** runs the one user unit. launchpad-web binds the **Tailscale interface**
  (`100.95.240.73:8785`, port 8785 is FREE — 8790/8781/8787 are the games web / drex-web /
  dreggcloud) via `LAUNCHPAD_HOST`, so only tailnet peers (the gateway) can reach it.
  **Never** `0.0.0.0`.
- **The private channel is Tailscale.** ⚠ The gateway is the **SAME shared prerequisite**
  as games (step 0): once it is a tailnet node, BOTH the games (:8790) and the launchpad
  (:8785) upstreams are reachable with no inbound port opened on hbox.

---

## Ordered go-live

### (0) PREREQUISITE — add the AWS gateway to the tailnet  ⟨EMBER⟩  ⟨SHARED with games⟩
The gateway must be a tailnet node to reach `100.95.240.73:8785`. This is the **same** join
as the games deploy (`deploy/games/RUNBOOK.md` step 0) — if games is already up, this is
done. Confirm:
```bash
# on the gateway, after joining the tailnet:
tailscale status | grep hbox-dregg              # hbox-dregg 100.95.240.73 ... active
curl -fsS http://100.95.240.73:8785/api/config  # once the hbox launchpad unit is up (step d)
```

### (a) DNS — point launchpad.dregg.fg-goose.online -> the gateway  ⟨EMBER⟩
Add an A/AAAA record `launchpad.dregg.fg-goose.online` -> the AWS gateway's public IP (the
same gateway that already serves `devnet.` / `games.`). Let's Encrypt (on the gateway) needs
this resolving + :80/:443 reachable BEFORE Caddy can issue the cert.

### (b) Place the env on hbox  ⟨EMBER⟩
```bash
# on hbox:
mkdir -p ~/.config/dregg ~/.local/state/dregg-launchpad
cp ~/dev/breadstuffs/deploy/launchpad/.env.example ~/.config/dregg/launchpad.env
$EDITOR ~/.config/dregg/launchpad.env    # LAUNCHPAD_ADDRESS (from step c), LAUNCHPAD_RPC,
                                          # LAUNCHPAD_HOST=100.95.240.73, PORT=8785
chmod 600 ~/.config/dregg/launchpad.env
```
**No prod key is ever committed or placed by an agent** — and for rung-1 the launchpad-web
process holds **no key at all**: the browser drives the contract with the USER's wallet; the
backend only READS the chain over `LAUNCHPAD_RPC`. The `DREGG_LAUNCHPAD_DOMAIN` /
`DREGG_LAUNCHPAD_UPSTREAM` vars in that file are read by the **gateway** Caddy, not hbox.

### (c) Deploy the contract to the testnet  ⟨DRY-RUN automated / BROADCAST ember⟩
First rehearse keylessly (no key, no tx — compiles, deploys in-sim, runs a full fair-launch
demo, asserts the uniform clearing):
```bash
cd ~/dev/breadstuffs/deploy/launchpad
./deploy-launchpad.sh contract-dryrun                    # pure local simulation
DEPLOY_RPC=base_sepolia ./deploy-launchpad.sh contract-dryrun   # READ-ONLY vs the real RPC
```
Then the **ember-only** broadcast (a real tx; needs a funded testnet key):
```bash
# Base-Sepolia (84532):
export DEPLOYER_PRIVATE_KEY=0x<funded testnet key>       # EMBER input, NEVER committed
export BASE_SEPOLIA_RPC_URL=https://sepolia.base.org
cd ~/dev/breadstuffs/chain
forge script script/DeployLaunchpad.s.sol:DeployLaunchpad --rpc-url base_sepolia --broadcast --verify -vvv

# Robinhood Chain (46630) instead:
export ROBINHOOD_TESTNET_RPC_URL=https://rpc.testnet.chain.robinhood.com
forge script script/DeployLaunchpad.s.sol:DeployLaunchpad --rpc-url robinhood_testnet --broadcast -vvv
```
The broadcast deploys **one** contract (the launchpad) and it is ready for real launches
immediately — registration is permissionless. Put the printed `DreggLaunchpad :` address
into `~/.config/dregg/launchpad.env` as `LAUNCHPAD_ADDRESS` (step b).

### (d) Run the deploy — hbox side, then the gateway side  ⟨AUTOMATED hbox / EMBER gateway⟩
**On hbox** (`npm ci` + install the one user unit; no Caddy — SKIP_CADDY=1 default):
```bash
ssh hbox
cd ~/dev/breadstuffs/deploy/launchpad
./deploy-launchpad.sh --dry-run     # rehearse — prints every step, no side effects
./deploy-launchpad.sh               # npm ci -> snapshot -> install -> reload -> health (+auto-revert)
```
The health gate polls `http://100.95.240.73:8785/api/config` (the tailnet iface the unit
binds — NOT localhost). Knobs: `AUTO_REVERT=0`, `HEALTH_TIMEOUT=180`.

**On the AWS gateway** (add the launchpad site block to the gateway Caddy + reload THERE —
after step 0, NEXT TO the games block, without editing it):
```bash
# on the gateway (a checkout with deploy/launchpad/caddy/Caddyfile.launchpad available):
./deploy-launchpad.sh gateway       # validates the block + prints the ember-gated append+reload
# then, as printed:
sudo sh -c 'cat deploy/launchpad/caddy/Caddyfile.launchpad >> /etc/caddy/Caddyfile'   # or paste it in
sudo caddy validate --adapter caddyfile --config /etc/caddy/Caddyfile                  # whole merged config
sudo systemctl reload caddy
```

### (e) Health-check + smoke test  ⟨AUTOMATED gate, then MANUAL smoke⟩
```bash
curl -fsS http://100.95.240.73:8785/api/config              # from the gateway (over Tailscale)
curl -fsS https://launchpad.dregg.fg-goose.online/api/config # 200 through the gateway Caddy/TLS
```
- Open `https://launchpad.dregg.fg-goose.online/` — the discovery page + catalog load.
- **Connect a wallet** (`window.ethereum`, on the testnet chain).
- **Run a rung-1 OPEN launch end-to-end on the testnet**: `create.html` register a launch
  with a disclosed schedule → sealed `commitBid` → `revealBid` → permissionless
  `finalizeClearing` (uniform price) → `settleBid` → token page shows the one clearing price
  everyone paid + the holder distribution. Every number is checkable on-chain; no attestor,
  no dregg node.

### (f) Rollback  ⟨AUTOMATED⟩
A failed health gate **auto-reverts** (restores the prior unit / stops it). Manual:
```bash
./deploy-launchpad.sh releases            # list snapshots
./deploy-launchpad.sh rollback            # restore the unit from the newest snapshot + restart
```
Take it fully offline instantly:
```bash
systemctl --user stop dregg-launchpad-web            # hbox: stop the unit
# gateway: ember removes the launchpad.dregg.fg-goose.online block (or reloads without it)
```

### (g) Firewall / ports  ⟨EMBER⟩
Because the server binds the **Tailscale iface** (`100.95.240.73:8785`), the public internet
can never reach it directly; the gateway holds :443. Open **no** public port on hbox for the
launchpad; allow only `tailscale0` + ssh (same posture as `deploy/games/RUNBOOK.md` step g).
```bash
sudo ss -tlnp | grep 8785    # verify: LISTEN 100.95.240.73:8785, NOT 0.0.0.0
```

### (go-live) The flip  ⟨EMBER⟩
With (0)–(g) green and the health gate passed, the revenue rehearsal is live on the testnet.
The go-live decision is ember's.

---

## What is automated vs ember-gated (the honest cut)

| Step | Who |
|---|---|
| `npm ci` the launchpad-web deps (on hbox) | **script** |
| snapshot a rollback point (unit + git rev) | **script** |
| install the user systemd unit + enable-linger | **script** |
| health-check `100.95.240.73:8785/api/config` + auto-revert | **script** |
| **keyless** contract deploy DRY-RUN (`contract-dryrun`) | **script** |
| validate the gateway Caddy block (`./deploy-launchpad.sh gateway`) | **script** |
| **(0)** add the AWS gateway to the tailnet (shared with games) | ember |
| DNS `launchpad.dregg.fg-goose.online` -> the gateway | ember |
| place `~/.config/dregg/launchpad.env` + chmod 600 | ember |
| the **contract testnet BROADCAST** (funded key + `--broadcast`) | ember |
| append the launchpad block to the gateway Caddy + reload | ember |
| the go-live decision | ember |

## Caveats (named, once)
- **rung-1 only, needs ZERO dregg.** This rehearsal runs OPEN / REPLAYABLE launches
  (`attestor = address(0)`, permissionless on-chain finalize). rung-2 (a real Groth16
  clearing attestor) and rung-3 (shielded, private-dregg clearing) are the named upgrades
  (`PRIVATE-DREGG-PUBLIC-LAUNCHPAD-ARCHITECTURE.md` §3) — NOT part of this rehearsal.
- **Caddy is on the gateway, not hbox.** `SKIP_CADDY=1` is the default; the launchpad block
  is a NEW block ADDED to the gateway's Caddy (next to games + devnet) and reloaded THERE.
  It does not edit the games block — distinct domain + distinct snippet name.
- **Tailscale, not the public internet.** The gateway↔hbox channel is Tailscale; the gateway
  must be a tailnet node (step 0, shared with games) before it can reach `100.95.240.73:8785`.
- **The launchpad-web holds no key.** The browser drives the contract with the user's own
  wallet; the backend only READS the chain. The funded deployer key (step c) is ember's, used
  once for the contract broadcast, never placed on hbox.
- **Rate limiting** is NOT in Caddy core — it needs the `caddy-ratelimit` plugin in a custom
  `xcaddy` build on the GATEWAY (named in `caddy/Caddyfile.launchpad`). Until then, per-IP
  rate limiting is an ember-gated go-live item; the body-size cap (2 MB) is active in the block.
- **Testnet, dev ceremony.** This is a public *testnet* rehearsal (no mainnet, no real value).
  A concrete attestor + the production MPC VK ceremony are ember-gated future steps.
