# OPS-RUNBOOK — hosted TESTNET demo (gateway + hbox infra)

The runbook for hosting dregg's clickable demos (**DrEX** — `drex-web/`; and the
**launchpad** — `launchpad-web/`) as a **testnet-only, honestly-graded** public
demo, with **no real value at risk**. This is the GROUNDWORK document: the
architecture, the security review, the copy-pasteable deploy/host procedures, and
the go-live checklist. The **live flip is ember-gated** — it happens only after
the core work lands, the security review signs off, and ember clears the audit
bar (see [Go-live checklist](#go-live-checklist)).

Honest scope up front: these are **unaudited testnet demos**. They settle against
public testnets (Base-Sepolia `84532`, optionally Robinhood Chain `46630`) with
**throwaway keys and no real custody**. Every trust claim in the UIs is graded
inline (PROVED Lean theorem / ATTESTED / BUILT-on-chain / REPLAYABLE). Nothing
here touches mainnet or real funds.

---

## Architecture

Two hosts, one exposed surface.

```
                         PUBLIC INTERNET
                               │
                    (DNS: demo.dregg.net, TLS)
                               │
                 ┌─────────────▼──────────────┐
                 │      AWS GATEWAY (public)   │   ← EMBER wires this
                 │  • TLS termination (Caddy/  │     (out of scope for
                 │    nginx, LetsEncrypt)      │      this runbook — see
                 │  • reverse-proxy → hbox     │      "What needs ember")
                 │  • rate-limit + abuse guard │
                 │  • the ONLY exposed surface │
                 └─────────────┬──────────────┘
                               │
                    PRIVATE CHANNEL (not public)
                    WireGuard tunnel  ── recommended
                    (or SSH reverse-tunnel; see below)
                               │
                 ┌─────────────▼──────────────┐
                 │      hbox  (private infra)  │   ← THIS runbook
                 │                             │
                 │  drex-web serve.mjs   :8781 │  bind 127.0.0.1 / wg iface
                 │  launchpad server.mjs :8785 │  bind 127.0.0.1 / wg iface
                 │  launchpad indexer (in-proc)│  → testnet RPC (egress)
                 │  drex_clear matcher   ─────────► persvati (prebuilt bin)
                 │  proving pipeline (fold/     │    or local target/
                 │    shrink/Groth16) — offline │
                 └─────────────┬──────────────┘
                               │ HTTPS egress only
                    ┌──────────▼───────────┐
                    │  PUBLIC TESTNET RPC  │  Base-Sepolia / Robinhood
                    │  (read + testnet tx) │  (verified in dry-run: hbox
                    └──────────────────────┘   reaches sepolia.base.org)
```

- **AWS gateway (public):** the single exposed surface. Terminates TLS, reverse-
  proxies to the hbox demo ports over the private channel, and rate-limits.
  Wired by ember — this runbook does **not** configure it. It follows the same
  `deploy/aws` Caddy-fronted topology the existing ops set describes
  (`docs/ops/README.md`).
- **hbox (private infra):** the demo web servers, the launchpad indexer, the
  DrEX matcher hop, and the proving pipeline. hbox is **not publicly reachable**;
  the gateway is its only ingress. The demo ports bind to `127.0.0.1` (or the
  WireGuard interface) — never `0.0.0.0`.
- **Private channel (gateway ↔ hbox):** three options, recommended first:
  1. **WireGuard tunnel (recommended).** A point-to-point `wg0` between gateway
     and hbox; the gateway proxies to `hbox-wg-ip:8781/8785`. Encrypted, keyed,
     survives NAT with `PersistentKeepalive`, and needs **no inbound port opened
     on hbox** (hbox dials out / holds the tunnel). Best fit: hbox sits behind a
     residential NAT (egress IP observed `73.4.118.165`), and a wg tunnel needs no
     hbox port-forward.
  2. **SSH reverse-tunnel.** From hbox: `ssh -N -R 8781:127.0.0.1:8781 gateway`
     (and `:8785`) via an autossh/systemd unit. Zero inbound on hbox; simplest to
     stand up; the gateway proxies to its own `127.0.0.1:8781`. Weaker than wg for
     a durable multi-service link but fine for a first demo.
  3. **Cloud private link / VPC peering.** Heavier; only if hbox moves into a
     cloud VPC. Not recommended for the home-box reality.

  **Recommendation: WireGuard.** It gives an authenticated, encrypted channel with
  no inbound hbox exposure, and scales to the indexer/proving traffic later.

---

## Security (reasonably-secured testnet)

The threat model of a **testnet demo with no custody**: the worst a full compromise
of the demo yields is (a) a defaced/downed demo page, (b) spent testnet gas from a
throwaway key (no value), and (c) reputational — someone points at an unaudited
demo as if it were production. There is **no real-value theft surface** because
there is no real custody and no mainnet key on the box. The controls below keep it
in that box.

- **hbox firewall — gateway ingress only.** ⚠ **Finding from the dry-run: hbox
  `ufw` is currently INACTIVE**, and hbox already listens on `0.0.0.0` for several
  unrelated services (`:80`, `:8091`, `:8787`, `:8799`) with a residential egress
  IP. Before ANY hosted demo, enable a default-deny inbound firewall:
  ```bash
  sudo ufw default deny incoming
  sudo ufw default allow outgoing
  sudo ufw allow 22/tcp                       # ssh (or restrict to your admin IP)
  sudo ufw allow in on wg0                     # the gateway private channel only
  sudo ufw enable
  ```
  The demo ports (`8781`, `8785`) must **never** be reachable except via the
  gateway. In the dry-run they were bound to `127.0.0.1` (verified:
  `LISTEN 127.0.0.1:18781`, not `0.0.0.0`). In production, bind to `127.0.0.1`
  (gateway on the same box or ssh-tunnel) or to the `wg0` interface IP only.
- **Testnet-ONLY keys (throwaway, no real value).** The deployer is a throwaway
  key funded only with testnet ETH — the Base-Sepolia settlement used deployer
  `0x8b251ADF19a78C6f9e9217E07CD3468C40F00343` (a throwaway; `chain/DEPLOYMENTS.md`).
  The key lives in the operator's secured env (`/etc/dregg/testnet-deploy.env`,
  mode 0600), **never in the repo** and **never on the public gateway**. No mainnet
  key is ever loaded on the demo path.
- **The dev-ceremony VK is not-a-live-secret, but named.** The on-chain settlement
  verifier (`DreggGroth16Verifier25`) bakes in a **dev single-party Groth16
  ceremony** VK (toxic-waste-known — not production MPC; `chain/DEPLOYMENTS.md`).
  This is fine for a testnet demo (it only gates a fixture proof, no value) but it
  is **explicitly labelled** as a dev ceremony wherever it appears — it must NOT be
  presented as production-secure. A production VK is a real MPC-ceremony go-live
  item (below).
- **Honest-grade labels front-and-center.** Both demos already grade every claim
  inline (PROVED / ATTESTED / BUILT / REPLAYABLE) with `file:line` Lean citations.
  The demo landing must carry a persistent banner: **"testnet · unaudited ·
  no real value · proofs are dev-ceremony fixtures."** What's proven vs open is
  the launchpad README's "Honest scope" and the DrEX graded ledger — do not strip
  these when hosting.
- **Rate-limiting + basic abuse protection at the gateway.** The gateway (ember's)
  rate-limits per-IP, caps request body size, and fronts the demo. The demo servers
  already cap POST bodies at 1 MiB (`serve.mjs`, `server.mjs` both `1 << 20`). The
  DrEX `POST /clear` shells to a matcher binary — the gateway must rate-limit it
  hard (it is the one compute-amplifying endpoint) and it accepts **only** the
  revealed-orders JSON shape.
- **No real custody.** The launchpad indexer is **read-only over chain** (it only
  `queryFilter`/`call`s a testnet contract; it holds no keys). DrEX proving runs
  client-side (wasm) + the matcher; no user funds are custodied. There is nothing
  on the box whose loss costs real value.

**What a testnet demo does / does not risk.** DOES: testnet gas, demo uptime,
reputation-if-mislabelled. DOES NOT: real funds, mainnet keys, user custody,
production-VK secrets. The single job of these controls is to keep it inside that
line — the firewall + localhost-bind + throwaway-key + honest-labels quartet.

---

## Deploy procedures

### A. Testnet contract deploys (ember-gated broadcast; dry-run is keyless)

The contracts are **already dry-run-verified plumbing**. Base-Sepolia settlement is
**live** (`chain/DEPLOYMENTS.md`); the launchpad deploy script is **ready** for
Base-Sepolia or Robinhood Chain. The **broadcast is ember's outward step** (it needs
a funded key); the dry-run needs no key.

RPC aliases live in `chain/foundry.toml` (`base_sepolia`, `robinhood_testnet`).

**Settlement (already live on Base-Sepolia — redeploy pattern):**
```bash
# keyless dry-run first (simulates deploy + self-settles the fixture proof):
forge script chain/script/DeploySettlement.s.sol:DeploySettlement

# ember broadcast (throwaway funded key + RPC in env):
export DEPLOYER_PRIVATE_KEY=0x<funded base-sepolia THROWAWAY key>
export BASE_SEPOLIA_RPC_URL=https://sepolia.base.org
export ETHERSCAN_API_KEY=<basescan key>          # for --verify
forge script chain/script/DeploySettlement.s.sol:DeploySettlement \
    --rpc-url base_sepolia --broadcast --verify -vvv
```
Records: the three addresses (verifier / adapter / `DreggSettlement`) into
`chain/DEPLOYMENTS.md`; read back `provenHeight()` / `provenRoot()` to confirm the
fixture proof settled (the live one: height 2, root `0x6ca8f74f…`).

**Launchpad (ready — Base-Sepolia or Robinhood Chain):**
```bash
# keyless dry-run (simulates deploy AND a full fair-launch lifecycle, asserts the
# uniform clearing price — no tx sent):
forge script chain/script/DeployLaunchpad.s.sol:DeployLaunchpad

# ember broadcast:
export DEPLOYER_PRIVATE_KEY=0x<funded THROWAWAY key>
export ROBINHOOD_TESTNET_RPC_URL=https://rpc.testnet.chain.robinhood.com
forge script chain/script/DeployLaunchpad.s.sol:DeployLaunchpad \
    --rpc-url robinhood_testnet --broadcast -vvv
#   Base-Sepolia instead:  --rpc-url base_sepolia --broadcast --verify
```
Records: the `DreggLaunchpad` address (the one live contract) → it becomes
`LAUNCHPAD_ADDRESS` for the demo host below. Verify with a Blockscout/Basescan
lookup.

> `forge` is **not installed on hbox** (dry-run finding). Run contract deploys from
> the Mac or a build host (persvati) that has Foundry — the deploy is a one-shot
> that only needs the RPC + key, not the demo host. hbox only needs the resulting
> **address**, not Foundry.

### B. Demo hosting on hbox (build + run the web servers)

Staging dir on hbox: `~/dregg-testnet-demo/` (the dry-run used this).

**Sync the demo tree to hbox.** ⚠ **Finding: the DrEX wasm is gitignored** — a
git-filtered rsync (`scripts/hbuild`/`pbuild`) will **NOT** carry
`extension/dregg_wasm_bg.wasm` (50 MB build artifact). Sync it explicitly:
```bash
# from the Mac repo root:
rsync -az --delete drex-web/ hbox:dregg-testnet-demo/drex-web/
rsync -az --delete \
  --include='dregg_wasm.js' --include='dregg_wasm_bg.wasm' \
  --include='confirm-intent-script.js' --include='disclosure-picker.js' \
  --include='provision.js' --include='origin-permission-script.js' \
  --include='manifest*.json' --include='package*.json' \
  --include='*/' --exclude='*' \
  extension/ hbox:dregg-testnet-demo/extension/
rsync -az --delete --exclude='node_modules/' \
  launchpad-web/ hbox:dregg-testnet-demo/launchpad-web/
```

**drex-web** (zero npm deps — pure node builtins):
```bash
ssh hbox
cd ~/dregg-testnet-demo/drex-web
# bind to localhost (gateway/tunnel only); NEVER 0.0.0.0:
PORT=8781 node serve.mjs        # serves /  + /wasm/  + POST /clear
```
- `serve.mjs` mounts the extension wasm from `../extension/` at `/wasm/` — the
  page loads the SAME wallet wasm the extension ships (real in-browser proving).
- `POST /clear` shells to the `drex_clear` matcher. It prefers a local
  `target/{release,debug}/drex_clear`; absent that it `ssh`es to
  `persvati:dregg-build/drex-matcher` (the prebuilt binary). **For hosting, build
  the matcher once on the box** (`scripts/hbuild drex-matcher 'cargo build -p
  dregg-intent --bin drex_clear'` then place it at `target/debug/drex_clear`), OR
  keep the persvati hop — but that couples the demo to persvati SSH (an ops
  dependency to close before go-live; see checklist).

**launchpad-web** (needs `ethers`; install once on the box):
```bash
ssh hbox
cd ~/dregg-testnet-demo/launchpad-web
npm install --no-audit --no-fund          # installs ethers (9 pkgs)
# point at the deployed launchpad + testnet RPC:
LAUNCHPAD_RPC=https://sepolia.base.org \
LAUNCHPAD_ADDRESS=0x<deployed DreggLaunchpad> \
PORT=8785 node server.mjs
```
- Without `LAUNCHPAD_ADDRESS` the server still serves the static frontend and
  `/api/config`; the `/api/*` data routes honestly return `503 indexer not ready`
  (dry-run confirmed) until a deploy is wired.
- The indexer backfills from genesis then polls new blocks — it is **read-only**
  over the testnet RPC (no keys).

**Process management — systemd (matches the existing `docs/ops` native pattern:
`systemd` units, git-ffwd + rebuild-on-box + restart).** Two units, bound to
localhost:
```ini
# /etc/systemd/system/dregg-drex-demo.service
[Unit]
Description=dregg DrEX testnet demo
After=network-online.target
[Service]
WorkingDirectory=/home/hbox/dregg-testnet-demo/drex-web
Environment=PORT=8781
ExecStart=/usr/bin/node serve.mjs
Restart=on-failure
User=hbox
[Install]
WantedBy=multi-user.target
```
```ini
# /etc/systemd/system/dregg-launchpad-demo.service
[Unit]
Description=dregg launchpad testnet demo
After=network-online.target
[Service]
WorkingDirectory=/home/hbox/dregg-testnet-demo/launchpad-web
EnvironmentFile=/etc/dregg/launchpad-demo.env   # LAUNCHPAD_RPC, LAUNCHPAD_ADDRESS, PORT
ExecStart=/usr/bin/node server.mjs
Restart=on-failure
User=hbox
[Install]
WantedBy=multi-user.target
```
```bash
sudo systemctl daemon-reload
sudo systemctl enable --now dregg-drex-demo dregg-launchpad-demo
```
(For a quick manual demo, `tmux` + the `node …` lines above is fine; `systemd` is
the durable form.) **Localhost bind:** the servers `listen(PORT)` on `0.0.0.0` by
default — either run them where the gateway/tunnel is the only reachable path, or
apply a one-line `listen(PORT, '127.0.0.1', …)` bind (the dry-run did exactly this
on the staged copies) and rely on the firewall as defence-in-depth.

---

## Monitoring + rollback

**Health checks** (the gateway/monitor polls these over the private channel):
```bash
curl -fsS http://127.0.0.1:8781/                    # DrEX page → 200
curl -fsS http://127.0.0.1:8785/api/config          # launchpad config → 200 JSON
curl -fsS http://127.0.0.1:8785/api/launches        # 200 once a launchpad is wired
```
A `200` on `/` + `/api/config` is "up"; `/api/launches` returning `503` means the
indexer has no `LAUNCHPAD_ADDRESS` (config gap, not a crash). Feed these into the
existing Prometheus/Grafana stack (`deploy/observability/`, `docs/ops/MONITORING.md`)
as blackbox probes.

**Logs:**
```bash
journalctl -u dregg-drex-demo -f
journalctl -u dregg-launchpad-demo -f          # indexer backfill/poll + errors
```

**Rollback a bad demo deploy:**
```bash
# re-sync the previous-good tree (rsync is idempotent; keep a tagged snapshot dir):
rsync -az --delete drex-web/ hbox:dregg-testnet-demo/drex-web/     # from good rev
sudo systemctl restart dregg-drex-demo dregg-launchpad-demo
# or hard revert: stop the unit, re-point the gateway to a maintenance page (ember)
```

**Take it down (kill the public demo instantly):**
```bash
sudo systemctl stop dregg-drex-demo dregg-launchpad-demo
# and/or ember disables the gateway reverse-proxy route → the public surface is gone
```
Because hbox is only reachable through the gateway, **stopping the gateway route
takes the demo fully offline** even if the hbox units keep running.

---

## Go-live checklist

The demo goes live **only when every box is true** — ember flips it, not this
runbook.

**Core-work gates (the "tons of core work remains first"):**
- [ ] The demos' backing flows are at the maturity ember wants to show publicly
      (DrEX matcher + launchpad lifecycle stable on the target testnet).
- [ ] `IClearingAttestor` decision for the launchpad (rung-1 REPLAYABLE today vs
      the rung-2 Groth16 clearing weld — named-not-built; `launchpad-web/README.md`).
- [ ] The DrEX matcher hop is de-coupled from persvati SSH (a prebuilt
      `drex_clear` on hbox, or an accepted persvati dependency) — no demo endpoint
      depends on an interactive SSH to a dev box.

**Security review (must sign off):**
- [ ] hbox firewall enabled, default-deny inbound, only the gateway private channel
      + ssh admit — verified with `ufw status` (⚠ currently INACTIVE).
- [ ] Demo ports bound localhost / wg-iface, never `0.0.0.0` — verified with `ss -tlnp`.
- [ ] The private channel (WireGuard recommended) stood up and authenticated;
      hbox has **no** inbound demo port open to the public internet.
- [ ] Throwaway testnet deployer key only; **no mainnet key** anywhere on the demo
      path; deploy key in `/etc/dregg/*.env` mode 0600, not in the repo.
- [ ] Gateway rate-limit + body-size caps live, with the DrEX `POST /clear`
      compute endpoint rate-limited hardest.

**Honest-grade audit (must pass):**
- [ ] The "testnet · unaudited · no real value · dev-ceremony proofs" banner is
      present and unremovable in the hosted build.
- [ ] The PROVED/ATTESTED/BUILT/REPLAYABLE grade labels + Lean `file:line`
      citations are intact (not stripped for polish).
- [ ] The dev-ceremony VK is labelled as such wherever the settlement proof shows;
      it is **not** presented as production-secure.

**ember's audit bar + decision (ember-only):**
- [ ] ember's security-review sign-off.
- [ ] ember's audit-bar clearance (the honest-grade + stranger-usable bar).
- [ ] The go-live decision itself — ember flips the gateway route public.

---

## What needs ember (not doable from the infra host)

These are **out of scope** for this runbook by design — they are ember's to wire:

- **The AWS gateway config** — the reverse-proxy routes (`demo.dregg.net` → hbox
  `:8781`/`:8785`), TLS/DNS (LetsEncrypt + the `dregg.net` records), and the
  gateway rate-limit rules. This runbook does not touch it.
- **The AWS ↔ hbox private channel** — standing up the WireGuard tunnel (or ssh
  reverse-tunnel) between gateway and hbox, and keying it.
- **The testnet contract broadcasts** — any `--broadcast` with a funded (throwaway)
  key is ember's outward step; the dry-runs here are keyless.
- **The security-review sign-off**, the **honest-grade audit**, ember's **audit-bar
  clearance**, and the **go-live decision** — the human gates above the plumbing.

---

## Dry-run record (2026-07-13, on hbox — no public exposure)

A tractable dry-run proved **hbox can host both demos**, bound to `127.0.0.1` only:

- **drex-web** (`serve.mjs`, `PORT=18781`, staged `~/dregg-testnet-demo/`):
  `GET /` → **HTTP 200**, 10139 bytes, `<title>DrEX · Dragon's EXchange</title>`;
  `GET /wasm/dregg_wasm.js` → 200, 273621 bytes, `text/javascript`;
  `GET /wasm/dregg_wasm_bg.wasm` → 200, **50256008 bytes**, `application/wasm` (the
  real extension wasm served whole). `ss` confirmed `LISTEN 127.0.0.1:18781` — not
  `0.0.0.0`.
- **launchpad-web** (`server.mjs`, `PORT=18785`, `npm install` → 9 pkgs):
  `GET /` → 200, `<title>dregg launchpad · fair launches</title>`;
  `GET /api/config` → 200 (rpc/address/abi JSON);
  `GET /api/launches` → **503 `indexer not ready`** (honest — no `LAUNCHPAD_ADDRESS`
  wired); `GET /vendor/ethers.js` → 200, 526551 bytes. `LISTEN 127.0.0.1:18785`.
- **hbox → testnet RPC egress:** `eth_chainId` to `https://sepolia.base.org` →
  `0x14a34` (= 84532, Base-Sepolia). The indexer's connection leg reaches the
  testnet from the infra host.

**Findings surfaced by the dry-run** (each folded into the sections above):
1. hbox `ufw` is **INACTIVE** and already listens on `0.0.0.0` for unrelated
   services — the firewall is a hard pre-go-live gate.
2. The DrEX wasm (`extension/dregg_wasm_bg.wasm`, 50 MB) is **gitignored** — a
   git-filtered rsync won't carry it; sync it explicitly.
3. **`forge` is not on hbox** — run contract deploys from the Mac/persvati; hbox
   only needs the resulting address.
4. The DrEX `POST /clear` matcher hop defaults to an **SSH to persvati** — couple
   or de-couple it before go-live (a demo endpoint shouldn't depend on interactive
   SSH to a dev box).

Both demo processes were stopped after the dry-run; nothing was left listening and
nothing was exposed publicly.
