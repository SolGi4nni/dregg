# deploy/ — what actually runs, where

Verified live 2026-07-15 by direct inspection of the boxes. Everything below is
observed state, not intent. Where something is aspirational it says so.

Read [`PRACTICES.md`](PRACTICES.md) before touching a box — it is short, and each
rule in it was paid for by an incident in the last session.

## The three boxes

| Box | Role | Reachable via | Public surface |
|---|---|---|---|
| **edge** (`dreggnet-staging`) | AWS t3.medium, us-east-1c, `i-03365e2bcf4ea08b2`, EIP `34.224.208.52`. Tailnet exit + docker stack. | EC2 Instance Connect (recipe in [`aws/README.md`](aws/README.md)) | EIP; node `:8420`/`:9420-udp` bound `0.0.0.0`; **and five DNS names — see below** |

### ⚠ The edge's public surface is bigger than this repo says

Corrected 2026-07-26 by probing every name that resolves to `34.224.208.52`.
The row above described the ports and missed the names. All five of these are
that one box:

| name | probe | what it is |
|---|---|---|
| `arcade.dregg.net` | `/` `/health` `/descent/play` `/offerings` `/tg` all **200** | A live play surface (`DreggNet Cloud — play + verify`) including the Telegram mini-app entry. **Undocumented** — `rg arcade` finds no hostname match anywhere in this repo, and it has no unit, no Caddyfile entry, and no compose service. Not a node: `/status` and `/api/cells` 404 while `node/src/api.rs` routes both. |
| `headscale.dreggnet.fg-goose.online` | **200** | Tailnet A's control plane. See `~/dev/dregg-infra/edge/RUNBOOK.md`. |
| `portal.dregg.studio` | **200**, `Last-Modified: 2026-06-28` | The static "live network" portal. Frozen bytes, still served. |
| `hello.dregg.works` | https **000**, http **308** | Broken. Caddy holds no cert for the name. |
| `devnet.dregg.fg-goose.online` | https **000**, http **308** | Same failure. The retired devnet-era name. |

So "restart the container, not the instance" is not the only hazard here — a
takedown of this box takes a working play surface with it. The ordering lives in
`~/dev/dregg-infra/edge/RUNBOOK.md`.
| **hbox** (`hbox-dregg`) | AMD Navi22 GPU, 24c/123G. **Build + prove box AND the live games demo host** (this is a problem — see PRACTICES §1). | `ssh hbox` / tailnet `100.95.240.73` | `https://hbox-dregg.skunk-emperor.ts.net` via `tailscale funnel` |
| **persvati** | CPU build/test box. On **both** tailnets. | `ssh persvati` | none |

## ⚠ There are TWO tailnets. They are not connected.

This is the single most load-bearing fact in this directory, and the stale docs
got it wrong in a way that made a whole deploy plan impossible:

```
  tailnet A — 100.64.0.x  ("the edge tailnet")
    edge          100.64.0.1     ← the exit node; tailscaled + firewall + ip_forward=1
    persvati      100.64.0.2
    lassie-dregg  100.64.0.4

  tailnet B — skunk-emperor.ts.net
    hbox-dregg    100.95.240.73  ← the games demo + funnel
    persvati      100.74.40.124
    nextop                        (also funnels)
```

**persvati is the only box on both.** The edge and hbox **cannot** reach each
other over tailscale. Any plan of the form "the edge's Caddy reverse-proxies
hbox over the tailnet" is not merely unimplemented — it is *false at the network
layer*. `deploy/games/RUNBOOK.md` is exactly that plan; it is marked aspirational.

## What runs where

### edge — a docker compose stack, NOT systemd units

`/opt/dreggnet/docker-compose.yml` + `/opt/dreggnet/docker-compose.observability.yml`.

| Container | Image | Binds |
|---|---|---|
| `dreggnet-dregg-node-1` | `dregg-node:n5` | `0.0.0.0:8420`, `9420/udp` |
| `dreggnet-dreggnet-discord-bot-1` | `dregg-discord-bot:staging` | — |
| grafana | | `127.0.0.1:3000` |
| prometheus | | `127.0.0.1:9090` |
| alertmanager | | `127.0.0.1:9093` |
| node-exporter, blackbox, alert-sink | | loopback |

Also on the box as **host** services: `tailscaled`, `dregg-harden-firewall.service`
(enabled), `ip_forward=1`. These make the edge the tailnet's public exit.

**Autostart = the docker restart policy.** Not systemd. There is no
`dregg-gateway.service` — `systemctl status dregg-gateway` on the box returns
`not-found`. Images are roughly two weeks old.

**⚠ DO NOT `aws ec2 stop-instances` THIS BOX.** It is the tailnet's public exit;
stopping it cuts the exit for every peer. We did this once this session. The EIP
survives stop/start (it is *elastic*), which is the only reason it recovered
without a DNS change — but the services blip and the exit drops meanwhile.

### hbox — the live games demo

- `dregg-web-games-funnel.service` — a systemd **user** unit (+ `loginctl enable-linger`),
  binds `127.0.0.1:8790`, `DREGG_NODE_URL=http://127.0.0.1:8420`.
- `tailscale funnel` publishes it at **https://hbox-dregg.skunk-emperor.ts.net**.
  No gateway, no Caddy, no DNS record. Funnel *is* the public edge (TLS + hostname).
- **Verified reboot-proof**: both the user unit and the funnel config came back
  cleanly after this session's hard reboot.

hbox is *also* the build/prove/GPU box. See PRACTICES §1 — this co-tenancy killed
the box once already.

### persvati — build/test only

No services. `ssh persvati`, `git push persvati main`, `scripts/pbuild`.

## What survives a reboot

Verified against this session's unplanned hbox reboot and the edge stop/start:

| Survives | Does not |
|---|---|
| systemd **user** units **with `loginctl enable-linger`** | anything hand-run in a shell / `nohup` |
| `tailscale funnel` config | ephemeral `--data-dir` state (see below) |
| docker containers with a `restart:` policy | |
| the edge's EIP (elastic — survives stop/start) | a non-elastic public IP would have dangled DNS |

**What we permanently lost:** a hand-run `dregg-node` on hbox whose `--data-dir`
was a temp dir. The devnet ledger — the operator cell and every anchored Descent
run — is **gone**, unrecoverable. That node was the `:8420` that
`dregg-web-games-funnel.service` still points at. See TODO-1.

## Where to build

**Never on the edge.** It is a 2-vCPU t3.medium. Build on **persvati** (CPU) or
**hbox** (GPU/prove), and ship **images** to the edge — not source. Anything in
this tree that tells you to `cargo build` or run `rustup` on the AWS box is
superseded fiction (see `aws/SUPERSEDED/`).

## Named gaps (real, not done)

- **TODO-1 — the hbox devnet node has no unit and no persistent data dir.** The
  one that existed was hand-run and its ledger is gone. Fix: a
  `dregg-node` systemd **user** unit on hbox (same shape as
  `dregg-web-games-funnel.service`: `%h` paths, linger, `WantedBy=default.target`)
  with `--data-dir %h/.local/state/dregg-node` (a real, backed-up path — *not*
  `mktemp -d`), listed in `ReadWritePaths=`. Until then `DREGG_NODE_URL=:8420` in
  the funnel unit points at nothing and submitted runs cannot anchor.
- **TODO-2 — the discord bot lives on the edge; it should not.** It runs as
  `dreggnet-dreggnet-discord-bot-1` on a 2-vCPU box that exists to be a network
  exit. Fix: move it to persvati (it is a thin Discord+drand egress client, no
  GPU, no node dependency). ⚠ One token = one bot: **stop the edge container
  before starting it anywhere else**, or every command double-fires.
- **TODO-3 — the demo shares a box with the prover.** Move
  `dregg-web-games-funnel` off hbox (persvati can funnel it — it is on
  skunk-emperor as `100.74.40.124`), **or** resource-cap the prover. See
  PRACTICES §1 for why this is not cosmetic.
- **TODO-4 — the edge's compose stack is not in this repo.** `/opt/dreggnet/docker-compose.yml`
  exists only on the box; nothing reachable from `main` defines it. Unreviewable,
  undiffable, one `rm` from gone. **The closest ancestor is recoverable** —
  `git show 0310c9e31^:dreggnet/deploy/staging/docker-compose.yml` (added `ab6328a3e`,
  deleted `0310c9e31` as "abandoned slop", on branches that never merged to main). It
  matches the deployed `dregg-node`/`dreggnet-discord-bot` services but is a **superset**
  (it also defines postgres/gateway/caddy/headscale, which are *not* running). Fix:
  recover it, **diff against the box**, land the truth in `deploy/edge/`, make the box a
  checkout. Until then the box is authoritative and this directory is only a description.
- **TODO-5 — `devnet.dregg.fg-goose.online/status` returns HTTP 000.** No
  container routes the node publicly. Per TODO-4's ancestor, a `caddy:2` service on
  80/443 was *meant* to — it is simply not running, so the route was never up here.
  Either bring it up or retire the hostname; right now the DNS name is a promise
  nothing keeps, and ~10 files across the tree still advertise it (see below).
- **TODO-6 — cruft on the edge:** `/home/ubuntu/DreggNet/docker-compose.yml` is a
  checkout of the **abandoned** DreggNet repo. It is not what runs. Delete it, or
  someone will eventually `docker compose up` the wrong file.
- **TODO-7 — we cannot rebuild the deployed images.** `dregg-node:n5` is the
  running tag and **nothing in this repo produces it.** The two Dockerfiles are
  real but are *runtime wrappers only* — they `COPY` a pre-built binary and compile
  nothing:
  - `docker/Dockerfile.node` (`dregg-node:staging`) — its header defers the actual
    build to "the pulse builder — DreggNet `deploy/staging/pulse-builder.sh`", **a
    path that does not exist in this repo** (it died with the deleted `dreggnet/` tree).
  - `discord-bot/Dockerfile` (`dregg-discord-bot:staging`).
  - `docker/build-multiarch.sh:37` builds *different* images
    (`ghcr.io/emberian/dregg/dregg-{node,gallery,discharge-gateway}:latest`), not these.

  So the images on the edge are ~2 weeks old **and unreproducible**. Fix: recover or
  rewrite the binary-build step (cross-build on persvati per PRACTICES §3), and land a
  tagged build script. Note the node binary links a host-native Lean archive and
  **cannot be cross-compiled** per `Dockerfile.node` — it must be built on a
  linux/amd64 box (persvati), which is the correct place anyway.

## Stale claims elsewhere in the tree (not fixed here — deploy/ only)

These contradict the verified ground truth above. Listed so the next person can find
them; **none were edited** — this pass owns `deploy/` only.

- `REORIENT.md:36` — asserts the devnet is live at `devnet.dregg.fg-goose.online` on
  "graviton `i-0540e3a`". **Wrong arch and wrong instance**: it is `i-03365e2bcf4ea08b2`,
  a t3.medium x86. (It does get the EIP `34.224.208.52` right — the EIP appears to have
  outlived the instance it was documented on, which is exactly the trap PRACTICES §5 is
  about.) Also `REORIENT.md:170,173,876` still route people to
  `deploy/aws/update.sh` / `federation-keygen.sh` — both now in `aws/SUPERSEDED/`.
- `redteam/MULTINODE-BYZANTINE-FINDINGS.md:67,119,274` — `systemctl restart dregg-gateway`,
  "fronted by Caddy on :443". That unit is `not-found`; there is no Caddy.
- `redteam/devnet_probe.sh:2` — probes `https://devnet.dregg.fg-goose.online`, which
  returns HTTP 000.
- `extension/README.md:139`, `extension/REVIEWER-AUDIT.md:38-39`,
  `extension/STORE-LISTING.md:135`, `extension/REVIEWER-NOTES.md:34`,
  `extension/STORE-READINESS-REVIEW.md:152`, `redteam/THREAT-MODEL-FUZZ.md:50` — all
  still advertise the dead hostname. `HORIZONLOG.md:7123` already flags it dead and
  names more (`site/dregg-works/*`, `site/light-client/index.html`, `site/transclusion/*`).
- Already correct, and contradicting `REORIENT.md`: `README-LLMs.md:148` and
  `extension/src/endpoints.ts:11` both describe the hostname as **retired**.

`docs/ops/OPS-RUNBOOK.md` and `docs/DEPLOY-PLAN.md` — cited throughout `deploy/games/`
as the authority on "the real live topology" — **do not exist in this repo.**

## Map of this directory

| Path | Status |
|---|---|
| `README.md`, `PRACTICES.md` | this map + the rules |
| `aws/` | the **real** edge: access, stack, do-not-stop |
| `aws/SUPERSEDED/` | the systemd/Caddy/Graviton deployment that **does not exist**. Kept for the reasoning inside, quarantined so it stops being read as instructions. |
| `games/` | funnel variant = **live**; gateway variant = **aspirational** (impossible today: wrong tailnet) |
| `observability/` | closest-to-real config in the tree; the box has drifted (it also runs a blackbox exporter this file lacks) |
| `genesis/` | devnet genesis material |
| `hbox/`, `launchpad/`, `gateway-ask/`, `webauth-edge/` | **unverified this session** — assume stale until checked against a box |
