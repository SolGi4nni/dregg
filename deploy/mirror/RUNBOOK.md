# deploy/mirror — putting `dregg.gg` on the internet

The mirror resolver (`dregg-mirror`) is the no-extension click path for `dregg://`
objects: someone posts a reference on X, a reader with nothing installed clicks the
`https://dregg.gg/...` form, and this service renders the object under an honest
tier-`server` label. DREGG-QUIET-UPGRADE.md §9 item 4 named this seam; the crate closes
it. Nothing in this directory is installed yet — this is the plan, and each step says how
to check it rather than assuming it.

## The shape, and why

```
  dregg.gg  A -> 34.224.208.52          (the edge's EIP)
       │  :443 TLS (Let's Encrypt HTTP-01, minted by Caddy on the edge)
  ┌────▼──── AWS EDGE (public, i-03365e2bcf4ea08b2) ────────┐
  │  caddy          :80 :443     ← NEW, must be added        │
  │      │ reverse_proxy 127.0.0.1:8791                      │
  │  dregg-mirror   127.0.0.1:8791  ← NEW                    │
  │  dregg-node     0.0.0.0:8420  (already there)            │
  └──────────────────────────────────────────────────────────┘
```

**On the edge, not hbox.** hbox already serves the games publicly, so it looks like the
obvious host — it is not, for two independent reasons:

1. hbox's public path is `tailscale funnel`, which can only publish a `*.ts.net` name. It
   cannot serve `dregg.gg` at all.
2. The edge cannot reverse-proxy hbox either: they sit on two disconnected tailnets
   (`deploy/README.md`'s load-bearing fact — the edge is `100.64.0.x`, hbox is
   `skunk-emperor`, and persvati is the only box on both). Any "edge Caddy proxies hbox"
   plan is false at the network layer, not merely unbuilt.

So the mirror runs on the edge, which is the only box with a stable public IP, and Caddy
on the edge is the one genuinely new public component.

**A plain site block, not the on-demand-TLS gateway.**
`deploy/gateway-ask/Caddyfile.on-demand-tls` is right for *hosted customer* domains: one
wildcard block, certificates minted per inbound SNI, gated by an `ask` against the
verified-domain registry. `dregg.gg` is a first-party apex we own — one name, known at
config time — so on-demand issuance would add an unbounded-issuance surface and buy
nothing. If that gateway is what ends up on the edge, fold the mirror in as one more
`handle` rather than running two Caddies.

## Prerequisites (ember-gated, one command each to verify)

| # | What | Check |
|---|---|---|
| P1 | `dregg.gg` A → `34.224.208.52`, and `www.dregg.gg` the same | `dig +short dregg.gg` |
| P2 | The EC2 security group admits `:80` and `:443` from `0.0.0.0/0`. The edge today publishes `:8420` and `:9420/udp`; 80/443 are **not known open**. HTTP-01 needs `:80` reachable or ACME never completes. | `aws ec2 describe-security-groups` for `i-03365e2bcf4ea08b2` |
| P3 | An `ACME_EMAIL` for the Let's Encrypt account | — |

No DNS API token and no wildcard: the mirror needs exactly `dregg.gg` and `www.dregg.gg`,
which HTTP-01 covers by itself. A wildcard would force DNS-01 and put a registrar
credential on a public box for no gain — do not.

## Ports

| Port | Who | Bind |
|---|---|---|
| 80, 443 | caddy (new) | `0.0.0.0` |
| **8791** | **dregg-mirror (new)** | **`127.0.0.1`** |
| 8420, 9420/udp | dregg-node | `0.0.0.0` |
| 8790 | dregg-web-games (hbox) | loopback |

8791 is free (8420/8781/8787/8790 are taken — `deploy/README.md`,
`docs/ops/OPS-RUNBOOK.md`). The mirror binds loopback **by default in the binary itself**,
not merely in the unit: it terminates no TLS and does no rate limiting, so "exposed
straight to the internet" must not be the path of least resistance.

## Install

The edge runs a **docker compose stack, not systemd** (`deploy/README.md`), so on the edge
this is two services added to `/opt/dreggnet/docker-compose.yml` — a `dregg-mirror`
binding `127.0.0.1:8791` and a `caddy` publishing `:80`/`:443` with
`Caddyfile.mirror` mounted and a named volume for `/data` (Caddy's certificate store —
**without a persistent volume every container restart re-requests certificates and will
hit Let's Encrypt's rate limit**).

`dregg-mirror.service` in this directory is the systemd variant, for a box that does use
units (persvati, hbox). Same binary, same env.

```
cargo build --release -p dregg-mirror
DREGG_MIRROR_BIND=127.0.0.1:8791 ./target/release/dregg-mirror --seed-demo
```

`--seed-demo` serves one in-memory object of every kind and prints their `dregg://`
references, so the whole path is clickable before a single real object is published.

## Configuration that is correctness, not cosmetics

* **`DREGG_MIRROR_ORIGIN`** is printed on every page as the party the reader is trusting
  ("dregg.gg checked this object. You did not."). If it is wrong, every page misnames who
  is being trusted.
* **`DREGG_MIRROR_COMMITTEE`** is the trusted Ed25519 committee for the anchored quorum
  gate. Empty today, because there is no committee to anchor against — so the gate runs
  **structurally** (signatures counted, not cryptographically anchored) and every page
  says exactly that. Set it the moment a real committee exists.
* **`DREGG_MIRROR_ROOT`** holds `<kind>/<64-hex>.json` object bodies and optional
  `<64-hex>.att.json` attestations. The filename is not trusted: the mirror re-hashes the
  bytes and refuses if they do not hash to the address that was asked for.

## Verify it is really up

```
curl -s https://dregg.gg/healthz                       # -> ok
curl -s https://dregg.gg/poll/<8-hex-prefix> | grep 'trust the origin'
curl -si https://dregg.gg/poll/$(python3 -c 'print("0"*64)') | head -1   # -> HTTP/2 404
```

The third one is the important one. A mirror that renders something optimistic for a dead
reference has lost the property the whole surface exists to preserve.
