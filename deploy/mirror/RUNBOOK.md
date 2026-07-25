# deploy/mirror — what `dregg-mirror` needs from whatever runs it

The mirror resolver is the no-extension click path for `dregg://` objects: someone posts a
reference on X, a reader with nothing installed clicks the `https://dregg.gg/...` form, and
this service renders the object under an honest tier-`server` label
(DREGG-QUIET-UPGRADE.md §9 item 4).

**The deployment itself lives in [`deploy/edge/`](../edge/RUNBOOK.md), not here.** That
directory is the edge as code — OpenTofu for the boxes, `compose/docker-compose.yml` for the
services, `compose/Caddyfile` for TLS — and it already carries the mirror as the `resolver`
service behind `dregg.gg`. This file is the *crate's* half of that contract: what the binary
needs, what is load-bearing about each setting, and what is still missing. Do not add a
second Caddy site block for `dregg.gg` here; there is one, and it is in `deploy/edge`.

`dregg-mirror.service` in this directory is the systemd variant, for a box that runs units
rather than compose (persvati, hbox). Same binary, same environment.

## The contract

| setting | value | why it is not cosmetics |
|---|---|---|
| `DREGG_MIRROR_BIND` | `0.0.0.0:8080` in a container; `127.0.0.1:8791` under systemd | The binary defaults to **loopback** deliberately: it terminates no TLS and does no rate limiting, so "exposed straight to the internet" must never be the path of least resistance. In compose that default is *wrong* — a sibling Caddy cannot reach the container's loopback — so the compose file sets it explicitly, on the port the Caddyfile proxies. |
| `DREGG_MIRROR_ORIGIN` | `dregg.gg` (a bare host) | Printed on every page as the party the reader is trusting: *"dregg.gg checked this object. You did not."* It is also the authority of every mirror link the page emits. A URL form (`https://dregg.gg/`) is normalized to the host by `page::normalize_origin`, so either spelling works — but the value means *host*. |
| `DREGG_MIRROR_ROOT` | a directory of `<kind>/<64-hex>.json` (+ optional `<64-hex>.att.json`) | The object corpus. Mountable **read-only**: the mirror serves and never writes. The filename is not trusted — the mirror re-hashes the bytes and refuses if they do not hash to the address that was asked for, so a tampered or mis-named file serves as nothing. |
| `DREGG_MIRROR_COMMITTEE` | unset today | The trusted Ed25519 committee for the anchored quorum gate. Empty means the gate runs **structurally** — signatures counted, not cryptographically anchored — and every page says that in those words. Set it the moment a real committee exists; do not leave the honest-but-weaker gate running once it is avoidable. |
| `DREGG_MIRROR_EXTENSION_URL` | where a reader gets the extension | The tier-`extension` upgrade path, linked from every page including the error pages. A dead link here removes the only route off the weakest tier. |

## The gap this deployment has, stated plainly

`deploy/edge/compose` sets `DREGG_NODE_URL`, because the intended shape is that the mirror
fetches attested envelopes from the node — the transport hop `extension/src/netlayer.ts`
injects. **That transport is not built.** The corpus is the mounted directory, and nothing
else. A mirror pointed at an empty directory 404s every reference, which is correct
behaviour and looks identical to a broken deploy — so the binary prints the reason on
startup rather than letting an empty mirror pass for a healthy one.

The seam is the `ObjectStore` trait (`dregg-mirror/src/store.rs`): `get`, `resolve_prefix`,
`list`. A node-backed implementation drops in beside `DirStore` with no change to routing,
verification, or rendering.

## TLS

Plain HTTP-01, which Caddy does by itself: no plugin, no DNS API token, no wildcard. The
mirror needs exactly `dregg.gg` and `www.dregg.gg`; a wildcard would force DNS-01 and put a
registrar credential on a public box for nothing. `deploy/edge/tofu` emits the CAA record
that authorizes Let's Encrypt.

Two things that will bite if they are wrong:

* `:80` must be reachable or HTTP-01 never completes. `:443/udp` too, for HTTP/3.
* Caddy's `/data` **must** be a persistent volume. Without it every container restart
  re-requests certificates and walks straight into Let's Encrypt's rate limit.

Turn HSTS on *after* a first successful certificate, never before — enabling it on a name
whose TLS is not yet working pins browsers to a broken https.

## Verify it is really up

```
curl -s https://dregg.gg/healthz                                        # -> ok
curl -s https://dregg.gg/poll/<8-hex-prefix> | grep 'trust the origin'  # -> the badge
curl -si https://dregg.gg/poll/$(python3 -c 'print("0"*64)') | head -1  # -> 404
```

The third one is the important one. A mirror that renders something optimistic for a dead
reference has lost the property the whole surface exists to preserve.
