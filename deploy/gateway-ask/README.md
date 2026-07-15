# gateway-ask — one on-demand-TLS + capability-auth sidecar for the gateway

A public gateway (Caddy) fronts every hosted surface. This kit replaces the
hand-written **per-surface** site blocks — each with a hardcoded domain and
upstream — with **two reusable idioms**, each backed by a real verified read, and
the deploy tooling to ship them safely.

## What it is

| Piece | File | What it does |
|-------|------|--------------|
| The sidecar crate | `src/lib.rs`, `src/main.rs` | Serves `GET /internal/site-exists` (the on-demand-TLS `ask`) + `GET\|POST /auth?cap=` (the capability forward-auth gate) + `GET /healthz`, over the hardened `http-serve` loop. |
| The Caddy config | `Caddyfile.on-demand-tls` | ONE wildcard block for every verified custom domain + the cap-gated operator idiom. No baked-in domain. |
| The deploy script | `deploy.sh` | Cross-build (zigbuild) → ship → **stage on an alt port** → **atomic swap** → **paired cold-backup rollback**. |
| Environment | `.env.example` | Every apex/domain/upstream as a variable. |

## The on-demand-TLS `ask` (replaces per-surface blocks)

Caddy's `on_demand_tls { ask <sidecar>/internal/site-exists }` asks the sidecar,
per inbound SNI, *before* it mints a Let's Encrypt certificate: "is this a host
you are authorized to serve?" The sidecar answers from the verified custom-domain
registry — [`starbridge_domains::DomainRegistry::is_verified`] — returning `200`
**iff a proven binding exists** for that host, else `404`. So:

- one wildcard Caddy block (`*.{$HOSTING_APEX}`) serves *every* verified site;
- a new site going live is a **registry write** (a `verify` turn, or a launch —
  see below), not a Caddyfile patch + reload;
- issuance is **fail-closed**: an unknown / merely-pending / forged SNI gets a
  `4xx` and no certificate (no unbounded ACME issuance from a wildcard).

This is the direct improvement over `deploy/aws/caddy/Caddyfile`,
`deploy/games/caddy/Caddyfile.games`, and `deploy/launchpad/caddy/Caddyfile.launchpad`,
which each hardcode one domain + upstream. They can be collapsed into the one
block here as sites move into the registry.

## The capability forward-auth gate

Caddy's `forward_auth <sidecar>/auth?cap=<name>` gates an operator surface. The
sidecar verifies the operator's printable capability token **offline** against the
issuer public key ([`dregg_auth::verify_offline`]) for the requested capability,
and answers `200` (admit) / `401` (sign in) / `403` (denied) / `503` (fail-closed,
no issuer configured). No password anywhere — the gate is a proof-carrying token.

**No-forge discipline.** The subject is derived from the VERIFIED token, never
from a request header. Caddy strips any client-supplied `X-Dregg-*` before the
subrequest (`strip_forged_identity` in the Caddyfile), and the gated upstreams are
reachable only from Caddy on the private network.

### Identity pass-through (labeled follow-up)

The gate ENFORCES admit/deny by HTTP **status**, which is complete for
`forward_auth`. Passing the verified subject *upstream* via Caddy's
`copy_headers X-Dregg-Subject` needs the sidecar to emit that as a real response
header; the base `http-serve` `WebResponse` carries no header map, so today the
sidecar returns the subject in the structured [`dregg_gateway_ask::CapAuth`] (used
by tests / a header-capable front) but does not yet set it as an HTTP header on
the wire. Until a header-capable response type lands, the upstream simply does not
receive the subject header — which is safe: the gate still fully admits/denies.
This is a tracked resolution step, not a gap in enforcement.

## Launchpad composition — a launch comes up with a landing page

[`dregg_gateway_ask::compose_launch_landing`] wires microsite hosting to a token
launch, so a launch is not just a contract but a **live page**:

1. the token metadata document + image are pinned on IPFS, **content-addressed** —
   the CID *is* the blake3 commitment of the bytes ([`dregg_ipfs`]), no second
   identity, so a visitor re-witnesses exactly what the launch committed;
2. a **verified** microsite binding `<slug>.<apex>` → site `<slug>` is adopted
   into the registry, so the landing host immediately answers the on-demand-TLS
   `ask` (gets a cert) and routes.

One call, and the launch has a content-addressed landing page. This is the
composition point the launchpad (`deploy/launchpad`) calls when a launch is
created — the microsite and the content are provisioned together, no separate
step. (The launcher's *own* custom domain is the separate DNS-challenge `verify`
flow; the platform `<slug>.<apex>` label is verified by construction.)

## The deploy discipline (`deploy.sh`)

The box compiles nothing (the sidecar pulls the verified-domain closure; a small
box OOMs). Two patterns are fused:

- **cross-build + ship** — `cargo zigbuild` the linux/amd64 binary on the dev
  box, rsync just the binary + config to the box (`build`, `ship`);
- **stage → atomic swap → paired rollback** — before the live binary is touched,
  the candidate is booted on an **alt loopback port** and health-probed **twice**
  (an idempotent restart that flaps is rejected); only a passing candidate is
  promoted, and promotion is a **single atomic rename** over the live binary
  (`stage`, `swap`). A **cold backup** of the previous binary is kept and
  checksum-verified, so `rollback` is the same atomic rename in reverse.
  `swap --auto-rollback` reverts itself on a failed post-swap gate.

```
deploy.sh all      # build + ship + stage + swap  (staging gates the swap)
deploy.sh rollback # atomic-swap back to the newest cold backup
deploy.sh releases # list the cold backups
```

## Build + test

```
cd deploy/gateway-ask
cargo build          # standalone workspace (mirrors the root ark-serialize patch)
cargo test           # 10 unit + 1 real-socket integration test
```

## Workspace note

The crate carries its own `[workspace]` + a mirror of the root
`[patch.crates-io]` ark-serialize redirect so it builds **disjoint** from the
shared root manifest (swarm-safe). The main loop may instead promote it into the
root `members` (removing the local `[workspace]` + `[patch]`) once the tree is
quiet — see the header comment in `Cargo.toml`. Flagged `touched_root_manifest`.

## Configuration — no hardcoded apex/domain

Every domain/apex/upstream is an environment variable (`DREGG_HOSTING_APEX`,
`HOSTING_APEX`, `GATEWAY_ASK_UPSTREAM`, `SITE_UPSTREAM`, `ACME_EMAIL`, …). See
`.env.example`. The registry reads its apex from `DREGG_HOSTING_APEX`
([`starbridge_domains`] default otherwise) — configuration, never a compile-time
constant.
