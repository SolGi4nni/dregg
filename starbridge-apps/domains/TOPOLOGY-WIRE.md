# Wiring `starbridge-domains` to the gateway ↔ Tailscale ↔ hbox topology

*Design, not deploy.* This describes how the verified-domain registry replaces the
current "one hardcoded Caddy block per surface" pattern with "on-demand-TLS + a
verified-domain registry," so any BYO custom domain a tenant has *proven* they control
is served under one gateway discipline. No Caddyfile here is edited; flipping it live is
a later, operator-gated step.

## The two surfaces the gateway consults

`starbridge-domains` exposes exactly the reads a gateway needs, on
[`DomainRegistry`](src/registry.rs):

- `is_verified(host) -> bool` — the **on-demand-TLS `ask` gate**. A certificate is
  minted for `host` only when a binding for it exists *and* is `Verified` (DNS
  proof-of-control passed). An unbound or still-`Pending` host answers `false`, so no
  cert is issued for a domain nobody has proven.
- `site_for_host(host) -> Option<String>` — the **route**. For a verified custom `Host`
  it returns the bound site `<name>` (whose `<name>.<apex>` cell serves the bytes);
  `None` for anything unverified, so the request falls through to the wildcard path.

Both read only `Verified` bindings; the write path (`bind`, then `verify` against a
`DnsResolver`) is cap-gated and lives off the request path.

## The apex is configuration

The hosting apex (the CNAME challenge target `<site>.<apex>`, and the wildcard host that
is *not* a bindable custom domain) is no longer a compile-time constant. A
`DomainRegistry` resolves it, in order:

1. `DomainRegistry::with_apex("dregg.fg-goose.online")` — explicit, wins.
2. the `DREGG_HOSTING_APEX` environment variable — the operator's deployment apex.
3. `dns::DEFAULT_HOSTING_APEX` — a generic placeholder fallback.

So the same binary serves `dregg.fg-goose.online`, `dregg.net`, or an arbitrary apex
with no rebuild. `registry.apex()` reports the resolved value.

## The Caddy `ask` idiom (the on-demand-TLS wire)

The gateway host runs a small HTTP endpoint backed by the registry — the `ask` Caddy
consults before minting a cert on demand:

```
GET /internal/site-exists?domain=<host>   ->  200 if registry.is_verified(host) else 404
```

A Caddy block that terminates TLS for *any* proven domain (instead of a hand-listed
`DREGG_SITE_DOMAINS`) then reads:

```caddyfile
{
    on_demand_tls {
        ask http://127.0.0.1:<ask-port>/internal/site-exists
    }
}

# One block serves every verified custom domain — no per-surface edit.
https:// {
    tls {
        on_demand
    }
    reverse_proxy <resolver>   # resolves Host -> site via registry.site_for_host
}
```

Caddy calls the `ask` before every on-demand certificate issuance; a `404` refuses the
cert, so an attacker cannot induce issuance for a domain they have not proven, and the
issuance surface is not a DoS amplifier.

## Mapping onto the existing per-surface blocks

Today each surface is a hand-written block reverse-proxying **over Tailscale** to a
**fixed hbox port**, each with its own DNS record and TLS entry:

| File | Surface | Upstream |
|---|---|---|
| `deploy/aws/caddy/Caddyfile` | node API + built site | `localhost:8420`, static dirs |
| `deploy/games/caddy/Caddyfile.games` | games | hbox `:8790` over Tailscale |
| `deploy/launchpad/caddy/Caddyfile.launchpad` | launchpad | hbox `:8785` over Tailscale |

The topology is unchanged — the gateway still terminates TLS at the edge and reverse-
proxies over the Tailscale mesh to hbox ports. What changes is **enrolment**: a new
offering or a tenant's BYO domain becomes a `bind` + `verify` turn against the registry
(cap-gated, DNS-proven), not a new Caddyfile block + DNS record + `DREGG_SITE_DOMAINS`
entry. The fixed-port upstreams stay as the routing target; the registry decides *which
hosts are admitted* and *which site each maps to*.

- **Manual per-surface block → the single on-demand block** gated by
  `is_verified`.
- **Manual DNS subdomain records → TXT/CNAME proof-of-control** (`bind` issues the
  challenge; `verify` checks it through the injected `DnsResolver` — a real client in
  prod, `MockDns` in tests).
- **Per-domain hand-listed Let's Encrypt → certs minted on-demand** only for proven
  domains, no list to maintain.

## What is real vs. what a deploy step adds

Real and tested here (`cargo test -p starbridge-domains`): the cap-gated `bind`, the
DNS-driven `verify` flip (once, `Monotonic`), the `is_verified` / `site_for_host`
verified reads, the owner-gated no-takeover rebind, and the configurable apex threading
into the CNAME challenge and the wildcard refusal.

A later deploy step adds: the thin `/internal/site-exists` HTTP handler over a live
`DomainRegistry`, a `DnsResolver` wired to a real DNS client (the `live-dns` feature
ships one), the on-demand Caddy block itself, and the gateway joining the tailnet
(already the operator-gated step 0 in the RUNBOOKs). None of that is performed here.
