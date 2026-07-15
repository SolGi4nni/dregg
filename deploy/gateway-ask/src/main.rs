//! `gateway-ask` — the public gateway's on-demand-TLS `ask` + capability
//! forward-auth sidecar. Binds a loopback / private-network address and serves,
//! under the hardened [`http_serve`] connection bounds:
//!
//! - `GET  /internal/site-exists?domain=<host>` — the on-demand-TLS `ask`:
//!   `200` iff `<host>` is a VERIFIED custom-domain binding, else `4xx`. Caddy
//!   mints a Let's Encrypt cert only for a `2xx`.
//! - `GET|POST /auth?cap=<name>` — the capability forward-auth gate: verifies the
//!   operator's printable token offline against the issuer public key; `2xx`
//!   admits, `401`/`403`/`503` denies.
//! - `GET  /healthz` — liveness for the deploy health-gate.
//!
//! Configuration (all environment, no hardcoded apex/domain):
//! - `DREGG_GATEWAY_ASK_BIND`      — bind address (default `127.0.0.1:8799`).
//! - `DREGG_HOSTING_APEX`          — the deployment hosting apex (read by the
//!   domain registry; the CNAME challenge target base + the launch landing apex).
//! - `DREGG_GATEWAY_AUTH_ROOT_PUBKEY` — the capability issuer public key (hex).
//!   Unset ⇒ every `/auth` route is fail-closed (`503`).
//!
//! The registry this process serves starts empty and is seeded by the binding
//! control plane (a `verify` turn adopts a proven binding) and by launch
//! composition (`compose_launch_landing`). A production deployment threads a
//! shared registry (or a persisted snapshot the process `adopt`s at boot); this
//! binary wires the serving surface.

use std::sync::Arc;

use dregg_gateway_ask::{GatewayState, bind_from_env, handle};
use starbridge_domains::DomainRegistry;

fn main() -> std::io::Result<()> {
    let bind = bind_from_env();

    // The registry reads its hosting apex from DREGG_HOSTING_APEX (else the
    // crate default) — configuration, never a compile-time constant.
    let registry = Arc::new(DomainRegistry::new());
    let state = GatewayState::new(registry).with_auth_root_from_env();

    let auth_status = if state.auth_root_pubkey_hex.is_some() {
        "capability gate ARMED (issuer key configured)"
    } else {
        "capability gate FAIL-CLOSED (no DREGG_GATEWAY_AUTH_ROOT_PUBKEY; /auth denies 503)"
    };
    eprintln!("gateway-ask: serving on {bind} — {auth_status}");
    eprintln!("gateway-ask: hosting apex = {}", state.registry.apex());
    eprintln!(
        "gateway-ask: routes = GET /internal/site-exists?domain=, GET|POST /auth?cap=, GET /healthz"
    );

    // The hardened std-net serve loop: one thread per connection under the
    // DREGG_HTTP_* robustness bounds (read/write timeouts, header cap, body cap,
    // connection ceiling). The handler is Send + Sync + 'static (state clones
    // cheaply behind the Arc).
    http_serve::serve_http(&bind, move |req| handle(&state, req))
}
