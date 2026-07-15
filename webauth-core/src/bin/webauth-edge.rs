//! `webauth-edge` — the capability forward-auth serving binary.
//!
//! It reads its configuration from the environment and serves the `/auth`
//! forward-auth decision + the passwordless login flow forever (pure `std`,
//! thread-per-connection — no async runtime, cross-builds trivially).
//!
//! A reverse proxy (see `deploy/webauth-edge/Caddyfile.capauth`) gates every
//! protected surface through `GET /auth` and maps the login flow
//! (`<login_base>/login`, `/login/challenge`, `/logout`, `/healthz`) as public
//! paths. Each admitted request carries back the VERIFIED `X-Dregg-Subject` /
//! `X-Dregg-Cap` the upstream trusts.
//!
//! Minimal single-surface run:
//!
//! ```text
//!   DREGG_WEBAUTH_ROOT_PUBKEY=<hex> \
//!   DREGG_WEBAUTH_HOST_CAPS='ops.example=ops-admin,launchpad.example=launchpad-operator' \
//!   DREGG_WEBAUTH_LOGIN_BASE=/.auth \
//!   DREGG_WEBAUTH_SESSION_TTL=86400 \
//!   webauth-edge --bind 0.0.0.0:8099
//! ```
//!
//! Every host, cap, cookie domain, and login base is configuration — there is no
//! hardcoded apex. Mint the root authority + capabilities with the issuing side
//! (`webauth_core::grant`), publish the root public key as
//! `DREGG_WEBAUTH_ROOT_PUBKEY`, and hand a user a `dga1_…` capability to sign in.

use webauth_core::config::WebAuthConfig;
use webauth_core::server;

fn main() -> std::io::Result<()> {
    let mut cfg = WebAuthConfig::from_env();
    // `--bind` override (a supervisor may pass it; the env is the main path).
    let args: Vec<String> = std::env::args().collect();
    if let Some(i) = args.iter().position(|a| a == "--bind") {
        if let Some(b) = args.get(i + 1) {
            cfg.bind = b.clone();
        }
    }
    server::serve(cfg)
}
