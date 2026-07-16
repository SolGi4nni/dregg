//! # Dregg endpoints — the ONE source of truth for production domains.
//!
//! Historically the dregg domains were hardcoded as string literals in ~83
//! places across the codebase (SDK defaults, the discord bot, the TUI, the
//! browser extensions, the deploy Caddyfile, …). Pointing the system at a new
//! domain (production, a fork, a private deployment) was therefore an 83-edit
//! chore. This module decouples that: the named endpoints live HERE, default to
//! the current product `dregg.net` family (so a client with no override points
//! at a real host), and are driven by env vars.
//!
//! The domains serve DIFFERENT purposes and are kept as distinct NAMED
//! endpoints (they are not collapsed into one):
//!
//! | Field             | Default                          | Env var                | Purpose |
//! |-------------------|----------------------------------|------------------------|---------|
//! | [`api`]           | `dregg.net`                      | `DREGG_API_DOMAIN`     | The main / canonical API host. |
//! | [`devnet`]        | `node.dregg.net`                 | `DREGG_DEVNET_DOMAIN`  | The public devnet node (HTTP + WSS). |
//! | [`auth`]          | `auth.dregg.net`                 | `DREGG_AUTH_DOMAIN`    | The auth / credential surface. |
//! | [`gateway`]       | `gateway.dregg.net`              | `DREGG_GATEWAY_DOMAIN` | The macaroon discharge gateway. |
//! | [`hosting`]       | `dregg.works`                    | `DREGG_HOSTING_DOMAIN` | The WebOfCells cell-hosting wildcard. |
//! | [`portal`]        | `portal.dregg.studio`            | `DREGG_PORTAL_DOMAIN`  | The static portal / "live" network view. |
//!
//! [`api`]: DreggEndpoints::api
//! [`devnet`]: DreggEndpoints::devnet
//! [`auth`]: DreggEndpoints::auth
//! [`gateway`]: DreggEndpoints::gateway
//! [`hosting`]: DreggEndpoints::hosting
//! [`portal`]: DreggEndpoints::portal
//!
//! ## Usage
//!
//! ```
//! use dregg_sdk::endpoints::DreggEndpoints;
//!
//! // Pure defaults (no env reads) — useful in const-ish contexts and tests.
//! let e = DreggEndpoints::production();
//! assert_eq!(e.devnet, "node.dregg.net");
//! assert_eq!(e.devnet_url(), "https://node.dregg.net");
//! assert_eq!(e.devnet_wss_url(), "wss://node.dregg.net/ws");
//!
//! // Env-driven: each field falls back to its production default when the
//! // corresponding DREGG_*_DOMAIN var is unset/empty, so behavior is unchanged
//! // until an operator overrides a domain.
//! let live = DreggEndpoints::from_env();
//! ```

/// The default (current production) domains. Changing the live deployment is a
/// matter of setting the `DREGG_*_DOMAIN` env vars — see [`DreggEndpoints::from_env`].
pub mod defaults {
    /// The main / canonical API host (the non-prefixed product `dregg.net`).
    pub const API: &str = "dregg.net";
    /// The public devnet node host (HTTP API + WSS event stream).
    pub const DEVNET: &str = "node.dregg.net";
    /// The auth / credential surface.
    pub const AUTH: &str = "auth.dregg.net";
    /// The macaroon discharge gateway.
    pub const GATEWAY: &str = "gateway.dregg.net";
    /// The WebOfCells cell-hosting wildcard root.
    pub const HOSTING: &str = "dregg.works";
    /// The static portal / "live" network view.
    pub const PORTAL: &str = "portal.dregg.studio";
}

/// The named dregg endpoints. Each field is a bare domain (no scheme); use the
/// `*_url` helpers to build `https://` / `wss://` URLs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DreggEndpoints {
    /// The main / canonical API host.
    pub api: String,
    /// The public devnet node host (HTTP + WSS).
    pub devnet: String,
    /// The auth / credential surface.
    pub auth: String,
    /// The macaroon discharge gateway.
    pub gateway: String,
    /// The WebOfCells cell-hosting wildcard root.
    pub hosting: String,
    /// The static portal / "live" network view.
    pub portal: String,
}

impl DreggEndpoints {
    /// The current production domains, with NO environment reads. This is the
    /// set of defaults baked into the system; [`from_env`](Self::from_env)
    /// layers env overrides on top of these.
    pub fn production() -> Self {
        Self {
            api: defaults::API.to_string(),
            devnet: defaults::DEVNET.to_string(),
            auth: defaults::AUTH.to_string(),
            gateway: defaults::GATEWAY.to_string(),
            hosting: defaults::HOSTING.to_string(),
            portal: defaults::PORTAL.to_string(),
        }
    }

    /// Resolve the endpoints from the environment, each field falling back to
    /// its production default when its `DREGG_*_DOMAIN` var is unset or empty:
    ///
    /// - `DREGG_API_DOMAIN`     → [`api`](Self::api)
    /// - `DREGG_DEVNET_DOMAIN`  → [`devnet`](Self::devnet)
    /// - `DREGG_AUTH_DOMAIN`    → [`auth`](Self::auth)
    /// - `DREGG_GATEWAY_DOMAIN` → [`gateway`](Self::gateway)
    /// - `DREGG_HOSTING_DOMAIN` → [`hosting`](Self::hosting)
    /// - `DREGG_PORTAL_DOMAIN`  → [`portal`](Self::portal)
    ///
    /// With no vars set this is byte-identical to [`production`](Self::production),
    /// so deployments that don't opt in see unchanged behavior.
    pub fn from_env() -> Self {
        Self {
            api: env_or("DREGG_API_DOMAIN", defaults::API),
            devnet: env_or("DREGG_DEVNET_DOMAIN", defaults::DEVNET),
            auth: env_or("DREGG_AUTH_DOMAIN", defaults::AUTH),
            gateway: env_or("DREGG_GATEWAY_DOMAIN", defaults::GATEWAY),
            hosting: env_or("DREGG_HOSTING_DOMAIN", defaults::HOSTING),
            portal: env_or("DREGG_PORTAL_DOMAIN", defaults::PORTAL),
        }
    }

    /// `https://{api}` — the canonical API base URL.
    pub fn api_url(&self) -> String {
        https(&self.api)
    }
    /// `https://{devnet}` — the devnet node base URL (the default an SDK / TUI /
    /// extension points at when no explicit URL is given).
    pub fn devnet_url(&self) -> String {
        https(&self.devnet)
    }
    /// `wss://{devnet}/ws` — the devnet node event-stream URL.
    pub fn devnet_wss_url(&self) -> String {
        format!("wss://{}/ws", self.devnet)
    }
    /// `https://{auth}` — the auth / credential surface base URL.
    pub fn auth_url(&self) -> String {
        https(&self.auth)
    }
    /// `https://{gateway}` — the macaroon discharge gateway base URL.
    pub fn gateway_url(&self) -> String {
        https(&self.gateway)
    }
    /// `https://{portal}` — the static portal base URL.
    pub fn portal_url(&self) -> String {
        https(&self.portal)
    }
}

impl Default for DreggEndpoints {
    /// [`from_env`](Self::from_env): honor `DREGG_*_DOMAIN` overrides, else the
    /// production defaults.
    fn default() -> Self {
        Self::from_env()
    }
}

fn https(domain: &str) -> String {
    format!("https://{domain}")
}

/// Read `var`, returning its trimmed value when present and non-empty, else
/// `fallback`.
fn env_or(var: &str, fallback: &str) -> String {
    match std::env::var(var) {
        Ok(v) if !v.trim().is_empty() => v.trim().to_string(),
        _ => fallback.to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn production_matches_current_domains() {
        let e = DreggEndpoints::production();
        assert_eq!(e.api, "dregg.net");
        assert_eq!(e.devnet, "node.dregg.net");
        assert_eq!(e.auth, "auth.dregg.net");
        assert_eq!(e.gateway, "gateway.dregg.net");
        assert_eq!(e.hosting, "dregg.works");
        assert_eq!(e.portal, "portal.dregg.studio");
    }

    #[test]
    fn url_helpers_preserve_current_literals() {
        let e = DreggEndpoints::production();
        assert_eq!(e.devnet_url(), "https://node.dregg.net");
        assert_eq!(e.devnet_wss_url(), "wss://node.dregg.net/ws");
        assert_eq!(e.api_url(), "https://dregg.net");
        assert_eq!(e.gateway_url(), "https://gateway.dregg.net");
        assert_eq!(e.portal_url(), "https://portal.dregg.studio");
    }

    #[test]
    fn env_unset_equals_production() {
        // No DREGG_*_DOMAIN vars are set in the test environment, so from_env
        // must reproduce the production defaults exactly.
        assert_eq!(DreggEndpoints::from_env(), DreggEndpoints::production());
    }
}
