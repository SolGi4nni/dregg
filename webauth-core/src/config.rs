// PORTED dregg-native from the prior operated layer (verbatim; unhex32 from credext).

//! Runtime configuration for the forward-auth service, read from the
//! environment (the compose / systemd path).

use std::collections::{BTreeMap, BTreeSet};

/// The forward-auth service configuration.
#[derive(Clone, Debug)]
pub struct WebAuthConfig {
    /// Address to bind (`DREGG_WEBAUTH_BIND`, default `0.0.0.0:8099`).
    pub bind: String,
    /// The issuer's ed25519 public key, hex (`DREGG_WEBAUTH_ROOT_PUBKEY`).
    /// REQUIRED in production: credentials verify under this and only this key.
    pub root_pubkey_hex: Option<String>,
    /// Break-glass override token (`DREGG_WEBAUTH_BREAK_GLASS`). When set, a
    /// request presenting this exact token in the `X-Dregg-Break-Glass` header
    /// or `dregg_break_glass` cookie is admitted regardless of the cap flow —
    /// so the operator is never locked out if the cap flow breaks. Unset
    /// (default) disables the override entirely.
    pub break_glass: Option<String>,
    /// Maps a request Host (the surface) to its required capability, so the
    /// service can derive the cap from the `X-Forwarded-Host` Caddy passes
    /// when no explicit `?cap=` query is present. Read from
    /// `DREGG_WEBAUTH_HOST_CAPS` as `host=cap,host2=cap2`.
    pub host_caps: BTreeMap<String, String>,
    /// The cookie name carrying the session credential (default `dregg_session`).
    pub cookie_name: String,
    /// Cookie/redirect domain for the login flow (`DREGG_WEBAUTH_COOKIE_DOMAIN`).
    pub cookie_domain: Option<String>,
    /// The PUBLIC path prefix the login flow is reachable at, as seen by the
    /// browser through Caddy (`DREGG_WEBAUTH_LOGIN_BASE`, default empty). In the
    /// deployment Caddy maps `<base>/*` to this service (stripping the prefix),
    /// so `<base>` must be a path that does NOT collide with the gated upstream
    /// (grafana and ops both serve their own `/login`). Set it to e.g.
    /// `/.dregg-auth`; the `/auth` deny-redirect and the form action both honor it.
    pub login_base: String,
    /// The **revocation deny-set** — the cloud-side analogue of
    /// `Effect::RevokeCapability` (Tier 0 compromise response). A presented
    /// credential is refused, AFTER its signature/cap checks would otherwise
    /// admit it, iff EITHER its tail commitment hex
    /// (`Credential::tail_hex`) OR its account subject
    /// ([`crate::subject_of`]) appears here. Keying on the tail kills exactly one
    /// leaked session token; keying on the subject kills every session for a
    /// compromised account (the proactive "rotate-out" companion). Offline-
    /// distributable: a signed list the forward-auth service loads
    /// (`DREGG_WEBAUTH_REVOKED` inline, `DREGG_WEBAUTH_REVOKED_FILE` a path).
    pub revoked: BTreeSet<String>,
    /// Default Time-To-Live (seconds) stamped as a `NotAfter` expiry on a freshly
    /// minted / re-issued session credential (`DREGG_WEBAUTH_SESSION_TTL`, default
    /// 24h). Bounds the blast radius of a leaked bearer token even before it is
    /// explicitly revoked: it self-expires. `0`/unset on the mint path means "no
    /// default expiry" (the legacy behaviour), but the deployment SHOULD set it.
    /// Also caps the session cookie's `Max-Age`.
    pub session_ttl_secs: Option<u64>,
    /// The key that authenticates login **challenges** (the stateless
    /// proof-of-possession nonce). Set from `DREGG_WEBAUTH_CHALLENGE_KEY` (hex,
    /// 32 bytes); if unset a fresh per-process random key is generated (a pending
    /// challenge then simply does not survive a webauth restart — fine for a
    /// 2-minute window). Set it explicitly across replicas so a challenge issued
    /// by one instance verifies at another.
    pub challenge_key: [u8; 32],
    /// The login challenge lifetime in seconds (`DREGG_WEBAUTH_CHALLENGE_TTL`,
    /// default [`crate::challenge::DEFAULT_CHALLENGE_TTL_SECS`]).
    pub challenge_ttl_secs: u64,
}

/// The recommended default session lifetime: 24 hours. Short enough that a
/// leaked bearer token self-expires within a day, long enough not to nag a
/// working operator. Re-issued on each login.
pub const DEFAULT_SESSION_TTL_SECS: u64 = 24 * 60 * 60;

impl Default for WebAuthConfig {
    fn default() -> Self {
        Self {
            bind: "0.0.0.0:8099".to_string(),
            root_pubkey_hex: None,
            break_glass: None,
            host_caps: BTreeMap::new(),
            cookie_name: "dregg_session".to_string(),
            cookie_domain: None,
            login_base: String::new(),
            revoked: BTreeSet::new(),
            session_ttl_secs: Some(DEFAULT_SESSION_TTL_SECS),
            challenge_key: random_key(),
            challenge_ttl_secs: crate::challenge::DEFAULT_CHALLENGE_TTL_SECS,
        }
    }
}

/// A fresh 32-byte key from OS randomness (the per-process challenge key when
/// `DREGG_WEBAUTH_CHALLENGE_KEY` is not set).
fn random_key() -> [u8; 32] {
    let mut k = [0u8; 32];
    getrandom::fill(&mut k).expect("operating-system randomness is available");
    k
}

impl WebAuthConfig {
    /// Is `tail_hex` / `subject` revoked? Either matching the deny-set refuses.
    pub fn is_revoked(&self, tail_hex: &str, subject: Option<&str>) -> bool {
        if self.revoked.is_empty() {
            return false;
        }
        if self.revoked.contains(tail_hex) {
            return true;
        }
        matches!(subject, Some(s) if self.revoked.contains(s))
    }

    /// Read configuration from the environment.
    pub fn from_env() -> Self {
        let mut cfg = Self::default();
        if let Ok(bind) = std::env::var("DREGG_WEBAUTH_BIND") {
            if !bind.trim().is_empty() {
                cfg.bind = bind;
            }
        }
        cfg.root_pubkey_hex = non_empty("DREGG_WEBAUTH_ROOT_PUBKEY");
        cfg.break_glass = non_empty("DREGG_WEBAUTH_BREAK_GLASS");
        cfg.cookie_domain = non_empty("DREGG_WEBAUTH_COOKIE_DOMAIN");
        if let Some(name) = non_empty("DREGG_WEBAUTH_COOKIE_NAME") {
            cfg.cookie_name = name;
        }
        if let Some(base) = non_empty("DREGG_WEBAUTH_LOGIN_BASE") {
            // Normalize: no trailing slash; the routes append `/login` etc.
            cfg.login_base = base.trim_end_matches('/').to_string();
        }
        if let Some(raw) = non_empty("DREGG_WEBAUTH_HOST_CAPS") {
            cfg.host_caps = parse_host_caps(&raw);
        }
        // The revocation deny-set: an inline comma/whitespace list and/or a file
        // of newline-separated entries (a tail hex or a `dregg:…` subject each).
        if let Some(raw) = non_empty("DREGG_WEBAUTH_REVOKED") {
            cfg.revoked.extend(parse_revoked(&raw));
        }
        if let Some(path) = non_empty("DREGG_WEBAUTH_REVOKED_FILE") {
            if let Ok(contents) = std::fs::read_to_string(&path) {
                cfg.revoked.extend(parse_revoked(&contents));
            } else {
                eprintln!("webauth-core: WARN revocation file `{path}` could not be read");
            }
        }
        match std::env::var("DREGG_WEBAUTH_SESSION_TTL") {
            Ok(v) if !v.trim().is_empty() => {
                cfg.session_ttl_secs = v.trim().parse::<u64>().ok().filter(|n| *n > 0);
            }
            _ => {}
        }
        // The challenge-authentication key (hex, 32 bytes). If set, challenges
        // issued by any replica sharing it verify at every replica; if unset the
        // per-process random key from `Default` stands (single-instance safe).
        if let Some(hex) = non_empty("DREGG_WEBAUTH_CHALLENGE_KEY") {
            match crate::credext::unhex32(hex.trim()) {
                Ok(k) => cfg.challenge_key = k,
                Err(_) => eprintln!(
                    "webauth-core: WARN DREGG_WEBAUTH_CHALLENGE_KEY is not 64 hex chars — using a per-process random key"
                ),
            }
        }
        if let Some(v) = non_empty("DREGG_WEBAUTH_CHALLENGE_TTL") {
            if let Some(n) = v.trim().parse::<u64>().ok().filter(|n| *n > 0) {
                cfg.challenge_ttl_secs = n;
            }
        }
        cfg
    }

    /// The capability required for a request, given the explicit `?cap=` query
    /// (Caddy's `forward_auth` copy_headers / query) and the forwarded Host.
    /// An explicit query wins; otherwise the host map is consulted.
    pub fn required_cap(&self, query_cap: Option<&str>, host: Option<&str>) -> Option<String> {
        if let Some(c) = query_cap {
            if !c.is_empty() {
                return Some(c.to_string());
            }
        }
        let host = host?;
        // Strip any port suffix from the Host header before matching.
        let host = host.split(':').next().unwrap_or(host);
        self.host_caps.get(host).cloned()
    }
}

fn non_empty(key: &str) -> Option<String> {
    std::env::var(key).ok().filter(|v| !v.trim().is_empty())
}

/// Parse a revocation list — entries separated by commas, whitespace, or
/// newlines; `#`-prefixed lines are comments. Each entry is a credential tail
/// hex or a `dregg:…` subject. Lowercased so tail-hex matching is canonical.
pub fn parse_revoked(raw: &str) -> BTreeSet<String> {
    raw.lines()
        .flat_map(|line| {
            let line = line.split('#').next().unwrap_or("");
            line.split([',', ' ', '\t'])
                .map(str::trim)
                .filter(|s| !s.is_empty())
                .map(|s| s.to_ascii_lowercase())
                .collect::<Vec<_>>()
        })
        .collect()
}

/// Parse `host=cap,host2=cap2` into a map.
pub fn parse_host_caps(raw: &str) -> BTreeMap<String, String> {
    raw.split(',')
        .filter_map(|pair| {
            let (h, c) = pair.split_once('=')?;
            let h = h.trim();
            let c = c.trim();
            if h.is_empty() || c.is_empty() {
                return None;
            }
            Some((h.to_string(), c.to_string()))
        })
        .collect()
}
