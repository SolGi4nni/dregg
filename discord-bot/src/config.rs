//! Environment-based configuration for the Discord bot.

use std::env;

/// Bot configuration loaded from environment variables.
#[derive(Clone)]
pub struct Config {
    /// Discord bot token.
    pub discord_token: String,
    /// Discord application ID (for slash command registration).
    pub discord_app_id: u64,
    /// Secret used for deterministic key derivation (32 bytes hex-encoded).
    pub bot_secret: [u8; 32],
    /// Base URL for the devnet API.
    pub devnet_url: String,
    /// SQLite database URL.
    pub database_url: String,

    // ─── Production HTTP read surface (§4.7 Starbridge RemoteRuntime) ─────
    /// Host to bind the axum HTTP read server (e.g. "0.0.0.0" or "127.0.0.1").
    pub http_host: String,
    /// Port for the HTTP read surface (default 8080; choose non-privileged in prod).
    pub http_port: u16,

    // ─── Soft-federation / clique identity (no more hard-coded zero bytes) ─
    /// Federation ID (32 raw bytes) this bot instance participates in.
    /// Loaded from FEDERATION_ID env (64 hex chars) or defaults to all-zero
    /// (suitable only for single-bot dev; real cliques must set the shared root).
    pub federation_id_bytes: [u8; 32],

    // ─── DreggNet Cloud admin surface ────────────────────────────────────
    /// The PRIMARY admin (ember) Discord user id — a single id, because this one
    /// is a *channel-visibility* fact: their per-user channels gain admin
    /// visibility and they are the recipient of every semi-private channel's read
    /// access (`channels::plan_private_overwrites`, every `CreateSessionChannel`).
    /// `None` = no admin pinned (dev/single-user).
    ///
    /// This is NOT the authorization set. An admin *command* asks
    /// [`Config::is_admin`], which consults [`Config::admin_discord_ids`].
    pub admin_discord_id: Option<u64>,
    /// The AUTHORIZATION set: every Discord user id allowed to drive an admin
    /// command. Parsed from `ADMIN_DISCORD_IDS` (comma-separated) unioned with the
    /// single `ADMIN_DISCORD_ID`, so the existing single-value deployment keeps
    /// working unchanged. EMPTY DENIES EVERYONE — an unconfigured bot must never
    /// read as "everyone is admin" (the same posture `authorize_open` takes).
    pub admin_discord_ids: Vec<u64>,
    /// Bearer token gating the admin webportal (`/admin`). `None` disables the
    /// admin surface entirely (it returns 404). In production this sits behind
    /// Caddy basic-auth on the edge as well — defence in depth.
    pub admin_token: Option<String>,
}

/// Parse the admin authorization set from the two env forms — PURE, so the
/// fail-closed rule is testable without touching the process environment.
///
/// `single` is `ADMIN_DISCORD_ID` (the existing var, also the channel-visibility
/// admin); `list` is `ADMIN_DISCORD_IDS` (comma-separated). The result is their
/// union, de-duplicated, with the single id FIRST when present so the primary
/// admin is stable. Unparseable and zero entries are dropped (`0` is not a valid
/// snowflake) rather than silently widening the set.
pub fn parse_admin_ids(single: Option<&str>, list: Option<&str>) -> Vec<u64> {
    let mut ids: Vec<u64> = Vec::new();
    let mut push = |id: u64| {
        if id != 0 && !ids.contains(&id) {
            ids.push(id);
        }
    };
    if let Some(id) = single.and_then(|s| s.trim().parse::<u64>().ok()) {
        push(id);
    }
    for entry in list.unwrap_or_default().split(',') {
        let entry = entry.trim();
        if entry.is_empty() {
            continue;
        }
        match entry.parse::<u64>() {
            Ok(id) => push(id),
            Err(_) => eprintln!(
                "warning: ADMIN_DISCORD_IDS entry {entry:?} is not a numeric Discord user id; skipping"
            ),
        }
    }
    ids
}

impl Config {
    /// **The admin gate.** Whether `user_id` may drive an admin command.
    ///
    /// FAIL-CLOSED: an empty [`Config::admin_discord_ids`] (neither
    /// `ADMIN_DISCORD_ID` nor `ADMIN_DISCORD_IDS` set) denies EVERYONE. There is
    /// deliberately no "no admin configured ⇒ anyone may" arm, and no Discord
    /// server-permission fallback: a guild administrator is an authority over
    /// *their guild*, not over this bot's operator settings (its narrator, its
    /// treasury, its credit ledger), which are shared across every guild it
    /// serves.
    pub fn is_admin(&self, user_id: u64) -> bool {
        self.admin_discord_ids.contains(&user_id)
    }
}

impl Config {
    /// Load configuration from environment variables.
    ///
    /// Returns a friendly error string (for operator UX) instead of panicking
    /// on missing/malformed required vars. This improves the "run the bot"
    /// experience and avoids scary stack traces for common misconfiguration.
    pub fn from_env() -> Result<Self, String> {
        let discord_token = env::var("DISCORD_TOKEN")
            .map_err(|_| "DISCORD_TOKEN environment variable is required (your bot token from Discord developer portal)".to_string())?;

        let app_id_str = env::var("DISCORD_APP_ID")
            .map_err(|_| "DISCORD_APP_ID environment variable is required (the numeric Application ID from Discord developer portal)".to_string())?;
        let discord_app_id: u64 = app_id_str
            .parse()
            .map_err(|_| format!("DISCORD_APP_ID must be a valid u64, got: {}", app_id_str))?;

        let secret_hex = env::var("BOT_SECRET")
            .map_err(|_| "BOT_SECRET environment variable is required (64 hex chars; the 32-byte secret used for deterministic per-user cipherclerk derivation)".to_string())?;
        let secret_bytes =
            hex::decode(&secret_hex).map_err(|e| format!("BOT_SECRET must be valid hex: {}", e))?;
        let bot_secret: [u8; 32] = secret_bytes
            .try_into()
            .map_err(|_| "BOT_SECRET must be exactly 32 bytes (64 hex chars)".to_string())?;

        // `DEVNET_URL` (explicit, full URL) wins; otherwise fall back to the
        // central endpoint config — the devnet domain there is itself overridable
        // via `DREGG_DEVNET_DOMAIN`, so the production domain lives in ONE place.
        let devnet_url = env::var("DEVNET_URL")
            .unwrap_or_else(|_| dregg_sdk::DreggEndpoints::from_env().devnet_url());

        let database_url = env::var("DATABASE_URL").unwrap_or_else(|_| "sqlite:bot.db".to_string());

        // Production HTTP surface (Starbridge RemoteRuntime / observability)
        let http_host = env::var("HTTP_HOST").unwrap_or_else(|_| "0.0.0.0".to_string());
        let http_port: u16 = env::var("HTTP_PORT")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(8080);

        // Soft-federation root (single Ed25519 trust root for the friend clique).
        // Real deployments MUST supply the 64-hex FEDERATION_ID shared by the clique.
        // Default (all-zero) is only for local dev and single-bot testing.
        let fed_hex = env::var("FEDERATION_ID").unwrap_or_else(|_| "0".repeat(64));
        let fed_bytes_vec = hex::decode(&fed_hex)
            .map_err(|e| format!("FEDERATION_ID must be valid 64-char hex: {}", e))?;
        let federation_id_bytes: [u8; 32] = fed_bytes_vec
            .try_into()
            .map_err(|_| "FEDERATION_ID must decode to exactly 32 bytes".to_string())?;

        if federation_id_bytes.iter().all(|&b| b == 0) {
            // Non-fatal; operator sees in logs when bot starts. Production cliques set the value.
            eprintln!(
                "warning: FEDERATION_ID not set (or all-zero); using dev default. Set FEDERATION_ID=<64 hex> for real soft-federation/clique use. (Against a reachable SOLO node the boot preflight fails FAST on a mismatch — every transfer would be rejected; see FEDERATION_ID_ALLOW_MISMATCH.)"
            );
        }

        // Admin (ember) identity + portal auth. Both optional: unset = no admin
        // pinned and the admin portal disabled.
        //
        // Two vars, one union: `ADMIN_DISCORD_ID` stays the PRIMARY admin (the
        // channel-visibility pin every session channel already grants read access
        // to), and `ADMIN_DISCORD_IDS` adds the rest of the authorization set.
        // Setting only the list still yields a primary (its first entry), so a
        // list-only deployment does not lose semi-private channel visibility.
        let single = env::var("ADMIN_DISCORD_ID").ok();
        let list = env::var("ADMIN_DISCORD_IDS").ok();
        let admin_discord_ids = parse_admin_ids(single.as_deref(), list.as_deref());
        let admin_discord_id = admin_discord_ids.first().copied();
        if admin_discord_ids.is_empty() {
            eprintln!(
                "warning: neither ADMIN_DISCORD_ID nor ADMIN_DISCORD_IDS is set; every admin command \
                 is REFUSED (fail-closed) and no admin is pinned for semi-private channel visibility. \
                 Set ADMIN_DISCORD_IDS=<your Discord user id> to enable them."
            );
        }
        let admin_token = env::var("ADMIN_TOKEN").ok().filter(|s| !s.is_empty());
        if admin_token.is_none() {
            eprintln!(
                "warning: ADMIN_TOKEN not set; the admin webportal (/admin) is DISABLED. Set ADMIN_TOKEN=<secret> to enable monitoring (and put Caddy basic-auth in front of it on the edge)."
            );
        }

        Ok(Self {
            discord_token,
            discord_app_id,
            bot_secret,
            devnet_url,
            database_url,
            http_host,
            http_port,
            federation_id_bytes,
            admin_discord_id,
            admin_discord_ids,
            admin_token,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A `Config` with only the admin fields populated — everything else is
    /// irrelevant to the gate and never read by it.
    fn cfg(ids: Vec<u64>) -> Config {
        Config {
            discord_token: String::new(),
            discord_app_id: 0,
            bot_secret: [0u8; 32],
            devnet_url: String::new(),
            database_url: String::new(),
            http_host: String::new(),
            http_port: 0,
            federation_id_bytes: [0u8; 32],
            admin_discord_id: ids.first().copied(),
            admin_discord_ids: ids,
            admin_token: None,
        }
    }

    /// The single existing var keeps working, the list adds to it, and the union
    /// is de-duplicated with the PRIMARY (single) id first.
    #[test]
    fn admin_ids_union_the_single_var_and_the_list() {
        assert_eq!(
            parse_admin_ids(Some("192258292544700426"), None),
            vec![192258292544700426]
        );
        assert_eq!(parse_admin_ids(None, Some("111,222")), vec![111, 222]);
        assert_eq!(
            parse_admin_ids(Some("999"), Some("111, 222 ,999")),
            vec![999, 111, 222],
            "the primary id sorts first and is not duplicated by the list"
        );
    }

    /// Garbage never widens the set: an unparseable entry, a zero snowflake and
    /// empty segments are dropped, not admitted.
    #[test]
    fn admin_id_parsing_drops_garbage_rather_than_widening() {
        assert!(parse_admin_ids(Some("not-a-number"), None).is_empty());
        assert!(
            parse_admin_ids(None, Some("0")).is_empty(),
            "0 is not a snowflake"
        );
        assert_eq!(parse_admin_ids(None, Some(" , 111 , , nope ,")), vec![111]);
        assert!(parse_admin_ids(None, None).is_empty());
        assert!(parse_admin_ids(None, Some("")).is_empty());
    }

    /// **THE GATE, both directions.** An unconfigured bot denies EVERYONE — an
    /// empty admin set must never read as "everyone is admin".
    #[test]
    fn the_admin_gate_denies_when_unconfigured_and_denies_non_admins() {
        let unconfigured = cfg(Vec::new());
        assert!(!unconfigured.is_admin(192258292544700426));
        assert!(!unconfigured.is_admin(0));

        let configured = cfg(vec![192258292544700426, 111]);
        assert!(configured.is_admin(192258292544700426));
        assert!(configured.is_admin(111), "a listed co-admin is admitted");
        assert!(
            !configured.is_admin(222),
            "an unlisted user is REFUSED even on a configured bot"
        );
        assert_eq!(
            configured.admin_discord_id,
            Some(192258292544700426),
            "the primary (channel-visibility) admin is the first id"
        );
    }
}
