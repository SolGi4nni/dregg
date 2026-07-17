//! **Per-Telegram-user derived dregg identity** — the faithful mirror of
//! `discord-bot/src/cipherclerk.rs`'s `UserCipherclerk::derive`. A Telegram user id becomes a
//! deterministic 32-byte seed, fed to the canonical `AgentCipherclerk::from_key_bytes` to produce
//! a REAL Ed25519 signing identity; the [`dreggnet_offerings::DreggIdentity`] a
//! [`crate::TelegramFrontend`] attributes moves to is that key's public-key hex — the SAME kind of
//! handle the Discord frontend derives, just under a Telegram-scoped BLAKE3 domain:
//!
//! ```text
//! seed = BLAKE3_derive_key("dregg-telegram-bot-v1", bot_secret || telegram_user_id_le)
//! ```
//!
//! Cross-platform, by construction: the SAME primitive on both frontends, a per-platform domain so
//! a Discord user and a Telegram user never collide, and a Telegram user always re-derives the
//! SAME dregg identity (reproducible custodial keys). Nothing here is Telegram-transport-specific —
//! it needs no token and no network.

use dregg_sdk::AgentCipherclerk;
use dreggnet_offerings::DreggIdentity;
use zeroize::Zeroizing;

/// The BLAKE3 derive-key domain for Telegram custodial seeds — the Telegram analogue of the
/// discord bot's `"dregg-discord-bot-v1"`. A distinct domain per frontend keeps the two platforms'
/// user-id spaces from ever colliding onto one dregg identity.
pub const TELEGRAM_SEED_DOMAIN: &str = "dregg-telegram-bot-v1";

/// The BLAKE3 derive-key domain the identity **master secret** falls back to when
/// `TELEGRAM_BOT_SECRET` is unset: `master = BLAKE3_derive_key(this, bot_token)`. Pinned — a
/// changed domain (or a rotated token on the fallback path) rotates EVERY derived identity.
pub const MASTER_SECRET_DOMAIN: &str = "dregg-telegram-bot identity master secret v1";

/// **Resolve the 32-byte identity master secret** — `explicit` (the `TELEGRAM_BOT_SECRET` env
/// value: 64 hex chars) when present and non-empty, else BLAKE3-derived from the token under
/// [`MASTER_SECRET_DOMAIN`]. The PURE core of [`master_secret_from_env`], separable for tests.
pub fn master_secret_from(token: &str, explicit: Option<&str>) -> Result<[u8; 32], String> {
    match explicit {
        Some(hexed) if !hexed.trim().is_empty() => {
            let bytes = hex::decode(hexed.trim())
                .map_err(|e| format!("TELEGRAM_BOT_SECRET is not hex: {e}"))?;
            <[u8; 32]>::try_from(bytes.as_slice()).map_err(|_| {
                format!(
                    "TELEGRAM_BOT_SECRET needs exactly 32 bytes (64 hex chars), got {}",
                    bytes.len()
                )
            })
        }
        _ => Ok(blake3::derive_key(MASTER_SECRET_DOMAIN, token.as_bytes())),
    }
}

/// The identity master secret from the environment: explicit `TELEGRAM_BOT_SECRET` (64 hex
/// chars) when set, else token-derived under the pinned [`MASTER_SECRET_DOMAIN`]. **The ONE
/// implementation both custodial processes call** — the bot binary and `dreggnet-web`'s Mini App
/// surface MUST resolve the same secret, or the "same" Telegram user forks into two dregg
/// identities. (Deploy corollary: set an explicit `TELEGRAM_BOT_SECRET` in BOTH unit files so a
/// BotFather token rotation does not silently rotate every custodial identity.)
pub fn master_secret_from_env(token: &str) -> Result<[u8; 32], String> {
    master_secret_from(token, std::env::var("TELEGRAM_BOT_SECRET").ok().as_deref())
}

/// The deterministic 32-byte custodial seed for a Telegram user — `seed =
/// BLAKE3_derive_key("dregg-telegram-bot-v1", bot_secret || telegram_user_id_le)`. This seed IS the
/// Ed25519 secret handed to `AgentCipherclerk::from_key_bytes`, so the identity is reproducible
/// (the exact shape of `discord-bot`'s `seed_for`, Telegram id in place of the Discord snowflake).
pub fn seed_for(bot_secret: &[u8; 32], telegram_user_id: u64) -> [u8; 32] {
    let mut input = Vec::with_capacity(32 + 8);
    input.extend_from_slice(bot_secret);
    input.extend_from_slice(&telegram_user_id.to_le_bytes());
    blake3::derive_key(TELEGRAM_SEED_DOMAIN, &input)
}

/// A deterministic per-Telegram-user cipherclerk handle — a real Ed25519 identity derived from the
/// bot secret + the Telegram user id. The mirror of `UserCipherclerk`, minus the legacy BLAKE3-MAC
/// wire path (this frontend has no legacy devnet endpoints to serve).
pub struct TelegramCipherclerk {
    /// The canonical agent cipherclerk (Ed25519, deterministic from the seed).
    agent: AgentCipherclerk,
    /// Cached hex-encoded Ed25519 public key — the [`DreggIdentity`] handle.
    public_key_hex_cached: String,
}

impl TelegramCipherclerk {
    /// Derive the cclerk for `telegram_user_id` under `bot_secret`. Deterministic and
    /// reproducible: the same inputs always yield the same Ed25519 identity.
    pub fn derive(bot_secret: &[u8; 32], telegram_user_id: u64) -> Self {
        // The transient seed copy handed to `from_key_bytes` is wiped after construction (as the
        // discord cclerk does).
        let secret = Zeroizing::new(seed_for(bot_secret, telegram_user_id));
        let agent = AgentCipherclerk::from_key_bytes(secret);
        let public_key_hex_cached = hex::encode(agent.public_key().0);
        TelegramCipherclerk {
            agent,
            public_key_hex_cached,
        }
    }

    /// The user's Ed25519 public key as lowercase hex.
    pub fn public_key_hex(&self) -> &str {
        &self.public_key_hex_cached
    }

    /// The user's Ed25519 public key as raw bytes — the electorate handle a
    /// `CouncilOffering` (via `dreggnet_catalog::CatalogConfig::council_members`) registers a member by (its
    /// [`identity`](Self::identity) is the lowercase-hex of these bytes, so a member's press
    /// matches the registered council member).
    pub fn public_key_bytes(&self) -> [u8; 32] {
        self.agent.public_key().0
    }

    /// The user's frontend-agnostic [`DreggIdentity`] (the public-key hex handle the core
    /// attributes moves to). The SAME actor → the SAME identity, on every frontend.
    pub fn identity(&self) -> DreggIdentity {
        DreggIdentity(self.public_key_hex_cached.clone())
    }

    /// The underlying agent cipherclerk — for a real deploy to actually SIGN a turn on the user's
    /// behalf (this crate only needs the public identity for attribution).
    pub fn agent(&self) -> &AgentCipherclerk {
        &self.agent
    }
}
