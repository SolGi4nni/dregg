//! # `discord_activity` — the Discord **Activity** (`/da`) surface's trust root.
//!
//! Design: `docs/DISCORD-ACTIVITIES-DESIGN.md`. A Discord Activity is this server's web app loaded
//! in a sandboxed iframe inside the Discord client. Unlike Telegram's initData (a self-contained
//! HMAC envelope Telegram hands the page), Discord's OAuth gives no re-validatable envelope —
//! verifying identity needs a Discord API round-trip. So the server verifies the uid ONCE (at
//! `/da/token`, via the OAuth code exchange + `/users/@me`) and then mints its OWN stateless
//! envelope — the **activity ticket** — restoring the exact `/tg/*` shape: a bearer credential the
//! client re-presents on every state-touching request, re-validated by a PURE function on each hit.
//!
//! ## What THIS module implements (the pure, testable trust root)
//!
//! The two pieces that need neither a live Discord app nor the OAuth secret to be correct:
//!
//! 1. [`mint_ticket`] — issue `ticket = base64url( uid ‖ minted_at ‖ nonce ‖ HMAC_SHA256(ticket_key,
//!    uid ‖ minted_at ‖ nonce) )`, with `uid`/`minted_at` as little-endian `u64` (the [`seed_for`
//!    ](dreggnet_discord_identity::seed_for) LE convention). `ticket_key` is
//!    [`ticket_key`]`(BOT_SECRET)` = `BLAKE3_derive_key("dregg-discord-activity-ticket-v1",
//!    BOT_SECRET)` — domain-separated from the signing seed AND the link-challenge key.
//! 2. [`validate_ticket_at`] — the PURE validator (no I/O, no clock: the caller injects `now` and
//!    the freshness window), mirroring [`telegram_miniapp::validate_init_data_at`
//!    ](crate::telegram_miniapp::validate_init_data_at) EXACTLY in shape + gate order:
//!    parse (`400`) → constant-time HMAC (`403`) → freshness window + future-skew (`403`) → and
//!    only after ALL gates is the uid read — the ONLY trusted Discord identity on the surface.
//!
//! The client attaches the ticket to every state-touching request in [`ACTIVITY_TICKET_HEADER`] (a
//! header, never a URL — bearer-like, never logged; the verified uid + `minted_at` are logged
//! instead), exactly as `/tg` uses `X-Telegram-Init-Data`.
//!
//! ## Honest attestation statement (unchanged from `/tg`)
//!
//! Discord's OAuth attests the HUMAN (this uid completed the flow within the window); the server
//! signs the turn with the key it CUSTODIANS for that human. The signature proves what signatures
//! prove; the ticket gate is what binds the human to the key on each request. The custodial key is
//! [`seed_for`](dreggnet_discord_identity::seed_for)`(BOT_SECRET, uid)` — byte-for-byte the identity
//! the in-chat Discord bot attributes (the extraction, design §3): the Activity player IS the
//! in-chat player.
//!
//! ## The `/da` surface (built here — the OAuth token-exchange STRUCTURE + the catalog routes)
//!
//! Beyond the pure trust root, this module now builds the whole `/da` scope (design §4), driving the
//! SAME `Arc<CatalogState>` as the cookie-identity catalog and the `/tg` Mini App — one registry,
//! three trust stories, never one handler:
//!
//! - [`DiscordActivityState`] — the `TgMiniAppState` analog: the shared catalog host plus
//!   `client_id` / `client_secret` (the OAuth credential), the identity `bot_secret`, the precomputed
//!   `ticket_key`, and the freshness window.
//! - `POST /da/token` — the ONE outbound HTTP call: the Discord OAuth `code` → `oauth2/token` →
//!   `/users/@me` exchange proves the uid, then [`mint_ticket`] issues the first ticket. Structured
//!   behind the [`DiscordTokenExchange`] trait (real backend [`HttpDiscordOAuth`]; a test stub in the
//!   suite) so the module compiles + the mint/response/parse structure is testable with NO live
//!   Discord app or secret. Returns `{ access_token, ticket, custodial_pubkey_hex }`.
//! - `GET /da` (+ same-origin `/da/static/*`) — the Activity shell: a strict-CSP static page that
//!   loads the (vendored) Discord Embedded App SDK, runs `sdk.ready()` + `authorize({scope:
//!   ['identify']})`, POSTs the code to `/da/token`, and attaches the returned ticket in
//!   [`ACTIVITY_TICKET_HEADER`] on every state-touching fetch — the `/tg` shell with the header
//!   renamed and the CSP hardened to the `/tg/link` review's posture.
//! - `GET /da/offerings`, `GET /da/offerings/{key}/session/{id}`, `POST …/act` — the ticket-gated
//!   catalog twins: validate → derive the SAME custodial signer → land ONE turn with verified
//!   `Signed` provenance inside a single host-thread job (`post_tg_act`'s body, ticket-gated).
//!
//! Mounted by [`discord_activity_from_env`] iff `DISCORD_CLIENT_ID` / `DISCORD_CLIENT_SECRET` /
//! `BOT_SECRET` are all set — one log line either way, every existing deployment untouched. The
//! cross-platform `/da/link` ceremony (design §5) is the next follow-up (the `/tg/link` twin).

use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

#[cfg(feature = "hosted-binary-operations")]
use axum::extract::Query;
use axum::{
    Json, Router,
    extract::{Form, Path, State},
    http::{HeaderMap, StatusCode, header},
    response::{Html, IntoResponse, Response},
    routing::{get, post},
};
use base64::Engine;
use base64::engine::general_purpose::URL_SAFE_NO_PAD;
use hmac::{Hmac, Mac};
use serde::Deserialize;
use sha2::Sha256;
use subtle::ConstantTimeEq;
use zeroize::Zeroizing;

use dreggnet_catalog::{game_kind, sign_game_action};
use dreggnet_discord_identity::seed_for;
use dreggnet_offerings::player_turn_receipt::{PlayerReplaySurface, PlayerTurnReceipt};
use dreggnet_offerings::{
    Action, Attribution, Custody, DreggIdentity, HostError, Outcome, SessionId, SignedError,
    TurnSigner,
};
use webauth_core::link_registry::LinkStore;

use crate::{
    CatalogGameError, CatalogState, OfferingActForm, act_signed, audit, metrics, open_audit_parts,
    refused_open_response, render_offering_response, wants_fragment,
};

// ─────────────────────────────────────────────────────────────────────────────
// Constants — the wire names, the pinned windows, and the ticket-key domain.
// ─────────────────────────────────────────────────────────────────────────────

/// The header the Activity shell attaches the ticket to on every state-touching request. A header,
/// never a URL: URLs leak into logs and Referer headers, and the ticket is bearer-like within its
/// freshness window. The `/da` analog of `X-Telegram-Init-Data`.
pub const ACTIVITY_TICKET_HEADER: &str = "x-dregg-activity-ticket";

/// The BLAKE3 derive-key domain for the ticket HMAC key — `ticket_key =
/// BLAKE3_derive_key(this, BOT_SECRET)`. Domain-separated from the signing seed
/// (`"dregg-discord-bot-v1"`) and the link-challenge key so a compromise of the ticket key never
/// reaches the custodial signing key.
pub const ACTIVITY_TICKET_KEY_DOMAIN: &str = "dregg-discord-activity-ticket-v1";

/// The env var tuning the ticket freshness window (seconds). Default
/// [`DEFAULT_ACTIVITY_TICKET_MAX_AGE_SECS`]. The ticket is a **bearer credential** (whoever holds
/// it acts as the verified uid within the window), so the default is a DELIBERATE, bounded choice —
/// long enough for a single play session, short enough that a captured ticket expires the same day.
/// A kiosk / all-day-stream deployment raises it explicitly; `authorize({prompt:'none'})` silently
/// re-issues on expiry for a returning user, so a tighter window is transparent to legitimate use.
pub const DISCORD_ACTIVITY_TICKET_MAX_AGE_ENV: &str = "DISCORD_ACTIVITY_TICKET_MAX_AGE_SECS";

/// The default ticket freshness window: **8 h** — a deliberate bearer-window choice (see
/// [`DISCORD_ACTIVITY_TICKET_MAX_AGE_ENV`]). Deliberately tighter than a full day so a captured
/// bearer is not valid for 24 h; covers any single session, and is env-overridable upward for
/// long-running kiosk deployments.
pub const DEFAULT_ACTIVITY_TICKET_MAX_AGE_SECS: u64 = 28_800;

/// The clock-skew guard: a `minted_at` more than this many seconds in the FUTURE is refused.
pub const FUTURE_SKEW_SECS: u64 = 300;

/// The env var tuning the `/da/token` outbound-exchange concurrency cap (see
/// [`DEFAULT_DA_TOKEN_CONCURRENCY`]).
pub const DA_TOKEN_CONCURRENCY_ENV: &str = "DA_TOKEN_MAX_CONCURRENCY";

/// The default cap on IN-FLIGHT `POST /da/token` OAuth exchanges. `/da/token` is the ONE
/// unauthenticated endpoint that makes an outbound Discord call per request, so an unbounded flood
/// amplifies into an outbound-request storm (and burns the OAuth rate budget). A small semaphore
/// bounds the simultaneous outbound calls; a request that cannot immediately acquire a permit is
/// refused a fast `429` instead of piling onto Discord.
pub const DEFAULT_DA_TOKEN_CONCURRENCY: usize = 8;

/// The `/da/token` concurrency cap from [`DA_TOKEN_CONCURRENCY_ENV`], else
/// [`DEFAULT_DA_TOKEN_CONCURRENCY`].
fn da_token_concurrency_from_env() -> usize {
    std::env::var(DA_TOKEN_CONCURRENCY_ENV)
        .ok()
        .and_then(|v| v.trim().parse::<usize>().ok())
        .filter(|n| *n > 0)
        .unwrap_or(DEFAULT_DA_TOKEN_CONCURRENCY)
}

// ─────────────────────────────────────────────────────────────────────────────
// The `/da/token` outbound-exchange RATE guard.
//
// The concurrency semaphore ([`DiscordActivityState::token_gate`]) bounds only how many exchanges
// run AT ONCE — a sequential stream of fast-failing bad codes (each releasing its permit on return)
// still sustains a continuous outbound POST to Discord's `oauth2/token`, throttling the app's shared
// OAuth client and self-DoS-ing every legitimate Activity open. A concurrency bound is not a RATE
// bound. This guard adds the missing RATE bound: a per-source + global token bucket charged BEFORE
// the outbound call, plus a negative cache that short-circuits a repeated already-rejected code with
// no outbound call at all.
// ─────────────────────────────────────────────────────────────────────────────

/// Tunable knobs for the `/da/token` outbound-exchange guard: the per-source and global token-bucket
/// rate caps (burst = bucket capacity, refill = sustained rate), the negative-code cache TTL, and the
/// per-source table bound. Defaults are sized so a legitimate Activity open (ONE exchange per session)
/// never trips them, while a sustained bad-code flood is capped at the refill rate.
#[derive(Debug, Clone, Copy)]
pub struct DaTokenGuardConfig {
    /// Per-source bucket capacity (the immediate burst one source may spend).
    pub per_source_burst: f64,
    /// Per-source sustained refill (tokens/second) once the burst is spent.
    pub per_source_refill_per_sec: f64,
    /// Global bucket capacity across ALL sources (the shared outbound OAuth budget).
    pub global_burst: f64,
    /// Global sustained refill (tokens/second) — the ceiling on the total outbound exchange rate.
    pub global_refill_per_sec: f64,
    /// How long a rejected code is remembered so a replay of it short-circuits (seconds).
    pub neg_cache_ttl_secs: u64,
    /// Cap on distinct tracked source buckets (memory bound; a full table fails a NEW source closed).
    pub max_sources: usize,
}

/// Env override for [`DaTokenGuardConfig`] fields (each optional; unset ⇒ the default below).
pub const DA_TOKEN_PER_SOURCE_BURST_ENV: &str = "DA_TOKEN_PER_SOURCE_BURST";
pub const DA_TOKEN_PER_SOURCE_REFILL_ENV: &str = "DA_TOKEN_PER_SOURCE_REFILL_PER_SEC";
pub const DA_TOKEN_GLOBAL_BURST_ENV: &str = "DA_TOKEN_GLOBAL_BURST";
pub const DA_TOKEN_GLOBAL_REFILL_ENV: &str = "DA_TOKEN_GLOBAL_REFILL_PER_SEC";
pub const DA_TOKEN_NEG_CACHE_TTL_ENV: &str = "DA_TOKEN_NEG_CACHE_TTL_SECS";

impl Default for DaTokenGuardConfig {
    fn default() -> Self {
        DaTokenGuardConfig {
            per_source_burst: 5.0,
            per_source_refill_per_sec: 1.0,
            global_burst: 30.0,
            global_refill_per_sec: 5.0,
            neg_cache_ttl_secs: 30,
            max_sources: 4096,
        }
    }
}

impl DaTokenGuardConfig {
    /// Read the guard config from env, falling back to [`Default`] per field. A non-parsing or
    /// non-positive value keeps the default (fail-safe: a typo never disables the guard).
    fn from_env() -> Self {
        fn env_pos_f64(name: &str, default: f64) -> f64 {
            std::env::var(name)
                .ok()
                .and_then(|v| v.trim().parse::<f64>().ok())
                .filter(|n| n.is_finite() && *n > 0.0)
                .unwrap_or(default)
        }
        let d = DaTokenGuardConfig::default();
        DaTokenGuardConfig {
            per_source_burst: env_pos_f64(DA_TOKEN_PER_SOURCE_BURST_ENV, d.per_source_burst),
            per_source_refill_per_sec: env_pos_f64(
                DA_TOKEN_PER_SOURCE_REFILL_ENV,
                d.per_source_refill_per_sec,
            ),
            global_burst: env_pos_f64(DA_TOKEN_GLOBAL_BURST_ENV, d.global_burst),
            global_refill_per_sec: env_pos_f64(DA_TOKEN_GLOBAL_REFILL_ENV, d.global_refill_per_sec),
            neg_cache_ttl_secs: std::env::var(DA_TOKEN_NEG_CACHE_TTL_ENV)
                .ok()
                .and_then(|v| v.trim().parse::<u64>().ok())
                .filter(|n| *n > 0)
                .unwrap_or(d.neg_cache_ttl_secs),
            max_sources: d.max_sources,
        }
    }
}

/// A monotonic-clock token bucket: `capacity` tokens, refilled at `refill_per_sec`. A `refill_per_sec`
/// of `0.0` yields a fixed budget of `capacity` (no replenishment) — the deterministic shape the
/// rate canary drives.
struct TokenBucket {
    capacity: f64,
    refill_per_sec: f64,
    tokens: f64,
    last: Instant,
}

impl TokenBucket {
    fn new(capacity: f64, refill_per_sec: f64) -> Self {
        TokenBucket {
            capacity,
            refill_per_sec,
            tokens: capacity,
            last: Instant::now(),
        }
    }

    /// Replenish for the time elapsed since the last touch (monotonic; a non-advancing clock is a
    /// no-op).
    fn refill(&mut self, now: Instant) {
        let elapsed = now.saturating_duration_since(self.last).as_secs_f64();
        if elapsed > 0.0 {
            self.tokens = (self.tokens + elapsed * self.refill_per_sec).min(self.capacity);
            self.last = now;
        }
    }

    /// Take one token at `now`; `true` iff one was available (after refill).
    fn try_take(&mut self, now: Instant) -> bool {
        self.refill(now);
        if self.tokens >= 1.0 {
            self.tokens -= 1.0;
            true
        } else {
            false
        }
    }

    /// A fully-replenished bucket carries no outstanding rate debt — dropping it and recreating it
    /// yields an identical full bucket, so it is safe to evict for memory bounding.
    fn is_full(&self) -> bool {
        self.tokens >= self.capacity
    }
}

/// The per-source + global token-bucket RATE limiter charged once BEFORE each outbound exchange.
/// Per-source is checked FIRST so an over-budget source never drains the shared global budget from
/// everyone else; global is the ceiling on the total outbound OAuth rate (the self-DoS guard).
struct TokenRateLimiter {
    config: DaTokenGuardConfig,
    global: Mutex<TokenBucket>,
    sources: Mutex<HashMap<String, TokenBucket>>,
}

impl TokenRateLimiter {
    fn new(config: DaTokenGuardConfig) -> Self {
        TokenRateLimiter {
            global: Mutex::new(TokenBucket::new(
                config.global_burst,
                config.global_refill_per_sec,
            )),
            sources: Mutex::new(HashMap::new()),
            config,
        }
    }

    /// Charge one outbound-exchange token for `source` at `now`. `None` ⇒ allowed; `Some(reason)` ⇒
    /// denied (the audit reason). Per-source table growth is bounded: when full, fully-refilled
    /// buckets are evicted first (lossless), and if still full a NEW source is failed closed so a
    /// flood of fresh keys can neither exhaust memory NOR win a free burst by table churn.
    fn check(&self, source: &str, now: Instant) -> Option<&'static str> {
        {
            let mut map = self.sources.lock().unwrap();
            if !map.contains_key(source) && map.len() >= self.config.max_sources {
                map.retain(|_, b| {
                    b.refill(now);
                    !b.is_full()
                });
                if map.len() >= self.config.max_sources {
                    return Some("rate_source_table_saturated");
                }
            }
            let bucket = map.entry(source.to_string()).or_insert_with(|| {
                TokenBucket::new(
                    self.config.per_source_burst,
                    self.config.per_source_refill_per_sec,
                )
            });
            if !bucket.try_take(now) {
                return Some("rate_limited_source");
            }
        }
        if !self.global.lock().unwrap().try_take(now) {
            return Some("rate_limited_global");
        }
        None
    }
}

/// A bounded, TTL'd cache of codes Discord has already REJECTED, so a client replaying the same bad
/// code short-circuits to a fast refusal with NO outbound call. Only Discord-rejected codes are
/// cached (never a transport failure — that is OUR connectivity, not a bad code).
struct NegativeCodeCache {
    ttl: Duration,
    max: usize,
    inner: Mutex<HashMap<String, Instant>>,
}

impl NegativeCodeCache {
    fn new(ttl_secs: u64, max: usize) -> Self {
        NegativeCodeCache {
            ttl: Duration::from_secs(ttl_secs),
            max,
            inner: Mutex::new(HashMap::new()),
        }
    }

    /// Is `code` a still-valid rejected entry at `now`? Expired entries are dropped as they are seen.
    fn contains(&self, code: &str, now: Instant) -> bool {
        let mut m = self.inner.lock().unwrap();
        match m.get(code) {
            Some(&exp) if exp > now => true,
            Some(_) => {
                m.remove(code);
                false
            }
            None => false,
        }
    }

    /// Remember `code` as rejected until `now + ttl`. Bounded: when full, expired entries are pruned
    /// first; if still full the insert is skipped (a full cache only weakens the short-circuit — the
    /// RATE limiter is the load-bearing bound, never this cache).
    fn insert(&self, code: String, now: Instant) {
        let mut m = self.inner.lock().unwrap();
        if m.len() >= self.max {
            m.retain(|_, &mut exp| exp > now);
            if m.len() >= self.max {
                return;
            }
        }
        m.insert(code, now + self.ttl);
    }
}

/// The request's rate-limiting source key: the leftmost `X-Forwarded-For` hop (the original client
/// as set by the trusted gateway), else `X-Real-IP`, else a shared `"unknown"` bucket (still under
/// the global cap). Best-effort — the GLOBAL bucket, not this key, is the hard outbound ceiling.
fn source_key(headers: &HeaderMap) -> String {
    fn first_hop(v: &str) -> &str {
        v.split(',').next().unwrap_or(v).trim()
    }
    headers
        .get("x-forwarded-for")
        .and_then(|v| v.to_str().ok())
        .map(first_hop)
        .filter(|s| !s.is_empty())
        .or_else(|| {
            headers
                .get("x-real-ip")
                .and_then(|v| v.to_str().ok())
                .map(str::trim)
                .filter(|s| !s.is_empty())
        })
        .unwrap_or("unknown")
        .to_string()
}

/// The minimum decoded ticket length: `uid(8) ‖ minted_at(8) ‖ HMAC(32)` — a nonce of length ≥ 0
/// sits between `minted_at` and the HMAC. Anything shorter cannot carry the fixed fields.
const MIN_TICKET_LEN: usize = 8 + 8 + 32;

// ─────────────────────────────────────────────────────────────────────────────
// The verified user + the refusal taxonomy (the `VerifiedTelegramUser` / `InitDataError` twins).
// ─────────────────────────────────────────────────────────────────────────────

/// **A cryptographically verified Discord user** — the ONLY product of a passed ticket validation,
/// and the only trusted Discord identity on the `/da/*` surface.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VerifiedDiscordUser {
    /// The verified Discord uid (the snowflake the `/da/token` OAuth exchange proved and sealed
    /// into the ticket). The input to [`seed_for`](dreggnet_discord_identity::seed_for).
    pub user_id: u64,
    /// The unix-seconds timestamp the ticket was minted at — what freshness was judged on (and the
    /// value logged alongside the uid; the raw ticket never is).
    pub minted_at: u64,
}

/// Why a ticket was REFUSED — each variant one fail-closed gate of [`validate_ticket_at`], named so
/// an audit sees which gate bit. [`http_status`](TicketError::http_status) maps each to the
/// design's refusal statuses (the `InitDataError` taxonomy, ticket-shaped).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TicketError {
    /// No ticket reached the server at all (`401` — the extractor's variant, produced by the future
    /// header extractor exactly as `InitDataError::Missing` is, never by [`validate_ticket_at`]).
    Missing,
    /// The ticket string is not decodable base64url (`400`).
    MalformedEncoding,
    /// The decoded bytes are too short to carry `uid ‖ minted_at ‖ HMAC` (`400`), refused before
    /// any comparison.
    MalformedLength,
    /// The HMAC over `uid ‖ minted_at ‖ nonce` did not match the sealed tag — forged or tampered
    /// (this is the gate a client-invented uid dies at) (`403`).
    BadHmac,
    /// The ticket is older than the freshness window (`403`).
    Stale {
        /// How old the ticket is (seconds).
        age_secs: u64,
        /// The window it exceeded.
        max_age_secs: u64,
    },
    /// The `minted_at` is further in the future than the skew guard allows (`403`).
    FromFuture {
        /// How far ahead of the server clock (seconds).
        ahead_secs: u64,
    },
}

impl TicketError {
    /// The design's refusal statuses: missing → `401`; malformed shapes → `400`; a refused HMAC /
    /// freshness gate → `403`.
    pub fn http_status(&self) -> StatusCode {
        match self {
            TicketError::Missing => StatusCode::UNAUTHORIZED,
            TicketError::BadHmac | TicketError::Stale { .. } | TicketError::FromFuture { .. } => {
                StatusCode::FORBIDDEN
            }
            TicketError::MalformedEncoding | TicketError::MalformedLength => {
                StatusCode::BAD_REQUEST
            }
        }
    }
}

impl std::fmt::Display for TicketError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TicketError::Missing => write!(f, "no activity ticket presented"),
            TicketError::MalformedEncoding => write!(f, "ticket is not decodable base64url"),
            TicketError::MalformedLength => {
                write!(f, "ticket is too short to carry uid ‖ minted_at ‖ HMAC")
            }
            TicketError::BadHmac => write!(f, "ticket HMAC did not verify (forged or tampered)"),
            TicketError::Stale {
                age_secs,
                max_age_secs,
            } => write!(
                f,
                "ticket is stale: {age_secs}s old, window {max_age_secs}s"
            ),
            TicketError::FromFuture { ahead_secs } => {
                write!(
                    f,
                    "ticket minted_at is {ahead_secs}s in the future (skew guard 300s)"
                )
            }
        }
    }
}

impl std::error::Error for TicketError {}

// ─────────────────────────────────────────────────────────────────────────────
// The HMAC primitive + the ticket key.
// ─────────────────────────────────────────────────────────────────────────────

type HmacSha256 = Hmac<Sha256>;

/// `HMAC_SHA256(key, msg)` → the 32-byte tag (HMAC accepts any key length).
fn hmac_sha256(key: &[u8], msg: &[u8]) -> [u8; 32] {
    let mut mac = HmacSha256::new_from_slice(key).expect("HMAC accepts any key length");
    mac.update(msg);
    mac.finalize().into_bytes().into()
}

/// **The ticket HMAC key for a bot secret** — `BLAKE3_derive_key("dregg-discord-activity-ticket-v1",
/// BOT_SECRET)` (see [`ACTIVITY_TICKET_KEY_DOMAIN`]). Precomputed once at mount (the future
/// `DiscordActivityState::new`); domain-separated so it is not the custodial signing key.
pub fn ticket_key(bot_secret: &[u8; 32]) -> [u8; 32] {
    blake3::derive_key(ACTIVITY_TICKET_KEY_DOMAIN, bot_secret)
}

// ─────────────────────────────────────────────────────────────────────────────
// Mint + validate — the trust root (design §2, pinned).
// ─────────────────────────────────────────────────────────────────────────────

/// **Mint an activity ticket** for a VERIFIED uid, minted at `minted_at`, with the supplied
/// `nonce`: `base64url( uid_le ‖ minted_at_le ‖ nonce ‖ HMAC_SHA256(ticket_key, uid_le ‖
/// minted_at_le ‖ nonce) )`. Called once per verified session at `/da/token`, after the OAuth code
/// exchange proves the uid; the caller supplies a fresh random `nonce` (uniqueness is advisory — the
/// HMAC + freshness window are the security properties, exactly as with initData).
pub fn mint_ticket(ticket_key: &[u8; 32], uid: u64, minted_at: u64, nonce: &[u8]) -> String {
    let mut payload = Vec::with_capacity(16 + nonce.len());
    payload.extend_from_slice(&uid.to_le_bytes());
    payload.extend_from_slice(&minted_at.to_le_bytes());
    payload.extend_from_slice(nonce);
    let mac = hmac_sha256(ticket_key, &payload);
    let mut bytes = payload;
    bytes.extend_from_slice(&mac);
    URL_SAFE_NO_PAD.encode(bytes)
}

/// **Validate a ticket — the pure core** (no I/O, no clock: the caller injects `now` and the
/// freshness window). The pinned algorithm, in gate order (the [`validate_init_data_at`
/// ](crate::telegram_miniapp::validate_init_data_at) shape, ticket-encoded):
///
/// 1. base64url-decode → [`TicketError::MalformedEncoding`] (`400`);
/// 2. length: the decoded bytes must carry `uid(8) ‖ minted_at(8) ‖ HMAC(32)` →
///    [`TicketError::MalformedLength`] (`400`), refused before any comparison;
/// 3. `expected = HMAC_SHA256(ticket_key, decoded[..len-32])`; constant-time compare against the
///    sealed 32-byte tail (`subtle::ConstantTimeEq`) → [`TicketError::BadHmac`] (`403`) — the gate a
///    client-invented uid dies at;
/// 4. freshness: `now - minted_at > max_age` → [`TicketError::Stale`]; `minted_at > now + 300` →
///    [`TicketError::FromFuture`] (`403`);
/// 5. only now read the uid (`decoded[..8]` as little-endian `u64`) — the verified identity.
pub fn validate_ticket_at(
    ticket_key: &[u8; 32],
    ticket: &str,
    now_unix: u64,
    max_age_secs: u64,
) -> Result<VerifiedDiscordUser, TicketError> {
    // 1. base64url decode (URL-safe, no padding — the mint encoding).
    let decoded = URL_SAFE_NO_PAD
        .decode(ticket.as_bytes())
        .map_err(|_| TicketError::MalformedEncoding)?;

    // 2. Length: enough for the fixed fields + the sealed HMAC (a nonce of length ≥ 0 between).
    if decoded.len() < MIN_TICKET_LEN {
        return Err(TicketError::MalformedLength);
    }
    let split = decoded.len() - 32;

    // 3. The HMAC gate, constant-time over the two 32-byte tags. The tag seals `uid ‖ minted_at ‖
    //    nonce` (everything before it), so ANY tamper — a swapped uid, a mangled nonce — refuses.
    let sealed: [u8; 32] = decoded[split..]
        .try_into()
        .expect("the tail is exactly 32 bytes");
    let expected = hmac_sha256(ticket_key, &decoded[..split]);
    if !bool::from(expected.ct_eq(&sealed)) {
        return Err(TicketError::BadHmac);
    }

    // 4. Freshness — the ticket is genuine; is it current? (`minted_at` is 8 fixed bytes from a
    //    length-checked buffer, so the decode is infallible; no malformed-timestamp gate exists.)
    let minted_at = u64::from_le_bytes(decoded[8..16].try_into().expect("8 bytes"));
    if minted_at > now_unix {
        let ahead = minted_at - now_unix;
        if ahead > FUTURE_SKEW_SECS {
            return Err(TicketError::FromFuture { ahead_secs: ahead });
        }
    } else {
        let age = now_unix - minted_at;
        if age > max_age_secs {
            return Err(TicketError::Stale {
                age_secs: age,
                max_age_secs,
            });
        }
    }

    // 5. Only after ALL gates: read the verified uid.
    let user_id = u64::from_le_bytes(decoded[0..8].try_into().expect("8 bytes"));
    Ok(VerifiedDiscordUser { user_id, minted_at })
}

/// [`validate_ticket_at`] against the system clock, with the freshness window from
/// `DISCORD_ACTIVITY_TICKET_MAX_AGE_SECS` (default 24 h) — the one-call convenience form the future
/// `/da/*` handlers use (the ticket key is precomputed once at mount).
pub fn validate_ticket(
    ticket_key: &[u8; 32],
    ticket: &str,
) -> Result<VerifiedDiscordUser, TicketError> {
    validate_ticket_at(ticket_key, ticket, unix_now(), max_age_from_env())
}

/// The freshness window: `DISCORD_ACTIVITY_TICKET_MAX_AGE_SECS` if set and parsable, else 24 h.
pub fn max_age_from_env() -> u64 {
    std::env::var(DISCORD_ACTIVITY_TICKET_MAX_AGE_ENV)
        .ok()
        .and_then(|v| v.trim().parse().ok())
        .unwrap_or(DEFAULT_ACTIVITY_TICKET_MAX_AGE_SECS)
}

fn unix_now() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0)
}

// ─────────────────────────────────────────────────────────────────────────────
// The OAuth code exchange — `POST /da/token`'s trust step (design §1). Structured behind a trait
// so the module COMPILES + the mint/response/parse structure is TESTABLE with no live Discord app
// or secret: the real backend ([`HttpDiscordOAuth`]) does the two HTTP round-trips; a test injects a
// stub. The server's trust root is its OWN exchange — the uid is asserted by Discord's API to the
// holder of our `client_secret`, NEVER by the client (the confused-deputy class is structurally
// avoided: no client-presented token is ever trusted here).
// ─────────────────────────────────────────────────────────────────────────────

/// Discord's OAuth2 token endpoint — the `code` → `access_token` exchange (form-urlencoded body,
/// `client_secret` in the body per Discord's Activity sample).
pub const DISCORD_TOKEN_URL: &str = "https://discord.com/api/oauth2/token";

/// Discord's current-user endpoint — `GET` with `Authorization: Bearer <access_token>` returns the
/// VERIFIED uid (`id`, a snowflake STRING). This round-trip, not the client, is the identity oracle.
pub const DISCORD_USER_URL: &str = "https://discord.com/api/users/@me";

/// **The verified product of a `/da/token` OAuth exchange** — the uid Discord's API asserted to the
/// holder of our `client_secret`, plus the `access_token` (handed back to the client so it can
/// complete the SDK handshake with `authenticate`; display-only for us) and the display username.
#[derive(Debug, Clone)]
pub struct DiscordCodeExchange {
    /// The VERIFIED Discord uid — the input to [`seed_for`] and the value sealed into the ticket.
    pub user_id: u64,
    /// The OAuth access token (returned to the client; never an identity input server-side).
    pub access_token: String,
    /// The username, if Discord returned one (display-only convenience).
    pub username: Option<String>,
}

/// Why a `/da/token` OAuth exchange failed — each variant an honest, fail-closed refusal.
#[derive(Debug, Clone)]
pub enum OAuthError {
    /// A network / HTTP-layer failure reaching Discord (timeout, DNS, TLS) — upstream, `502`.
    Transport(String),
    /// `oauth2/token` returned non-2xx — the `code` was invalid/expired (or our credentials are
    /// wrong). Surfaced as `401` so the client re-authorizes.
    TokenStatus(u16),
    /// The token response carried no `access_token` string — upstream shape drift, `502`.
    TokenParse,
    /// `users/@me` returned non-2xx (a revoked/again-expired token) — upstream, `502`.
    UserStatus(u16),
    /// `users/@me` carried no u64-parseable `id` — upstream shape drift, `502`.
    UserParse,
}

impl OAuthError {
    /// A bad `code` → `401` (re-authorize); everything else is an upstream/us failure → `502`.
    pub fn http_status(&self) -> StatusCode {
        match self {
            OAuthError::TokenStatus(_) => StatusCode::UNAUTHORIZED,
            OAuthError::Transport(_)
            | OAuthError::TokenParse
            | OAuthError::UserStatus(_)
            | OAuthError::UserParse => StatusCode::BAD_GATEWAY,
        }
    }

    /// Did Discord authoritatively reject the `code` ITSELF (invalid/expired at `oauth2/token`)?
    /// Only this is monotonic ("a bad code stays bad") and safe to negative-cache — the other
    /// variants are our transport, upstream shape drift, or a POST-token failure where the code was
    /// actually accepted, none of which a code replay should short-circuit.
    fn is_bad_code(&self) -> bool {
        matches!(self, OAuthError::TokenStatus(_))
    }

    /// The machine reason for the audit trail — `oauth:<gate>`.
    fn reason(&self) -> &'static str {
        match self {
            OAuthError::Transport(_) => "oauth:transport",
            OAuthError::TokenStatus(_) => "oauth:token_status",
            OAuthError::TokenParse => "oauth:token_parse",
            OAuthError::UserStatus(_) => "oauth:user_status",
            OAuthError::UserParse => "oauth:user_parse",
        }
    }
}

impl std::fmt::Display for OAuthError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OAuthError::Transport(e) => write!(f, "could not reach Discord: {e}"),
            OAuthError::TokenStatus(s) => {
                write!(f, "oauth2/token returned HTTP {s} (bad or expired code)")
            }
            OAuthError::TokenParse => write!(f, "oauth2/token response carried no access_token"),
            OAuthError::UserStatus(s) => write!(f, "users/@me returned HTTP {s}"),
            OAuthError::UserParse => write!(f, "users/@me carried no u64 id"),
        }
    }
}

impl std::error::Error for OAuthError {}

/// **The code-exchange backend** — the seam that lets the whole `/da/token` path (mint + response
/// shape + parse) be exercised with NO live Discord. The default backend is [`HttpDiscordOAuth`]
/// (two real HTTP round-trips); tests inject a stub returning a fixed uid. `client_id` /
/// `client_secret` are passed per call from [`DiscordActivityState`] (the secret lives on the state,
/// not duplicated in the backend).
pub trait DiscordTokenExchange: Send + Sync {
    /// Exchange an OAuth `code` for a VERIFIED [`DiscordCodeExchange`] (the two-step
    /// `oauth2/token` → `users/@me` flow), or an honest [`OAuthError`]. Blocking (run off the async
    /// reactor via [`tokio::task::spawn_blocking`]).
    fn exchange(
        &self,
        client_id: &str,
        client_secret: &str,
        code: &str,
    ) -> Result<DiscordCodeExchange, OAuthError>;
}

/// **The real OAuth backend** — the ONE outbound HTTP call-site in `dreggnet-web`. Uses the
/// `reqwest::blocking` client `dregg-node-target`'s `http` feature already compiles (no new heavy
/// dep), driven off the async reactor by the caller's [`tokio::task::spawn_blocking`].
pub struct HttpDiscordOAuth {
    http: reqwest::blocking::Client,
}

impl HttpDiscordOAuth {
    /// Build the backend with a bounded timeout (a hung Discord edge never wedges a `/da/token`
    /// worker).
    pub fn new() -> Self {
        let http = reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(10))
            .user_agent("dreggnet-web/0.1 (+https://dregg.net)")
            .build()
            .expect("reqwest blocking client builds with a static config");
        HttpDiscordOAuth { http }
    }
}

impl Default for HttpDiscordOAuth {
    fn default() -> Self {
        Self::new()
    }
}

impl DiscordTokenExchange for HttpDiscordOAuth {
    fn exchange(
        &self,
        client_id: &str,
        client_secret: &str,
        code: &str,
    ) -> Result<DiscordCodeExchange, OAuthError> {
        // 1. Exchange the code for an access token — `client_secret` in the form body (Discord's
        //    Activity sample shape); NO redirect_uri (the Embedded App SDK's authorize flow).
        let token_resp = self
            .http
            .post(DISCORD_TOKEN_URL)
            .form(&[
                ("client_id", client_id),
                ("client_secret", client_secret),
                ("grant_type", "authorization_code"),
                ("code", code),
            ])
            .send()
            .map_err(|e| OAuthError::Transport(e.to_string()))?;
        let status = token_resp.status();
        let body = token_resp
            .text()
            .map_err(|e| OAuthError::Transport(e.to_string()))?;
        if !status.is_success() {
            return Err(OAuthError::TokenStatus(status.as_u16()));
        }
        let access_token = parse_access_token(&body).ok_or(OAuthError::TokenParse)?;

        // 2. Read the VERIFIED uid from Discord's own API with the freshly minted token.
        let user_resp = self
            .http
            .get(DISCORD_USER_URL)
            .bearer_auth(&access_token)
            .send()
            .map_err(|e| OAuthError::Transport(e.to_string()))?;
        let ustatus = user_resp.status();
        let ubody = user_resp
            .text()
            .map_err(|e| OAuthError::Transport(e.to_string()))?;
        if !ustatus.is_success() {
            return Err(OAuthError::UserStatus(ustatus.as_u16()));
        }
        let (user_id, username) = parse_user_me(&ubody).ok_or(OAuthError::UserParse)?;
        Ok(DiscordCodeExchange {
            user_id,
            access_token,
            username,
        })
    }
}

/// Parse an `access_token` out of a Discord `oauth2/token` JSON response — the parse step that needs
/// NO live Discord (pinned by a fixture-JSON unit test).
pub fn parse_access_token(json: &str) -> Option<String> {
    serde_json::from_str::<serde_json::Value>(json)
        .ok()?
        .get("access_token")?
        .as_str()
        .map(str::to_string)
}

/// Parse `(uid, username?)` out of a Discord `users/@me` JSON response. Discord ids are snowflake
/// **strings**, so the `id` is parsed from a string field — the exact shape a fixture pins.
pub fn parse_user_me(json: &str) -> Option<(u64, Option<String>)> {
    let v: serde_json::Value = serde_json::from_str(json).ok()?;
    let user_id = v.get("id")?.as_str()?.parse::<u64>().ok()?;
    let username = v
        .get("username")
        .and_then(|x| x.as_str())
        .map(str::to_string);
    Some((user_id, username))
}

/// Discord's token-introspection endpoint — `GET /oauth2/@me` with `Authorization: Bearer <token>`
/// returns `{ application: { id, ... }, scopes, expires, user }`. The `application.id` is the app the
/// token was minted FOR — the audience.
pub const DISCORD_OAUTH_ME_URL: &str = "https://discord.com/api/oauth2/@me";

/// Parse the `application.id` (the AUDIENCE — the app a token was minted for) out of a Discord
/// `GET /oauth2/@me` JSON response. Discord ids are snowflake **strings**. `None` on shape drift.
pub fn oauth_me_application_id(json: &str) -> Option<String> {
    serde_json::from_str::<serde_json::Value>(json)
        .ok()?
        .get("application")?
        .get("id")?
        .as_str()
        .map(str::to_string)
}

/// **The audience-trap guard** (design §1, §9) — `true` iff a Discord `/oauth2/@me` introspection
/// response names OUR application as the token's audience (`application.id == our_client_id`).
///
/// The `/da/token` MAIN path never needs this: it exchanges the `code` with our OWN `client_secret`,
/// so every token it holds was minted for us by construction — the confused-deputy class is avoided
/// STRUCTURALLY, and no client-*presented* token is ever trusted on `/da/*`. This guard is the
/// MANDATORY check the design pins for any FUTURE client-presented-token path: an attacker who got a
/// victim to authorize a *different* app could otherwise replay that foreign token here. Kept a pure,
/// tested function so the check is real code (not a doc-comment promise) the day such a path is added.
pub fn token_audience_ok(oauth_me_json: &str, our_client_id: &str) -> bool {
    matches!(
        oauth_me_application_id(oauth_me_json),
        Some(app_id) if app_id == our_client_id
    )
}

/// A per-mint ticket nonce. Uniqueness is ADVISORY (design §2: the HMAC + freshness window are the
/// security properties), so this needs no CSPRNG — a process-lifetime counter mixed with the
/// wall-clock nanos + the uid, hashed to 16 bytes, makes two same-second tickets for one user
/// differ. Dependency-free (blake3 is already pulled in); the ticket's security never rests on it.
fn fresh_nonce(uid: u64, minted_at: u64) -> [u8; 16] {
    static NONCE_COUNTER: AtomicU64 = AtomicU64::new(0);
    let n = NONCE_COUNTER.fetch_add(1, Ordering::Relaxed);
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.subsec_nanos())
        .unwrap_or(0);
    let mut h = blake3::Hasher::new();
    h.update(&uid.to_le_bytes());
    h.update(&minted_at.to_le_bytes());
    h.update(&n.to_le_bytes());
    h.update(&(nanos as u64).to_le_bytes());
    let mut out = [0u8; 16];
    out.copy_from_slice(&h.finalize().as_bytes()[..16]);
    out
}

// ─────────────────────────────────────────────────────────────────────────────
// The router + state (design §4) — the `TgMiniAppState` / `tg_miniapp_router` analogs.
// ─────────────────────────────────────────────────────────────────────────────

/// The env vars this surface is gated on (all three must be set to mount — design §3 ops coupling).
pub const DISCORD_CLIENT_ID_ENV: &str = "DISCORD_CLIENT_ID";
/// See [`DISCORD_CLIENT_ID_ENV`].
pub const DISCORD_CLIENT_SECRET_ENV: &str = "DISCORD_CLIENT_SECRET";
/// The identity master secret — the SAME `BOT_SECRET` (64 hex chars) the in-chat bot reads
/// (`discord-bot/src/config.rs`); a fork here forks every user into two identities.
pub const BOT_SECRET_ENV: &str = "BOT_SECRET";

/// **The Discord Activity surface's axum state** — the `TgMiniAppState` analog. Holds the shared
/// catalog host, the OAuth credential (`client_id` + `client_secret`), the identity `bot_secret`,
/// the precomputed `ticket_key`, the freshness window, and the code-exchange backend (default
/// [`HttpDiscordOAuth`]; a stub in tests). One registry, three trust stories, never one handler.
pub struct DiscordActivityState {
    /// The SAME catalog host the cookie-identity + `/tg` routes drive.
    catalog: Arc<CatalogState>,
    /// The Discord application id — sent to the client (the shell constructs `new DiscordSDK(id)`).
    client_id: String,
    /// The OAuth client secret — the ONLY thing that makes Discord assert a uid to US (never sent
    /// to the client; zeroized on drop).
    client_secret: Zeroizing<String>,
    /// The 32-byte identity master secret [`seed_for`] derives per-uid Ed25519 seeds from.
    bot_secret: [u8; 32],
    /// `ticket_key(bot_secret)` — precomputed once at mount (domain-separated from the signing seed).
    ticket_key: [u8; 32],
    /// The ticket freshness window (seconds).
    max_age_secs: u64,
    /// The code-exchange backend — the seam that keeps `/da/token` testable without live Discord.
    oauth: Arc<dyn DiscordTokenExchange>,
    /// Single-use cache for spent link-ceremony challenge nonces — a `POST /da/link` challenge is
    /// consumed on success so a captured claim can't be replayed within its TTL (the `/tg/link`
    /// posture; internally synced).
    link_replay: webauth_core::replay::NonceCache,
    /// Bounds concurrent `POST /da/token` OAuth exchanges — the one unauthenticated endpoint that
    /// makes an outbound Discord call per request. A request that cannot immediately acquire a
    /// permit is refused `429` (see [`post_da_token`]). Concurrency ONLY — the RATE bound is
    /// [`token_rate`](Self::token_rate).
    token_gate: Arc<tokio::sync::Semaphore>,
    /// Bounds the outbound-exchange RATE (per-source + global token bucket), charged BEFORE the
    /// outbound call. The semaphore caps simultaneous exchanges; a sequential bad-code stream slips
    /// past it (each permit released on return) — this bucket is what caps that stream.
    token_rate: TokenRateLimiter,
    /// Short-circuits a replayed already-rejected code with no outbound call (see
    /// [`NegativeCodeCache`]).
    neg_code_cache: NegativeCodeCache,
}

impl DiscordActivityState {
    /// Assemble the state over a shared catalog with the real [`HttpDiscordOAuth`] backend.
    pub fn new(
        catalog: Arc<CatalogState>,
        client_id: impl Into<String>,
        client_secret: impl Into<String>,
        bot_secret: [u8; 32],
        max_age_secs: u64,
    ) -> Self {
        Self::with_oauth(
            catalog,
            client_id,
            client_secret,
            bot_secret,
            max_age_secs,
            Arc::new(HttpDiscordOAuth::new()),
        )
    }

    /// Assemble the state with an INJECTED code-exchange backend — the ctor tests use to drive the
    /// whole `/da/token` + ticket-gated catalog flow with a stub (no live Discord app or secret). The
    /// outbound-exchange guard is read from env ([`DaTokenGuardConfig::from_env`]).
    pub fn with_oauth(
        catalog: Arc<CatalogState>,
        client_id: impl Into<String>,
        client_secret: impl Into<String>,
        bot_secret: [u8; 32],
        max_age_secs: u64,
        oauth: Arc<dyn DiscordTokenExchange>,
    ) -> Self {
        Self::with_oauth_and_guard(
            catalog,
            client_id,
            client_secret,
            bot_secret,
            max_age_secs,
            oauth,
            DaTokenGuardConfig::from_env(),
        )
    }

    /// As [`with_oauth`](Self::with_oauth), but with an EXPLICIT outbound-exchange guard config — the
    /// seam the rate/negative-cache canaries use to drive the token bucket deterministically (a tiny
    /// burst, zero refill) instead of the env/production defaults.
    pub fn with_oauth_and_guard(
        catalog: Arc<CatalogState>,
        client_id: impl Into<String>,
        client_secret: impl Into<String>,
        bot_secret: [u8; 32],
        max_age_secs: u64,
        oauth: Arc<dyn DiscordTokenExchange>,
        guard: DaTokenGuardConfig,
    ) -> Self {
        DiscordActivityState {
            catalog,
            client_id: client_id.into(),
            client_secret: Zeroizing::new(client_secret.into()),
            bot_secret,
            ticket_key: ticket_key(&bot_secret),
            max_age_secs,
            oauth,
            link_replay: webauth_core::replay::NonceCache::new(true, 8192),
            token_gate: Arc::new(tokio::sync::Semaphore::new(da_token_concurrency_from_env())),
            neg_code_cache: NegativeCodeCache::new(guard.neg_cache_ttl_secs, 8192),
            token_rate: TokenRateLimiter::new(guard),
        }
    }

    /// The verified viewer's dregg identity — the bot's OWN derivation ([`seed_for`], CALLED not
    /// mirrored): the Activity player IS the in-chat player. The transient seed is wiped after use.
    fn identity_for(&self, uid: u64) -> DreggIdentity {
        let seed = Zeroizing::new(seed_for(&self.bot_secret, uid));
        TurnSigner::from_seed(*seed).identity()
    }
}

/// **Build the `/da` Activity router** over a shared [`DiscordActivityState`]. Additive beside the
/// catalog + `/tg` routers; mounted by [`discord_activity_from_env`] when the creds are present.
pub fn discord_activity_router(state: Arc<DiscordActivityState>) -> Router {
    let router = Router::new()
        .route("/da", get(get_da_shell))
        .route("/da/token", post(post_da_token))
        .route("/da/static/discord-sdk.js", get(get_da_sdk_js))
        .route("/da/static/app.js", get(get_da_app_js))
        .route("/da/offerings", get(get_da_offerings))
        .route("/da/offerings/{key}/session/{id}", get(get_da_session))
        .route(
            "/da/offerings/{key}/session/{id}/verify",
            get(get_da_verify),
        )
        .route("/da/offerings/{key}/session/{id}/act", post(post_da_act))
        // The cross-platform LINK ceremony (design §5) — the `/tg/link` twin, `platform="discord"`,
        // recording into the SAME shared `links.tsv` so a link made in the Activity resolves on
        // Telegram (and vice versa). Vendored noble is served same-origin under `/da/static`.
        .route("/da/link/challenge", get(get_da_link_challenge))
        .route("/da/link", get(get_da_link_page).post(post_da_link))
        .route("/da/link/app.js", get(get_da_link_app_js))
        .route("/da/static/noble-ed25519.js", get(get_da_noble_ed25519));
    #[cfg(feature = "hosted-binary-operations")]
    let router = router
        .route(
            "/da/offerings/{key}/session/{id}/operations",
            get(get_da_operations),
        )
        .route(
            "/da/offerings/{key}/session/{id}/operations/{name}",
            post(post_da_operation),
        )
        .route(
            "/da/offerings/{key}/session/{id}/artifacts",
            get(get_da_artifacts),
        )
        .route(
            "/da/offerings/{key}/session/{id}/artifacts/{name}",
            get(get_da_artifact),
        );
    #[cfg(feature = "fhegg-settlement")]
    let router = router.route(
        "/da/operations/{name}",
        get(crate::fhegg_operation::get_descriptor),
    );
    router.with_state(state)
}

/// **Resolve the Activity router from the environment** — `Some(router)` iff `DISCORD_CLIENT_ID`,
/// `DISCORD_CLIENT_SECRET`, and `BOT_SECRET` (64 hex chars → the 32-byte identity secret, the SAME
/// value + parse the bot binary uses) are ALL set. `None` (with one log line) leaves the web catalog
/// + `/tg` surface serving exactly as before — the Activity surface is ops-gated, every existing
/// deployment untouched.
pub fn discord_activity_from_env(catalog: Arc<CatalogState>) -> Option<Router> {
    let client_id = non_empty_env(DISCORD_CLIENT_ID_ENV);
    let client_secret = non_empty_env(DISCORD_CLIENT_SECRET_ENV);
    let (Some(client_id), Some(client_secret)) = (client_id, client_secret) else {
        tracing::info!(
            "Discord Activity surface NOT mounted — {DISCORD_CLIENT_ID_ENV}/{DISCORD_CLIENT_SECRET_ENV} \
             unset (the web catalog serves unchanged)"
        );
        return None;
    };
    let bot_secret = match non_empty_env(BOT_SECRET_ENV).and_then(|s| bot_secret_from_hex(&s)) {
        Some(s) => s,
        None => {
            tracing::error!(
                "Discord Activity surface NOT mounted — {BOT_SECRET_ENV} unset or not 64 hex chars \
                 (the identity master secret did not resolve)"
            );
            return None;
        }
    };
    let max_age = max_age_from_env();
    tracing::info!(
        max_age_secs = max_age,
        "Discord Activity surface mounted at /da (ticket-verified identities; turns land with \
         Signed provenance under the SAME custodial key the in-chat bot derives)"
    );
    Some(discord_activity_router(Arc::new(
        DiscordActivityState::new(catalog, client_id, client_secret, bot_secret, max_age),
    )))
}

/// A non-empty trimmed env var, or `None`.
fn non_empty_env(key: &str) -> Option<String> {
    std::env::var(key).ok().filter(|v| !v.trim().is_empty())
}

/// Decode exactly 64 hex chars into the 32-byte `BOT_SECRET` — the SAME parse
/// `discord-bot/src/config.rs` applies (`hex::decode` → `[u8; 32]`), so the two processes resolve
/// byte-identical identity secrets. `None` on any other shape.
fn bot_secret_from_hex(s: &str) -> Option<[u8; 32]> {
    let bytes = s.trim().as_bytes();
    if bytes.len() != 64 {
        return None;
    }
    let mut out = [0u8; 32];
    for (i, chunk) in bytes.chunks_exact(2).enumerate() {
        out[i] = (hex_nib(chunk[0])? << 4) | hex_nib(chunk[1])?;
    }
    Some(out)
}

fn hex_nib(c: u8) -> Option<u8> {
    match c {
        b'0'..=b'9' => Some(c - b'0'),
        b'a'..=b'f' => Some(c - b'a' + 10),
        b'A'..=b'F' => Some(c - b'A' + 10),
        _ => None,
    }
}

/// Decode exactly 64 hex chars into 32 bytes (a root Ed25519 pubkey); `None` on any other shape.
fn decode_hex_32(s: &str) -> Option<[u8; 32]> {
    let bytes = s.trim().as_bytes();
    if bytes.len() != 64 {
        return None;
    }
    let mut out = [0u8; 32];
    for (i, chunk) in bytes.chunks_exact(2).enumerate() {
        out[i] = (hex_nib(chunk[0])? << 4) | hex_nib(chunk[1])?;
    }
    Some(out)
}

/// Decode exactly 128 hex chars into 64 bytes (an Ed25519 signature); `None` on any other shape.
fn decode_hex_64(s: &str) -> Option<[u8; 64]> {
    let bytes = s.trim().as_bytes();
    if bytes.len() != 128 {
        return None;
    }
    let mut out = [0u8; 64];
    for (i, chunk) in bytes.chunks_exact(2).enumerate() {
        out[i] = (hex_nib(chunk[0])? << 4) | hex_nib(chunk[1])?;
    }
    Some(out)
}

// ─────────────────────────────────────────────────────────────────────────────
// Handlers.
// ─────────────────────────────────────────────────────────────────────────────

/// The machine reason for a refused ticket gate — `ticket:<gate>` (each [`TicketError`] variant is
/// one named fail-closed gate).
fn ticket_reason(e: &TicketError) -> String {
    let gate = match e {
        TicketError::Missing => "missing",
        TicketError::MalformedEncoding => "malformed_encoding",
        TicketError::MalformedLength => "malformed_length",
        TicketError::BadHmac => "bad_hmac",
        TicketError::Stale { .. } => "stale",
        TicketError::FromFuture { .. } => "from_future",
    };
    format!("ticket:{gate}")
}

/// Validate the request's `X-Dregg-Activity-Ticket` header into a [`VerifiedDiscordUser`], or the
/// honest refusal response (`401` missing / `400` malformed / `403` refused). The raw ticket is
/// never logged — the verified uid + `minted_at` are. Both audit polarities land on `corr` (the
/// verified custodial identity on ACCEPT, the NAMED gate on REFUSE), mirroring `/tg`'s initData gate.
fn verified_user(
    state: &DiscordActivityState,
    headers: &HeaderMap,
    corr: &str,
    route: &str,
) -> Result<VerifiedDiscordUser, Response> {
    let refused_event = |e: &TicketError| {
        audit::AuditEvent::new(
            "discord-activity",
            audit::Actor::unattributed(),
            audit::Surface::Http,
            audit::Input::new(
                route,
                serde_json::json!({
                    "error": e.to_string(),
                    "status": e.http_status().as_u16(),
                }),
            ),
        )
        .correlated(corr)
        .decided("gated", ticket_reason(e))
    };
    let raw = match headers
        .get(ACTIVITY_TICKET_HEADER)
        .and_then(|v| v.to_str().ok())
    {
        Some(r) if !r.is_empty() => r,
        _ => {
            let e = TicketError::Missing;
            audit::log().emit(refused_event(&e));
            return Err((
                e.http_status(),
                format!("activity ticket refused: {e} — open this surface inside Discord"),
            )
                .into_response());
        }
    };
    match validate_ticket_at(&state.ticket_key, raw, unix_now(), state.max_age_secs) {
        Ok(u) => {
            let identity = state.identity_for(u.user_id);
            tracing::debug!(
                uid = u.user_id,
                minted_at = u.minted_at,
                "activity ticket verified"
            );
            audit::log().emit(
                audit::AuditEvent::new(
                    "discord-activity",
                    audit::Actor::custodial(u.user_id.to_string(), identity.0.clone()),
                    audit::Surface::Http,
                    audit::Input::new(route, serde_json::json!({ "minted_at": u.minted_at })),
                )
                .correlated(corr),
            );
            Ok(u)
        }
        Err(e) => {
            tracing::debug!(error = %e, "activity ticket refused");
            audit::log().emit(refused_event(&e));
            Err((e.http_status(), format!("activity ticket refused: {e}")).into_response())
        }
    }
}

/// The `{ code }` JSON body of `POST /da/token`.
#[derive(Debug, Clone, Deserialize)]
pub struct TokenRequest {
    /// The OAuth authorization code the client obtained from `sdk.commands.authorize(...)`.
    pub code: String,
}

/// `POST /da/token` — the OAuth exchange that mints the FIRST ticket (design §1). Runs the blocking
/// exchange off the async reactor, mints a ticket for the VERIFIED uid, and returns
/// `{ access_token, ticket, custodial_pubkey_hex }`. The uid derives the SAME custodial identity via
/// [`seed_for`] (called, never mirrored); the client never supplies an identity.
async fn post_da_token(
    State(state): State<Arc<DiscordActivityState>>,
    headers: HeaderMap,
    Json(req): Json<TokenRequest>,
) -> Response {
    let corr = audit::correlation_id();
    let route = "POST /da/token";
    let charged_at = Instant::now();
    let source = source_key(&headers);

    // NEGATIVE-CODE SHORT-CIRCUIT — a code Discord already REJECTED stays rejected; replaying it
    // costs NO outbound call and NO rate token (a fast, fail-closed refusal). This blunts a
    // same-code replay flood; the RATE bucket below blunts a distinct-code flood.
    if state.neg_code_cache.contains(&req.code, charged_at) {
        audit::log().emit(
            audit::AuditEvent::new(
                "discord-activity",
                audit::Actor::unattributed(),
                audit::Surface::Http,
                audit::Input::new(route, serde_json::json!({ "status": 401 })),
            )
            .correlated(&corr)
            .decided("gated", "oauth:cached_bad_code"),
        );
        return (
            StatusCode::UNAUTHORIZED,
            "token exchange refused: this code was already rejected — re-authorize for a fresh one",
        )
            .into_response();
    }

    // RATE LIMIT (the outbound self-DoS guard) — the concurrency semaphore below bounds only
    // SIMULTANEOUS exchanges; a sequential stream of fast-failing bad codes (each releasing its
    // permit on return) sustains a continuous outbound POST to Discord's token endpoint, throttling
    // the app's shared OAuth client. Charge a per-source + global token BEFORE the outbound call so
    // that stream is capped by RATE, not just concurrency; over-budget ⇒ a fast `429`.
    if let Some(reason) = state.token_rate.check(&source, charged_at) {
        audit::log().emit(
            audit::AuditEvent::new(
                "discord-activity",
                audit::Actor::unattributed(),
                audit::Surface::Http,
                audit::Input::new(route, serde_json::json!({ "status": 429 })),
            )
            .correlated(&corr)
            .decided("gated", reason),
        );
        return (
            StatusCode::TOO_MANY_REQUESTS,
            "token exchange rate limit — retry shortly",
        )
            .into_response();
    }

    // CONCURRENCY BOUND — cap simultaneous in-flight exchanges. The permit is held (via `_permit`)
    // until this handler returns, i.e. across the whole exchange; a request that cannot immediately
    // acquire one is refused `429` rather than piling another concurrent outbound call onto Discord.
    let _permit = match Arc::clone(&state.token_gate).try_acquire_owned() {
        Ok(p) => p,
        Err(_) => {
            audit::log().emit(
                audit::AuditEvent::new(
                    "discord-activity",
                    audit::Actor::unattributed(),
                    audit::Surface::Http,
                    audit::Input::new(route, serde_json::json!({ "status": 429 })),
                )
                .correlated(&corr)
                .decided("gated", "rate_limited"),
            );
            return (
                StatusCode::TOO_MANY_REQUESTS,
                "too many concurrent token exchanges — retry shortly",
            )
                .into_response();
        }
    };

    // The exchange is blocking (reqwest::blocking) — drive it off the async reactor.
    let oauth = Arc::clone(&state.oauth);
    let client_id = state.client_id.clone();
    let client_secret = state.client_secret.clone();
    let code = req.code.clone();
    let exchanged = tokio::task::spawn_blocking(move || {
        oauth.exchange(&client_id, client_secret.as_str(), &code)
    })
    .await;

    let verified = match exchanged {
        Ok(Ok(v)) => v,
        Ok(Err(e)) => {
            // Remember a Discord-rejected code so a replay of it short-circuits with no outbound
            // call (only `TokenStatus` — the monotonic "this code is invalid/expired"; never a
            // transport/shape-drift/post-token failure, where the code may be fine on retry).
            if e.is_bad_code() {
                state.neg_code_cache.insert(req.code.clone(), charged_at);
            }
            audit::log().emit(
                audit::AuditEvent::new(
                    "discord-activity",
                    audit::Actor::unattributed(),
                    audit::Surface::Http,
                    audit::Input::new(
                        route,
                        serde_json::json!({ "error": e.to_string(), "status": e.http_status().as_u16() }),
                    ),
                )
                .correlated(&corr)
                .decided("gated", e.reason()),
            );
            return (e.http_status(), format!("token exchange refused: {e}")).into_response();
        }
        Err(join) => {
            tracing::error!(error = %join, "the /da/token exchange task panicked");
            return (
                StatusCode::INTERNAL_SERVER_ERROR,
                "token exchange failed (server)",
            )
                .into_response();
        }
    };

    // Mint the ticket for the VERIFIED uid, and derive the custodial pubkey to return.
    let now = unix_now();
    let nonce = fresh_nonce(verified.user_id, now);
    let ticket = mint_ticket(&state.ticket_key, verified.user_id, now, &nonce);
    let identity = state.identity_for(verified.user_id);

    audit::log().emit(
        audit::AuditEvent::new(
            "discord-activity",
            audit::Actor::custodial(verified.user_id.to_string(), identity.0.clone()),
            audit::Surface::Http,
            audit::Input::new(
                route,
                serde_json::json!({ "minted_at": now, "username": verified.username }),
            ),
        )
        .correlated(&corr)
        .decided("routed", "ticket_minted"),
    );

    Json(serde_json::json!({
        "access_token": verified.access_token,
        "ticket": ticket,
        "custodial_pubkey_hex": identity.0,
    }))
    .into_response()
}

/// RFC 3986 path-segment encoding for values returned decoded by Axum's
/// `Path` extractor. Route delimiters and markup never come from a session id.
fn path_segment(value: &str) -> String {
    const HEX: &[u8; 16] = b"0123456789ABCDEF";
    let mut encoded = String::with_capacity(value.len());
    for byte in value.bytes() {
        if byte.is_ascii_alphanumeric() || matches!(byte, b'-' | b'.' | b'_' | b'~') {
            encoded.push(byte as char);
        } else {
            encoded.push('%');
            encoded.push(HEX[(byte >> 4) as usize] as char);
            encoded.push(HEX[(byte & 0x0f) as usize] as char);
        }
    }
    encoded
}

fn da_session_path(key: &str, id: &str) -> String {
    format!(
        "/da/offerings/{}/session/{}",
        path_segment(key),
        path_segment(id)
    )
}

/// Rebind the shared browser fragment to the Discord-native rail. Resume and
/// replay stay ticket-authenticated and the common chrome tells the truth about
/// signed Discord provenance.
fn da_native_fragment(html: String, key: &str, id: &str, fragment: bool) -> String {
    let web_base = format!("/offerings/{}/session/{}", crate::esc(key), crate::esc(id));
    let native_base = da_session_path(key, id);
    let web_verify = format!("{web_base}/verify");
    let mut native = html.replace(
        &format!("href=\"{web_base}\" rel=\"bookmark\""),
        &format!(
            "href=\"{native_base}\" data-da-session=\"{native_base}\" rel=\"bookmark\""
        ),
    )
    .replace(
        &format!("href=\"{web_verify}\""),
        &format!(
            "href=\"{native_base}/verify\" data-da-verify=\"{native_base}/verify\""
        ),
    )
    .replace(
        &format!("action=\"{web_base}"),
        &format!("action=\"{native_base}"),
    )
    .replace(
        "data-actor-attribution=\"asserted\"",
        "data-actor-attribution=\"signed\"",
    )
    .replace(
        "Browser actor attribution is asserted, not authenticated.",
        "Discord identity is authenticated by OAuth ticket; turns carry custodial signed provenance.",
    );
    if fragment {
        if let Some(kind) = game_kind(key) {
            native = format!(
                "<section class=\"game-session-rail\" data-game-session=\"true\" \
                 data-game-family=\"{}\" data-session-id=\"{}\" \
                 data-actor-attribution=\"signed\" aria-label=\"Session continuity and privacy\">\
                 <div class=\"game-session-resume\"><span class=\"game-session-kicker\">Session</span>\
                 <strong>{}</strong><a href=\"{native_base}\" data-da-session=\"{native_base}\" \
                 rel=\"bookmark\">Resume here</a></div>\
                 <p class=\"game-session-boundary\"><span aria-hidden=\"true\">◐</span>\
                 Discord identity is authenticated by OAuth ticket; turns carry custodial signed provenance. \
                 Private game fields remain scoped to their owning projection.</p></section>{native}",
                kind.as_str(),
                crate::esc(id),
                crate::esc(id),
            );
        }
    }
    native
}

/// `GET /da/offerings` — the catalog fragment for the VERIFIED viewer: a card per registered
/// offering linking that viewer's own default session (`da-{key}-{ident16}` — relaunching the
/// Activity lands the same player in the same session).
async fn get_da_offerings(
    State(state): State<Arc<DiscordActivityState>>,
    headers: HeaderMap,
) -> Response {
    let corr = audit::correlation_id();
    let user = match verified_user(&state, &headers, &corr, "GET /da/offerings") {
        Ok(u) => u,
        Err(resp) => return resp,
    };
    let ident = state.identity_for(user.user_id);
    let offerings = state.catalog.list_offerings();
    let ident16 = &ident.0[..16.min(ident.0.len())];
    let mut cards = String::new();
    for o in &offerings {
        let session = format!("da-{}-{ident16}", o.key);
        let path = da_session_path(&o.key, &session);
        cards.push_str(&format!(
            "<div class=\"card\" style=\"margin:.6rem 0;padding:1rem;border:1px solid \
             var(--border);border-radius:var(--r-md);background:var(--panel)\">\
             <h3 style=\"margin:0 0 .35rem\">{title}</h3>\
             <a class=\"btn btn-primary\" href=\"{path}\" data-da-session=\"{path}\">Play</a>\
             </div>",
            title = crate::esc(&o.title),
            path = crate::esc(&path),
        ));
    }
    // THE LAB FRAMING (shared words: `dreggnet_catalog::{flagship_pointer, lab_intro}`) — the same
    // Descent-first shelf the `/tg` fragment paints, so the Activity is visually the SAME product.
    //
    // COHERENCE FIX (maturation cluster 5): the featured Descent used to carry a plain
    // `<a href="/descent">` — an OUT-link to the COOKIE-identity surface — dropping a
    // Discord-VERIFIED viewer onto a DIFFERENT, unverified identity right under the "Verified via
    // Discord" banner. There is no ticket-gated Descent twin under `/da` yet, so we DROP the
    // OUT-link from the verified shelf and NAME the identity boundary (pointing at the link
    // ceremony that actually binds the two) instead of laundering it. The identity-coherent
    // playables are the ticket-gated offering `cards` above.
    let featured = format!(
        "<div class=\"card\" style=\"margin:.6rem 0;padding:1rem;border:1px solid \
         var(--border);border-radius:var(--r-md);background:var(--panel)\">\
         <h3 style=\"margin:0 0 .35rem\">The Descent</h3>\
         <p class=\"prose\" style=\"margin:0 0 .5rem\">{flagship}</p>\
         <p class=\"prose\" style=\"margin:0;font-size:.85em;opacity:.75\">Played on the open \
         leaderboard under a SEPARATE identity from your Discord-verified play here — \
         <b>Link across platforms</b> below binds them into one.</p>\
         </div>\
         <p class=\"prose\" style=\"margin:.8rem 0 .4rem\">{lab}</p>",
        flagship = crate::esc(dreggnet_catalog::flagship_pointer()),
        lab = crate::esc(dreggnet_catalog::lab_intro()),
    );
    // A discoverable entry to the cross-platform link ceremony. A PLAIN anchor (no
    // `data-da-session`) so the shell's click interceptor ignores it and the iframe navigates to
    // `/da/link` as a document load — where the page runs its own SDK OAuth to obtain a ticket.
    let link = "<p class=\"prose\" style=\"margin:1rem 0 .2rem\">\
         <a class=\"btn\" href=\"/da/link\">🔗 Link this Discord account across platforms</a></p>\
         <p class=\"prose\" style=\"margin:0;font-size:.85em;opacity:.8\">Bind Discord-you and \
         Telegram-you to one root key — one human on boards + leaderboards.</p>";
    let body = format!(
        "<div class=\"notice ok\" role=\"status\">Verified via Discord — playing as \
         <code>{ident16}…</code> (the same identity as in-chat)</div>{featured}{cards}{link}",
    );
    Html(body).into_response()
}

/// `GET /da/offerings/{key}/session/{id}` — validate the ticket, open the session as the VERIFIED
/// identity (opener attribution stays `Asserted`: only `verify_signed` ever earns `Signed`; the
/// opener lane is an advisory quota key, here backed by a ticket-verified label), and render the
/// viewer's own projection. Unlike `/tg`, there is NO cold-deep-link soft path: the Activity iframe
/// always boots the root shell, so every `/da/*` fetch carries the ticket (missing → hard `401`).
async fn get_da_session(
    State(state): State<Arc<DiscordActivityState>>,
    Path((key, id)): Path<(String, String)>,
    headers: HeaderMap,
) -> Response {
    let corr = audit::correlation_id();
    let route = "GET /da/offerings/{key}/session/{id}";
    let user = match verified_user(&state, &headers, &corr, route) {
        Ok(u) => u,
        Err(resp) => return resp,
    };
    let viewer = state.identity_for(user.user_id);
    let sid = SessionId::new(id);

    let opened = state.catalog.ensure_open_and_bind(
        &key,
        &sid,
        &viewer,
        Some(Attribution::Asserted {
            label: viewer.0.clone(),
        }),
    );
    metrics::set_sessions_open(state.catalog.shared_session_count() as f64);
    {
        let (kind, reason) = match &opened {
            Ok(_) => ("routed", String::new()),
            Err(CatalogGameError::Host(e)) => open_audit_parts(e),
            Err(e) => ("gated", e.to_string()),
        };
        audit::log().emit(
            audit::AuditEvent::new(
                "discord-activity",
                audit::Actor::custodial(user.user_id.to_string(), viewer.0.clone()),
                audit::Surface::Http,
                audit::Input::new(route, serde_json::Value::Null),
            )
            .correlated(&corr)
            .in_session(Some(key.clone()), Some(sid.0.clone()))
            .decided(kind, reason),
        );
    }
    match opened {
        Ok(_) => {}
        Err(CatalogGameError::Host(HostError::UnknownOffering(k))) => {
            return (
                StatusCode::NOT_FOUND,
                format!("no offering registered under key {k:?}"),
            )
                .into_response();
        }
        Err(CatalogGameError::Host(
            e @ (HostError::Policy(_) | HostError::ResumeFailed { .. }),
        )) => {
            return refused_open_response(&sid, &e);
        }
        Err(CatalogGameError::Host(error)) => {
            return (StatusCode::INTERNAL_SERVER_ERROR, error.to_string()).into_response();
        }
        Err(error) => return (StatusCode::CONFLICT, error.to_string()).into_response(),
    }

    Html(da_native_fragment(
        render_offering_response(
            &state.catalog,
            &key,
            &sid,
            None,
            &viewer,
            wants_fragment(&headers),
        ),
        &key,
        &sid.0,
        wants_fragment(&headers),
    ))
    .into_response()
}

/// Ticket-authenticated replay verification on the Activity rail.  The link
/// never drops into the cookie-identity web surface.
async fn get_da_verify(
    State(state): State<Arc<DiscordActivityState>>,
    Path((key, id)): Path<(String, String)>,
    headers: HeaderMap,
) -> Response {
    let corr = audit::correlation_id();
    let user = match verified_user(
        &state,
        &headers,
        &corr,
        "GET /da/offerings/{key}/session/{id}/verify",
    ) {
        Ok(user) => user,
        Err(response) => return response,
    };
    let viewer = state.identity_for(user.user_id);
    let sid = SessionId::new(id);
    let report = if game_kind(&key).is_some() {
        match state.catalog.run_current_bound_game(
            &key,
            &sid,
            &viewer,
            move |host, _, _, session| host.verify(session.offering(), session.session_id()),
        ) {
            Ok(report) => report,
            Err(error) => {
                return (
                    StatusCode::CONFLICT,
                    Json(serde_json::json!({
                        "verified": false,
                        "turns": 0,
                        "detail": error.to_string(),
                        "surface": "discord",
                    })),
                )
                    .into_response();
            }
        }
    } else {
        let routed_key = key.clone();
        let routed_sid = sid.clone();
        state.catalog.run_offering(&key, &viewer, move |host| {
            host.verify(&routed_key, &routed_sid)
        })
    };
    match report {
        Some(report) => Json(serde_json::json!({
            "verified": report.verified,
            "turns": report.turns,
            "detail": report.detail,
            "surface": "discord",
        }))
        .into_response(),
        None => (
            StatusCode::NOT_FOUND,
            Json(serde_json::json!({
                "verified": false,
                "turns": 0,
                "detail": "no such Discord game session",
                "surface": "discord",
            })),
        )
            .into_response(),
    }
}

/// Ticket-authenticated discovery of transport-bearing affordances on one live
/// session. The descriptor itself is shared byte-for-byte across surfaces.
#[cfg(feature = "hosted-binary-operations")]
async fn get_da_operations(
    State(state): State<Arc<DiscordActivityState>>,
    Path((key, id)): Path<(String, String)>,
    headers: HeaderMap,
) -> Response {
    let corr = audit::correlation_id();
    if let Err(response) = verified_user(
        &state,
        &headers,
        &corr,
        "GET /da/offerings/{key}/session/{id}/operations",
    ) {
        return response;
    }
    crate::fhegg_operation::session_operations(&state.catalog, key, id)
}

/// Discord-ticket wrapper around the one shared owning-bundle implementation.
/// Ticket verification completes before bounded body collection; neither the
/// bearer ticket nor uploaded bundle is logged.
#[cfg(feature = "hosted-binary-operations")]
async fn post_da_operation(
    State(state): State<Arc<DiscordActivityState>>,
    Path((key, id, name)): Path<(String, String, String)>,
    request: axum::extract::Request,
) -> Response {
    let corr = audit::correlation_id();
    let user = match verified_user(
        &state,
        request.headers(),
        &corr,
        "POST /da/offerings/{key}/session/{id}/operations/{name}",
    ) {
        Ok(user) => user,
        Err(response) => return response,
    };
    let actor = state.identity_for(user.user_id);
    crate::fhegg_operation::execute_upload(
        Arc::clone(&state.catalog),
        key,
        id,
        name,
        actor,
        request,
    )
    .await
}

/// Discord-ticket-authenticated discovery of read-only session artifacts.
#[cfg(feature = "hosted-binary-operations")]
async fn get_da_artifacts(
    State(state): State<Arc<DiscordActivityState>>,
    Path((key, id)): Path<(String, String)>,
    headers: HeaderMap,
) -> Response {
    let corr = audit::correlation_id();
    if let Err(response) = verified_user(
        &state,
        &headers,
        &corr,
        "GET /da/offerings/{key}/session/{id}/artifacts",
    ) {
        return response;
    }
    crate::fhegg_operation::session_artifacts(&state.catalog, key, id)
}

/// Discord-ticket-authenticated wrapper around the shared artifact export.
#[cfg(feature = "hosted-binary-operations")]
async fn get_da_artifact(
    State(state): State<Arc<DiscordActivityState>>,
    Path((key, id, name)): Path<(String, String, String)>,
    Query(authority): Query<crate::fhegg_operation::GameResourceAuthorityQuery>,
    headers: HeaderMap,
) -> Response {
    let corr = audit::correlation_id();
    let user = match verified_user(
        &state,
        &headers,
        &corr,
        "GET /da/offerings/{key}/session/{id}/artifacts/{name}",
    ) {
        Ok(user) => user,
        Err(response) => return response,
    };
    crate::fhegg_operation::export_artifact(
        &state.catalog,
        key,
        id,
        name,
        Some(state.identity_for(user.user_id)),
        authority,
    )
}

/// The `{turn, arg, text}` POST body of `POST /da/offerings/{key}/session/{id}/act` — the same form
/// shape as the unsigned `/act` twin (and the `/tg` twin), plus the optional signed free-text payload.
#[derive(Debug, Clone, Deserialize)]
pub struct DaActForm {
    /// The affordance verb.
    pub turn: String,
    /// The affordance argument.
    #[serde(default)]
    pub arg: i64,
    /// Optional free-text payload (signed; absent signs as empty).
    #[serde(default)]
    pub text: Option<String>,
    #[serde(default)]
    pub game_host_incarnation: Option<String>,
    #[serde(default)]
    pub game_session_generation: Option<u64>,
    #[serde(default)]
    pub game_expected_pre_head: Option<String>,
    #[serde(default)]
    pub game_form_token: Option<String>,
}

/// `POST /da/offerings/{key}/session/{id}/act` — validate the ticket, rebuild the custodial signer
/// (`TurnSigner::from_seed(seed_for(bot_secret, uid))` — byte-identical to the identity the bot
/// attributes), and land ONE turn with **verified `Signed` provenance**: inside a single host-thread
/// job, read the replay-counter floor, sign at exactly the expected counter, and delegate to
/// `advance_signed` — atomic, no TOCTOU. `post_tg_act`'s body, ticket-gated. A `403` from the
/// VERIFIER on this path is a server bug (the server signed for itself in the same job) — logged loudly.
async fn post_da_act(
    State(state): State<Arc<DiscordActivityState>>,
    Path((key, id)): Path<(String, String)>,
    headers: HeaderMap,
    Form(form): Form<DaActForm>,
) -> Response {
    let corr = audit::correlation_id();
    let route = "POST /da/offerings/{key}/session/{id}/act";
    let user = match verified_user(&state, &headers, &corr, route) {
        Ok(u) => u,
        Err(resp) => return resp,
    };
    let sid = SessionId::new(id);
    let audit_detail = serde_json::json!({
        "turn": form.turn,
        "arg": form.arg,
        "text": form.text,
    });

    // The custodial signer for the VERIFIED uid — the same seed, therefore the same Ed25519
    // identity, as the in-chat cipherclerk. The transient seed copy is wiped after construction.
    let seed = Zeroizing::new(seed_for(&state.bot_secret, user.user_id));
    let signer = TurnSigner::from_seed(*seed);
    drop(seed);
    let viewer = signer.identity();
    let act_event = |detail: serde_json::Value| {
        audit::AuditEvent::new(
            "discord-activity",
            audit::Actor::custodial(user.user_id.to_string(), viewer.0.clone()),
            audit::Surface::Http,
            audit::Input::new(route, detail),
        )
        .correlated(&corr)
        .in_session(Some(key.clone()), Some(sid.0.clone()))
    };

    let mut action = Action::new(form.turn.clone(), form.turn, form.arg, true);
    if let Some(text) = form.text.filter(|t| !t.is_empty()) {
        action = action.with_text(text);
    }

    let presented_game = if game_kind(&key).is_some() {
        let authority_form = OfferingActForm {
            turn: action.turn.clone(),
            arg: action.arg,
            game_host_incarnation: form.game_host_incarnation,
            game_session_generation: form.game_session_generation,
            game_expected_pre_head: form.game_expected_pre_head,
            game_form_token: form.game_form_token,
        };
        match state
            .catalog
            .presented_game_action_for(&key, &sid, &authority_form, &action)
        {
            Ok(reference) => Some(reference),
            Err(error) => return (StatusCode::CONFLICT, error.to_string()).into_response(),
        }
    } else {
        None
    };

    if presented_game.is_none() {
        match state.catalog.ensure_open_and_bind(
            &key,
            &sid,
            &viewer,
            Some(Attribution::Signed {
                pubkey_hex: viewer.0.clone(),
            }),
        ) {
            Ok(_) => {}
            Err(CatalogGameError::Host(HostError::UnknownOffering(k))) => {
                audit::log().emit(act_event(audit_detail).decided("refused", "unknown_offering"));
                return (
                    StatusCode::NOT_FOUND,
                    format!("no offering registered under key {k:?}"),
                )
                    .into_response();
            }
            Err(CatalogGameError::Host(
                e @ (HostError::Policy(_) | HostError::ResumeFailed { .. }),
            )) => {
                let (kind, reason) = open_audit_parts(&e);
                audit::log().emit(act_event(audit_detail).decided(kind, reason));
                return refused_open_response(&sid, &e);
            }
            Err(error) => return (StatusCode::CONFLICT, error.to_string()).into_response(),
        }
    }

    // ONE atomic host-thread job: floor-read → sign at exactly the expected counter → verify →
    // consume → executor referees the move. No other job can interleave. Routed to the viewer's
    // own world for an RPG key.
    let outcome = if let Some(reference) = presented_game {
        let presented = reference.session.clone();
        let k = key.clone();
        let sid = sid.clone();
        let opener = Attribution::Signed {
            pubkey_hex: viewer.0.clone(),
        };
        match state.catalog.run_presented_bound_game(
            presented,
            &viewer,
            opener,
            move |h, incarnation, generation, session| {
                let expected = match h.signed_counter(&k, &sid, signer.pubkey_hex()) {
                    None => 0,
                    Some(last) => match last.checked_add(1) {
                        Some(n) => n,
                        None => {
                            return act_signed::SignedAdvance::HostError(HostError::Signature(
                                SignedError::StaleCounter {
                                    presented: u64::MAX,
                                    expected: u64::MAX,
                                },
                            ));
                        }
                    },
                };
                let command = match sign_game_action(&signer, reference, expected, action) {
                    Ok(command) => command,
                    Err(error) => {
                        return act_signed::SignedAdvance::GameRouteRefused(error.to_string());
                    }
                };
                act_signed::advance_signed_on_host(
                    h,
                    k,
                    sid,
                    Some((incarnation, generation, session)),
                    act_signed::RoutedSignedAction::Game(command),
                    Custody::Custodial,
                )
            },
        ) {
            Ok(outcome) => outcome,
            Err(CatalogGameError::Host(error)) => act_signed::SignedAdvance::HostError(error),
            Err(error) => act_signed::SignedAdvance::GameRouteRefused(error.to_string()),
        }
    } else {
        let k = key.clone();
        let sid = sid.clone();
        state.catalog.run_offering(&key, &viewer, move |h| {
            let expected = match h.signed_counter(&k, &sid, signer.pubkey_hex()) {
                None => 0,
                Some(last) => match last.checked_add(1) {
                    Some(n) => n,
                    None => {
                        return act_signed::SignedAdvance::HostError(HostError::Signature(
                            SignedError::StaleCounter {
                                presented: u64::MAX,
                                expected: u64::MAX,
                            },
                        ));
                    }
                },
            };
            // CUSTODIAL: sign under THIS host's incarnation so a captured envelope cannot re-verify
            // on a same-`id` session reopened under a later incarnation.
            let sa = signer.sign_in_epoch(&k, &sid, expected, &h.signing_epoch(), action);
            act_signed::advance_signed_on_host(
                h,
                k,
                sid,
                None,
                act_signed::RoutedSignedAction::Legacy(sa),
                Custody::Custodial,
            )
        })
    };

    {
        let (kind, reason, out) = match &outcome {
            act_signed::SignedAdvance::Advanced {
                outcome: Outcome::Landed { receipt, ended },
                ..
            } => (
                "routed",
                String::new(),
                audit::AuditOutcome::Landed {
                    turn_hash: audit::hex32(&receipt.turn_hash),
                    ended: *ended,
                },
            ),
            act_signed::SignedAdvance::Advanced {
                outcome: Outcome::Refused(why),
                ..
            } => (
                "routed",
                String::new(),
                audit::AuditOutcome::Refused { why: why.clone() },
            ),
            act_signed::SignedAdvance::CommittedButPublicationFailed { outcome, error, .. } => {
                let out = match outcome {
                    Outcome::Landed { receipt, ended } => audit::AuditOutcome::Landed {
                        turn_hash: audit::hex32(&receipt.turn_hash),
                        ended: *ended,
                    },
                    Outcome::Refused(why) => audit::AuditOutcome::Refused { why: why.clone() },
                };
                ("committed", format!("publication_failed:{error}"), out)
            }
            act_signed::SignedAdvance::HostError(HostError::Signature(e)) => (
                "error",
                format!("custodial_verifier_refused: {e}"),
                audit::AuditOutcome::Error {
                    what: e.to_string(),
                },
            ),
            act_signed::SignedAdvance::HostError(e) => {
                let (kind, reason) = open_audit_parts(e);
                (kind, reason, audit::AuditOutcome::None)
            }
            act_signed::SignedAdvance::GameRouteRefused(reason) => {
                ("gated", reason.clone(), audit::AuditOutcome::None)
            }
        };
        audit::log().emit(
            act_event(audit_detail)
                .decided(kind, reason)
                .with_outcome(out),
        );
    }

    let notice = match outcome {
        act_signed::SignedAdvance::Advanced {
            outcome: Outcome::Landed { receipt, ended },
            publication,
            ..
        } => format!(
            "Turn committed — {}",
            publication.as_ref().map_or_else(
                || PlayerTurnReceipt::from_landed_signed(
                    &receipt,
                    ended,
                    Custody::Custodial,
                    viewer.0.clone(),
                )
                .compact_text(PlayerReplaySurface::Discord),
                |publication| crate::game_session::public_receipt_text(
                    publication,
                    PlayerReplaySurface::Discord,
                ),
            )
        ),
        act_signed::SignedAdvance::Advanced {
            outcome: Outcome::Refused(why),
            ..
        } => {
            metrics::inc_turn_refused();
            format!("Refused: {why} (nothing committed — anti-ghost).")
        }
        act_signed::SignedAdvance::CommittedButPublicationFailed { error, .. } => format!(
            "Turn committed, but its public receipt could not be rendered ({error}). Do not retry; refresh to inspect the committed state."
        ),
        act_signed::SignedAdvance::HostError(HostError::Signature(e)) => {
            tracing::error!(
                error = %e,
                offering = %key,
                "custodial signed advance REFUSED BY THE VERIFIER — this indicates a server bug"
            );
            return (
                StatusCode::FORBIDDEN,
                format!("signed advance refused: {e}"),
            )
                .into_response();
        }
        act_signed::SignedAdvance::HostError(
            e @ (HostError::UnknownOffering(_) | HostError::UnknownSession { .. }),
        ) => {
            return (StatusCode::NOT_FOUND, e.to_string()).into_response();
        }
        act_signed::SignedAdvance::HostError(
            e @ (HostError::Policy(_) | HostError::ResumeFailed { .. }),
        ) => {
            return refused_open_response(&sid, &e);
        }
        act_signed::SignedAdvance::HostError(e @ HostError::Deploy(_)) => {
            return (StatusCode::INTERNAL_SERVER_ERROR, e.to_string()).into_response();
        }
        act_signed::SignedAdvance::GameRouteRefused(reason) => {
            return (StatusCode::CONFLICT, reason).into_response();
        }
    };

    Html(da_native_fragment(
        render_offering_response(
            &state.catalog,
            &key,
            &sid,
            Some(&notice),
            &viewer,
            wants_fragment(&headers),
        ),
        &key,
        &sid.0,
        wants_fragment(&headers),
    ))
    .into_response()
}

// ─────────────────────────────────────────────────────────────────────────────
// The Activity shell (design §5/§6) — strict CSP, same-origin scripts, vendored SDK.
// ─────────────────────────────────────────────────────────────────────────────

/// The strict Content-Security-Policy for the Activity shell — the `/tg/link` review's posture
/// (`docs/TG-LINK-SECURITY-REVIEW-2026-07-18.md`), adapted for the Discord iframe: NO external
/// origins at all (§6 — everything same-origin under the root URL mapping), no `'unsafe-inline'` for
/// scripts (the SDK + the shell module are served same-origin), `connect-src 'self'` denies any
/// exfiltration channel, and `frame-ancestors` restricts embedding to Discord's proxy + clients.
const ACTIVITY_CSP: &str = "default-src 'none'; \
    script-src 'self'; \
    style-src 'unsafe-inline'; \
    connect-src 'self'; \
    img-src 'self' data:; \
    base-uri 'none'; object-src 'none'; form-action 'none'; \
    frame-ancestors https://discord.com https://*.discord.com https://*.discordsays.com";

/// `GET /da` — the Activity shell (static HTML; the strict CSP header is the point). The `client_id`
/// is injected into a `data-` attribute (never inline script), so the same-origin module can
/// construct `new DiscordSDK(client_id)` under `script-src 'self'`.
async fn get_da_shell(State(state): State<Arc<DiscordActivityState>>) -> Response {
    let html = shell_page(&state.client_id);
    (
        [(header::CONTENT_SECURITY_POLICY, ACTIVITY_CSP)],
        Html(html),
    )
        .into_response()
}

/// `GET /da/static/app.js` — the shell's bootstrap module, served SAME-ORIGIN so the CSP forbids
/// inline script (a CDN swap or XSS of the flow-driving code has no foothold).
async fn get_da_app_js() -> impl IntoResponse {
    (
        [(header::CONTENT_TYPE, "text/javascript; charset=utf-8")],
        DA_APP_JS,
    )
}

/// `GET /da/static/discord-sdk.js` — the vendored `@discord/embedded-app-sdk` browser bundle,
/// same-origin (§6 — no `esm.sh`, no external origin under the iframe CSP).
///
/// **TODO(ember): vendor the real bundle.** This ships a PLACEHOLDER: `dreggnet-web` has no JS build
/// pipeline, and the real SDK is an esbuild single-file bundle. Build it once
/// (`esbuild @discord/embedded-app-sdk --bundle --format=iife --global-name=... `, exposing
/// `window.DiscordSDK`) and replace [`DA_SDK_PLACEHOLDER_JS`] with the pinned output. Until then the
/// shell detects the placeholder and shows an honest "SDK not vendored yet" notice instead of
/// authorizing — every other part of the flow (ready → authorize → `/da/token` → ticket header) is
/// already wired and lights up the moment the real bundle lands.
async fn get_da_sdk_js() -> impl IntoResponse {
    (
        [(header::CONTENT_TYPE, "text/javascript; charset=utf-8")],
        DA_SDK_PLACEHOLDER_JS,
    )
}

/// **The Activity shell page** — the served HTML for `GET /da`: the crate's own stylesheet (so the
/// Activity is visually the SAME product), the vendored SDK as the FIRST script, the live region,
/// and the same-origin bootstrap module. Static — identity only ever comes from the ticket the
/// module attaches after `/da/token`. `client_id` is HTML-escaped into `data-client-id`, never
/// interpolated into script.
fn shell_page(client_id: &str) -> String {
    format!(
        "<!doctype html><html lang=\"en\"><head><meta charset=\"utf-8\">\
         <meta name=\"viewport\" content=\"width=device-width, initial-scale=1, viewport-fit=cover\">\
         <title>DreggNet — Discord Activity</title>\
         {style}</head><body>\
         <main class=\"session\">\
         <p class=\"prose\" id=\"da-greet\">DreggNet offerings — every move is a receipt.</p>\
         <div id=\"da-root\" data-client-id=\"{client_id}\"><p class=\"prose\">Loading the catalog…</p></div>\
         </main>\
         <script src=\"/da/static/discord-sdk.js\"></script>\
         <script type=\"module\" src=\"/da/static/app.js\"></script>\
         </body></html>",
        style = crate::STYLE,
        client_id = crate::esc(client_id),
    )
}

/// The PLACEHOLDER SDK bundle (see [`get_da_sdk_js`]). It deliberately does NOT define
/// `window.DiscordSDK`, so the shell shows an honest "not vendored yet" notice rather than pretending
/// to authorize. Replace with the real esbuild bundle.
const DA_SDK_PLACEHOLDER_JS: &str = r##"// PLACEHOLDER — @discord/embedded-app-sdk is NOT vendored yet.
// TODO(ember): replace this file with the pinned esbuild bundle that exposes `window.DiscordSDK`.
// dreggnet-web has no JS build step; build the bundle once and commit it here (design §6).
window.__DISCORD_SDK_PLACEHOLDER = true;
console.warn("dregg: @discord/embedded-app-sdk placeholder — vendor the real bundle at /da/static/discord-sdk.js");
"##;

/// The Activity bootstrap module — the `/tg` shell script with the header renamed to
/// `X-Dregg-Activity-Ticket` and the identity step swapped from Telegram's `initData` envelope to
/// the Discord OAuth flow (`ready` → `authorize({scope:['identify']})` → `POST /da/token` → ticket).
/// Served same-origin so the strict CSP forbids inline script. Guards on the placeholder SDK so a
/// missing vendored bundle degrades to an honest notice, never a broken authorize.
const DA_APP_JS: &str = r##"const root = document.getElementById("da-root");
const clientId = root && root.dataset ? root.dataset.clientId : "";

function notice(message, cls) {
  const box = document.createElement("div");
  box.className = "notice " + (cls || "refused");
  box.setAttribute("role", "status");
  box.textContent = String(message);
  root.replaceChildren(box);
}
function failure(error) {
  notice(error && error.message ? error.message : error, "refused");
}
function report(message, cls) {
  const old = root.querySelector("[data-native-replay-report]");
  if (old) { old.remove(); }
  const box = document.createElement("div");
  box.className = "notice " + (cls || "refused");
  box.setAttribute("role", "status");
  box.setAttribute("data-native-replay-report", "true");
  box.textContent = String(message);
  root.prepend(box);
}

// The SDK must be vendored (window.DiscordSDK). The placeholder degrades to an honest message.
const SDKCtor = window.DiscordSDK;
if (window.__DISCORD_SDK_PLACEHOLDER || typeof SDKCtor !== "function") {
  notice("The Discord Embedded App SDK is not vendored on this build yet — the Activity cannot " +
    "identify you. Serve the real same-origin SDK bundle to enable it.", "refused");
} else {
  bootActivity(new SDKCtor(clientId)).catch(function (e) {
    failure(new Error("Could not start the Activity: " + (e && e.message ? e.message : e)));
  });
}

// The verified ticket, attached to every state-touching fetch (a HEADER, never a URL).
let TICKET = null;

function nativePath(raw) {
  const url = new URL(raw, window.location.origin);
  if (url.origin !== window.location.origin) { throw new Error("Refused a cross-origin game route."); }
  let path = url.pathname;
  if (path === "/offerings" || path.indexOf("/offerings/") === 0) { path = "/da" + path; }
  if (path !== "/da/offerings" && path.indexOf("/da/offerings/") !== 0) {
    throw new Error("Refused a non-Discord game route.");
  }
  return path + url.search;
}
function responseError(resp, body) {
  const detail = body ? ": " + body.slice(0, 500) : "";
  return new Error("Request refused (HTTP " + resp.status + ")" + detail);
}
function isType(resp, expected) {
  const actual = (resp.headers.get("content-type") || "").split(";", 1)[0].trim().toLowerCase();
  return expected === "json"
    ? (actual === "application/json" || actual.endsWith("+json"))
    : actual === "text/html";
}
async function readHtml(resp) {
  const body = await resp.text();
  if (!resp.ok) { throw responseError(resp, body); }
  if (!isType(resp, "html")) { throw new Error("Refused a non-HTML fragment response."); }
  return body;
}
async function readJson(resp) {
  const body = await resp.text();
  if (!resp.ok) { throw responseError(resp, body); }
  if (!isType(resp, "json")) { throw new Error("Refused a non-JSON operation response."); }
  try { return JSON.parse(body); } catch (_) { throw new Error("Refused malformed JSON."); }
}
function daRequest(path, opts) {
  opts = opts || {};
  const headers = new Headers(opts.headers || {});
  if (TICKET) { headers.set("X-Dregg-Activity-Ticket", TICKET); }
  headers.set("X-Fragment", "1");
  opts.headers = headers;
  opts.credentials = "same-origin";
  opts.cache = "no-store";
  return fetch(path, opts);
}
function daFetchHtml(path, opts) {
  return daRequest(nativePath(path), opts).then(readHtml);
}
function encodeForm(form) {
  const params = new URLSearchParams();
  new FormData(form).forEach(function (value, name) {
    if (typeof value !== "string") { throw new Error("A file is not a turn-form field."); }
    params.append(name, value);
  });
  return params.toString();
}

function showCatalog() {
  daFetchHtml("/da/offerings").then(function (html) { root.innerHTML = html; }).catch(failure);
}
function openSession(path) {
  daFetchHtml(path).then(function (html) { root.innerHTML = html; }).catch(failure);
}
function showVerification(path) {
  daRequest(nativePath(path), { headers: { "Accept": "application/json" } })
    .then(readJson)
    .then(function (report) {
      const message = (report.verified ? "Replay verified" : "Replay refused") + " · " +
        report.turns + " turns · " + report.detail;
      report(message, report.verified ? "ok" : "refused");
    })
    .catch(failure);
}

async function bootActivity(sdk) {
  await sdk.ready();
  // The consent step (once per user); prompt:'none' re-issues silently once consent exists.
  const { code } = await sdk.commands.authorize({
    client_id: clientId,
    response_type: "code",
    prompt: "none",
    scope: ["identify"],
  });
  // Server-side exchange: the uid is asserted by Discord to the holder of our client_secret, and
  // the server mints the ticket. The client never asserts identity.
  const tokenResponse = await fetch("/da/token", {
    method: "POST",
    headers: { "Content-Type": "application/json", "Accept": "application/json" },
    credentials: "same-origin",
    cache: "no-store",
    body: JSON.stringify({ code }),
  });
  const data = await readJson(tokenResponse);
  if (!data.ticket || typeof data.ticket !== "string") { throw new Error("Token response omitted the activity ticket."); }
  TICKET = data.ticket;
  // Complete the SDK handshake client-side (the access_token is display-only for the server).
  if (data.access_token) {
    try { await sdk.commands.authenticate({ access_token: data.access_token }); } catch (e) { /* handshake best-effort */ }
  }
  const greet = document.getElementById("da-greet");
  if (greet && data.custodial_pubkey_hex) {
    greet.textContent = "Verified via Discord — playing as " + data.custodial_pubkey_hex.slice(0, 16) + "…";
  }

  root.addEventListener("submit", async function (ev) {
    const form = ev.target;
    if (!form || !form.action) { return; }
    ev.preventDefault();
    let path;
    try { path = nativePath(form.action); } catch (error) { failure(error); return; }

    // Opaque proof/receipt uploads are raw File bodies.  URLSearchParams must
    // never see them: its coercion would upload "[object File]" instead.
    if (form.classList.contains("binary-operation")) {
      const input = form.querySelector("input[type=file]");
      const status = form.querySelector("[role=status]");
      const file = input && input.files && input.files[0];
      if (!file) {
        if (status) { status.textContent = "Choose the canonical proof or receipt first."; }
        return;
      }
      form.classList.add("pending");
      if (status) { status.textContent = "Verifying opaque receipt…"; }
      try {
        const operationResponse = await daRequest(path, {
          method: "POST",
          headers: {
            "Content-Type": form.getAttribute("data-media") || "application/octet-stream",
            "Accept": "application/json"
          },
          body: file
        });
        await readJson(operationResponse);
        openSession(path.split("/operations/", 1)[0]);
      } catch (error) {
        form.classList.remove("pending");
        if (status) { status.textContent = "Refused: " + (error.message || error); }
      }
      return;
    }

    try {
      const html = await daFetchHtml(path, {
        method: "POST",
        headers: { "Content-Type": "application/x-www-form-urlencoded" },
        body: encodeForm(form),
      });
      root.innerHTML = html;
    } catch (error) { failure(error); }
  });
  // Catalog navigation and native replay verification keep the activity ticket.
  root.addEventListener("click", function (ev) {
    let el = ev.target;
    while (el && el !== root && !(el.getAttribute &&
      (el.getAttribute("data-da-session") || el.getAttribute("data-da-verify")))) {
      el = el.parentNode;
    }
    if (!el || el === root || !el.getAttribute) { return; }
    const verify = el.getAttribute("data-da-verify");
    if (verify) { ev.preventDefault(); showVerification(verify); return; }
    const path = el.getAttribute("data-da-session");
    if (!path) { return; }
    ev.preventDefault();
    openSession(path);
  });

  showCatalog();
}
"##;

// ─────────────────────────────────────────────────────────────────────────────
// The cross-platform LINK ceremony (`/da/link/*`, design §5) — bind this Discord account to a
// user-held root key K, recorded in the SHARED registry (`links.tsv`) so a link made inside the
// Activity resolves on Telegram (and vice versa) — Discord-you and Telegram-you collapse into ONE
// human via root key K. The `post_tg_link` twin, `platform="discord"`: the activity ticket
// authenticates WHICH Discord uid; K's own signature attests the human. The SERVER half; the client
// (`/da/link` page: passkey / passphrase / relay) signs the claim with K and POSTs it here.
// ─────────────────────────────────────────────────────────────────────────────

/// The BLAKE3 derive-key domain for the `/da/link` challenge key. **Distinct** from the in-chat
/// bot's older `"dregg-discord-link-challenge-v1"` deterministic-challenge ceremony (design §5): the
/// Activity uses the nonce'd [`webauth_core::challenge`] scheme (which fixes that ceremony's replay
/// wound), and a distinct domain keeps the two auditable apart. Also domain-separated from the ticket
/// key AND the custodial signing seed, so a compromise of one never reaches another.
pub const LINK_CHALLENGE_KEY_DOMAIN: &str = "dregg-discord-link-claim-v1";

/// The stable server key for `/da/link` challenge freshness — derived from the identity master
/// secret so it survives restarts without a separate env (see [`LINK_CHALLENGE_KEY_DOMAIN`]).
fn link_challenge_key(bot_secret: &[u8; 32]) -> [u8; 32] {
    blake3::derive_key(LINK_CHALLENGE_KEY_DOMAIN, bot_secret)
}

/// `GET /da/link/challenge` — ticket-authenticated. Returns a fresh nonce'd challenge plus the EXACT
/// fields the link_claim must bind (`platform="discord"`, the verified uid, this account's custodial
/// pubkey), so the client can build + sign the canonical [`webauth_core::link_claim`] message with
/// root key K.
async fn get_da_link_challenge(
    State(state): State<Arc<DiscordActivityState>>,
    headers: HeaderMap,
) -> Response {
    let corr = audit::correlation_id();
    let route = "GET /da/link/challenge";
    let user = match verified_user(&state, &headers, &corr, route) {
        Ok(u) => u,
        Err(resp) => return resp,
    };
    let custodial = state.identity_for(user.user_id).0;
    let challenge =
        webauth_core::challenge::issue(&link_challenge_key(&state.bot_secret), unix_now(), 300);
    audit::log().emit(
        audit::AuditEvent::new(
            "discord-activity",
            audit::Actor::custodial(user.user_id.to_string(), custodial.clone()),
            audit::Surface::Http,
            audit::Input::new(route, serde_json::Value::Null),
        )
        .correlated(&corr)
        .decided("routed", "link_challenge_issued"),
    );
    Json(serde_json::json!({
        "platform": "discord",
        "platform_uid": user.user_id.to_string(),
        "custodial_pubkey_hex": custodial,
        "challenge": challenge,
        "link_domain": webauth_core::link_claim::LINK_CLAIM_DOMAIN,
    }))
    .into_response()
}

/// The link-claim submission wire: root key K signed a [`webauth_core::link_claim`] message binding
/// (`discord`, this uid, this custodial pubkey, K, the challenge) — the client sends the root pubkey,
/// the signature, and the challenge it signed over.
#[derive(Debug, Clone, Deserialize)]
struct DaLinkForm {
    root_pubkey_hex: String,
    signature_hex: String,
    challenge: String,
}

/// `POST /da/link` — verify a root-key-signed link claim for this ticket-authenticated Discord
/// account and record `(discord custodial → root K)` in the SHARED registry. Fail-closed:
/// missing/stale/forged claim → refused, nothing recorded. On success the challenge nonce is
/// consumed (single-use) so a captured claim can't be replayed within its TTL.
async fn post_da_link(
    State(state): State<Arc<DiscordActivityState>>,
    headers: HeaderMap,
    Form(form): Form<DaLinkForm>,
) -> Response {
    let corr = audit::correlation_id();
    let route = "POST /da/link";
    let user = match verified_user(&state, &headers, &corr, route) {
        Ok(u) => u,
        Err(resp) => return resp,
    };
    let uid_str = user.user_id.to_string();
    let custodial = state.identity_for(user.user_id).0;
    let ev = |kind: &'static str, reason: &'static str| {
        audit::AuditEvent::new(
            "discord-activity",
            audit::Actor::custodial(uid_str.clone(), custodial.clone()),
            audit::Surface::Http,
            audit::Input::new(route, serde_json::Value::Null),
        )
        .correlated(&corr)
        .decided(kind, reason)
    };

    let Some(root_pubkey) = decode_hex_32(form.root_pubkey_hex.trim()) else {
        audit::log().emit(ev("refused", "bad_root_pubkey"));
        return (
            StatusCode::BAD_REQUEST,
            "root_pubkey_hex must be 64 hex chars",
        )
            .into_response();
    };
    let Some(signature) = decode_hex_64(&form.signature_hex) else {
        audit::log().emit(ev("refused", "bad_signature"));
        return (
            StatusCode::BAD_REQUEST,
            "signature_hex must be 128 hex chars",
        )
            .into_response();
    };

    match webauth_core::link_claim::verify_link_claim(
        &link_challenge_key(&state.bot_secret),
        "discord",
        &uid_str,
        &custodial,
        &root_pubkey,
        &form.challenge,
        &signature,
        unix_now(),
    ) {
        Ok(()) => {
            // Single-use: consume the challenge nonce so a captured claim can't be replayed within
            // its TTL (the contract link_claim.rs names — "record the spent challenge via replay").
            if let Some((nonce, exp)) = webauth_core::challenge::nonce_and_exp(&form.challenge) {
                if !state.link_replay.consume(nonce, exp, unix_now()) {
                    audit::log().emit(ev("refused", "challenge_replayed"));
                    return (StatusCode::FORBIDDEN, "link challenge already used").into_response();
                }
            }
            let root_hex = form.root_pubkey_hex.trim().to_lowercase();
            let recorded = webauth_core::link_registry::FileLinkStore::new(
                webauth_core::link_registry::default_store_path(),
            )
            .record(&webauth_core::link_registry::LinkRecord {
                root_pubkey_hex: root_hex.clone(),
                platform: "discord".to_string(),
                platform_uid: uid_str.clone(),
                custodial_pubkey_hex: custodial.clone(),
                verified_at: unix_now(),
            })
            .is_ok();
            audit::log().emit(ev(
                "routed",
                if recorded {
                    "linked"
                } else {
                    "linked_unrecorded"
                },
            ));
            Json(serde_json::json!({
                "ok": true,
                "root_pubkey_hex": root_hex,
                "recorded": recorded,
            }))
            .into_response()
        }
        Err(e) => {
            audit::log().emit(ev("refused", "link_claim_invalid"));
            (
                StatusCode::FORBIDDEN,
                format!("link claim did not verify: {e:?}"),
            )
                .into_response()
        }
    }
}

/// `GET /da/link` — the link-ceremony page (design §5): the `/tg/link` hardened twin, restructured
/// for the Discord iframe. Strict [`ACTIVITY_CSP`], vendored `@noble/ed25519` same-origin, no
/// external origins. The `client_id` is HTML-escaped into a `data-client-id` attribute (never inline
/// script) so the same-origin module can drive its own SDK OAuth flow to obtain a ticket.
async fn get_da_link_page(State(state): State<Arc<DiscordActivityState>>) -> Response {
    (
        [(header::CONTENT_SECURITY_POLICY, ACTIVITY_CSP)],
        Html(link_page(&state.client_id)),
    )
        .into_response()
}

/// `GET /da/link/app.js` — the link page's module, served SAME-ORIGIN so the strict CSP forbids
/// inline script (a would-be XSS or CDN swap of the K-touching code has no foothold).
async fn get_da_link_app_js() -> impl IntoResponse {
    (
        [(header::CONTENT_TYPE, "text/javascript; charset=utf-8")],
        LINK_APP_JS,
    )
}

/// `GET /da/static/noble-ed25519.js` — the vendored Ed25519 primitive (the SAME in-repo,
/// version-frozen file `/tg/link` serves), same-origin so it survives the iframe CSP (§6 — no
/// `esm.sh`, no external origin). Inside the TCB, not a third-party CDN resolution.
async fn get_da_noble_ed25519() -> impl IntoResponse {
    (
        [(header::CONTENT_TYPE, "text/javascript; charset=utf-8")],
        include_str!("../assets/noble-ed25519.js"),
    )
}

/// The link page HTML — the crate-independent inline style (Discord-blurple dark palette; inline
/// `<style>` is permitted by [`ACTIVITY_CSP`]'s `style-src 'unsafe-inline'`), the same tab/panel ids
/// the module wires, the vendored SDK as the first script, and the same-origin module. `client_id`
/// escapes into `data-client-id` on `<body>` (never into script).
fn link_page(client_id: &str) -> String {
    format!(
        r####"<!doctype html>
<html lang="en"><head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">
<title>Link your dregg identity</title>
{style}
</head><body data-client-id="{client_id}">
<h1>🔗 Link this Discord account to your dregg identity</h1>
<p class="sub">Sign a one-time claim with your <b>root key</b>. Then Discord-you and Telegram-you are
the same human on boards + leaderboards — no browser extension needed.</p>

<div id="who" class="card">Identifying you via Discord…</div>

<div class="tabs">
  <button id="tab-passkey">🔐 Passkey / passphrase</button>
  <button id="tab-relay" class="ghost">📋 Paste a signature</button>
</div>

<div id="panel-passkey" class="card">
  <div id="key-none">
    <b>No dregg key on this device yet</b>
    <p><small>Choose one — a new key is created ON this device and locked behind a passkey (or a
    passphrase). It never leaves the device unencrypted. <b>Back it up</b> after creating, or it
    lives only here.</small></p>
    <button id="do-create">✨ Create a new dregg key here</button>
    <button id="show-restore" class="ghost">↩︎ Restore a key from backup</button>
    <div id="restore-box" class="hidden">
      <textarea id="restore-seed" rows="2" placeholder="paste your backed-up key (64 hex)"></textarea>
      <button id="do-restore">↩︎ Restore &amp; link</button>
    </div>
  </div>
  <div id="key-have" class="hidden">
    <b>Unlock your dregg key &amp; link</b>
    <button id="do-unlock">🔐 Unlock &amp; link this Discord account</button>
    <button id="do-backup" class="ghost">🔑 Back up my key</button>
  </div>
  <div id="pass-fallback" class="hidden">
    <p><small>No passkey PRF on this device — using a passphrase. Pick something long + unguessable
    (≥ 12 chars); a short passphrase can be brute-forced from a stolen device.</small></p>
    <input id="passphrase" type="password" placeholder="passphrase to lock your key" autocomplete="off">
    <button id="do-passphrase">🔑 Continue with passphrase</button>
  </div>
  <div id="backup-box" class="hidden">
    <p class="warn"><small>⚠ This is your key. Anyone with it controls your identity. Save it
    somewhere only you can reach, then dismiss.</small></p>
    <div id="backup-seed" class="mono">—</div>
    <button id="backup-done" class="ghost">I saved it</button>
  </div>
</div>

<div id="panel-relay" class="card hidden">
  <b>Sign it wherever your key lives</b>
  <p><small>Enter your root public key, then sign the <b>exact bytes</b> shown with your dregg root
  key (Ed25519) and paste the signature.</small></p>
  <input id="root-hex" placeholder="root public key (64 hex)" autocomplete="off">
  <div id="msg-label" class="hidden">message to sign (hex):</div>
  <div id="msg-hex" class="mono hidden">—</div>
  <textarea id="sig-hex" rows="2" placeholder="signature (128 hex)"></textarea>
  <button id="do-relay">📋 Submit signature</button>
</div>

<div id="status" class="status"></div>

<script src="/da/static/discord-sdk.js"></script>
<script type="module" src="/da/link/app.js"></script>
</body></html>
"####,
        style = LINK_STYLE,
        client_id = crate::esc(client_id),
    )
}

/// The link page's inline style — a self-contained dark palette (Discord blurple accents) so the page
/// renders identically regardless of the catalog's `STYLE`, and every class the module toggles
/// (`.card`, `.tabs`, `.mono`, `.status`, `.ok`/`.err`/`.warn`, `.hidden`) is defined here.
const LINK_STYLE: &str = r####"<style>
  :root { color-scheme: dark; }
  body { font: 15px/1.5 system-ui, sans-serif; margin: 0; padding: 16px; background: #0e0f13; color: #e8e8ea; }
  h1 { font-size: 1.25rem; margin: .2rem 0 .1rem; }
  .sub { color: #9aa0aa; margin: 0 0 1rem; }
  .card { border: 1px solid #2a2d36; border-radius: 12px; padding: 14px; margin: 12px 0; background: #16181e; }
  button { font: inherit; font-weight: 600; width: 100%; padding: 13px; border: 0; border-radius: 10px;
           background: #5865f2; color: #fff; margin-top: 8px; cursor: pointer; }
  button.ghost { background: transparent; color: #8b93f8; border: 1px solid #5865f2; }
  button:disabled { opacity: .5; }
  textarea, input { width: 100%; box-sizing: border-box; font: 13px/1.4 ui-monospace, monospace;
                    padding: 9px; border-radius: 8px; border: 1px solid #2a2d36; background: #101218; color: inherit; }
  .mono { font: 12px/1.4 ui-monospace, monospace; word-break: break-all;
          background: #101218; padding: 8px; border-radius: 6px; }
  .status { margin-top: 10px; font-weight: 600; }
  .ok { color: #46d17f; }
  .err { color: #ff6b81; }
  .warn { color: #e0a83e; }
  .tabs { display: flex; gap: 8px; margin-bottom: 4px; }
  .tabs button { width: auto; flex: 1; padding: 9px; font-size: .9rem; }
  .hidden { display: none; }
  small { color: #9aa0aa; }
</style>"####;

/// The link page's bootstrap module — the `/tg/link` hardened module, re-graded for the Activity: the
/// identity step swaps Telegram's client-available `initData` for the Discord OAuth flow (the SDK
/// mints a code, the server exchanges it for a ticket), and the fetches carry `X-Dregg-Activity-Ticket`.
/// The three custody paths (passkey-PRF / passphrase / relay) are byte-for-byte the reviewed `/tg`
/// paths — the K-touching code is identical, only the transport around it changed. Served same-origin
/// so the strict CSP forbids inline script; `@noble/ed25519` is the vendored same-origin copy.
const LINK_APP_JS: &str = r####"import * as ed from "/da/static/noble-ed25519.js";

const clientId = (document.body && document.body.dataset) ? document.body.dataset.clientId : "";
const $ = (id) => document.getElementById(id);
const setStatus = (msg, cls) => { const s = $("status"); s.textContent = msg; s.className = "status " + (cls||""); };

const enc = new TextEncoder();
const toHex = (u8) => Array.from(u8).map(b => b.toString(16).padStart(2, "0")).join("");
const fromHex = (h) => { const s = h.trim(); if (s.length % 2) throw new Error("bad hex");
  const o = new Uint8Array(s.length/2);
  for (let i=0;i<o.length;i++){ const b = parseInt(s.slice(2*i,2*i+2),16); if (Number.isNaN(b)) throw new Error("bad hex"); o[i]=b; } return o; };
function concatBytes(...arrs){ let n=0; for(const a of arrs) n+=a.length; const o=new Uint8Array(n); let p=0;
  for(const a of arrs){ o.set(a,p); p+=a.length; } return o; }
const zero = (u8) => { if (u8) u8.fill(0); };

// The canonical link-claim message — MUST match webauth_core::link_claim::link_claim_message
// byte-for-byte: DOMAIN‖platform‖0‖uid‖0‖custodial_hex‖0‖root_hex‖0‖challenge.
function linkClaimMessage(platform, uid, custodialHex, rootHex, challenge){
  const Z = new Uint8Array([0]);
  return concatBytes(
    enc.encode("dregg-identity-link-v1:" + platform), Z,
    enc.encode(uid), Z, enc.encode(custodialHex), Z, enc.encode(rootHex), Z, enc.encode(challenge));
}

let CTX = null;    // {platform, platform_uid, custodial_pubkey_hex, challenge} from /da/link/challenge
let TICKET = null; // the server-minted activity ticket, attached to every state-touching fetch

async function jsonResponse(resp, label){
  const body = await resp.text();
  if (!resp.ok) throw new Error(label + ": HTTP " + resp.status + (body ? ": " + body.slice(0,500) : ""));
  const type = (resp.headers.get("content-type") || "").split(";",1)[0].trim().toLowerCase();
  if (type !== "application/json" && !type.endsWith("+json")) throw new Error(label + ": refused a non-JSON response");
  try { return JSON.parse(body); } catch(_){ throw new Error(label + ": malformed JSON"); }
}

// Identify via the Discord Embedded App SDK: ready → authorize → the SERVER exchanges the code with
// our client_secret and mints the ticket. The uid is asserted by Discord to the server, never the
// client. (prompt:'none' re-issues silently once consent exists — usually already granted by the shell.)
async function acquireTicket(){
  const SDKCtor = window.DiscordSDK;
  if (window.__DISCORD_SDK_PLACEHOLDER || typeof SDKCtor !== "function"){
    throw new Error("the Discord Embedded App SDK is not vendored on this build yet (serve the real bundle at /da/static/discord-sdk.js)");
  }
  const sdk = new SDKCtor(clientId);
  await sdk.ready();
  const auth = await sdk.commands.authorize({ client_id: clientId, response_type: "code", prompt: "none", scope: ["identify"] });
  const resp = await fetch("/da/token", { method: "POST", credentials:"same-origin", cache:"no-store",
    headers: { "Content-Type": "application/json", "Accept":"application/json" }, body: JSON.stringify({ code: auth.code }) });
  const data = await jsonResponse(resp, "token exchange failed");
  if (data.access_token){ try { await sdk.commands.authenticate({ access_token: data.access_token }); } catch(e){ /* handshake best-effort */ } }
  return data.ticket;
}

async function fetchChallenge(){
  const r = await fetch("/da/link/challenge", { credentials:"same-origin", cache:"no-store",
    headers: { "X-Dregg-Activity-Ticket": TICKET, "Accept":"application/json" } });
  return await jsonResponse(r, "challenge");
}
async function submit(rootHex, sigHex){
  const body = new URLSearchParams({ root_pubkey_hex: rootHex, signature_hex: sigHex, challenge: CTX.challenge });
  const r = await fetch("/da/link", { method: "POST",
    credentials:"same-origin", cache:"no-store",
    headers: { "X-Dregg-Activity-Ticket": TICKET, "content-type": "application/x-www-form-urlencoded", "Accept":"application/json" },
    body: body.toString() });
  return await jsonResponse(r, "link refused");
}

// ── Custody of the root key K (seed wrapped in localStorage; NEVER auto-minted) ──
const LS_KEY = "dregg_root_k_v1";
const PRF_SALT = new Uint8Array(await crypto.subtle.digest("SHA-256", enc.encode("dregg-link-prf-v1")));

async function aesFromRaw(raw){
  const base = await crypto.subtle.importKey("raw", raw, "HKDF", false, ["deriveKey"]);
  return crypto.subtle.deriveKey(
    { name:"HKDF", hash:"SHA-256", salt: PRF_SALT, info: enc.encode("dregg-link-wrap-v1") },
    base, { name:"AES-GCM", length:256 }, false, ["encrypt","decrypt"]);
}
async function aesFromPassphrase(pass, salt){
  const base = await crypto.subtle.importKey("raw", enc.encode(pass), "PBKDF2", false, ["deriveKey"]);
  return crypto.subtle.deriveKey({ name:"PBKDF2", salt, iterations:600000, hash:"SHA-256" },
    base, { name:"AES-GCM", length:256 }, false, ["encrypt","decrypt"]);
}

class NoPrf extends Error {}          // PRF genuinely unsupported here → offer passphrase
class PkFailed extends Error {}       // passkey cancelled/failed → RETRY, never downgrade

async function prfSecret(create){
  let cred;
  try {
    const opts = create ? {
      publicKey: { challenge: crypto.getRandomValues(new Uint8Array(32)),
        rp:{ name:"dregg" }, user:{ id: crypto.getRandomValues(new Uint8Array(16)), name:"dregg", displayName:"dregg" },
        pubKeyCredParams:[{type:"public-key",alg:-7},{type:"public-key",alg:-257}],
        authenticatorSelection:{ residentKey:"required", userVerification:"required" },
        extensions:{ prf:{ eval:{ first: PRF_SALT } } } } }
    : { publicKey: { challenge: crypto.getRandomValues(new Uint8Array(32)), userVerification:"required",
        extensions:{ prf:{ eval:{ first: PRF_SALT } } } } };
    cred = create ? await navigator.credentials.create(opts) : await navigator.credentials.get(opts);
  } catch(e){
    if (e && (e.name === "NotSupportedError")) throw new NoPrf();
    if (!window.PublicKeyCredential) throw new NoPrf();
    throw new PkFailed(e && e.name ? e.name : String(e));
  }
  const res = cred.getClientExtensionResults();
  if (res && res.prf && res.prf.results && res.prf.results.first) return new Uint8Array(res.prf.results.first);
  throw new NoPrf();
}

function storeWrapped(mode, iv, ct, salt){
  localStorage.setItem(LS_KEY, JSON.stringify({ mode, iv:toHex(iv), ct:toHex(ct), ...(salt?{salt:toHex(salt)}:{}) })); }
async function wrapSeed(aes, seed){
  const iv = crypto.getRandomValues(new Uint8Array(12));
  const ct = new Uint8Array(await crypto.subtle.encrypt({name:"AES-GCM", iv}, aes, seed));
  return { iv, ct };
}
async function unwrapSeed(aes, rec){
  const seed = await crypto.subtle.decrypt({name:"AES-GCM", iv:fromHex(rec.iv)}, aes, fromHex(rec.ct));
  return new Uint8Array(seed);
}

// Sign a fresh CTX claim with an in-memory seed, then zeroize it.
async function signAndLink(seed){
  let rootHex, msg;
  try {
    rootHex = toHex(await ed.getPublicKeyAsync(seed));
    msg = linkClaimMessage(CTX.platform, CTX.platform_uid, CTX.custodial_pubkey_hex, rootHex, CTX.challenge);
    setStatus("submitting…");
    const sig = await ed.signAsync(msg, seed);
    await submit(rootHex, toHex(sig));
  } finally { zero(seed); }
  setStatus("✅ Linked! Discord-you is now bound to your root key — one human across platforms.", "ok");
}

// Explicit CREATE — never auto-minted. Wrap under passkey-PRF (or passphrase), then link.
async function createOrUnlock(create){
  let prf;
  try { prf = await prfSecret(create); }
  catch(e){
    if (e instanceof NoPrf){ $("pass-fallback").classList.remove("hidden");
      setStatus("no passkey PRF here — set a passphrase below.", "warn"); return; }
    if (e instanceof PkFailed){ setStatus("✗ passkey " + e.message + " — tap again to retry (not falling back).", "err"); return; }
    throw e;
  }
  const aes = await aesFromRaw(prf.slice(0,32)); zero(prf);
  const rec = localStorage.getItem(LS_KEY);
  let seed;
  if (rec){
    const r = JSON.parse(rec);
    if (r.mode !== "prf"){ setStatus("this device's key is passphrase-locked — use the passphrase.", "err"); return; }
    seed = await unwrapSeed(aes, r);
  } else {
    seed = ed.utils.randomPrivateKey();
    const { iv, ct } = await wrapSeed(aes, seed);
    storeWrapped("prf", iv, ct);
  }
  await signAndLink(seed);
}
async function passphrasePath(pass){
  const rec = localStorage.getItem(LS_KEY);
  let seed;
  if (rec){
    const r = JSON.parse(rec);
    if (r.mode !== "pass") throw new Error("this device's key is passkey-locked, not passphrase");
    seed = await unwrapSeed(await aesFromPassphrase(pass, fromHex(r.salt)), r);
  } else {
    const salt = crypto.getRandomValues(new Uint8Array(16));
    seed = ed.utils.randomPrivateKey();
    const { iv, ct } = await wrapSeed(await aesFromPassphrase(pass, salt), seed);
    storeWrapped("pass", iv, ct, salt);
  }
  await signAndLink(seed);
}

// ── UI wiring ──
function haveKey(){ return !!localStorage.getItem(LS_KEY); }
function refreshKeyPanel(){
  $("key-none").classList.toggle("hidden", haveKey());
  $("key-have").classList.toggle("hidden", !haveKey());
}
$("tab-passkey").onclick = () => { $("panel-passkey").classList.remove("hidden"); $("panel-relay").classList.add("hidden");
  $("tab-passkey").classList.remove("ghost"); $("tab-relay").classList.add("ghost"); refreshKeyPanel(); };
$("tab-relay").onclick = () => { $("panel-relay").classList.remove("hidden"); $("panel-passkey").classList.add("hidden");
  $("tab-relay").classList.remove("ghost"); $("tab-passkey").classList.add("ghost"); };

$("do-create").onclick    = () => createOrUnlock(true).catch(e => setStatus("✗ " + e.message, "err"));
$("do-unlock").onclick    = () => createOrUnlock(false).catch(e => setStatus("✗ " + e.message, "err"));
$("show-restore").onclick = () => $("restore-box").classList.toggle("hidden");
$("do-restore").onclick   = async () => {
  try { const seed = fromHex($("restore-seed").value);
    if (seed.length !== 32) throw new Error("a backed-up key is 64 hex chars");
    $("pass-fallback").classList.remove("hidden");
    setStatus("set a passphrase to lock the restored key, then Continue.", "warn");
    window.__restoreSeed = seed;
  } catch(e){ setStatus("✗ " + e.message, "err"); }
};
$("do-passphrase").onclick = async () => {
  try {
    const pass = $("passphrase").value;
    if (pass.length < 12){ setStatus("passphrase needs ≥ 12 characters (longer is safer).", "err"); return; }
    if (window.__restoreSeed){
      const salt = crypto.getRandomValues(new Uint8Array(16));
      const { iv, ct } = await wrapSeed(await aesFromPassphrase(pass, salt), window.__restoreSeed);
      storeWrapped("pass", iv, ct, salt);
      const seed = window.__restoreSeed; window.__restoreSeed = null;
      await signAndLink(seed);
    } else { await passphrasePath(pass); }
  } catch(e){ setStatus("✗ " + e.message, "err"); }
};
$("do-backup").onclick = async () => {
  setStatus("Unlock to reveal your key…", "warn");
  try {
    const r = JSON.parse(localStorage.getItem(LS_KEY));
    let aes;
    if (r.mode === "prf"){ const prf = await prfSecret(false); aes = await aesFromRaw(prf.slice(0,32)); zero(prf); }
    else { const p = prompt("passphrase to reveal your key"); if (!p) return; aes = await aesFromPassphrase(p, fromHex(r.salt)); }
    const seed = await unwrapSeed(aes, r);
    $("backup-seed").textContent = toHex(seed); zero(seed);
    $("backup-box").classList.remove("hidden"); setStatus("");
  } catch(e){ setStatus("✗ " + (e.message||e), "err"); }
};
$("backup-done").onclick = () => { $("backup-seed").textContent = "—"; $("backup-box").classList.add("hidden"); };

function relayMsgHex(){
  const rootHex = $("root-hex").value.trim().toLowerCase();
  if (rootHex.length === 64 && CTX){
    $("msg-label").classList.remove("hidden"); $("msg-hex").classList.remove("hidden");
    $("msg-hex").textContent = toHex(linkClaimMessage(CTX.platform, CTX.platform_uid, CTX.custodial_pubkey_hex, rootHex, CTX.challenge));
  } else { $("msg-label").classList.add("hidden"); $("msg-hex").classList.add("hidden"); }
}
$("root-hex").addEventListener("input", relayMsgHex);
$("do-relay").onclick = async () => {
  try {
    const rootHex = $("root-hex").value.trim().toLowerCase();
    const sigHex = $("sig-hex").value.trim().toLowerCase();
    if (rootHex.length !== 64 || sigHex.length !== 128){ setStatus("root pubkey must be 64 hex, signature 128 hex.", "err"); return; }
    setStatus("submitting…"); await submit(rootHex, sigHex);
    setStatus("✅ Linked! Discord-you is now bound to your root key — one human across platforms.", "ok");
  } catch(e){ setStatus("✗ " + e.message, "err"); }
};

// boot: identify via the SDK to obtain a ticket, then fetch the challenge that binds this uid.
(async () => {
  try {
    TICKET = await acquireTicket();
  } catch(e){
    const error = document.createElement("span");
    error.className = "err";
    error.textContent = "Could not identify you via Discord: " + (e.message||e) +
      " — the link ceremony needs the Activity SDK to prove which Discord account you are.";
    $("who").replaceChildren(error);
    return;
  }
  try {
    CTX = await fetchChallenge();
    const label = document.createTextNode("Discord ");
    const uid = document.createElement("b");
    uid.textContent = "#" + CTX.platform_uid;
    const suffix = document.createTextNode(" · this account's dregg key:");
    const key = document.createElement("div");
    key.className = "mono";
    key.textContent = CTX.custodial_pubkey_hex;
    $("who").replaceChildren(label, uid, suffix, key);
    refreshKeyPanel();
  } catch(e){
    const error = document.createElement("span");
    error.className = "err";
    error.textContent = e.message || String(e);
    $("who").replaceChildren(error);
  }
})();
"####;

#[cfg(test)]
mod tests {
    use super::*;
    use dreggnet_discord_identity::seed_for;
    use dreggnet_offerings::TurnSigner;

    const NONCE: &[u8] = &[0xAB; 16];

    fn key() -> [u8; 32] {
        ticket_key(&[42u8; 32])
    }

    // ── Family (i): the vector accepts; every tamper class refuses, named. ──

    #[test]
    fn a_correctly_hmacd_ticket_is_accepted_with_the_exact_uid() {
        let k = key();
        let ticket = mint_ticket(&k, 42_424_242, 1_760_000_000, NONCE);
        let u = validate_ticket_at(&k, &ticket, 1_760_000_100, 86_400)
            .expect("the genuine ticket validates");
        assert_eq!(u.user_id, 42_424_242);
        assert_eq!(u.minted_at, 1_760_000_000);
    }

    /// Decode a minted ticket to raw bytes, so a tamper test can mutate one byte and re-seal the
    /// (now-wrong) envelope.
    fn decode(ticket: &str) -> Vec<u8> {
        URL_SAFE_NO_PAD
            .decode(ticket.as_bytes())
            .expect("mint emits valid base64url")
    }
    fn encode(bytes: &[u8]) -> String {
        URL_SAFE_NO_PAD.encode(bytes)
    }

    #[test]
    fn every_tamper_class_is_refused_by_its_named_gate() {
        let k = key();
        let minted = 1_760_000_000u64;
        let now = minted + 100;
        let ticket = mint_ticket(&k, 42, minted, NONCE);

        // TAMPERED HMAC: flip the last byte (in the sealed tag) → BadHmac (403).
        let mut b = decode(&ticket);
        let last = b.len() - 1;
        b[last] ^= 0x01;
        let e = validate_ticket_at(&k, &encode(&b), now, 86_400).unwrap_err();
        assert_eq!(e, TicketError::BadHmac);
        assert_eq!(e.http_status(), StatusCode::FORBIDDEN);

        // FORGED UID: flip a uid byte, keep the genuine tag → BadHmac (the HMAC covers the uid; a
        // client-claimed uid without a valid tag is refused — the hard rule).
        let mut b = decode(&ticket);
        b[0] ^= 0xFF;
        assert_eq!(
            validate_ticket_at(&k, &encode(&b), now, 86_400).unwrap_err(),
            TicketError::BadHmac
        );

        // TAMPERED NONCE: mutate a nonce byte (index 16 = first nonce byte), keep the tag → BadHmac
        // (the HMAC covers the nonce too).
        let mut b = decode(&ticket);
        b[16] ^= 0xFF;
        assert_eq!(
            validate_ticket_at(&k, &encode(&b), now, 86_400).unwrap_err(),
            TicketError::BadHmac
        );

        // WRONG KEY: a genuine ticket under another ticket_key → BadHmac here.
        let other = mint_ticket(&ticket_key(&[7u8; 32]), 42, minted, NONCE);
        assert_eq!(
            validate_ticket_at(&k, &other, now, 86_400).unwrap_err(),
            TicketError::BadHmac
        );

        // TRUNCATED below the fixed fields → MalformedLength (400), before any comparison.
        let short = encode(&decode(&ticket)[..MIN_TICKET_LEN - 1]);
        let e = validate_ticket_at(&k, &short, now, 86_400).unwrap_err();
        assert_eq!(e, TicketError::MalformedLength);
        assert_eq!(e.http_status(), StatusCode::BAD_REQUEST);

        // TRUNCATED but still ≥ MIN_TICKET_LEN → BadHmac. Chopping the tail re-splits the envelope
        // (the validator now reads the nonce bytes as part of the 32-byte tag and treats only
        // uid‖minted_at as the payload), and the HMAC over that shorter payload cannot match.
        let mut b = decode(&ticket);
        b.truncate(MIN_TICKET_LEN);
        assert_eq!(
            validate_ticket_at(&k, &encode(&b), now, 86_400).unwrap_err(),
            TicketError::BadHmac
        );

        // NON-BASE64URL string → MalformedEncoding (400).
        let e = validate_ticket_at(&k, "not!valid!base64url", now, 86_400).unwrap_err();
        assert_eq!(e, TicketError::MalformedEncoding);
        assert_eq!(e.http_status(), StatusCode::BAD_REQUEST);

        // EMPTY string decodes to zero bytes → MalformedLength (400).
        assert_eq!(
            validate_ticket_at(&k, "", now, 86_400).unwrap_err(),
            TicketError::MalformedLength
        );

        // STALE: a GENUINE ticket past the window → Stale (403). Both polarities: at the window
        // edge it still validates.
        let e = validate_ticket_at(&k, &ticket, minted + 86_401, 86_400).unwrap_err();
        assert!(matches!(e, TicketError::Stale { .. }), "{e:?}");
        assert_eq!(e.http_status(), StatusCode::FORBIDDEN);
        validate_ticket_at(&k, &ticket, minted + 86_400, 86_400)
            .expect("exactly at the window edge is still fresh");

        // FUTURE: minted_at beyond the 300s skew guard → FromFuture (403); within it, accepted.
        let future = mint_ticket(&k, 42, minted + 400, NONCE);
        let e = validate_ticket_at(&k, &future, minted, 86_400).unwrap_err();
        assert!(matches!(e, TicketError::FromFuture { .. }), "{e:?}");
        let near_future = mint_ticket(&k, 42, minted + 200, NONCE);
        validate_ticket_at(&k, &near_future, minted, 86_400)
            .expect("within the skew guard is accepted");
    }

    // ── Family (ii): identity parity — the ticket's uid derives the in-chat player's key. ──

    /// **The parity pin — web side.** The extracted [`seed_for`] must remain the historical
    /// `BLAKE3_derive_key("dregg-discord-bot-v1", secret ‖ uid_le)`; the pinned algorithm is
    /// recomputed inline from the LITERAL domain + byte layout, so a drift in the shared
    /// `dreggnet-discord-identity` crate diverges from this and fails HERE (the web Activity side).
    /// Its twin lives in `discord-bot/src/cipherclerk.rs`, hardcoding the same literal on the
    /// in-chat side — one seed, pinned from both callers.
    #[test]
    fn the_shared_seed_derivation_is_pinned_byte_for_byte() {
        let secret = [42u8; 32];
        let uid = 555_000_111u64;
        let mut input = Vec::new();
        input.extend_from_slice(&secret);
        input.extend_from_slice(&uid.to_le_bytes());
        let expected = blake3::derive_key("dregg-discord-bot-v1", &input);
        assert_eq!(
            seed_for(&secret, uid),
            expected,
            "the Activity surface derives the SAME seed the in-chat bot does"
        );
        // And the identity the Activity signer lands turns under is that seed's Ed25519 pubkey hex.
        let ident = TurnSigner::from_seed(seed_for(&secret, uid)).identity();
        assert_eq!(ident.0.len(), 64, "ed25519 pubkey hex is 64 chars");
    }

    #[test]
    fn the_verified_uid_derives_the_custodial_identity() {
        let bot_secret = [42u8; 32];
        let uid = 42_424_242u64;
        let k = ticket_key(&bot_secret);
        // End-to-end: a genuine ticket's recovered uid derives the custodial signer identity, and
        // re-deriving from the same uid is stable (reproducible custodial keys).
        let ticket = mint_ticket(&k, uid, 1_760_000_000, NONCE);
        let verified = validate_ticket_at(&k, &ticket, 1_760_000_100, 86_400).unwrap();
        let ident_a = TurnSigner::from_seed(seed_for(&bot_secret, verified.user_id)).identity();
        let ident_b = TurnSigner::from_seed(seed_for(&bot_secret, uid)).identity();
        assert_eq!(ident_a, ident_b);
    }

    // ── Family (iii): the ticket key is domain-separated from the signing seed. ──

    #[test]
    fn ticket_key_is_deterministic_and_domain_separated_from_the_signing_seed() {
        let secret = [9u8; 32];
        assert_eq!(ticket_key(&secret), ticket_key(&secret));
        assert_ne!(ticket_key(&[1u8; 32]), ticket_key(&[2u8; 32]));
        // The ticket key is NOT the custodial signing seed for any uid derived from the same secret
        // (different BLAKE3 domains), so a ticket-key compromise never yields a signing key.
        assert_ne!(ticket_key(&secret), seed_for(&secret, 0));
        assert_ne!(ticket_key(&secret), seed_for(&secret, 12345));
        assert_eq!(
            ACTIVITY_TICKET_KEY_DOMAIN,
            "dregg-discord-activity-ticket-v1"
        );
    }

    // ── Family (iv): the OAuth token-response parsers — the parts that need NO live Discord. ──

    #[test]
    fn the_token_and_user_json_parsers_read_the_pinned_shapes() {
        // A Discord oauth2/token response — the access_token is read out.
        let tok = r#"{"access_token":"abc123","token_type":"Bearer","expires_in":604800,"scope":"identify"}"#;
        assert_eq!(parse_access_token(tok).as_deref(), Some("abc123"));
        assert_eq!(parse_access_token(r#"{"error":"invalid_grant"}"#), None);
        // A users/@me response — id is a snowflake STRING, parsed to u64; username is optional.
        let me = r#"{"id":"42424242","username":"emberian","global_name":"Ember","avatar":null}"#;
        assert_eq!(
            parse_user_me(me),
            Some((42_424_242u64, Some("emberian".to_string())))
        );
        // A non-numeric / missing id refuses.
        assert_eq!(parse_user_me(r#"{"username":"x"}"#), None);
        assert_eq!(parse_user_me(r#"{"id":"not-a-number"}"#), None);
    }

    // ── Family (v): route-level — the shell serves, the ticket gate refuses, the token path mints. ──

    use axum::body::Body;
    use axum::http::Request;
    use dungeon_on_dregg::KP_PRESS_ON;
    use tower::ServiceExt; // oneshot

    /// The fixture identity master secret (never a real one). Same value the pure-fn tests use.
    const BOT_SECRET: [u8; 32] = [42u8; 32];

    /// A stub code-exchange backend: it asserts a fixed uid without any live Discord app or secret,
    /// so the whole `/da/token` → mint → ticket-gated-catalog flow is exercised deterministically.
    struct StubExchange {
        uid: u64,
    }
    impl DiscordTokenExchange for StubExchange {
        fn exchange(
            &self,
            _client_id: &str,
            _client_secret: &str,
            _code: &str,
        ) -> Result<DiscordCodeExchange, OAuthError> {
            Ok(DiscordCodeExchange {
                user_id: self.uid,
                access_token: "stub-access-token".to_string(),
                username: Some("emberian".to_string()),
            })
        }
    }

    fn test_state(uid: u64) -> (Arc<DiscordActivityState>, Arc<CatalogState>) {
        let catalog = Arc::new(CatalogState::new());
        let state = Arc::new(DiscordActivityState::with_oauth(
            Arc::clone(&catalog),
            "1234567890",
            "test-client-secret",
            BOT_SECRET,
            86_400,
            Arc::new(StubExchange { uid }),
        ));
        (state, catalog)
    }

    async fn send(
        app: &Router,
        method: &str,
        uri: &str,
        ticket: Option<&str>,
        content_type: Option<&str>,
        body: Option<&str>,
    ) -> (StatusCode, String) {
        let mut req = Request::builder().method(method).uri(uri);
        if let Some(t) = ticket {
            req = req.header(ACTIVITY_TICKET_HEADER, t);
        }
        if let Some(ct) = content_type {
            req = req.header("content-type", ct);
        }
        let b = match body {
            Some(s) => Body::from(s.to_string()),
            None => Body::empty(),
        };
        let resp = app.clone().oneshot(req.body(b).unwrap()).await.unwrap();
        let status = resp.status();
        let bytes = axum::body::to_bytes(resp.into_body(), usize::MAX)
            .await
            .unwrap();
        (status, String::from_utf8(bytes.to_vec()).unwrap())
    }

    fn game_authority_fields(fragment: &str) -> String {
        fn value(fragment: &str, name: &str) -> String {
            let marker = format!("name=\"{name}\" value=\"");
            fragment
                .split_once(&marker)
                .and_then(|(_, tail)| tail.split_once('\"'))
                .map(|(value, _)| value.to_string())
                .unwrap_or_else(|| panic!("missing {name} in game fragment"))
        }
        [
            "game_host_incarnation",
            "game_session_generation",
            "game_expected_pre_head",
            "game_form_token",
        ]
        .into_iter()
        .map(|name| format!("{name}={}", value(fragment, name)))
        .collect::<Vec<_>>()
        .join("&")
    }

    #[tokio::test(flavor = "multi_thread")]
    async fn get_da_serves_the_shell_with_a_strict_csp_and_the_sdk_wiring() {
        let (state, _catalog) = test_state(1);
        let app = discord_activity_router(state);

        // The shell serves without auth (it is just a page), with the strict CSP header.
        let resp = app
            .clone()
            .oneshot(
                Request::builder()
                    .method("GET")
                    .uri("/da")
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap();
        assert_eq!(resp.status(), StatusCode::OK);
        let csp = resp
            .headers()
            .get("content-security-policy")
            .expect("the shell ships a CSP header")
            .to_str()
            .unwrap()
            .to_string();
        assert!(csp.contains("script-src 'self'"), "{csp}");
        assert!(csp.contains("connect-src 'self'"), "{csp}");
        assert!(csp.contains("frame-ancestors"), "{csp}");
        let bytes = axum::body::to_bytes(resp.into_body(), usize::MAX)
            .await
            .unwrap();
        let body = String::from_utf8(bytes.to_vec()).unwrap();
        assert!(body.contains("/da/static/discord-sdk.js"), "{body}");
        assert!(body.contains("/da/static/app.js"), "{body}");
        assert!(body.contains("data-client-id=\"1234567890\""), "{body}");
        // No external SDK origin (design §6 — everything same-origin).
        assert!(!body.contains("esm.sh"));

        // The same-origin module carries the pinned flow: authorize → /da/token → ticket header.
        let (st, appjs) = send(&app, "GET", "/da/static/app.js", None, None, None).await;
        assert_eq!(st, StatusCode::OK);
        assert!(appjs.contains("X-Dregg-Activity-Ticket"), "{appjs}");
        assert!(appjs.contains("/da/token"), "{appjs}");
        assert!(appjs.contains("authorize"), "{appjs}");
        assert!(appjs.contains("scope"), "{appjs}");
        assert!(appjs.contains("body: file"), "{appjs}");
        assert!(
            !appjs.contains("new URLSearchParams(new FormData(form))"),
            "{appjs}"
        );
        assert!(
            appjs.contains("box.textContent = String(message)"),
            "{appjs}"
        );
        assert!(appjs.contains("if (!resp.ok)"), "{appjs}");
        assert!(
            appjs.contains("Refused a non-HTML fragment response"),
            "{appjs}"
        );
    }

    #[tokio::test(flavor = "multi_thread")]
    async fn a_ticket_gated_handler_refuses_a_missing_ticket() {
        let (state, catalog) = test_state(7);
        let app = discord_activity_router(state);

        // GET /da/offerings with NO ticket → 401 (the anti-ghost gate).
        let (st, _) = send(&app, "GET", "/da/offerings", None, None, None).await;
        assert_eq!(st, StatusCode::UNAUTHORIZED);

        // GET a session with NO ticket → 401 (no cold-deep-link soft path on /da).
        let (st, _) = send(
            &app,
            "GET",
            "/da/offerings/dungeon/session/da-x",
            None,
            None,
            None,
        )
        .await;
        assert_eq!(st, StatusCode::UNAUTHORIZED);

        // POST act with a VALID form body but NO ticket → 401 (the Form extracts, then the gate
        // refuses — a body-shaped 415 would be the wrong signal, so the body/content-type are sent).
        let (st, _) = send(
            &app,
            "POST",
            "/da/offerings/dungeon/session/da-x/act",
            None,
            Some("application/x-www-form-urlencoded"),
            Some(&format!("turn=choose&arg={}", KP_PRESS_ON)),
        )
        .await;
        assert_eq!(st, StatusCode::UNAUTHORIZED);

        // ANTI-GHOST GROUND TRUTH: none of the refusals opened the session.
        assert!(
            !catalog.is_open("dungeon", &SessionId::new("da-x")),
            "a refused request opens no session"
        );
    }

    #[tokio::test(flavor = "multi_thread")]
    async fn da_token_mints_a_ticket_the_gate_accepts_and_the_uid_derives_the_custodial_identity() {
        let uid = 42_424_242u64;
        let (state, _catalog) = test_state(uid);
        let app = discord_activity_router(state);

        // POST /da/token {code} → { access_token, ticket, custodial_pubkey_hex } via the stub.
        let (st, body) = send(
            &app,
            "POST",
            "/da/token",
            None,
            Some("application/json"),
            Some(r#"{"code":"stub-code"}"#),
        )
        .await;
        assert_eq!(st, StatusCode::OK, "{body}");
        let v: serde_json::Value = serde_json::from_str(&body).unwrap();
        assert_eq!(
            v.get("access_token").and_then(|x| x.as_str()),
            Some("stub-access-token")
        );
        let ticket = v
            .get("ticket")
            .and_then(|x| x.as_str())
            .unwrap()
            .to_string();
        let custodial = v
            .get("custodial_pubkey_hex")
            .and_then(|x| x.as_str())
            .unwrap()
            .to_string();

        // The minted ticket validates to the stub uid under the state's ticket key.
        let verified =
            validate_ticket_at(&ticket_key(&BOT_SECRET), &ticket, unix_now() + 1, 86_400).unwrap();
        assert_eq!(verified.user_id, uid);
        // And custodial_pubkey_hex IS the identity the in-chat bot derives for that uid.
        let expected = TurnSigner::from_seed(seed_for(&BOT_SECRET, uid))
            .identity()
            .0;
        assert_eq!(custodial, expected);

        // The minted ticket now GATES the catalog: GET /da/offerings names the verified identity.
        let (st, cat) = send(&app, "GET", "/da/offerings", Some(&ticket), None, None).await;
        assert_eq!(st, StatusCode::OK, "{cat}");
        assert!(
            cat.contains(&expected[..16]),
            "the listing names the verified identity: {cat}"
        );
    }

    // ── The /da/token outbound-exchange RATE guard (self-DoS closure). ──
    //
    // FLAW: the concurrency semaphore releases each permit on return, so a SEQUENTIAL stream of
    // fast-failing bad codes reaches the outbound Discord exchange once per request — a self-DoS on
    // the app's shared OAuth client. The guard adds a RATE bound (token bucket) + a negative-code
    // short-circuit BEFORE the outbound call. These canaries pin that the outbound `exchange` is not
    // reached past the bucket.

    use std::sync::atomic::AtomicUsize;

    /// A code-exchange stub that COUNTS calls and always reports a Discord-rejected code — so a test
    /// can assert exactly how many requests reached the outbound exchange.
    struct CountingRejectExchange {
        calls: Arc<AtomicUsize>,
    }
    impl DiscordTokenExchange for CountingRejectExchange {
        fn exchange(
            &self,
            _client_id: &str,
            _client_secret: &str,
            _code: &str,
        ) -> Result<DiscordCodeExchange, OAuthError> {
            self.calls.fetch_add(1, Ordering::SeqCst);
            Err(OAuthError::TokenStatus(401))
        }
    }

    /// Build a `/da/token` app over the counting stub with an EXPLICIT guard config, returning the
    /// call counter so a canary can read how many requests reached the outbound exchange.
    fn rate_guard_app(guard: DaTokenGuardConfig) -> (Router, Arc<AtomicUsize>) {
        let catalog = Arc::new(CatalogState::new());
        let calls = Arc::new(AtomicUsize::new(0));
        let state = Arc::new(DiscordActivityState::with_oauth_and_guard(
            Arc::clone(&catalog),
            "1234567890",
            "test-client-secret",
            BOT_SECRET,
            86_400,
            Arc::new(CountingRejectExchange {
                calls: Arc::clone(&calls),
            }),
            guard,
        ));
        (discord_activity_router(state), calls)
    }

    async fn post_token(app: &Router, code: &str) -> StatusCode {
        let (st, _body) = send(
            app,
            "POST",
            "/da/token",
            None,
            Some("application/json"),
            Some(&format!(r#"{{"code":"{code}"}}"#)),
        )
        .await;
        st
    }

    /// CANARY — sustained bad codes are capped by RATE (a fast `429`), and the outbound exchange is
    /// NOT reached past the token bucket.
    ///
    /// Guard: per-source burst 2, zero refill, wide-open global — so exactly the first 2 SEQUENTIAL
    /// requests may reach the outbound call; the rest are refused by rate. Codes are all DISTINCT so
    /// the negative cache never short-circuits — this isolates the RATE bucket as the thing firing.
    ///
    /// FAIL-BEFORE (old concurrency-only code): with no rate bucket, every sequential request would
    /// acquire-then-release a permit and reach the exchange → `calls == 6` (≠ 2) and every status
    /// `401` (never `429`). Both assertions below are therefore RED on the old code and GREEN on the
    /// fixed code — the mutation the guard is load-bearing for. (Established by reasoning, not
    /// `git stash`: stashing the working tree is not swarm-safe here, and the companion test
    /// `da_token_without_a_rate_cap_reaches_the_outbound_on_every_sequential_request` empirically
    /// reproduces the `calls == 6` old behavior by opening the burst wide.)
    #[tokio::test(flavor = "multi_thread")]
    async fn da_token_caps_the_outbound_exchange_by_rate_not_concurrency() {
        let guard = DaTokenGuardConfig {
            per_source_burst: 2.0,
            per_source_refill_per_sec: 0.0,
            global_burst: 1_000.0,
            global_refill_per_sec: 0.0,
            neg_cache_ttl_secs: 30,
            max_sources: 4096,
        };
        let (app, calls) = rate_guard_app(guard);

        let mut statuses = Vec::new();
        for i in 0..6 {
            statuses.push(post_token(&app, &format!("bad-{i}")).await);
        }

        // Exactly the burst (2) reached the outbound exchange; the rest never did.
        assert_eq!(
            calls.load(Ordering::SeqCst),
            2,
            "only the burst of 2 may reach the outbound Discord exchange; the flood must not"
        );
        // The first 2 pass the bucket (and get the stub's 401); requests 3..6 are refused by RATE.
        assert_eq!(
            statuses,
            vec![
                StatusCode::UNAUTHORIZED,
                StatusCode::UNAUTHORIZED,
                StatusCode::TOO_MANY_REQUESTS,
                StatusCode::TOO_MANY_REQUESTS,
                StatusCode::TOO_MANY_REQUESTS,
                StatusCode::TOO_MANY_REQUESTS,
            ],
            "sustained bad codes are 429'd by RATE past the bucket, not served"
        );
    }

    /// The companion that empirically reproduces the OLD (pre-fix) self-DoS: with the burst opened
    /// wide (so the RATE bucket never fires) every sequential request reaches the outbound exchange —
    /// `calls == 6`. This is exactly what the concurrency-only semaphore allowed, and precisely what
    /// the canary above caps at 2. Together they show the `429`s above come from the RATE cap.
    #[tokio::test(flavor = "multi_thread")]
    async fn da_token_without_a_rate_cap_reaches_the_outbound_on_every_sequential_request() {
        let guard = DaTokenGuardConfig {
            per_source_burst: 1_000.0,
            per_source_refill_per_sec: 0.0,
            global_burst: 1_000.0,
            global_refill_per_sec: 0.0,
            neg_cache_ttl_secs: 30,
            max_sources: 4096,
        };
        let (app, calls) = rate_guard_app(guard);

        for i in 0..6 {
            assert_eq!(
                post_token(&app, &format!("bad-{i}")).await,
                StatusCode::UNAUTHORIZED
            );
        }
        assert_eq!(
            calls.load(Ordering::SeqCst),
            6,
            "with the rate cap opened wide every sequential bad code reaches the outbound exchange \
             — the self-DoS the rate bucket closes"
        );
    }

    /// The negative-code cache short-circuits a REPLAYED already-rejected code with no outbound call:
    /// the same bad code sent 4 times reaches the exchange exactly once, the rest short-circuit to a
    /// fast `401`. (Burst opened wide so the rate bucket is not what is firing here.)
    #[tokio::test(flavor = "multi_thread")]
    async fn da_token_negative_cache_short_circuits_a_replayed_bad_code() {
        let guard = DaTokenGuardConfig {
            per_source_burst: 1_000.0,
            per_source_refill_per_sec: 0.0,
            global_burst: 1_000.0,
            global_refill_per_sec: 0.0,
            neg_cache_ttl_secs: 30,
            max_sources: 4096,
        };
        let (app, calls) = rate_guard_app(guard);

        for _ in 0..4 {
            assert_eq!(
                post_token(&app, "same-bad-code").await,
                StatusCode::UNAUTHORIZED
            );
        }
        assert_eq!(
            calls.load(Ordering::SeqCst),
            1,
            "a replayed rejected code reaches the outbound exchange once, then short-circuits"
        );
    }

    #[tokio::test(flavor = "multi_thread")]
    async fn a_da_post_lands_a_verified_signed_turn() {
        let uid = 42_424_242u64;
        let (state, catalog) = test_state(uid);
        let app = discord_activity_router(state);
        let expected_ident = TurnSigner::from_seed(seed_for(&BOT_SECRET, uid)).identity();

        // A fresh ticket, minted the way /da/token mints it.
        let ticket = mint_ticket(&ticket_key(&BOT_SECRET), uid, unix_now(), NONCE);

        // Open the session as the verified viewer.
        let sid = "da-e2e-1";
        let uri = format!("/da/offerings/dungeon/session/{sid}");
        let (st, opened) = send(&app, "GET", &uri, Some(&ticket), None, None).await;
        assert_eq!(st, StatusCode::OK);
        let routed_epoch = catalog
            .bound_game_session("dungeon", &SessionId::new(sid))
            .expect("Activity GET binds the shared renderer to a live game epoch");

        // POST one turn: it lands through the common game spine. The shared
        // result card carries signed provenance without publishing the actor.
        let act = format!("{uri}/act");
        let (st, body) = send(
            &app,
            "POST",
            &act,
            Some(&ticket),
            Some("application/x-www-form-urlencoded"),
            Some(&format!(
                "turn=choose&arg={}&{}",
                KP_PRESS_ON,
                game_authority_fields(&opened)
            )),
        )
        .await;
        assert_eq!(st, StatusCode::OK, "{body}");
        assert!(body.contains("Turn committed"), "{body}");
        let notice = body
            .split_once("role=\"status\">")
            .and_then(|(_, tail)| tail.split_once("</div>"))
            .map(|(notice, _)| notice)
            .expect("landed response has a status notice");
        assert!(
            notice.contains("Verified dungeon receipt") && notice.contains("publication"),
            "the notice consumes the common public game receipt: {notice}"
        );
        assert!(
            !notice.contains(&expected_ident.0),
            "the public result notice must not publish the custodial actor: {notice}"
        );
        assert_eq!(
            catalog
                .bound_game_session("dungeon", &SessionId::new(sid))
                .expect("Activity POST retains the same live route"),
            routed_epoch
        );

        // GROUND TRUTH off the host's own move log: the landed move carries Signed provenance,
        // attributed to the discord-derived identity.
        let sid_owned = SessionId::new(sid);
        let log = catalog
            .host
            .run(move |h| h.move_log("dungeon", &sid_owned))
            .expect("the session has a move log");
        assert_eq!(log.moves.len(), 1, "one real turn landed");
        assert!(
            log.moves[0].attribution.is_signed(),
            "the Activity turn is Signed provenance: {:?}",
            log.moves[0].attribution
        );
        assert_eq!(log.moves[0].actor, expected_ident);

        // And the committed chain re-verifies by replay (genesis + 1 turn).
        let report = catalog
            .verify("dungeon", &SessionId::new(sid))
            .expect("verify");
        assert!(report.verified);
        assert_eq!(report.turns, 2);
    }

    #[tokio::test(flavor = "multi_thread")]
    async fn native_fragment_keeps_signed_provenance_resume_and_replay_on_discord() {
        let uid = 77;
        let (state, _) = test_state(uid);
        let app = discord_activity_router(state);
        let ticket = mint_ticket(&ticket_key(&BOT_SECRET), uid, unix_now(), NONCE);
        let uri = "/da/offerings/dungeon/session/hostile.tab-one";
        let response = app
            .oneshot(
                Request::builder()
                    .method("GET")
                    .uri(uri)
                    .header(ACTIVITY_TICKET_HEADER, ticket)
                    .header("x-fragment", "1")
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap();
        assert_eq!(response.status(), StatusCode::OK);
        let body = String::from_utf8(
            axum::body::to_bytes(response.into_body(), usize::MAX)
                .await
                .unwrap()
                .to_vec(),
        )
        .unwrap();
        assert!(body.contains("data-actor-attribution=\"signed\""), "{body}");
        assert!(body.contains("custodial signed provenance"), "{body}");
        assert!(
            !body.contains("Browser actor attribution is asserted"),
            "{body}"
        );
        assert!(
            body.contains("href=\"/da/offerings/dungeon/session/hostile.tab-one\""),
            "{body}"
        );
        assert!(
            body.contains(
                "data-da-verify=\"/da/offerings/dungeon/session/hostile.tab-one/verify\""
            ),
            "{body}"
        );
        assert!(!body.contains("href=\"/offerings/"), "{body}");
        assert_eq!(
            da_session_path("dungeon", "quote\"?hash#slash/"),
            "/da/offerings/dungeon/session/quote%22%3Fhash%23slash%2F"
        );
    }

    // ── Family (vi): the audience trap — a token minted for ANOTHER app is rejected. ──

    /// The confused-deputy defense (design §1/§9). The `/da/token` main path never trusts a
    /// client-presented token (it exchanges the code with our own `client_secret`), so this class is
    /// avoided STRUCTURALLY — but the guard is real, tested code so that any future
    /// client-presented-token path cannot silently skip it: an introspection response naming a
    /// foreign application id is refused, our own is accepted, and shape drift is refused (never
    /// silently trusted).
    #[test]
    fn the_audience_trap_rejects_a_foreign_app_token() {
        // A Discord GET /oauth2/@me introspection response — application.id is the AUDIENCE.
        let ours = r#"{"application":{"id":"1234567890","name":"dregg"},"scopes":["identify"],"expires":"2026-01-01T00:00:00Z"}"#;
        let foreign = r#"{"application":{"id":"9999999999","name":"evil"},"scopes":["identify"]}"#;
        assert_eq!(oauth_me_application_id(ours).as_deref(), Some("1234567890"));
        assert!(
            token_audience_ok(ours, "1234567890"),
            "our own app's token is trusted"
        );
        assert!(
            !token_audience_ok(foreign, "1234567890"),
            "a token minted for ANOTHER app is refused — the confused-deputy trap"
        );
        // Shape drift (no application/id) or non-JSON is refused, never silently trusted.
        assert!(!token_audience_ok(
            r#"{"scopes":["identify"]}"#,
            "1234567890"
        ));
        assert!(!token_audience_ok("not json at all", "1234567890"));
    }

    // ── Family (vii): the cross-platform LINK ceremony (design §5). ──

    /// A ticket-authenticated Discord account presents a claim signed by root key K binding it to K —
    /// it verifies + records into the SAME shared `links.tsv`; a forged signature is refused. (The
    /// registry write is redirected to a temp dir so the test does not touch the real shared store.)
    /// This is the `/da` twin of `the_tg_link_ceremony_verifies_a_root_claim_and_refuses_a_forgery`.
    #[tokio::test(flavor = "multi_thread")]
    async fn the_da_link_ceremony_verifies_a_root_claim_and_refuses_a_forgery() {
        use ed25519_dalek::{Signer, SigningKey};
        let tmp = std::env::temp_dir().join(format!("dregg-da-linktest-{}", std::process::id()));
        unsafe { std::env::set_var("DREGG_LINK_DIR", &tmp) };

        let uid = 555_000_111u64;
        let (state, _catalog) = test_state(uid);
        let app = discord_activity_router(state);
        let custodial = TurnSigner::from_seed(seed_for(&BOT_SECRET, uid))
            .identity()
            .0;
        let challenge =
            webauth_core::challenge::issue(&link_challenge_key(&BOT_SECRET), unix_now(), 300);

        // A fresh ticket, minted the way /da/token mints it (the ceremony's authenticator).
        let ticket = mint_ticket(&ticket_key(&BOT_SECRET), uid, unix_now(), NONCE);

        let root = SigningKey::from_bytes(&[5u8; 32]);
        let root_hex: String = root
            .verifying_key()
            .to_bytes()
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect();
        let msg = webauth_core::link_claim::link_claim_message(
            "discord",
            &uid.to_string(),
            &custodial,
            &root_hex,
            &challenge,
        )
        .unwrap();
        let sig_hex = |sk: &SigningKey| -> String {
            sk.sign(&msg)
                .to_bytes()
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect()
        };

        // (a) a genuine root-key claim links (the challenge string is URL-safe by construction —
        //     base64url(body) ‖ "." ‖ hex-tag — so it rides the form body unencoded).
        let body = format!(
            "root_pubkey_hex={root_hex}&signature_hex={}&challenge={challenge}",
            sig_hex(&root),
        );
        let (st, out) = send(
            &app,
            "POST",
            "/da/link",
            Some(&ticket),
            Some("application/x-www-form-urlencoded"),
            Some(&body),
        )
        .await;
        assert_eq!(st, StatusCode::OK, "genuine link claim verifies: {out}");
        assert!(out.contains("\"ok\":true"), "{out}");

        // (b) a forged signature (a different key over the same message) is refused.
        let attacker = SigningKey::from_bytes(&[9u8; 32]);
        let forged = format!(
            "root_pubkey_hex={root_hex}&signature_hex={}&challenge={challenge}",
            sig_hex(&attacker),
        );
        let (st2, _) = send(
            &app,
            "POST",
            "/da/link",
            Some(&ticket),
            Some("application/x-www-form-urlencoded"),
            Some(&forged),
        )
        .await;
        assert_eq!(st2, StatusCode::FORBIDDEN, "a forged claim is refused");

        // The link ceremony is ticket-gated: no ticket → 401 (nothing recorded).
        let (st3, _) = send(&app, "GET", "/da/link/challenge", None, None, None).await;
        assert_eq!(st3, StatusCode::UNAUTHORIZED);

        let _ = std::fs::remove_dir_all(&tmp);
    }

    /// The link page serves under the strict CSP with the vendored (same-origin) noble + SDK wiring,
    /// and its module carries the ticket-header + `platform="discord"` claim shape — no external origin.
    #[tokio::test(flavor = "multi_thread")]
    async fn the_da_link_page_ships_a_strict_csp_and_same_origin_scripts() {
        let (state, _catalog) = test_state(1);
        let app = discord_activity_router(state);

        let resp = app
            .clone()
            .oneshot(
                Request::builder()
                    .method("GET")
                    .uri("/da/link")
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap();
        assert_eq!(resp.status(), StatusCode::OK);
        let csp = resp
            .headers()
            .get("content-security-policy")
            .expect("the link page ships a CSP header")
            .to_str()
            .unwrap()
            .to_string();
        assert!(csp.contains("script-src 'self'"), "{csp}");
        assert!(csp.contains("connect-src 'self'"), "{csp}");
        let bytes = axum::body::to_bytes(resp.into_body(), usize::MAX)
            .await
            .unwrap();
        let body = String::from_utf8(bytes.to_vec()).unwrap();
        assert!(body.contains("/da/link/app.js"), "{body}");
        assert!(
            body.contains("/da/static/noble-ed25519.js")
                || LINK_APP_JS.contains("/da/static/noble-ed25519.js")
        );
        assert!(body.contains("/da/static/discord-sdk.js"), "{body}");
        assert!(body.contains("data-client-id=\"1234567890\""), "{body}");
        assert!(
            !body.contains("esm.sh"),
            "no external SDK/noble origin (design §6)"
        );

        // The module carries the pinned ceremony wiring: ticket header + discord platform tag.
        let (st, appjs) = send(&app, "GET", "/da/link/app.js", None, None, None).await;
        assert_eq!(st, StatusCode::OK);
        assert!(appjs.contains("X-Dregg-Activity-Ticket"), "{appjs}");
        assert!(appjs.contains("/da/static/noble-ed25519.js"), "{appjs}");
        assert!(appjs.contains("linkClaimMessage"), "{appjs}");
        assert!(appjs.contains("/da/link/challenge"), "{appjs}");

        // The vendored noble serves same-origin with a JS content-type.
        let (stn, _) = send(&app, "GET", "/da/static/noble-ed25519.js", None, None, None).await;
        assert_eq!(stn, StatusCode::OK);
    }
}
