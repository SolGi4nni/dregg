//! # `telegram_miniapp` — the Telegram Mini App surface: HMAC-verified Telegram identity → the
//! SAME derived dregg identity the in-chat bot uses → **verified `Attribution::Signed`** turns.
//!
//! Design: `docs/TELEGRAM-MINIAPP-DESIGN.md`. A Mini App is this server's HTTPS URL opened inside
//! Telegram's web-view; the page receives **initData** — a query string HMAC-signed by the bot
//! token — and sends it back on every state-touching request in the `X-Telegram-Init-Data`
//! header. This module:
//!
//! 1. **Validates initData** ([`validate_init_data_at`], pure) — the exact algorithm from
//!    Telegram's "Validating data received via the Mini App": data-check-string of all decoded
//!    `key=value` pairs except `hash`/`signature`, sorted by key, joined by `\n`;
//!    `secret_key = HMAC_SHA256(key = "WebAppData", msg = bot_token)`;
//!    `expected = HMAC_SHA256(key = secret_key, msg = dcs)`; constant-time compare; an
//!    `auth_date` freshness window (default 24 h, env-tunable) plus a 300 s future-skew guard.
//!    Only after ALL gates pass is `user.id` parsed — the ONLY trusted Telegram identity.
//! 2. **Derives the dregg identity** with the in-chat bot's OWN derivation
//!    ([`dreggnet_telegram::cipherclerk::TelegramCipherclerk::derive`] /
//!    [`dreggnet_telegram::cipherclerk::seed_for`]) — the Mini App player and the in-chat player
//!    are byte-for-byte ONE identity (same master secret, same BLAKE3 domain, same Ed25519 key).
//! 3. **Lands turns with verified provenance** — the POST path rebuilds the custodial
//!    [`TurnSigner`] from the derived seed, reads the replay-counter floor and signs at exactly
//!    the expected counter, and delegates to
//!    [`OfferingHost::advance_signed`](dreggnet_offerings::OfferingHost::advance_signed) — all
//!    inside ONE [`HostThread`](crate::HostThread) job, so floor-read → sign → verify → consume
//!    is atomic (no TOCTOU, no counter bookkeeping outside the host thread).
//!
//! ## Honest attestation statement (what `Signed` means here)
//!
//! Telegram's HMAC attests the HUMAN (this uid opened the Mini App within the freshness window);
//! the server signs the turn with the key it CUSTODIANS for that human (rung 1 of the signed.rs
//! ladder — the frontend's existing custodial design). The signature proves what signatures
//! prove: the key-holder authorized this exact turn in this exact session at this counter. The
//! initData gate is what binds the human to the key on each request. Rung 2 (client-held keys in
//! the web-view) replaces the custodial signer with the extension-style client-signed wire from
//! [`crate::act_signed`] — the verifier does not change.
//!
//! ## Refusals (fail-closed, cheapest first)
//!
//! Missing initData → `401`; malformed query string / non-hex hash / missing `auth_date` →
//! `400`; HMAC mismatch or stale/future `auth_date` → `403`. A refused request derives no
//! identity, opens no session, lands no turn. `initDataUnsafe`, a client-posted uid, a query
//! param, a cookie — never identity inputs on `/tg/*`. The raw initData string is bearer-like:
//! it rides ONLY in a header (never a URL) and is never logged (the verified uid + `auth_date`
//! are logged instead).
//!
//! ## Routes (additive `/tg` scope beside the cookie-identity catalog — the two trust stories
//! never share a handler)
//!
//! ```text
//! GET  /tg                                    — Mini App shell (static HTML+JS; no auth to serve)
//! GET  /tg/offerings                          — catalog fragment rendered for the VERIFIED viewer
//! GET  /tg/offerings/{key}/session/{id}       — validate → ensure_open_as(Asserted ident) → render_for(ident)
//!                                               (header-less DOCUMENT navigation — the bot's deep-linked
//!                                               launch buttons — serves the shell with this path as its
//!                                               boot target instead; no state touched, fragment fetches
//!                                               and POSTs keep the hard 401)
//! POST /tg/offerings/{key}/session/{id}/act   — validate → derive signer → atomic custodial advance → Signed turn
//! ```
//!
//! Mounted by [`make_app`](crate::make_app) iff `TELEGRAM_BOT_TOKEN` is set (see
//! [`tg_miniapp_from_env`]); absent, the web catalog works unchanged and one line logs the gate.

use std::sync::Arc;
use std::time::{SystemTime, UNIX_EPOCH};

#[cfg(feature = "hosted-binary-operations")]
use axum::extract::Query;
use axum::{
    Json, Router,
    extract::{Form, Path, State},
    http::{HeaderMap, StatusCode, header},
    response::{Html, IntoResponse, Response},
    routing::{get, post},
};
use hmac::{Hmac, Mac};
use serde::Deserialize;
use sha2::Sha256;
use subtle::ConstantTimeEq;
use zeroize::Zeroizing;

use dreggnet_catalog::{game_kind, sign_game_action};
use dreggnet_offerings::player_turn_receipt::{PlayerReplaySurface, PlayerTurnReceipt};
use dreggnet_offerings::{
    Action, Attribution, Custody, DreggIdentity, HostError, Outcome, SessionId, SignedError,
    TurnSigner,
};
use dreggnet_telegram::cipherclerk::{TelegramCipherclerk, seed_for};
use webauth_core::link_registry::LinkStore;

use crate::{
    CatalogGameError, CatalogState, OfferingActForm, act_signed, audit, metrics, open_audit_parts,
    refused_open_response, render_offering_response, wants_fragment,
};

// ─────────────────────────────────────────────────────────────────────────────
// Constants — the wire names and the pinned windows.
// ─────────────────────────────────────────────────────────────────────────────

/// The header the Mini App shell attaches the raw initData string to on every state-touching
/// request. A header, never a URL: URLs leak into logs and Referer headers, and initData is
/// bearer-like within its freshness window.
pub const INIT_DATA_HEADER: &str = "x-telegram-init-data";

/// The env var carrying the bot token (exactly the variable the bot bin already requires) —
/// the HMAC validation credential. Shared-credential co-tenancy with the bot process, named in
/// the design doc §2: web + bot on one box, one operator, ONE trust domain.
pub const TELEGRAM_BOT_TOKEN_ENV: &str = "TELEGRAM_BOT_TOKEN";

/// The env var tuning the initData freshness window (seconds). Default
/// [`DEFAULT_INITDATA_MAX_AGE_SECS`] — a Mini App keeps its launch-time initData for the whole
/// web-view lifetime, so the window must cover a long play session.
pub const TELEGRAM_INITDATA_MAX_AGE_ENV: &str = "TELEGRAM_INITDATA_MAX_AGE_SECS";

/// The default initData freshness window: 24 h.
pub const DEFAULT_INITDATA_MAX_AGE_SECS: u64 = 86_400;

/// The clock-skew guard: an `auth_date` more than this many seconds in the FUTURE is refused.
pub const FUTURE_SKEW_SECS: u64 = 300;

/// The Mini App shell may load Telegram's official bridge plus this crate's
/// same-origin bootstrap module.  Fragment HTML is server-authored; uploaded
/// proof bytes and refusal bodies never become script or markup.
const TG_SHELL_CSP: &str = "default-src 'none'; \
    script-src 'self' https://telegram.org; \
    style-src 'unsafe-inline'; \
    connect-src 'self'; \
    img-src 'self' data:; \
    base-uri 'none'; object-src 'none'; form-action 'self'; \
    frame-ancestors https://web.telegram.org https://*.telegram.org";

// ─────────────────────────────────────────────────────────────────────────────
// initData validation — the trust root (design doc §1, pinned).
// ─────────────────────────────────────────────────────────────────────────────

/// **A cryptographically verified Telegram user** — the ONLY product of a passed initData
/// validation, and the only trusted Telegram identity on the `/tg/*` surface.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VerifiedTelegramUser {
    /// The verified Telegram uid (`user.id` from the HMAC-covered `user` JSON).
    pub user_id: u64,
    /// The username, if Telegram sent one (display-only convenience; never an identity input).
    pub username: Option<String>,
    /// The first name, if sent (display-only convenience).
    pub first_name: Option<String>,
    /// The `auth_date` the envelope was minted at (unix seconds) — what freshness was judged on.
    pub auth_date: u64,
}

/// Why an initData string was REFUSED — each variant one fail-closed gate of
/// [`validate_init_data_at`], named so an audit sees which gate bit. [`http_status`
/// ](InitDataError::http_status) maps each to the design's refusal statuses.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InitDataError {
    /// No initData reached the server at all (`401` — the extractor's variant).
    Missing,
    /// The query string does not parse (bad percent-encoding / non-UTF-8 after decode).
    MalformedQuery,
    /// No `hash` pair was present.
    MissingHash,
    /// The `hash` value is not 64 hex chars (refused before any comparison).
    MalformedHash,
    /// No `auth_date` pair was present.
    MissingAuthDate,
    /// The `auth_date` value is not a unix-seconds integer.
    MalformedAuthDate,
    /// The HMAC over the data-check-string did not match the presented hash — forged or
    /// tampered initData (this is the gate a client-invented uid dies at).
    BadHmac,
    /// The envelope is older than the freshness window.
    Stale {
        /// How old the envelope is (seconds).
        age_secs: u64,
        /// The window it exceeded.
        max_age_secs: u64,
    },
    /// The `auth_date` is further in the future than the skew guard allows.
    FromFuture {
        /// How far ahead of the server clock (seconds).
        ahead_secs: u64,
    },
    /// A valid HMAC with no `user` pair — nothing to attribute to (still a refusal).
    MissingUser,
    /// A valid HMAC whose `user` JSON does not carry a u64 `id`.
    MalformedUser,
}

impl InitDataError {
    /// The design's refusal statuses: missing → `401`; malformed shapes → `400`; a refused
    /// HMAC / freshness gate → `403`.
    pub fn http_status(&self) -> StatusCode {
        match self {
            InitDataError::Missing => StatusCode::UNAUTHORIZED,
            InitDataError::BadHmac
            | InitDataError::Stale { .. }
            | InitDataError::FromFuture { .. } => StatusCode::FORBIDDEN,
            _ => StatusCode::BAD_REQUEST,
        }
    }
}

impl std::fmt::Display for InitDataError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InitDataError::Missing => write!(f, "no initData presented"),
            InitDataError::MalformedQuery => write!(f, "initData is not a decodable query string"),
            InitDataError::MissingHash => write!(f, "initData carries no hash pair"),
            InitDataError::MalformedHash => write!(f, "hash is not 64 hex chars"),
            InitDataError::MissingAuthDate => write!(f, "initData carries no auth_date pair"),
            InitDataError::MalformedAuthDate => write!(f, "auth_date is not unix seconds"),
            InitDataError::BadHmac => write!(f, "HMAC did not verify over the data-check-string"),
            InitDataError::Stale {
                age_secs,
                max_age_secs,
            } => write!(
                f,
                "auth_date is stale: {age_secs}s old, window {max_age_secs}s"
            ),
            InitDataError::FromFuture { ahead_secs } => {
                write!(
                    f,
                    "auth_date is {ahead_secs}s in the future (skew guard 300s)"
                )
            }
            InitDataError::MissingUser => write!(f, "valid HMAC but no user pair to attribute to"),
            InitDataError::MalformedUser => write!(f, "user JSON does not carry a u64 id"),
        }
    }
}

impl std::error::Error for InitDataError {}

type HmacSha256 = Hmac<Sha256>;

/// `HMAC_SHA256(key, msg)` → the 32-byte tag (HMAC accepts any key length).
fn hmac_sha256(key: &[u8], msg: &[u8]) -> [u8; 32] {
    let mut mac = HmacSha256::new_from_slice(key).expect("HMAC accepts any key length");
    mac.update(msg);
    mac.finalize().into_bytes().into()
}

/// **The Mini App HMAC secret key for a bot token** — `HMAC_SHA256(key = "WebAppData",
/// msg = bot_token)`. Note the constant string is the HMAC **key** and the token is the
/// **message** (the direction Telegram pins). Computed once at mount ([`TgMiniAppState::new`]).
pub fn webapp_secret_key(bot_token: &str) -> [u8; 32] {
    hmac_sha256(b"WebAppData", bot_token.as_bytes())
}

/// Percent-decode one form-urlencoded component (`%XX` → byte, `+` → space); `None` on a
/// malformed escape or non-UTF-8 result. The decode Telegram's own `URLSearchParams`-shaped
/// consumers apply before building the data-check-string.
fn url_decode(s: &str) -> Option<String> {
    let bytes = s.as_bytes();
    let mut out = Vec::with_capacity(bytes.len());
    let mut i = 0;
    while i < bytes.len() {
        match bytes[i] {
            b'%' => {
                if i + 2 >= bytes.len() {
                    return None;
                }
                let hi = hex_nib(bytes[i + 1])?;
                let lo = hex_nib(bytes[i + 2])?;
                out.push((hi << 4) | lo);
                i += 3;
            }
            b'+' => {
                out.push(b' ');
                i += 1;
            }
            b => {
                out.push(b);
                i += 1;
            }
        }
    }
    String::from_utf8(out).ok()
}

fn hex_nib(c: u8) -> Option<u8> {
    match c {
        b'0'..=b'9' => Some(c - b'0'),
        b'a'..=b'f' => Some(c - b'a' + 10),
        b'A'..=b'F' => Some(c - b'A' + 10),
        _ => None,
    }
}

/// Decode exactly 64 hex chars into 32 bytes; `None` on any other shape (an immediate refusal
/// before any comparison — never compare against a malformed hash).
fn decode_hex_32(s: &str) -> Option<[u8; 32]> {
    let bytes = s.as_bytes();
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

/// **Validate an initData string — the pure core** (no I/O, no clock: the caller injects
/// `now_unix` and the freshness window). The pinned algorithm, in gate order:
///
/// 1. parse the query string into URL-decoded `(key, value)` pairs (`400` shapes first);
/// 2. the `hash` pair must exist and be 64 hex chars; `auth_date` must exist and parse;
/// 3. build the data-check-string: every pair EXCEPT `hash` and `signature` (the third-party
///    Ed25519 scheme's field — not part of the HMAC scheme), rendered `key=<decoded value>`,
///    sorted by key, joined by `\n`;
/// 4. `expected = HMAC_SHA256(key = secret_key, msg = dcs)`; constant-time compare
///    (`subtle::ConstantTimeEq` over the decoded 32-byte tags) → [`InitDataError::BadHmac`];
/// 5. freshness: `now - auth_date > max_age_secs` → [`InitDataError::Stale`];
///    `auth_date > now + 300` → [`InitDataError::FromFuture`];
/// 6. only now parse `user` as JSON and extract the u64 `id` — the verified uid.
///
/// `secret_key` is [`webapp_secret_key`]`(bot_token)`, precomputed once.
pub fn validate_init_data_at(
    secret_key: &[u8; 32],
    init_data: &str,
    now_unix: u64,
    max_age_secs: u64,
) -> Result<VerifiedTelegramUser, InitDataError> {
    if init_data.is_empty() {
        return Err(InitDataError::MalformedQuery);
    }

    // 1. Parse into URL-decoded pairs. A pair with no `=` decodes as an empty value (the
    //    URLSearchParams shape); a malformed escape refuses the whole string.
    let mut pairs: Vec<(String, String)> = Vec::new();
    for part in init_data.split('&') {
        if part.is_empty() {
            return Err(InitDataError::MalformedQuery);
        }
        let (k, v) = match part.split_once('=') {
            Some((k, v)) => (k, v),
            None => (part, ""),
        };
        let k = url_decode(k).ok_or(InitDataError::MalformedQuery)?;
        let v = url_decode(v).ok_or(InitDataError::MalformedQuery)?;
        pairs.push((k, v));
    }

    // 2. The 400-shape gates, cheapest first.
    let provided_hash_hex = pairs
        .iter()
        .find(|(k, _)| k == "hash")
        .map(|(_, v)| v.clone())
        .ok_or(InitDataError::MissingHash)?;
    let provided_hash = decode_hex_32(&provided_hash_hex).ok_or(InitDataError::MalformedHash)?;
    let auth_date_raw = pairs
        .iter()
        .find(|(k, _)| k == "auth_date")
        .map(|(_, v)| v.clone())
        .ok_or(InitDataError::MissingAuthDate)?;
    let auth_date: u64 = auth_date_raw
        .parse()
        .map_err(|_| InitDataError::MalformedAuthDate)?;

    // 3. The data-check-string: every received pair except `hash` (and `signature`) — the HMAC
    //    covers ALL of them, including pairs this server does not otherwise use.
    let mut covered: Vec<(String, String)> = pairs
        .iter()
        .filter(|(k, _)| k != "hash") // signature IS covered by the HMAC data-check-string (verified against real Telegram initData 2026-07-17)
        .cloned()
        .collect();
    covered.sort();
    let dcs = covered
        .iter()
        .map(|(k, v)| format!("{k}={v}"))
        .collect::<Vec<_>>()
        .join("\n");

    // 4. The HMAC gate, constant-time over the two 32-byte tags.
    let expected = hmac_sha256(secret_key, dcs.as_bytes());
    if !bool::from(expected.ct_eq(&provided_hash)) {
        return Err(InitDataError::BadHmac);
    }

    // 5. Freshness — the envelope is genuine; is it current?
    if auth_date > now_unix {
        let ahead = auth_date - now_unix;
        if ahead > FUTURE_SKEW_SECS {
            return Err(InitDataError::FromFuture { ahead_secs: ahead });
        }
    } else {
        let age = now_unix - auth_date;
        if age > max_age_secs {
            return Err(InitDataError::Stale {
                age_secs: age,
                max_age_secs,
            });
        }
    }

    // 6. Only after ALL gates: parse `user` and extract the verified uid.
    let user_json = pairs
        .iter()
        .find(|(k, _)| k == "user")
        .map(|(_, v)| v.clone())
        .ok_or(InitDataError::MissingUser)?;
    let user: serde_json::Value =
        serde_json::from_str(&user_json).map_err(|_| InitDataError::MalformedUser)?;
    let user_id = user
        .get("id")
        .and_then(|v| v.as_u64())
        .ok_or(InitDataError::MalformedUser)?;

    Ok(VerifiedTelegramUser {
        user_id,
        username: user
            .get("username")
            .and_then(|v| v.as_str())
            .map(str::to_string),
        first_name: user
            .get("first_name")
            .and_then(|v| v.as_str())
            .map(str::to_string),
        auth_date,
    })
}

/// [`validate_init_data_at`] against the system clock, with the secret key derived from the
/// token and the freshness window from `TELEGRAM_INITDATA_MAX_AGE_SECS` (default 24 h) — the
/// one-call convenience form.
pub fn validate_init_data(
    bot_token: &str,
    init_data: &str,
) -> Result<VerifiedTelegramUser, InitDataError> {
    let secret = webapp_secret_key(bot_token);
    validate_init_data_at(&secret, init_data, unix_now(), max_age_from_env())
}

/// The freshness window: `TELEGRAM_INITDATA_MAX_AGE_SECS` if set and parsable, else 24 h.
fn max_age_from_env() -> u64 {
    std::env::var(TELEGRAM_INITDATA_MAX_AGE_ENV)
        .ok()
        .and_then(|v| v.trim().parse().ok())
        .unwrap_or(DEFAULT_INITDATA_MAX_AGE_SECS)
}

fn unix_now() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0)
}

// ─────────────────────────────────────────────────────────────────────────────
// The router + state.
// ─────────────────────────────────────────────────────────────────────────────

/// **The Mini App surface's axum state** — the shared catalog host handle plus the two secrets
/// this surface needs: the HMAC `secret_key` (validation credential, from the bot token) and the
/// identity `bot_secret` (derivation root — MUST resolve identically in the bot process, see
/// `master_secret_from_env`; a fork here forks every user into two identities).
pub struct TgMiniAppState {
    /// The SAME catalog host the cookie-identity routes drive — one registry, two trust stories,
    /// never one handler.
    catalog: Arc<CatalogState>,
    /// `HMAC_SHA256("WebAppData", bot_token)` — precomputed once at mount.
    secret_key: [u8; 32],
    /// The 32-byte identity master secret `seed_for` derives per-uid Ed25519 seeds from.
    bot_secret: [u8; 32],
    /// The initData freshness window (seconds).
    max_age_secs: u64,
    /// Single-use cache for spent link-ceremony challenge nonces — a `POST /tg/link` challenge is
    /// consumed on success so a captured claim can't be replayed within its TTL (internally synced).
    link_replay: webauth_core::replay::NonceCache,
}

impl TgMiniAppState {
    /// Assemble the Mini App state over a shared catalog. `bot_token` is consumed into the
    /// precomputed HMAC secret key (the raw token is not retained here).
    pub fn new(
        catalog: Arc<CatalogState>,
        bot_token: &str,
        bot_secret: [u8; 32],
        max_age_secs: u64,
    ) -> Self {
        TgMiniAppState {
            catalog,
            secret_key: webapp_secret_key(bot_token),
            bot_secret,
            max_age_secs,
            link_replay: webauth_core::replay::NonceCache::new(true, 8192),
        }
    }

    /// The verified viewer's dregg identity — the bot's OWN derivation, called (never mirrored):
    /// the Mini App player IS the in-chat player.
    fn identity_for(&self, uid: u64) -> DreggIdentity {
        TelegramCipherclerk::derive(&self.bot_secret, uid).identity()
    }
}

/// **Build the `/tg` Mini App router** over a shared [`TgMiniAppState`]. Additive beside
/// [`catalog_router`](crate::catalog_router); mounted by [`tg_miniapp_from_env`] when the token
/// is present.
pub fn tg_miniapp_router(state: Arc<TgMiniAppState>) -> Router {
    let router = Router::new()
        .route("/tg", get(get_tg_shell))
        .route("/tg/static/app.js", get(get_tg_app_js))
        .route("/tg/offerings", get(get_tg_offerings))
        .route("/tg/offerings/{key}/session/{id}", get(get_tg_session))
        .route(
            "/tg/offerings/{key}/session/{id}/verify",
            get(get_tg_verify),
        )
        .route("/tg/offerings/{key}/session/{id}/act", post(post_tg_act))
        .route("/tg/link/challenge", get(get_tg_link_challenge))
        .route(
            "/tg/link",
            get(crate::tg_link_page::get_tg_link_page).post(post_tg_link),
        )
        .route(
            "/tg/link/app.js",
            get(crate::tg_link_page::get_tg_link_app_js),
        )
        .route(
            "/tg/assets/noble-ed25519.js",
            get(crate::tg_link_page::get_noble_ed25519),
        );
    #[cfg(feature = "hosted-binary-operations")]
    let router = router
        .route(
            "/tg/offerings/{key}/session/{id}/operations",
            get(get_tg_operations),
        )
        .route(
            "/tg/offerings/{key}/session/{id}/operations/{name}",
            post(post_tg_operation),
        )
        .route(
            "/tg/offerings/{key}/session/{id}/artifacts",
            get(get_tg_artifacts),
        )
        .route(
            "/tg/offerings/{key}/session/{id}/artifacts/{name}",
            get(get_tg_artifact),
        );
    #[cfg(feature = "fhegg-settlement")]
    let router = router.route(
        "/tg/operations/{name}",
        get(crate::fhegg_operation::get_descriptor),
    );
    router.with_state(state)
}

/// **Resolve the Mini App router from the environment** — `Some(router)` iff
/// `TELEGRAM_BOT_TOKEN` is set (non-empty) AND the identity master secret resolves (explicit
/// `TELEGRAM_BOT_SECRET` hex, else token-derived — the SAME
/// `dreggnet_telegram::cipherclerk::master_secret_from_env` the bot binary uses: one impl, two
/// callers, zero identity drift). `None` (with one log line) leaves the web catalog serving
/// exactly as before — the Mini App surface is ops-gated exactly like the bot is.
pub fn tg_miniapp_from_env(catalog: Arc<CatalogState>) -> Option<Router> {
    let token = match std::env::var(TELEGRAM_BOT_TOKEN_ENV) {
        Ok(t) if !t.trim().is_empty() => t,
        _ => {
            tracing::info!(
                "Telegram Mini App surface NOT mounted — {TELEGRAM_BOT_TOKEN_ENV} unset \
                 (the web catalog serves unchanged)"
            );
            return None;
        }
    };
    let bot_secret = match dreggnet_telegram::cipherclerk::master_secret_from_env(&token) {
        Ok(s) => s,
        Err(e) => {
            tracing::error!(
                error = %e,
                "Telegram Mini App surface NOT mounted — identity master secret did not resolve"
            );
            return None;
        }
    };
    let max_age = max_age_from_env();
    tracing::info!(
        max_age_secs = max_age,
        "Telegram Mini App surface mounted at /tg (initData-verified identities; turns land \
         with Signed provenance)"
    );
    Some(tg_miniapp_router(Arc::new(TgMiniAppState::new(
        catalog, &token, bot_secret, max_age,
    ))))
}

// ─────────────────────────────────────────────────────────────────────────────
// Handlers.
// ─────────────────────────────────────────────────────────────────────────────

/// The machine reason for a refused initData gate — `initdata:<gate>` (the audit design's §3
/// taxonomy; each [`InitDataError`] variant is one named fail-closed gate).
fn initdata_reason(e: &InitDataError) -> String {
    let gate = match e {
        InitDataError::Missing => "missing",
        InitDataError::MalformedQuery => "malformed_query",
        InitDataError::MissingHash => "missing_hash",
        InitDataError::MalformedHash => "malformed_hash",
        InitDataError::MissingAuthDate => "missing_auth_date",
        InitDataError::MalformedAuthDate => "malformed_auth_date",
        InitDataError::BadHmac => "bad_hmac",
        InitDataError::Stale { .. } => "stale",
        InitDataError::FromFuture { .. } => "from_future",
        InitDataError::MissingUser => "missing_user",
        InitDataError::MalformedUser => "malformed_user",
    };
    format!("initdata:{gate}")
}

/// Validate the request's `X-Telegram-Init-Data` header into a [`VerifiedTelegramUser`], or the
/// honest refusal response (`401` missing / `400` malformed / `403` refused). The raw initData
/// is never logged — the verified uid + `auth_date` are.
///
/// AUDIT EMIT (both polarities — this is the trail the live HMAC-mismatch debugging reads):
/// every validation lands ONE `surface: "initdata"` event on `corr` — ACCEPT (`routed`, the
/// verified uid + `auth_date` + derived identity) or REFUSE (`gated`, the NAMED gate via
/// [`initdata_reason`] + the error text + status). The raw initData string never enters the
/// record (§8 hard rule); the deep dcs/hash diagnostic stays on `validate_init_data_at`'s
/// tracing warn.
fn verified_user(
    state: &TgMiniAppState,
    headers: &HeaderMap,
    corr: &str,
    route: &str,
) -> Result<VerifiedTelegramUser, Response> {
    let refused_event = |e: &InitDataError| {
        audit::AuditEvent::new(
            "tg-miniapp",
            audit::Actor::unattributed(),
            audit::Surface::InitData,
            audit::Input::new(
                route,
                serde_json::json!({
                    "error": e.to_string(),
                    "status": e.http_status().as_u16(),
                }),
            ),
        )
        .correlated(corr)
        .decided("gated", initdata_reason(e))
    };
    let raw = match headers.get(INIT_DATA_HEADER).and_then(|v| v.to_str().ok()) {
        Some(r) if !r.is_empty() => r,
        _ => {
            let e = InitDataError::Missing;
            audit::log().emit(refused_event(&e));
            return Err((
                e.http_status(),
                format!("initData refused: {e} — open this surface inside Telegram"),
            )
                .into_response());
        }
    };
    match validate_init_data_at(&state.secret_key, raw, unix_now(), state.max_age_secs) {
        Ok(u) => {
            tracing::debug!(
                uid = u.user_id,
                auth_date = u.auth_date,
                "initData verified"
            );
            audit::log().emit(
                audit::AuditEvent::new(
                    "tg-miniapp",
                    audit::Actor::initdata_verified(
                        u.user_id.to_string(),
                        Some(state.identity_for(u.user_id).0),
                    ),
                    audit::Surface::InitData,
                    audit::Input::new(
                        route,
                        serde_json::json!({
                            "auth_date": u.auth_date,
                            "username": u.username,
                        }),
                    ),
                )
                .correlated(corr),
            );
            Ok(u)
        }
        Err(e) => {
            tracing::debug!(error = %e, "initData refused");
            audit::log().emit(refused_event(&e));
            Err((e.http_status(), format!("initData refused: {e}")).into_response())
        }
    }
}

/// Build a shell response with the same policy for root and cold deep links.
fn tg_shell_response(boot: Option<&str>) -> Response {
    (
        [
            (header::CONTENT_SECURITY_POLICY, TG_SHELL_CSP),
            (header::X_CONTENT_TYPE_OPTIONS, "nosniff"),
            (header::REFERRER_POLICY, "no-referrer"),
        ],
        Html(shell_page(boot)),
    )
        .into_response()
}

/// `GET /tg` — the Mini App shell. No auth to SERVE (it is just a page); every
/// state-touching fetch it makes carries the header.
async fn get_tg_shell() -> Response {
    tg_shell_response(None)
}

/// Same-origin bootstrap so the shell does not require `script-src 'unsafe-inline'`.
async fn get_tg_app_js() -> impl IntoResponse {
    (
        [
            (header::CONTENT_TYPE, "text/javascript; charset=utf-8"),
            (header::X_CONTENT_TYPE_OPTIONS, "nosniff"),
        ],
        TG_SHELL_SCRIPT,
    )
}

/// RFC 3986 path-segment encoding.  `Path` gives handlers decoded values; putting
/// them back into a route without this step would turn `?`, `#`, `/`, or quotes
/// into route structure or markup rather than data.
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

fn tg_session_path(key: &str, id: &str) -> String {
    format!(
        "/tg/offerings/{}/session/{}",
        path_segment(key),
        path_segment(id)
    )
}

/// The shared renderer deliberately speaks the web rail.  Native clients must
/// not lose their authenticated principal by following its resume/replay URLs,
/// and their signed provenance must not be labelled as browser-asserted.
fn tg_native_fragment(html: String, key: &str, id: &str, fragment: bool) -> String {
    let web_base = format!("/offerings/{}/session/{}", crate::esc(key), crate::esc(id));
    let native_base = tg_session_path(key, id);
    let web_verify = format!("{web_base}/verify");
    let mut native = html.replace(
        &format!("href=\"{web_base}\" rel=\"bookmark\""),
        &format!(
            "href=\"{native_base}\" data-tg-session=\"{native_base}\" rel=\"bookmark\""
        ),
    )
    .replace(
        &format!("href=\"{web_verify}\""),
        &format!(
            "href=\"{native_base}/verify\" data-tg-verify=\"{native_base}/verify\""
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
        "Telegram identity is authenticated by signed initData; turns carry custodial signed provenance.",
    );
    if fragment {
        if let Some(kind) = game_kind(key) {
            native = format!(
                "<section class=\"game-session-rail\" data-game-session=\"true\" \
                 data-game-family=\"{}\" data-session-id=\"{}\" \
                 data-actor-attribution=\"signed\" aria-label=\"Session continuity and privacy\">\
                 <div class=\"game-session-resume\"><span class=\"game-session-kicker\">Session</span>\
                 <strong>{}</strong><a href=\"{native_base}\" data-tg-session=\"{native_base}\" \
                 rel=\"bookmark\">Resume here</a></div>\
                 <p class=\"game-session-boundary\"><span aria-hidden=\"true\">◐</span>\
                 Telegram identity is authenticated by signed initData; turns carry custodial signed provenance. \
                 Private game fields remain scoped to their owning projection.</p></section>{native}",
                kind.as_str(),
                crate::esc(id),
                crate::esc(id),
            );
        }
    }
    native
}

/// `GET /tg/offerings` — the catalog fragment for the VERIFIED viewer: a card per registered
/// offering linking that viewer's own default session (`tg-{key}-{ident16}` — reopening the
/// Mini App lands the same player in the same session).
async fn get_tg_offerings(
    State(state): State<Arc<TgMiniAppState>>,
    headers: HeaderMap,
) -> Response {
    let corr = audit::correlation_id();
    let user = match verified_user(&state, &headers, &corr, "GET /tg/offerings") {
        Ok(u) => u,
        Err(resp) => return resp,
    };
    let ident = state.identity_for(user.user_id);
    let offerings = state.catalog.list_offerings();
    let ident16 = &ident.0[..16.min(ident.0.len())];
    let mut cards = String::new();
    for o in &offerings {
        let session = format!("tg-{}-{ident16}", o.key);
        let path = tg_session_path(&o.key, &session);
        cards.push_str(&format!(
            "<div class=\"card\" style=\"margin:.6rem 0;padding:1rem;border:1px solid \
             var(--border);border-radius:var(--r-md);background:var(--panel)\">\
             <h3 style=\"margin:0 0 .35rem\">{title}</h3>\
             <a class=\"btn btn-primary\" href=\"{path}\" data-tg-session=\"{path}\">Play</a>\
             </div>",
            title = crate::esc(&o.title),
            path = crate::esc(&path),
        ));
    }
    // THE LAB FRAMING (shared words: `dreggnet_catalog::{flagship_pointer, lab_intro}`) —
    // The Descent featured first, then the catalog honestly labelled as the lab shelf.
    let featured = format!(
        "<div class=\"card\" style=\"margin:.6rem 0;padding:1rem;border:1px solid \
         var(--border);border-radius:var(--r-md);background:var(--panel)\">\
         <h3 style=\"margin:0 0 .35rem\">The Descent</h3>\
         <p class=\"prose\" style=\"margin:0 0 .5rem\">{flagship}</p>\
         <a class=\"btn btn-primary\" href=\"{play}\">Play today's descent</a>\
         <a class=\"btn btn-ghost\" href=\"/descent\">See today's no-cheat board</a>\
         </div>\
         <p class=\"prose\" style=\"margin:.8rem 0 .4rem\">{lab}</p>",
        // The button SAYS "Play today's descent" — so it must LAND on the game. It pointed at
        // `/descent`, the no-cheat BOARD, so every Telegram player who took the flagship's own CTA
        // arrived at a leaderboard. The board keeps its own (honestly labelled) link beside it.
        play = crate::DESCENT_PLAY_PATH,
        flagship = crate::esc(dreggnet_catalog::flagship_pointer()),
        lab = crate::esc(dreggnet_catalog::lab_intro()),
    );
    let body = format!(
        "<div class=\"notice ok\" role=\"status\">Verified via Telegram — playing as \
         <code>{ident16}…</code> (the same identity as in-chat)</div>{featured}{cards}",
    );
    Html(body).into_response()
}

/// `GET /tg/offerings/{key}/session/{id}` — validate the header, open the session as the
/// VERIFIED identity (opener attribution stays `Asserted` on purpose: only `verify_signed` ever
/// earns `Signed`, and the opener lane is an advisory quota key — here backed by an
/// HMAC-verified label, which makes the quota lane honest without the type claiming more than
/// the seam checked), and render the viewer's own per-player projection.
async fn get_tg_session(
    State(state): State<Arc<TgMiniAppState>>,
    Path((key, id)): Path<(String, String)>,
    headers: HeaderMap,
) -> Response {
    // A COLD DOCUMENT NAVIGATION — the bot's `web_app` launch buttons deep-link straight to
    // this path, and Telegram's web-view opens it as a plain page load: no header exists yet
    // (initData only materializes in JS, via telegram-web-app.js). Serve the static shell with
    // this deep path as its boot target; the shell's script then re-fetches the SAME path with
    // the header attached. No state is touched and nothing identity-gated is revealed — a
    // fragment fetch (`X-Fragment`) or any request that DID send a header keeps the full gate.
    if !headers.contains_key(INIT_DATA_HEADER) && !wants_fragment(&headers) {
        return tg_shell_response(Some(&tg_session_path(&key, &id)));
    }
    let corr = audit::correlation_id();
    let route = "GET /tg/offerings/{key}/session/{id}";
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
    // AUDIT EMIT: the open decision for the verified viewer, joined to the initData accept
    // event by `corr`.
    {
        let (kind, reason) = match &opened {
            Ok(_) => ("routed", String::new()),
            Err(CatalogGameError::Host(e)) => open_audit_parts(e),
            Err(e) => ("gated", e.to_string()),
        };
        audit::log().emit(
            audit::AuditEvent::new(
                "tg-miniapp",
                audit::Actor::initdata_verified(user.user_id.to_string(), Some(viewer.0.clone())),
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

    Html(tg_native_fragment(
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

/// Ticket-equivalent, initData-authenticated replay verification.  The native
/// replay link never falls through to the cookie-identity web route.
async fn get_tg_verify(
    State(state): State<Arc<TgMiniAppState>>,
    Path((key, id)): Path<(String, String)>,
    headers: HeaderMap,
) -> Response {
    let corr = audit::correlation_id();
    let user = match verified_user(
        &state,
        &headers,
        &corr,
        "GET /tg/offerings/{key}/session/{id}/verify",
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
                        "surface": "telegram",
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
            "surface": "telegram",
        }))
        .into_response(),
        None => (
            StatusCode::NOT_FOUND,
            Json(serde_json::json!({
                "verified": false,
                "turns": 0,
                "detail": "no such Telegram game session",
                "surface": "telegram",
            })),
        )
            .into_response(),
    }
}

/// Authenticated discovery of transport-bearing affordances on one live
/// session. The returned descriptor is the same value the web and Discord
/// surfaces render; only this wrapper's initData gate differs.
#[cfg(feature = "hosted-binary-operations")]
async fn get_tg_operations(
    State(state): State<Arc<TgMiniAppState>>,
    Path((key, id)): Path<(String, String)>,
    headers: HeaderMap,
) -> Response {
    let corr = audit::correlation_id();
    if let Err(response) = verified_user(
        &state,
        &headers,
        &corr,
        "GET /tg/offerings/{key}/session/{id}/operations",
    ) {
        return response;
    }
    crate::fhegg_operation::session_operations(&state.catalog, key, id)
}

/// Telegram-authenticated wrapper around the one shared owning-bundle
/// implementation. Authentication completes before the bounded request body is
/// read; the raw initData and bundle bytes are never logged.
#[cfg(feature = "hosted-binary-operations")]
async fn post_tg_operation(
    State(state): State<Arc<TgMiniAppState>>,
    Path((key, id, name)): Path<(String, String, String)>,
    request: axum::extract::Request,
) -> Response {
    let corr = audit::correlation_id();
    let user = match verified_user(
        &state,
        request.headers(),
        &corr,
        "POST /tg/offerings/{key}/session/{id}/operations/{name}",
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

/// Telegram-authenticated discovery of read-only live-session artifacts.
#[cfg(feature = "hosted-binary-operations")]
async fn get_tg_artifacts(
    State(state): State<Arc<TgMiniAppState>>,
    Path((key, id)): Path<(String, String)>,
    headers: HeaderMap,
) -> Response {
    let corr = audit::correlation_id();
    if let Err(response) = verified_user(
        &state,
        &headers,
        &corr,
        "GET /tg/offerings/{key}/session/{id}/artifacts",
    ) {
        return response;
    }
    crate::fhegg_operation::session_artifacts(&state.catalog, key, id)
}

/// Telegram-authenticated wrapper around the shared canonical artifact export.
#[cfg(feature = "hosted-binary-operations")]
async fn get_tg_artifact(
    State(state): State<Arc<TgMiniAppState>>,
    Path((key, id, name)): Path<(String, String, String)>,
    Query(authority): Query<crate::fhegg_operation::GameResourceAuthorityQuery>,
    headers: HeaderMap,
) -> Response {
    let corr = audit::correlation_id();
    let user = match verified_user(
        &state,
        &headers,
        &corr,
        "GET /tg/offerings/{key}/session/{id}/artifacts/{name}",
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

/// The `{turn, arg, text}` POST body of `POST /tg/offerings/{key}/session/{id}/act` — the same
/// form shape as the unsigned `/act` twin, plus the optional free-text payload the canonical
/// signing message covers.
#[derive(Debug, Clone, Deserialize)]
pub struct TgActForm {
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

/// `POST /tg/offerings/{key}/session/{id}/act` — validate the header, rebuild the custodial
/// signer (`TurnSigner::from_seed(seed_for(bot_secret, uid))` — byte-identical to the identity
/// the bot attributes), and land ONE turn with **verified `Signed` provenance**: inside a single
/// host-thread job, read the replay-counter floor, sign at exactly the expected counter, and
/// delegate to `advance_signed` — atomic, no TOCTOU.
///
/// Status mapping mirrors [`crate::act_signed`] (with the initData gate's `401/400/403` in
/// front). A `403` from the VERIFIER on this path indicates a server bug (the server signed for
/// itself and the verify/consume runs in the same job) — logged loudly.
async fn post_tg_act(
    State(state): State<Arc<TgMiniAppState>>,
    Path((key, id)): Path<(String, String)>,
    headers: HeaderMap,
    Form(form): Form<TgActForm>,
) -> Response {
    let corr = audit::correlation_id();
    let route = "POST /tg/offerings/{key}/session/{id}/act";
    let user = match verified_user(&state, &headers, &corr, route) {
        Ok(u) => u,
        Err(resp) => return resp,
    };
    let sid = SessionId::new(id);
    // THE SEAT LOCK on a minted table. Such a table binds its two seats to two unguessable BROWSER
    // link labels; a Mini App actor is a custodial pubkey identity and can never be one of them,
    // so admitting it here would let a Telegram user take a seat the invite link was supposed to
    // hold. Refused for minted `af1-` automatafl and `tug1-` tug sessions ONLY — every ad-hoc id
    // and every other key is untouched, and this Mini App never mints one.
    if let Err(why) = crate::table_seats::refuse_non_seat_route(&key, &sid.0) {
        return (StatusCode::FORBIDDEN, why).into_response();
    }
    // The PUBLIC audit substance, captured before `form` is consumed into the action: the
    // `{turn, arg, text}` IS the trail (§8 — user content, no secrets on this wire).
    let audit_detail = serde_json::json!({
        "turn": form.turn,
        "arg": form.arg,
        "text": form.text,
    });

    // The custodial signer for the VERIFIED uid — the same seed, therefore the same Ed25519
    // identity, as `TelegramCipherclerk::derive`. The transient seed copy is wiped after the
    // signer is constructed (as the cipherclerk does).
    let seed = Zeroizing::new(seed_for(&state.bot_secret, user.user_id));
    let signer = TurnSigner::from_seed(*seed);
    drop(seed);
    let viewer = signer.identity();
    let act_event = |detail: serde_json::Value| {
        audit::AuditEvent::new(
            "tg-miniapp",
            audit::Actor::initdata_verified(user.user_id.to_string(), Some(viewer.0.clone())),
            audit::Surface::Http,
            audit::Input::new(route, detail),
        )
        .correlated(&corr)
        .in_session(Some(key.clone()), Some(sid.0.clone()))
    };

    // The typed action — label defaults to the verb, `enabled` is decoration (the executor is
    // the sole referee of a crafted POST, exactly as on every other surface).
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
    // consume → executor referees the move. No other job can interleave, so the custodial
    // signer never races its own counter. Routed to the viewer's own world for an RPG key.
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
                    // A consumed u64::MAX leaves no acceptable next counter — the lane is
                    // exhausted; surface the same refusal advance_signed would.
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
            // CUSTODIAL: sign under THIS host's incarnation so the turn verifies through
            // `advance_signed_attributed` and a captured envelope cannot re-verify on a same-`id`
            // session reopened under a later incarnation.
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

    // AUDIT EMIT: the custodial-Signed advance, joined to the initData accept by `corr` —
    // `Landed` carries the receipt-chain join; a verifier refusal HERE is a server bug (the
    // server signed for itself in the same atomic job) and is recorded as `error`.
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
                .compact_text(PlayerReplaySurface::Telegram),
                |publication| crate::game_session::public_receipt_text(
                    publication,
                    PlayerReplaySurface::Telegram,
                ),
            )
        ),
        // The signature verified; the executor refused the move itself — the anti-ghost banner.
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
        // On the CUSTODIAL path the server signed for itself in the same atomic job, so a
        // verifier refusal is a server bug, not client input — log loudly, refuse honestly.
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

    Html(tg_native_fragment(
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
// The shell page — the Telegram.WebApp JS surface (design doc §5).
// ─────────────────────────────────────────────────────────────────────────────

/// The Mini App bootstrap script. The pinned JS surface, nothing more: `ready()`/`expand()`,
/// `themeParams` → the page's CSS custom properties (re-applied on `themeChanged`), a
/// catalog-navigation-only BackButton, `initData` attached as `X-Telegram-Init-Data` on every
/// fetch (never a URL), and `initDataUnsafe` used for DISPLAY ONLY (it is the unverified parse;
/// the server never receives or trusts it). Forms rendered by the shared fragment path POST to
/// `/offerings/...`; the submit interceptor rewrites them onto the `/tg` twin so the turn lands
/// through the initData-verified custodial-Signed path.
const TG_SHELL_SCRIPT: &str = r##"(function () {
  var tg = window.Telegram && window.Telegram.WebApp;
  var root = document.getElementById('tg-root');

  function notice(message, cls) {
    var box = document.createElement('div');
    box.className = 'notice ' + (cls || 'refused');
    box.setAttribute('role', 'status');
    box.textContent = String(message);
    root.replaceChildren(box);
  }
  function failure(error) {
    notice(error && error.message ? error.message : error, 'refused');
  }
  function report(message, cls) {
    var old = root.querySelector('[data-native-replay-report]');
    if (old) { old.remove(); }
    var box = document.createElement('div');
    box.className = 'notice ' + (cls || 'refused');
    box.setAttribute('role', 'status');
    box.setAttribute('data-native-replay-report', 'true');
    box.textContent = String(message);
    root.prepend(box);
  }
  if (!tg || !tg.initData) {
    notice('Open this page inside Telegram — the Mini App needs its signed initData to identify you.');
    return;
  }
  // The raw signed string — sent ONLY as a header, never in a URL (URLs leak into logs/Referer).
  var initData = tg.initData;
  tg.ready();
  tg.expand();

  // themeParams → the page's CSS custom properties, re-applied on themeChanged.
  function applyTheme() {
    var p = tg.themeParams || {};
    var r = document.documentElement.style;
    if (p.bg_color) { r.setProperty('--bg', p.bg_color); document.body.style.background = p.bg_color; }
    if (p.secondary_bg_color) { r.setProperty('--panel', p.secondary_bg_color); r.setProperty('--card', p.secondary_bg_color); }
    if (p.text_color) { r.setProperty('--fg', p.text_color); }
    if (p.hint_color) { r.setProperty('--muted', p.hint_color); r.setProperty('--fg-3', p.hint_color); }
    if (p.link_color) { r.setProperty('--accent', p.link_color); }
    if (p.button_color) { r.setProperty('--accent', p.button_color); }
    document.documentElement.style.colorScheme = tg.colorScheme || 'dark';
  }
  applyTheme();
  tg.onEvent('themeChanged', applyTheme);

  // initDataUnsafe is the UNVERIFIED client-side parse — display only, never an identity input.
  var unsafe = tg.initDataUnsafe || {};
  var greet = document.getElementById('tg-greet');
  if (greet && unsafe.user && unsafe.user.first_name) {
    greet.textContent = 'Welcome, ' + unsafe.user.first_name + '.';
  }

  // Normalize a server-authored route without ever decoding and rebuilding its
  // path segments. URL rejects foreign origins and normalizes dot segments.
  function nativePath(raw) {
    var url = new URL(raw, window.location.origin);
    if (url.origin !== window.location.origin) { throw new Error('Refused a cross-origin game route.'); }
    var path = url.pathname;
    if (path === '/offerings' || path.indexOf('/offerings/') === 0) { path = '/tg' + path; }
    if (path !== '/tg/offerings' && path.indexOf('/tg/offerings/') !== 0) {
      throw new Error('Refused a non-Telegram game route.');
    }
    return path + url.search;
  }
  function responseError(resp, body) {
    var detail = body ? ': ' + body.slice(0, 500) : '';
    return new Error('Request refused (HTTP ' + resp.status + ')' + detail);
  }
  function isType(resp, expected) {
    var actual = (resp.headers.get('content-type') || '').split(';', 1)[0].trim().toLowerCase();
    return expected === 'json'
      ? (actual === 'application/json' || actual.endsWith('+json'))
      : actual === 'text/html';
  }
  async function readHtml(resp) {
    var body = await resp.text();
    if (!resp.ok) { throw responseError(resp, body); }
    if (!isType(resp, 'html')) { throw new Error('Refused a non-HTML fragment response.'); }
    return body;
  }
  async function readJson(resp) {
    var body = await resp.text();
    if (!resp.ok) { throw responseError(resp, body); }
    if (!isType(resp, 'json')) { throw new Error('Refused a non-JSON operation response.'); }
    try { return JSON.parse(body); } catch (_) { throw new Error('Refused malformed JSON.'); }
  }
  function tgRequest(path, opts) {
    opts = opts || {};
    var headers = new Headers(opts.headers || {});
    headers.set('X-Telegram-Init-Data', initData);
    headers.set('X-Fragment', '1');
    opts.headers = headers;
    opts.credentials = 'same-origin';
    opts.cache = 'no-store';
    return fetch(path, opts);
  }
  function tgFetchHtml(path, opts) {
    return tgRequest(nativePath(path), opts).then(readHtml);
  }
  function encodeForm(form) {
    var params = new URLSearchParams();
    new FormData(form).forEach(function (value, name) {
      if (typeof value !== 'string') { throw new Error('A file is not a turn-form field.'); }
      params.append(name, value);
    });
    return params.toString();
  }

  // BackButton = catalog navigation ONLY (turns are receipts; never wired to undo).
  function showCatalog() {
    tg.BackButton.hide();
    tgFetchHtml('/tg/offerings').then(function (html) { root.innerHTML = html; }).catch(failure);
  }
  function openSession(path) {
    tgFetchHtml(path).then(function (html) {
      root.innerHTML = html;
      tg.BackButton.show();
    }).catch(failure);
  }
  function showVerification(path) {
    tgRequest(nativePath(path), { headers: { 'Accept': 'application/json' } })
      .then(readJson)
      .then(function (report) {
        var message = (report.verified ? 'Replay verified' : 'Replay refused') + ' · ' +
          report.turns + ' turns · ' + report.detail, report.verified ? 'ok' : 'refused');
        report(message, report.verified ? 'ok' : 'refused');
      })
      .catch(failure);
  }
  tg.BackButton.onClick(showCatalog);

  // A deep-linked boot target (the bot's launch buttons land the web-view directly on a
  // session path; the server hands the path back for the shell to open WITH the header).
  var boot = root.getAttribute('data-boot');

  root.addEventListener('click', function (ev) {
    var el = ev.target;
    while (el && el !== root && !(el.getAttribute &&
      (el.getAttribute('data-tg-session') || el.getAttribute('data-tg-verify')))) {
      el = el.parentNode;
    }
    if (!el || el === root || !el.getAttribute) { return; }
    var verify = el.getAttribute('data-tg-verify');
    if (verify) { ev.preventDefault(); showVerification(verify); return; }
    var path = el.getAttribute('data-tg-session');
    if (!path) { return; }
    ev.preventDefault();
    openSession(path);
  });

  root.addEventListener('submit', async function (ev) {
    var form = ev.target;
    if (!form || !form.action) { return; }
    ev.preventDefault();
    var path;
    try { path = nativePath(form.action); } catch (error) { failure(error); return; }

    // Proof/receipt uploads are opaque bytes.  Never pass a File through
    // URLSearchParams (which silently serializes it as "[object File]").
    if (form.classList.contains('binary-operation')) {
      var input = form.querySelector('input[type=file]');
      var status = form.querySelector('[role=status]');
      var file = input && input.files && input.files[0];
      if (!file) {
        if (status) { status.textContent = 'Choose the canonical proof or receipt first.'; }
        return;
      }
      form.classList.add('pending');
      if (status) { status.textContent = 'Verifying opaque receipt…'; }
      try {
        var operationResponse = await tgRequest(path, {
          method: 'POST',
          headers: {
            'Content-Type': form.getAttribute('data-media') || 'application/octet-stream',
            'Accept': 'application/json'
          },
          body: file
        });
        await readJson(operationResponse);
        openSession(path.split('/operations/', 1)[0]);
      } catch (error) {
        form.classList.remove('pending');
        if (status) { status.textContent = 'Refused: ' + (error.message || error); }
      }
      return;
    }

    try {
      var html = await tgFetchHtml(path, {
        method: 'POST',
        headers: { 'Content-Type': 'application/x-www-form-urlencoded' },
        body: encodeForm(form)
      });
      root.innerHTML = html;
    } catch (error) { failure(error); }
  });

  if (boot) { openSession(boot); } else { showCatalog(); }
})();
"##;

/// **The Mini App shell page** — the served HTML for `GET /tg` (and for a cold, header-less
/// document GET of a deep session path — the bot's launch buttons): the crate's own stylesheet
/// (so the Mini App is visually the SAME product), the official `telegram-web-app.js` as the
/// FIRST script (the Telegram requirement), a greeting slot, the live region, and the bootstrap
/// script. Static — identity only ever comes from the header the script attaches. `boot`, when
/// present, is the deep `/tg/...` path the script opens first (with the header) instead of the
/// catalog; it is HTML-escaped into a `data-boot` attribute, never interpolated into script.
fn shell_page(boot: Option<&str>) -> String {
    let boot_attr = match boot {
        Some(path) => format!(" data-boot=\"{}\"", crate::esc(path)),
        None => String::new(),
    };
    format!(
        "<!doctype html><html lang=\"en\"><head><meta charset=\"utf-8\">\
         <meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\
         <title>DreggNet — Telegram Mini App</title>\
         <script src=\"https://telegram.org/js/telegram-web-app.js\"></script>\
         {style}</head><body>\
         <main class=\"session\">\
         <p class=\"prose\" id=\"tg-greet\">DreggNet offerings — every move is a receipt.</p>\
         <div id=\"tg-root\"{boot_attr}><p class=\"prose\">Loading the catalog…</p></div>\
         </main><script src=\"/tg/static/app.js\"></script></body></html>",
        style = crate::STYLE,
        boot_attr = boot_attr,
    )
}

// ─────────────────────────────────────────────────────────────────────────────
// The cross-platform LINK ceremony (`/tg/link/*`) — bind this Telegram account to a
// user-held root key K, recorded in the shared registry so Discord-you and Telegram-you
// resolve to ONE human. The SERVER half; the client (passkey / extension-relay) signs the
// claim with K and POSTs it here. initData authenticates WHICH Telegram uid; K's signature
// attests the human — the same two-sided trust the Discord `/link-prove` ceremony makes.
// ─────────────────────────────────────────────────────────────────────────────

/// The stable server key for link-challenge freshness, domain-separated from the initData HMAC
/// and derived from the identity master secret so it survives restarts without a separate env.
fn link_challenge_key(bot_secret: &[u8; 32]) -> [u8; 32] {
    hmac_sha256(b"dregg-tg-link-challenge-v1", bot_secret)
}

fn now_unix_secs() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0)
}

/// The link-claim submission wire: root key K signed a [`webauth_core::link_claim`] message
/// binding (`telegram`, this uid, this custodial pubkey, K, the challenge) — the client sends the
/// root pubkey, the signature, and the challenge it signed over.
#[derive(Debug, Clone, Deserialize)]
struct TgLinkForm {
    root_pubkey_hex: String,
    signature_hex: String,
    challenge: String,
}

/// `GET /tg/link/challenge` — initData-authenticated. Returns a fresh nonce'd challenge plus the
/// EXACT fields the link_claim must bind (platform, uid, this Telegram account's custodial pubkey),
/// so the client can build + sign the canonical message with root key K.
async fn get_tg_link_challenge(
    State(state): State<Arc<TgMiniAppState>>,
    headers: HeaderMap,
) -> Response {
    let corr = audit::correlation_id();
    let route = "GET /tg/link/challenge";
    let user = match verified_user(&state, &headers, &corr, route) {
        Ok(u) => u,
        Err(resp) => return resp,
    };
    let custodial = state.identity_for(user.user_id).0;
    let challenge = webauth_core::challenge::issue(
        &link_challenge_key(&state.bot_secret),
        now_unix_secs(),
        300,
    );
    audit::log().emit(
        audit::AuditEvent::new(
            "tg-miniapp",
            audit::Actor::initdata_verified(user.user_id.to_string(), Some(custodial.clone())),
            audit::Surface::Http,
            audit::Input::new(route, serde_json::Value::Null),
        )
        .correlated(&corr)
        .decided("routed", "link_challenge_issued"),
    );
    axum::Json(serde_json::json!({
        "platform": "telegram",
        "platform_uid": user.user_id.to_string(),
        "custodial_pubkey_hex": custodial,
        "challenge": challenge,
        "link_domain": webauth_core::link_claim::LINK_CLAIM_DOMAIN,
    }))
    .into_response()
}

/// `POST /tg/link` — verify a root-key-signed link claim for this initData-authenticated Telegram
/// account and record `(telegram custodial → root K)` in the shared registry. Fail-closed:
/// missing/stale/forged claim → refused, nothing recorded.
async fn post_tg_link(
    State(state): State<Arc<TgMiniAppState>>,
    headers: HeaderMap,
    Form(form): Form<TgLinkForm>,
) -> Response {
    let corr = audit::correlation_id();
    let route = "POST /tg/link";
    let user = match verified_user(&state, &headers, &corr, route) {
        Ok(u) => u,
        Err(resp) => return resp,
    };
    let uid_str = user.user_id.to_string();
    let custodial = state.identity_for(user.user_id).0;
    let ev = |kind: &'static str, reason: &'static str| {
        audit::AuditEvent::new(
            "tg-miniapp",
            audit::Actor::initdata_verified(uid_str.clone(), Some(custodial.clone())),
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
        "telegram",
        &uid_str,
        &custodial,
        &root_pubkey,
        &form.challenge,
        &signature,
        now_unix_secs(),
    ) {
        Ok(()) => {
            // Single-use: consume the challenge nonce so a captured claim can't be replayed within
            // its TTL (the contract link_claim.rs names — "record the spent challenge via replay").
            if let Some((nonce, exp)) = webauth_core::challenge::nonce_and_exp(&form.challenge) {
                if !state.link_replay.consume(nonce, exp, now_unix_secs()) {
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
                platform: "telegram".to_string(),
                platform_uid: uid_str.clone(),
                custodial_pubkey_hex: custodial.clone(),
                verified_at: now_unix_secs(),
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
            axum::Json(serde_json::json!({
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

// ─────────────────────────────────────────────────────────────────────────────
// Tests — the three families the design pins: vector+tamper, identity parity,
// end-to-end custodial Signed turn.
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use axum::body::Body;
    use axum::http::Request;
    use dungeon_on_dregg::{KP_CLAIM_RED, KP_PRESS_ON};
    use tower::ServiceExt; // oneshot

    /// A fixture bot token (never a real one) — the validation algorithm is token-generic.
    const TOKEN: &str = "7654321:TEST-fixture-token-AAAA";

    fn hex32(b: &[u8; 32]) -> String {
        let mut s = String::with_capacity(64);
        for x in b {
            s.push_str(&format!("{x:02x}"));
        }
        s
    }

    /// Minimal percent-encoding for the fixture (everything non-unreserved as %XX).
    fn url_encode(s: &str) -> String {
        let mut out = String::new();
        for b in s.bytes() {
            match b {
                b'A'..=b'Z' | b'a'..=b'z' | b'0'..=b'9' | b'-' | b'_' | b'.' | b'~' => {
                    out.push(b as char)
                }
                _ => out.push_str(&format!("%{b:02X}")),
            }
        }
        out
    }

    /// Build a VALID initData string for `uid`/`auth_date` under `token` by running the pinned
    /// algorithm FORWARD (sorted data-check-string, HMAC chain) — the acceptance vector.
    fn fixture_init_data(token: &str, uid: u64, auth_date: u64) -> String {
        let user_json = format!(r#"{{"id":{uid},"first_name":"Ember","username":"emberian"}}"#);
        // Sorted by key: auth_date < query_id < user.
        let dcs = format!("auth_date={auth_date}\nquery_id=AAtest\nuser={user_json}");
        let secret = webapp_secret_key(token);
        let hash = hex32(&hmac_sha256(&secret, dcs.as_bytes()));
        format!(
            "query_id=AAtest&user={}&auth_date={auth_date}&hash={hash}",
            url_encode(&user_json)
        )
    }

    // ── Family (i): the vector accepts; every tamper class refuses, named. ──

    #[test]
    fn a_correctly_hmacd_fixture_is_accepted_with_the_exact_uid() {
        let secret = webapp_secret_key(TOKEN);
        let init = fixture_init_data(TOKEN, 42_424_242, 1_760_000_000);
        let u = validate_init_data_at(&secret, &init, 1_760_000_100, 86_400)
            .expect("the genuine envelope validates");
        assert_eq!(u.user_id, 42_424_242);
        assert_eq!(u.auth_date, 1_760_000_000);
        assert_eq!(u.first_name.as_deref(), Some("Ember"));
        assert_eq!(u.username.as_deref(), Some("emberian"));
    }

    /// Build a VALID initData INCLUDING a `signature` field — the real-Telegram shape (2024+),
    /// where the HMAC data-check-string COVERS the signature (sorted `auth_date < query_id <
    /// signature < user`, excluding only `hash`).
    fn fixture_init_data_with_signature(
        token: &str,
        uid: u64,
        auth_date: u64,
        signature: &str,
    ) -> String {
        let user_json = format!(r#"{{"id":{uid},"first_name":"Ember","username":"emberian"}}"#);
        let dcs = format!(
            "auth_date={auth_date}\nquery_id=AAtest\nsignature={signature}\nuser={user_json}"
        );
        let secret = webapp_secret_key(token);
        let hash = hex32(&hmac_sha256(&secret, dcs.as_bytes()));
        format!(
            "query_id=AAtest&user={}&auth_date={auth_date}&signature={signature}&hash={hash}",
            url_encode(&user_json)
        )
    }

    /// REGRESSION (2026-07-17, ember's live @dreggnet_bot Mini App): real Telegram initData carries
    /// a third-party Ed25519 `signature` field, and the HMAC `hash` COVERS it (the DCS excludes only
    /// `hash`). The original code excluded `signature` too and rejected every real Mini App request.
    /// This pins the fix from BOTH sides so it can never silently regress.
    #[test]
    fn the_signature_field_is_covered_by_the_hmac() {
        let secret = webapp_secret_key(TOKEN);
        // (a) a signature that is part of the signed DCS validates — the real-Telegram acceptance
        //     vector. If someone re-excludes `signature`, this line panics.
        let good = fixture_init_data_with_signature(TOKEN, 7, 1_760_000_000, "sig-abc");
        assert_eq!(
            validate_init_data_at(&secret, &good, 1_760_000_100, 86_400)
                .expect("signature IS covered by the HMAC data-check-string")
                .user_id,
            7
        );
        // (b) a `signature` APPENDED to a signature-less hash must be REFUSED — excluding signature
        //     (the bug) would WRONGLY accept this.
        let bad = format!(
            "{}&signature=sig-abc",
            fixture_init_data(TOKEN, 7, 1_760_000_000)
        );
        assert_eq!(
            validate_init_data_at(&secret, &bad, 1_760_000_100, 86_400),
            Err(InitDataError::BadHmac)
        );
    }

    #[test]
    fn every_tamper_class_is_refused_by_its_named_gate() {
        let secret = webapp_secret_key(TOKEN);
        let auth = 1_760_000_000u64;
        let now = auth + 100;
        let init = fixture_init_data(TOKEN, 42, auth);

        // TAMPERED HASH: flip one hex digit → BadHmac (403).
        let mut chars: Vec<char> = init.chars().collect();
        let last = chars.len() - 1;
        chars[last] = if chars[last] == '0' { '1' } else { '0' };
        let flipped: String = chars.into_iter().collect();
        let e = validate_init_data_at(&secret, &flipped, now, 86_400).unwrap_err();
        assert_eq!(e, InitDataError::BadHmac);
        assert_eq!(e.http_status(), StatusCode::FORBIDDEN);

        // FORGED UID: swap the user pair for a different uid, keep the genuine hash → BadHmac.
        // (This is the hard rule: a client-claimed uid without a valid HMAC is refused.)
        let forged_user = url_encode(r#"{"id":99999,"first_name":"Mallory"}"#);
        let genuine_user = url_encode(r#"{"id":42,"first_name":"Ember","username":"emberian"}"#);
        let forged = init.replace(&genuine_user, &forged_user);
        assert_ne!(forged, init, "the swap really happened");
        assert_eq!(
            validate_init_data_at(&secret, &forged, now, 86_400).unwrap_err(),
            InitDataError::BadHmac
        );

        // TAMPERED COVERED FIELD: change query_id, keep the hash → BadHmac (HMAC covers ALL pairs).
        let extra = init.replace("query_id=AAtest", "query_id=AAtamper");
        assert_eq!(
            validate_init_data_at(&secret, &extra, now, 86_400).unwrap_err(),
            InitDataError::BadHmac
        );

        // ADDED PAIR the DCS did not cover at signing time → BadHmac.
        let appended = format!("{init}&bonus=1");
        assert_eq!(
            validate_init_data_at(&secret, &appended, now, 86_400).unwrap_err(),
            InitDataError::BadHmac
        );

        // DROPPED HASH → MissingHash (400).
        let hashless = init
            .split('&')
            .filter(|p| !p.starts_with("hash="))
            .collect::<Vec<_>>()
            .join("&");
        let e = validate_init_data_at(&secret, &hashless, now, 86_400).unwrap_err();
        assert_eq!(e, InitDataError::MissingHash);
        assert_eq!(e.http_status(), StatusCode::BAD_REQUEST);

        // NON-HEX HASH → MalformedHash (400), refused before any comparison.
        let badhex = format!("{hashless}&hash={}", "z".repeat(64));
        assert_eq!(
            validate_init_data_at(&secret, &badhex, now, 86_400).unwrap_err(),
            InitDataError::MalformedHash
        );

        // STALE: a GENUINE envelope past the window → Stale (403). Both polarities: at the
        // window edge it still validates.
        let e = validate_init_data_at(&secret, &init, auth + 86_401, 86_400).unwrap_err();
        assert!(matches!(e, InitDataError::Stale { .. }), "{e:?}");
        assert_eq!(e.http_status(), StatusCode::FORBIDDEN);
        validate_init_data_at(&secret, &init, auth + 86_400, 86_400)
            .expect("exactly at the window edge is still fresh");

        // FUTURE: auth_date beyond the 300s skew guard → FromFuture (403); within it, accepted.
        let future = fixture_init_data(TOKEN, 42, auth + 400);
        let e = validate_init_data_at(&secret, &future, auth, 86_400).unwrap_err();
        assert!(matches!(e, InitDataError::FromFuture { .. }), "{e:?}");
        let near_future = fixture_init_data(TOKEN, 42, auth + 200);
        validate_init_data_at(&secret, &near_future, auth, 86_400)
            .expect("within the skew guard is accepted");

        // WRONG TOKEN: a genuine-under-another-token envelope → BadHmac here.
        let other = fixture_init_data("1111:OTHER-token", 42, auth);
        assert_eq!(
            validate_init_data_at(&secret, &other, now, 86_400).unwrap_err(),
            InitDataError::BadHmac
        );
    }

    // ── Family (ii): identity parity — validate → derive == the bot's own derivation. ──

    #[test]
    fn the_verified_identity_equals_the_telegram_derived_identity_for_the_same_uid() {
        let bot_secret = [42u8; 32];
        let uid = 42_424_242u64;

        // The path the GET handlers take.
        let via_cipherclerk = TelegramCipherclerk::derive(&bot_secret, uid).identity();
        // The path the POST handler takes (the custodial signer's identity).
        let via_signer = TurnSigner::from_seed(seed_for(&bot_secret, uid)).identity();
        assert_eq!(
            via_signer, via_cipherclerk,
            "the Mini App signer and the in-chat cipherclerk are ONE identity"
        );

        // And end-to-end through validation: the uid recovered from a genuine envelope derives
        // the same identity again.
        let secret = webapp_secret_key(TOKEN);
        let init = fixture_init_data(TOKEN, uid, 1_760_000_000);
        let verified = validate_init_data_at(&secret, &init, 1_760_000_100, 86_400).unwrap();
        assert_eq!(
            TelegramCipherclerk::derive(&bot_secret, verified.user_id).identity(),
            via_cipherclerk
        );
    }

    // ── Family (iii): end-to-end — a Mini App POST lands a VERIFIED Signed turn. ──

    fn test_state() -> (Arc<TgMiniAppState>, Arc<CatalogState>, [u8; 32]) {
        let catalog = Arc::new(CatalogState::new());
        let bot_secret = [42u8; 32];
        let state = Arc::new(TgMiniAppState::new(
            Arc::clone(&catalog),
            TOKEN,
            bot_secret,
            86_400,
        ));
        (state, catalog, bot_secret)
    }

    /// A fresh initData header value for `uid`, minted "now" (so freshness always passes).
    fn header_for(uid: u64) -> String {
        fixture_init_data(TOKEN, uid, unix_now())
    }

    async fn send(
        app: &Router,
        method: &str,
        uri: &str,
        init_data: Option<&str>,
        form_body: Option<&str>,
    ) -> (StatusCode, String) {
        let mut req = Request::builder().method(method).uri(uri);
        if let Some(h) = init_data {
            req = req.header(INIT_DATA_HEADER, h);
        }
        let body = match form_body {
            Some(b) => {
                req = req.header("content-type", "application/x-www-form-urlencoded");
                Body::from(b.to_string())
            }
            None => Body::empty(),
        };
        let resp = app.clone().oneshot(req.body(body).unwrap()).await.unwrap();
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

    /// The cross-platform link ceremony: an initData-authenticated Telegram account presents a
    /// claim signed by root key K binding it to K — it verifies + records; a forged signature is
    /// refused. (The registry write is redirected to a temp dir so the test does not touch the
    /// real shared store.)
    #[tokio::test(flavor = "multi_thread")]
    async fn the_tg_link_ceremony_verifies_a_root_claim_and_refuses_a_forgery() {
        use ed25519_dalek::{Signer, SigningKey};
        let tmp = std::env::temp_dir().join(format!("dregg-linktest-{}", std::process::id()));
        unsafe { std::env::set_var("DREGG_LINK_DIR", &tmp) };

        let (state, _catalog, bot_secret) = test_state();
        let app = tg_miniapp_router(state);
        let uid = 555_000_111u64;
        let init = header_for(uid);
        let custodial = TelegramCipherclerk::derive(&bot_secret, uid).identity().0;
        let challenge =
            webauth_core::challenge::issue(&link_challenge_key(&bot_secret), unix_now(), 300);

        let root = SigningKey::from_bytes(&[5u8; 32]);
        let root_hex = hex32(&root.verifying_key().to_bytes());
        let msg = webauth_core::link_claim::link_claim_message(
            "telegram",
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

        // (a) a genuine root-key claim links.
        let body = format!(
            "root_pubkey_hex={root_hex}&signature_hex={}&challenge={}",
            sig_hex(&root),
            url_encode(&challenge)
        );
        let (st, out) = send(&app, "POST", "/tg/link", Some(&init), Some(&body)).await;
        assert_eq!(st, StatusCode::OK, "genuine link claim verifies: {out}");
        assert!(out.contains("\"ok\":true"), "{out}");

        // (b) a forged signature (a different key over the same message) is refused.
        let attacker = SigningKey::from_bytes(&[9u8; 32]);
        let forged = format!(
            "root_pubkey_hex={root_hex}&signature_hex={}&challenge={}",
            sig_hex(&attacker),
            url_encode(&challenge)
        );
        let (st2, _) = send(&app, "POST", "/tg/link", Some(&init), Some(&forged)).await;
        assert_eq!(st2, StatusCode::FORBIDDEN, "a forged claim is refused");

        let _ = std::fs::remove_dir_all(&tmp);
    }

    #[tokio::test(flavor = "multi_thread")]
    async fn a_mini_app_post_lands_a_verified_signed_turn_and_the_next_counter_follows() {
        let (state, catalog, bot_secret) = test_state();
        let app = tg_miniapp_router(state);
        let uid = 42_424_242u64;
        let init = header_for(uid);
        let expected_ident = TelegramCipherclerk::derive(&bot_secret, uid).identity();

        // The catalog fragment renders for the verified viewer and links the per-user session.
        let (status, body) = send(&app, "GET", "/tg/offerings", Some(&init), None).await;
        assert_eq!(status, StatusCode::OK, "{body}");
        assert!(body.contains("data-tg-session"), "{body}");
        assert!(
            body.contains(&expected_ident.0[..16]),
            "the listing names the verified identity: {body}"
        );

        // Open the session as the verified viewer.
        let sid = "tg-e2e-1";
        let uri = format!("/tg/offerings/dungeon/session/{sid}");
        let (status, opened) = send(&app, "GET", &uri, Some(&init), None).await;
        assert_eq!(status, StatusCode::OK);
        let routed_epoch = catalog
            .bound_game_session("dungeon", &SessionId::new(sid))
            .expect("Mini App GET binds the shared renderer to a live game epoch");

        // POST one turn: it lands through the common game spine. The shared
        // result card carries signed provenance without publishing the actor.
        let act = format!("{uri}/act");
        let (status, body) = send(
            &app,
            "POST",
            &act,
            Some(&init),
            Some(&format!(
                "turn=choose&arg={}&{}",
                KP_PRESS_ON,
                game_authority_fields(&opened)
            )),
        )
        .await;
        assert_eq!(status, StatusCode::OK, "{body}");
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
                .expect("Mini App POST retains the same live route"),
            routed_epoch
        );

        // A second POST consumes the NEXT counter (the atomic floor-read works across turns).
        let (status, body) = send(
            &app,
            "POST",
            &act,
            Some(&init),
            Some(&format!(
                "turn=choose&arg={}&{}",
                KP_CLAIM_RED,
                game_authority_fields(&body)
            )),
        )
        .await;
        assert_eq!(status, StatusCode::OK, "{body}");
        assert!(body.contains("Turn committed"), "{body}");

        // GROUND TRUTH: both landed moves carry Attribution::Signed provenance, attributed to
        // the telegram-derived identity — read off the host's own move log, not the banner.
        let sid_owned = SessionId::new(sid);
        let log = catalog
            .host
            .run(move |h| h.move_log("dungeon", &sid_owned))
            .expect("the session has a move log");
        assert_eq!(log.moves.len(), 2, "two real turns landed");
        for m in &log.moves {
            assert!(
                m.attribution.is_signed(),
                "every Mini App turn is Signed provenance: {:?}",
                m.attribution
            );
            assert_eq!(m.actor, expected_ident);
        }

        // And the committed chain re-verifies by replay (genesis + 2 turns).
        let report = catalog
            .verify("dungeon", &SessionId::new(sid))
            .expect("verify");
        assert!(report.verified);
        assert_eq!(report.turns, 3);
    }

    #[tokio::test(flavor = "multi_thread")]
    async fn the_route_refuses_missing_tampered_and_forged_identities() {
        let (state, catalog, _) = test_state();
        let app = tg_miniapp_router(state);
        let uri = "/tg/offerings/dungeon/session/tg-refuse-1";
        let act = format!("{uri}/act");
        let body_form = format!("turn=choose&arg={}", KP_PRESS_ON);

        // MISSING initData → 401 (and no session opens, no turn lands).
        let (status, _) = send(&app, "POST", &act, None, Some(&body_form)).await;
        assert_eq!(status, StatusCode::UNAUTHORIZED);

        // TAMPERED: a valid envelope with its hash flipped → 403.
        let init = header_for(7);
        let tampered = {
            let mut c: Vec<char> = init.chars().collect();
            let last = c.len() - 1;
            c[last] = if c[last] == '0' { '1' } else { '0' };
            c.into_iter().collect::<String>()
        };
        let (status, body) = send(&app, "POST", &act, Some(&tampered), Some(&body_form)).await;
        assert_eq!(status, StatusCode::FORBIDDEN, "{body}");

        // FORGED UID: a client-claimed uid spliced into a genuinely-signed envelope → 403
        // (the HMAC covers the user pair; no valid HMAC, no identity — the hard rule).
        let genuine_user = url_encode(r#"{"id":7,"first_name":"Ember","username":"emberian"}"#);
        let forged_user = url_encode(r#"{"id":31337,"first_name":"Mallory"}"#);
        let forged = init.replace(&genuine_user, &forged_user);
        assert_ne!(forged, init);
        let (status, body) = send(&app, "POST", &act, Some(&forged), Some(&body_form)).await;
        assert_eq!(status, StatusCode::FORBIDDEN, "{body}");

        // STALE: a genuine envelope minted outside the freshness window → 403.
        let stale = fixture_init_data(TOKEN, 7, unix_now().saturating_sub(90_000));
        let (status, body) = send(&app, "POST", &act, Some(&stale), Some(&body_form)).await;
        assert_eq!(status, StatusCode::FORBIDDEN, "{body}");
        assert!(body.contains("stale"), "{body}");

        // ANTI-GHOST GROUND TRUTH: none of the refusals opened the session or landed anything.
        let sid = SessionId::new("tg-refuse-1");
        assert!(
            !catalog.is_open("dungeon", &sid),
            "a refused request opens no session"
        );
    }

    #[tokio::test(flavor = "multi_thread")]
    async fn a_cold_deep_link_get_serves_the_shell_with_the_boot_target_and_opens_no_session() {
        let (state, catalog, _) = test_state();
        let app = tg_miniapp_router(state);
        // The bot's `web_app` launch buttons deep-link exactly this shape (chat-scoped
        // `tg:{chat}` session id), and Telegram's web-view opens it as a document navigation:
        // NO header exists yet — initData only materializes in JS. The route must hand back
        // the bootable shell, not a 401 dead end.
        let uri = "/tg/offerings/dungeon/session/tg:42";
        let (status, body) = send(&app, "GET", uri, None, None).await;
        assert_eq!(status, StatusCode::OK, "{body}");
        assert!(body.contains("https://telegram.org/js/telegram-web-app.js"));
        assert!(
            body.contains("data-boot=\"/tg/offerings/dungeon/session/tg%3A42\""),
            "the shell carries the deep path as its boot target: {body}"
        );
        // Serving the shell touched NO session state.
        assert!(
            !catalog.is_open("dungeon", &SessionId::new("tg:42")),
            "a cold shell serve opens no session"
        );
        // A header-less FRAGMENT fetch of the same path keeps the hard refusal — the soft
        // path exists ONLY for document navigations.
        let resp = app
            .clone()
            .oneshot(
                Request::builder()
                    .method("GET")
                    .uri(uri)
                    .header("x-fragment", "1")
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap();
        assert_eq!(resp.status(), StatusCode::UNAUTHORIZED);
    }

    #[tokio::test(flavor = "multi_thread")]
    async fn the_shell_serves_without_auth_and_carries_the_pinned_js_surface() {
        let (state, _, _) = test_state();
        let app = tg_miniapp_router(state);
        let response = app
            .clone()
            .oneshot(
                Request::builder()
                    .method("GET")
                    .uri("/tg")
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap();
        assert_eq!(response.status(), StatusCode::OK);
        let csp = response
            .headers()
            .get(header::CONTENT_SECURITY_POLICY)
            .expect("Telegram shell ships a CSP")
            .to_str()
            .unwrap();
        assert!(
            csp.contains("script-src 'self' https://telegram.org"),
            "{csp}"
        );
        assert!(!csp.contains("script-src 'unsafe-inline'"), "{csp}");
        let body = String::from_utf8(
            axum::body::to_bytes(response.into_body(), usize::MAX)
                .await
                .unwrap()
                .to_vec(),
        )
        .unwrap();
        // The official bridge script is FIRST; our bootstrap is same-origin.
        assert!(body.contains("https://telegram.org/js/telegram-web-app.js"));
        assert!(body.contains("/tg/static/app.js"));
        let (status, script) = send(&app, "GET", "/tg/static/app.js", None, None).await;
        assert_eq!(status, StatusCode::OK);
        assert!(script.contains("tg.ready()"));
        assert!(script.contains("tg.expand()"));
        assert!(script.contains("themeChanged"));
        assert!(script.contains("BackButton"));
        assert!(script.contains("X-Telegram-Init-Data"));
        // initDataUnsafe appears only in its display-only role.
        assert!(script.contains("initDataUnsafe"));
        // Opaque operation files ride as raw bytes; refusal bodies never become markup.
        assert!(script.contains("body: file"), "{script}");
        assert!(
            !script.contains("new URLSearchParams(new FormData(form))"),
            "{script}"
        );
        assert!(
            script.contains("box.textContent = String(message)"),
            "{script}"
        );
        assert!(script.contains("if (!resp.ok)"), "{script}");
        assert!(
            script.contains("Refused a non-HTML fragment response"),
            "{script}"
        );
    }

    #[tokio::test(flavor = "multi_thread")]
    async fn native_fragment_keeps_signed_provenance_resume_and_replay_on_telegram() {
        let (state, _, _) = test_state();
        let app = tg_miniapp_router(state);
        let init = header_for(77);
        let uri = "/tg/offerings/dungeon/session/hostile.tab-one";
        let response = app
            .oneshot(
                Request::builder()
                    .method("GET")
                    .uri(uri)
                    .header(INIT_DATA_HEADER, init)
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
            body.contains("href=\"/tg/offerings/dungeon/session/hostile.tab-one\""),
            "{body}"
        );
        assert!(
            body.contains(
                "data-tg-verify=\"/tg/offerings/dungeon/session/hostile.tab-one/verify\""
            ),
            "{body}"
        );
        assert!(!body.contains("href=\"/offerings/"), "{body}");
        assert_eq!(
            tg_session_path("dungeon", "quote\"?hash#slash/"),
            "/tg/offerings/dungeon/session/quote%22%3Fhash%23slash%2F"
        );
    }
}
