//! # `seed_identity` — a player identity you can WRITE DOWN and get back.
//!
//! Before this module the web surface had exactly one identity: the `dregg_user` visitor cookie
//! ([`crate::web_identity_http`]) — 128 random bits minted on first request, durable only as long
//! as the browser keeps the cookie. **Clear your cookies and you were a new person, with nothing to
//! recover with.** The flagship game was worse: `/descent/play`'s `browserActor()` mints a random
//! `web:<hex>` pseudonym into `localStorage`, so the actor the native journal chain BINDS TO — the
//! name on the leaderboard — died with a cleared site-data.
//!
//! This adds the missing thing: **24 words that reproduce your identity on any device.**
//!
//! ## The progression (all three rungs, named)
//!
//! 1. **Anonymous cookie** — the pre-existing default, UNCHANGED. A visitor who wants to click a
//!    game clicks it; nothing on this page is in front of play. Their identity is
//!    `blake3(visitor-label)`, durable-but-unrecoverable, and that is stated on the page.
//! 2. **Claimed seed identity** — this module. 24 BIP39 words → an Ed25519 keypair → **the identity
//!    IS the public key** (`DreggIdentity` = the 64-char lowercase pubkey hex, byte-identical to
//!    what [`dreggnet_offerings::verify_signed`] yields for that key). Opt-in, reversible, and it
//!    survives a cleared cookie because the words reproduce it.
//! 3. **Linked platforms** — NOT this module's job. `webauth-core::linked_platforms` proves "one
//!    human across ≥N platforms without revealing which accounts", over a **root key K**. The
//!    Discord/Telegram link ceremony ([`crate::tg_link_page`], `discord_activity::LINK_APP_JS`)
//!    already holds such a K client-side — wrapped in `localStorage` under WebAuthn-PRF or a
//!    600k-round PBKDF2 passphrase — and its human backup is **64 hex characters**, which is the
//!    part a person actually loses. A phrase from this module derives an Ed25519 seed by the SAME
//!    convention the CLI uses, so it is exactly the shape that K wants; wiring it is a follow-up
//!    (see the residuals at the bottom of this doc).
//!
//! ## The mechanism — reused, not invented
//!
//! Nothing cryptographic is authored here. The whole derivation is three existing calls:
//!
//! ```text
//! dregg_sdk::mnemonic::generate_mnemonic()             // 256 bits + an 8-bit SHA-256 checksum
//!                                                      //   → 24 words of the BIP39 English list
//! dregg_sdk::mnemonic::mnemonic_to_seed(phrase, "")    // validates word count / list / CHECKSUM,
//!                                                      //   then BLAKE3 derive_key → a 64-byte seed
//! dregg_sdk::mnemonic::derive_keypair(&seed, "dregg/0")// BLAKE3 derive_key → an Ed25519 seed,
//!                                                      //   ed25519-dalek → the public key
//! ```
//!
//! [`DERIVATION_PATH`] is `"dregg/0"` — **the same constant `cli/src/commands/id.rs` pins** (and
//! `dregg_sdk::cipherclerk`'s `from_mnemonic`). That is not decoration: it means a phrase claimed
//! here, typed into `dregg id import`, yields the same signing key, so the CLI can land
//! `Attribution::Signed` turns on `POST /offerings/{key}/session/{id}/act-signed` **as the identity
//! this page shows you**. `tests/seed_identity_web.rs` proves that join end to end rather than
//! asserting it here.
//!
//! ## ⚑ WHERE THE KEY LIVES, and what that exposes
//!
//! **Nowhere. There is no stored secret, on either side.** A request derives the keypair from the
//! phrase, keeps the 32-byte public key, and [`Zeroize`]s every byte of secret material before it
//! returns. Between requests the browser holds only:
//!
//! * `dregg_claim` — `dregg-id-<pubkey_hex>.<mac>`, `HttpOnly; SameSite=Lax` (`Secure` on https).
//!   The durable record of who you are. `mac` = 128 bits of `blake3::keyed_hash` under a
//!   server-only key, which is what stops a stranger from simply *typing* your (public!) key into
//!   their own cookie and being you — see [`claim_label`].
//! * `dregg_user` — the same label, in the acting slot the rest of the surface already reads.
//!
//! The three honest costs of that choice, none of them hidden from the player:
//!
//! 1. **The phrase transits the server.** It is generated server-side and typed back into a POST
//!    body on restore. We derive-and-zeroize in the request and never log or persist it, but a
//!    compromised host, or anything that captures request bodies, sees it in that window. The
//!    alternative — generate and derive in the browser, so the words never leave the device — needs
//!    a real BLAKE3 in JS (the Ed25519 half is already vendored: `assets/noble-ed25519.js`).
//!    Hand-rolling BLAKE3 is exactly what this repo forbids, so that is a **dependency decision,
//!    left for ember**, not something taken silently here.
//! 2. **The cookie is a bearer token.** Steal it and you play as that identity until it expires.
//!    `HttpOnly` keeps it out of `document.cookie`, so unlike a key in `localStorage` it is **not
//!    XSS-readable** — that was the deciding reason to put it here rather than in web storage. It
//!    is still only as private as the transport, and the *label* (which embeds the mac) is
//!    therefore a credential: a URL carrying `?user=dregg-id-…` hands over the same access a
//!    copied cookie would. It does not hand over the phrase, so it cannot be used to SIGN.
//! 3. **The web page does not sign.** Turns pressed in the browser land
//!    [`Attribution::Asserted`](dreggnet_offerings::Attribution::Asserted) under your public-key
//!    identity, because the server holds no key to sign with and the page has none either. Only a
//!    holder of the phrase (the CLI, the extension) reaches
//!    [`Attribution::Signed`](dreggnet_offerings::Attribution::Signed) +
//!    [`Custody::UserHeld`](dreggnet_offerings::Custody::UserHeld) on `/act-signed`. The page says
//!    this in those words; **a claimed identity is a durable NAME, not yet a browser credential.**
//!
//! ## Named residuals (work not done, stated as such)
//!
//! * The mac key is process-local unless `DREGGNET_WEB_IDENTITY_KEY` /
//!   `DREGGNET_WEB_SESSION_DIR` pin it, so a restart makes every claim cookie stop verifying and
//!   the player must re-enter their phrase. Fail-CLOSED (an old cookie degrades to a fresh
//!   anonymous visitor), never fail-open.
//! * A seat at an automatafl/tug table overwrites `dregg_user` with the seat label by design (the
//!   seat *is* the identity there). `dregg_claim` is a SEPARATE cookie precisely so sitting down
//!   cannot destroy a claim; `/identity` offers "act as my identity again" to restore the acting
//!   slot when you leave the table.
//! * `POST /descent/submit`'s procgen `player` string is still free-form. The native lane — the one
//!   `/descent/play` actually posts to — is bound, because its actor is injected into the page.
//! * `wasm/src/lib.rs::derive_keypair_from_mnemonic` claims to match `dregg-sdk` and **does not**:
//!   it feeds `blake3::hash(mnemonic_bytes)` to the KDF instead of the BIP39-validated entropy and
//!   skips the checksum entirely, so the same words give a DIFFERENT key there. Nothing in this
//!   module touches it; it is reported as a pre-existing cross-surface identity split.

use std::sync::OnceLock;

use axum::Router;
use axum::extract::Form;
use axum::http::{HeaderMap, StatusCode, header};
use axum::response::{Html, IntoResponse, Response};
use axum::routing::{get, post};
use dreggnet_offerings::DreggIdentity;
use serde::Deserialize;
use zeroize::Zeroize;

use dregg_sdk::mnemonic::{MnemonicError, derive_keypair, generate_mnemonic, mnemonic_to_seed};

use crate::{document_with_head, esc, hex_bytes};

// ─────────────────────────────────────────────────────────────────────────────
// THE CONSTANTS THAT MUST NOT DRIFT
// ─────────────────────────────────────────────────────────────────────────────

/// The BLAKE3 derivation path for a player's primary identity key.
///
/// ⚑ **This string is a cross-surface contract.** `cli/src/commands/id.rs` pins the same
/// `"dregg/0"`, as does `dregg_sdk::cipherclerk::AgentCipherclerk::from_mnemonic`. Change it here
/// and a phrase claimed on the web stops reproducing the CLI's key — the identity silently splits.
/// `tests/seed_identity_web.rs::the_derivation_path_matches_the_cli` is the tripwire.
pub const DERIVATION_PATH: &str = "dregg/0";

/// The durable record of a claimed identity — survives a seat label overwriting [`ACTING_COOKIE`].
pub const CLAIM_COOKIE: &str = "dregg_claim";

/// The acting-identity cookie the rest of the surface already reads
/// ([`crate::web_identity_http`]). A claim writes its label here too, so every existing route
/// attributes to the claimed identity with no per-route change.
const ACTING_COOKIE: &str = "dregg_user";

/// The prefix a claimed label wears. Deliberately unlike every other label in the system: a
/// visitor token is `visitor-<32 hex>`, a seat label is `<af1|tug1><a|b>-<32 hex>`, and a bare
/// derived identity is 64 hex chars with no prefix at all — so [`resolve_identity`] can never
/// mistake one for another.
const CLAIM_LABEL_PREFIX: &str = "dregg-id-";

/// The domain the label mac is bound under (never confusable with a seat label or a form token).
const MAC_DOMAIN: &[u8] = b"dregg-web-claimed-identity-v1:";

/// A claim cookie lasts a year, like the visitor token it replaces. The phrase is what makes this
/// number unimportant: an expired cookie costs a re-entry, not the identity.
const CLAIM_MAX_AGE_SECS: u64 = 365 * 24 * 60 * 60;

/// How many hex chars of the public key make the short human tag shown beside a name.
const SHORT_TAG_HEX: usize = 6;

/// The number of words a phrase has. 24 = 256 bits of entropy + an 8-bit checksum.
const PHRASE_WORDS: usize = 24;

// ─────────────────────────────────────────────────────────────────────────────
// THE LABEL: an unforgeable naming of a PUBLIC key
// ─────────────────────────────────────────────────────────────────────────────

/// The server-only key every claim label's mac is derived under. Resolution order (env pin →
/// a file under `DREGGNET_WEB_SESSION_DIR` → fresh per process) is
/// [`crate::table_seats::resolve_process_key`]'s, so this key gets the same ops story — and the
/// same fail-closed restart behaviour — as the table seat key.
fn identity_key() -> &'static [u8; 32] {
    static KEY: OnceLock<[u8; 32]> = OnceLock::new();
    KEY.get_or_init(|| {
        crate::table_seats::resolve_process_key(
            "DREGGNET_WEB_IDENTITY_KEY",
            "web-identity-key.bin",
            "claimed player identities",
        )
    })
}

/// **Mint the cookie label for a public key** — `dregg-id-<pubkey_hex>.<mac>`.
///
/// ⚑ The mac is the whole point, and it is not belt-and-braces. A public key is *public*: it is
/// printed on `/identity`, it rides in every `/act-signed` envelope, and it is the name on the
/// leaderboard. Without a mac, "the label is the identity" would mean anyone who read your key
/// could set their own cookie to it and BE you — strictly worse than the unguessable visitor token
/// this replaces. The mac makes the label sayable only by this server, so the label answers "this
/// browser presented the phrase (or was just handed this identity)", which is the claim a cookie
/// is allowed to make.
pub fn claim_label(pubkey_hex: &str) -> String {
    let mut input = Vec::with_capacity(MAC_DOMAIN.len() + pubkey_hex.len());
    input.extend_from_slice(MAC_DOMAIN);
    input.extend_from_slice(pubkey_hex.as_bytes());
    let mac = blake3::keyed_hash(identity_key(), &input);
    format!(
        "{CLAIM_LABEL_PREFIX}{pubkey_hex}.{}",
        hex_bytes(&mac.as_bytes()[..16])
    )
}

/// **Verify a claim label and recover the public key it names.** `None` for anything that is not a
/// well-formed, mac-valid claim label — a foreign prefix, a wrong-length key, a non-hex key, or a
/// forged/stale mac. Fail-closed: an unverifiable label is simply not a claim, and the caller
/// treats it as the ordinary asserted string it is.
pub fn parse_claim_label(label: &str) -> Option<String> {
    let rest = label.strip_prefix(CLAIM_LABEL_PREFIX)?;
    let (pubkey_hex, mac_hex) = rest.split_once('.')?;
    if pubkey_hex.len() != 64
        || !pubkey_hex
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
    {
        return None;
    }
    let expected = claim_label(pubkey_hex);
    let presented = format!("{CLAIM_LABEL_PREFIX}{pubkey_hex}.{mac_hex}");
    // Constant-time over the whole label: a mac oracle here would let a caller grind a valid label
    // for a key they do not hold the phrase for.
    if !constant_time_eq(expected.as_bytes(), presented.as_bytes()) {
        return None;
    }
    Some(pubkey_hex.to_string())
}

fn constant_time_eq(left: &[u8], right: &[u8]) -> bool {
    if left.len() != right.len() {
        return false;
    }
    let mut diff = 0_u8;
    for (l, r) in left.iter().zip(right.iter()) {
        diff |= l ^ r;
    }
    diff == 0
}

/// **THE JOIN — an asserted web label to the [`DreggIdentity`] the substrate attributes to.**
///
/// A mac-valid claim label resolves to the public key *itself*, so the claimed identity is
/// byte-identical to what [`dreggnet_offerings::verify_signed`] returns when that same key signs a
/// turn on `/act-signed`. Every other label keeps the historical `blake3(label)` derivation
/// ([`crate::web_identity`]) untouched — a visitor token, a seat label, an explicit `?user=`, and
/// the council electorate all hash exactly as before.
///
/// Without this the claim would be *worse* than useless: `blake3(dregg-id-…-<mac>)` folds the mac
/// into the identity, so a restart (which re-rolls the process key) would silently rename the
/// player and hand them a fresh, empty history — the precise failure the phrase exists to prevent.
pub fn resolve_identity(label: &str) -> DreggIdentity {
    match parse_claim_label(label) {
        Some(pubkey_hex) => DreggIdentity(pubkey_hex),
        None => crate::web_identity(label),
    }
}

/// The claimed public key this browser holds, from the durable [`CLAIM_COOKIE`] — `None` for an
/// ordinary anonymous visitor, and `None` for a forged/stale claim cookie.
pub fn claimed_pubkey(headers: &HeaderMap) -> Option<String> {
    cookie(headers, CLAIM_COOKIE).and_then(|label| parse_claim_label(&label))
}

/// The short human tag a claimed identity wears beside a name — the first [`SHORT_TAG_HEX`] hex
/// chars of the public key. Not a security boundary (it is 24 bits); it is the part of the
/// identity a person can read out loud and recognise on a leaderboard.
pub fn short_tag(pubkey_hex: &str) -> String {
    pubkey_hex.chars().take(SHORT_TAG_HEX).collect()
}

// ─────────────────────────────────────────────────────────────────────────────
// DERIVATION — the phrase in, a public key out, nothing kept
// ─────────────────────────────────────────────────────────────────────────────

/// **Derive the identity a phrase names.** Validates word count, wordlist membership, and the
/// SHA-256 checksum (so a mistyped word is refused rather than silently becoming a different,
/// empty identity), then derives at [`DERIVATION_PATH`]. Every intermediate secret — the 64-byte
/// KDF seed and the 32-byte Ed25519 seed — is zeroized before returning; only the public key
/// leaves.
pub fn derive_pubkey_hex(phrase: &str) -> Result<String, MnemonicError> {
    let mut seed = mnemonic_to_seed(phrase, "")?;
    let (public, mut secret) = derive_keypair(&seed, DERIVATION_PATH);
    seed.zeroize();
    secret.zeroize();
    Ok(hex_bytes(&public))
}

/// Normalize what a human typed into the restore box: lowercase, collapse all whitespace
/// (newlines from a pasted column, double spaces, a trailing return). A phrase differing only in
/// spacing is the SAME phrase, and being strict about that would be a recovery failure the player
/// cannot debug.
fn normalize_phrase(raw: &str) -> String {
    raw.split_whitespace()
        .map(|word| word.trim_matches(|c: char| !c.is_ascii_alphabetic()))
        .filter(|word| !word.is_empty())
        .map(|word| word.to_ascii_lowercase())
        .collect::<Vec<_>>()
        .join(" ")
}

// ─────────────────────────────────────────────────────────────────────────────
// COOKIES
// ─────────────────────────────────────────────────────────────────────────────

fn cookie(headers: &HeaderMap, name: &str) -> Option<String> {
    let needle = format!("{name}=");
    headers
        .get(header::COOKIE)
        .and_then(|value| value.to_str().ok())
        .and_then(|cookies| {
            cookies.split(';').find_map(|part| {
                part.trim()
                    .strip_prefix(&needle)
                    .filter(|value| !value.is_empty())
                    .map(str::to_string)
            })
        })
}

/// Whether this request arrived over https (directly, or through a proxy that says so) — the same
/// test [`crate::web_identity_http::bootstrap_visitor_identity`] applies, so the `Secure`
/// attribute appears in exactly the same deployments.
fn is_https(headers: &HeaderMap) -> bool {
    headers
        .get("x-forwarded-proto")
        .and_then(|value| value.to_str().ok())
        .is_some_and(|proto| proto.eq_ignore_ascii_case("https"))
}

fn set_cookie(name: &str, value: &str, max_age: u64, secure: bool) -> String {
    let secure = if secure { "; Secure" } else { "" };
    format!("{name}={value}; Path=/; Max-Age={max_age}; HttpOnly; SameSite=Lax{secure}")
}

/// A `303` to `/identity` that installs (or clears) both cookies. Redirect rather than a rendered
/// body so a reload cannot re-POST the claim, and `private, no-store` so no shared cache can ever
/// replay one player's identity to another browser.
fn redirect_with_cookies(cookies: Vec<String>) -> Response {
    let mut response = (StatusCode::SEE_OTHER, Html(String::new())).into_response();
    let headers = response.headers_mut();
    headers.insert(header::LOCATION, "/identity".parse().expect("static path"));
    headers.insert(
        header::CACHE_CONTROL,
        header::HeaderValue::from_static("private, no-store"),
    );
    for cookie in cookies {
        if let Ok(value) = header::HeaderValue::from_str(&cookie) {
            headers.append(header::SET_COOKIE, value);
        }
    }
    response
}

/// A page that must never be cached, proxied, or replayed — the one that shows the phrase.
fn no_store(body: String) -> Response {
    let mut response = Html(body).into_response();
    response.headers_mut().insert(
        header::CACHE_CONTROL,
        header::HeaderValue::from_static("private, no-store, max-age=0"),
    );
    // A phrase page must not leak its URL to anywhere the player then clicks.
    response.headers_mut().insert(
        header::REFERRER_POLICY,
        header::HeaderValue::from_static("no-referrer"),
    );
    response
}

// ─────────────────────────────────────────────────────────────────────────────
// THE ROUTES
// ─────────────────────────────────────────────────────────────────────────────

/// **Mount the identity door.** Additive: every path is under `/identity`, which overlaps nothing
/// on the merged app. Deliberately NOT layered with
/// [`crate::web_identity_http::bootstrap_visitor_identity`] — visiting the page that explains
/// identity should not silently mint one.
pub fn identity_router() -> Router {
    Router::new()
        .route("/identity", get(get_identity))
        .route("/identity/claim", post(post_claim))
        .route("/identity/confirm", post(post_confirm))
        .route("/identity/restore", post(post_restore))
        .route("/identity/release", post(post_release))
}

/// `GET /identity` — who you are, what that costs you today, and the two buttons.
async fn get_identity(headers: HeaderMap) -> Response {
    let claimed = claimed_pubkey(&headers);
    let acting = cookie(&headers, ACTING_COOKIE);
    no_store(identity_page(claimed.as_deref(), acting.as_deref(), None))
}

/// `POST /identity/claim` — generate a phrase and SHOW IT ONCE.
///
/// This deliberately sets **no cookie**. The identity is not yours until you say you have written
/// the words down ([`post_confirm`]), so a player who closes this tab is exactly who they were a
/// moment ago rather than silently re-homed onto an identity whose phrase is gone forever.
async fn post_claim(headers: HeaderMap) -> Response {
    let phrase = generate_mnemonic();
    let pubkey_hex = match derive_pubkey_hex(&phrase) {
        Ok(hex) => hex,
        // Unreachable: `generate_mnemonic` builds its own checksum. Answer honestly rather than
        // panicking a request thread on a should-not-happen.
        Err(error) => {
            return (
                StatusCode::INTERNAL_SERVER_ERROR,
                no_store(identity_page(
                    claimed_pubkey(&headers).as_deref(),
                    cookie(&headers, ACTING_COOKIE).as_deref(),
                    Some(&format!(
                        "Refused: the generated phrase did not validate ({error}) — nothing was claimed."
                    )),
                )),
            )
                .into_response();
        }
    };
    // The confirm token IS the label: mac'd, so `/identity/confirm` cannot be pointed at a public
    // key this server did not just generate (see `claim_label`). Without it, an unauthenticated
    // `pubkey_hex` field would let anyone mint a valid cookie for anyone else's published key.
    let token = claim_label(&pubkey_hex);
    no_store(phrase_page(&phrase, &pubkey_hex, &token))
}

/// The confirm form — the mac'd token, plus the checkbox the player must actually tick.
#[derive(Debug, Clone, Deserialize)]
pub struct ConfirmForm {
    /// The [`claim_label`] token minted by [`post_claim`].
    pub token: String,
    /// Present only when the "I have written these down" box is checked.
    #[serde(default)]
    pub saved: Option<String>,
}

/// `POST /identity/confirm` — take up the identity whose phrase was just shown.
async fn post_confirm(headers: HeaderMap, Form(form): Form<ConfirmForm>) -> Response {
    let Some(pubkey_hex) = parse_claim_label(&form.token) else {
        return (
            StatusCode::FORBIDDEN,
            no_store(identity_page(
                claimed_pubkey(&headers).as_deref(),
                cookie(&headers, ACTING_COOKIE).as_deref(),
                Some(
                    "Refused: that confirmation did not come from a phrase this server just \
                     generated (nothing was claimed). If the server restarted, generate a new \
                     phrase — do not reuse the one on the old page.",
                ),
            )),
        )
            .into_response();
    };
    if form.saved.is_none() {
        // Not an error page: send them back to the phrase they still have on screen would be
        // impossible (we no longer hold it), so say plainly what happened and offer a fresh one.
        return (
            StatusCode::BAD_REQUEST,
            no_store(identity_page(
                claimed_pubkey(&headers).as_deref(),
                cookie(&headers, ACTING_COOKIE).as_deref(),
                Some(
                    "Refused: the \"I have written these down\" box was not ticked, so nothing was \
                     claimed. That phrase is gone — the server does not keep it. Generate a new one.",
                ),
            )),
        )
            .into_response();
    }
    let label = claim_label(&pubkey_hex);
    let secure = is_https(&headers);
    redirect_with_cookies(vec![
        set_cookie(CLAIM_COOKIE, &label, CLAIM_MAX_AGE_SECS, secure),
        set_cookie(ACTING_COOKIE, &label, CLAIM_MAX_AGE_SECS, secure),
    ])
}

/// The restore form.
#[derive(Debug, Clone, Deserialize)]
pub struct RestoreForm {
    /// The 24 words, however the human pasted them.
    pub phrase: String,
}

/// `POST /identity/restore` — become the identity those 24 words name, on this device.
///
/// There is nothing to look up: the phrase *is* the identity, so this works on a browser that has
/// never seen this server, and it restores prior play because every game already files work under
/// the derived [`DreggIdentity`].
async fn post_restore(headers: HeaderMap, Form(form): Form<RestoreForm>) -> Response {
    let mut phrase = normalize_phrase(&form.phrase);
    let words = phrase.split_whitespace().count();
    let derived = derive_pubkey_hex(&phrase);
    phrase.zeroize();
    match derived {
        Ok(pubkey_hex) => {
            let label = claim_label(&pubkey_hex);
            let secure = is_https(&headers);
            redirect_with_cookies(vec![
                set_cookie(CLAIM_COOKIE, &label, CLAIM_MAX_AGE_SECS, secure),
                set_cookie(ACTING_COOKIE, &label, CLAIM_MAX_AGE_SECS, secure),
            ])
        }
        Err(error) => {
            // Say WHICH check failed — "invalid phrase" is useless to somebody holding a piece of
            // paper. A checksum failure in particular almost always means one mistyped word.
            let detail = match &error {
                MnemonicError::InvalidWordCount(_) => format!(
                    "that is {words} word{} — a dregg phrase is exactly {PHRASE_WORDS}.",
                    if words == 1 { "" } else { "s" }
                ),
                MnemonicError::UnknownWord(word) => format!(
                    "{:?} is not one of the 2048 words in the list — check that word's spelling.",
                    esc(word)
                ),
                MnemonicError::InvalidChecksum => "all 24 words are real words, but the phrase's \
                     built-in checksum does not match, which almost always means ONE word is wrong \
                     or two are swapped. Nothing was changed."
                    .to_string(),
            };
            (
                StatusCode::BAD_REQUEST,
                no_store(identity_page(
                    claimed_pubkey(&headers).as_deref(),
                    cookie(&headers, ACTING_COOKIE).as_deref(),
                    Some(&format!("Refused: {detail}")),
                )),
            )
                .into_response()
        }
    }
}

/// The release form — the same tick-to-confirm shape as the claim.
#[derive(Debug, Clone, Deserialize)]
pub struct ReleaseForm {
    /// Present only when the "I still have my 24 words" box is checked.
    #[serde(default)]
    pub understood: Option<String>,
}

/// `POST /identity/release` — sign this browser out of a claimed identity.
///
/// Clears BOTH cookies. The identity itself is untouched and un-deletable: the phrase still names
/// it, so this is "log out on this device", never "delete my account".
async fn post_release(headers: HeaderMap, Form(form): Form<ReleaseForm>) -> Response {
    if form.understood.is_none() {
        return (
            StatusCode::BAD_REQUEST,
            no_store(identity_page(
                claimed_pubkey(&headers).as_deref(),
                cookie(&headers, ACTING_COOKIE).as_deref(),
                Some(
                    "Refused: releasing this browser needs the confirmation box ticked — without \
                     your 24 words you would not be able to get back in.",
                ),
            )),
        )
            .into_response();
    }
    let secure = is_https(&headers);
    redirect_with_cookies(vec![
        set_cookie(CLAIM_COOKIE, "", 0, secure),
        set_cookie(ACTING_COOKIE, "", 0, secure),
    ])
}

// ─────────────────────────────────────────────────────────────────────────────
// THE PAGES
// ─────────────────────────────────────────────────────────────────────────────

/// Page-local styling. The product shell ([`document_with_head`]) carries the voice; these are the
/// three shapes it has no class for — the numbered word grid, the key readout, and the stakes box.
const IDENTITY_STYLE: &str = r##"<style>
.id-grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(9.5rem,1fr));gap:.4rem .8rem;
 margin:1rem 0;padding:1rem 1.1rem;border:1px solid var(--line,#2a2a2a);border-radius:4px;
 background:rgba(255,255,255,.02)}
.id-word{font-family:ui-monospace,SFMono-Regular,Menlo,monospace;font-size:1rem;letter-spacing:.01em;
 display:flex;gap:.5rem;align-items:baseline}
.id-word i{font-style:normal;opacity:.45;font-size:.8rem;min-width:1.4rem;text-align:right}
.id-plain{margin:.6rem 0 1.2rem;padding:.7rem .8rem;border:1px dashed var(--line,#2a2a2a);border-radius:4px;
 font-family:ui-monospace,SFMono-Regular,Menlo,monospace;font-size:.9rem;line-height:1.7;
 overflow-wrap:anywhere;opacity:.85}
.id-key{font-family:ui-monospace,SFMono-Regular,Menlo,monospace;font-size:.85rem;overflow-wrap:anywhere;
 opacity:.8}
.id-stakes{margin:1.2rem 0;padding:.9rem 1rem;border:1px solid rgba(201,106,94,.4);
 border-left:2px solid rgba(201,106,94,.8);border-radius:0 3px 3px 0;background:rgba(201,106,94,.05)}
.id-stakes h3{margin:0 0 .4rem;font-size:.95rem}
.id-stakes ul{margin:.3rem 0 0;padding-left:1.2rem}
.id-stakes li{margin:.2rem 0}
.id-honest{margin:1.4rem 0 0;padding:.85rem 1rem;border:1px solid var(--line,#2a2a2a);border-radius:4px;
 background:rgba(255,255,255,.015);font-size:.9rem;line-height:1.6}
.id-honest h3{margin:0 0 .45rem;font-size:.9rem;letter-spacing:.04em;text-transform:uppercase;opacity:.7}
.id-honest dt{font-weight:600;margin-top:.6rem}
.id-honest dd{margin:.15rem 0 0;opacity:.85}
.id-rungs{margin:1.2rem 0;padding:0;list-style:none;counter-reset:rung}
.id-rungs li{margin:.45rem 0;padding-left:2rem;position:relative;line-height:1.55}
.id-rungs li::before{counter-increment:rung;content:counter(rung);position:absolute;left:0;top:.05rem;
 width:1.35rem;height:1.35rem;border:1px solid var(--line,#2a2a2a);border-radius:50%;
 display:flex;align-items:center;justify-content:center;font-size:.75rem;opacity:.7}
.id-rungs li.now{font-weight:600}
.id-rungs li.later{opacity:.6}
.id-restore textarea{width:100%;min-height:5.5rem;padding:.6rem .7rem;border:1px solid var(--line,#2a2a2a);
 border-radius:4px;background:rgba(0,0,0,.25);color:inherit;font-family:ui-monospace,Menlo,monospace;
 font-size:.9rem;line-height:1.6}
.id-check{display:flex;gap:.55rem;align-items:flex-start;margin:1rem 0;line-height:1.5}
.id-check input{margin-top:.25rem}
.id-actions{display:flex;flex-wrap:wrap;gap:.6rem;align-items:center;margin:1.1rem 0 0}
.id-sep{margin:2rem 0;border:0;border-top:1px solid var(--line,#2a2a2a)}
</style>"##;

/// The honest-limits block, rendered on both pages. One source, so the page a player reads while
/// deciding and the page they read after claiming cannot say different things.
fn honest_block() -> String {
    "<div class=\"id-honest\"><h3>What this does and does not protect</h3><dl>\
     <dt>Where the key lives: nowhere.</dt>\
     <dd>Your 24 words are turned into a keypair inside the one request that needs it, and every \
     byte of secret material is wiped before the response goes out. Nothing is stored — not on the \
     server, and not in this browser.</dd>\
     <dt>The words pass through the server once.</dt>\
     <dd>They are generated here and typed back here to restore. We never write them to disk or to \
     a log, but that is a promise about this code, not a guarantee the shape of the system gives \
     you. Generating them entirely inside your browser is the next step and is not what this page \
     does today.</dd>\
     <dt>Your browser holds a cookie, not a key.</dt>\
     <dd>It is <code>HttpOnly</code>, so page scripts — including an injected one — cannot read it. \
     That is why the identity lives in a cookie rather than in <code>localStorage</code>, which any \
     script on the page can read. It is still a bearer token: whoever has it can play as you until \
     it expires, so treat a link containing <code>?user=dregg-id-…</code> the way you would treat a \
     password.</dd>\
     <dt>Pressing a button here is not a signature.</dt>\
     <dd>Turns you play in the browser are attributed to your public key, not signed by it — the \
     server has no key to sign with and neither does this page. A tool that holds your phrase (the \
     <code>dregg</code> CLI, the browser extension) can sign turns as this identity through \
     <code>/act-signed</code>, and only those turns carry a real signature.</dd>\
     <dt>A server restart may sign you out.</dt>\
     <dd>Unless the deployment pins its identity key, restarting re-rolls it and your cookie stops \
     verifying. You come back as a fresh anonymous visitor and re-enter your words — never as \
     somebody else.</dd>\
     </dl></div>"
        .to_string()
}

/// The three-rung progression, with the current rung marked. Same list on both pages.
fn rungs_block(claimed: bool) -> String {
    let anon = if claimed { "later" } else { "now" };
    let seed = if claimed { "now" } else { "later" };
    format!(
        "<ol class=\"id-rungs\">\
         <li class=\"{anon}\"><strong>Anonymous visitor.</strong> A cookie, minted the first time \
         you load a page. Nothing to remember, nothing to lose — except that clearing your cookies \
         ends that person permanently.</li>\
         <li class=\"{seed}\"><strong>A claimed identity.</strong> 24 words you keep. The same words \
         reproduce the same identity on any device, so your history follows you.</li>\
         <li class=\"later\"><strong>Linked accounts.</strong> Proving that your Discord, Telegram \
         and web selves are one human <em>without</em> revealing which accounts. The machinery for \
         this exists in the tree and is not wired to this page yet.</li>\
         </ol>"
    )
}

/// `GET /identity` — the front page of identity.
fn identity_page(claimed: Option<&str>, acting: Option<&str>, notice: Option<&str>) -> String {
    let notice = crate::notice_html(notice);
    let body = match claimed {
        Some(pubkey_hex) => claimed_body(pubkey_hex, acting),
        None => unclaimed_body(acting),
    };
    document_with_head(
        "Your identity — DreggNet",
        "",
        IDENTITY_STYLE,
        &format!(
            "<main class=\"session\">\
             <header class=\"page-head\"><p class=\"eyebrow\">Identity</p>\
             <h1>Who you are here</h1>\
             <p class=\"deck\">Playing needs no account. Keeping what you played does.</p>\
             </header>{notice}{body}</main>"
        ),
    )
}

/// The body for a browser with no claimed identity — the offer, never a wall.
fn unclaimed_body(acting: Option<&str>) -> String {
    let now = match acting {
        Some(label) if label.starts_with("visitor-") => format!(
            "<p class=\"prose\">Right now you are an anonymous visitor, \
             <span class=\"id-key\">{}</span>. That is a perfectly good way to play and you do not \
             have to change it. It lasts exactly as long as this browser keeps its cookie: clear \
             your cookies, use another device, or open a private window, and you arrive as somebody \
             new with an empty history and no way back to this one.</p>",
            esc(label)
        ),
        Some(label) => format!(
            "<p class=\"prose\">Right now this browser is acting as \
             <span class=\"id-key\">{}</span> — a label, not a key. It lasts as long as the cookie \
             does, and there is no way to recover it once the cookie is gone.</p>",
            esc(label)
        ),
        None => "<p class=\"prose\">This browser has no identity yet. One gets minted the moment \
             you open a game — a cookie that lasts as long as the cookie lasts, with no way to \
             recover it once it is gone.</p>"
            .to_string(),
    };
    format!(
        "{now}{rungs}\
         <h2>Keep this identity</h2>\
         <p class=\"prose\">We will show you 24 words, once. Written down, they reproduce your \
         identity on any device, forever — that is the whole mechanism. You stay signed in here \
         either way; the words are the copy you keep.</p>\
         {stakes}\
         <form class=\"id-actions\" method=\"post\" action=\"/identity/claim\">\
         <button class=\"btn btn-primary\" type=\"submit\">Show me my 24 words</button>\
         <a class=\"btn btn-ghost\" href=\"/offerings\">No thanks — just let me play</a>\
         </form>\
         <hr class=\"id-sep\">\
         <h2>Already have a phrase?</h2>\
         <p class=\"prose\">Type or paste your 24 words to become that identity on this device. \
         Nothing needs to have happened on this browser first — the words are the identity, so this \
         works on a machine that has never seen us before.</p>\
         {restore}{honest}",
        now = now,
        rungs = rungs_block(false),
        stakes = stakes_block(),
        restore = restore_form(),
        honest = honest_block(),
    )
}

/// The body for a browser holding a claimed identity.
fn claimed_body(pubkey_hex: &str, acting: Option<&str>) -> String {
    let acting_is_claim = acting
        .and_then(parse_claim_label)
        .is_some_and(|acting_key| acting_key == pubkey_hex);
    // A seat at a locked automatafl/tug table deliberately takes over the acting slot. Say so, and
    // offer the way back, rather than letting the player think their claim evaporated.
    let acting_note = if acting_is_claim {
        String::new()
    } else {
        format!(
            "<div class=\"notice\" role=\"status\">This browser is currently <em>acting as</em> \
             something else — <span class=\"id-key\">{}</span>. That is normal while you hold a \
             seat at a locked two-player table: the seat is the identity there. Your claimed \
             identity is untouched.</div>\
             <form class=\"id-actions\" method=\"post\" action=\"/identity/confirm\">\
             <input type=\"hidden\" name=\"token\" value=\"{token}\">\
             <input type=\"hidden\" name=\"saved\" value=\"yes\">\
             <button class=\"btn\" type=\"submit\">Act as my identity again</button></form>",
            esc(acting.unwrap_or("nothing")),
            token = esc(&claim_label(pubkey_hex)),
        )
    };
    format!(
        "<p class=\"prose\">You are <strong>{tag}</strong> — a real, recoverable identity. Your \
         full public name is</p><p class=\"id-key\">{full}</p>\
         <p class=\"prose\">Your 24 words reproduce this on any device. We cannot show them again: \
         they were never stored.</p>{acting_note}{rungs}\
         <h2>Where this identity works</h2>\
         <p class=\"prose\">All three shipped games file your play under this public name: \
         <a href=\"/descent/play\">The Descent</a> (it is the actor on your run records and the name \
         on the native board), <a href=\"/automatafl\">Automatafl</a> and <a href=\"/tug\">the \
         Tug</a> (it is the actor on every turn you land through the shared host, and it is who a \
         table sees when you are not sitting in a locked seat).</p>\
         <p class=\"prose\">Discord and Telegram already give a player a real platform identity, \
         and those surfaces derive their own key from the bot secret — a <em>custodial</em> key, \
         held by the server rather than by you. This phrase is a different, self-held identity; \
         proving that both are the same human is the third rung above, and it is not wired yet.</p>\
         <h2>Signing as this identity</h2>\
         <p class=\"prose\">A tool that holds your phrase derives the same key and can sign turns \
         that verify as <em>you</em> rather than merely being attributed to you. That is the \
         <code>/act-signed</code> path, and it is the only way a turn here carries a real \
         signature. The derivation is the ordinary one — 24 words, BIP39 checksum, BLAKE3 at path \
         <code>dregg/0</code> — the same path the <code>dregg</code> CLI uses, so a phrase claimed \
         here imports there unchanged.</p>\
         <hr class=\"id-sep\">\
         <h2>Restore a different identity</h2>\
         <p class=\"prose\">Entering another phrase makes this browser that identity instead. \
         Nothing about the current one is deleted — the words still name it.</p>\
         {restore}\
         <hr class=\"id-sep\">\
         <h2>Release this browser</h2>\
         <p class=\"prose\">Clears this browser's claim and hands you back an anonymous visitor. \
         Your identity survives; only this device forgets it. Do not do this without your words.</p>\
         <form method=\"post\" action=\"/identity/release\">\
         <label class=\"id-check\"><input type=\"checkbox\" name=\"understood\" value=\"yes\">\
         <span>I still have my 24 words written down somewhere I can find them.</span></label>\
         <div class=\"id-actions\">\
         <button class=\"btn btn-ghost\" type=\"submit\">Release this browser</button></div></form>\
         {honest}",
        tag = esc(&short_tag(pubkey_hex)),
        full = esc(pubkey_hex),
        acting_note = acting_note,
        rungs = rungs_block(true),
        restore = restore_form(),
        honest = honest_block(),
    )
}

/// The stakes, stated at the size they actually are. ⚑ This is a GAME identity: the loss is a
/// record, not a balance. Borrowing wallet-grade fear here would be a lie, and would also teach
/// the player the wrong thing about the one real risk (that we cannot help them).
fn stakes_block() -> String {
    "<div class=\"id-stakes\"><h3>What losing the words actually costs you</h3>\
     <ul><li>Your game history — the runs, turns and receipts filed under this identity.</li>\
     <li>Your name on the Descent board, and the actor recorded on your past run cards.</li>\
     <li>Anything a future feature files under who you are.</li></ul>\
     <p>That is the whole list. <strong>No money is attached to this phrase.</strong> There is no \
     balance, no token and no wallet behind it — it is the name your play is filed under. It is \
     worth writing on paper; it is not worth a safe deposit box.</p>\
     <p>The part that matters: <strong>we cannot recover it for you.</strong> Not because of a \
     policy, but because we never have it — the identity is derived from the words, so nobody \
     without them can reproduce it, us included.</p></div>"
        .to_string()
}

fn restore_form() -> String {
    "<form class=\"id-restore\" method=\"post\" action=\"/identity/restore\">\
     <label for=\"phrase\" class=\"eyebrow\">Your 24 words</label>\
     <textarea id=\"phrase\" name=\"phrase\" rows=\"3\" autocomplete=\"off\" spellcheck=\"false\" \
     autocapitalize=\"none\" placeholder=\"abandon ability able about …\"></textarea>\
     <div class=\"id-actions\">\
     <button class=\"btn\" type=\"submit\">Restore this identity</button>\
     <span class=\"prose\" style=\"opacity:.7;font-size:.85rem\">Case and spacing do not matter. A \
     mistyped word is caught by the phrase's own checksum.</span></div></form>"
        .to_string()
}

/// The one-time phrase page. Shown once, cached nowhere, and the identity is not taken up until
/// the player says the words are written down.
fn phrase_page(phrase: &str, pubkey_hex: &str, token: &str) -> String {
    let grid = phrase
        .split_whitespace()
        .enumerate()
        .map(|(index, word)| {
            format!(
                "<span class=\"id-word\"><i>{n}</i>{word}</span>",
                n = index + 1,
                word = esc(word)
            )
        })
        .collect::<String>();
    document_with_head(
        "Write these down — DreggNet",
        "",
        IDENTITY_STYLE,
        &format!(
            "<main class=\"session\">\
             <header class=\"page-head\"><p class=\"eyebrow\">Identity · shown once</p>\
             <h1>Write these 24 words down</h1>\
             <p class=\"deck\">On paper, in order. This page is the only time they exist anywhere \
             outside your own notes.</p></header>\
             <div class=\"id-grid\">{grid}</div>\
             <p class=\"eyebrow\">The same words on one line, if that is easier to copy</p>\
             <p class=\"id-plain\">{plain}</p>\
             <p class=\"prose\">These words name the identity \
             <strong>{tag}</strong> (<span class=\"id-key\">{full}</span>). Typing them into any \
             device reproduces it exactly.</p>\
             {stakes}\
             <form method=\"post\" action=\"/identity/confirm\">\
             <input type=\"hidden\" name=\"token\" value=\"{token}\">\
             <label class=\"id-check\"><input type=\"checkbox\" name=\"saved\" value=\"yes\">\
             <span>I have written these 24 words down somewhere I will still have them next \
             month.</span></label>\
             <div class=\"id-actions\">\
             <button class=\"btn btn-primary\" type=\"submit\">This is me now</button>\
             <a class=\"btn btn-ghost\" href=\"/identity\">Cancel — stay anonymous</a></div>\
             </form>\
             <p class=\"prose\" style=\"opacity:.75;font-size:.9rem\">Until you press that button \
             nothing has changed: you are still whoever you were, and this phrase is inert. \
             Cancelling throws it away — the server does not keep a copy to offer you later.</p>\
             {honest}</main>",
            grid = grid,
            plain = esc(phrase),
            tag = esc(&short_tag(pubkey_hex)),
            full = esc(pubkey_hex),
            stakes = stakes_block(),
            token = esc(token),
            honest = honest_block(),
        ),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A phrase round-trips: generate → derive → the same 24 words derive the same public key, and
    /// the public key is what the identity IS.
    #[test]
    fn a_generated_phrase_reproduces_its_identity() {
        let phrase = generate_mnemonic();
        assert_eq!(phrase.split_whitespace().count(), PHRASE_WORDS);
        let first = derive_pubkey_hex(&phrase).expect("a generated phrase validates");
        let again = derive_pubkey_hex(&phrase).expect("derivation is deterministic");
        assert_eq!(first, again);
        assert_eq!(
            first.len(),
            64,
            "the identity is a 32-byte public key in hex"
        );
        assert_eq!(resolve_identity(&claim_label(&first)), DreggIdentity(first));
    }

    /// Case, newlines, and stray punctuation from a pasted column do not cost a player their
    /// identity — the normalizer folds them and the SAME key comes back.
    #[test]
    fn recovery_survives_how_a_human_actually_types_it() {
        let phrase = generate_mnemonic();
        let expected = derive_pubkey_hex(&phrase).expect("valid");
        let words: Vec<&str> = phrase.split_whitespace().collect();
        let messy = format!(
            "  {}\n  {} ,\n{}\n",
            words[0].to_uppercase(),
            words[1],
            words[2..].join("\n")
        );
        let normalized = normalize_phrase(&messy);
        assert_eq!(normalized, phrase);
        assert_eq!(derive_pubkey_hex(&normalized).expect("valid"), expected);
    }

    /// ⚑ THE FORGERY TOOTH. A public key is public, so a label naming one MUST be unforgeable —
    /// otherwise reading somebody's identity off the leaderboard would be enough to become them.
    #[test]
    fn a_label_for_a_public_key_cannot_be_forged() {
        let victim = derive_pubkey_hex(&generate_mnemonic()).expect("valid");
        let genuine = claim_label(&victim);
        assert_eq!(
            parse_claim_label(&genuine).as_deref(),
            Some(victim.as_str())
        );

        // Every shape an attacker can write down by hand, knowing only the public key.
        for forged in [
            format!("{CLAIM_LABEL_PREFIX}{victim}"),
            format!("{CLAIM_LABEL_PREFIX}{victim}."),
            format!("{CLAIM_LABEL_PREFIX}{victim}.00000000000000000000000000000000"),
            format!("{CLAIM_LABEL_PREFIX}{victim}.deadbeef"),
            victim.clone(),
            format!("{genuine}x"),
            genuine.replace("dregg-id-", "dregg-id"),
        ] {
            assert_eq!(
                parse_claim_label(&forged),
                None,
                "a hand-written label verified: {forged}"
            );
        }
        // A flipped mac nibble refuses too.
        let mut tampered: Vec<char> = genuine.chars().collect();
        let last = tampered.len() - 1;
        tampered[last] = if tampered[last] == 'a' { 'b' } else { 'a' };
        assert_eq!(
            parse_claim_label(&tampered.into_iter().collect::<String>()),
            None
        );
    }

    /// The historical derivation is UNTOUCHED for every label that is not a claim: a visitor
    /// token, a seat label, and the council electorate all still hash exactly as before.
    #[test]
    fn non_claim_labels_keep_the_historical_blake3_derivation() {
        for label in [
            "visitor-0123456789abcdef0123456789abcdef",
            "af1a-0123456789abcdef0123456789abcdef",
            "alice",
            "anonymous-visitor-shared-world",
            // A 64-hex string that is NOT a claim label (no prefix, no mac) must not be mistaken
            // for one just because it is the right shape for a public key.
            "aa".repeat(32).as_str(),
        ] {
            assert_eq!(resolve_identity(label), crate::web_identity(label));
        }
    }

    /// A mistyped word is REFUSED, not silently turned into a different (empty) identity — the
    /// checksum is the whole reason a phrase is 24 words and not 22.
    #[test]
    fn a_mistyped_phrase_is_refused_rather_than_renaming_the_player() {
        let phrase = generate_mnemonic();
        let mut words: Vec<String> = phrase.split_whitespace().map(str::to_string).collect();
        words[5] = if words[5] == "abandon" {
            "ability".to_string()
        } else {
            "abandon".to_string()
        };
        let swapped = words.join(" ");
        assert!(
            matches!(
                derive_pubkey_hex(&swapped),
                Err(MnemonicError::InvalidChecksum)
            ),
            "one wrong word must fail the checksum"
        );
        assert!(matches!(
            derive_pubkey_hex("not a real phrase at all"),
            Err(MnemonicError::InvalidWordCount(6))
        ));
        let mut bogus: Vec<String> = phrase.split_whitespace().map(str::to_string).collect();
        bogus[0] = "xyzzyplugh".to_string();
        assert!(matches!(
            derive_pubkey_hex(&bogus.join(" ")),
            Err(MnemonicError::UnknownWord(_))
        ));
    }

    /// Two different phrases are two different people (no collapse onto one identity).
    #[test]
    fn different_phrases_are_different_identities() {
        let a = derive_pubkey_hex(&generate_mnemonic()).expect("valid");
        let b = derive_pubkey_hex(&generate_mnemonic()).expect("valid");
        assert_ne!(a, b);
        assert_ne!(claim_label(&a), claim_label(&b));
    }
}
