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
//! ## ⚑ WHO IS ALLOWED TO CHANGE THIS BROWSER'S IDENTITY
//!
//! The cookie story above reasons about a stolen credential. There is a second, cheaper attack in
//! the opposite direction and it was open until now: **implantation**. A hostile page auto-submits
//! an ordinary `application/x-www-form-urlencoded` form to `POST /identity/restore` carrying **the
//! attacker's own 24 words**. No JS privilege is needed and no preflight happens; the `303`'s
//! `Set-Cookie` is honoured, because `SameSite=Lax` governs when a cookie is later *sent*, not
//! whether the origin server may set one on its own response to a top-level navigation. The victim
//! is silently switched onto an identity **the attacker holds the phrase to**, and every run,
//! receipt and relic afterwards files under it. `POST /identity/confirm` was the same attack with an
//! attacker-minted token.
//!
//! Two gates close it, both fail-CLOSED:
//!
//! 1. **[`request_origin`] runs first on every state-changing identity route** (`/identity/claim`,
//!    `/confirm`, `/restore`, `/release`, and [`crate::identity_link`]'s `POST /identity/link`).
//!    `Sec-Fetch-Site: same-origin` admits; anything else refuses; and with no fetch metadata at all
//!    an `Origin`/`Referer` must match the host the request was addressed to. A request that says
//!    NOTHING about where it came from is refused — an absent check refuses here, as everywhere.
//! 2. **A shown phrase can only be taken up by the browser it was shown to.** `POST /identity/claim`
//!    sets a [`PENDING_COOKIE`] nonce and the confirm token is mac'd OVER that nonce, so a token
//!    lifted off somebody else's screen — or a label read out of a `?user=` URL — cannot be POSTed
//!    to `/identity/confirm` by a different browser. The one other legitimate confirm ("act as my
//!    identity again") is authorised by the claim cookie the browser already holds.
//!
//! ⚑ **Residual, named rather than implied: only the identity routes are gated.** The rest of this
//! crate's state-changing POSTs (`/offerings/…/act`, `/automatafl/table`, `/tug/table`,
//! `/descent/submit`) still accept a cross-origin form. Their stakes are lower — they act as
//! whoever the cookie already is rather than *replacing* who that is — but the class is the same and
//! the gate is one call ([`same_origin_post`]) away. It is not applied here because this pass was
//! scoped to identity; do not read the identity routes' gate as a crate-wide one.
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
//! * ~~`wasm/src/lib.rs::derive_keypair_from_mnemonic` claims to match `dregg-sdk` and does
//!   not.~~ **CLOSED 2026-07-26.** It fed `blake3::hash(mnemonic_bytes)` to the KDF instead of
//!   the BIP39-validated entropy and skipped the checksum, so the same words gave a DIFFERENT
//!   key in the browser extension — and the extension is the only surface that reaches
//!   `Attribution::Signed`, so a person's signed play was filed under a different identity than
//!   their asserted play. Both wasm entry points (`derive_keypair_from_mnemonic` and
//!   `privacy.rs::derive_stealth_keys`, which carried a second copy) now route through
//!   `dregg_sdk::mnemonic` via the one `wasm/src/lib.rs::derive_identity_keypair`. Pinned by
//!   `wasm/tests/mnemonic_derivation_matches_the_sdk.rs` (source) and
//!   `extension/tests/passkey-sign/run.mjs` (the shipped bundle). ⚑ The COMPILED
//!   `extension/dregg_wasm{.js,_bg.wasm}` are committed build artifacts and still carry the old
//!   derivation until `./extension/build.sh wasm` regenerates them.

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

/// **The cookie that binds a shown phrase to the browser it was shown to.** Holds 128 bits of
/// nonce, nothing else — it names no identity and grants nothing on its own. See
/// [`pending_token`].
pub const PENDING_COOKIE: &str = "dregg_claim_pending";

/// The prefix a confirm token wears. Deliberately NOT [`CLAIM_LABEL_PREFIX`]: a confirm token must
/// not double as a usable cookie label, and a cookie label must not be replayable as a confirm
/// token. [`parse_claim_label`] and [`parse_pending_token`] therefore cannot admit each other's
/// strings even before the macs are compared.
const PENDING_TOKEN_PREFIX: &str = "dregg-pending-";

/// The domain the confirm token's mac is bound under — a third, separate domain, so no mac from one
/// of these three purposes verifies as another.
const PENDING_DOMAIN: &[u8] = b"dregg-web-claim-confirm-v1:";

/// How long a shown phrase stays confirmable. Generous (a person writing 24 words on paper is not
/// in a hurry) but bounded, so a phrase page left open on a shared machine stops being live.
const PENDING_MAX_AGE_SECS: u64 = 30 * 60;

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
    if !is_pubkey_hex(pubkey_hex) {
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

/// A 32-byte public key in lowercase hex — the ONLY shape either token parser accepts for the key
/// half, so neither can be pointed at a longer or upper-cased string that macs differently.
fn is_pubkey_hex(candidate: &str) -> bool {
    candidate.len() == 64
        && candidate
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
}

/// **The confirm token for a phrase we just showed, BOUND TO ONE BROWSER** — `dregg-pending-<pubkey
/// hex>.<mac over (nonce, pubkey)>`.
///
/// ⚑ The nonce is why this exists. The token used to BE the cookie label ([`claim_label`]), which
/// made it unforgeable but not *bound*: any browser that came to hold a mac-valid label — off a
/// shoulder-surfed phrase page, out of a `?user=dregg-id-…` URL, out of a shared screenshot — could
/// POST it to `/identity/confirm` and be handed that identity as a cookie. Macing over a nonce that
/// only ever left the server in one [`PENDING_COOKIE`] means the token answers "this is the browser
/// the phrase was shown to", which is the claim a confirm is allowed to make.
fn pending_token(pubkey_hex: &str, nonce: &str) -> String {
    let mut mac = blake3::Hasher::new_keyed(identity_key());
    mac.update(PENDING_DOMAIN);
    // Length-prefixed, the crate's own framing convention (see `game_form_token`): without it a
    // (nonce, key) pair could be re-cut into a different pair with the same concatenation.
    for field in [nonce.as_bytes(), pubkey_hex.as_bytes()] {
        mac.update(&(field.len() as u64).to_be_bytes());
        mac.update(field);
    }
    format!(
        "{PENDING_TOKEN_PREFIX}{pubkey_hex}.{}",
        hex_bytes(&mac.finalize().as_bytes()[..16])
    )
}

/// **Verify a confirm token against the nonce THIS browser presents**, recovering the public key it
/// names. `None` for a foreign prefix, a wrong-shaped key, a forged mac, or — the case that matters
/// — a genuine token presented with somebody else's (or no) nonce.
fn parse_pending_token(token: &str, nonce: &str) -> Option<String> {
    let rest = token.strip_prefix(PENDING_TOKEN_PREFIX)?;
    let (pubkey_hex, _mac_hex) = rest.split_once('.')?;
    if !is_pubkey_hex(pubkey_hex) {
        return None;
    }
    let expected = pending_token(pubkey_hex, nonce);
    // Constant-time over the whole token, for the same reason `parse_claim_label` is: a mac oracle
    // would let a caller grind a token for a key they were never shown a phrase for.
    if !constant_time_eq(expected.as_bytes(), token.as_bytes()) {
        return None;
    }
    Some(pubkey_hex.to_string())
}

/// A fresh 128-bit pending nonce, hex.
fn mint_pending_nonce() -> String {
    let mut bytes = [0u8; 16];
    getrandom::fill(&mut bytes).expect("operating-system RNG must mint a claim-confirm nonce");
    hex_bytes(&bytes)
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

/// **Derive the SIGNING key a phrase names** — the same [`DERIVATION_PATH`] derivation as
/// [`derive_pubkey_hex`], but keeping the 32-byte Ed25519 seed so the caller can produce ONE
/// signature with it.
///
/// ⚑ The only caller is [`crate::identity_link`], which needs a signature over a link claim while
/// the phrase is transiently in hand. It lives HERE, beside [`DERIVATION_PATH`], so there is exactly
/// one place in the crate that turns words into a key — a second derivation site is how the same
/// phrase silently becomes two identities (`wasm/src/lib.rs` WAS the standing example of that; it
/// now delegates to `dregg_sdk::mnemonic` from a single `derive_identity_keypair`, see this
/// module's residuals).
///
/// The returned secret is [`Zeroizing`], so it is wiped when the caller's binding drops even on an
/// early return; the 64-byte KDF seed is wiped here.
pub(crate) fn derive_root_keypair(
    phrase: &str,
) -> Result<(String, zeroize::Zeroizing<[u8; 32]>), MnemonicError> {
    let mut seed = mnemonic_to_seed(phrase, "")?;
    let (public, secret) = derive_keypair(&seed, DERIVATION_PATH);
    seed.zeroize();
    Ok((hex_bytes(&public), zeroize::Zeroizing::new(secret)))
}

/// Fold however a human typed their 24 words into the canonical phrase — see
/// [`normalize_phrase`]. Shared with [`crate::identity_link`] so the restore box and the link box
/// cannot disagree about what counts as the same phrase.
pub(crate) fn normalize_typed_phrase(raw: &str) -> String {
    normalize_phrase(raw)
}

/// Read one cookie by name — shared with [`crate::identity_link`]. See [`cookie`].
pub(crate) fn read_cookie(headers: &HeaderMap, name: &str) -> Option<String> {
    cookie(headers, name)
}

/// The full honest-limits block, so the link page's own honesty section can sit BESIDE the identity
/// page's rather than paraphrasing it. See [`honest_block`].
pub(crate) fn honest_limits_html() -> String {
    honest_block()
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
// ⚑ ORIGIN — did this POST come from OUR OWN PAGE?
// ─────────────────────────────────────────────────────────────────────────────

/// What a request's own headers say about where it was initiated.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RequestOrigin {
    /// A page on this very origin initiated it — the ONLY verdict that may change an identity.
    SameOrigin,
    /// A header positively said somewhere else. The string is for the operator's log line only; it
    /// is attacker-chosen text and never reaches a page.
    Foreign(String),
    /// **Nothing said where this came from**: no `Sec-Fetch-Site`, no `Origin`, no usable `Referer`,
    /// or no host to compare one against. Refused exactly like a foreign one — an absent check
    /// refuses. In a real deployment this means a reverse proxy is dropping headers, and
    /// [`refuse_foreign_origin`] logs that as its own case so an operator can tell the two apart.
    Unstated,
}

/// **Where a request came from, decided from its own headers.** The gate every state-changing
/// identity route runs before it derives, sets, or clears anything.
///
/// ⚑ **Why this shape.** Two mechanisms were on the table. A per-session CSRF token is stronger, but
/// it needs somewhere to live, and the whole point of this module is that the server keeps NO
/// per-player state — so it would have meant inventing a session store to protect a stateless
/// feature. Origin verification needs no state and no dependency: `Sec-Fetch-Site` is sent by every
/// browser we care about (Chrome 76+, Firefox 90+, Safari 16.4+), and `Origin` is sent on every
/// cross-origin *and* same-origin `POST` by every browser since ~2016. So the cheap mechanism is
/// also sufficient here, and the expensive one would have cost the property the module is built on.
/// (The confirm route additionally carries a real per-browser token — see [`pending_token`] — because
/// there it is free: the phrase page already had to hand something back.)
///
/// The three decisions inside, each of them fail-closed:
///
/// * `Sec-Fetch-Site: same-origin` admits. **`same-site` does not** — that would admit any sibling
///   subdomain, and a subdomain takeover or an XSS on one would then be able to implant an identity
///   here. Our own forms are same-origin; nothing legitimate needs the looser rule.
/// * `none` does not admit either. It means no initiating context (a typed URL, a bookmark), and a
///   typed URL cannot submit our form.
/// * With no fetch metadata at all, the stated initiator must MATCH the host this request was
///   addressed to (`X-Forwarded-Host`, else `Host`). `Origin` is preferred; `Referer` is the
///   fallback for the handful of clients that omit `Origin`. Userinfo in the value
///   (`https://ourhost@evil.example/`) is refused rather than parsed, because the real host there is
///   the attacker's.
pub fn request_origin(headers: &HeaderMap) -> RequestOrigin {
    if let Some(site) = header_str(headers, "sec-fetch-site") {
        return if site.eq_ignore_ascii_case("same-origin") {
            RequestOrigin::SameOrigin
        } else {
            RequestOrigin::Foreign(format!("Sec-Fetch-Site: {}", clip(site)))
        };
    }
    let Some(host) = effective_host(headers) else {
        return RequestOrigin::Unstated;
    };
    for name in ["origin", "referer"] {
        let Some(value) = header_str(headers, name) else {
            continue;
        };
        return match authority_of(value) {
            Some(authority) if authority == host => RequestOrigin::SameOrigin,
            _ => RequestOrigin::Foreign(format!("{name}: {}", clip(value))),
        };
    }
    RequestOrigin::Unstated
}

/// **Whether a state-changing POST may be honoured at all** — `true` only for
/// [`RequestOrigin::SameOrigin`]. The form [`crate::identity_link`] and any future adopter call.
pub fn same_origin_post(headers: &HeaderMap) -> bool {
    matches!(request_origin(headers), RequestOrigin::SameOrigin)
}

/// One header's trimmed, non-empty value.
fn header_str<'a>(headers: &'a HeaderMap, name: &str) -> Option<&'a str> {
    headers
        .get(name)
        .and_then(|value| value.to_str().ok())
        .map(str::trim)
        .filter(|value| !value.is_empty())
}

/// Keep a log line's copy of an attacker-chosen header bounded.
fn clip(value: &str) -> String {
    value.chars().take(80).collect()
}

/// The `host[:port]` this request was ADDRESSED to: `X-Forwarded-Host`'s first entry when a proxy
/// set one (the same proxy trust `is_https` already extends to `X-Forwarded-Proto`), else `Host`.
/// `None` when neither is present — which is what makes a request carrying no host `Unstated`
/// rather than accidentally same-origin.
fn effective_host(headers: &HeaderMap) -> Option<String> {
    let raw = match header_str(headers, "x-forwarded-host") {
        Some(forwarded) => forwarded.split(',').next().unwrap_or_default(),
        None => header_str(headers, "host")?,
    };
    normalize_authority(raw)
}

/// Lowercase, drop a trailing root dot, and drop a default port, so `Example.COM:443` and
/// `example.com` compare equal. Applied to BOTH sides of the comparison, so the normalization
/// cannot make two different hosts match.
fn normalize_authority(raw: &str) -> Option<String> {
    let host = raw.trim().trim_end_matches('.').to_ascii_lowercase();
    if host.is_empty() {
        return None;
    }
    let bare = host
        .strip_suffix(":443")
        .or_else(|| host.strip_suffix(":80"))
        .unwrap_or(host.as_str());
    Some(bare.to_string())
}

/// The `host[:port]` an `Origin` or `Referer` value names. `None` for `null` (a sandboxed frame),
/// for a value with no scheme, and for anything carrying userinfo.
fn authority_of(value: &str) -> Option<String> {
    let (_scheme, rest) = value.split_once("://")?;
    let authority = rest.split(['/', '?', '#']).next().unwrap_or_default();
    if authority.contains('@') {
        return None;
    }
    normalize_authority(authority)
}

/// The one sentence a player reads when a state-changing identity request did not come from a page
/// on this site. It names the ACTION they can take; "your `Sec-Fetch-Site` was cross-site" is true
/// and useless to a person.
const FOREIGN_ORIGIN_NOTICE: &str = "Refused: this did not come from our page, so nothing was changed; no identity was claimed, \
     restored or released. Open /identity here and try again. If you got here by pressing something \
     on another website, that button was trying to switch this browser onto somebody else's \
     identity.";

/// **Refuse a state-changing identity request that did not come from our own page.** `None` when it
/// did, so every handler reads `if let Some(refusal) = refuse_foreign_origin(…) { return refusal; }`
/// as its first line.
///
/// The two refusing verdicts are logged as DIFFERENT lines on purpose. `Foreign` is somebody
/// attacking a player; `Unstated` is almost always an operator's reverse proxy eating headers, and
/// telling an operator "you are under attack" when their proxy is misconfigured would send them
/// looking in the wrong place for a week.
fn refuse_foreign_origin(headers: &HeaderMap, route: &str) -> Option<Response> {
    match request_origin(headers) {
        RequestOrigin::SameOrigin => None,
        RequestOrigin::Foreign(said) => {
            tracing::warn!(
                route,
                said = %said,
                "REFUSED a cross-origin identity request (login-CSRF / identity fixation: a hostile \
                 page auto-submitting its OWN phrase would otherwise re-home this browser onto an \
                 identity the attacker holds the words to). Nothing was derived and no cookie was set."
            );
            Some(foreign_origin_response(headers))
        }
        RequestOrigin::Unstated => {
            tracing::warn!(
                route,
                "REFUSED an identity request that stated no origin at all — no Sec-Fetch-Site, no \
                 Origin, no Referer, or no Host to compare against, so this server cannot tell \
                 whether it came from its own page and fails CLOSED. If players are seeing this, the \
                 reverse proxy in front of this process is dropping Origin/Sec-Fetch-Site or not \
                 passing Host through."
            );
            Some(foreign_origin_response(headers))
        }
    }
}

fn foreign_origin_response(headers: &HeaderMap) -> Response {
    (
        StatusCode::FORBIDDEN,
        no_store(identity_page(
            claimed_pubkey(headers).as_deref(),
            cookie(headers, ACTING_COOKIE).as_deref(),
            Some(FOREIGN_ORIGIN_NOTICE),
        )),
    )
        .into_response()
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
/// This deliberately sets **no identity cookie**. The identity is not yours until you say you have
/// written the words down ([`post_confirm`]), so a player who closes this tab is exactly who they
/// were a moment ago rather than silently re-homed onto an identity whose phrase is gone forever.
///
/// It DOES set one non-identity cookie: the [`PENDING_COOKIE`] nonce that the confirm token is
/// mac'd over, which is what makes the shown phrase confirmable by *this* browser and no other.
/// That cookie names nobody and grants nothing on its own.
async fn post_claim(headers: HeaderMap) -> Response {
    if let Some(refusal) = refuse_foreign_origin(&headers, "/identity/claim") {
        return refusal;
    }
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
                        "Refused: the generated phrase did not validate ({error}); nothing was claimed."
                    )),
                )),
            )
                .into_response();
        }
    };
    // The confirm token is mac'd, so `/identity/confirm` cannot be pointed at a public key this
    // server did not just generate — and it is mac'd OVER A FRESH NONCE that leaves only in this
    // response's cookie, so it cannot be replayed by a browser that was not shown this phrase.
    // Without the first property an unauthenticated `pubkey_hex` field would let anyone mint a valid
    // cookie for anyone else's published key; without the second, a token seen on somebody else's
    // screen would still install.
    let nonce = mint_pending_nonce();
    let token = pending_token(&pubkey_hex, &nonce);
    let mut response = no_store(phrase_page(&phrase, &pubkey_hex, &token));
    let pending = set_cookie(
        PENDING_COOKIE,
        &nonce,
        PENDING_MAX_AGE_SECS,
        is_https(&headers),
    );
    if let Ok(value) = header::HeaderValue::from_str(&pending) {
        response.headers_mut().append(header::SET_COOKIE, value);
    }
    response
}

/// Which of the TWO legitimate confirms this is — and the proof that this browser may make it.
///
/// ⚑ Before this existed, `/identity/confirm` accepted ANY mac-valid label from ANY browser. Only
/// this server can mint one, so it was unforgeable; but it was not *bound*, and a label does escape
/// (the module doc says plainly that a URL carrying `?user=dregg-id-…` hands over the same access a
/// copied cookie would). Presenting such a label to `/identity/confirm` turned that transient leak
/// into an installed, year-long cookie. Both arms below are bound to the browser asking.
enum ConfirmAuthority {
    /// A phrase THIS browser was just shown — proven by the [`PENDING_COOKIE`] nonce the token is
    /// mac'd over.
    JustShown,
    /// An identity this browser ALREADY holds a mac-valid claim cookie for. This is `/identity`'s
    /// "act as my identity again" button, which puts the claim back in the acting slot after a
    /// locked table seat took it over. Nothing new is granted: the browser is asking for the
    /// identity it already provably holds.
    AlreadyHeld,
}

/// Authorise a confirm, recovering the public key it is for. `None` refuses.
fn authorize_confirm(headers: &HeaderMap, token: &str) -> Option<(String, ConfirmAuthority)> {
    if let Some(nonce) = cookie(headers, PENDING_COOKIE) {
        if let Some(pubkey_hex) = parse_pending_token(token, &nonce) {
            return Some((pubkey_hex, ConfirmAuthority::JustShown));
        }
    }
    let held = claimed_pubkey(headers)?;
    let presented = parse_claim_label(token)?;
    (presented == held).then_some((held, ConfirmAuthority::AlreadyHeld))
}

/// The confirm form — the mac'd token, plus the checkbox the player must actually tick.
#[derive(Debug, Clone, Deserialize)]
pub struct ConfirmForm {
    /// Either the [`pending_token`] [`post_claim`] minted for THIS browser, or — on `/identity`'s
    /// "act as my identity again" button — the [`claim_label`] of the identity this browser already
    /// holds a claim cookie for. [`authorize_confirm`] is what decides which, and both are bound to
    /// the browser asking; a bare mac-valid label from a stranger is neither.
    pub token: String,
    /// Present only when the "I have written these down" box is checked.
    #[serde(default)]
    pub saved: Option<String>,
}

/// `POST /identity/confirm` — take up the identity whose phrase was just shown.
async fn post_confirm(headers: HeaderMap, Form(form): Form<ConfirmForm>) -> Response {
    if let Some(refusal) = refuse_foreign_origin(&headers, "/identity/confirm") {
        return refusal;
    }
    let Some((pubkey_hex, authority)) = authorize_confirm(&headers, &form.token) else {
        return (
            StatusCode::FORBIDDEN,
            no_store(identity_page(
                claimed_pubkey(&headers).as_deref(),
                cookie(&headers, ACTING_COOKIE).as_deref(),
                Some(
                    "Refused: this browser cannot make that confirmation, so nothing was claimed. \
                     A phrase can only be taken up by the browser it was shown to, and this one is \
                     not carrying that page's cookie. If the server restarted, or the phrase page \
                     was opened somewhere else, generate a new phrase rather than reusing the one on \
                     the old page.",
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
                     claimed. That phrase is gone: the server does not keep it. Generate a new one.",
                ),
            )),
        )
            .into_response();
    }
    let label = claim_label(&pubkey_hex);
    let secure = is_https(&headers);
    let mut cookies = vec![
        set_cookie(CLAIM_COOKIE, &label, CLAIM_MAX_AGE_SECS, secure),
        set_cookie(ACTING_COOKIE, &label, CLAIM_MAX_AGE_SECS, secure),
    ];
    if matches!(authority, ConfirmAuthority::JustShown) {
        // One shown phrase, one confirm: spend the nonce, so a back-button re-POST of the same
        // token cannot re-install it later on a machine somebody else has since sat down at.
        cookies.push(set_cookie(PENDING_COOKIE, "", 0, secure));
    }
    redirect_with_cookies(cookies)
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
    // ⚑ FIRST, before the phrase is even normalized: a cross-origin POST here is the identity
    // fixation attack in its purest form — the attacker's own 24 words, submitted by the victim's
    // browser, with the `303`'s `Set-Cookie` honoured. Nothing below runs for a request that cannot
    // show it came from our page.
    if let Some(refusal) = refuse_foreign_origin(&headers, "/identity/restore") {
        return refusal;
    }
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
                    "that is {words} word{}; a dregg phrase is exactly {PHRASE_WORDS}.",
                    if words == 1 { "" } else { "s" }
                ),
                MnemonicError::UnknownWord(word) => format!(
                    "{:?} is not one of the 2048 words in the list; check that word's spelling.",
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
    // A cross-origin logout is a smaller wound than a cross-origin login, not a different class: a
    // hostile page that can sign a player out mid-run costs them the acting slot they were playing
    // under. Same gate, same refusal.
    if let Some(refusal) = refuse_foreign_origin(&headers, "/identity/release") {
        return refusal;
    }
    if form.understood.is_none() {
        return (
            StatusCode::BAD_REQUEST,
            no_store(identity_page(
                claimed_pubkey(&headers).as_deref(),
                cookie(&headers, ACTING_COOKIE).as_deref(),
                Some(
                    "Refused: releasing this browser needs the confirmation box ticked; without \
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
/* ⚑ THE POSITION INDEX IS NOT DECORATION. It is the ORDER of a 24-word phrase on the page where
   getting the order wrong loses the identity for good, and at `opacity:.45` it measured 4.06:1 —
   the DIMMEST thing on the highest-stakes surface in the product. `.7` measures 8.24:1 on the page
   floor (6.71:1 under the top wash) and still reads as subordinate to the word beside it. */
.id-word i{font-style:normal;opacity:.7;font-size:.8rem;min-width:1.4rem;text-align:right}
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
///
/// ⚑ **This block used to reason ONLY about theft** — somebody taking your cookie. That is the wrong
/// half of the threat model to reason carefully about on its own, because the other half is cheaper
/// for the attacker: they need steal nothing, they can **give** you an identity of their choosing (a
/// hostile page auto-submitting its own 24 words to `/identity/restore`, whose `Set-Cookie` the
/// browser honours). A page that is careful about the wrong threat is worse than one that says
/// nothing, so implantation is now named here beside theft, together with the two gates that refuse
/// it — see this module's "WHO IS ALLOWED TO CHANGE THIS BROWSER'S IDENTITY".
fn honest_block() -> String {
    "<div class=\"id-honest\"><h3>What this does and does not protect</h3><dl>\
     <dt>Where the key lives: nowhere.</dt>\
     <dd>Your 24 words are turned into a keypair inside the one request that needs it, and every \
     byte of secret material is wiped before the response goes out. Nothing is stored: not on the \
     server, and not in this browser.</dd>\
     <dt>The words pass through the server once, each time you use them.</dt>\
     <dd>They are generated here, and typed back here whenever a request needs the key they derive: \
     restoring this identity on a device, or signing a cross-platform link. We never write them to \
     disk or to a log, but that is a promise about this code, not a guarantee the shape of the \
     system gives you. Generating them entirely inside your browser is the next step and is not what \
     these pages do today.</dd>\
     <dt>Your browser holds a cookie, not a key.</dt>\
     <dd>It is <code>HttpOnly</code>, so page scripts, including an injected one, cannot read it. \
     That is why the identity lives in a cookie rather than in <code>localStorage</code>, which any \
     script on the page can read. It is still a bearer token: whoever has it can play as you until \
     it expires, so treat a link containing <code>?user=dregg-id-…</code> the way you would treat a \
     password.</dd>\
     <dt>And nobody else can put an identity INTO this browser.</dt>\
     <dd>Theft is not the only direction. A hostile page can also try to <em>give</em> you an \
     identity, quietly submitting <em>its own</em> 24 words to this site so that everything you play \
     afterwards is filed under a name somebody else holds the words to, with nothing on screen \
     looking wrong. Claiming, confirming, restoring, releasing and linking therefore only work from a \
     page on this site: a request that cannot show it came from here is refused before anything is \
     derived or set, including when it says nothing at all about where it came from. And a phrase we \
     have just shown can only be taken up by the browser it was shown to, so a token glimpsed on \
     somebody else's screen is not a way in.</dd>\
     <dt>Pressing a button here is not a signature.</dt>\
     <dd>Turns you play in the browser are attributed to your public key, not signed by it; the \
     server has no key to sign with and neither does this page. A tool that holds your phrase (the \
     <code>dregg</code> CLI, the browser extension) can sign turns as this identity through \
     <code>/act-signed</code>, and only those turns carry a real signature.</dd>\
     <dt>A server restart may sign you out.</dt>\
     <dd>Unless the deployment pins its identity key, restarting re-rolls it and your cookie stops \
     verifying. You come back as a fresh anonymous visitor and re-enter your words, never as \
     somebody else.</dd>\
     </dl></div>"
        .to_string()
}

/// The three-rung progression, with the current rung marked. Same list on both pages.
///
/// ⚑ Rung 3 used to say linking "is not wired to this page yet". It IS now
/// ([`crate::identity_link`], `/identity/link`) — but only the PLAIN version: the link is a
/// plaintext record the operator can read. The rung therefore names both what exists and what the
/// private version would add, rather than swapping one over-claim for another.
fn rungs_block(claimed: bool) -> String {
    let anon = if claimed { "later" } else { "now" };
    let seed = if claimed { "now" } else { "later" };
    format!(
        "<ol class=\"id-rungs\">\
         <li class=\"{anon}\"><strong>Anonymous visitor.</strong> A cookie, minted the first time \
         you load a page. Nothing to remember, nothing to lose (except that clearing your cookies \
         ends that person permanently).</li>\
         <li class=\"{seed}\"><strong>A claimed identity.</strong> 24 words you keep. The same words \
         reproduce the same identity on any device, so your history follows you.</li>\
         <li class=\"later\"><strong>Linked accounts.</strong> Proving that your Discord or Telegram \
         self and this one are the same human, so the boards rank you once. \
         <a href=\"/identity/link\">This works today</a>, in the plain version: the link is stored \
         as \"this key and that account are one person\", which the operator can read. Proving it \
         <em>without</em> revealing which accounts is the machinery that exists in the tree and is \
         not what that page does.</li>\
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
        "Your identity · DreggNet",
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
             <span class=\"id-key\">{}</span> (a label, not a key). It lasts as long as the cookie \
             does, and there is no way to recover it once the cookie is gone.</p>",
            esc(label)
        ),
        None => "<p class=\"prose\">This browser has no identity yet. One gets minted the moment \
             you open a game: a cookie that lasts as long as the cookie lasts, with no way to \
             recover it once it is gone.</p>"
            .to_string(),
    };
    format!(
        "{now}{rungs}\
         <h2>Keep this identity</h2>\
         <p class=\"prose\">We will show you 24 words, once. Written down, they reproduce your \
         identity on any device, forever; that is the whole mechanism. You stay signed in here \
         either way; the words are the copy you keep.</p>\
         {stakes}\
         <form class=\"id-actions\" method=\"post\" action=\"/identity/claim\">\
         <button class=\"btn btn-primary\" type=\"submit\">Show me my 24 words</button>\
         <a class=\"btn btn-ghost\" href=\"/offerings\">No thanks · just let me play</a>\
         </form>\
         <hr class=\"id-sep\">\
         <h2>Already have a phrase?</h2>\
         <p class=\"prose\">Type or paste your 24 words to become that identity on this device. \
         Nothing needs to have happened on this browser first: the words are the identity, so this \
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
             something else: <span class=\"id-key\">{}</span>. That is normal while you hold a \
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
        "<p class=\"prose\">You are <strong>{tag}</strong>: a real, recoverable identity. Your \
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
         and those surfaces derive their own key from the bot secret: a <em>custodial</em> key, \
         held by the operator rather than by you. This phrase is a different, self-held identity, \
         and until you say otherwise the two are <strong>different players with different \
         histories on the same board</strong>. \
         <a href=\"/identity/link\">Prove they are one human</a> and the boards rank you once and \
         <a href=\"/you\">/you</a> counts both sides. It does <em>not</em> merge the keys: your \
         platform key stays custodial, and that page says so rather than selling you otherwise.</p>\
         <h2>Signing as this identity</h2>\
         <p class=\"prose\">A tool that holds your phrase derives the same key and can sign turns \
         that verify as <em>you</em> rather than merely being attributed to you. That is the \
         <code>/act-signed</code> path, and it is the only way a turn here carries a real \
         signature. The derivation is the ordinary one (24 words, BIP39 checksum, BLAKE3 at path \
         <code>dregg/0</code>), the same path the <code>dregg</code> CLI uses, so a phrase claimed \
         here imports there unchanged.</p>\
         <hr class=\"id-sep\">\
         <h2>Restore a different identity</h2>\
         <p class=\"prose\">Entering another phrase makes this browser that identity instead. \
         Nothing about the current one is deleted; the words still name it.</p>\
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
     <ul><li>Your game history · every run and every landed turn filed under this identity.</li>\
     <li>Your name on the Descent board, and the actor recorded on your past run cards.</li>\
     <li>Anything a future feature files under who you are.</li></ul>\
     <p>That is the whole list. <strong>No money is attached to this phrase.</strong> There is no \
     balance, no token and no wallet behind it; it is the name your play is filed under. It is \
     worth writing on paper; it is not worth a safe deposit box.</p>\
     <p>The part that matters: <strong>we cannot recover it for you.</strong> Not because of a \
     policy, but because we never have it: the identity is derived from the words, so nobody \
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
        "Write these down · DreggNet",
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
             <a class=\"btn btn-ghost\" href=\"/identity\">Cancel · stay anonymous</a></div>\
             </form>\
             <p class=\"prose\" style=\"opacity:.75;font-size:.9rem\">Until you press that button \
             nothing has changed: you are still whoever you were, and this phrase is inert. \
             Cancelling throws it away: the server does not keep a copy to offer you later.</p>\
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

    fn headers_of(pairs: &[(&str, &str)]) -> HeaderMap {
        let mut headers = HeaderMap::new();
        for (name, value) in pairs {
            headers.insert(
                header::HeaderName::from_bytes(name.as_bytes()).expect("a static header name"),
                header::HeaderValue::from_str(value).expect("a static header value"),
            );
        }
        headers
    }

    /// ⚑ **THE ORIGIN TOOTH, BOTH POLARITIES.** Our own form POST is admitted; every shape a hostile
    /// page can produce is refused — INCLUDING the shape that says nothing at all, which is the one a
    /// fail-open guard would wave through.
    #[test]
    fn only_our_own_page_may_change_an_identity() {
        // Admitted: the fetch metadata every browser we care about sends for our own form.
        for admitted in [
            vec![("sec-fetch-site", "same-origin")],
            vec![("sec-fetch-site", "Same-Origin")],
            // No fetch metadata (an older client), but a matching Origin.
            vec![("host", "play.example"), ("origin", "https://play.example")],
            // …with a port, and with the case and a default port normalized on both sides.
            vec![
                ("host", "Play.Example:443"),
                ("origin", "https://play.example"),
            ],
            vec![
                ("host", "127.0.0.1:8080"),
                ("origin", "http://127.0.0.1:8080"),
            ],
            // A proxy that rewrites Host but forwards the real one.
            vec![
                ("host", "internal-8080"),
                ("x-forwarded-host", "play.example"),
                ("origin", "https://play.example"),
            ],
            // Referer only, matching — the fallback for clients that omit Origin.
            vec![
                ("host", "play.example"),
                ("referer", "https://play.example/identity"),
            ],
        ] {
            assert_eq!(
                request_origin(&headers_of(&admitted)),
                RequestOrigin::SameOrigin,
                "a legitimate same-origin POST was refused: {admitted:?}"
            );
            assert!(same_origin_post(&headers_of(&admitted)));
        }

        // Refused. Every one of these is a shape a hostile page (or a stripped proxy) produces.
        for refused in [
            // The attack: a cross-site form auto-submit.
            vec![("sec-fetch-site", "cross-site")],
            // ⚑ A SIBLING SUBDOMAIN IS NOT US. `same-site` would admit a subdomain takeover.
            vec![("sec-fetch-site", "same-site")],
            // No initiating context at all cannot have submitted our form.
            vec![("sec-fetch-site", "none")],
            // A foreign Origin against our host.
            vec![("host", "play.example"), ("origin", "https://evil.example")],
            // ⚑ USERINFO: the real host here is `evil.example`, not `play.example`.
            vec![
                ("host", "play.example"),
                ("origin", "https://play.example@evil.example"),
            ],
            // A sandboxed frame's opaque origin.
            vec![("host", "play.example"), ("origin", "null")],
            // A subdomain, spelled out — same refusal as the header form.
            vec![
                ("host", "play.example"),
                ("origin", "https://cdn.play.example"),
            ],
            // A suffix that merely ENDS with our host.
            vec![
                ("host", "play.example"),
                ("origin", "https://notplay.example"),
            ],
            // A foreign Referer.
            vec![
                ("host", "play.example"),
                ("referer", "https://evil.example/go"),
            ],
            // ⚑ NOTHING SAID AT ALL — the fail-open case. This is what `tower::oneshot` sends by
            // default, and what a header-stripping proxy sends, and it must refuse.
            vec![],
            vec![("host", "play.example")],
            // A host with no origin to compare, and an origin with no host to compare against.
            vec![("origin", "https://play.example")],
        ] {
            let headers = headers_of(&refused);
            assert_ne!(
                request_origin(&headers),
                RequestOrigin::SameOrigin,
                "a request that could not show it came from our page was ADMITTED: {refused:?}"
            );
            assert!(!same_origin_post(&headers));
        }

        // The two refusing verdicts stay distinguishable, because the operator story differs: one is
        // an attack on a player, the other is a proxy eating headers.
        assert!(matches!(
            request_origin(&headers_of(&[("sec-fetch-site", "cross-site")])),
            RequestOrigin::Foreign(_)
        ));
        assert_eq!(
            request_origin(&headers_of(&[])),
            RequestOrigin::Unstated,
            "a request stating nothing must be reported as stating nothing, not as an attack"
        );
        // The player-facing sentence says what happened and what to do, and never names a header.
        assert!(FOREIGN_ORIGIN_NOTICE.starts_with("Refused:"));
        assert!(FOREIGN_ORIGIN_NOTICE.contains("/identity"));
        for machinery in ["Sec-Fetch", "Origin", "Referer", "CSRF", "header"] {
            assert!(
                !FOREIGN_ORIGIN_NOTICE.contains(machinery),
                "the refusal names machinery at a player: {machinery}"
            );
        }
    }

    /// ⚑ **A CONFIRM TOKEN IS BOUND TO ONE BROWSER.** The genuine token verifies under the nonce it
    /// was minted with and under NOTHING else — which is what stops a token seen on somebody else's
    /// screen, or a claim label lifted out of a `?user=` URL, from being POSTed to
    /// `/identity/confirm` and installing as a year-long cookie.
    #[test]
    fn a_confirm_token_only_verifies_for_the_browser_it_was_shown_to() {
        let key = derive_pubkey_hex(&generate_mnemonic()).expect("valid");
        let mine = mint_pending_nonce();
        let theirs = mint_pending_nonce();
        assert_ne!(mine, theirs, "the nonce is random per claim");
        let token = pending_token(&key, &mine);

        assert_eq!(
            parse_pending_token(&token, &mine).as_deref(),
            Some(&key[..])
        );
        for wrong_nonce in [theirs.as_str(), "", "00000000000000000000000000000000"] {
            assert_eq!(
                parse_pending_token(&token, wrong_nonce),
                None,
                "a genuine token verified under a nonce it was not minted with: {wrong_nonce}"
            );
        }

        // ⚑ THE TWO TOKEN SPACES DO NOT MEET. A cookie label is not a confirm token, and a confirm
        // token is not a cookie label — so neither can be replayed as the other even with the right
        // nonce in hand.
        let label = claim_label(&key);
        assert_eq!(parse_pending_token(&label, &mine), None);
        assert_eq!(parse_claim_label(&token), None);

        // And every hand-written shape refuses.
        for forged in [
            format!("{PENDING_TOKEN_PREFIX}{key}"),
            format!("{PENDING_TOKEN_PREFIX}{key}."),
            format!("{PENDING_TOKEN_PREFIX}{key}.00000000000000000000000000000000"),
            format!("{token}x"),
            key.clone(),
        ] {
            assert_eq!(
                parse_pending_token(&forged, &mine),
                None,
                "a hand-written confirm token verified: {forged}"
            );
        }
    }

    /// The confirm authority has exactly TWO arms, and each is bound to the browser asking: the
    /// pending nonce, or a claim cookie the browser already provably holds. A browser holding
    /// neither cannot confirm anything, whatever token it presents.
    #[test]
    fn a_confirm_needs_the_pending_nonce_or_an_identity_already_held() {
        let key = derive_pubkey_hex(&generate_mnemonic()).expect("valid");
        let nonce = mint_pending_nonce();
        let token = pending_token(&key, &nonce);
        let label = claim_label(&key);

        // Arm 1: the browser that was shown the phrase.
        let shown = headers_of(&[("cookie", &format!("{PENDING_COOKIE}={nonce}"))]);
        assert!(matches!(
            authorize_confirm(&shown, &token),
            Some((ref got, ConfirmAuthority::JustShown)) if *got == key
        ));

        // Arm 2: "act as my identity again" — authorised by the claim cookie, not by a token.
        let holder = headers_of(&[("cookie", &format!("{CLAIM_COOKIE}={label}"))]);
        assert!(matches!(
            authorize_confirm(&holder, &label),
            Some((ref got, ConfirmAuthority::AlreadyHeld)) if *got == key
        ));

        // ⚑ NEITHER: a stranger holding the genuine token, or the genuine label, gets nothing.
        let stranger = HeaderMap::new();
        assert!(authorize_confirm(&stranger, &token).is_none());
        assert!(
            authorize_confirm(&stranger, &label).is_none(),
            "a label lifted out of a URL must not be installable by a browser that does not hold it"
        );
        // …and a browser holding a claim for a DIFFERENT identity cannot confirm this one.
        let other_key = derive_pubkey_hex(&generate_mnemonic()).expect("valid");
        let other = headers_of(&[(
            "cookie",
            &format!("{CLAIM_COOKIE}={}", claim_label(&other_key)),
        )]);
        assert!(authorize_confirm(&other, &label).is_none());
    }
}
