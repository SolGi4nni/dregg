//! # `identity_unlink` — **the un-link door.**
//!
//! `identity_link`'s residual list opened with this, in these words: *"⚑ **NO UN-LINK DOOR.** A
//! rebind supersedes for the same custodial key, but a link made by mistake — or one made on a
//! stranger's code that the player ticked through anyway — leaves a row that nothing here removes.
//! … **This is the first thing to build next.**"* It also leaked into the player's own copy, three
//! times, as "there is no way to undo a link yet" — a sentence the consent box leans on to argue
//! that the player should be careful, which is a poor substitute for being able to fix it.
//!
//! ## What was actually missing, and what was not
//!
//! Not the vocabulary. [`webauth_core::link_kel`] has carried [`LinkVerb::Unlink`], the
//! [`UNLINK_CLAIM_DOMAIN`] and [`unlink_claim_message`] since the deep version's brick 2 — a
//! domain-separated attestation, signed by the root key, that cannot be forged from a LINK
//! signature because the domains differ. It had **no shallow consumer**: it was waiting for the
//! identity cell, while the TSV store the boards actually read had no way to express a removal.
//!
//! So this module is a wiring job, not an invention. The two halves it joins:
//!
//! * the **attestation** that already existed — [`unlink_claim_message`], signed here by the key the
//!   player's 24 words derive, and verified with the shared
//!   [`verify_detached`](dreggnet_offerings::verify_detached) before anything is written;
//! * the **record** that now exists — [`LinkStore::revoke`], whose tombstone drops the binding out
//!   of BOTH resolution directions and does so even for a reader too old to know what a tombstone
//!   is (see `link_registry`'s revocation note for why that mattered more than a tidier schema).
//!
//! ## The gate that actually matters: you may only remove YOUR OWN row
//!
//! The authority is the phrase, and the check is that the row **currently resolves to the key those
//! words derive**. That is deliberately not "the row names your root somewhere in history": a
//! binding that has since been superseded by its rightful owner is no longer yours to revoke, and
//! revoking it would let a previous holder reach into the current one's record. The live view
//! ([`LinkStore::platforms_for_root`]) is the same one the link page prints, so what a player can
//! remove is exactly what they are shown.
//!
//! ⚑ **It is not gated on the browser's cookie.** Like restoring and like linking, the words are the
//! authority, so a player can undo a mistaken link from a device that has never seen this server —
//! which is the case that matters, because the machine where the mistake happened is often the one
//! they no longer trust.
//!
//! ## What a revocation does and does not do
//!
//! It removes the **join**. The two keys stop resolving to one human: the board ranks them
//! separately again, `/you` stops counting the other side's play, and the row leaves the link page.
//!
//! It does not, and cannot, do three things, all of them said on the page:
//!
//! * **It does not take the custodial key away from the operator.** A Discord key is
//!   `BLAKE3(bot secret, account id)` before a link, during it, and after a revocation. Un-linking
//!   is not a security boundary against the bot's operator and would be a lie if it were sold as
//!   one.
//! * **It does not stop a revoked device key from signing.** Its signatures still verify under its
//!   own public key, because a signature is a fact about bytes. What stops is the *resolution* — the
//!   key is nobody's again, so nothing it signs lands on the player's record. Refusing such a turn
//!   at the gate wants the session-grant envelope and is a different seam.
//! * **It does not erase history.** The log is append-only on purpose; a revocation is a later line,
//!   not a deletion. The play that already happened still happened.

use std::sync::Arc;

use axum::Router;
use axum::extract::{Form, State};
use axum::http::{HeaderMap, StatusCode, header};
use axum::response::{Html, IntoResponse, Response};
use axum::routing::{get, post};
use serde::Deserialize;
use zeroize::Zeroize;

use dreggnet_offerings::{TurnSigner, verify_detached};
use webauth_core::challenge;
use webauth_core::link_kel::unlink_claim_message;
use webauth_core::link_registry::{FileLinkStore, LinkRecord, LinkStore, default_store_path};

use crate::device_key::{DEVICE_PLATFORM, platform_is_self_held};
use crate::identity_link::WEB_PLATFORM;
use crate::seed_identity::{
    self, CLAIM_COOKIE, derive_root_keypair, normalize_typed_phrase, read_cookie, short_tag,
};
use crate::{document_with_head, esc, notice_html};

/// How long the un-link page's challenge stays usable — the same window the device page uses, for
/// the same reason: bounded, so a page left open on a shared machine stops being able to act.
const UNLINK_TTL_SECS: u64 = 30 * 60;

/// The server key an un-link challenge is minted and verified under. A THIRD, separate key domain:
/// no challenge minted for logging in, for linking, or for enrolling a device can be spent here.
fn unlink_key() -> &'static [u8; 32] {
    static KEY: std::sync::OnceLock<[u8; 32]> = std::sync::OnceLock::new();
    KEY.get_or_init(|| {
        crate::table_seats::resolve_process_key(
            "DREGGNET_WEB_UNLINK_KEY",
            "web-unlink-key.bin",
            "removing a linked account",
        )
    })
}

fn unix_now() -> u64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0)
}

// ─────────────────────────────────────────────────────────────────────────────
// The refusal taxonomy
// ─────────────────────────────────────────────────────────────────────────────

/// Why a removal was refused. Nothing was written in any of them.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UnlinkRefusal {
    /// ⚑ The request did not come from a page on this site. First, ahead of everything: a
    /// cross-origin submit here would let a hostile page tear a player's accounts apart while they
    /// watched something else.
    NotFromOurPage,
    /// The page had been open too long, or the token is not one this server minted.
    StaleChallenge,
    /// The confirmation box was not ticked.
    NotConfirmed,
    /// The phrase did not validate — carries the which-check-failed sentence already rendered.
    BadPhrase(String),
    /// ⚑ **The words are valid, but they do not name the human this binding currently belongs to.**
    /// The one gate that stops a removal from being a way to reach into somebody else's record.
    NotYours,
    /// Our own attestation failed our own verifier. Never a statement about the player.
    SelfCheckFailed,
    /// The append to the shared store failed.
    NotRecorded,
}

impl UnlinkRefusal {
    fn http_status(&self) -> StatusCode {
        match self {
            UnlinkRefusal::NotFromOurPage
            | UnlinkRefusal::StaleChallenge
            | UnlinkRefusal::NotYours => StatusCode::FORBIDDEN,
            UnlinkRefusal::NotConfirmed | UnlinkRefusal::BadPhrase(_) => StatusCode::BAD_REQUEST,
            UnlinkRefusal::SelfCheckFailed | UnlinkRefusal::NotRecorded => {
                StatusCode::INTERNAL_SERVER_ERROR
            }
        }
    }

    fn message(&self) -> String {
        match self {
            UnlinkRefusal::NotFromOurPage => "Refused: this did not come from our page, so nothing \
                 was removed and your words were not used. Open the removal page here and try \
                 again. If something on another website submitted this for you, it was trying to \
                 pull your accounts apart without showing you."
                .to_string(),
            UnlinkRefusal::StaleChallenge => "Refused: this page had been open too long, so \
                 nothing was removed and your words were not used. Reload the page and do it again."
                .to_string(),
            UnlinkRefusal::NotConfirmed => "Refused: the confirmation box was not ticked, so \
                 nothing was removed and your words were not used. Tick it and try again."
                .to_string(),
            UnlinkRefusal::BadPhrase(detail) => format!(
                "Refused: {detail} Nothing was removed and everything is still linked exactly as it \
                 was. Check that one word and try again."
            ),
            UnlinkRefusal::NotYours => "Refused: those 24 words are a valid phrase, but this \
                 account is not currently attached to the identity they name, so nothing was \
                 removed. If you meant a different identity, check that you typed the right phrase. \
                 If somebody else has since attached this account to themselves, it is theirs to \
                 remove now, not yours."
                .to_string(),
            UnlinkRefusal::SelfCheckFailed => "Refused: this server built a removal that its own \
                 checker would not accept, so it wrote nothing and everything is still linked. That \
                 is a fault on our side, not in what you did, and the server log names the cause."
                .to_string(),
            UnlinkRefusal::NotRecorded => "Refused: the removal was proven but could not be \
                 written to the shared record, so nothing was removed. That is on our side; the \
                 server log names the cause. Try again in a moment."
                .to_string(),
        }
    }
}

fn phrase_detail(error: &dregg_sdk::mnemonic::MnemonicError) -> String {
    use dregg_sdk::mnemonic::MnemonicError;
    match error {
        MnemonicError::InvalidWordCount(n) => format!(
            "that is {n} word{}; a dregg phrase is exactly 24.",
            if *n == 1 { "" } else { "s" }
        ),
        MnemonicError::UnknownWord(word) => format!(
            "{:?} is not one of the 2048 words in the list; check that word's spelling.",
            esc(word)
        ),
        MnemonicError::InvalidChecksum => "all 24 words are real words, but the phrase's own \
             checksum does not match, which almost always means ONE word is wrong or two are \
             swapped."
            .to_string(),
    }
}

/// What a successful removal took away.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Unlinked {
    /// The platform whose binding is gone (`"discord"`, `"telegram"`, or a device).
    pub platform: String,
    /// The account id, or the device's short tag.
    pub platform_uid: String,
    /// The key that no longer resolves to this human.
    pub custodial_pubkey_hex: String,
}

// ─────────────────────────────────────────────────────────────────────────────
// State + mount
// ─────────────────────────────────────────────────────────────────────────────

/// The un-link door's state. Holds no player material.
pub struct IdentityUnlinkState {
    store_path: std::path::PathBuf,
}

impl IdentityUnlinkState {
    /// State over an explicit store path — the seam tests drive.
    pub fn new(store_path: std::path::PathBuf) -> Self {
        IdentityUnlinkState { store_path }
    }
}

/// **Mount the un-link door.** Additive, under the `/identity` prefix the identity routes own.
pub fn identity_unlink_router(state: Arc<IdentityUnlinkState>) -> Router {
    Router::new()
        .route("/identity/unlink", get(get_unlink).post(post_unlink))
        .with_state(state)
}

/// The un-link door over the shared store every dregg unit points at.
pub fn identity_unlink_from_env() -> Router {
    identity_unlink_router(Arc::new(IdentityUnlinkState::new(default_store_path())))
}

// ─────────────────────────────────────────────────────────────────────────────
// ⚑ THE CEREMONY — pure over its clock and its store
// ─────────────────────────────────────────────────────────────────────────────

/// **Prove and record a removal.** The complete gate order:
///
/// 1. **freshness** — the challenge must be one this server minted and not expired
///    ([`UnlinkRefusal::StaleChallenge`]), before the phrase is touched;
/// 2. **consent** ([`UnlinkRefusal::NotConfirmed`]), also before the derivation, so a refusal costs
///    no phrase submission;
/// 3. **your half** — the 24 words derive the root key ([`UnlinkRefusal::BadPhrase`]);
/// 4. ⚑ **ownership** — the binding must appear in the LIVE view of that root
///    ([`UnlinkRefusal::NotYours`]). This is the gate that makes a removal safe to expose: it is
///    read from [`LinkStore::platforms_for_root`], the same function the link page renders, so a
///    player can remove exactly what they can see and nothing else;
/// 5. **sign** the canonical UNLINK attestation with the root key — a domain separate from LINK, so
///    a captured link signature can never be replayed as a removal;
/// 6. **self-check** the attestation before writing anything;
/// 7. **record** the tombstone.
fn prove_and_record(
    state: &IdentityUnlinkState,
    custodial_pubkey_hex: &str,
    raw_phrase: &str,
    chal: &str,
    confirmed: bool,
    now: u64,
) -> Result<Unlinked, UnlinkRefusal> {
    // 1. Freshness.
    if challenge::verify(unlink_key(), chal, now).is_err() {
        return Err(UnlinkRefusal::StaleChallenge);
    }
    // 2. Consent.
    if !confirmed {
        return Err(UnlinkRefusal::NotConfirmed);
    }
    // 3. YOUR HALF.
    let mut phrase = normalize_typed_phrase(raw_phrase);
    let derived = derive_root_keypair(&phrase);
    phrase.zeroize();
    let (root_pubkey_hex, root_seed) =
        derived.map_err(|e| UnlinkRefusal::BadPhrase(phrase_detail(&e)))?;

    // 4. ⚑ OWNERSHIP, from the LIVE view. Note this is `platforms_for_root`, not a scan of history:
    //    a binding somebody else has since taken over is no longer this player's to revoke, and
    //    reading history instead would hand a former holder a lever on the current one.
    let mut store = FileLinkStore::new(&state.store_path);
    let row: LinkRecord = store
        .platforms_for_root(&root_pubkey_hex)
        .unwrap_or_default()
        .into_iter()
        .find(|r| {
            r.custodial_pubkey_hex
                .eq_ignore_ascii_case(custodial_pubkey_hex)
        })
        .ok_or(UnlinkRefusal::NotYours)?;

    // ⚑ The web SELF-row is not removable, and that is not an oversight. It records "this identity
    // acts under its own key on the web" — the row that makes the resolver give the player's own
    // key and their linked keys the same join key. Removing it would not un-link anything; it would
    // split the player from THEMSELVES, so the board printed two rows for one person again.
    if row.platform == WEB_PLATFORM {
        return Err(UnlinkRefusal::NotYours);
    }

    // 5. The attestation, under the UNLINK domain.
    let message = unlink_claim_message(
        &row.platform,
        &row.platform_uid,
        &row.custodial_pubkey_hex,
        &root_pubkey_hex,
        chal,
    )
    .map_err(|_| UnlinkRefusal::SelfCheckFailed)?;
    let signature = TurnSigner::from_seed(*root_seed).sign_detached(&message);
    drop(root_seed); // wiped by `Zeroizing`; explicit so the wipe point is visible.

    // 6. THE SELF-CHECK, with the shared verifier, on our own bytes.
    verify_detached(&root_pubkey_hex, &message, &signature)
        .map_err(|_| UnlinkRefusal::SelfCheckFailed)?;

    // 7. Record the tombstone.
    store
        .revoke(
            &row.platform,
            &row.platform_uid,
            &row.custodial_pubkey_hex,
            now,
        )
        .map_err(|_| UnlinkRefusal::NotRecorded)?;

    Ok(Unlinked {
        platform: row.platform,
        platform_uid: row.platform_uid,
        custodial_pubkey_hex: row.custodial_pubkey_hex,
    })
}

// ─────────────────────────────────────────────────────────────────────────────
// Handlers
// ─────────────────────────────────────────────────────────────────────────────

/// The removal form.
#[derive(Debug, Clone, Deserialize)]
pub struct UnlinkForm {
    /// Which binding to remove, named by the key it is for.
    pub custodial_pubkey_hex: String,
    /// The challenge this page was rendered with.
    pub challenge: String,
    /// The 24 words.
    pub phrase: String,
    /// Present only when the confirmation box is ticked.
    #[serde(default)]
    pub understood: Option<String>,
}

fn no_store(body: String) -> Response {
    let mut response = Html(body).into_response();
    response.headers_mut().insert(
        header::CACHE_CONTROL,
        header::HeaderValue::from_static("private, no-store, max-age=0"),
    );
    response.headers_mut().insert(
        header::REFERRER_POLICY,
        header::HeaderValue::from_static("no-referrer"),
    );
    response
}

fn viewer_root(headers: &HeaderMap) -> Option<String> {
    read_cookie(headers, CLAIM_COOKIE).and_then(|l| seed_identity::parse_claim_label(&l))
}

/// `GET /identity/unlink` — what removing does, what this identity currently has, and one form per
/// removable binding.
async fn get_unlink(State(state): State<Arc<IdentityUnlinkState>>, headers: HeaderMap) -> Response {
    let root = viewer_root(&headers);
    no_store(unlink_page(
        &state.store_path,
        root.as_deref(),
        challenge::issue(unlink_key(), unix_now(), UNLINK_TTL_SECS),
        None,
        None,
    ))
}

/// `POST /identity/unlink` — remove one binding.
async fn post_unlink(
    State(state): State<Arc<IdentityUnlinkState>>,
    headers: HeaderMap,
    Form(form): Form<UnlinkForm>,
) -> Response {
    let root = viewer_root(&headers);
    let fresh = || challenge::issue(unlink_key(), unix_now(), UNLINK_TTL_SECS);

    if !seed_identity::same_origin_post(&headers) {
        tracing::warn!(
            "REFUSED a removal that could not show it came from a page on this site — nothing was \
             derived and NO RECORD WAS WRITTEN"
        );
        let message = UnlinkRefusal::NotFromOurPage.message();
        return (
            UnlinkRefusal::NotFromOurPage.http_status(),
            no_store(unlink_page(
                &state.store_path,
                root.as_deref(),
                fresh(),
                None,
                Some(&message),
            )),
        )
            .into_response();
    }

    match prove_and_record(
        &state,
        &form.custodial_pubkey_hex,
        &form.phrase,
        &form.challenge,
        form.understood.is_some(),
        unix_now(),
    ) {
        Ok(unlinked) => {
            tracing::info!(
                platform = %unlinked.platform,
                platform_uid = %unlinked.platform_uid,
                custodial = %unlinked.custodial_pubkey_hex,
                "identity link REVOKED — the key no longer resolves to that human on any board; \
                 history is preserved (the record is append-only) and the custodial key itself is \
                 unchanged"
            );
            let message = format!(
                "Removed. {} is no longer attached to this identity: the boards rank it separately \
                 again and your record stops counting its play. Nothing you already played was \
                 deleted.",
                describe(&unlinked.platform, &unlinked.platform_uid),
            );
            no_store(unlink_page(
                &state.store_path,
                root.as_deref(),
                fresh(),
                Some(&message),
                None,
            ))
        }
        Err(refusal) => {
            let status = refusal.http_status();
            let message = refusal.message();
            (
                status,
                no_store(unlink_page(
                    &state.store_path,
                    root.as_deref(),
                    fresh(),
                    None,
                    Some(&message),
                )),
            )
                .into_response()
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The page
// ─────────────────────────────────────────────────────────────────────────────

/// How a binding is named to a person. A device is "this browser", not an account number.
fn describe(platform: &str, platform_uid: &str) -> String {
    if platform == DEVICE_PLATFORM {
        format!("Browser {}", esc(platform_uid))
    } else {
        format!(
            "{} account {}",
            esc(&title_case(platform)),
            esc(platform_uid)
        )
    }
}

fn title_case(s: &str) -> String {
    let mut chars = s.chars();
    match chars.next() {
        Some(first) => first.to_uppercase().collect::<String>() + chars.as_str(),
        None => String::new(),
    }
}

const UNLINK_STYLE: &str = r##"<style>
.ul-list{list-style:none;margin:1.2rem 0;padding:0;display:flex;flex-direction:column;gap:.9rem}
.ul-list li{padding:.85rem 1rem;border:1px solid var(--line,#2a2a2a);
 border-left:3px solid rgba(201,106,94,.6);border-radius:0 4px 4px 0;background:rgba(255,255,255,.02)}
.ul-list li.self{border-left-color:rgba(120,200,150,.7)}
.ul-list b{display:block;font-size:.98rem}
.ul-key{font-family:ui-monospace,Menlo,monospace;font-size:.82rem;overflow-wrap:anywhere;opacity:.8}
.ul-form label{display:block;margin:.8rem 0 .3rem;font-size:.78rem;letter-spacing:.1em;
 text-transform:uppercase;opacity:.7}
.ul-form textarea{width:100%;min-height:4.5rem;padding:.55rem .65rem;border:1px solid var(--line,#2a2a2a);
 border-radius:4px;background:rgba(0,0,0,.25);color:inherit;font-family:ui-monospace,Menlo,monospace;
 font-size:.86rem;line-height:1.6}
.ul-check{display:flex;gap:.55rem;align-items:flex-start;margin:.85rem 0 .2rem;line-height:1.55;
 font-size:.92rem}
.ul-check input{margin-top:.3rem;flex:none}
</style>"##;

/// One removable binding, with its own form. Each row carries its own phrase box on purpose: a
/// single form with a row selector would let a mis-click remove the wrong account, and the words are
/// typed once per removal precisely so the act stays deliberate.
fn removable_rows(store_path: &std::path::Path, root: &str, challenge: &str) -> String {
    let rows: Vec<LinkRecord> = FileLinkStore::new(store_path)
        .platforms_for_root(root)
        .unwrap_or_default()
        .into_iter()
        // The web self-row is the identity's own key; see `prove_and_record` for why removing it
        // would split the player from themselves rather than un-link anything.
        .filter(|r| r.platform != WEB_PLATFORM)
        .collect();
    if rows.is_empty() {
        return "<p class=\"prose\">Nothing is attached to this identity, so there is nothing to \
                remove. If you meant to attach a chat account, \
                <a href=\"/identity/link\">the linking page</a> is where that happens.</p>"
            .to_string();
    }
    let mut sorted = rows;
    sorted.sort_by(|a, b| {
        a.platform
            .cmp(&b.platform)
            .then_with(|| a.platform_uid.cmp(&b.platform_uid))
    });
    let items: String = sorted
        .iter()
        .map(|r| {
            let self_held = platform_is_self_held(&r.platform);
            let what = if self_held {
                "This is a browser you allowed to sign turns as you. Removing it means turns it \
                 signs stop being recorded as yours. It does not delete anything that browser \
                 already played, and it does not reach into that browser to destroy its key."
            } else {
                "This is a chat account you proved you control. Removing it means the boards rank \
                 it separately from you again and your record stops counting its play. The key that \
                 account plays under belongs to whoever runs the bot, before and after this, and \
                 removing the link does not change that."
            };
            format!(
                "<li{cls}><b>{name}</b><span class=\"ul-key\">{key}</span>\
                 <p class=\"prose\" style=\"margin:.45rem 0 0;font-size:.92rem\">{what}</p>\
                 <form class=\"ul-form\" method=\"post\" action=\"/identity/unlink\">\
                 <input type=\"hidden\" name=\"custodial_pubkey_hex\" value=\"{key}\">\
                 <input type=\"hidden\" name=\"challenge\" value=\"{chal}\">\
                 <label for=\"p-{tag}\">Your 24 words, to prove this is yours to remove</label>\
                 <textarea id=\"p-{tag}\" name=\"phrase\" rows=\"2\" autocomplete=\"off\" \
                 spellcheck=\"false\" autocapitalize=\"none\" \
                 placeholder=\"abandon ability able about …\"></textarea>\
                 <label class=\"ul-check\"><input type=\"checkbox\" name=\"understood\" \
                 value=\"yes\"><span>Remove this. I understand the play that already happened stays \
                 where it is.</span></label>\
                 <div class=\"id-actions\" style=\"margin:.7rem 0 0\">\
                 <button class=\"btn\" type=\"submit\">Remove {name}</button></div>\
                 </form></li>",
                cls = if self_held { " class=\"self\"" } else { "" },
                name = describe(&r.platform, &r.platform_uid),
                key = esc(&r.custodial_pubkey_hex),
                chal = esc(challenge),
                tag = esc(&short_tag(&r.custodial_pubkey_hex)),
                what = what,
            )
        })
        .collect();
    format!("<ul class=\"ul-list\">{items}</ul>")
}

fn unlink_page(
    store_path: &std::path::Path,
    root_pubkey_hex: Option<&str>,
    challenge: String,
    success: Option<&str>,
    refusal: Option<&str>,
) -> String {
    let notice = notice_html(success.or(refusal));
    let body = match root_pubkey_hex {
        Some(root) => format!(
            "<h2>Attached to <span class=\"ul-key\">{tag}</span></h2>\
             <p class=\"prose\">Everything currently attached to the identity your 24 words derive. \
             Removing one takes the connection away; it never touches the account, the browser, or \
             the play.</p>{rows}",
            tag = esc(&short_tag(root)),
            rows = removable_rows(store_path, root, &challenge),
        ),
        None => "<h2>No identity on this browser yet</h2>\
             <p class=\"prose\">This page shows what is attached to the identity this browser is \
             signed in as, so there is nothing to show yet. \
             <a href=\"/identity\">Restore your identity with your 24 words</a> and come back, and \
             everything attached to it will be listed here with a way to remove each one.</p>"
            .to_string(),
    };
    document_with_head(
        "Remove a linked account · DreggNet",
        "",
        UNLINK_STYLE,
        &format!(
            "<main class=\"session\">\
             <header class=\"page-head\"><p class=\"eyebrow\">Identity · removing</p>\
             <h1>Undo a link</h1>\
             <p class=\"deck\">A link made by mistake used to be permanent. It is not any \
             more.</p></header>{notice}\
             <p class=\"prose\">Linking says &ldquo;this account and this identity are the same \
             human&rdquo;, so the boards rank you once. Removing it says the opposite from now on: \
             the two go back to being separate players, your record stops counting the other side, \
             and the row disappears from your linking page.</p>\
             <p class=\"prose\">Three things it deliberately does not do. It does not delete \
             anything you played: the record only ever grows, so a removal is a later entry rather \
             than an erasure, and your past runs stay exactly where they are. It does not take a \
             chat account's key away from whoever runs that bot; that key was theirs to derive \
             before you ever linked and it still is. And it is not a way to reach into somebody \
             else's record: you can only remove what is attached to the identity your own 24 words \
             name, which is exactly the list below.</p>\
             {body}</main>",
            notice = notice,
            body = body,
        ),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_sdk::mnemonic::generate_mnemonic;
    use dreggnet_offerings::refusal::audit_player_text;
    use webauth_core::identity_resolve::RootResolver;

    const NOW: u64 = 1_790_000_000;

    fn tmp_store(tag: &str) -> std::path::PathBuf {
        let dir = std::env::temp_dir().join(format!(
            "dregg-identity-unlink-{}-{tag}-{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        let _ = std::fs::remove_dir_all(&dir);
        dir.join("links.tsv")
    }

    fn link(store: &std::path::Path, root: &str, platform: &str, uid: &str, cust: &str, at: u64) {
        FileLinkStore::new(store)
            .record(&LinkRecord {
                root_pubkey_hex: root.to_string(),
                platform: platform.to_string(),
                platform_uid: uid.to_string(),
                custodial_pubkey_hex: cust.to_string(),
                verified_at: at,
            })
            .expect("the test store writes");
    }

    /// ⚑ THE DOOR ACTUALLY OPENS: a bad link is removable, it leaves both directions, and the
    /// player's OTHER link survives — removing one account is not signing out.
    #[test]
    fn a_mistaken_link_can_be_removed_and_the_others_survive() {
        let path = tmp_store("payoff");
        let state = IdentityUnlinkState::new(path.clone());
        let phrase = generate_mnemonic();
        let root = seed_identity::derive_pubkey_hex(&phrase).expect("a fresh phrase derives");
        let stranger = "aa".repeat(32);
        let mine = "bb".repeat(32);
        // The bad row (a stranger's account, bound with the player's own signature) and a good one.
        link(&path, &root, "discord", "111", &stranger, 100);
        link(&path, &root, "telegram", "222", &mine, 101);
        link(&path, &root, WEB_PLATFORM, &root, &root, 100);

        // NON-VACUOUS: the stranger really is joined to this human first.
        let before = RootResolver::from_store(&FileLinkStore::new(&path));
        assert_eq!(before.resolve(&stranger), before.resolve(&root));

        let chal = challenge::issue(unlink_key(), NOW, UNLINK_TTL_SECS);
        let gone = prove_and_record(&state, &stranger, &phrase, &chal, true, NOW + 5)
            .expect("the removal proves");
        assert_eq!(gone.platform, "discord");
        assert_eq!(gone.platform_uid, "111");

        // The join is gone in both directions…
        let store = FileLinkStore::new(&path);
        assert_eq!(store.resolve_root(&stranger).expect("readable"), None);
        let left: Vec<String> = store
            .platforms_for_root(&root)
            .expect("readable")
            .into_iter()
            .map(|r| r.platform)
            .collect();
        assert!(!left.contains(&"discord".to_string()));
        // …and the OTHER account, plus the player's own web row, are untouched.
        assert!(left.contains(&"telegram".to_string()));
        assert!(left.contains(&WEB_PLATFORM.to_string()));
        let after = RootResolver::from_store(&FileLinkStore::new(&path));
        assert_ne!(after.resolve(&stranger), after.resolve(&root));
        assert_eq!(after.resolve(&mine), after.resolve(&root));

        let _ = std::fs::remove_dir_all(path.parent().expect("a temp dir"));
    }

    /// ⚑ THE OWNERSHIP TOOTH — the gate that makes this door safe to expose at all. A valid phrase
    /// that is not the CURRENT holder's removes nothing, and neither does one aimed at a key that
    /// was never linked. Both polarities, so the gate is not vacuously refusing everything.
    #[test]
    fn only_the_current_holder_can_remove_a_binding() {
        let path = tmp_store("ownership");
        let state = IdentityUnlinkState::new(path.clone());
        let owner_phrase = generate_mnemonic();
        let other_phrase = generate_mnemonic();
        let owner = seed_identity::derive_pubkey_hex(&owner_phrase).expect("derives");
        let account = "cc".repeat(32);
        link(&path, &owner, "discord", "111", &account, 100);

        let chal = challenge::issue(unlink_key(), NOW, UNLINK_TTL_SECS);
        // A DIFFERENT valid phrase cannot touch it.
        assert_eq!(
            prove_and_record(&state, &account, &other_phrase, &chal, true, NOW),
            Err(UnlinkRefusal::NotYours)
        );
        // Nor can the owner remove a key that is not attached to them at all.
        assert_eq!(
            prove_and_record(&state, &"dd".repeat(32), &owner_phrase, &chal, true, NOW),
            Err(UnlinkRefusal::NotYours)
        );
        // Nor the web self-row, which is the identity's own key rather than a link.
        link(&path, &owner, WEB_PLATFORM, &owner, &owner, 100);
        assert_eq!(
            prove_and_record(&state, &owner, &owner_phrase, &chal, true, NOW),
            Err(UnlinkRefusal::NotYours)
        );
        // …and NOTHING above wrote a tombstone.
        assert_eq!(
            FileLinkStore::new(&path)
                .resolve_root(&account)
                .expect("readable"),
            Some(owner.clone()),
            "a refused removal must leave the binding exactly as it was"
        );
        // The owner CAN, which is what makes the three refusals above meaningful.
        assert!(prove_and_record(&state, &account, &owner_phrase, &chal, true, NOW).is_ok());

        let _ = std::fs::remove_dir_all(path.parent().expect("a temp dir"));
    }

    /// Every other gate refuses and writes nothing.
    #[test]
    fn the_remaining_gates_refuse_and_record_nothing() {
        let path = tmp_store("gates");
        let state = IdentityUnlinkState::new(path.clone());
        let phrase = generate_mnemonic();
        let root = seed_identity::derive_pubkey_hex(&phrase).expect("derives");
        let account = "ee".repeat(32);
        link(&path, &root, "discord", "111", &account, 100);
        let chal = challenge::issue(unlink_key(), NOW, UNLINK_TTL_SECS);

        assert_eq!(
            prove_and_record(&state, &account, &phrase, "nope", true, NOW),
            Err(UnlinkRefusal::StaleChallenge)
        );
        assert_eq!(
            prove_and_record(
                &state,
                &account,
                &phrase,
                &chal,
                true,
                NOW + UNLINK_TTL_SECS + 60
            ),
            Err(UnlinkRefusal::StaleChallenge)
        );
        assert_eq!(
            prove_and_record(&state, &account, &phrase, &chal, false, NOW),
            Err(UnlinkRefusal::NotConfirmed)
        );
        assert!(matches!(
            prove_and_record(&state, &account, "abandon ability able", &chal, true, NOW),
            Err(UnlinkRefusal::BadPhrase(_))
        ));
        assert_eq!(
            FileLinkStore::new(&path)
                .resolve_root(&account)
                .expect("readable"),
            Some(root),
            "no refused gate may write a tombstone"
        );

        let _ = std::fs::remove_dir_all(path.parent().expect("a temp dir"));
    }

    /// ⚑ THE COPY GATE, on the strings this module ships.
    #[test]
    fn every_refusal_passes_the_shared_copy_gate() {
        for refusal in [
            UnlinkRefusal::NotFromOurPage,
            UnlinkRefusal::StaleChallenge,
            UnlinkRefusal::NotConfirmed,
            UnlinkRefusal::BadPhrase("that is 3 words; a dregg phrase is exactly 24.".to_string()),
            UnlinkRefusal::NotYours,
            UnlinkRefusal::SelfCheckFailed,
            UnlinkRefusal::NotRecorded,
        ] {
            let text = refusal.message();
            assert_eq!(
                audit_player_text(&text, true, true),
                Vec::new(),
                "a refusal this module ships fails the shared copy gate: {text}"
            );
            assert!(text.starts_with("Refused:"), "{text}");
        }
    }
}
