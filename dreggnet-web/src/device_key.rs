//! # `device_key` — **the browser signs, and this server cannot.**
//!
//! ## The gap this closes, stated at its real size
//!
//! Every turn pressed in a browser landed [`Attribution::Asserted`](dreggnet_offerings::Attribution):
//! the page took the name in the cookie at face value and checked no signature. The product said so
//! honestly on four surfaces — but honest is not strong, and on a board whose pitch is that it
//! cannot be faked, "we took your word for it" is the whole of what a web row meant.
//!
//! [`crate::seed_identity`] named the blocker: deriving the phrase's key in the browser needs a real
//! BLAKE3 in JS, and hand-rolling BLAKE3 is forbidden here, so it is a dependency decision left for
//! ember. **That blocker is real and it is untouched. It was also not the blocker for signing.**
//!
//! `dreggnet_offerings::signed::signing_message` contains NO HASH. It is a plain byte
//! concatenation of the domain tag, the offering key, the session id, the counter, and the action's
//! `{turn, arg, text}`. Signing a turn therefore needs Ed25519 and nothing else — and Ed25519 has
//! been in the browser's own `crypto.subtle` since Chrome 137 / Firefox 129 / Safari 17. So the web
//! reaches [`Attribution::Signed`](dreggnet_offerings::Attribution) with **no new dependency, no
//! vendored crypto, and no BLAKE3 in JS**.
//!
//! ## ⚑ THE CHOICE, and why it is not "hand the browser the phrase's key"
//!
//! Three routes were on the table (`assets/dregg-device-key.mjs` carries the JS half of this
//! reasoning):
//!
//! 1. **Vendor a BLAKE3 JS/wasm and derive the phrase's key in the browser.** Strongest — the words
//!    would never leave the device — and NOT TAKEN here, because it is the dependency decision
//!    `seed_identity` explicitly reserves, and because it is not needed to make a move signed. It
//!    remains the right next step for a different property (keeping the phrase off the wire), and
//!    nothing here is in its way.
//! 2. **Reuse the `wasm/` crate, which now derives correctly through `dregg_sdk::mnemonic`.** NOT
//!    TAKEN: the shipped `extension/dregg_wasm{.js,_bg.wasm}` are COMMITTED BUILD ARTIFACTS that
//!    still carry the pre-fix derivation (`seed_identity`'s residuals say so in those words), so
//!    adopting them would mean shipping a browser that files a player's signed play under a
//!    different identity than their asserted play — the exact wound that was just closed.
//! 3. **Keep derivation server-side and let the BROWSER hold a key.** TAKEN — but in the stronger
//!    form. The obvious reading of (3) is "derive from the phrase, hand the secret to the browser",
//!    and that would make [`Custody::UserHeld`](dreggnet_offerings::Custody) an overstatement: the
//!    server would have held that secret, and `Custody`'s whole purpose is to refuse exactly that
//!    kind of self-awarded grade. **So the browser mints its own keypair instead.** The server never
//!    sees it, cannot reproduce it, and could not sign as this device if it wanted to. `UserHeld` is
//!    then literally true rather than generously interpreted.
//!
//! ## What a web move carries now
//!
//! ```text
//!   browser:  crypto.subtle.generateKey({name:"Ed25519"}, extractable=FALSE)   ← the secret, once
//!             stored in IndexedDB as a live key handle — never as bytes
//!   enrol:    POST /identity/device   device pubkey + your 24 words
//!             the phrase signs "this device may act as me" (webauth_core::link_claim)
//!             recorded as a link row: device pubkey → your root key
//!   play:     POST /offerings/{key}/session/{id}/act-signed
//!             signature made by crypto.subtle in the page, verified by verify_signed
//!             → Attribution::Signed + Custody::UserHeld
//! ```
//!
//! The phrase still transits the server at enrolment, exactly as `/identity/restore` already makes
//! it. What is new is that **it transits once per device instead of once per session, and after it
//! every move carries a signature this server did not produce.**
//!
//! ## ⚑ THE HONEST COST: a device is a second key, and the boards join it
//!
//! A device key is not the identity. The identity is still the phrase's key, and a turn signed by
//! the device is attributed to the DEVICE'S public key by
//! [`verify_signed`](dreggnet_offerings::verify_signed) — because that is what actually signed, and
//! rewriting the attributed actor to the root would be a signature claim about a key that did not
//! sign.
//!
//! The join is therefore the one the product already has: the enrolment writes a
//! [`LinkRecord`](webauth_core::link_registry::LinkRecord) under [`DEVICE_PLATFORM`], so
//! `RootResolver` collapses the device key and the phrase key onto one human on the Descent board,
//! and `/you` counts both. That is the identical mechanism a linked Discord account uses, with one
//! difference stated on the page: **a device key is the only linked key in the system that is
//! neither the operator's nor derivable from anything the operator holds.**
//!
//! The residual that follows from it, named rather than implied: an offering's PER-IDENTITY state
//! (an RPG world keyed by actor) is keyed on the signing key, so a session played half-asserted and
//! half-signed is two actors to the host even though it is one human to every board. Enrolment is
//! therefore a deliberate act on its own page, not something a game does for you mid-run.
//!
//! ## Named residuals
//!
//! * **The user-held lane is not epoch-bound.** `act_signed.rs` binds the host incarnation only for
//!   custodial signers; the browser signs the epoch-free message, exactly as the extension does. The
//!   fix is the same one the extension owes: echo and sign the epoch. Until then a captured envelope
//!   could re-verify on a same-id session reopened after a restart.
//! * **Revocation is the un-link door** ([`crate::identity_unlink`]) and it removes the JOIN, not the
//!   key's ability to sign. A revoked device still produces signatures that `verify_signed` accepts
//!   under its own public key; what it stops doing is resolving to the player's human. Turning a
//!   revocation into a refusal at the turn gate wants the session-grant envelope, which is a
//!   different seam and is not touched here.
//! * **Nothing yet enrols a device from the extension or the CLI**, which hold the phrase's own key
//!   and reach `Signed`/`UserHeld` directly without one.

use std::sync::Arc;

use axum::Router;
use axum::extract::{Form, State};
use axum::http::{HeaderMap, StatusCode, header};
use axum::response::{Html, IntoResponse, Response};
use axum::routing::{get, post};
use serde::Deserialize;
use zeroize::Zeroize;

use webauth_core::challenge;
use webauth_core::link_claim::{sign_link_claim, verify_link_claim};
use webauth_core::link_registry::{FileLinkStore, LinkRecord, LinkStore, default_store_path};

use crate::seed_identity::{
    self, CLAIM_COOKIE, derive_root_keypair, normalize_typed_phrase, read_cookie, short_tag,
};
use crate::{document_with_head, esc, notice_html};

// ─────────────────────────────────────────────────────────────────────────────
// Constants
// ─────────────────────────────────────────────────────────────────────────────

/// The `platform` string a device enrolment wears in the shared link store.
///
/// ⚑ Deliberately NOT `"web"`. The web self-row records "this root key acts under itself on the web"
/// and its custodial key IS the root; a device row records a DIFFERENT key that the root has
/// authorised. Collapsing them would make the device key look like the identity, and `/you` would
/// then count the same play twice.
pub const DEVICE_PLATFORM: &str = "device";

/// How long an enrolment page's challenge stays usable. Generous — a person is copying 24 words —
/// but bounded, so a device page left open on a shared machine stops being enrollable.
const ENROL_TTL_SECS: u64 = 30 * 60;

/// Whether a stored link row's key is SELF-HELD rather than derivable by an operator.
///
/// ⚑ This function exists because the flag used to be spelled `platform != "web"`, which was right
/// while `"web"` was the only self-held row and became WRONG the moment a device row could exist: it
/// would have printed "the operator can derive this key" beside the one key in the whole system that
/// nobody but this browser can produce. Understating custody is the safe direction, so it was never
/// going to be a security bug — it would have been a lie in the player's favour, which on a page
/// whose entire job is telling them who holds what is the same defect.
pub fn platform_is_self_held(platform: &str) -> bool {
    matches!(
        platform,
        crate::identity_link::WEB_PLATFORM | DEVICE_PLATFORM
    )
}

/// The server key an enrolment challenge is minted and verified under. Same resolution order (env
/// pin → a file under the session dir → fresh per process) as every other web-side key, so it
/// inherits the same ops story and the same fail-CLOSED restart behaviour: after a restart an
/// in-flight enrolment page must be reloaded, and no enrolment is ever admitted on a challenge this
/// process cannot check.
fn enrol_key() -> &'static [u8; 32] {
    static KEY: std::sync::OnceLock<[u8; 32]> = std::sync::OnceLock::new();
    KEY.get_or_init(|| {
        crate::table_seats::resolve_process_key(
            "DREGGNET_WEB_DEVICE_KEY",
            "web-device-key.bin",
            "browser signing-key enrolments",
        )
    })
}

fn unix_now() -> u64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0)
}

/// A 32-byte public key in lowercase hex — the only shape an enrolment accepts.
fn is_pubkey_hex(candidate: &str) -> bool {
    candidate.len() == 64
        && candidate
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
}

// ─────────────────────────────────────────────────────────────────────────────
// The refusal taxonomy — one variant per gate that ran and said no
// ─────────────────────────────────────────────────────────────────────────────

/// Why an enrolment was refused. Nothing was recorded in any of them, and in every one of them the
/// player's 24 words were derived-and-wiped or never touched at all.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EnrolRefusal {
    /// ⚑ The request did not come from a page on this site. FIRST, ahead of everything, because an
    /// enrolment writes a durable record: a hostile page that could submit one would bind ITS OWN
    /// key as a device of this player, and every "signed" move that key then made would read as the
    /// player's own.
    NotFromOurPage,
    /// The browser presented no usable public key.
    MalformedDeviceKey,
    /// The enrolment page's challenge is missing, expired, or not one this server minted.
    StaleChallenge,
    /// The confirmation box was not ticked.
    NotConfirmed,
    /// The phrase did not validate — carries the which-check-failed sentence already rendered.
    BadPhrase(String),
    /// ⚑ Our OWN construction failed the shared verifier. Never a statement about the player.
    SelfCheckFailed,
    /// The append to the shared store failed (a read-only mount, a bad store directory).
    NotRecorded,
}

impl EnrolRefusal {
    fn http_status(&self) -> StatusCode {
        match self {
            EnrolRefusal::NotFromOurPage => StatusCode::FORBIDDEN,
            EnrolRefusal::StaleChallenge => StatusCode::FORBIDDEN,
            EnrolRefusal::MalformedDeviceKey
            | EnrolRefusal::NotConfirmed
            | EnrolRefusal::BadPhrase(_) => StatusCode::BAD_REQUEST,
            EnrolRefusal::SelfCheckFailed | EnrolRefusal::NotRecorded => {
                StatusCode::INTERNAL_SERVER_ERROR
            }
        }
    }

    /// The sentence a player reads. Every one begins "Refused:", names the check that failed in
    /// plain words, says that nothing was recorded, and gives one thing to do next — the three
    /// rules `dreggnet_offerings::refusal::audit_player_text` enforces.
    fn message(&self) -> String {
        match self {
            EnrolRefusal::NotFromOurPage => "Refused: this did not come from our page, so nothing \
                 was enrolled and your words were not used. Open the signing page here and try \
                 again. If something on another website submitted this for you, it was trying to \
                 make its own key able to play under your name."
                .to_string(),
            EnrolRefusal::MalformedDeviceKey => "Refused: this browser did not offer a usable \
                 signing key, so nothing was enrolled and your words were not used. Reload the page \
                 and try again. If it keeps happening, this browser is probably too old for the kind \
                 of key we use, and playing without one works exactly as before."
                .to_string(),
            EnrolRefusal::StaleChallenge => "Refused: this page had been open too long, so nothing \
                 was enrolled and your words were not used. Reload the page and do it again; the \
                 wait exists so a page left open on a shared machine stops being able to enrol \
                 anything."
                .to_string(),
            EnrolRefusal::NotConfirmed => "Refused: the confirmation box was not ticked, so nothing \
                 was enrolled and your words were not used. Tick it and try again."
                .to_string(),
            EnrolRefusal::BadPhrase(detail) => format!(
                "Refused: {detail} Nothing was enrolled and this browser's key was not registered. \
                 Check that one word and try again."
            ),
            EnrolRefusal::SelfCheckFailed => "Refused: this server built an enrolment that its own \
                 checker would not accept, so it recorded nothing. That is a fault on our side, not \
                 in what you did, and the server log names the cause."
                .to_string(),
            EnrolRefusal::NotRecorded => "Refused: the enrolment was proven but could not be \
                 written to the shared record, so nothing is enrolled and this browser still plays \
                 the ordinary way. That is on our side; the server log names the cause."
                .to_string(),
        }
    }
}

/// Say WHICH phrase check failed — the same three branches the restore box and the link box print,
/// so all three phrase boxes on the product teach the same thing.
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

// ─────────────────────────────────────────────────────────────────────────────
// State + mount
// ─────────────────────────────────────────────────────────────────────────────

/// The device door's state. Holds no player material — only where the shared link store lives.
pub struct DeviceKeyState {
    store_path: std::path::PathBuf,
}

impl DeviceKeyState {
    /// State over an explicit store path — the seam tests drive.
    pub fn new(store_path: std::path::PathBuf) -> Self {
        DeviceKeyState { store_path }
    }
}

/// **Mount the device door.** Additive: everything is under `/identity/device`, which overlaps
/// nothing. Always mounted, like the link door and for the same reason — the identity page links
/// here, and a link to a 404 teaches a player nothing.
pub fn device_key_router(state: Arc<DeviceKeyState>) -> Router {
    Router::new()
        .route("/identity/device", get(get_device).post(post_device))
        .route(
            "/identity/device/static/device-key.js",
            get(get_device_key_js),
        )
        .with_state(state)
}

/// The device door over the shared store path every dregg unit points at.
pub fn device_key_from_env() -> Router {
    device_key_router(Arc::new(DeviceKeyState::new(default_store_path())))
}

/// `GET /identity/device/static/device-key.js` — the signer, same-origin and version-frozen
/// in-repo. Served the way `/descent/play/static/actions.js` is: `include_str!`, no static-file
/// service, no third-party resolution, so what a player runs is what is in this tree.
async fn get_device_key_js() -> impl IntoResponse {
    (
        [(header::CONTENT_TYPE, "text/javascript; charset=utf-8")],
        include_str!("../assets/dregg-device-key.mjs"),
    )
}

// ─────────────────────────────────────────────────────────────────────────────
// ⚑ THE CEREMONY — pure over its clock and its store
// ─────────────────────────────────────────────────────────────────────────────

/// What a successful enrolment produced.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Enrolled {
    /// The browser key that may now sign as this human.
    pub device_pubkey_hex: String,
    /// The phrase's own key — the join key both now resolve through.
    pub root_pubkey_hex: String,
}

/// **Prove and record a device enrolment.** The complete gate order, and the only place a device
/// row is written:
///
/// 1. **the device key must be a real 32-byte key** → [`EnrolRefusal::MalformedDeviceKey`];
/// 2. **the challenge must be one this server minted and not yet expired** →
///    [`EnrolRefusal::StaleChallenge`]. Before the phrase is touched, so a stale page never costs a
///    phrase submission;
/// 3. **consent** → [`EnrolRefusal::NotConfirmed`], also before the derivation;
/// 4. **your half** — the 24 words derive the root key → [`EnrolRefusal::BadPhrase`];
/// 5. **sign** the canonical claim binding `(device platform, device key) → root`, with the root
///    key, through the SAME [`sign_link_claim`] the platform ceremony uses;
/// 6. **self-check** with the shared [`verify_link_claim`], so no record is written that the
///    independent verifier would reject;
/// 7. **record** one row. ⚑ Only ONE, unlike the platform ceremony: the `web` self-row that makes
///    the resolver agree about the root is written by the link ceremony and is not this module's to
///    duplicate — appending a second copy would be a same-second rebind of the root onto itself,
///    which is harmless today and is exactly the kind of harmless-today write that later becomes a
///    tie-break bug.
///
/// Every secret is wiped before returning.
fn prove_and_record(
    state: &DeviceKeyState,
    device_pubkey_hex: &str,
    raw_phrase: &str,
    chal: &str,
    confirmed: bool,
    now: u64,
) -> Result<Enrolled, EnrolRefusal> {
    // 1. A key we cannot verify signatures under is not a device.
    let device_pubkey_hex = device_pubkey_hex.trim().to_ascii_lowercase();
    if !is_pubkey_hex(&device_pubkey_hex) {
        return Err(EnrolRefusal::MalformedDeviceKey);
    }

    // 2. Freshness, before anything expensive and before the phrase.
    if challenge::verify(enrol_key(), chal, now).is_err() {
        return Err(EnrolRefusal::StaleChallenge);
    }

    // 3. Consent, still before the derivation, so a refusal costs no phrase submission.
    if !confirmed {
        return Err(EnrolRefusal::NotConfirmed);
    }

    // 4. YOUR HALF. The phrase is the authority; this browser's cookie is not consulted, so a
    //    device can be enrolled from a machine that has never seen this server.
    let mut phrase = normalize_typed_phrase(raw_phrase);
    let derived = derive_root_keypair(&phrase);
    phrase.zeroize();
    let (root_pubkey_hex, root_seed) =
        derived.map_err(|e| EnrolRefusal::BadPhrase(phrase_detail(&e)))?;

    // 5. The claim: the root key attests that this device key acts for it.
    let device_uid = short_tag(&device_pubkey_hex);
    let (root_pubkey, signature) = sign_link_claim(
        &root_seed,
        DEVICE_PLATFORM,
        &device_uid,
        &device_pubkey_hex,
        chal,
    )
    .map_err(|_| EnrolRefusal::SelfCheckFailed)?;
    drop(root_seed); // wiped by `Zeroizing`; explicit so the wipe point is visible.

    // 6. THE SELF-CHECK, on our own output, with the shared verifier.
    verify_link_claim(
        enrol_key(),
        DEVICE_PLATFORM,
        &device_uid,
        &device_pubkey_hex,
        &root_pubkey,
        chal,
        &signature,
        now,
    )
    .map_err(|_| EnrolRefusal::SelfCheckFailed)?;

    // 7. Record.
    FileLinkStore::new(&state.store_path)
        .record(&LinkRecord {
            root_pubkey_hex: root_pubkey_hex.clone(),
            platform: DEVICE_PLATFORM.to_string(),
            platform_uid: device_uid,
            custodial_pubkey_hex: device_pubkey_hex.clone(),
            verified_at: now,
        })
        .map_err(|_| EnrolRefusal::NotRecorded)?;

    Ok(Enrolled {
        device_pubkey_hex,
        root_pubkey_hex,
    })
}

// ─────────────────────────────────────────────────────────────────────────────
// Handlers
// ─────────────────────────────────────────────────────────────────────────────

/// The enrolment form.
#[derive(Debug, Clone, Deserialize)]
pub struct EnrolForm {
    /// The public half of the keypair this browser minted. Filled in by the page's script from
    /// `crypto.subtle`; never a key the server chose.
    pub device_pubkey_hex: String,
    /// The challenge this page was rendered with.
    pub challenge: String,
    /// The 24 words, however they were pasted.
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

/// `GET /identity/device` — what a device key is, what this browser currently has, and the form.
async fn get_device(State(state): State<Arc<DeviceKeyState>>, headers: HeaderMap) -> Response {
    let root = viewer_root(&headers);
    no_store(device_page(
        &state.store_path,
        root.as_deref(),
        challenge::issue(enrol_key(), unix_now(), ENROL_TTL_SECS),
        None,
        None,
    ))
}

/// `POST /identity/device` — enrol this browser's key.
async fn post_device(
    State(state): State<Arc<DeviceKeyState>>,
    headers: HeaderMap,
    Form(form): Form<EnrolForm>,
) -> Response {
    let root = viewer_root(&headers);
    let fresh = || challenge::issue(enrol_key(), unix_now(), ENROL_TTL_SECS);

    // GATE 0: our own page. Before the key is parsed, before the phrase is touched.
    if !seed_identity::same_origin_post(&headers) {
        tracing::warn!(
            "REFUSED a device enrolment that could not show it came from a page on this site — \
             nothing was derived and NO RECORD WAS WRITTEN. A cross-origin submit would otherwise \
             enrol an attacker-chosen key as a device of this player, and every move that key then \
             signed would read as theirs"
        );
        let message = EnrolRefusal::NotFromOurPage.message();
        return (
            EnrolRefusal::NotFromOurPage.http_status(),
            no_store(device_page(
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
        &form.device_pubkey_hex,
        &form.phrase,
        &form.challenge,
        form.understood.is_some(),
        unix_now(),
    ) {
        Ok(enrolled) => {
            // PUBLIC halves only: two public keys. Never the phrase.
            tracing::info!(
                device = %enrolled.device_pubkey_hex,
                root = %enrolled.root_pubkey_hex,
                "device signing key ENROLLED — turns signed by it land as a verified, user-held \
                 signature and resolve to the same human as the phrase's key"
            );
            let root = enrolled.root_pubkey_hex.clone();
            no_store(device_page(
                &state.store_path,
                Some(root.as_str()),
                fresh(),
                Some(&enrolled),
                None,
            ))
        }
        Err(refusal) => {
            let status = refusal.http_status();
            let message = refusal.message();
            (
                status,
                no_store(device_page(
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

const DEVICE_STYLE: &str = r##"<style>
.dk-state{margin:1.1rem 0;padding:.85rem 1rem;border:1px solid var(--line,#2a2a2a);
 border-left:3px solid rgba(140,160,220,.7);border-radius:0 4px 4px 0;background:rgba(255,255,255,.02);
 line-height:1.6}
.dk-state.ready{border-left-color:rgba(120,200,150,.75)}
.dk-key{font-family:ui-monospace,Menlo,monospace;font-size:.85rem;overflow-wrap:anywhere;opacity:.85}
.dk-form label{display:block;margin:1rem 0 .3rem;font-size:.8rem;letter-spacing:.1em;
 text-transform:uppercase;opacity:.7}
.dk-form textarea{width:100%;min-height:5.5rem;padding:.6rem .7rem;border:1px solid var(--line,#2a2a2a);
 border-radius:4px;background:rgba(0,0,0,.25);color:inherit;font-family:ui-monospace,Menlo,monospace;
 font-size:.88rem;line-height:1.6}
.dk-check{display:flex;gap:.55rem;align-items:flex-start;margin:1.1rem 0 .2rem;line-height:1.55}
.dk-check input{margin-top:.3rem;flex:none}
.dk-list{list-style:none;margin:1rem 0;padding:0;display:flex;flex-direction:column;gap:.5rem}
.dk-list li{padding:.7rem .85rem;border:1px solid var(--line,#2a2a2a);
 border-left:3px solid rgba(120,200,150,.7);border-radius:0 4px 4px 0;background:rgba(255,255,255,.02)}
.dk-list b{display:block;font-size:.95rem}
.dk-sep{margin:2rem 0;border:0;border-top:1px solid var(--line,#2a2a2a)}
</style>"##;

/// The one script on this page: mint-or-read the browser's key and put its public half in the form.
///
/// ⚑ It NEVER touches the phrase box, and it is worth being able to see that at a glance — the words
/// go where they always went, into an ordinary form POST, and this script's only reach into the DOM
/// is the hidden key field and the two status paragraphs.
const DEVICE_SCRIPT: &str = r##"<script type="module">
import { ensureDeviceKey, currentDeviceKey, deviceKeysSupported }
  from "/identity/device/static/device-key.js";
const field = document.getElementById("device-pubkey");
const state = document.getElementById("dk-state");
const submit = document.getElementById("dk-submit");
function say(text, ready){ if(state){ state.textContent = text;
  state.className = ready ? "dk-state ready" : "dk-state"; } }
(async () => {
  try {
    if (!(await deviceKeysSupported())) {
      say("This browser cannot hold a signing key of the kind we use, so your turns will keep " +
          "being recorded under your name without one. Everything still works; nothing here is " +
          "needed to play.", false);
      if (submit) submit.disabled = true;
      return;
    }
    const held = await currentDeviceKey();
    const key = held || await ensureDeviceKey();
    if (!key) { say("This browser could not make a signing key just now. Reload the page to try " +
                    "again; playing without one works exactly as before.", false);
                if (submit) submit.disabled = true; return; }
    if (field) field.value = key.publicKeyHex;
    say("This browser has made itself a signing key. It was made here and never sent anywhere: " +
        "the key that signs cannot be read by this page, by us, or by anything you paste. Enrol " +
        "it below to have your turns carry its signature.", true);
  } catch (e) {
    say("This browser could not make a signing key just now. Reload the page to try again; " +
        "playing without one works exactly as before.", false);
    if (submit) submit.disabled = true;
  }
})();
</script>"##;

/// The devices currently enrolled under a root, from the shared store.
fn devices_block(store_path: &std::path::Path, root_pubkey_hex: &str) -> String {
    let rows: Vec<LinkRecord> = FileLinkStore::new(store_path)
        .platforms_for_root(root_pubkey_hex)
        .unwrap_or_default()
        .into_iter()
        .filter(|r| r.platform == DEVICE_PLATFORM)
        .collect();
    if rows.is_empty() {
        return "<p class=\"prose\">No browser is enrolled to sign for this identity yet. That is \
                a perfectly ordinary state: turns you press are recorded under your name, which is \
                how playing in a browser has always worked here.</p>"
            .to_string();
    }
    let items: String = rows
        .iter()
        .map(|r| {
            format!(
                "<li><b>Browser {tag}</b><span class=\"dk-key\">{key}</span>\
                 <p class=\"prose\" style=\"margin:.4rem 0 0;font-size:.9rem\">Turns signed by this \
                 key are recorded as yours. Only the browser that made it can sign with it; we \
                 cannot, and neither can anyone holding your 24 words. \
                 <a href=\"/identity/unlink\">Remove this browser</a> if it is not one you \
                 use.</p></li>",
                tag = esc(&r.platform_uid),
                key = esc(&r.custodial_pubkey_hex),
            )
        })
        .collect();
    format!("<ul class=\"dk-list\">{items}</ul>")
}

/// The page.
fn device_page(
    store_path: &std::path::Path,
    root_pubkey_hex: Option<&str>,
    challenge: String,
    just_enrolled: Option<&Enrolled>,
    refusal: Option<&str>,
) -> String {
    let notice = match just_enrolled {
        Some(enrolled) => notice_html(Some(&format!(
            "Enrolled. Browser {} can now sign turns as the identity {}, and every turn it signs \
             carries a signature made on this device.",
            short_tag(&enrolled.device_pubkey_hex),
            short_tag(&enrolled.root_pubkey_hex),
        ))),
        None => notice_html(refusal),
    };
    let current = match root_pubkey_hex {
        Some(root) => format!(
            "<h2>Browsers enrolled for <span class=\"dk-key\">{tag}</span></h2>{list}",
            tag = esc(&short_tag(root)),
            list = devices_block(store_path, root),
        ),
        None => "<h2>No identity on this browser yet</h2>\
             <p class=\"prose\">You can still enrol from here: the form reads your 24 words, not \
             this browser's cookie. If you have not claimed an identity at all, \
             <a href=\"/identity\">start there</a>: a signing key signs <em>as</em> somebody, so \
             there has to be somebody first.</p>"
            .to_string(),
    };
    document_with_head(
        "Sign your turns · DreggNet",
        "",
        &format!("{DEVICE_STYLE}{}", crate::attribution::ATTRIBUTION_STYLE),
        &format!(
            "<main class=\"session\">\
             <header class=\"page-head\"><p class=\"eyebrow\">Identity · signing</p>\
             <h1>Let this browser sign for you</h1>\
             <p class=\"deck\">Turns you press are recorded under your name. With a signing key \
             they are recorded under your name <em>and</em> carry a signature we could not have \
             written ourselves.</p></header>{notice}\
             <h2>What changes, exactly</h2>\
             <p class=\"prose\">Today a turn you press here is <strong>attributed</strong>: this \
             page hands us the name you are signed in as and we take it at face value. That is not \
             a flaw in how you played; it is the ordinary way a browser plays, and every board \
             counts those turns. What it cannot do is prove that the person pressing the button was \
             you.</p>\
             <p class=\"prose\">A signing key changes that. Your browser makes one, here, in this \
             tab. The half that signs never leaves it: not to us, not into this page, not into \
             anything you could paste somewhere. From then on each turn you press is signed on this \
             machine and we check the signature before the move lands, so the record says \
             <strong>signed</strong> instead of attributed.</p>\
             <div class=\"dk-state\" id=\"dk-state\">Checking whether this browser can hold a \
             signing key…</div>\
             {current}\
             <hr class=\"dk-sep\">\
             <h2>Enrol this browser</h2>\
             <p class=\"prose\">Your 24 words sign a short statement that this browser's key is \
             allowed to play as you. That is the only thing they are used for here, and the same \
             thing happens to them as everywhere else on this site: they are turned into a key \
             inside this one request, used once, and every byte wiped before the answer goes \
             out.</p>\
             <form class=\"dk-form\" method=\"post\" action=\"/identity/device\">\
             <input type=\"hidden\" id=\"device-pubkey\" name=\"device_pubkey_hex\" value=\"\">\
             <input type=\"hidden\" name=\"challenge\" value=\"{challenge}\">\
             <label for=\"phrase\">Your 24 words</label>\
             <textarea id=\"phrase\" name=\"phrase\" rows=\"3\" autocomplete=\"off\" \
             spellcheck=\"false\" autocapitalize=\"none\" \
             placeholder=\"abandon ability able about …\"></textarea>\
             <label class=\"dk-check\"><input type=\"checkbox\" name=\"understood\" value=\"yes\">\
             <span>I am at this browser now, and I understand that clearing this browser's site \
             data removes its signing key. My 24 words still work everywhere; only this browser \
             would go back to playing the ordinary way.</span></label>\
             <div class=\"id-actions\" style=\"display:flex;gap:.6rem;flex-wrap:wrap;margin:1.1rem 0 0\">\
             <button class=\"btn btn-primary\" type=\"submit\" id=\"dk-submit\">Enrol this \
             browser</button>\
             <a class=\"btn btn-ghost\" href=\"/identity\">Back to your identity</a></div></form>\
             {honest}{script}</main>",
            notice = notice,
            current = current,
            challenge = esc(&challenge),
            honest = honest_block(),
            script = DEVICE_SCRIPT,
        ),
    )
}

/// The honest-limits block for this page. It must say the three things a player could otherwise
/// believe wrongly: that a device key is an account, that it protects the run rather than the name,
/// and that losing the browser loses something it does not.
fn honest_block() -> String {
    "<div class=\"id-honest\" style=\"margin:1.4rem 0 0;padding:.85rem 1rem;\
     border:1px solid var(--line,#2a2a2a);border-radius:4px;background:rgba(255,255,255,.015);\
     font-size:.9rem;line-height:1.6\">\
     <h3 style=\"margin:0 0 .45rem;font-size:.9rem;letter-spacing:.04em;text-transform:uppercase;\
     opacity:.7\">What a signing key is and is not</h3><dl>\
     <dt style=\"font-weight:600;margin-top:.6rem\">It is a device, not an identity.</dt>\
     <dd style=\"margin:.15rem 0 0;opacity:.85\">Your 24 words are still who you are. This key is a \
     browser you have said may play as you. Enrol as many browsers as you like; remove any of them \
     whenever you want. Losing this one costs you the ability to sign <em>from this browser</em> and \
     nothing else.</dd>\
     <dt style=\"font-weight:600;margin-top:.6rem\">We cannot sign with it, and neither can your \
     words.</dt>\
     <dd style=\"margin:.15rem 0 0;opacity:.85\">The key was made by this browser and stored in a \
     form the browser will use but will not hand back: not to us, not to this page's own scripts. \
     That is what makes a signature from it mean something we could not have produced. It also means \
     there is no recovering it: a new browser makes a new key and you enrol that one.</dd>\
     <dt style=\"font-weight:600;margin-top:.6rem\">It says who moved, not that the move was \
     legal.</dt>\
     <dd style=\"margin:.15rem 0 0;opacity:.85\">Whether a move was allowed is decided by the rules \
     and re-checked when anyone replays your session; that has always been true and does not depend \
     on any of this. A signature answers the other question, the one a name alone could never \
     answer.</dd>\
     <dt style=\"font-weight:600;margin-top:.6rem\">Your words still pass through us, once.</dt>\
     <dd style=\"margin:.15rem 0 0;opacity:.85\">Enrolling needs a signature by the key your words \
     derive, and that key exists only while the words are in hand. So this is the same trade \
     <a href=\"/identity\">restoring an identity</a> already makes, paid once per browser instead of \
     once per visit. Turning the words into a key inside your browser instead is a further step we \
     have not taken.</dd>\
     </dl></div>"
        .to_string()
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_sdk::mnemonic::generate_mnemonic;
    use dreggnet_offerings::refusal::audit_player_text;
    use dreggnet_offerings::{Action, SessionId, TurnSigner, verify_signed};
    use webauth_core::identity_resolve::RootResolver;

    const NOW: u64 = 1_790_000_000;

    fn tmp_store(tag: &str) -> std::path::PathBuf {
        let dir = std::env::temp_dir().join(format!(
            "dregg-device-key-{}-{tag}-{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        let _ = std::fs::remove_dir_all(&dir);
        dir.join("links.tsv")
    }

    /// A stand-in for the browser: a keypair the SERVER never sees the secret of. The real one is
    /// `crypto.subtle.generateKey`; what matters for the ceremony is that the enrolment is over a
    /// public key alone.
    fn a_browser_key(seed: u8) -> TurnSigner {
        TurnSigner::from_seed([seed; 32])
    }

    /// ⚑ THE WHOLE POINT, end to end: a browser-minted key, enrolled with a phrase, signs a turn
    /// that the offering verifier admits — and the two keys resolve to ONE human on the boards.
    #[test]
    fn an_enrolled_browser_key_signs_a_turn_that_verifies_and_joins_one_human() {
        let path = tmp_store("payoff");
        let state = DeviceKeyState::new(path.clone());
        let phrase = generate_mnemonic();
        let root = seed_identity::derive_pubkey_hex(&phrase).expect("a fresh phrase derives");
        let browser = a_browser_key(0x5a);
        let chal = challenge::issue(enrol_key(), NOW, ENROL_TTL_SECS);

        let enrolled =
            prove_and_record(&state, browser.pubkey_hex(), &phrase, &chal, true, NOW + 10)
                .expect("the enrolment proves");
        assert_eq!(enrolled.root_pubkey_hex, root);
        assert_eq!(enrolled.device_pubkey_hex, browser.pubkey_hex());
        assert_ne!(
            enrolled.device_pubkey_hex, root,
            "the device key is a SECOND key; nothing was merged and nothing was re-derived"
        );

        // The browser signs a turn the way the page does, and the offering verifier admits it as a
        // VERIFIED actor — this is the asserted→signed step, on the real verifier.
        let sid = SessionId::new("s-1");
        let signed = browser.sign(
            "dungeon",
            &sid,
            0,
            Action::new("press on", "choose", 3, true),
        );
        let actor =
            verify_signed("dungeon", &sid, 0, &signed).expect("the browser's turn verifies");
        assert_eq!(actor.0, browser.pubkey_hex());

        // …and the board sees one human, not two strangers.
        let resolver = RootResolver::from_store(&FileLinkStore::new(&path));
        assert_eq!(
            resolver.resolve(browser.pubkey_hex()),
            resolver.resolve(&root),
            "a device key and the phrase's key must resolve to ONE human"
        );
        let _ = std::fs::remove_dir_all(path.parent().expect("a temp dir"));
    }

    /// Every gate refuses, and every refusal leaves the record EMPTY. The order matters as much as
    /// the outcomes: a bad phrase must not be reachable before consent, because a player who has
    /// not consented should never have had their words derived at all.
    #[test]
    fn every_gate_refuses_and_records_nothing() {
        let path = tmp_store("gates");
        let state = DeviceKeyState::new(path.clone());
        let phrase = generate_mnemonic();
        let browser = a_browser_key(0x11);
        let chal = challenge::issue(enrol_key(), NOW, ENROL_TTL_SECS);

        // A key that is not 32 bytes of hex.
        for bad_key in ["", "abcd", &"z".repeat(64), &"ab".repeat(31)] {
            assert_eq!(
                prove_and_record(&state, bad_key, &phrase, &chal, true, NOW),
                Err(EnrolRefusal::MalformedDeviceKey)
            );
        }
        // A challenge this server never minted, and one long expired.
        assert_eq!(
            prove_and_record(&state, browser.pubkey_hex(), &phrase, "nope", true, NOW),
            Err(EnrolRefusal::StaleChallenge)
        );
        assert_eq!(
            prove_and_record(
                &state,
                browser.pubkey_hex(),
                &phrase,
                &chal,
                true,
                NOW + ENROL_TTL_SECS + 60
            ),
            Err(EnrolRefusal::StaleChallenge)
        );
        // No consent — and note this fires even with a PERFECT phrase, so the words are never
        // derived for somebody who did not tick the box.
        assert_eq!(
            prove_and_record(&state, browser.pubkey_hex(), &phrase, &chal, false, NOW),
            Err(EnrolRefusal::NotConfirmed)
        );
        // A phrase that does not validate, in all three ways a person actually breaks one.
        for bad in [
            "",
            "abandon ability able",
            &phrase.replace(' ', " xyzzyplugh "),
        ] {
            assert!(matches!(
                prove_and_record(&state, browser.pubkey_hex(), bad, &chal, true, NOW),
                Err(EnrolRefusal::BadPhrase(_))
            ));
        }

        // NOTHING was written by any of them.
        assert!(
            FileLinkStore::new(&path)
                .all()
                .unwrap_or_default()
                .is_empty(),
            "a refused enrolment must leave the shared record untouched"
        );
        let _ = std::fs::remove_dir_all(path.parent().expect("a temp dir"));
    }

    /// ⚑ THE COPY GATE, on the strings this module actually produces. Every refusal must name its
    /// failing check in plain words, say that nothing was recorded, and give one next action.
    #[test]
    fn every_refusal_passes_the_shared_copy_gate() {
        for refusal in [
            EnrolRefusal::NotFromOurPage,
            EnrolRefusal::MalformedDeviceKey,
            EnrolRefusal::StaleChallenge,
            EnrolRefusal::NotConfirmed,
            EnrolRefusal::BadPhrase(
                "all 24 words are real words, but the phrase's own checksum does not match, which \
                 almost always means ONE word is wrong or two are swapped."
                    .to_string(),
            ),
            EnrolRefusal::SelfCheckFailed,
            EnrolRefusal::NotRecorded,
        ] {
            let text = refusal.message();
            assert_eq!(
                audit_player_text(&text, true, true),
                Vec::new(),
                "a refusal this module ships fails the shared copy gate: {text}"
            );
            assert!(
                text.starts_with("Refused:"),
                "every refusal must read as a refusal: {text}"
            );
        }
    }

    /// A device row is SELF-HELD, and the flag that says so must not be the old `platform != web`
    /// spelling — which would have printed "an operator can derive this key" beside the one key
    /// nobody but the browser can produce.
    #[test]
    fn a_device_row_is_self_held_and_a_bot_row_is_not() {
        assert!(platform_is_self_held(DEVICE_PLATFORM));
        assert!(platform_is_self_held(crate::identity_link::WEB_PLATFORM));
        assert!(!platform_is_self_held("discord"));
        assert!(!platform_is_self_held("telegram"));
    }
}
