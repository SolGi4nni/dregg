//! **A player identity you can WRITE DOWN, driven through the real HTTP surface.**
//!
//! Every assertion here is over the actual axum routes (`ServiceExt::oneshot`, no network), and
//! every one has both polarities. The five things being proved, in the order a player meets them:
//!
//! 1. **The casual path SURVIVES.** A visitor with no cookie and no phrase still opens a game and
//!    lands a real turn, and `/identity` is an offer with a "just let me play" way out — never a
//!    wall. Nothing on the claim path is required to reach a game.
//! 2. **Claim is CONFIRM-ACTIVATED.** `POST /identity/claim` shows 24 words and sets NO cookie; only
//!    a confirm carrying the mac'd token *and* the ticked box installs the identity. An unticked box
//!    is a `400`, a hand-written token is a `403`, and neither sets a cookie — so a player who
//!    walked away is exactly who they were.
//! 3. **⚑ RECOVERY BRINGS THE GAMES BACK.** A phrase-backed player forges an item into their
//!    private RPG world; a fresh browser (nothing but the 24 words) restores the identity and the
//!    item is THERE. A *different* phrase does not see it. This is the whole point, and it is
//!    asserted over the real per-identity world isolation rather than on a label comparison.
//! 4. **⚑ THE SIGNED JOIN.** The keypair is re-derived here from the phrase using `dregg_sdk`
//!    DIRECTLY (never through the code under test), a `TurnSigner` built on it lands a genuinely
//!    signed turn on `/act-signed`, and the actor that route verifies to is byte-identical to the
//!    identity the claim cookie resolves to. One player, one name, whether they press a button or
//!    sign from a tool that holds their words.
//! 5. **The forgery tooth.** A public key is public. A cookie naming one, hand-written by somebody
//!    who read it off a page, must NOT act as that identity.
//! 6. **⚑ NOBODY ELSE MAY CHANGE THIS BROWSER'S IDENTITY.** The threat model here is not only theft.
//!    A hostile page can try to *implant* one: an ordinary cross-site form POST carrying **the
//!    attacker's own 24 words**, whose `303`'s `Set-Cookie` the browser honours (`SameSite=Lax`
//!    governs when a cookie is SENT, not whether we may set one). Every state-changing identity route
//!    refuses a request that cannot show it came from a page on this site — including one that says
//!    nothing at all — and a shown phrase can only be taken up by the browser it was shown to.

use std::sync::Arc;

use axum::body::Body;
use axum::http::{Request, StatusCode};
use dreggnet_offerings::{Action, DreggIdentity, SessionId, TurnSigner};
use dreggnet_web::{CatalogState, catalog_router, seed_identity};
use tower::ServiceExt; // oneshot

mod common;

// ═══════════════════════════════════════════════════════════════════════════════
// The harness
// ═══════════════════════════════════════════════════════════════════════════════

/// The catalog surface PLUS the identity door — the two routers a real deploy merges.
fn app() -> axum::Router {
    common::guard(
        catalog_router(Arc::new(CatalogState::new())).merge(seed_identity::identity_router()),
    )
}

async fn get_with_cookie(
    app: &axum::Router,
    uri: &str,
    cookie: Option<&str>,
) -> (StatusCode, String) {
    let mut builder = Request::builder().uri(uri);
    if let Some(cookie) = cookie {
        builder = builder.header("cookie", cookie);
    }
    let response = app
        .clone()
        .oneshot(builder.body(Body::empty()).unwrap())
        .await
        .unwrap();
    let status = response.status();
    let bytes = axum::body::to_bytes(response.into_body(), usize::MAX)
        .await
        .unwrap();
    (status, String::from_utf8_lossy(&bytes).to_string())
}

/// POST a form, returning the status, EVERY `Set-Cookie` header, and the body.
///
/// ⚑ **It presents `Sec-Fetch-Site: same-origin`, and that is not decoration.** Every
/// state-changing identity route now refuses a request that cannot show it came from a page on this
/// site ([`seed_identity::request_origin`]) — including one that says NOTHING, which is what a bare
/// `tower::oneshot` request is. Any test here that drops the header is asserting the refusal, not the
/// flow; [`post_form_from`] is the door for that.
async fn post_form(
    app: &axum::Router,
    uri: &str,
    body: &str,
    cookie: Option<&str>,
) -> (StatusCode, Vec<String>, String) {
    post_form_from(app, uri, body, cookie, &[("sec-fetch-site", "same-origin")]).await
}

/// [`post_form`] with the origin-stating headers spelled out — `&[]` is a request that states
/// nothing at all, which is exactly what a hostile page's auto-submitted form looks like to us.
async fn post_form_from(
    app: &axum::Router,
    uri: &str,
    body: &str,
    cookie: Option<&str>,
    origin_headers: &[(&str, &str)],
) -> (StatusCode, Vec<String>, String) {
    let mut builder = Request::builder()
        .method("POST")
        .uri(uri)
        .header("content-type", "application/x-www-form-urlencoded");
    for (name, value) in origin_headers {
        builder = builder.header(*name, *value);
    }
    if let Some(cookie) = cookie {
        builder = builder.header("cookie", cookie);
    }
    let response = app
        .clone()
        .oneshot(builder.body(Body::from(body.to_string())).unwrap())
        .await
        .unwrap();
    let status = response.status();
    let cookies: Vec<String> = response
        .headers()
        .get_all(axum::http::header::SET_COOKIE)
        .iter()
        .map(|value| value.to_str().unwrap().to_string())
        .collect();
    let bytes = axum::body::to_bytes(response.into_body(), usize::MAX)
        .await
        .unwrap();
    (status, cookies, String::from_utf8_lossy(&bytes).to_string())
}

/// The value a `Set-Cookie` line installs for `name` — `None` when the line CLEARS it (`Max-Age=0`).
fn cookie_value(cookies: &[String], name: &str) -> Option<String> {
    let prefix = format!("{name}=");
    cookies.iter().find_map(|line| {
        let rest = line.strip_prefix(&prefix)?;
        let value = rest.split(';').next().unwrap_or_default();
        (!value.is_empty()).then(|| value.to_string())
    })
}

/// Every word of the phrase off the one-time page's numbered grid (`<i>N</i>word`).
fn phrase_from_page(html: &str) -> String {
    let words: Vec<&str> = html
        .split("class=\"id-word\">")
        .skip(1)
        .filter_map(|chunk| chunk.split_once("</i>"))
        .map(|(_, rest)| rest.split('<').next().unwrap_or_default())
        .collect();
    assert_eq!(
        words.len(),
        24,
        "the one-time page must show exactly 24 words: {html}"
    );
    words.join(" ")
}

/// The mac'd confirm token off the one-time page's hidden field.
fn token_from_page(html: &str) -> String {
    html.split_once("name=\"token\" value=\"")
        .unwrap_or_else(|| panic!("the phrase page carried no confirm token: {html}"))
        .1
        .split_once('"')
        .unwrap()
        .0
        .to_string()
}

/// The `dregg_claim_pending` cookie line as a browser would send it back — the nonce the confirm
/// token is mac'd over. ⚑ A confirm is BOUND to the browser the phrase was shown to, so a test that
/// walks the claim flow has to carry this exactly as a browser does; dropping it is the refusal path
/// (`a_confirm_from_a_browser_that_was_not_shown_the_phrase_installs_nothing`).
fn pending_cookie(cookies: &[String]) -> String {
    let nonce = cookie_value(cookies, "dregg_claim_pending")
        .expect("showing a phrase installs the pending-confirm nonce");
    format!("dregg_claim_pending={nonce}")
}

/// Walk the whole claim flow: generate → confirm → the installed `dregg_user` cookie value plus
/// the phrase the player wrote down.
async fn claim_an_identity(app: &axum::Router) -> (String, String) {
    let (status, cookies, page) = post_form(app, "/identity/claim", "", None).await;
    assert_eq!(status, StatusCode::OK, "{page}");
    assert!(
        cookie_value(&cookies, "dregg_user").is_none()
            && cookie_value(&cookies, "dregg_claim").is_none(),
        "showing a phrase must install NO IDENTITY — it is not taken up until confirmed: {cookies:?}"
    );
    let pending = pending_cookie(&cookies);
    let phrase = phrase_from_page(&page);
    let token = token_from_page(&page);

    let (status, cookies, _) = post_form(
        app,
        "/identity/confirm",
        &format!("token={token}&saved=yes"),
        Some(&pending),
    )
    .await;
    assert_eq!(status, StatusCode::SEE_OTHER, "a confirmed claim redirects");
    let label = cookie_value(&cookies, "dregg_user").expect("confirm installs the acting cookie");
    assert_eq!(
        cookie_value(&cookies, "dregg_claim").as_deref(),
        Some(label.as_str()),
        "the durable claim cookie carries the same label"
    );
    (label, phrase)
}

/// Re-derive the signing key from a phrase using `dregg_sdk` DIRECTLY. Deliberately NOT through
/// `seed_identity::derive_pubkey_hex`: if the code under test derived wrongly, checking it against
/// itself would agree happily. This is the independent witness.
fn signer_from_phrase(phrase: &str) -> TurnSigner {
    let seed = dregg_sdk::mnemonic::mnemonic_to_seed(phrase, "").expect("the phrase validates");
    let (_public, secret) =
        dregg_sdk::mnemonic::derive_keypair(&seed, seed_identity::DERIVATION_PATH);
    TurnSigner::from_seed(secret)
}

fn hex_bytes(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

// ═══════════════════════════════════════════════════════════════════════════════
// 1. THE CASUAL PATH SURVIVES
// ═══════════════════════════════════════════════════════════════════════════════

/// **A visitor who just wants to click a game still can.** No cookie, no phrase, no visit to
/// `/identity` — a real turn lands. The identity door must be an upgrade, never a gate.
#[tokio::test]
async fn a_visitor_with_no_identity_at_all_still_plays() {
    let app = app();
    let (status, body) =
        common::post_act_anonymous(&app, "/offerings/craft/session/casual/act", "craft", 0).await;
    assert_eq!(status, StatusCode::OK, "{body}");
    assert!(
        body.contains("Turn committed"),
        "an anonymous visitor lands a real receipt with no identity ceremony: {body}"
    );
}

/// The offer reads as an offer: the page names the anonymous default, gives a way past it, states
/// the stakes at GAME size (a record, not money), and never claims a safety it does not have.
#[tokio::test]
async fn the_identity_page_offers_rather_than_demands() {
    let app = app();
    let (status, page) = get_with_cookie(&app, "/identity", None).await;
    assert_eq!(status, StatusCode::OK);

    // A way straight to a game, from the page itself.
    assert!(
        page.contains("just let me play") && page.contains("/offerings"),
        "the page must offer a way past it: {page}"
    );
    // The stakes, at their real size — and explicitly NOT wallet-grade fear.
    assert!(page.contains("No money is attached"), "{page}");
    assert!(page.contains("game history"), "{page}");
    assert!(
        page.contains("we cannot recover it for you"),
        "the one honest hard limit must be stated: {page}"
    );
    // The three rungs. ⚑ Rung 3 (cross-platform linking) USED to say "not wired to this page yet";
    // `/identity/link` now exists, so the page must offer it — but only as the PLAIN version, whose
    // record the operator can read. Both halves are asserted, because swapping one over-claim for
    // another (silently implying the private version shipped) is the same wound.
    assert!(page.contains("Linked accounts"), "{page}");
    assert!(
        page.contains("/identity/link"),
        "rung 3 must point at the door that now exists: {page}"
    );
    assert!(
        !page.contains("not wired to this page yet"),
        "the stale 'not wired' sentence survived into a page that now links: {page}"
    );
    assert!(
        page.contains("without</em> revealing which accounts")
            || page.contains("revealing which accounts"),
        "the page must still say the PRIVATE version is not what it does: {page}"
    );
    // ⚑ The security note, in the page a player actually reads — not only in a doc comment.
    assert!(page.contains("HttpOnly"), "{page}");
    assert!(
        page.contains("localStorage"),
        "the rejected alternative and WHY must be on the page: {page}"
    );
    assert!(
        page.contains("not signed by it") || page.contains("is not a signature"),
        "the page must not imply a browser turn is signed: {page}"
    );
}

// ═══════════════════════════════════════════════════════════════════════════════
// 2. CLAIM IS CONFIRM-ACTIVATED
// ═══════════════════════════════════════════════════════════════════════════════

/// The one-time page shows 24 words and installs NOTHING; the confirm is what makes it yours, and
/// the resulting page names the identity.
#[tokio::test]
async fn the_phrase_is_shown_once_and_the_confirm_is_what_activates_it() {
    let app = app();
    let (status, cookies, page) = post_form(&app, "/identity/claim", "", None).await;
    assert_eq!(status, StatusCode::OK);
    // ⚑ NO IDENTITY before confirmation. The one cookie a claim DOES set is the pending-confirm
    // nonce, which names nobody: it is what binds the shown phrase to this browser.
    assert!(
        cookie_value(&cookies, "dregg_user").is_none()
            && cookie_value(&cookies, "dregg_claim").is_none(),
        "no identity before confirmation: {cookies:?}"
    );
    let pending = pending_cookie(&cookies);
    // A phrase page must never be cached or replayed to another browser.
    assert!(page.contains("Write these 24 words down"), "{page}");
    let phrase = phrase_from_page(&page);
    assert_eq!(phrase.split_whitespace().count(), 24);
    // The plain one-line copy is the same words (a player who copies either gets the same identity).
    assert!(
        page.contains(&phrase),
        "the one-line copy must match: {page}"
    );
    // The page states that walking away costs nothing.
    assert!(page.contains("nothing has changed"), "{page}");

    let token = token_from_page(&page);
    let (status, cookies, _) = post_form(
        &app,
        "/identity/confirm",
        &format!("token={token}&saved=yes"),
        Some(&pending),
    )
    .await;
    assert_eq!(status, StatusCode::SEE_OTHER);
    let label = cookie_value(&cookies, "dregg_user").expect("the claim installs");

    // The label names the public key those words derive, and the identity IS that key.
    let expected = seed_identity::derive_pubkey_hex(&phrase).expect("valid");
    assert_eq!(
        seed_identity::parse_claim_label(&label).as_deref(),
        Some(expected.as_str())
    );
    assert_eq!(
        seed_identity::resolve_identity(&label),
        DreggIdentity(expected.clone()),
        "the identity is the PUBLIC KEY, not a hash of a cookie"
    );

    // …and the page now says who you are, by short tag, without reprinting the phrase.
    let (status, page) =
        get_with_cookie(&app, "/identity", Some(&format!("dregg_claim={label}"))).await;
    assert_eq!(status, StatusCode::OK);
    assert!(
        page.contains(&seed_identity::short_tag(&expected)),
        "{page}"
    );
    assert!(page.contains(&expected), "the full public name is shown");
    // The phrase must never be shown a second time — it was never stored, so it CANNOT be. Checked
    // as the whole phrase plus the absence of the word grid: individual BIP39 words are ordinary
    // English ("act", "able", "game") and do occur in the page's own prose, so a per-word check
    // would be a false alarm rather than a tooth.
    assert!(
        !page.contains(&phrase),
        "the phrase reappeared on a later page: {page}"
    );
    assert!(
        !page.contains("class=\"id-word\""),
        "only the one-time page may render the word grid: {page}"
    );
    assert!(
        page.contains("We cannot show them again"),
        "the page must say why it cannot re-show them: {page}"
    );
}

/// **Both refusal polarities of the confirm, and NEITHER installs anything.** An unticked box is a
/// `400`; a token nobody minted here is a `403`.
#[tokio::test]
async fn an_unconfirmed_or_forged_claim_installs_nothing() {
    let app = app();
    let (_s, claim_cookies, page) = post_form(&app, "/identity/claim", "", None).await;
    let pending = pending_cookie(&claim_cookies);
    let token = token_from_page(&page);

    // The box was not ticked. ⚑ The pending nonce IS carried, so this is genuinely the tick-box gate
    // refusing and not the browser-binding gate refusing first.
    let (status, cookies, body) = post_form(
        &app,
        "/identity/confirm",
        &format!("token={token}"),
        Some(&pending),
    )
    .await;
    assert_eq!(status, StatusCode::BAD_REQUEST);
    assert!(cookies.is_empty(), "nothing installed: {cookies:?}");
    assert!(body.contains("was not ticked"), "{body}");

    // A hand-written token for a real public key — the shape an attacker who read a key off a page
    // would try. Refused, because only this server can mac a label.
    let victim =
        seed_identity::derive_pubkey_hex(&dregg_sdk::mnemonic::generate_mnemonic()).expect("valid");
    for forged in [
        format!("dregg-id-{victim}.00000000000000000000000000000000"),
        format!("dregg-id-{victim}"),
        victim.clone(),
    ] {
        let (status, cookies, _) = post_form(
            &app,
            "/identity/confirm",
            &format!("token={forged}&saved=yes"),
            None,
        )
        .await;
        assert_eq!(
            status,
            StatusCode::FORBIDDEN,
            "forged token admitted: {forged}"
        );
        assert!(
            cookies.is_empty(),
            "a forged token installed a cookie: {cookies:?}"
        );
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// 2b. ⚑ NOBODY ELSE MAY CHANGE THIS BROWSER'S IDENTITY
// ═══════════════════════════════════════════════════════════════════════════════

/// **⚑ LOGIN-CSRF / IDENTITY FIXATION, over the live routes.**
///
/// The attack: a hostile page auto-submits an ordinary `application/x-www-form-urlencoded` form to
/// `POST /identity/restore` carrying **the attacker's own 24 words**. No JS privilege, no preflight,
/// and the `303`'s `Set-Cookie` is honoured — `SameSite=Lax` governs when a cookie is later SENT,
/// never whether the origin server may set one on its own response to a top-level navigation. The
/// victim's browser is silently switched onto an identity the attacker holds the phrase to, and every
/// run, receipt and relic afterwards files under it.
///
/// Every state-changing identity route must refuse, in every shape the request can arrive in — and
/// ⚑ INCLUDING the shape that says NOTHING about where it came from, because an absent check refuses.
/// The polarity that makes this non-vacuous is at the bottom: the identical body WITH a same-origin
/// statement restores fine, so this is the origin gate firing and not a broken request.
#[tokio::test]
async fn a_cross_origin_post_cannot_install_restore_or_release_an_identity() {
    let app = app();
    // A real, valid phrase — the attacker's own. Nothing here is malformed.
    let phrase = dregg_sdk::mnemonic::generate_mnemonic();
    let body = format!("phrase={}", phrase.replace(' ', "+"));

    for origin_headers in [
        // The attack, as a browser reports it.
        vec![("sec-fetch-site", "cross-site")],
        // A sibling subdomain is not us either.
        vec![("sec-fetch-site", "same-site")],
        // No initiating context at all.
        vec![("sec-fetch-site", "none")],
        // An older client, with a foreign Origin against our host.
        vec![("host", "play.example"), ("origin", "https://evil.example")],
        vec![
            ("host", "play.example"),
            ("referer", "https://evil.example/attack"),
        ],
        // ⚑ THE FAIL-OPEN SHAPE: nothing stated at all.
        vec![],
    ] {
        for (uri, form) in [
            ("/identity/restore", body.as_str()),
            ("/identity/claim", ""),
            ("/identity/release", "understood=yes"),
            ("/identity/confirm", "token=whatever&saved=yes"),
        ] {
            let (status, cookies, page) =
                post_form_from(&app, uri, form, None, &origin_headers).await;
            assert_eq!(
                status,
                StatusCode::FORBIDDEN,
                "⚑ {uri} honoured a request from {origin_headers:?}: {page}"
            );
            assert!(
                cookies.is_empty(),
                "⚑ {uri} set a cookie for a request from {origin_headers:?}: {cookies:?}"
            );
            // The player is told what happened and what to do — not which header refused them.
            assert!(
                page.contains("did not come from our page"),
                "the refusal must say what happened: {page}"
            );
            for machinery in ["Sec-Fetch", "CSRF"] {
                assert!(
                    !page.contains(machinery),
                    "the refusal names machinery at a player ({machinery}): {page}"
                );
            }
        }
    }

    // ⚑ NON-VACUOUS: the SAME body, from our own page, restores.
    let (status, cookies, page) = post_form(&app, "/identity/restore", &body, None).await;
    assert_eq!(status, StatusCode::SEE_OTHER, "{page}");
    let installed = cookie_value(&cookies, "dregg_user").expect("our own page still restores");
    assert_eq!(
        seed_identity::parse_claim_label(&installed).as_deref(),
        seed_identity::derive_pubkey_hex(&phrase).ok().as_deref(),
        "the legitimate flow must be untouched by the gate"
    );
}

/// **The link ceremony's gate 0.** A `POST /identity/link` that cannot show where it came from is
/// refused with `403 NotFromOurPage` before the code is parsed, before the phrase is touched and
/// before any nonce could be spent — so a cross-origin submit cannot bind an attacker-chosen account
/// to this browser's identity, which matters more here than anywhere else because there is no
/// un-link door.
///
/// The polarity is asserted on WHICH refusal fired rather than on a status, because which later gate
/// a same-origin request lands on depends on whether this machine's environment carries a platform
/// secret — and a test whose green is a function of the box is not a test.
#[tokio::test]
async fn a_cross_origin_link_post_is_refused_before_any_other_gate() {
    let app = common::guard(dreggnet_web::identity_link::identity_link_from_env());
    let form = "code=1234567:whatever.abc&phrase=abandon+ability&mine=yes";

    let (status, _cookies, page) = post_form_from(&app, "/identity/link", form, None, &[]).await;
    assert_eq!(
        status,
        StatusCode::FORBIDDEN,
        "a request stating no origin must be refused by gate 0: {page}"
    );
    assert!(page.contains("did not come from our page"), "{page}");
    assert!(
        page.contains("your code was not spent"),
        "a foreign request must cost the player nothing: {page}"
    );

    // …and from our own page the request reaches the LATER gates instead — WHICHEVER one applies
    // here, since that depends on whether this machine's environment carries a platform secret.
    // Asserted on the refusal's identity rather than on its status, so this test cannot become a
    // function of the box it runs on.
    let (_status, _cookies, page) = post_form(&app, "/identity/link", form, None).await;
    assert!(
        !page.contains("did not come from our page"),
        "gate 0 fired on our own page: {page}"
    );
}

/// ⚑ **A PHRASE CAN ONLY BE TAKEN UP BY THE BROWSER IT WAS SHOWN TO.** The confirm token is mac'd
/// over a nonce that leaves only in the phrase page's own cookie, so a token read off somebody else's
/// screen — or a `dregg-id-…` label lifted out of a `?user=` URL — cannot be POSTed to
/// `/identity/confirm` by a different browser and installed as a year-long cookie.
#[tokio::test]
async fn a_confirm_from_a_browser_that_was_not_shown_the_phrase_installs_nothing() {
    let app = app();
    let (_status, claim_cookies, page) = post_form(&app, "/identity/claim", "", None).await;
    let token = token_from_page(&page);
    let phrase = phrase_from_page(&page);
    let key = seed_identity::derive_pubkey_hex(&phrase).expect("valid");

    // A second browser, holding the genuine token and nothing else.
    let (status, cookies, body) = post_form(
        &app,
        "/identity/confirm",
        &format!("token={token}&saved=yes"),
        None,
    )
    .await;
    assert_eq!(status, StatusCode::FORBIDDEN, "{body}");
    assert!(cookies.is_empty(), "⚑ a bound token installed: {cookies:?}");
    assert!(body.contains("cannot make that confirmation"), "{body}");

    // …and holding a mac-valid CLAIM LABEL for that key gets it no further: a label is not a token.
    let (status, cookies, _) = post_form(
        &app,
        "/identity/confirm",
        &format!("token={}&saved=yes", seed_identity::claim_label(&key)),
        None,
    )
    .await;
    assert_eq!(status, StatusCode::FORBIDDEN);
    assert!(cookies.is_empty(), "{cookies:?}");

    // ⚑ NON-VACUOUS: the browser that WAS shown the phrase confirms.
    let (status, cookies, _) = post_form(
        &app,
        "/identity/confirm",
        &format!("token={token}&saved=yes"),
        Some(&pending_cookie(&claim_cookies)),
    )
    .await;
    assert_eq!(status, StatusCode::SEE_OTHER);
    let label = cookie_value(&cookies, "dregg_user").expect("the shown browser confirms");
    assert_eq!(
        seed_identity::parse_claim_label(&label).as_deref(),
        Some(key.as_str())
    );
    // The nonce is SPENT: the same token cannot be confirmed a second time on that machine.
    assert!(
        cookies
            .iter()
            .any(|line| line.starts_with("dregg_claim_pending=") && line.contains("Max-Age=0")),
        "the pending nonce must be cleared on a successful confirm: {cookies:?}"
    );
}

/// A mistyped word is refused with a reason a person holding paper can act on, and the restore
/// changes nothing.
#[tokio::test]
async fn a_mistyped_phrase_is_refused_with_a_usable_reason() {
    let app = app();

    let (status, cookies, body) = post_form(
        &app,
        "/identity/restore",
        "phrase=abandon+ability+able",
        None,
    )
    .await;
    assert_eq!(status, StatusCode::BAD_REQUEST);
    assert!(cookies.is_empty(), "nothing installed on a bad phrase");
    assert!(body.contains("that is 3 words"), "{body}");

    let (_s, _c, page) = post_form(&app, "/identity/claim", "", None).await;
    let phrase = phrase_from_page(&page);
    let mut words: Vec<String> = phrase.split_whitespace().map(str::to_string).collect();
    words[7] = if words[7] == "zoo" { "zone" } else { "zoo" }.to_string();
    let (status, cookies, body) = post_form(
        &app,
        "/identity/restore",
        &format!("phrase={}", words.join("+")),
        None,
    )
    .await;
    assert_eq!(status, StatusCode::BAD_REQUEST);
    assert!(cookies.is_empty());
    assert!(
        body.contains("checksum") && body.contains("ONE word is wrong"),
        "the reason must be actionable: {body}"
    );

    // An unknown word names the word.
    words[7] = "xyzzyplugh".to_string();
    let (status, _c, body) = post_form(
        &app,
        "/identity/restore",
        &format!("phrase={}", words.join("+")),
        None,
    )
    .await;
    assert_eq!(status, StatusCode::BAD_REQUEST);
    assert!(body.contains("xyzzyplugh"), "{body}");
}

// ═══════════════════════════════════════════════════════════════════════════════
// 3. ⚑ RECOVERY BRINGS THE GAMES BACK
// ═══════════════════════════════════════════════════════════════════════════════

/// **THE PAYOFF, over the real per-identity worlds.** A claimed player forges a Greatblade into
/// their own RPG world. A fresh browser carrying nothing but the 24 words restores the identity —
/// and the Greatblade is on its inventory. A DIFFERENT phrase's browser sees an empty shelf, so the
/// match is the identity and not a shared world.
#[tokio::test]
async fn restoring_a_phrase_brings_the_prior_games_back() {
    let app = app();
    let (label, phrase) = claim_an_identity(&app).await;

    // Play as the claimed identity: forge the bench's Greatblade into MY world.
    let (status, body) = common::post_act_with_cookie(
        &app,
        "/offerings/craft/session/primary/act",
        "craft",
        0,
        &format!("dregg_user={label}"),
    )
    .await;
    assert_eq!(status, StatusCode::OK, "{body}");
    assert!(body.contains("Turn committed"), "the forge lands: {body}");

    let (status, mine) = get_with_cookie(
        &app,
        "/offerings/inventory/session/primary",
        Some(&format!("dregg_user={label}")),
    )
    .await;
    assert_eq!(status, StatusCode::OK);
    assert!(mine.contains("Greatblade"), "it is on my own shelf: {mine}");

    // ── A FRESH BROWSER. It carries no cookie at all; the ONLY thing crossing is the 24 words. ──
    let (status, cookies, _) = post_form(
        &app,
        "/identity/restore",
        &format!("phrase={}", phrase.replace(' ', "+")),
        None,
    )
    .await;
    assert_eq!(status, StatusCode::SEE_OTHER, "a valid phrase restores");
    let restored = cookie_value(&cookies, "dregg_user").expect("restore installs the identity");
    assert_eq!(
        restored, label,
        "the same words name the same identity — recovery, not a new player"
    );

    let (status, recovered) = get_with_cookie(
        &app,
        "/offerings/inventory/session/primary",
        Some(&format!("dregg_user={restored}")),
    )
    .await;
    assert_eq!(status, StatusCode::OK);
    assert!(
        recovered.contains("Greatblade"),
        "⚑ the recovered identity holds the item it forged before: {recovered}"
    );

    // ── THE OTHER POLARITY: a different phrase is a different person, empty shelf. ──
    let (other_label, other_phrase) = claim_an_identity(&app).await;
    assert_ne!(other_phrase, phrase);
    assert_ne!(other_label, label);
    let (status, stranger) = get_with_cookie(
        &app,
        "/offerings/inventory/session/primary",
        Some(&format!("dregg_user={other_label}")),
    )
    .await;
    assert_eq!(status, StatusCode::OK);
    assert!(
        !stranger.contains("Greatblade"),
        "a different phrase must not inherit somebody else's shelf: {stranger}"
    );
}

/// Releasing a browser clears BOTH cookies and does not destroy the identity: the same words
/// restore it. And the confirmation box is required, so nobody signs themselves out by a stray
/// click while their phrase is in a drawer somewhere.
#[tokio::test]
async fn releasing_a_browser_is_a_logout_not_a_deletion() {
    let app = app();
    let (label, phrase) = claim_an_identity(&app).await;
    let cookie = format!("dregg_claim={label}; dregg_user={label}");

    // Unticked → refused, still claimed.
    let (status, cookies, body) = post_form(&app, "/identity/release", "", Some(&cookie)).await;
    assert_eq!(status, StatusCode::BAD_REQUEST);
    assert!(cookies.is_empty(), "{cookies:?}");
    assert!(body.contains("confirmation box"), "{body}");

    // Ticked → both cookies cleared.
    let (status, cookies, _) =
        post_form(&app, "/identity/release", "understood=yes", Some(&cookie)).await;
    assert_eq!(status, StatusCode::SEE_OTHER);
    assert!(
        cookie_value(&cookies, "dregg_user").is_none(),
        "{cookies:?}"
    );
    assert!(
        cookie_value(&cookies, "dregg_claim").is_none(),
        "{cookies:?}"
    );
    assert_eq!(cookies.len(), 2, "both cookies are addressed: {cookies:?}");

    // The identity itself is untouched — the words still name it.
    let (status, cookies, _) = post_form(
        &app,
        "/identity/restore",
        &format!("phrase={}", phrase.replace(' ', "+")),
        None,
    )
    .await;
    assert_eq!(status, StatusCode::SEE_OTHER);
    assert_eq!(
        cookie_value(&cookies, "dregg_user").as_deref(),
        Some(label.as_str())
    );
}

// ═══════════════════════════════════════════════════════════════════════════════
// 4. ⚑ THE SIGNED JOIN — one player, one name, both paths
// ═══════════════════════════════════════════════════════════════════════════════

/// **The identity the browser shows and the identity `/act-signed` VERIFIES are the same bytes.**
///
/// The keypair is re-derived here from the phrase through `dregg_sdk` directly, a real Ed25519
/// signature is produced over the canonical turn message, and the live signed route admits it —
/// naming an actor equal to the claimed identity. That is what makes a phrase useful beyond a name:
/// a tool holding it can act as you with a genuine signature, on the same identity your browser
/// plays under.
#[tokio::test]
async fn a_phrase_signs_turns_as_the_very_identity_the_browser_claims() {
    let app = app();
    let (label, phrase) = claim_an_identity(&app).await;
    let claimed = seed_identity::resolve_identity(&label);

    // The independent witness: dregg_sdk, at the CLI's derivation path.
    let signer = signer_from_phrase(&phrase);
    assert_eq!(
        signer.identity(),
        claimed,
        "⚑ the phrase's signing key and the claimed identity must be ONE DreggIdentity"
    );

    // A real signed turn on `craft` — an UNSPINED offering, so this exercises the legacy signed
    // path (`advance_signed_attributed`) rather than the game-authority envelope, which
    // `tests/act_signed.rs` already covers. `craft` is also a per-identity RPG key, which makes the
    // read-back below the strongest form of the join: a turn SIGNED by a tool holding the phrase
    // and a page read carrying only the cookie land in ONE world.
    let sid = SessionId::new("primary");
    let action = Action::new("craft", "craft", 0, true);
    let sa = signer.sign("craft", &sid, 0, action);
    let wire = serde_json::json!({
        "action": {
            "label": sa.action.label,
            "turn": sa.action.turn,
            "arg": sa.action.arg,
            "enabled": sa.action.enabled,
            "text": sa.action.text,
        },
        "actor_pubkey_hex": sa.actor_pubkey_hex,
        "counter": 0,
        "signature_hex": hex_bytes(&sa.signature),
    })
    .to_string();

    let response = app
        .clone()
        .oneshot(
            Request::builder()
                .method("POST")
                .uri("/offerings/craft/session/primary/act-signed")
                .header("content-type", "application/json")
                .body(Body::from(wire))
                .unwrap(),
        )
        .await
        .unwrap();
    let status = response.status();
    let bytes = axum::body::to_bytes(response.into_body(), usize::MAX)
        .await
        .unwrap();
    let body = String::from_utf8_lossy(&bytes).to_string();
    assert_eq!(
        status,
        StatusCode::OK,
        "the signed turn is admitted: {body}"
    );
    assert!(
        body.contains("Turn committed"),
        "the signed turn really landed: {body}"
    );
    assert!(
        body.contains(claimed.as_str()),
        "the VERIFIED actor is the claimed identity, named in the response: {body}"
    );

    // ⚑ THE JOIN, OBSERVED: the item that SIGNED turn forged is on the shelf the BROWSER sees when
    // it presents only its claim cookie. One player, two paths, one world.
    let (status, shelf) = get_with_cookie(
        &app,
        "/offerings/inventory/session/primary",
        Some(&format!("dregg_user={label}")),
    )
    .await;
    assert_eq!(status, StatusCode::OK);
    assert!(
        shelf.contains("Greatblade"),
        "a signed turn and a cookie read must reach ONE world: {shelf}"
    );

    // The other polarity: a DIFFERENT key's signature does not reach that world.
    let stranger = TurnSigner::from_seed([200u8; 32]);
    assert_ne!(stranger.identity(), claimed);
    let (status, stranger_shelf) = get_with_cookie(
        &app,
        "/offerings/inventory/session/primary",
        Some(&format!(
            "dregg_user={}",
            seed_identity::claim_label(stranger.pubkey_hex())
        )),
    )
    .await;
    assert_eq!(status, StatusCode::OK);
    assert!(
        !stranger_shelf.contains("Greatblade"),
        "another key must not see this identity's shelf: {stranger_shelf}"
    );
}

/// The derivation path is a cross-surface contract with the CLI. If this constant ever drifts, a
/// phrase claimed in the browser stops reproducing `dregg id`'s key and the identity silently
/// splits — so the constant is pinned here rather than trusted.
#[tokio::test]
async fn the_derivation_path_matches_the_cli() {
    assert_eq!(
        seed_identity::DERIVATION_PATH,
        "dregg/0",
        "cli/src/commands/id.rs pins DERIVATION_PATH = \"dregg/0\"; they must agree"
    );
    // And the whole pipeline agrees with the SDK, computed independently.
    let phrase = dregg_sdk::mnemonic::generate_mnemonic();
    let seed = dregg_sdk::mnemonic::mnemonic_to_seed(&phrase, "").unwrap();
    let (public, _secret) = dregg_sdk::mnemonic::derive_keypair(&seed, "dregg/0");
    assert_eq!(
        seed_identity::derive_pubkey_hex(&phrase).unwrap(),
        hex_bytes(&public)
    );
}

// ═══════════════════════════════════════════════════════════════════════════════
// 5. THE FORGERY TOOTH — over the live surface
// ═══════════════════════════════════════════════════════════════════════════════

/// **A public key read off a page is not a login.** A stranger sets their own cookie to a
/// hand-written `dregg-id-<victim>` label; the surface must NOT treat them as the victim. It falls
/// back to the historical `blake3(label)` derivation, which is a different, harmless pseudonym — so
/// the stranger gets an empty shelf, not the victim's.
#[tokio::test]
async fn a_hand_written_label_for_a_public_key_does_not_become_that_player() {
    let app = app();
    let (label, phrase) = claim_an_identity(&app).await;
    let victim_key = seed_identity::derive_pubkey_hex(&phrase).expect("valid");

    // The victim forges something identifying.
    let (status, _) = common::post_act_with_cookie(
        &app,
        "/offerings/craft/session/primary/act",
        "craft",
        0,
        &format!("dregg_user={label}"),
    )
    .await;
    assert_eq!(status, StatusCode::OK);

    // Every label a stranger can write down knowing only the (public!) key.
    for forged in [
        format!("dregg-id-{victim_key}"),
        format!("dregg-id-{victim_key}.00000000000000000000000000000000"),
        format!("dregg-id-{victim_key}.deadbeefdeadbeefdeadbeefdeadbeef"),
        victim_key.clone(),
    ] {
        assert_eq!(
            seed_identity::parse_claim_label(&forged),
            None,
            "a hand-written label verified: {forged}"
        );
        let (status, shelf) = get_with_cookie(
            &app,
            "/offerings/inventory/session/primary",
            Some(&format!("dregg_user={forged}")),
        )
        .await;
        assert_eq!(status, StatusCode::OK);
        assert!(
            !shelf.contains("Greatblade"),
            "⚑ a hand-written label reached the victim's world: {forged}\n{shelf}"
        );
    }

    // …and the genuine label still does.
    let (status, mine) = get_with_cookie(
        &app,
        "/offerings/inventory/session/primary",
        Some(&format!("dregg_user={label}")),
    )
    .await;
    assert_eq!(status, StatusCode::OK);
    assert!(
        mine.contains("Greatblade"),
        "the real holder still reaches their own world: {mine}"
    );
}
