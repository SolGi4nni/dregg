//! **Shared support for the web integration suite — and the structural close of the silent-`/act` class.**
//!
//! ## The class this module exists to kill
//!
//! Since the common game-session spine landed, `POST /offerings/{key}/session/{id}/act` on a
//! SPINED key ([`dreggnet_catalog::game_spine::game_kind`] — `descent`, `descent-campaign`,
//! `dungeon`, `bazaar`, `dark-pool`, `private-raid`, `council`, `market`, `tug`, `automatafl`)
//! requires the four route-authority fields the server itself stamps into the play form:
//! `game_host_incarnation`, `game_session_generation`, `game_expected_pre_head`, `game_form_token`.
//! A test posting a bare `turn=&arg=` is answered `409 invalid game reference` and its move NEVER
//! REACHES THE EXECUTOR.
//!
//! Whether that shows up is pure luck of assertion polarity. `assert!(body.contains("Turn
//! committed"))` goes red; `assert!(!body.contains("YOUR sealed move"))` goes GREEN having checked
//! nothing at all. The second shape is the dangerous one: a fog/isolation/refusal property that
//! "passes" because the turn it was supposed to observe never happened.
//!
//! ## The two halves of the repair
//!
//! 1. [`post_act`] / [`authority_suffix`] read the authority off the viewer's own live page,
//!    exactly as their browser would, so a test's move actually lands.
//! 2. [`guard`] wraps a test router in a tripwire that PANICS when any `…/act` POST is refused for
//!    a MISSING authority. A test that silently stopped presenting one can no longer coast to a
//!    vacuous green — it dies at the request, naming the route.
//!
//! The tripwire is deliberately narrow: it fires only on the four "missing/malformed" refusals a
//! bare POST earns, never on a PRESENTED-but-rejected authority (a stale tab, a pre-restart token,
//! a foreign incarnation). Those are real properties tests SHOULD assert, and `game_epoch_runtime`
//! does. The markers are pinned against the live server by
//! `no_silent_dark_act::a_bare_act_post_really_is_refused_for_a_missing_authority`, so a reworded
//! refusal turns the gate red instead of blind.

#![allow(dead_code)]

use axum::Router;
use axum::body::Body;
use axum::extract::Request as AxumRequest;
use axum::http::{Method, Request, StatusCode};
use axum::middleware::Next;
use axum::response::Response;
use tower::ServiceExt; // oneshot

/// ⚑ **THE TRIPWIRE'S EYES MOVED FROM THE COPY TO A HEADER, and the move is the repair, not a
/// weakening.**
///
/// This gate used to key on four PROSE markers in the response body —
/// `"missing or malformed game_host_incarnation"` and friends — which worked only because the body of
/// a refused act POST *was* the raw `to_string()` of a `GameSpineError`. That is the leak the
/// player-facing refusal audit closed: `dreggnet_web::refused_game_route_response` now serves a styled
/// page whose copy says the same thing to every reader in every one of these cases, because to a
/// player they mean the same thing and have the same remedy.
///
/// Had the markers stayed, [`is_missing_authority_refusal`] would have silently gone to always-`false`
/// and every guarded suite in this directory would be blind again — a hardening commit disarming a
/// working guard. So the server stamps [`dreggnet_web::REFUSAL_KIND_HEADER`] instead, answered
/// structurally by `GameSpineError::is_missing_route_authority` rather than by re-reading a sentence,
/// and this gate reads that. A reworded refusal can no longer blind it AT ALL, which the prose version
/// could only ever mitigate (by going red and asking to be repaired).
///
/// `no_silent_dark_act::a_bare_act_post_really_is_refused_for_a_missing_authority` is still the
/// positive control: it pins the header against the live server.
pub fn is_missing_authority_refusal(status: StatusCode, headers: &axum::http::HeaderMap) -> bool {
    status == StatusCode::CONFLICT
        && headers
            .get(dreggnet_web::REFUSAL_KIND_HEADER)
            .and_then(|v| v.to_str().ok())
            == Some(dreggnet_web::REFUSAL_MISSING_GAME_AUTHORITY)
}

/// **THE TRIPWIRE.** Wrap a test's router so that an `…/act` POST refused for a MISSING route
/// authority kills the test at the request instead of letting it walk into assertions that cannot
/// fire. Costs nothing on every other route and response.
///
/// Apply it to whatever router the test builds — `guard(catalog_router(state))`,
/// `guard(make_app())`, `guard(a.merge(b))` — and leave it on even for offerings that are not
/// spined today: the day one becomes a game key, that suite goes RED rather than dark.
pub fn guard(router: Router) -> Router {
    router.layer(axum::middleware::from_fn(trip_on_dark_act))
}

async fn trip_on_dark_act(request: AxumRequest, next: Next) -> Response {
    let watched = request.method() == Method::POST && request.uri().path().ends_with("/act");
    if !watched {
        return next.run(request).await;
    }
    let uri = request.uri().to_string();
    let response = next.run(request).await;
    if response.status() != StatusCode::CONFLICT {
        return response;
    }
    // Only a CONFLICT is ever buffered, so the ordinary path keeps streaming.
    let (parts, body) = response.into_parts();
    let bytes = axum::body::to_bytes(body, usize::MAX)
        .await
        .unwrap_or_default();
    let text = String::from_utf8_lossy(&bytes).to_string();
    assert!(
        !is_missing_authority_refusal(parts.status, &parts.headers),
        "DARK ACT — `POST {uri}` presented NO game route authority, so the executor was never \
         reached and every assertion after this call is about a turn that did not happen.\n  \
         server said: {text}\n  (the machine-readable cause is the `{header}: {kind}` response \
         header; the body is player copy and says the same thing for every stale route)\n  fix: \
         post through `common::post_act` (or add `common::authority_suffix(...)` to the body), \
         which reads the four hidden `game_*` fields off the viewer's own live page exactly as \
         their browser does.",
        header = dreggnet_web::REFUSAL_KIND_HEADER,
        kind = dreggnet_web::REFUSAL_MISSING_GAME_AUTHORITY,
    );
    Response::from_parts(parts, Body::from(bytes))
}

/// **A served page with its `<style>` and `<script>` elements removed** — what a substring
/// assertion about page CONTENT must be run against.
///
/// ⚑ **THE PAGE SHIPS ITS OWN PROSE INSIDE ITS STYLESHEET, AND TWO SUITES WERE READING IT.** Every
/// page `document()` builds inlines the whole skin, and that skin is HEAVILY COMMENTED — the
/// comments explain why a rule exists, in English, naming the very things the tests look for. Both
/// of these were live, and neither is about the product:
///
/// * `driven`'s receipt check does `body.find("executor receipt ")` and reads the next 64 characters
///   as hex. The FIRST occurrence in the document is `lib.rs:1199` — the comment explaining why
///   `.notice` needs `overflow-wrap:anywhere`, which says "a 64-character executor receipt hex". The
///   test read `hex — ONE unbroken word, in proport…` and reported that the receipt id was not hex.
/// * `descent`'s day-isolation check does `!board_b.contains("anna")`. `lib.rs:1060` says
///   "…is equally sc**anna**ble and the pair reads as one axis", so day-b's board "contained" day-a's
///   player and the day filter looked broken. It is not: that board ranks `boris` and nothing else.
///
/// One root cause, and it will recur every time the skin gains a sentence, so the reader is shared
/// rather than patched per suite. Everything outside the two elements is left EXACTLY as served —
/// tags, attributes and hidden inputs included — because the assertions that ride this also check
/// markup (`action="/session/keep-a/act"`), which [`crate::common`] must not strip out from under
/// them.
pub fn without_stylesheets(html: &str) -> String {
    const ELEMENTS: [(&str, &str); 2] = [("<style", "</style>"), ("<script", "</script>")];
    let mut out = String::with_capacity(html.len());
    let mut rest = html;
    loop {
        // The NEAREST opener, always — taking a later `<script>` first would swallow an earlier
        // `<style>` and everything between the two.
        let next = ELEMENTS
            .iter()
            .filter_map(|(open, close)| rest.find(open).map(|at| (at, *open, *close)))
            .min_by_key(|(at, _, _)| *at);
        let Some((at, open, close)) = next else {
            out.push_str(rest);
            return out;
        };
        out.push_str(&rest[..at]);
        out.push(' ');
        rest = match rest[at + open.len()..].split_once(close) {
            Some((_, tail)) => tail,
            // An unterminated element runs to the end of the document.
            None => return out,
        };
    }
}

/// The value of a `<input type="hidden" name="{name}" value="…">` on a rendered page.
pub fn hidden_value<'a>(html: &'a str, name: &str) -> Option<&'a str> {
    let marker = format!("name=\"{name}\" value=\"");
    Some(html.split_once(&marker)?.1.split_once('"')?.0)
}

/// The first act the page actually OFFERS, as `(turn, arg)` read out of its own form.
///
/// ⚑ Use this instead of hardcoding a `(method, index)` pair. `arg` is an INDEX into the
/// offering's LIVE decision list, so a fixed index goes stale the moment the engine offers a
/// different decision space. `demo_playthrough`'s tug test sent `("comp", 3)` until the engine
/// grew a real decision space and it started refusing with
///   method `comp` does not name decision 3 (Secret { card: 9 }, which dispatches under `secret`)
/// — a red that says nothing about the thing the test is for. Reading the pair off the rendered
/// form keeps such a test about "a browser user's offered play lands" rather than about the
/// engine's ordering.
///
/// `turn` and `arg` are emitted adjacently within one affordance form, so the first `arg` at or
/// after the first `turn` belongs to that same affordance.
pub fn first_offered_act(html: &str) -> Option<(String, i64)> {
    let (_, after_turn) = html.split_once("name=\"turn\" value=\"")?;
    let (turn, rest) = after_turn.split_once('"')?;
    let (_, after_arg) = rest.split_once("name=\"arg\" value=\"")?;
    let (arg, _) = after_arg.split_once('"')?;
    Some((turn.to_string(), arg.parse().ok()?))
}

/// **One act a rendered page OFFERS**, read off its own form — `{turn, arg}` plus the two things a
/// bare `(turn, arg)` pair loses: whether the control is actually pressable, and what it SAYS.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OfferedAct {
    /// The affordance verb (the form's hidden `turn`).
    pub turn: String,
    /// The affordance argument — an INDEX into the offering's live decision list, so never
    /// hardcode one; read it here.
    pub arg: i64,
    /// `false` when the control is rendered `disabled` (the cap tooth SHOWN, not hidden). Pressing
    /// one is a real executor refusal, so a test driving "a browser user's play lands" must pick an
    /// ENABLED row.
    pub enabled: bool,
    /// The control's own text. ⚑ A label is user-facing state: tug leaked a seat's committed hand
    /// through action-row labels while its fog *sections* were correct (`7f216ec8b`), so a fog test
    /// that reads only the prose cannot see the leak. This is where it lives.
    pub label: String,
    /// **The form carries a text field** (`<input name="text">`) — the affordance DECLARED it wants
    /// the user's prose (`MenuItem::wants_text`, from `Action::wants_text`).
    ///
    /// ⚑ A driver that ignores this posts `turn=&arg=` into a slot whose executor demands a string
    /// and reads back a refusal, which is exactly the shape `hermes`/`names`/`doc` were stuck in — and
    /// a test that *keeps* ignoring it cannot tell the missing carrier from a missing string. Press
    /// one of these through [`post_act_typing`].
    pub wants_text: bool,
}

/// **Every act a rendered page offers**, in document order — the affordance forms AND the clickable
/// board cells, since a `CoordGrid` square is a real POST form too.
///
/// Use this instead of hardcoding a `(method, index)` pair; see [`first_offered_act`] for why.
pub fn offered_acts(html: &str) -> Vec<OfferedAct> {
    let mut out = Vec::new();
    for chunk in html.split("<form ").skip(1) {
        let form = match chunk.split_once("</form>") {
            Some((form, _)) => form,
            None => chunk,
        };
        let Some(turn) = attr_value(form, "turn") else {
            continue;
        };
        let Some(arg) = attr_value(form, "arg").and_then(|a| a.parse::<i64>().ok()) else {
            continue;
        };
        // The renderer emits ` disabled` on BOTH the arg input and the button of a `!enabled`
        // affordance; a board cell is never disabled.
        let enabled = !form.contains(" disabled");
        let label = form
            .split_once("<button")
            .and_then(|(_, rest)| rest.split_once('>'))
            .and_then(|(_, rest)| rest.split_once("</button>"))
            .map(|(inner, _)| strip_tags(inner))
            .unwrap_or_default();
        // Read off the RENDERED form, never guessed from the offering: the page itself states
        // whether this affordance takes prose.
        let wants_text = form.contains("name=\"text\"");
        out.push(OfferedAct {
            turn,
            arg,
            enabled,
            label,
            wants_text,
        });
    }
    out
}

/// The value of `name="{name}" value="…"` within one form chunk.
fn attr_value(form: &str, name: &str) -> Option<String> {
    let marker = format!("name=\"{name}\" value=\"");
    let (_, rest) = form.split_once(&marker)?;
    let (value, _) = rest.split_once('"')?;
    Some(value.to_string())
}

/// Tags out, whitespace collapsed — a control's spoken text.
fn strip_tags(html: &str) -> String {
    let mut out = String::new();
    let mut in_tag = false;
    for c in html.chars() {
        match c {
            '<' => in_tag = true,
            '>' => {
                in_tag = false;
                out.push(' ');
            }
            c if !in_tag => out.push(c),
            _ => {}
        }
    }
    out.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// The play-surface URI an act route hangs off — `…/session/{id}/act?q` → `…/session/{id}?q`.
pub fn surface_uri_of(act_uri: &str) -> String {
    let (path, query) = match act_uri.split_once('?') {
        Some((path, query)) => (path, Some(query)),
        None => (act_uri, None),
    };
    let base = path.strip_suffix("/act").unwrap_or(path);
    match query {
        Some(query) => format!("{base}?{query}"),
        None => base.to_string(),
    }
}

/// GET a page carrying the raw `cookie` header (`None` = a cookie-less browser).
pub async fn get_with_cookie(
    app: &Router,
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

/// **The form-encoded route-authority suffix for `act_uri`, read off the live page.**
///
/// Returns `&game_host_incarnation=…&game_session_generation=…&game_expected_pre_head=…&
/// game_form_token=…` — or the empty string for an offering that is not spined (its surface
/// carries no such form, and its act route asks for none).
///
/// The authority is bound to `{offering, session, incarnation, generation, pre-head}` and NOT to
/// the viewer, so reading it as this cookie is the same bytes any seat would be served; the GET is
/// made as `cookie` only so a per-viewer surface renders the page the caller is about to act on.
pub async fn authority_suffix(app: &Router, act_uri: &str, cookie: Option<&str>) -> String {
    let (_, surface) = get_with_cookie(app, &surface_uri_of(act_uri), cookie).await;
    [
        "game_host_incarnation",
        "game_session_generation",
        "game_expected_pre_head",
        "game_form_token",
    ]
    .iter()
    .map(|name| hidden_value(&surface, name).map(|value| format!("&{name}={value}")))
    .collect::<Option<String>>()
    .unwrap_or_default()
}

/// The `{turn, arg}` POST body a browser submits from the play form, authority included.
pub async fn act_body(
    app: &Router,
    act_uri: &str,
    turn: &str,
    arg: i64,
    cookie: Option<&str>,
) -> String {
    let authority = authority_suffix(app, act_uri, cookie).await;
    format!("turn={turn}&arg={arg}{authority}")
}

/// **POST one turn to `act_uri` as `dregg_user={user}`, carrying the route authority.**
pub async fn post_act(
    app: &Router,
    act_uri: &str,
    turn: &str,
    arg: i64,
    user: &str,
) -> (StatusCode, String) {
    post_act_with_cookie(app, act_uri, turn, arg, &format!("dregg_user={user}")).await
}

/// [`post_act`] over a raw cookie header — for suites driving minted visitor cookies verbatim.
pub async fn post_act_with_cookie(
    app: &Router,
    act_uri: &str,
    turn: &str,
    arg: i64,
    cookie: &str,
) -> (StatusCode, String) {
    let body = act_body(app, act_uri, turn, arg, Some(cookie)).await;
    let response = app
        .clone()
        .oneshot(
            Request::builder()
                .method("POST")
                .uri(act_uri)
                .header("content-type", "application/x-www-form-urlencoded")
                .header("cookie", cookie)
                .body(Body::from(body))
                .unwrap(),
        )
        .await
        .unwrap();
    let status = response.status();
    let bytes = axum::body::to_bytes(response.into_body(), usize::MAX)
        .await
        .unwrap();
    (status, String::from_utf8_lossy(&bytes).to_string())
}

/// **POST one turn, TYPING into the affordance's text field** — [`post_act`] for an act whose form
/// declared a free-text want ([`OfferedAct::wants_text`]).
///
/// `typed` is what a person would put in the box; `None` presses the button with the box left empty,
/// which is a real (and legibly refused) thing a browser can do — it is how you check that the
/// executor still demands the string rather than accepting a bare press.
///
/// ⚑ This is the driver half of the text carrier, and without it the renderer half is untestable:
/// a `wants_text` affordance pressed through plain [`post_act`] posts no `text=` at all, so the
/// executor refuses ("no prompt supplied … the button label is not a prompt") and the page looks
/// exactly as broken as it did before the carrier existed.
pub async fn post_act_typing(
    app: &Router,
    act_uri: &str,
    turn: &str,
    arg: i64,
    typed: Option<&str>,
    user: &str,
) -> (StatusCode, String) {
    let cookie = format!("dregg_user={user}");
    let authority = authority_suffix(app, act_uri, Some(&cookie)).await;
    let text = typed
        .map(|t| format!("&text={}", form_encode(t)))
        .unwrap_or_default();
    let body = format!("turn={turn}&arg={arg}{text}{authority}");
    let response = app
        .clone()
        .oneshot(
            Request::builder()
                .method("POST")
                .uri(act_uri)
                .header("content-type", "application/x-www-form-urlencoded")
                .header("cookie", &cookie)
                .body(Body::from(body))
                .unwrap(),
        )
        .await
        .unwrap();
    let status = response.status();
    let bytes = axum::body::to_bytes(response.into_body(), usize::MAX)
        .await
        .unwrap();
    (status, String::from_utf8_lossy(&bytes).to_string())
}

/// Percent-encode one `application/x-www-form-urlencoded` field value. Deliberately tiny and
/// conservative — everything outside the unreserved set is escaped, so a typed sentence (spaces,
/// punctuation, `&`, `=`) survives the body intact instead of forging extra fields.
fn form_encode(value: &str) -> String {
    let mut out = String::new();
    for byte in value.as_bytes() {
        match byte {
            b'A'..=b'Z' | b'a'..=b'z' | b'0'..=b'9' | b'-' | b'_' | b'.' | b'~' => {
                out.push(*byte as char)
            }
            b' ' => out.push('+'),
            other => out.push_str(&format!("%{other:02X}")),
        }
    }
    out
}

/// [`post_act`] with no cookie at all (the bootstrap mints a visitor identity per request).
pub async fn post_act_anonymous(
    app: &Router,
    act_uri: &str,
    turn: &str,
    arg: i64,
) -> (StatusCode, String) {
    let body = act_body(app, act_uri, turn, arg, None).await;
    let response = app
        .clone()
        .oneshot(
            Request::builder()
                .method("POST")
                .uri(act_uri)
                .header("content-type", "application/x-www-form-urlencoded")
                .body(Body::from(body))
                .unwrap(),
        )
        .await
        .unwrap();
    let status = response.status();
    let bytes = axum::body::to_bytes(response.into_body(), usize::MAX)
        .await
        .unwrap();
    (status, String::from_utf8_lossy(&bytes).to_string())
}
