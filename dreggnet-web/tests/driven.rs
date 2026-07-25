//! **The driven end-to-end proof — the WEB frontend, over the REAL substrate, via axum.**
//!
//! A [`DungeonOffering`] session PLAYS THROUGH the [`WebFrontend`] + the axum handlers, with NO
//! real network (axum's `ServiceExt::oneshot`) and NO Discord:
//! - `GET /session/{id}` renders the room prose + ONE affordance control (a POST `<form>`) per
//!   [`Action`] — asserted in the HTML;
//! - `POST /session/{id}/act` advances a REAL turn — a winning line lands (the world moves, the
//!   verified-turn count grows, the HTML reflects the new committed state); an illegal move is a
//!   real executor refusal surfaced as an honest banner, nothing committed (anti-ghost);
//! - `GET /session/{id}/verify` holds — the whole committed chain re-verifies by replay.

use std::sync::Arc;

use axum::body::Body;
use axum::http::{Request, StatusCode};
use dreggnet_web::{WebState, router};
use tower::ServiceExt; // oneshot

mod common;

use dungeon_on_dregg::{KP_CLAIM_RED, KP_DESCEND, KP_PRESS_ON, KP_SEIZE, KP_TRADE_BLOWS};

const CHOOSE: &str = "choose";

/// Drive a `GET` and return `(status, body)`.
async fn get(app: &axum::Router, uri: &str) -> (StatusCode, String) {
    let resp = app
        .clone()
        .oneshot(Request::builder().uri(uri).body(Body::empty()).unwrap())
        .await
        .unwrap();
    let status = resp.status();
    let bytes = axum::body::to_bytes(resp.into_body(), usize::MAX)
        .await
        .unwrap();
    (status, String::from_utf8(bytes.to_vec()).unwrap())
}

/// Drive a `POST /session/{id}/act` with a form-encoded `{turn, arg}` and a `dregg_user` cookie
/// (the web identity); return `(status, body)`.
async fn act(
    app: &axum::Router,
    id: &str,
    turn: &str,
    arg: i64,
    user: &str,
) -> (StatusCode, String) {
    let resp = app
        .clone()
        .oneshot(
            Request::builder()
                .method("POST")
                .uri(format!("/session/{id}/act"))
                .header("content-type", "application/x-www-form-urlencoded")
                .header("cookie", format!("dregg_user={user}"))
                .body(Body::from(format!("turn={turn}&arg={arg}")))
                .unwrap(),
        )
        .await
        .unwrap();
    let status = resp.status();
    let bytes = axum::body::to_bytes(resp.into_body(), usize::MAX)
        .await
        .unwrap();
    (status, String::from_utf8(bytes.to_vec()).unwrap())
}

/// Count the affordance controls (POST-form submit buttons) in a rendered page.
fn control_count(html: &str) -> usize {
    html.matches("<button type=\"submit\"").count()
}

/// `GET /session/{id}` opens a real DungeonOffering session and renders the room prose + ONE
/// affordance control per cap-gated [`Action`] — the affordance Surface, as HTML.
#[tokio::test]
async fn get_renders_the_room_and_one_control_per_affordance() {
    let app = common::guard(router(Arc::new(WebState::new())));

    let (status, body) = get(&app, "/session/keep-a").await;
    assert_eq!(status, StatusCode::OK);

    // The Keep names itself, and the surface carries the gatehall's cap-gated affordances as
    // POST forms — the gatehall offers two moves (trade blows, press on).
    assert!(
        body.contains("The Warden&#x27;s Keep") || body.contains("Warden"),
        "the surface names the Keep: {body}"
    );
    assert!(
        body.contains("The party&#x27;s move") || body.contains("party"),
        "the affordance section is present"
    );
    assert!(
        body.contains(&format!("value=\"{}\"", KP_PRESS_ON)),
        "the press-on affordance's arg is a POST form field"
    );
    assert!(
        body.contains("action=\"/session/keep-a/act\""),
        "each affordance POSTs its Action to the act route"
    );
    assert_eq!(
        control_count(&body),
        2,
        "one affordance control per Action (gatehall offers two): {body}"
    );
}

/// The full lifecycle: a winning line PLAYS THROUGH the web surface — each `POST /act` advances a
/// real turn, the world moves room to room, the verified-turn count grows, the HTML reflects the
/// new committed state, and `verify` holds throughout. The Keep clears.
#[tokio::test]
async fn a_winning_line_plays_through_the_web_surface() {
    let state = Arc::new(WebState::new());
    let app = common::guard(router(state.clone()));
    let id = "win";
    let sid = dreggnet_offerings::SessionId::new(id);

    // Open + render the gatehall.
    let (_s, body) = get(&app, &format!("/session/{id}")).await;
    assert!(
        body.contains("1 (") || body.contains("1 verified") || body.contains(">1<"),
        "genesis is one verified turn"
    );
    assert_eq!(state.current_room(&sid).as_deref(), Some("gatehall"));
    assert_eq!(
        state.receipts_len(&sid),
        Some(1),
        "genesis is the first verified turn"
    );

    // press on (gatehall → hall) — a real committed turn.
    let (status, body) = act(&app, id, CHOOSE, KP_PRESS_ON as i64, "alice").await;
    assert_eq!(status, StatusCode::OK);
    assert!(
        body.contains("Turn committed"),
        "the honest banner reports a committed turn"
    );
    let receipt_start = body
        .find("executor receipt ")
        .expect("the landing banner publishes a copyable receipt-chain join")
        + "executor receipt ".len();
    let receipt_id = &body[receipt_start..receipt_start + 64];
    assert!(
        receipt_id
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte)),
        "the complete 32-byte receipt id is lowercase hex: {receipt_id}"
    );
    assert!(
        body.contains("class=\"replay-verify\"")
            && body.contains("href=\"/session/win/verify\"")
            && body.contains(">Replay-verify</a>"),
        "the receipt has an actual replay control, not only a status label: {body}"
    );
    assert_eq!(
        state.current_room(&sid).as_deref(),
        Some("hall"),
        "the world advanced to the plundered hall"
    );
    assert_eq!(
        state.receipts_len(&sid),
        Some(2),
        "a real verified turn landed"
    );
    assert!(
        body.contains("hall"),
        "the HTML reflects the new committed room"
    );

    // claim the crown for the Red Hand (hall).
    let (_s, _b) = act(&app, id, CHOOSE, KP_CLAIM_RED as i64, "alice").await;
    assert_eq!(state.receipts_len(&sid), Some(3));

    // descend the collapsing stair (hall → sanctum).
    let (_s, _b) = act(&app, id, CHOOSE, KP_DESCEND as i64, "alice").await;
    assert_eq!(
        state.current_room(&sid).as_deref(),
        Some("sanctum"),
        "descended to the warded sanctum"
    );
    assert_eq!(state.receipts_len(&sid), Some(4));

    // seize the hoard (ends the dungeon).
    let (status, body) = act(&app, id, CHOOSE, KP_SEIZE as i64, "alice").await;
    assert_eq!(status, StatusCode::OK);
    assert!(
        body.contains("The Keep is cleared"),
        "the objective is met — the HTML shows the cleared banner: {body}"
    );
    assert_eq!(
        state.receipts_len(&sid),
        Some(5),
        "genesis + four committed turns"
    );
    assert_eq!(state.current_room(&sid), None, "the dungeon has ended");

    // The whole committed chain re-verifies by replay — over HTTP.
    let (status, verify_json) = get(&app, &format!("/session/{id}/verify")).await;
    assert_eq!(status, StatusCode::OK);
    assert!(
        verify_json.contains("\"verified\":true"),
        "the chain re-verifies by replay: {verify_json}"
    );
    assert!(
        verify_json.contains("\"turns\":5"),
        "five verified turns: {verify_json}"
    );

    let report = state.verify(&sid).expect("the session exists");
    assert!(report.verified, "verify() holds: {}", report.detail);
    assert_eq!(report.turns, 5);
}

/// An illegal move (a killing blow past the HP floor) POSTed at the web surface is a REAL executor
/// refusal — the affordance is a dimmed cap-tooth in the HTML, but a crafted POST of it still
/// lands as [`Outcome::Refused`]: nothing commits, no receipt, the world does not move, and the
/// refusal is surfaced honestly. The honest prefix still re-verifies. The executor is the sole
/// referee — the web `enabled` decoration is not.
#[tokio::test]
async fn an_illegal_move_is_refused_honestly_no_receipt() {
    let state = Arc::new(WebState::new());
    let app = common::guard(router(state.clone()));
    let id = "danger";
    let sid = dreggnet_offerings::SessionId::new(id);

    let _ = get(&app, &format!("/session/{id}")).await;

    // Two survivable trade-blows (hp 50 → 30 → 10), each a real committed turn.
    for _ in 0..2 {
        let (_s, body) = act(&app, id, CHOOSE, KP_TRADE_BLOWS as i64, "bob").await;
        assert!(body.contains("Turn committed"), "a survivable blow commits");
    }
    let before = state.receipts_len(&sid);
    assert_eq!(
        state.current_room(&sid).as_deref(),
        Some("gatehall"),
        "still trading blows in the gatehall"
    );

    // At hp 10 the trade-blows affordance is now a DIMMED cap-tooth in the rendered HTML.
    let (_s, body) = get(&app, &format!("/session/{id}")).await;
    assert!(
        body.contains("affordance dimmed"),
        "the killing blow is rendered as a dimmed cap-tooth: {body}"
    );

    // Craft a POST of it anyway — the REAL executor refuses (the HP floor gate on the post-state).
    let (status, body) = act(&app, id, CHOOSE, KP_TRADE_BLOWS as i64, "bob").await;
    assert_eq!(status, StatusCode::OK);
    assert!(
        body.contains("Refused"),
        "the illegal move is surfaced honestly as a refusal: {body}"
    );
    assert!(body.contains("anti-ghost"), "the anti-ghost tooth is named");

    // Nothing committed — no receipt, the world unmoved.
    assert_eq!(
        state.receipts_len(&sid),
        before,
        "no receipt landed for the refused move"
    );
    assert_eq!(
        state.current_room(&sid).as_deref(),
        Some("gatehall"),
        "the world did not move"
    );

    // The honest prefix still re-verifies.
    assert!(
        state.verify(&sid).unwrap().verified,
        "the honest prefix re-verifies after the refusal"
    );
}

/// A POST for an affordance the surface never offered (an out-of-ballot arg) is an honest
/// frontend-level refusal, BEFORE the substrate — the frontend refuses to collect a control it
/// did not present, and nothing advances.
#[tokio::test]
async fn a_post_for_an_unpresented_affordance_is_refused_before_the_substrate() {
    let state = Arc::new(WebState::new());
    let app = common::guard(router(state.clone()));
    let id = "nope";
    let sid = dreggnet_offerings::SessionId::new(id);

    let _ = get(&app, &format!("/session/{id}")).await;
    let before = state.receipts_len(&sid);

    // arg 99 is not on the gatehall ballot → the frontend never presented it → not collected.
    let (status, body) = act(&app, id, CHOOSE, 99, "carol").await;
    assert_eq!(status, StatusCode::OK);
    assert!(
        body.contains("not on the current surface"),
        "an unpresented affordance is an honest frontend-level refusal: {body}"
    );
    assert_eq!(state.receipts_len(&sid), before, "nothing advanced");
}

/// The same web user derives the SAME dregg identity across requests, and distinct users derive
/// distinct identities — the frontend-agnostic identity contract (mirroring the Discord
/// derivation shape), driven through the `Frontend` impl.
#[tokio::test]
async fn web_identity_is_deterministic_and_per_user() {
    use dreggnet_offerings::Frontend;
    let fe = dreggnet_web::WebFrontend::new();
    assert_eq!(fe.identity("alice".into()), fe.identity("alice".into()));
    assert_ne!(fe.identity("alice".into()), fe.identity("bob".into()));
}
