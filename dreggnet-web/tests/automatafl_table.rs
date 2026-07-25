//! **THE AUTOMATAFL TABLE — the bespoke web surface, driven.**
//!
//! `games.rs` proves a turn PLAYS on the generic catalog rails. This proves the front door built
//! over them, and it pins the four properties that front door exists for:
//!
//! - **realtime** — a seat holding an open `EventSource` is PUSHED the opponent's move; the frame
//!   arrives with no second request and no reload (`the_waiting_seat_is_pushed_the_opponents_move`);
//! - **the seat lock** — a table minted at `/automatafl` binds its two seats to two unguessable
//!   server-derived labels: a stranger who knows the id cannot claim a seat, and cannot reach the
//!   sealed-move disclosure by asserting a label;
//! - **the fog** — the sealed plaintext reaches its own seat and NOBODY else: not the opponent, not
//!   a stranger, not a spectator;
//! - **spectating** — a non-seat viewer gets the live board with both moves fogged and every
//!   control natively disabled.
//!
//! The board indices here are derived from `dregg_automatafl::game::N`, never a literal — the
//! surface is n-generic and this test moves with it.

use std::sync::Arc;
use std::time::Duration;

use axum::body::Body;
use axum::http::{Request, StatusCode};
use dregg_automatafl::game::N;
use dreggnet_web::automatafl_web::{self, SeatSlot};
use dreggnet_web::{CatalogState, catalog_router};
use tokio_stream::StreamExt;
use tower::ServiceExt; // oneshot

/// The merged surface under test: the catalog rails (the play + the events stream) plus the
/// automatafl front door, over ONE shared state.
fn app() -> axum::Router {
    let state = Arc::new(CatalogState::new());
    catalog_router(Arc::clone(&state)).merge(automatafl_web::automatafl_router(state))
}

/// The board index of `(x, y)` — derived from the crate's own board width, not a literal.
fn idx(x: i64, y: i64) -> i64 {
    y * N as i64 + x
}

async fn get_as(app: &axum::Router, uri: &str, user: Option<&str>) -> (StatusCode, String) {
    let mut builder = Request::builder().uri(uri);
    if let Some(user) = user {
        builder = builder.header("cookie", format!("dregg_user={user}"));
    }
    let resp = app
        .clone()
        .oneshot(builder.body(Body::empty()).unwrap())
        .await
        .unwrap();
    let status = resp.status();
    let bytes = axum::body::to_bytes(resp.into_body(), usize::MAX)
        .await
        .unwrap();
    (status, String::from_utf8_lossy(&bytes).to_string())
}

fn hidden_value<'a>(html: &'a str, name: &str) -> Option<&'a str> {
    let marker = format!("name=\"{name}\" value=\"");
    Some(html.split_once(&marker)?.1.split_once('"')?.0)
}

/// Post one turn as `user`.
///
/// ⚠ THIS HELPER WAS DARK. `automatafl` has been a SPINED game key since the common game-session
/// spine landed (`game_spine::game_kind`), so `POST …/act` requires the server-presented route
/// authority (`{incarnation, generation, pre-head, token}`) that the play surface stamps into its
/// own form. This helper posted a bare `turn=&arg=`, so every act in this file was answered `409
/// invalid game reference` and the four properties the file exists to pin — the seat lock, the
/// fog, the realtime push, the spectator — had not actually been checked at the act layer for as
/// long as the spine has existed. It now reads the authority off that user's live page, exactly as
/// their browser would, so the assertions below reach the executor again.
async fn post_act(
    app: &axum::Router,
    id: &str,
    turn: &str,
    arg: i64,
    user: &str,
) -> (StatusCode, String) {
    let (_, surface) = get_as(
        app,
        &format!("/offerings/automatafl/session/{id}"),
        Some(user),
    )
    .await;
    let authority = [
        "game_host_incarnation",
        "game_session_generation",
        "game_expected_pre_head",
        "game_form_token",
    ]
    .iter()
    .map(|name| hidden_value(&surface, name).map(|value| format!("&{name}={value}")))
    .collect::<Option<String>>()
    .unwrap_or_default();
    let resp = app
        .clone()
        .oneshot(
            Request::builder()
                .method("POST")
                .uri(format!("/offerings/automatafl/session/{id}/act"))
                .header("content-type", "application/x-www-form-urlencoded")
                .header("cookie", format!("dregg_user={user}"))
                .body(Body::from(format!("turn={turn}&arg={arg}{authority}")))
                .unwrap(),
        )
        .await
        .unwrap();
    let status = resp.status();
    let bytes = axum::body::to_bytes(resp.into_body(), usize::MAX)
        .await
        .unwrap();
    (status, String::from_utf8_lossy(&bytes).to_string())
}

/// The next SSE frame off an already-open stream (the test's whole point: no second request).
async fn next_frame(frames: &mut axum::body::BodyDataStream) -> String {
    let frame = tokio::time::timeout(Duration::from_secs(10), frames.next())
        .await
        .expect("a frame arrives within the timeout")
        .expect("the stream is still open")
        .expect("the frame is not an error");
    String::from_utf8_lossy(&frame).to_string()
}

/// Mint a table through the real route and return `(id, seat A label, seat B label)`.
async fn open_table(app: &axum::Router) -> (String, String, String) {
    let resp = app
        .clone()
        .oneshot(
            Request::builder()
                .method("POST")
                .uri("/automatafl/table")
                .body(Body::empty())
                .unwrap(),
        )
        .await
        .unwrap();
    assert_eq!(resp.status(), StatusCode::OK, "the table mints");
    let bytes = axum::body::to_bytes(resp.into_body(), usize::MAX)
        .await
        .unwrap();
    let body = String::from_utf8_lossy(&bytes).to_string();
    let id = body
        .split("/automatafl/table/")
        .nth(1)
        .and_then(|rest| rest.split('?').next())
        .expect("the lobby page carries a seat link")
        .to_string();
    assert!(
        id.starts_with("af1-"),
        "a minted table is seat-locked: {id}"
    );
    (
        id.clone(),
        automatafl_web::seat_label(&id, SeatSlot::A),
        automatafl_web::seat_label(&id, SeatSlot::B),
    )
}

/// **The landing page states the rules and offers the one control that matters.** It also names the
/// board's real width, read from the game crate — so a board-size change moves the page, not a
/// hand-maintained sentence.
#[tokio::test]
async fn the_landing_page_states_the_rules_and_offers_a_table() {
    let app = app();
    let (status, body) = get_as(&app, "/automatafl", None).await;
    assert_eq!(status, StatusCode::OK);
    assert!(
        body.contains(&format!("{N}×{N}")),
        "the rules name the ACTUAL board width ({N}): {body}"
    );
    assert!(
        body.contains("commit → reveal → resolve"),
        "the simultaneous-move round is explained"
    );
    assert!(
        body.contains("action=\"/automatafl/table\""),
        "the 'open a table' CTA posts to the mint route"
    );
}

/// **A minted table hands back two DISTINCT seat links plus a spectator link.** The invite is the
/// seat: it is the only thing that can sit down in seat B.
#[tokio::test]
async fn minting_a_table_hands_back_two_seat_links_and_a_spectator_link() {
    let app = app();
    let (id, a, b) = open_table(&app).await;
    let (_, body) = get_as(&app, "/automatafl", None).await;
    assert!(!body.contains(&id), "the landing page leaks no table");

    assert_ne!(a, b, "the two seats carry different secrets");
    let resp = app
        .clone()
        .oneshot(
            Request::builder()
                .method("POST")
                .uri("/automatafl/table")
                .body(Body::empty())
                .unwrap(),
        )
        .await
        .unwrap();
    let bytes = axum::body::to_bytes(resp.into_body(), usize::MAX)
        .await
        .unwrap();
    let second = String::from_utf8_lossy(&bytes).to_string();
    assert!(
        !second.contains(&id),
        "each mint is a fresh table (no id reuse)"
    );
    assert!(
        second.contains("seat=a&amp;key=") && second.contains("seat=b&amp;key="),
        "both seat links are on the lobby page: {second}"
    );
    assert!(
        second.contains("/automatafl/watch/"),
        "the spectator link is on the lobby page"
    );
}

/// **A valid seat link installs the seat; a forged one is refused.** The secret is moved out of the
/// URL into an `HttpOnly` cookie and the browser is redirected to the ordinary table.
#[tokio::test]
async fn a_seat_link_installs_the_seat_and_a_forged_key_is_refused() {
    let app = app();
    let (id, a, _) = open_table(&app).await;

    let resp = app
        .clone()
        .oneshot(
            Request::builder()
                .uri(format!("/automatafl/table/{id}?seat=a&key={a}"))
                .body(Body::empty())
                .unwrap(),
        )
        .await
        .unwrap();
    assert_eq!(
        resp.status(),
        StatusCode::SEE_OTHER,
        "the seat link redirects"
    );
    let cookie = resp
        .headers()
        .get("set-cookie")
        .expect("the seat link installs the seat")
        .to_str()
        .unwrap()
        .to_string();
    assert!(
        cookie.contains(&format!("dregg_user={a}")) && cookie.contains("HttpOnly"),
        "the seat is installed as an HttpOnly identity cookie: {cookie}"
    );
    assert_eq!(
        resp.headers().get("location").unwrap().to_str().unwrap(),
        format!("/offerings/automatafl/session/{id}"),
        "the secret leaves the address bar immediately"
    );
    assert_eq!(
        resp.headers().get("referrer-policy").unwrap(),
        "no-referrer",
        "the seat secret is never handed to the next hop"
    );

    // A forged key — and a valid key against the WRONG seat — are both refused.
    for uri in [
        format!(
            "/automatafl/table/{id}?seat=a&key=afs1-a-{}",
            "0".repeat(32)
        ),
        format!("/automatafl/table/{id}?seat=b&key={a}"),
        format!("/automatafl/table/{id}"),
    ] {
        let resp = app
            .clone()
            .oneshot(Request::builder().uri(&uri).body(Body::empty()).unwrap())
            .await
            .unwrap();
        assert_eq!(resp.status(), StatusCode::FORBIDDEN, "refused: {uri}");
    }
}

/// **THE SEAT COOKIE IS `Secure` BEHIND TLS.** The seat label IS the seat: a browser that received
/// it over https must never be willing to put it back on a plaintext hop. The evidence is exactly
/// the evidence the visitor-cookie bootstrap uses (the request scheme, or the `X-Forwarded-Proto`
/// the TLS-terminating edge sets), so the two identity cookies cannot drift apart.
///
/// This drives the seat link WITHOUT minting through the offering host — the link's verification is
/// pure key-checking, so this leg stays meaningful even when opening a world is refused.
#[tokio::test]
async fn the_seat_cookie_is_marked_secure_behind_a_tls_edge() {
    let app = app();
    let id = automatafl_web::mint_table_id();
    let a = automatafl_web::seat_label(&id, SeatSlot::A);
    let link = format!("/automatafl/table/{id}?seat=a&key={a}");

    let cookie_of = |proto: Option<&str>| {
        let mut builder = Request::builder().uri(&link);
        if let Some(proto) = proto {
            builder = builder.header("x-forwarded-proto", proto);
        }
        let app = app.clone();
        let request = builder.body(Body::empty()).unwrap();
        async move {
            let resp = app.oneshot(request).await.unwrap();
            assert_eq!(
                resp.status(),
                StatusCode::SEE_OTHER,
                "the seat link verifies"
            );
            resp.headers()
                .get("set-cookie")
                .expect("the seat link installs the seat")
                .to_str()
                .unwrap()
                .to_string()
        }
    };

    let plain = cookie_of(None).await;
    assert!(
        plain.contains("HttpOnly") && plain.contains("SameSite=Lax"),
        "the seat cookie is script-invisible and not sent cross-site: {plain}"
    );
    assert!(
        !plain.contains("Secure"),
        "a plain-http development request is not marked Secure (it would never be sent back): {plain}"
    );

    let behind_tls = cookie_of(Some("https")).await;
    assert!(
        behind_tls.contains("; Secure"),
        "behind a TLS-terminating edge the seat secret is https-only: {behind_tls}"
    );
    assert!(
        behind_tls.contains(&format!("dregg_user={a}")) && behind_tls.contains("HttpOnly"),
        "and it is still the seat's own HttpOnly identity: {behind_tls}"
    );
}

/// **A stranger cannot take a seat at a minted table.** Before this, seats went to whoever POSTed
/// first at a guessable id. Now the two minted labels are the only actors the table admits.
#[tokio::test]
async fn a_stranger_cannot_claim_a_seat_on_a_minted_table() {
    let app = app();
    let (id, a, _) = open_table(&app).await;

    let (_, body) = post_act(&app, &id, "select", idx(3, 1), "mallory").await;
    assert!(
        body.contains("seat-locked table"),
        "an asserted stranger is refused by the seat lock: {body}"
    );
    assert!(
        !body.contains("Turn committed"),
        "nothing committed for the stranger: {body}"
    );

    // The seat's own label plays normally.
    let (_, body) = post_act(&app, &id, "select", idx(3, 1), &a).await;
    assert!(
        body.contains("Turn committed"),
        "the seat link's holder plays: {body}"
    );

    // The signed route is fail-closed on a locked table (a pubkey actor is never a seat label).
    let resp = app
        .clone()
        .oneshot(
            Request::builder()
                .method("POST")
                .uri(format!("/offerings/automatafl/session/{id}/act-signed"))
                .header("content-type", "application/json")
                .body(Body::from("{}"))
                .unwrap(),
        )
        .await
        .unwrap();
    assert_eq!(
        resp.status(),
        StatusCode::FORBIDDEN,
        "act-signed is refused on a seat-locked table"
    );
}

/// **The sealed move reaches its own seat and nobody else.** Seat A seals; A sees the plaintext,
/// while seat B, a stranger, and a spectator all see only the commitment.
#[tokio::test]
async fn a_sealed_move_is_disclosed_only_to_its_own_seat() {
    let app = app();
    let (id, a, b) = open_table(&app).await;
    let table = format!("/offerings/automatafl/session/{id}");

    // BOTH links sit down (so the opponent below is a genuinely SEATED opponent, not a bystander),
    // then one of them seals.
    post_act(&app, &id, "select", idx(3, 1), &a).await;
    post_act(&app, &id, "select", idx(7, 1), &b).await;
    let (_, sealed) = post_act(&app, &id, "commit", idx(3, 3), &a).await;
    assert!(
        sealed.contains("YOUR sealed move"),
        "the sealer sees their own plaintext: {sealed}"
    );

    let (_, own) = get_as(&app, &table, Some(&a)).await;
    assert!(
        own.contains("YOUR sealed move"),
        "and still does on a plain GET: {own}"
    );

    for (who, label) in [
        ("the opponent", Some(b.as_str())),
        ("a stranger", Some("alice")),
    ] {
        let (_, view) = get_as(&app, &table, label).await;
        assert!(
            !view.contains("YOUR sealed move"),
            "{who} must not see the sealed plaintext: {view}"
        );
        assert!(
            view.contains("move SEALED"),
            "{who} sees the commitment only: {view}"
        );
    }

    let (status, spectator) = get_as(&app, &format!("/automatafl/watch/{id}"), None).await;
    assert_eq!(status, StatusCode::OK);
    assert!(
        !spectator.contains("YOUR sealed move") && spectator.contains("move SEALED"),
        "a spectator sees the commitment and never the plaintext: {spectator}"
    );
    assert!(
        spectator.contains("<fieldset class=\"spectate-lock\" disabled>"),
        "every spectator control is natively disabled: {spectator}"
    );
    assert!(
        spectator.contains(&format!("data-events=\"/automatafl/watch/{id}/events\"")),
        "the spectator board is live too"
    );
}

/// **REALTIME: the waiting seat is PUSHED the opponent's move.** Seat A opens the stream, seat B
/// acts, and A's next frame arrives on the already-open connection — no second request, no reload.
/// This is the defect the whole lane exists for: in a simultaneous-move game the waiting seat had
/// no way to learn that anything had happened.
#[tokio::test]
async fn the_waiting_seat_is_pushed_the_opponents_move() {
    let app = app();
    let (id, a, b) = open_table(&app).await;

    // Seat A subscribes.
    let resp = app
        .clone()
        .oneshot(
            Request::builder()
                .uri(format!("/offerings/automatafl/session/{id}/events"))
                .header("cookie", format!("dregg_user={a}"))
                .body(Body::empty())
                .unwrap(),
        )
        .await
        .unwrap();
    assert_eq!(resp.status(), StatusCode::OK);
    assert_eq!(
        resp.headers()
            .get("content-type")
            .unwrap()
            .to_str()
            .unwrap(),
        "text/event-stream",
        "the events route is a real SSE stream"
    );
    let mut frames = resp.into_body().into_data_stream();

    // The first frame is A's current surface: the board, in the commit phase.
    let first = next_frame(&mut frames).await;
    assert!(
        first.starts_with("data:"),
        "the frame is an SSE data frame: {first}"
    );
    assert!(
        first.contains("coordgrid") && first.contains("COMMIT (both seats seal a move)"),
        "the first frame is A's live surface: {first}"
    );
    assert!(
        !first.contains("move SEALED"),
        "nothing is sealed yet: {first}"
    );

    // Seat B seals, on a DIFFERENT connection. Nothing asks A's browser for anything.
    post_act(&app, &id, "select", idx(7, 1), &b).await;
    post_act(&app, &id, "commit", idx(7, 3), &b).await;

    // A's already-open stream carries the change through.
    let mut pushed = String::new();
    for _ in 0..8 {
        let frame = next_frame(&mut frames).await;
        if frame.contains("move SEALED") {
            pushed = frame;
            break;
        }
    }
    assert!(
        pushed.contains("move SEALED"),
        "the opponent's seal was PUSHED to the waiting seat: {pushed}"
    );
    assert!(
        !pushed.contains("YOUR sealed move"),
        "and the push carries A's fog, not B's plaintext: {pushed}"
    );
}

/// **A spectator's stream is a spectator's fog.** The realtime frame is the same per-viewer render
/// the page was served with, so subscribing never widens what a viewer may see.
#[tokio::test]
async fn a_spectator_stream_never_carries_a_sealed_plaintext() {
    let app = app();
    let (id, a, _) = open_table(&app).await;
    post_act(&app, &id, "select", idx(3, 1), &a).await;
    post_act(&app, &id, "commit", idx(3, 3), &a).await;

    let resp = app
        .clone()
        .oneshot(
            Request::builder()
                .uri(format!("/automatafl/watch/{id}/events"))
                .body(Body::empty())
                .unwrap(),
        )
        .await
        .unwrap();
    assert_eq!(resp.status(), StatusCode::OK);
    let mut frames = resp.into_body().into_data_stream();
    let frame = tokio::time::timeout(Duration::from_secs(10), frames.next())
        .await
        .expect("a frame arrives")
        .expect("the stream is open")
        .expect("the frame is not an error");
    let frame = String::from_utf8_lossy(&frame).to_string();
    assert!(
        frame.contains("move SEALED") && !frame.contains("YOUR sealed move"),
        "the spectator stream is fogged: {frame}"
    );
}

/// **Watching does not OPEN a table.** The ordinary session route deploys a world on first touch;
/// the spectator route must not, or anyone could mint unplayable tables by typing URLs.
#[tokio::test]
async fn watching_an_unknown_table_does_not_open_one() {
    let app = app();
    let (status, body) = get_as(&app, "/automatafl/watch/af1-nosuchtable", None).await;
    assert_eq!(status, StatusCode::NOT_FOUND);
    assert!(
        body.contains("No automatafl table") && body.contains("Watching does not open one"),
        "the refusal is honest about why: {body}"
    );
    // And the table really did not come into being: the stream over it stays silent, and a second
    // look still says no.
    let (status, _) = get_as(&app, "/automatafl/watch/af1-nosuchtable", None).await;
    assert_eq!(status, StatusCode::NOT_FOUND, "still no table");
}

/// **The ordinary table page declares its own realtime seam**, so the swap target and the stream can
/// never disagree about which session they show.
#[tokio::test]
async fn every_offering_table_declares_its_events_stream() {
    let app = app();
    let (status, body) = get_as(&app, "/offerings/tug/session/rt-tug", Some("alice")).await;
    assert_eq!(status, StatusCode::OK);
    assert!(
        body.contains("data-events=\"/offerings/tug/session/rt-tug/events\""),
        "the live region names its stream: {body}"
    );
    assert!(
        body.contains("new EventSource"),
        "the enhancement script subscribes to it"
    );
}
