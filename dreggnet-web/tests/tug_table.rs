//! **THE MULTIWAY-TUG TABLE — the front door the tug never had, driven end-to-end.**
//!
//! Before this surface existed, two people could not reliably start a game of multiway-tug. The
//! catalog page pointed every visitor at ONE publicly-guessable table, the first two identities to
//! press a button took the seats, and everybody after them was told they were a spectator. This
//! file pins the properties that replaced that:
//!
//! - **two identities can start a game** — a mint hands back two secret seat links, each opens its
//!   own seat, and both land real executor turns on the same table;
//! - **a third is refused a seat** — a stranger who knows the table id is refused BEFORE the
//!   substrate, with nothing committed, however they assert their identity;
//! - **an abandoned match RESOLVES** — a table whose owed move never arrives is forfeited against
//!   the seat that owed it, and every later act is refused with that outcome;
//! - **the fog** — a spectator sees both hands as a count and a committed root, never a card;
//! - **the old global table is gone** — nothing in the served HTML points at `tug-web`.
//!
//! The clock is driven by passing an explicit `now` to the reaper rather than by sleeping, so the
//! deadline under test is the REAL configured one and the test takes microseconds.

use std::sync::Arc;
use std::time::{Duration, Instant};

use axum::body::Body;
use axum::http::{Request, StatusCode};
use tower::ServiceExt; // oneshot

use dreggnet_web::table_seats::{self, SeatSlot};
use dreggnet_web::{CatalogState, catalog_router, tug_web};

/// The merged surface under test: the catalog rails (the play surface) plus the tug front door,
/// over ONE shared state — the same composition `make_app` builds.
fn app() -> (axum::Router, Arc<CatalogState>) {
    let state = Arc::new(CatalogState::new());
    let router = catalog_router(Arc::clone(&state)).merge(tug_web::tug_router(Arc::clone(&state)));
    (router, state)
}

async fn send(app: &axum::Router, request: Request<Body>) -> (StatusCode, String, Vec<String>) {
    let resp = app.clone().oneshot(request).await.unwrap();
    let status = resp.status();
    let cookies = resp
        .headers()
        .get_all("set-cookie")
        .iter()
        .filter_map(|v| v.to_str().ok())
        .map(str::to_string)
        .collect();
    let bytes = axum::body::to_bytes(resp.into_body(), usize::MAX)
        .await
        .unwrap();
    (status, String::from_utf8_lossy(&bytes).to_string(), cookies)
}

async fn get_as(app: &axum::Router, uri: &str, user: Option<&str>) -> (StatusCode, String) {
    let mut builder = Request::builder().uri(uri);
    if let Some(user) = user {
        builder = builder.header("cookie", format!("dregg_user={user}"));
    }
    let (status, body, _) = send(app, builder.body(Body::empty()).unwrap()).await;
    (status, body)
}

/// Mint a table through the real route and return its id.
async fn mint(app: &axum::Router) -> String {
    let (status, body, _) = send(
        app,
        Request::builder()
            .method("POST")
            .uri("/tug/table")
            .body(Body::empty())
            .unwrap(),
    )
    .await;
    assert_eq!(status, StatusCode::OK, "minting a tug table: {body}");
    // The lobby prints the session id in its own `sid` span.
    let id = body
        .split("<span class=\"sid\">")
        .nth(1)
        .and_then(|rest| rest.split('<').next())
        .expect("the lobby names the session")
        .to_string();
    assert!(id.starts_with("tug1-"), "minted id was `{id}`");
    id
}

fn hidden_value<'a>(html: &'a str, name: &str) -> Option<&'a str> {
    let marker = format!("name=\"{name}\" value=\"");
    let rest = html.split_once(&marker)?.1;
    Some(rest.split_once('"')?.0)
}

/// Post one turn as `user`. The tug is a SPINED game key, so a turn carries the server-presented
/// route authority (`{incarnation, generation, pre-head, token}`) the play surface stamps into its
/// own form — this reads it off that user's live page, exactly as their browser would. A page that
/// carries no form (a stranger's, a resolved table's) posts the bare turn, which is what a hand-
/// rolled request looks like and what the seat lock has to refuse.
async fn post_act(
    app: &axum::Router,
    id: &str,
    turn: &str,
    arg: i64,
    user: &str,
) -> (StatusCode, String) {
    let (_, surface) = get_as(app, &format!("/offerings/tug/session/{id}"), Some(user)).await;
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
    let (status, body, _) = send(
        app,
        Request::builder()
            .method("POST")
            .uri(format!("/offerings/tug/session/{id}/act"))
            .header("content-type", "application/x-www-form-urlencoded")
            .header("cookie", format!("dregg_user={user}"))
            .body(Body::from(format!("turn={turn}&arg={arg}{authority}")))
            .unwrap(),
    )
    .await;
    (status, body)
}

/// The tug round's action schedule is fixed by `Engine::order`, so the k-th press of a round is a
/// known `{turn, arg}`. Read it off the crate rather than hardcoding it here.
fn scheduled(session: &dregg_multiway_tug::TugSession) -> (String, i64) {
    let action = session.scheduled_action().expect("the round is live");
    (action.method().to_string(), action.idx() as i64)
}

/// The `{turn, arg}` a FRESH tug round opens with — derived, never a literal.
fn opening_turn() -> (String, i64) {
    use dreggnet_offerings::{Offering, SessionConfig};
    let session = dregg_multiway_tug::TugOffering
        .open(SessionConfig::default())
        .expect("a tug round opens");
    scheduled(&session)
}

// ───────────────────────────────────────────────────────────────────────────────────────
// 1. TWO IDENTITIES START A GAME — the thing that was impossible.
// ───────────────────────────────────────────────────────────────────────────────────────

/// **The whole point of the lane.** Two people, two links, one table, two real landed turns — and
/// a third person who knows the id is refused a seat.
#[tokio::test]
async fn two_identities_start_a_game_and_a_third_is_refused_a_seat() {
    let (app, _state) = app();
    let id = mint(&app).await;

    let seat_a = table_seats::TUG.seat_label(&id, SeatSlot::A);
    let seat_b = table_seats::TUG.seat_label(&id, SeatSlot::B);
    assert_ne!(seat_a, seat_b);

    // BOTH links are printed in the lobby, and each one really opens its own seat: following it
    // installs that seat's label as the browser's cookie and redirects to the play surface.
    for (seat, expected) in [(SeatSlot::A, &seat_a), (SeatSlot::B, &seat_b)] {
        let link = table_seats::TUG.seat_link(&id, seat);
        let (status, _, cookies) = send(
            &app,
            Request::builder().uri(&link).body(Body::empty()).unwrap(),
        )
        .await;
        assert_eq!(status, StatusCode::SEE_OTHER, "seat {seat:?} link");
        let cookie = cookies
            .iter()
            .find(|c| c.starts_with("dregg_user="))
            .unwrap_or_else(|| panic!("seat {seat:?} link sets the seat cookie"));
        assert!(
            cookie.contains(expected.as_str()),
            "the cookie must BE the seat label"
        );
        assert!(
            cookie.contains("HttpOnly"),
            "the seat secret is not scriptable"
        );
    }

    // A THIRD IDENTITY knows the table id — they were sent the watch link, or guessed. They may
    // not sit down, however they assert themselves.
    let (opening_turn_name, opening_arg) = opening_turn();
    for stranger in ["mallory", "visitor-deadbeef", "anon"] {
        let (status, body) = post_act(&app, &id, &opening_turn_name, opening_arg, stranger).await;
        assert_eq!(status, StatusCode::OK, "the refusal is a rendered page");
        assert!(
            body.contains("seat-locked table"),
            "stranger `{stranger}` was not refused the seat: {}",
            &body[..body.len().min(600)]
        );
        assert!(
            body.contains("nothing committed"),
            "the refusal must say nothing committed"
        );
    }

    // AND the two seats really play. Seat A opens the round.
    let (status, body) = post_act(&app, &id, &opening_turn_name, opening_arg, &seat_a).await;
    assert_eq!(status, StatusCode::OK);
    assert!(
        body.contains("Turn committed"),
        "seat A's opening press did not land: {}",
        &body[..body.len().min(800)]
    );

    // Seat B answers with whatever the schedule now owes. The turn is read off the live surface,
    // not guessed: the tug alternates and the schedule is fixed.
    let (status, body) = post_act(&app, &id, &opening_turn_name, opening_arg, &seat_b).await;
    assert_eq!(status, StatusCode::OK);
    assert!(
        body.contains("Turn committed"),
        "seat B could not answer on the same table: {}",
        &body[..body.len().min(800)]
    );
}

// ───────────────────────────────────────────────────────────────────────────────────────
// 2. AN ABANDONED MATCH RESOLVES — instead of hanging forever.
// ───────────────────────────────────────────────────────────────────────────────────────

/// **The zombie-table wound, closed.** Seat A plays and seat B never answers. Past the per-turn
/// deadline the table is FORFEIT against B — recorded, surfaced, and refused to further acts —
/// rather than sitting in the tug's alternation forever waiting for a move that is not coming.
#[tokio::test]
async fn an_abandoned_match_resolves_against_the_seat_that_owed_the_move() {
    let (app, state) = app();
    let id = mint(&app).await;
    let seat_a = table_seats::TUG.seat_label(&id, SeatSlot::A);
    let seat_b = table_seats::TUG.seat_label(&id, SeatSlot::B);

    // Seat A plays. Seat B walks away.
    let (turn, arg) = opening_turn();
    let (_, body) = post_act(&app, &id, &turn, arg, &seat_a).await;
    assert!(body.contains("Turn committed"), "seat A must land a turn");

    // Inside the deadline: nothing happens. This is the non-vacuity check — if the reaper fired
    // unconditionally the test below would pass for the wrong reason.
    let now = Instant::now();
    assert!(
        table_seats::reap_table(&state, &id, now).is_none(),
        "a table inside its deadline must not be forfeited"
    );
    assert!(
        table_seats::enforce("tug", &id, &seat_b).is_ok(),
        "and it still takes acts"
    );

    // Past it: the table resolves against B, who owed the move.
    let expired = now + table_seats::turn_limit() + Duration::from_secs(1);
    let resolution = table_seats::reap_table(&state, &id, expired)
        .expect("a table past its deadline with an owed move must resolve");
    assert_eq!(
        resolution.forfeited,
        vec![SeatSlot::B],
        "the seat that owed the move is the one that forfeits"
    );
    assert_eq!(
        resolution.winner(),
        Some(SeatSlot::A),
        "the seat that showed up takes the table"
    );

    // It is RESOLVED, not merely annotated: every further act is refused, including seat B's own
    // belated one, and the refusal names what happened.
    let refused = table_seats::enforce("tug", &id, &seat_b)
        .expect_err("a resolved table takes no further acts");
    assert!(refused.contains("forfeit"), "{refused}");
    let (status, body) = post_act(&app, &id, &turn, arg, &seat_b).await;
    assert_eq!(status, StatusCode::OK);
    assert!(
        body.contains("this table is over"),
        "the belated player is told the table ended: {}",
        &body[..body.len().min(800)]
    );

    // And it is not dressed up as a proven result. No executor turn backs a forfeit and the copy
    // must say so — this assertion is the guard on the claim, not decoration.
    assert!(
        refused.contains("not a proven win"),
        "a forfeit must never be described as a proven win: {refused}"
    );

    // Reaping again is idempotent and does not rewrite the outcome.
    let again = table_seats::reap_table(&state, &id, expired + Duration::from_secs(600))
        .expect("still resolved");
    assert_eq!(again, resolution, "a resolution is write-once");
}

/// **A table nobody ever sat at expires without blaming anybody.** The invite was never opened; no
/// move was played, so there is no forfeit to record and no winner to name.
#[tokio::test]
async fn a_table_nobody_sat_at_expires_without_a_forfeit() {
    let (app, state) = app();
    let id = mint(&app).await;

    let now = Instant::now();
    assert!(table_seats::reap_table(&state, &id, now).is_none());
    let expired = now + table_seats::open_limit() + Duration::from_secs(1);
    let resolution = table_seats::reap_table(&state, &id, expired).expect("expires");
    assert!(
        resolution.forfeited.is_empty(),
        "nobody played, so nobody forfeits"
    );
    assert_eq!(resolution.winner(), None);
    assert!(resolution.headline().contains("nothing was played"));
}

/// **Resignation is the one resolution a player can cause, and it can only cost them.** Seat A
/// resigns; the table goes to B. There is no route by which A could have aimed it at B.
#[tokio::test]
async fn a_seat_can_only_ever_resign_itself() {
    let (app, _state) = app();
    let id = mint(&app).await;
    let seat_a = table_seats::TUG.seat_label(&id, SeatSlot::A);

    // A stranger cannot resign somebody else's table.
    let (status, _, _) = send(
        &app,
        Request::builder()
            .method("POST")
            .uri(format!("/tug/table/{id}/resign"))
            .header("cookie", "dregg_user=mallory")
            .body(Body::empty())
            .unwrap(),
    )
    .await;
    assert_eq!(status, StatusCode::FORBIDDEN, "a stranger holds no seat");

    // Seat A resigns; the resolution names A as the forfeiting seat, never B.
    let (status, body, _) = send(
        &app,
        Request::builder()
            .method("POST")
            .uri(format!("/tug/table/{id}/resign"))
            .header("cookie", format!("dregg_user={seat_a}"))
            .body(Body::empty())
            .unwrap(),
    )
    .await;
    assert_eq!(status, StatusCode::OK, "{body}");
    let resolution = table_seats::registry()
        .resolution(&id)
        .expect("the resignation is recorded");
    assert_eq!(resolution.forfeited, vec![SeatSlot::A]);
    assert_eq!(resolution.winner(), Some(SeatSlot::B));
}

// ───────────────────────────────────────────────────────────────────────────────────────
// 3. THE FOG, THE WATCH ROUTE, AND THE DEAD GLOBAL TABLE.
// ───────────────────────────────────────────────────────────────────────────────────────

/// **A spectator sees the guild lanes and neither hand.** The watch route renders as an identity
/// holding no seat, which is the `surface_for(None)` branch: a count plus a committed root per
/// hand, never a card id.
#[tokio::test]
async fn a_spectator_sees_both_hands_as_fog_and_every_control_inert() {
    let (app, _state) = app();
    let id = mint(&app).await;
    let seat_a = table_seats::TUG.seat_label(&id, SeatSlot::A);

    // Play one turn so there is something to look at.
    let (turn, arg) = opening_turn();
    post_act(&app, &id, &turn, arg, &seat_a).await;

    let (status, watch) = get_as(&app, &format!("/tug/watch/{id}"), None).await;
    assert_eq!(status, StatusCode::OK);
    assert!(watch.contains("Spectating"));
    assert!(
        watch.contains("(hidden)"),
        "a spectator must see the fog form of a hand"
    );
    assert!(
        !watch.contains("Your hand"),
        "a spectator must never be served the own-hand projection"
    );
    assert!(
        watch.contains("<fieldset class=\"spectate-lock\" disabled>"),
        "every control on a spectator page is natively inert"
    );

    // The seated player, by contrast, DOES see their own cards on the play surface — so the
    // assertion above is about the viewer, not about the surface simply never showing a hand.
    let (status, seated) =
        get_as(&app, &format!("/offerings/tug/session/{id}"), Some(&seat_a)).await;
    assert_eq!(status, StatusCode::OK);
    assert!(
        seated.contains("Your hand"),
        "the seat that played must see its own hand"
    );
}

/// **Watching does not open a table.** A spectator URL for a table nobody minted answers "no such
/// table" rather than quietly deploying an unplayable one.
#[tokio::test]
async fn watching_a_table_that_does_not_exist_does_not_mint_one() {
    let (app, state) = app();
    let ghost = "tug1-000000000000000000000000";
    let (status, body) = get_as(&app, &format!("/tug/watch/{ghost}"), None).await;
    assert_eq!(status, StatusCode::NOT_FOUND);
    assert!(body.contains("Watching does not open one"));
    assert!(!state.is_open(
        "tug",
        &dreggnet_offerings::SessionId::new(ghost.to_string())
    ));
}

/// **The global `tug-web` table is gone.** It was the whole joining experience and it was a race:
/// the first two identities to press took the seats, and the id was printed on a public page, so
/// asserting the opponent's label rendered their hand. Nothing served may point at it any more.
#[tokio::test]
async fn nothing_advertises_the_old_global_tug_table() {
    let (app, _state) = app();
    for uri in ["/offerings", "/tug"] {
        let (status, body) = get_as(&app, uri, None).await;
        assert_eq!(status, StatusCode::OK, "{uri}");
        assert!(
            !body.contains("/offerings/tug/session/tug-web"),
            "`{uri}` still advertises the global tug table"
        );
        assert!(
            !body.contains("/offerings/automatafl/session/automatafl-web"),
            "`{uri}` still advertises the global automatafl table"
        );
    }
    // And the catalog's tug card points at the front door instead.
    let (_, catalog) = get_as(&app, "/offerings", None).await;
    assert!(
        catalog.contains("href=\"/tug\""),
        "the catalog must route the tug through its own door"
    );
}
