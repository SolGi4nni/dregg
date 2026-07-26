//! **THE DESCENT'S DOOR, DRIVEN** — the flagship game was unplayable for every visitor, and this is
//! the suite that says so out loud and keeps it said.
//!
//! ## What was broken
//!
//! Every server-side play CTA on the product pointed at ONE fixed session id,
//! `/offerings/descent/session/descent-web`. A native Descent binds its player on the first move
//! that LANDS (`NativeDescentOffering::advance` writes `session.actor` once, then refuses every
//! other identity with the shared wrong-player sentence). So the first person who ever took a turn
//! there owned the product's front door permanently: two independent fresh browsers, measured on the
//! live deployment, were both refused, and the board they landed on carried dimmed controls and no
//! control anywhere that opened a run of their own. *"Start today's run →"* could not start a run.
//!
//! ## What is pinned here, and in which direction
//!
//! Every leg drives the REAL merged app (`make_app`, axum `oneshot`) through
//! [`common::guard`], so a move that never reached the executor kills the test instead of coasting.
//!
//! 1. [`the_shared_demo_run_is_claimed_by_its_first_mover`] — the MECHANISM, reproduced. This is the
//!    non-vacuity control for everything below: without it, "the door gives you your own run" could
//!    pass on a game that had no ownership at all.
//! 2. [`a_stranger_on_a_claimed_run_is_told_and_is_handed_a_door`] — the state ember measured. The
//!    guard still refuses (it must: it is what makes a run mean anything), the board no longer paints
//!    a single pressable control, and the page carries the way out.
//! 3. [`a_fresh_visitor_opens_a_run_takes_a_turn_and_gets_a_receipt`] — the end-to-end proof, from a
//!    cookie-less browser to a committed turn with a replay-verification strip on it.
//! 4. [`two_fresh_visitors_get_two_different_runs`] — the property the shared session did not have.
//! 5. [`pressing_the_door_twice_resumes_rather_than_opening_a_second_run`] — the door is a
//!    navigation, not a mint.
//! 6. [`a_finished_run_advances_the_door_to_the_next_one`] — `flee` settles a run; the next press
//!    gives a new board rather than the dead one.
//! 7. [`every_play_cta_points_at_the_door_and_none_at_the_shared_session`] — the routing repair, at
//!    every CTA on the product at once.
//! 8. [`an_unestablished_name_opens_no_run`] — the flood backstop, since the address is derived from
//!    the label.

use axum::Router;
use axum::body::Body;
use axum::http::{Request, StatusCode, header};
use dreggnet_web::descent_door::{DEMO_RUN, DESCENT_RUN_PATH, RUN_PREFIX, is_own_run};
use dreggnet_web::{DESCENT_PLAY_PATH, make_app};
use tower::ServiceExt; // oneshot

mod common;

/// The real merged app, with a verified Descent day published.
///
/// ⚑ **THE DAY IS NOT OPTIONAL AND NOT A FIXTURE HACK.** `make_app` builds its host through
/// `dreggnet_catalog::CatalogConfig::live`, which binds a run's banked-relic provenance to the
/// CURRENT verified beacon day and REFUSES to open a Descent until one has been published — a live
/// surface must not serve a pre-computable provenance root because a beacon fetch has not landed.
/// The serving binary publishes it at boot (`arm_todays_descent_day`, over the network); a test
/// process publishes the pinned, BLS-verifiable reveal instead, exactly as every other Descent web
/// suite here does (`game_session_coherence`, `catalog_flow_harness`, `descent_campaign_catalog`).
/// Without it every leg below would be measuring a 409, not a game.
fn app() -> Router {
    dreggnet_catalog::publish_pinned_descent_day().expect("the pinned published round verifies");
    common::guard(make_app())
}

/// A GET carrying an optional raw cookie, handing back the status, the `Location`, the minted
/// `Set-Cookie` and the body — everything a browser would act on.
struct Hit {
    status: StatusCode,
    location: Option<String>,
    set_cookie: Option<String>,
    body: String,
}

async fn get(app: &Router, uri: &str, cookie: Option<&str>) -> Hit {
    let mut builder = Request::builder().uri(uri);
    if let Some(cookie) = cookie {
        builder = builder.header(header::COOKIE, cookie);
    }
    let response = app
        .clone()
        .oneshot(builder.body(Body::empty()).unwrap())
        .await
        .expect("the app responds");
    let status = response.status();
    let header_str = |name: header::HeaderName| {
        response
            .headers()
            .get(name)
            .and_then(|v| v.to_str().ok())
            .map(str::to_string)
    };
    let location = header_str(header::LOCATION);
    let set_cookie = header_str(header::SET_COOKIE);
    let bytes = axum::body::to_bytes(response.into_body(), usize::MAX)
        .await
        .expect("a bounded body");
    Hit {
        status,
        location,
        set_cookie,
        body: String::from_utf8_lossy(&bytes).to_string(),
    }
}

/// The `dregg_user=…` pair out of a `Set-Cookie`, ready to send back as a `Cookie` header.
fn cookie_of(set_cookie: &str) -> String {
    set_cookie
        .split(';')
        .next()
        .expect("a cookie has a first pair")
        .trim()
        .to_string()
}

/// **Walk a cookie-less browser through the door**, returning `(cookie, run session id)` — the two
/// things every leg below needs. The cookie is the one the bootstrap minted on this very request,
/// which is what makes this a genuinely fresh visitor rather than a hand-named one.
async fn open_a_run(app: &Router) -> (String, String) {
    let hit = get(app, DESCENT_RUN_PATH, None).await;
    assert_eq!(
        hit.status,
        StatusCode::SEE_OTHER,
        "the door sends a browser to a run: {}",
        hit.body
    );
    let cookie = cookie_of(
        &hit.set_cookie
            .expect("a cookie-less browser is given a name it can come back with"),
    );
    let location = hit.location.expect("the door names the run it opened");
    let id = location
        .rsplit_once('/')
        .expect("a session location has a last segment")
        .1
        .to_string();
    assert!(
        is_own_run(&id),
        "the door opens a run of the reader's own, not a shared one: {location}"
    );
    assert_eq!(location, format!("/offerings/descent/session/{id}"));
    (cookie, id)
}

/// Every act the page offers, with `enabled` read off the rendered form.
fn offered(html: &str) -> Vec<common::OfferedAct> {
    common::offered_acts(html)
}

/// The first act the page offers that a browser could actually press.
fn first_enabled(html: &str) -> Option<common::OfferedAct> {
    offered(html).into_iter().find(|act| act.enabled)
}

// ─────────────────────────────────────────────────────────────────────────────────────────
// 1 + 2. THE MECHANISM, AND THE STATE IT LEFT A STRANGER IN
// ─────────────────────────────────────────────────────────────────────────────────────────

/// ⚑ **THE ROOT CAUSE, REPRODUCED.** One turn in the shared demo session binds it forever. This is
/// the control that keeps every "the door gives you your own run" assertion below from being a
/// statement about a game with no ownership at all.
#[tokio::test]
async fn the_shared_demo_run_is_claimed_by_its_first_mover() {
    let app = app();
    let base = format!("/offerings/descent/session/{DEMO_RUN}");
    let act = format!("{base}/act");

    let (status, page) = common::get_with_cookie(&app, &base, Some("dregg_user=first")).await;
    assert_eq!(status, StatusCode::OK);
    assert!(
        page.contains("unclaimed"),
        "before anybody moves, the run says it is unclaimed: {page}"
    );
    let opening = first_enabled(&page).expect("an unclaimed run offers a move");

    let (status, landed) = common::post_act(&app, &act, &opening.turn, opening.arg, "first").await;
    assert_eq!(status, StatusCode::OK, "{landed}");
    assert!(
        landed.contains("Turn committed"),
        "the first mover's turn must actually land, or the claim below is about nothing: {landed}"
    );

    // A second browser presses the same control it is served.
    let (status, page) = common::get_with_cookie(&app, &base, Some("dregg_user=second")).await;
    assert_eq!(status, StatusCode::OK);
    let refused_act = offered(&page)
        .into_iter()
        .next()
        .expect("the board still paints its moves");
    let (status, refusal) =
        common::post_act(&app, &act, &refused_act.turn, refused_act.arg, "second").await;
    assert_eq!(status, StatusCode::OK, "{refusal}");
    assert!(
        refusal.contains("belongs to a different player"),
        "the run is bound to whoever moved first: {refusal}"
    );
}

/// ⚑ **THE MEASURED STATE, AND BOTH HALVES OF ITS REPAIR.** A stranger on a claimed run is still
/// refused — the guard is the thing that makes a run somebody's, and weakening it was never the fix —
/// but the page no longer paints a single pressable control it will only refuse, and it no longer
/// leaves the reader with nowhere to go.
#[tokio::test]
async fn a_stranger_on_a_claimed_run_is_told_and_is_handed_a_door() {
    let app = app();
    let base = format!("/offerings/descent/session/{DEMO_RUN}");
    let act = format!("{base}/act");

    // ⚑ The status is asserted before the affordance count, or a refusal page (which carries no
    // forms at all) would satisfy "not one pressable control" without the guard being involved.
    let (status, page) = common::get_with_cookie(&app, &base, Some("dregg_user=owner")).await;
    assert_eq!(status, StatusCode::OK, "the demo run serves: {page}");
    let opening = first_enabled(&page).expect("an unclaimed run offers a move");
    let (_, landed) = common::post_act(&app, &act, &opening.turn, opening.arg, "owner").await;
    assert!(landed.contains("Turn committed"), "{landed}");

    let (status, stranger) =
        common::get_with_cookie(&app, &base, Some("dregg_user=stranger")).await;
    assert_eq!(status, StatusCode::OK);

    // (a) NOT ONE PRESSABLE CONTROL. `actions_for` always dimmed a non-owner's affordances, but
    //     `render` built its menu from `actions`, so the painted board offered live buttons that
    //     could only ever refuse. `NativeDescentOffering::render_for` closes that.
    let pressable: Vec<String> = offered(&stranger)
        .into_iter()
        .filter(|a| a.enabled)
        .map(|a| a.label)
        .collect();
    assert!(
        pressable.is_empty(),
        "a board that is not yours must not paint a control that works: {pressable:?}"
    );
    assert!(
        !offered(&stranger).is_empty(),
        "…and the moves are still SHOWN, dimmed: a blank page would pass the line above vacuously"
    );

    // (b) AND THE WAY OUT IS ON THE PAGE.
    assert!(
        stranger.contains(&format!("href=\"{DESCENT_RUN_PATH}\"")),
        "the stranded reader is handed a run of their own: {stranger}"
    );
    assert!(
        stranger.contains("not yours"),
        "the page says whose run this is: {stranger}"
    );

    // (c) THE GUARD IS UNTOUCHED. It still refuses a crafted press.
    let any = offered(&stranger)
        .into_iter()
        .next()
        .expect("the board paints its moves");
    let (_, refusal) = common::post_act(&app, &act, &any.turn, any.arg, "stranger").await;
    assert!(
        refusal.contains("belongs to a different player"),
        "the ownership check must still hold: {refusal}"
    );

    // …and the OWNER's own board is unaffected: it still offers a pressable move.
    let (_, owner_page) = common::get_with_cookie(&app, &base, Some("dregg_user=owner")).await;
    assert!(
        first_enabled(&owner_page).is_some(),
        "dimming a stranger's board must not dim the owner's: {owner_page}"
    );
}

// ─────────────────────────────────────────────────────────────────────────────────────────
// 3 - 6. THE DOOR
// ─────────────────────────────────────────────────────────────────────────────────────────

/// ⚑ **THE WHOLE ASK, DRIVEN: a stranger arrives, presses the CTA, plays, and holds a receipt.**
#[tokio::test]
async fn a_fresh_visitor_opens_a_run_takes_a_turn_and_gets_a_receipt() {
    let app = app();
    let (cookie, id) = open_a_run(&app).await;

    let hit = get(
        &app,
        &format!("/offerings/descent/session/{id}"),
        Some(&cookie),
    )
    .await;
    assert_eq!(hit.status, StatusCode::OK, "the run serves: {}", hit.body);
    assert!(
        hit.body.contains("Your own run")
            && hit.body.contains("belongs to the browser that opened it"),
        "the board says whose it is: {}",
        hit.body
    );
    let opening = first_enabled(&hit.body).expect("a fresh run offers a move to its owner");

    let (status, landed) = common::post_act_with_cookie(
        &app,
        &format!("/offerings/descent/session/{id}/act"),
        &opening.turn,
        opening.arg,
        &cookie,
    )
    .await;
    assert_eq!(status, StatusCode::OK, "{landed}");
    assert!(
        landed.contains("Turn committed"),
        "the visitor's own move LANDS: {landed}"
    );
    // The receipt strip, and the audit affordance beside it that re-runs the whole chain.
    assert!(
        landed.contains(&format!("/offerings/descent/session/{id}/verify")),
        "the turn carries the replay-verification control: {landed}"
    );
    let (status, verified) = common::get_with_cookie(
        &app,
        &format!("/offerings/descent/session/{id}/verify"),
        Some(&cookie),
    )
    .await;
    assert_eq!(status, StatusCode::OK, "{verified}");
    assert!(
        verified.contains("\"verified\":true"),
        "the run re-verifies by replay: {verified}"
    );
}

/// ⚑ **THE PROPERTY THE SHARED SESSION DID NOT HAVE.** Two fresh browsers, two runs, and the second
/// one can move.
#[tokio::test]
async fn two_fresh_visitors_get_two_different_runs() {
    let app = app();
    let (first_cookie, first_id) = open_a_run(&app).await;
    let (second_cookie, second_id) = open_a_run(&app).await;
    assert_ne!(
        first_id, second_id,
        "a run is per browser, not one board for the whole deployment"
    );

    for (cookie, id) in [(&first_cookie, &first_id), (&second_cookie, &second_id)] {
        let hit = get(
            &app,
            &format!("/offerings/descent/session/{id}"),
            Some(cookie),
        )
        .await;
        let opening = first_enabled(&hit.body).expect("each visitor's own run offers a move");
        let (status, landed) = common::post_act_with_cookie(
            &app,
            &format!("/offerings/descent/session/{id}/act"),
            &opening.turn,
            opening.arg,
            cookie,
        )
        .await;
        assert_eq!(status, StatusCode::OK, "{landed}");
        assert!(
            landed.contains("Turn committed"),
            "the SECOND visitor is not refused by the first one's claim: {landed}"
        );
    }
}

/// ⚑ **THE DOOR IS A NAVIGATION, NOT A MINT.** Pressing the CTA again mid-run brings you back to the
/// run you are in; it does not abandon it for a fresh board.
#[tokio::test]
async fn pressing_the_door_twice_resumes_rather_than_opening_a_second_run() {
    let app = app();
    let (cookie, id) = open_a_run(&app).await;
    let hit = get(
        &app,
        &format!("/offerings/descent/session/{id}"),
        Some(&cookie),
    )
    .await;
    let opening = first_enabled(&hit.body).expect("a move");
    let (_, landed) = common::post_act_with_cookie(
        &app,
        &format!("/offerings/descent/session/{id}/act"),
        &opening.turn,
        opening.arg,
        &cookie,
    )
    .await;
    assert!(landed.contains("Turn committed"), "{landed}");

    let again = get(&app, DESCENT_RUN_PATH, Some(&cookie)).await;
    assert_eq!(again.status, StatusCode::SEE_OTHER);
    assert_eq!(
        again.location.as_deref(),
        Some(format!("/offerings/descent/session/{id}").as_str()),
        "a second press returns the reader to the run they are already in"
    );
}

/// ⚑ **A FINISHED RUN IS NOT A DEAD END.** `flee` is the Descent's terminal settlement: it ends the
/// run and the offering then offers nothing at all. The next press of the same CTA has to be a new
/// board, or the door would hand a player who finished exactly the dead end it exists to remove.
#[tokio::test]
async fn a_finished_run_advances_the_door_to_the_next_one() {
    let app = app();
    let (cookie, id) = open_a_run(&app).await;
    let act = format!("/offerings/descent/session/{id}/act");

    let hit = get(
        &app,
        &format!("/offerings/descent/session/{id}"),
        Some(&cookie),
    )
    .await;
    let flee = offered(&hit.body)
        .into_iter()
        .find(|a| a.turn == "flee" && a.enabled)
        .expect("a fresh run can always end itself");
    let (status, ended) =
        common::post_act_with_cookie(&app, &act, &flee.turn, flee.arg, &cookie).await;
    assert_eq!(status, StatusCode::OK, "{ended}");
    assert!(ended.contains("Turn committed"), "{ended}");

    let settled = get(
        &app,
        &format!("/offerings/descent/session/{id}"),
        Some(&cookie),
    )
    .await;
    assert!(
        offered(&settled.body).is_empty(),
        "a settled run offers no further move, which is what the door reads: {}",
        settled.body
    );

    let next = get(&app, DESCENT_RUN_PATH, Some(&cookie)).await;
    assert_eq!(next.status, StatusCode::SEE_OTHER);
    let next_id = next
        .location
        .as_deref()
        .and_then(|l| l.rsplit_once('/'))
        .map(|(_, id)| id.to_string())
        .expect("the door names a run");
    assert_ne!(next_id, id, "a finished run must not be served as a start");
    assert!(next_id.starts_with(RUN_PREFIX));
    let fresh = get(
        &app,
        &format!("/offerings/descent/session/{next_id}"),
        Some(&cookie),
    )
    .await;
    assert!(
        first_enabled(&fresh.body).is_some(),
        "and the run it opened is playable: {}",
        fresh.body
    );
}

// ─────────────────────────────────────────────────────────────────────────────────────────
// 7 + 8. THE ROUTING, AND THE BACKSTOP
// ─────────────────────────────────────────────────────────────────────────────────────────

/// ⚑ **EVERY PLAY CTA ON THE PRODUCT AT ONCE.** The landing, the catalog and the play page each
/// carry a route to a run of the reader's own, and NOTHING anywhere still sends a player at the one
/// shared session. This is the leg that would have caught the original defect.
#[tokio::test]
async fn every_play_cta_points_at_the_door_and_none_at_the_shared_session() {
    let app = app();
    let shared = format!("/offerings/descent/session/{DEMO_RUN}");
    // ⚑ Keyed on the ANCHOR, not on the bare path. The served stylesheet carries a design comment
    // quoting that URL (it is where a 390px measurement was taken), so a substring test would be
    // red on prose and would have to be softened into uselessness.
    let cta = format!("href=\"{shared}\"");

    for (page, what) in [
        ("/", "the landing"),
        ("/offerings", "the catalog"),
        (DESCENT_PLAY_PATH, "the play page"),
        ("/guide", "the guide"),
    ] {
        let hit = get(&app, page, None).await;
        assert_eq!(hit.status, StatusCode::OK, "{what} serves");
        assert!(
            !hit.body.contains(&cta),
            "{what} still sends a player at the shared session"
        );
    }

    // The play page is where the two loudest CTAs live ("Start today's run →" and the `<noscript>`
    // fallback), and both are the door now.
    let play = get(&app, DESCENT_PLAY_PATH, None).await;
    assert!(
        play.body.contains(&format!("href=\"{DESCENT_RUN_PATH}\"")),
        "the play page's primary CTA is the door: {}",
        play.body
    );
    assert!(
        play.body.contains("Start today's run"),
        "…and it still says what it does: {}",
        play.body
    );
    // ⚑ The CTA's own claim, checked rather than assumed: pressing exactly what the page links
    // opens a run.
    let (_, id) = open_a_run(&app).await;
    assert!(is_own_run(&id));

    // The catalog card reaches the same door.
    let catalog = get(&app, "/offerings", None).await;
    assert!(
        catalog
            .body
            .contains(&format!("href=\"{DESCENT_RUN_PATH}\"")),
        "the catalog's Descent card opens a run of your own: {}",
        catalog.body
    );

    // And the demo session, if somebody still reaches it, says what it is rather than pretending.
    let demo = get(&app, &shared, None).await;
    assert_eq!(demo.status, StatusCode::OK);
    assert!(
        demo.body.contains("demo run") && demo.body.contains(DESCENT_RUN_PATH),
        "the old front door names itself and points at the new one: {}",
        demo.body
    );
}

/// ⚑ **THE FLOOD BACKSTOP.** The run address is a pure function of the browser's label, so a caller
/// who may choose the label at will could open a bounded number of hosted worlds per invented name,
/// without bound. Only the durable cookie this server minted opens a run.
#[tokio::test]
async fn an_unestablished_name_opens_no_run() {
    let app = app();
    let hit = get(&app, &format!("{DESCENT_RUN_PATH}?user=invented"), None).await;
    assert_eq!(
        hit.status,
        StatusCode::FORBIDDEN,
        "an asserted name opens nothing: {}",
        hit.body
    );
    assert!(hit.location.is_none(), "and it is sent at no run");
    assert!(
        hit.body.contains("nothing was opened"),
        "the refusal says what was and was not done: {}",
        hit.body
    );

    // The positive control: the SAME name, backed by the cookie, is established and does open one.
    let hit = get(
        &app,
        &format!("{DESCENT_RUN_PATH}?user=invented"),
        Some("dregg_user=invented"),
    )
    .await;
    assert_eq!(
        hit.status,
        StatusCode::SEE_OTHER,
        "a name the browser actually holds is not the refused case: {}",
        hit.body
    );
}
