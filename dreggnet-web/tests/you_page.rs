//! **`GET /you` — the page where a player sees their own record, driven end to end.**
//!
//! The gap this closes was measured, not guessed: there was no `/me`, `/you`, `/account`,
//! `/profile` or `/stats` anywhere on the surface, so the one identity-shaped endpoint a player
//! could reach was `/metrics` (Prometheus, for operators). A player who closed the tab had no way
//! back to their table, and no way to see their own history on a daily board that prints their name.
//!
//! What this file pins, in the order it matters:
//!
//! 1. **THE PRIVACY TOOTH.** `?user=` is attacker-choosable on this surface — the code says so
//!    outright — so a page made entirely of "your games" must refuse it. Driven adversarially: a
//!    victim really lands a turn, then an attacker asks for the victim's page and gets `403` with
//!    the victim's session id NOWHERE in the body. Non-vacuous, because the same request WITH the
//!    victim's own cookie does show it.
//! 2. **The seat join.** A minted automatafl table appears on its seat-holder's page after the seat
//!    link and BEFORE any move — the join is the seat secret, not a move.
//! 3. **The actor join.** A landed turn puts its session on that identity's page, with the resume
//!    link and the existing replay-verify link.
//! 4. **The board join.** A Descent run recorded under the viewer's label appears with its existing
//!    run-card link; a run under a neighbouring label does NOT.
//! 5. **The empty states are prose.** A brand-new visitor is told what is empty and where to start,
//!    never handed a blank panel.
//! 6. **No credential is echoed.** The `dregg_user` value is a bearer credential here (`?user=`
//!    replays it, and for a table it IS the seat key), so it must not appear in the page.

use std::sync::Arc;

use axum::body::Body;
use axum::http::{Request, StatusCode, header};
use dreggnet_offerings::DreggIdentity;
use dreggnet_offerings::character::{CharacterStore, InMemoryCharacterStore};
use dreggnet_offerings::daily_descent::{
    CORRIDOR_ON, DailyDescentOffering, DailyRun, GATE_HEAL, GATE_MEASURED, GATE_PRESS, HOARD_FORCE,
    HOARD_SEIZE, KEY_TAKE,
};
use dreggnet_web::automatafl_web::{self, SeatSlot};
use dreggnet_web::{CatalogState, DescentState, catalog_router, descent_router, you_router};
use dungeon_on_dregg::progression::WARRIOR;
use procgen_dregg::daily_seed;
use tower::ServiceExt; // oneshot

mod common;

/// The merged surface under test: the catalog rails (so a turn can really land), the automatafl
/// front door (so a table can really be minted and sat at), the Descent board (so a run card
/// really exists to link to) and the YOU page over the SAME two states.
fn app_with(descent: Arc<DescentState>) -> axum::Router {
    let catalog = Arc::new(CatalogState::new());
    common::guard(
        catalog_router(Arc::clone(&catalog))
            .merge(automatafl_web::automatafl_router(Arc::clone(&catalog)))
            .merge(descent_router(Arc::clone(&descent)))
            .merge(you_router(catalog, descent)),
    )
}

fn app() -> axum::Router {
    app_with(Arc::new(DescentState::new()))
}

struct Reply {
    status: StatusCode,
    body: String,
    set_cookie: Option<String>,
    cache_control: Option<String>,
}

async fn get(app: &axum::Router, uri: &str, cookie: Option<&str>) -> Reply {
    let mut builder = Request::builder().uri(uri);
    if let Some(cookie) = cookie {
        builder = builder.header(header::COOKIE, cookie);
    }
    let response = app
        .clone()
        .oneshot(builder.body(Body::empty()).unwrap())
        .await
        .expect("the request is served");
    let status = response.status();
    let header_of = |name: header::HeaderName| {
        response
            .headers()
            .get(name)
            .and_then(|value| value.to_str().ok())
            .map(str::to_string)
    };
    let set_cookie = header_of(header::SET_COOKIE);
    let cache_control = header_of(header::CACHE_CONTROL);
    let bytes = axum::body::to_bytes(response.into_body(), usize::MAX)
        .await
        .expect("the body reads");
    Reply {
        status,
        body: String::from_utf8_lossy(&bytes).to_string(),
        set_cookie,
        cache_control,
    }
}

async fn post(app: &axum::Router, uri: &str) -> Reply {
    post_as(app, uri, None).await
}

/// [`post`] carrying a cookie — the seat-bearing routes (`…/resign`) authorise off the browser's
/// `dregg_user`, so a test that means to act AS a seat has to present it.
async fn post_as(app: &axum::Router, uri: &str, cookie: Option<&str>) -> Reply {
    let mut builder = Request::builder().method("POST").uri(uri);
    if let Some(cookie) = cookie {
        builder = builder.header(header::COOKIE, cookie);
    }
    let response = app
        .clone()
        .oneshot(builder.body(Body::empty()).unwrap())
        .await
        .expect("the request is served");
    let status = response.status();
    let bytes = axum::body::to_bytes(response.into_body(), usize::MAX)
        .await
        .expect("the body reads");
    Reply {
        status,
        body: String::from_utf8_lossy(&bytes).to_string(),
        set_cookie: None,
        cache_control: None,
    }
}

/// The `{turn, arg}` of the first ENABLED affordance the server itself painted. **Derived, never a
/// literal**: a tug session's schedule is seeded from its session id, so the opening decision (and
/// therefore its dispatch method) differs per table — a hardcoded `comp 3` is refused as "method
/// `comp` does not name decision 3" on most ids, and every assertion downstream of it then checks
/// nothing. A dimmed affordance wears `class="affordance dimmed"`, an argument box
/// `class="affordance input"`, and a free-text affordance `class="affordance text"` — so matching the
/// BARE class picks a move that is both actually offered AND landable from a plain `turn=&arg=` POST,
/// which is exactly what this helper's callers then send.
fn first_enabled_move(html: &str) -> Option<(String, i64)> {
    let (_, after) = html.split_once("<form class=\"affordance\" ")?;
    let (_, turn_at) = after.split_once("name=\"turn\" value=\"")?;
    let (turn, rest) = turn_at.split_once('"')?;
    let (_, arg_at) = rest.split_once("name=\"arg\" value=\"")?;
    let (arg, _) = arg_at.split_once('"')?;
    Some((turn.to_string(), arg.parse().ok()?))
}

/// **Land one real turn** on an ad-hoc (NOT seat-locked) tug session as `user`, and refuse to
/// continue unless it actually committed. An ad-hoc session id carries no seat lock, so the first
/// two distinct actors simply claim seats A and B.
async fn land_a_turn(app: &axum::Router, session: &str, user: &str) {
    let cookie = format!("dregg_user={user}");
    let opened = get(
        app,
        &format!("/offerings/tug/session/{session}"),
        Some(&cookie),
    )
    .await;
    assert_eq!(opened.status, StatusCode::OK, "{}", opened.body);
    let (turn, arg) = first_enabled_move(&opened.body)
        .unwrap_or_else(|| panic!("the tug surface offered this seat no move: {}", opened.body));
    let (status, body) = common::post_act(
        app,
        &format!("/offerings/tug/session/{session}/act"),
        &turn,
        arg,
        user,
    )
    .await;
    assert_eq!(status, StatusCode::OK, "{body}");
    assert!(
        body.contains("Turn committed"),
        "the turn every assertion below depends on did NOT land ({turn} {arg}): {body}"
    );
}

/// The `href` of the first anchor whose target starts with `prefix`.
fn first_href(html: &str, prefix: &str) -> Option<String> {
    let mut rest = html;
    while let Some((_, after)) = rest.split_once("href=\"") {
        let (href, tail) = after.split_once('"')?;
        if href.starts_with(prefix) {
            return Some(href.replace("&amp;", "&"));
        }
        rest = tail;
    }
    None
}

// ═══════════════════════════════════════════════════════════════════════════════
// 1. THE PRIVACY TOOTH — `?user=` cannot read anybody's page.
// ═══════════════════════════════════════════════════════════════════════════════

/// **The adversarial one.** A victim lands a real turn (so there IS something to steal), then an
/// attacker asks for the victim's page by asserting the victim's label. The refusal is flat and the
/// victim's session id does not appear anywhere in the response — and the same lookup with the
/// victim's OWN cookie proves the assertion is not passing because the shelf was empty.
#[tokio::test]
async fn an_asserted_user_cannot_read_another_players_page() {
    let app = app();
    let victim = "you-victim";
    let session = "you-victim-table";

    // Open the victim's session and land one real turn as them.
    land_a_turn(&app, session, victim).await;

    // NON-VACUITY: the victim's own page really does carry the session.
    let mine = get(&app, "/you", Some(&format!("dregg_user={victim}"))).await;
    assert_eq!(mine.status, StatusCode::OK, "{}", mine.body);
    assert!(
        mine.body.contains(session),
        "the victim's own page must show their session, or the theft check below proves nothing: \
         {}",
        mine.body
    );

    // THE ATTACK: assert the victim's label from a browser holding a different cookie.
    let stolen = get(
        &app,
        &format!("/you?user={victim}"),
        Some("dregg_user=you-attacker"),
    )
    .await;
    assert_eq!(
        stolen.status,
        StatusCode::FORBIDDEN,
        "an asserted `?user=` must be refused outright: {}",
        stolen.body
    );
    assert!(
        !stolen.body.contains(session),
        "the victim's session leaked into an asserted read: {}",
        stolen.body
    );
    assert!(
        stolen.body.contains("a claim, not a credential"),
        "the refusal must say WHY: {}",
        stolen.body
    );

    // …and with no cookie at all either (the bootstrap declines to mint one for an explicit
    // `?user=`, so this label is unbacked too).
    let bare = get(&app, &format!("/you?user={victim}"), None).await;
    assert_eq!(bare.status, StatusCode::FORBIDDEN, "{}", bare.body);
    assert!(!bare.body.contains(session), "{}", bare.body);
}

/// Re-asserting the label the cookie ALREADY holds is you, not an impersonation, and must still
/// work — the refusal is aimed at an unbacked label, not at the presence of a query param.
#[tokio::test]
async fn re_asserting_your_own_cookie_is_still_you() {
    let app = app();
    let reply = get(&app, "/you?user=you-self", Some("dregg_user=you-self")).await;
    assert_eq!(reply.status, StatusCode::OK, "{}", reply.body);
    assert!(reply.body.contains("Who you are here"), "{}", reply.body);
}

// ═══════════════════════════════════════════════════════════════════════════════
// 2. THE SEAT JOIN — a table is yours because you hold its seat.
// ═══════════════════════════════════════════════════════════════════════════════

/// Mint a real automatafl table through the real door, take seat A through the real seat link, and
/// then find that table on `/you` — **with no move played**. The join is the seat secret, which only
/// its holder can present, so this is exactly the "I closed the tab" recovery the page exists for.
#[tokio::test]
async fn a_minted_table_appears_on_its_seat_holders_page_before_any_move() {
    let app = app();
    let lobby = post(&app, "/automatafl/table").await;
    assert_eq!(lobby.status, StatusCode::OK, "{}", lobby.body);
    let seat_link =
        first_href(&lobby.body, "/automatafl/table/").expect("the lobby hands out a seat link");
    let table_id = seat_link
        .trim_start_matches("/automatafl/table/")
        .split('?')
        .next()
        .expect("the seat link names its table")
        .to_string();

    // Take the seat exactly as a browser does: the link 303s and installs the seat label as the
    // `dregg_user` cookie.
    let seated = get(&app, &seat_link, None).await;
    assert_eq!(seated.status, StatusCode::SEE_OTHER, "{}", seated.body);
    let cookie = seated
        .set_cookie
        .as_deref()
        .and_then(|value| value.split(';').next())
        .expect("the seat link installs the seat cookie")
        .to_string();

    let page = get(&app, "/you", Some(&cookie)).await;
    assert_eq!(page.status, StatusCode::OK, "{}", page.body);
    assert!(
        page.body.contains(&table_id),
        "the table this browser holds a seat at must be on its page: {}",
        page.body
    );
    assert!(
        page.body
            .contains(&format!("/offerings/automatafl/session/{table_id}")),
        "…with the way back INTO it: {}",
        page.body
    );
    assert!(
        page.body
            .contains(&format!("/offerings/automatafl/session/{table_id}/verify")),
        "…and the existing replay-verify route, not a re-implementation: {}",
        page.body
    );
    assert!(
        page.body.contains("seat A"),
        "the page must say which seat is held: {}",
        page.body
    );
    assert!(
        page.body.contains("0 of 0 landed turns yours"),
        "the seat join must not depend on a move having been played: {}",
        page.body
    );

    // ⚑ THE CREDENTIAL MUST NOT BE ECHOED. The cookie value IS the seat key.
    let seat_label = automatafl_web::seat_label(&table_id, SeatSlot::A);
    assert!(
        !page.body.contains(&seat_label),
        "the seat secret was printed on the page: {}",
        page.body
    );
    assert!(
        page.body.contains("afs1-a-…"),
        "only the label's SHAPE may be shown: {}",
        page.body
    );
    // And a stranger who learns the table id still cannot read that table's page as its seat.
    let stranger = get(&app, "/you", Some("dregg_user=you-stranger")).await;
    assert!(
        !stranger.body.contains(&table_id),
        "a table leaked to a viewer holding neither seat: {}",
        stranger.body
    );
}

// ═══════════════════════════════════════════════════════════════════════════════
// 2b. ⚑ A FINISHED MATCH IS KEPT, LISTED, AND STILL REPLAYABLE.
// ═══════════════════════════════════════════════════════════════════════════════

/// The surface with a **durable session store attached**, which is what the archive needs to exist
/// at all.
///
/// ⚑ This is the detection half of the change, and it is why the test builds its own host instead of
/// using [`CatalogState::new`]: with no resume store the host has nowhere to archive to, so
/// `archived_logs()` is empty and a finished-match assertion would pass vacuously forever. The store
/// is constructed INSIDE the host-thread closure because `InMemoryResumeStore` is `Rc`-backed and
/// never crosses a thread.
fn app_with_a_session_store() -> axum::Router {
    let catalog = Arc::new(CatalogState::with_host(|| {
        dreggnet_web::demo_host()
            .with_resume_store(Box::new(dreggnet_offerings::InMemoryResumeStore::new()))
    }));
    let descent = Arc::new(DescentState::new());
    common::guard(
        catalog_router(Arc::clone(&catalog))
            .merge(automatafl_web::automatafl_router(Arc::clone(&catalog)))
            .merge(you_router(catalog, descent)),
    )
}

/// Every `{turn, arg}` the server painted as a **pressable board cell**, in the order it painted
/// them.
///
/// The automatafl board is a coordgrid: each actionable square is its own `<form class="cell …">`,
/// not a `class="affordance"` row, so `first_enabled_move` above cannot see it. ⚑ This is derived
/// from the live board on purpose — a coordinate literal encodes a world-fact (which square a seat
/// may commit to on this board, at this generation, under these rules) and a literal that encodes a
/// world-fact outlives the world. The caller presses these in order until one commits, so a change
/// to the board's legality does not silently make the test check nothing.
fn board_cells(html: &str) -> Vec<(String, i64)> {
    let mut out = Vec::new();
    let mut rest = html;
    while let Some((_, after)) = rest.split_once("<form class=\"cell") {
        let Some((form, tail)) = after.split_once("</form>") else {
            break;
        };
        let field = |name: &str| -> Option<String> {
            let marker = format!("name=\"{name}\" value=\"");
            Some(form.split_once(&marker)?.1.split_once('"')?.0.to_string())
        };
        if let (Some(turn), Some(arg)) = (
            field("turn"),
            field("arg").and_then(|arg| arg.parse::<i64>().ok()),
        ) {
            out.push((turn, arg));
        }
        rest = tail;
    }
    out
}

/// **Land one real turn as a seated player**, by pressing the cells the SERVER itself painted until
/// one commits. Panics naming the surface if none does — a silently-unlanded turn would make every
/// assertion downstream of it vacuous.
async fn land_a_seated_turn(app: &axum::Router, key: &str, id: &str, cookie: &str) {
    let surface = get(app, &format!("/offerings/{key}/session/{id}"), Some(cookie)).await;
    assert_eq!(surface.status, StatusCode::OK, "{}", surface.body);
    let cells = board_cells(&surface.body);
    assert!(
        !cells.is_empty(),
        "the server painted this seat no pressable cell at all: {}",
        surface.body
    );
    for (turn, arg) in &cells {
        let (status, body) = common::post_act_with_cookie(
            app,
            &format!("/offerings/{key}/session/{id}/act"),
            turn,
            *arg,
            cookie,
        )
        .await;
        if status == StatusCode::OK && body.contains("Turn committed") {
            return;
        }
    }
    panic!(
        "none of the {} cells the server painted as pressable committed — every assertion below \
         would have been vacuous",
        cells.len()
    );
}

/// Mint a real automatafl table through the real door and return `(id, seat-A label, seat-B label)`.
async fn mint_automatafl_table(app: &axum::Router) -> (String, String, String) {
    let lobby = post(app, "/automatafl/table").await;
    assert_eq!(lobby.status, StatusCode::OK, "{}", lobby.body);
    let id = lobby
        .body
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

/// ⚑ **THE WHOLE GAP, END TO END.** A real seat-locked match is played, ended, and then found on its
/// player's own page — and the thing the page links to RE-EXECUTES it.
///
/// Before this, `close` deleted the durable move-log and the table registry was an in-process map, so
/// the moment the match became an artifact was the moment its only record was destroyed. Every clause
/// below was unreachable then:
///
/// 1. a real turn lands (so the archive holds something a replay can check);
/// 2. seat A resigns — the ending is recorded AND the session is retired;
/// 3. the match leaves *Games in progress* and appears under *Matches you have finished*;
/// 4. its verify url still answers `verified: true`, by re-execution rather than by a stored bit;
/// 5. a stranger's page does not list it.
#[tokio::test]
async fn a_finished_match_is_listed_on_your_page_and_still_replays() {
    let app = app_with_a_session_store();
    let (id, seat_a, _seat_b) = mint_automatafl_table(&app).await;
    let cookie_a = format!("dregg_user={seat_a}");

    // 1. A REAL TURN — so the archive holds something a replay can actually check. The move is read
    //    off the board the server painted for THIS seat, and carries the route authority that same
    //    page stamped into its forms.
    land_a_seated_turn(&app, "automatafl", &id, &cookie_a).await;

    // 2. THE MATCH ENDS. Resignation is the ending a player can cause on demand, and it is the one
    //    that also RETIRES the session (archiving its log) rather than leaving a zombie table.
    let resigned = post_as(
        &app,
        &format!("/automatafl/table/{id}/resign"),
        Some(&cookie_a),
    )
    .await;
    assert_eq!(resigned.status, StatusCode::OK, "{}", resigned.body);

    // 3. IT IS ON THE PAGE, in the FINISHED panel and not in the live one.
    let page = get(&app, "/you", Some(&cookie_a)).await;
    assert_eq!(page.status, StatusCode::OK, "{}", page.body);
    assert!(
        page.body.contains("Matches you have finished"),
        "the finished panel must be assembled: {}",
        page.body
    );
    assert!(
        page.body.contains(&id),
        "the finished match must be listed — this is exactly what used to be DELETED: {}",
        page.body
    );
    assert!(
        page.body.contains("Replay this match"),
        "…with the link that re-executes it: {}",
        page.body
    );
    assert!(
        page.body
            .contains(&format!("/offerings/automatafl/session/{id}/verify")),
        "…at the EXISTING verify route, not a re-implementation: {}",
        page.body
    );
    assert!(
        page.body.contains("seat A") && page.body.contains("1 of 1 landed turn yours"),
        "the seat and actor joins must survive into the finished list: {}",
        page.body
    );
    // The seat secret is still never echoed, finished or not.
    assert!(
        !page.body.contains(&seat_a),
        "the seat secret reached the page: {}",
        page.body
    );

    // 4. AND IT STILL REPLAYS — by re-execution, on this request.
    let verify = get(
        &app,
        &format!("/offerings/automatafl/session/{id}/verify"),
        Some(&cookie_a),
    )
    .await;
    assert_eq!(verify.status, StatusCode::OK, "{}", verify.body);
    assert!(
        verify.body.contains("\"verified\":true"),
        "a finished match must still re-verify from its archived moves: {}",
        verify.body
    );
    assert!(
        !verify.body.contains("no such offering session"),
        "the verify route must reach the archive, not report the match missing: {}",
        verify.body
    );
    // Replaying it twice must not consume it — the archive is the artifact, not a one-shot.
    let again = get(
        &app,
        &format!("/offerings/automatafl/session/{id}/verify"),
        Some(&cookie_a),
    )
    .await;
    assert!(again.body.contains("\"verified\":true"), "{}", again.body);

    // 5. AND IT IS STILL PRIVATE: a stranger holding neither seat sees nothing of it.
    let stranger = get(&app, "/you", Some("dregg_user=you-finished-stranger")).await;
    assert!(
        !stranger.body.contains(&id),
        "a finished match leaked to a viewer who never sat at it: {}",
        stranger.body
    );
}

// ═══════════════════════════════════════════════════════════════════════════════
// 3. THE ACTOR JOIN + THE RECEIPTS PANEL.
// ═══════════════════════════════════════════════════════════════════════════════

/// A landed turn puts its session on the mover's page and mints the receipt the page counts. The
/// receipt panel points at the session's OWN `/verify` route — the page never re-implements replay.
#[tokio::test]
async fn a_landed_turn_shows_up_as_a_game_in_progress_and_as_a_receipt() {
    let app = app();
    let user = "you-mover";
    let session = "you-mover-table";

    let before = get(&app, "/you", Some(&format!("dregg_user={user}"))).await;
    assert!(
        before.body.contains("No receipt carries your name yet"),
        "the empty receipt state must be prose: {}",
        before.body
    );

    land_a_turn(&app, session, user).await;

    let after = get(&app, "/you", Some(&format!("dregg_user={user}"))).await;
    assert_eq!(after.status, StatusCode::OK, "{}", after.body);
    assert!(
        after.body.contains(session),
        "the session a turn landed in must appear: {}",
        after.body
    );
    assert!(
        after
            .body
            .contains(&format!("/offerings/tug/session/{session}/verify")),
        "the receipt links at the existing verify route: {}",
        after.body
    );
    assert!(
        after.body.contains("landed turn") && after.body.contains("minted a receipt"),
        "the receipts panel must count the landed turns: {}",
        after.body
    );
    assert!(
        !after.body.contains("No receipt carries your name yet"),
        "the empty state must be GONE once a receipt exists: {}",
        after.body
    );
    // Honesty: a browser turn is asserted, never presented as a signature.
    assert!(
        after.body.contains("asserted"),
        "the attribution grade must be stated: {}",
        after.body
    );
}

// ═══════════════════════════════════════════════════════════════════════════════
// 4. THE BOARD JOIN — my Descent runs, and only mine.
// ═══════════════════════════════════════════════════════════════════════════════

fn drive_win<S: CharacterStore>(off: &DailyDescentOffering<S>, run: &mut DailyRun) {
    for _ in 0..64 {
        let Some(room) = run.current_room() else {
            break;
        };
        let choice = match room.as_str() {
            "gate" => {
                if run.read_var("warden_hp") == 0 {
                    GATE_PRESS
                } else if run.read_var("hp") >= 16 {
                    GATE_MEASURED
                } else {
                    GATE_HEAL
                }
            }
            "keyroom" => KEY_TAKE,
            "hoardgate" => HOARD_FORCE,
            "hoard" => HOARD_SEIZE,
            corridor if corridor.starts_with("corridor") => CORRIDOR_ON,
            other => panic!("unexpected room in a winning line: {other}"),
        };
        assert!(off.advance(run, choice).landed(), "a careful move landed");
    }
}

/// A board with one honest winning run for `mine` and one for `theirs`.
fn board_with_two_players(mine: &str, theirs: &str) -> Arc<DescentState> {
    let seed = daily_seed(&[3; 32]);
    let off = DailyDescentOffering::new(InMemoryCharacterStore::new());
    let state = Arc::new(DescentState::new());
    state.open_day("today", seed);
    for (label, run_id) in [(mine, "you-run-mine"), (theirs, "you-run-theirs")] {
        let mut run = off
            .open_from_seed(DreggIdentity(label.to_string()), seed)
            .expect("the day opens");
        off.choose_class(&run, WARRIOR).expect("a class is chosen");
        drive_win(&off, &mut run);
        assert!(run.is_won(), "the careful line reached the hoard");
        state.ingest_run(
            "today",
            run_id,
            label,
            run.character().level(),
            run.character().class(),
            run.playthrough(),
        );
    }
    state
}

/// The viewer's own recorded run appears with the run card that already replays it; a neighbouring
/// label's run does not. The label match is EXACT — a board is not a fuzzy search.
#[tokio::test]
async fn my_descent_runs_appear_and_someone_elses_do_not() {
    let mine = "you-runner";
    let theirs = "you-runner-2";
    let app = app_with(board_with_two_players(mine, theirs));

    let page = get(&app, "/you", Some(&format!("dregg_user={mine}"))).await;
    assert_eq!(page.status, StatusCode::OK, "{}", page.body);
    assert!(
        page.body.contains("/descent/run/you-run-mine"),
        "my run must link at the EXISTING run card: {}",
        page.body
    );
    assert!(
        !page.body.contains("you-run-theirs"),
        "another label's run leaked onto my page: {}",
        page.body
    );
    assert!(
        page.body.contains("re-verified"),
        "the verdict must be the one taken on this read: {}",
        page.body
    );

    // The neighbouring label — whose name is a PREFIX-superset of mine — sees only its own.
    let other = get(&app, "/you", Some(&format!("dregg_user={theirs}"))).await;
    assert!(
        other.body.contains("/descent/run/you-run-theirs"),
        "{}",
        other.body
    );
    assert!(!other.body.contains("you-run-mine"), "{}", other.body);
}

// ═══════════════════════════════════════════════════════════════════════════════
// 5 + 6. The brand-new visitor, the shell, and the headers.
// ═══════════════════════════════════════════════════════════════════════════════

/// A first-time visitor arrives with no cookie, is given one by the bootstrap, and is told in prose
/// what is empty and where to start — never handed a blank panel. And the minted cookie value, which
/// is a bearer credential on this surface, does not appear in the page it was minted for.
#[tokio::test]
async fn a_brand_new_visitor_is_told_what_is_empty_and_where_to_start() {
    let app = app();
    let reply = get(&app, "/you", None).await;
    assert_eq!(reply.status, StatusCode::OK, "{}", reply.body);

    let minted = reply
        .set_cookie
        .as_deref()
        .expect("a cookie-less visitor is given a durable label")
        .split(';')
        .next()
        .and_then(|pair| pair.split_once('='))
        .map(|(_, value)| value.to_string())
        .expect("the Set-Cookie carries the label");
    assert!(
        !reply.body.contains(&minted),
        "the visitor's own credential was echoed into the page: {}",
        reply.body
    );

    for said in [
        "Nothing is waiting for you",
        "The board has no run under this label",
        "No receipt carries your name yet",
    ] {
        assert!(
            reply.body.contains(said),
            "an absence spoke for itself instead of being said in prose ({said}): {}",
            reply.body
        );
    }
    // …and every empty panel offers the way in.
    assert!(reply.body.contains("/descent/play"), "{}", reply.body);
    assert!(reply.body.contains("/automatafl"), "{}", reply.body);

    // Identity durability is stated, not glossed.
    assert!(
        reply.body.contains("no recovery") && reply.body.contains("Clear your cookies"),
        "the cookie identity's fragility must be said outright: {}",
        reply.body
    );

    // Personal pages are never cacheable by a shared cache.
    let cache = reply.cache_control.unwrap_or_default();
    assert!(
        cache.contains("no-store") && cache.contains("private"),
        "a personal page must not be shared-cacheable: {cache}"
    );
}

/// `/me` is the other thing people type, and it serves the same page. The page is dressed in the
/// house skin (the Night Record) and hangs in the product shell rather than being a naked fragment.
#[tokio::test]
async fn the_page_is_reachable_as_me_and_wears_the_house_skin() {
    let app = app();
    let you = get(&app, "/you", Some("dregg_user=you-skin")).await;
    let me = get(&app, "/me", Some("dregg_user=you-skin")).await;
    assert_eq!(me.status, StatusCode::OK, "{}", me.body);
    assert_eq!(
        me.body, you.body,
        "`/me` and `/you` must be the same page, not two drifting copies"
    );
    assert!(
        you.body
            .contains("<main class=\"session af-table you-page\">"),
        "the page must be served in the Night Record: {}",
        you.body
    );
    assert!(
        you.body.contains("<header class=\"topbar\">")
            && you.body.contains("<footer class=\"foot\">"),
        "the page must hang in the product shell: {}",
        you.body
    );
    // The nav has to LINK it, or the page is exactly as findable as it was when it did not exist.
    assert!(
        you.body.contains("href=\"/you\""),
        "the shared nav must offer a way to this page: {}",
        you.body
    );
}
