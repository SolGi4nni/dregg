//! **THE FULL DEMO, DRIVEN END-TO-END THROUGH THE DEPLOYED APP.**
//!
//! `games.rs` drives the two games through `catalog_router`; this drives the WHOLE deployed
//! surface through [`make_app`] — the exact `Router` the server binds — to prove a clean
//! play-through of all three games with NO dead action / no non-advancing POST / no confusing
//! empty state, and to render the POLISHED surfaces (goal squares, the tug guild table, a feature
//! surface) so they can be eyeballed:
//!
//! - **the landing + grouped catalog** render (Games / Feature surfaces / Services shelves);
//! - **automatafl** plays a full simultaneous turn (`select → commit → reveal → resolve`), the
//!   board's GOAL squares paint their distinct `goal` look, and an illegal move is refused
//!   (nothing commits);
//! - **multiway-tug** opens with its guild lanes as a real `.deos-table` (not a wall of `<p>`) and
//!   a play lands;
//! - **The Descent** ingests the honest winning run through `POST /descent/submit` and it then
//!   ranks on `GET /descent`;
//! - **a feature surface** (trade) renders its goods as a real table with a header row and a play
//!   lands.
//!
//! It also writes HTML samples of the polished surfaces to `/tmp/demo-samples/` (a side output for
//! eyeballing; the assertions are the gate).

use axum::body::Body;
use axum::http::{Request, StatusCode};
use dreggnet_web::{demo_win, make_app};
use tower::ServiceExt; // oneshot

mod common;

/// The deployed app, wrapped in the shared silent-409 tripwire.
fn app() -> axum::Router {
    common::guard(make_app())
}

/// A GET as web user `user` (a `dregg_user` cookie) — the identity a per-viewer RPG world is keyed
/// on, and therefore the only viewer whose `/verify` sees that viewer's own chain.
async fn get_as(app: &axum::Router, uri: &str, user: &str) -> (StatusCode, String) {
    let (status, body) =
        common::get_with_cookie(app, uri, Some(&format!("dregg_user={user}"))).await;
    (status, body)
}

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

/// POST a `{turn, arg}` affordance form as web user `user`, carrying the route authority the play
/// surface stamped into its own form (`automatafl` and `tug` are SPINED keys; `trade` is not, and
/// the helper simply finds no authority to carry there).
async fn post_act(
    app: &axum::Router,
    uri: &str,
    turn: &str,
    arg: i64,
    user: &str,
) -> (StatusCode, String) {
    common::post_act(app, uri, turn, arg, user).await
}

/// POST a JSON body (the Descent submit seam).
async fn post_json(app: &axum::Router, uri: &str, body: serde_json::Value) -> (StatusCode, String) {
    let resp = app
        .clone()
        .oneshot(
            Request::builder()
                .method("POST")
                .uri(uri)
                .header("content-type", "application/json")
                .body(Body::from(body.to_string()))
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

/// The automatafl board index of `(x, y)` — the board's OWN width, never a literal.
fn idx(x: i64, y: i64) -> i64 {
    y * dregg_automatafl::game::N as i64 + x
}

/// **THE OUTCOME, not the copy** — how many turns the offering's own replay proof accepts on this
/// session's committed chain right now (`GET …/verify` → `{"verified":…,"turns":N}`). A refusal that
/// quietly committed, or a landing that quietly did not, moves this number; a banner cannot.
async fn committed_turns(app: &axum::Router, base: &str) -> u64 {
    let (status, body) = get(app, &format!("{base}/verify")).await;
    assert_eq!(status, StatusCode::OK, "{body}");
    let json: serde_json::Value = serde_json::from_str(&body).expect("verify answers JSON");
    assert_eq!(
        json["verified"], true,
        "the committed chain must re-verify at every step: {body}"
    );
    json["turns"].as_u64().expect("verify reports a turn count")
}

/// Write an HTML sample for eyeballing (best-effort; never fails the test).
fn sample(name: &str, html: &str) {
    let dir = std::path::Path::new("/tmp/demo-samples");
    let _ = std::fs::create_dir_all(dir);
    let _ = std::fs::write(dir.join(name), html);
}

/// **The landing + grouped catalog render** — the two pages a stranger opens first.
#[tokio::test]
async fn the_landing_and_grouped_catalog_render() {
    let app = app();

    let (status, body) = get(&app, "/").await;
    assert_eq!(status, StatusCode::OK);
    assert!(
        body.contains(dreggnet_web::PRODUCT_NAME),
        "the landing renders under the current product name"
    );
    assert!(
        !body.contains("DreggNet Cloud"),
        "…and never under the retired layer name: {body}"
    );
    assert!(
        body.contains("/offerings") && body.contains("/descent"),
        "the landing links the catalog + the leaderboard"
    );
    sample("landing.html", &body);

    let (status, body) = get(&app, "/offerings").await;
    assert_eq!(status, StatusCode::OK);
    // The shelves are GROUPING, and a shelf with no shipped cards renders as nothing — so the
    // only one that must be here is the one the ship list actually fills. Asserting the grouped
    // style rather than a hardcoded set of headings keeps this honest when the list changes.
    assert!(
        body.contains("group-h"),
        "the shelf uses the grouped-heading style"
    );
    assert!(
        body.contains("Games"),
        "the shipped offerings sit on a named shelf"
    );
    // A play link from each category is present — and it is the RIGHT link. A SEAT-LOCKED game
    // (`tug`, `automatafl`) deliberately advertises its table-minting FRONT DOOR *instead of* a
    // shared `/offerings/{key}/session/{key}-web` id: a printed shared id was a seat race and let
    // anyone render an opponent's private projection by asserting their label. Asserting the old
    // shared link here would demand the repaired hole back.
    for key in ["automatafl", "tug"] {
        let door = dreggnet_web::table_seats::lock_for_key(key)
            .unwrap_or_else(|| panic!("{key} is a seat-locked table game"));
        assert!(
            body.contains(&format!("href=\"{}\"", door.route)),
            "the {key} card opens its own table at {}: {body}",
            door.route
        );
        assert!(
            !body.contains(&format!("/offerings/{key}/session/")),
            "and never re-advertises a shared, guessable {key} table id: {body}"
        );
    }
    // ⚑ THE SHELF IS THE SHIP LIST, read from it rather than re-listed here. Every shipped
    // offering has a front door; nothing else is advertised at all.
    for key in dreggnet_catalog::SHIPPED_KEYS {
        let door = match dreggnet_web::table_seats::lock_for_key(key) {
            Some(lock) => format!("href=\"{}\"", lock.route),
            None => format!("/offerings/{key}/session/"),
        };
        assert!(
            body.contains(&door),
            "the catalog gives shipped `{key}` a front door: {body}"
        );
    }
    for key in dreggnet_catalog::CATALOG_KEYS {
        if dreggnet_catalog::is_shipped(key) {
            continue;
        }
        assert!(
            !body.contains(&format!("/offerings/{key}/session/")),
            "`{key}` is off the ship list and must not be advertised: {body}"
        );
    }
    // ⚑ NEVER PAINT A ZERO — `{key} · 0 open` on every card read as "nobody is here".
    assert!(
        !body.contains("0 open"),
        "an idle card must say nothing about its population: {body}"
    );
    sample("catalog.html", &body);
}

/// **Automatafl plays a full turn through the deployed app; the goal squares paint distinctly.**
#[tokio::test]
async fn automatafl_full_playthrough_with_goal_squares() {
    let app = app();
    let base = "/offerings/automatafl/session/pt-auto";

    // Open: the board paints, and the four GOAL CORNERS carry the distinct `goal` class — never
    // indistinguishable from an ordinary square. On the STOCK opening every corner is OCCUPIED (a
    // repulsor sits on all four), so the marker rides the cell's `goal` TAG rather than the
    // lowercase `a`/`b` glyph a VACANT corner paints; both earn the ring.
    let (status, body) = get(&app, base).await;
    assert_eq!(status, StatusCode::OK);
    assert!(body.contains("coordgrid"), "the board paints");
    assert_eq!(
        body.matches("tag-goal goal").count(),
        4,
        "all four goal corners carry the distinct `goal` look — they are OCCUPIED at the stock \
         opening (a repulsor on each), so this is the tag-borne marker, not the `a`/`b` glyph: {}",
        &body[..body.len().min(400)]
    );
    assert!(
        body.contains(".coordgrid .cell.goal{"),
        "the goal-square CSS rule ships on the page"
    );
    sample("automatafl-board.html", &body);

    // ── A full simultaneous turn: select → (illegal refused) → commit → reveal → resolve.
    let (_, body) = post_act(&app, &format!("{base}/act"), "select", idx(3, 1), "alice").await;
    assert!(body.contains("Turn committed"), "the select lands: {body}");
    assert!(
        body.contains("highlighted"),
        "the selected piece lights its legal moves"
    );

    // An illegal (diagonal) move is refused — nothing commits (no dead/ghost action).
    //
    // ⚑ Asserted on the referee's VERDICT and on the committed chain, not on the concatenation
    // `"Refused: illegal move"`: the notice is `Refused: {what you pressed} · {why}`, so naming the
    // pressed control split that literal and reddened this line while the rule was working. The
    // refusal had not broken.
    let before = committed_turns(&app, base).await;
    let (_, body) = post_act(&app, &format!("{base}/act"), "commit", idx(4, 2), "alice").await;
    assert!(
        body.contains("Refused") && body.contains("illegal move (3,1) → (4,2)"),
        "a diagonal is refused by the real referee, which names the move it refused: {body}"
    );
    assert_eq!(
        committed_turns(&app, base).await,
        before,
        "the refused move committed NOTHING — the chain must not have grown"
    );
    assert!(
        body.contains("COMMIT (both seats seal a move)"),
        "…and the board did not advance — still the commit phase"
    );

    let (_, body) = post_act(&app, &format!("{base}/act"), "commit", idx(3, 3), "alice").await;
    assert!(body.contains("Turn committed"), "the legal seal lands");
    let (_, body) = post_act(&app, &format!("{base}/act"), "select", idx(7, 1), "bob").await;
    assert!(body.contains("Turn committed"), "bob claims seat B");
    let (_, body) = post_act(&app, &format!("{base}/act"), "commit", idx(7, 3), "bob").await;
    assert!(body.contains("Turn committed"));
    assert!(body.contains("REVEAL (both moves sealed"), "both seals in");

    let (_, _) = post_act(&app, &format!("{base}/act"), "reveal", 0, "alice").await;
    let (_, body) = post_act(&app, &format!("{base}/act"), "reveal", 0, "bob").await;
    assert!(body.contains("RESOLVE (both open"), "both open");
    let (_, body) = post_act(&app, &format!("{base}/act"), "resolve", 0, "alice").await;
    assert!(body.contains("Turn committed"), "the resolution lands");
    assert!(
        body.contains("Automatafl · turn 1"),
        "the turn counter advanced: {body}"
    );

    let (status, body) = get(&app, &format!("{base}/verify")).await;
    assert_eq!(status, StatusCode::OK);
    assert!(
        body.contains("\"verified\":true"),
        "the committed match verifies: {body}"
    );
}

/// **Multiway-tug opens with a real guild TABLE and a play lands.**
#[tokio::test]
async fn tug_guild_table_renders_and_a_play_lands() {
    let app = app();
    let base = "/offerings/tug/session/pt-tug";

    let (status, body) = get(&app, base).await;
    assert_eq!(status, StatusCode::OK);
    assert!(body.contains("Multiway-Tug"), "the tug surface renders");
    // The polish: the guild lanes are a real bordered table of flex rows (NOT a wall of <p>).
    assert!(
        body.contains("deos-table") && body.contains("deos-row"),
        "the guild lanes render as a real table"
    );
    assert!(
        body.contains("Guild 0") && body.contains("Guild 6"),
        "all seven guild lanes paint"
    );
    sample("tug-surface.html", &body);

    // Two browser users claim the seats and their offered plays land.
    //
    // ⚑ READ THE MOVE OFF THE PAGE — do NOT hardcode a (method, index) pair. `arg` is an
    // INDEX into `legal_decisions()`, and tug offers a real decision space now, so a fixed
    // index drifts: this test used to send `("comp", 3)` and went red with
    //   Refused: method `comp` does not name decision 3 (Secret { card: 9 }, which
    //   dispatches under `secret`) (nothing committed — anti-ghost).
    // because index 3 became a `Secret` for this session. `tug_web.rs`'s own doc warns about
    // exactly this. Acting on whatever the surface actually offers keeps the test about
    // "a browser user's play lands" instead of about the engine's ordering.
    let (turn, arg) = common::first_offered_act(&body).expect("the tug surface offers an act");
    let (_, body) = post_act(&app, &format!("{base}/act"), &turn, arg, "alice").await;
    assert!(
        body.contains("Turn committed"),
        "seat A's play lands: {body}"
    );
    // ⚑ Seat B's affordances live on SEAT B'S OWN PAGE. Re-reading the response to A's act hands
    // back an act that is not B's to make — the page is rendered for the actor, and in a
    // simultaneous-move game that actor has already sealed. Reading A's response for B's move is
    // what made this fail with "seat B's play lands" after the first-offered-act fix.
    let (_, b_page) = get_as(&app, base, "bob").await;
    let (turn, arg) =
        common::first_offered_act(&b_page).expect("the tug surface offers seat B an act");
    let (_, body) = post_act(&app, &format!("{base}/act"), &turn, arg, "bob").await;
    assert!(
        body.contains("Turn committed"),
        "seat B's play lands: {body}"
    );
    // The board rendered the OWN-hand once a seat is claimed (a real hidden-hand reveal).
    sample("tug-after-play.html", &body);

    let (status, body) = get(&app, &format!("{base}/verify")).await;
    assert_eq!(status, StatusCode::OK);
    assert!(body.contains("\"verified\":true"), "the tug round verifies");
}

/// **The Descent ingests the honest winning run and it ranks.**
#[tokio::test]
async fn descent_submit_ranks_the_honest_run() {
    let app = app();

    // The leaderboard opens (the short URL a stranger types).
    let (status, board) = get(&app, "/descent").await;
    assert_eq!(status, StatusCode::OK);
    assert!(
        board.contains("descent") || board.contains("Descent") || board.contains("leaderboard"),
        "the leaderboard page renders"
    );
    sample("descent-board.html", &board);

    // Submit the honest winning line through the real ingest seam — it re-executes + verifies.
    let (moves, level, class) = demo_win();
    let (status, body) = post_json(
        &app,
        "/descent/submit",
        serde_json::json!({
            "player": "pt-hero",
            "level": level,
            "class": class,
            "moves": moves,
        }),
    )
    .await;
    assert_eq!(status, StatusCode::OK, "a valid run is accepted: {body}");
    assert!(
        body.contains("\"ranked\":true"),
        "the honest run ranks (re-executed + no-cheat-verified): {body}"
    );

    // It now appears on the board (re-verified on render).
    let (_, board) = get(&app, "/descent").await;
    assert!(
        board.contains("pt-hero"),
        "the ingested honest run appears on the leaderboard"
    );

    // A forged / empty run is fail-closed (400) — nothing ranks.
    let (status, body) = post_json(
        &app,
        "/descent/submit",
        serde_json::json!({ "player": "pt-forger", "moves": [0,0,0] }),
    )
    .await;
    assert_eq!(
        status,
        StatusCode::BAD_REQUEST,
        "a losing/forged run is refused: {body}"
    );
    assert!(body.contains("\"ranked\":false"));
}

/// **A feature surface (trade) renders as a real table and a play lands** — the do-once surfaces
/// are legible + coherent, not a raw ViewNode dump.
#[tokio::test]
async fn a_feature_surface_renders_and_a_play_lands() {
    let app = app();
    let base = "/offerings/trade/session/pt-trade";

    let (status, body) = get(&app, base).await;
    assert_eq!(status, StatusCode::OK);
    assert!(body.contains("Trade"), "the trade surface renders");
    // The goods overview is a real table with a header row (the polish).
    assert!(
        body.contains("deos-table") && body.contains("deos-row header"),
        "the goods render as a table with a header row"
    );
    assert!(
        body.contains("Ember Cloak"),
        "the seeded goods paint in the table"
    );
    sample("trade-surface.html", &body);

    // A real play lands: list good #0 into custody (an owner-signed transfer turn).
    let (_, body) = post_act(&app, &format!("{base}/act"), "list", 0, "seller").await;
    assert!(
        body.contains("Turn committed"),
        "the list play lands a real receipt: {body}"
    );
    sample("trade-after-list.html", &body);

    // ⚑ AS THE SAME VIEWER. `trade` is an RPG key, so the chain the `seller` POST landed on is
    // SELLER's own per-identity world; a cookie-less `/verify` asks the shared anonymous world and
    // is honestly told "no such offering session". Re-verify the world the turn actually landed in.
    let (status, body) = get_as(&app, &format!("{base}/verify"), "seller").await;
    assert_eq!(status, StatusCode::OK);
    assert!(
        body.contains("\"verified\":true"),
        "the trade provenance verifies for its own player: {body}"
    );
}
