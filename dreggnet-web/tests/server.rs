//! THE PUBLIC-DEMO SERVER APP — the merged [`make_app`] Router, driven end to end with NO real
//! network (axum `ServiceExt::oneshot`). This is the smoke test for the deploy scout's Phase-0
//! unblocker: the ONE app the `dreggnet-web-server` bin binds + serves must
//! - answer `GET /health` 200 (the liveness probe the fronting proxy hits);
//! - list the eight games AND the nine do-once feature surfaces at `GET /offerings`;
//! - play a real turn on a game through the merged router (a POST lands a committed receipt);
//! - render the seeded no-cheat Descent leaderboard (the honest winner ranks, the forgery is
//!   excluded) and the run-cards (an honest run PASSes, the forgery FAILs) — all by replay.
//!
//! Green here = a stranger can open the demo URL and play + independently verify, node-free.

use axum::body::Body;
use axum::http::{Request, StatusCode};
use dreggnet_web::{demo_win, make_app};
use dungeon_on_dregg::KP_PRESS_ON;
use tower::ServiceExt; // oneshot

mod common;

/// The deployed app, wrapped in the shared silent-409 tripwire.
fn app() -> axum::Router {
    common::guard(make_app())
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

/// POST a `{turn, arg}` affordance form as `user`, carrying the route authority the play surface
/// stamped into its own form (`dungeon` and `automatafl` are SPINED keys — a bare `turn=&arg=` is
/// `409 invalid game reference` and never reaches the executor).
async fn post(
    app: &axum::Router,
    uri: &str,
    turn: &str,
    arg: i64,
    user: &str,
) -> (StatusCode, String) {
    common::post_act(app, uri, turn, arg, user).await
}

/// POST a JSON body (the `POST /descent/submit` run-ingest shape).
async fn post_json(app: &axum::Router, uri: &str, body: &str) -> (StatusCode, String) {
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

/// `GET /health` answers 200 with an ok status — the liveness probe the fronting proxy checks.
#[tokio::test]
async fn health_is_200() {
    let app = app();
    let (status, body) = get(&app, "/health").await;
    assert_eq!(status, StatusCode::OK);
    assert!(body.contains("ok"), "health reports ok: {body}");
}

/// `GET /` renders the landing page linking the catalog + the no-cheat board.
#[tokio::test]
async fn the_landing_page_renders() {
    let app = app();
    let (status, body) = get(&app, "/").await;
    assert_eq!(status, StatusCode::OK);
    assert!(
        body.contains("/offerings"),
        "landing links the catalog: {body}"
    );
    assert!(
        body.contains("href=\"/descent\""),
        "landing links the no-cheat board (the short /descent URL): {body}"
    );
}

/// ⚑ **`GET /offerings` lists EXACTLY the ship list** — read from
/// `dreggnet_catalog::SHIPPED_KEYS`, never re-hardcoded here, so paring or re-listing an offering
/// moves this test with it instead of leaving it stale.
///
/// Both directions: every shipped offering has a real front door on the page, and no offering we
/// took off the shelf appears on it at all.
#[tokio::test]
async fn offerings_lists_exactly_the_ship_list() {
    let app = app();
    let (status, body) = get(&app, "/offerings").await;
    assert_eq!(status, StatusCode::OK);

    for key in dreggnet_catalog::SHIPPED_KEYS {
        // A SEAT-LOCKED game (`tug`, `automatafl`) advertises its table-minting front door instead
        // of a shared `/offerings/{key}/session/{key}-web` id: a printed shared id was a seat race,
        // and an asserted label could render the opponent's private projection on it.
        match dreggnet_web::table_seats::lock_for_key(key) {
            Some(door) => {
                assert!(
                    body.contains(&format!("href=\"{}\"", door.route)),
                    "the seat-locked {key} card opens its own table at {}: {body}",
                    door.route
                );
                assert!(
                    !body.contains(&format!("/offerings/{key}/session/")),
                    "and never re-advertises a shared, guessable {key} table id: {body}"
                );
            }
            None => assert!(
                body.contains(&format!("/offerings/{key}/session/")),
                "the catalog lists the shipped {key}: {body}"
            ),
        }
    }

    for key in dreggnet_catalog::CATALOG_KEYS {
        if dreggnet_catalog::is_shipped(key) {
            continue;
        }
        assert!(
            !body.contains(&format!("/offerings/{key}/session/")),
            "`{key}` is off the ship list and must not be advertised on the catalog page: {body}"
        );
    }
}

/// ⚑ **UNLISTED IS NOT DELETED.** Everything we took off the shelf still opens and renders at its
/// own URL — the ship list decides what we ADVERTISE, never what works.
#[tokio::test]
async fn an_unlisted_offering_still_opens_at_its_own_url() {
    let app = app();
    for key in dreggnet_catalog::CATALOG_KEYS {
        if dreggnet_catalog::is_shipped(key) {
            continue;
        }
        let uri = format!("/offerings/{key}/session/{key}-unlisted-probe");
        let (status, body) = get(&app, &uri).await;
        // The property is ROUTING, not a 200: an offering may still refuse its own open for its
        // own reasons (`descent-campaign` under a live day binding with no published day answers
        // 409, exactly as it did before the ship list existed). What must never happen is the key
        // becoming unknown.
        assert_ne!(
            status,
            StatusCode::NOT_FOUND,
            "unlisted {key} lost its route"
        );
        assert!(
            !body.contains("No offering registered"),
            "unlisted `{key}` must stay ROUTED, not unmounted: {body}"
        );
    }
}

/// A game plays a real turn through the merged router: open the dungeon, POST a legal move, and a
/// committed verified receipt lands.
#[tokio::test]
async fn a_game_plays_a_turn_through_the_merged_router() {
    let app = app();
    let base = "/offerings/dungeon/session/smoke1";
    let act = format!("{base}/act");

    let (status, body) = get(&app, base).await;
    assert_eq!(status, StatusCode::OK);
    assert!(body.contains("Warden"), "the Keep opens: {body}");

    let (status, body) = post(&app, &act, "choose", KP_PRESS_ON as i64, "ember").await;
    assert_eq!(status, StatusCode::OK);
    assert!(body.contains("Turn committed"), "a real turn lands: {body}");
}

/// The single-offering session surface (`/session/{id}`) is also mounted + plays through the merged
/// app (offering #0), and re-verifies over HTTP.
#[tokio::test]
async fn the_single_offering_session_surface_is_mounted() {
    let app = app();
    let (status, body) = get(&app, "/session/s0").await;
    assert_eq!(status, StatusCode::OK);
    assert!(!body.is_empty(), "the session #0 surface renders");

    let (status, verify) = get(&app, "/session/s0/verify").await;
    assert_eq!(status, StatusCode::OK);
    assert!(
        verify.contains("\"verified\":true"),
        "the fresh session re-verifies: {verify}"
    );
}

/// The seeded no-cheat leaderboard renders: the honest winner ranks, the forgery is excluded — the
/// re-verification is on render, by replay.
#[tokio::test]
async fn the_no_cheat_leaderboard_renders_the_verified_winner() {
    let app = app();
    let (status, body) = get(&app, "/descent/leaderboard").await;
    assert_eq!(status, StatusCode::OK);
    assert!(body.contains("ember"), "the verified winner ranks: {body}");
    assert!(
        body.contains("/descent/run/demo-ember"),
        "the winning row links to its run-card: {body}"
    );
    assert!(
        !body.contains("a-forger"),
        "the forged run is excluded from the no-cheat board: {body}"
    );
    assert!(body.contains("no-cheat"), "the board states its property");
}

/// The run-cards prove by re-execution: the honest run PASSes, the seeded forgery FAILs.
#[tokio::test]
async fn a_run_card_proves_honest_and_fails_the_forgery() {
    let app = app();

    let (status, won) = get(&app, "/descent/run/demo-ember").await;
    assert_eq!(status, StatusCode::OK);
    assert!(
        won.contains("Independent verification — PASS"),
        "the honest run re-executes to PASS: {won}"
    );

    let (status, forged) = get(&app, "/descent/run/demo-forgery").await;
    assert_eq!(status, StatusCode::OK);
    assert!(
        forged.contains("Independent verification — FAIL"),
        "the forged run shows FAIL: {forged}"
    );
    assert!(
        !forged.contains("Independent verification — PASS"),
        "the forged run is NOT a fake pass: {forged}"
    );
}

/// **The short `/descent` URL renders the no-cheat board (regression: it used to 404).** The landing
/// button and a bare shared link point at `/descent`; before it was mounted, only
/// `/descent/leaderboard` existed and `GET /descent` fell through to 404. Now `/descent`,
/// `/descent/`, and `/descent/leaderboard` all render the same re-verified board.
#[tokio::test]
async fn the_short_descent_url_renders_the_board() {
    let app = app();

    // The exact break the deploy hit: GET /descent must NOT 404.
    let (status, body) = get(&app, "/descent").await;
    assert_eq!(
        status,
        StatusCode::OK,
        "GET /descent is not a 404: {status}"
    );
    assert!(
        body.contains("no-cheat"),
        "the board renders its property: {body}"
    );
    assert!(
        body.contains("ember"),
        "the seeded verified winner ranks on /descent: {body}"
    );
    assert!(
        !body.contains("a-forger"),
        "the forged run is excluded from /descent: {body}"
    );

    // The trailing-slash form and the explicit name render the same board.
    let (status, _) = get(&app, "/descent/").await;
    assert_eq!(status, StatusCode::OK, "GET /descent/ is not a 404");
    let (status, _) = get(&app, "/descent/leaderboard").await;
    assert_eq!(
        status,
        StatusCode::OK,
        "GET /descent/leaderboard still renders"
    );

    // The landing button now points at the working short URL.
    let (_, landing) = get(&app, "/").await;
    assert!(
        landing.contains("href=\"/descent\""),
        "the landing button links the working /descent URL: {landing}"
    );
}

/// **A full automatafl turn plays end-to-end through the MERGED demo app.** `games.rs` drives this
/// through the standalone `catalog_router`; this proves the SAME commit→reveal→resolve loop works
/// through the exact `make_app` a stranger hits: open the board, select a piece (its legal moves
/// light), an illegal diagonal is REFUSED (nothing commits), both seats seal, both reveal, the turn
/// resolves and the board re-paints with the advanced turn counter, and the chain re-verifies.
#[tokio::test]
async fn a_full_automatafl_turn_plays_through_the_merged_app() {
    let app = app();
    let base = "/offerings/automatafl/session/merged-auto-1";
    let act = format!("{base}/act");

    // The board paints as a clickable CoordGrid in the commit phase.
    let (status, body) = get(&app, base).await;
    assert_eq!(status, StatusCode::OK);
    assert!(
        body.contains("coordgrid"),
        "the board paints as a CoordGrid: {body}"
    );
    assert!(
        body.contains("name=\"turn\" value=\"select\""),
        "a board square is a real clickable POST affordance"
    );
    assert!(
        body.contains("COMMIT (both seats seal a move)"),
        "the match opens in the commit phase: {body}"
    );

    // Seat A (alice): select the stock attractor at (3,1) — its legal-move set lights.
    let (_, body) = post(&app, &act, "select", idx(3, 1), "alice").await;
    assert!(body.contains("Turn committed"), "the select lands: {body}");
    assert!(
        body.contains("highlighted"),
        "the selected piece lights its legal moves through the merged app: {body}"
    );

    // An illegal diagonal (3,1)->(4,2) is refused by the real referee; nothing commits.
    let (_, body) = post(&app, &act, "commit", idx(4, 2), "alice").await;
    assert!(
        body.contains("Refused: illegal move"),
        "a diagonal is refused: {body}"
    );
    assert!(
        body.contains("COMMIT (both seats seal a move)"),
        "the refused move committed nothing — still commit phase"
    );

    // The legal seal lands. The POST re-renders AS alice (viewer-aware host boundary), so the sealer
    // sees HER OWN move revealed — the opponent, not the sealer, is the one kept in the fog.
    let (_, body) = post(&app, &act, "commit", idx(3, 3), "alice").await;
    assert!(body.contains("Turn committed"), "the seal lands: {body}");
    assert!(
        body.contains("YOUR sealed move"),
        "the sealer sees THEIR OWN sealed move on their own surface (per-viewer, not viewer-blind fog): {body}"
    );

    // Seat B (bob): select (7,1), seal to (7,3) — both seals in flips to reveal.
    let (_, body) = post(&app, &act, "select", idx(7, 1), "bob").await;
    assert!(body.contains("Turn committed"), "bob claims seat B: {body}");
    let (_, body) = post(&app, &act, "commit", idx(7, 3), "bob").await;
    assert!(body.contains("Turn committed"));
    // Rendered AS bob now: ALICE's sealed move is FOG to him (only the commitment shows) — the
    // simultaneous-secret fog, correctly keyed to the OPPONENT's viewpoint.
    assert!(
        body.contains("move SEALED"),
        "the opponent's sealed move is fog to bob: {body}"
    );
    assert!(
        body.contains("REVEAL (both moves sealed"),
        "both seals in → reveal phase: {body}"
    );

    // Both reveal, then resolve — the turn counter advances and the board re-paints.
    let (_, body) = post(&app, &act, "reveal", 0, "alice").await;
    assert!(body.contains("Turn committed"), "alice opens her seal");
    let (_, body) = post(&app, &act, "reveal", 0, "bob").await;
    assert!(body.contains("Turn committed"), "bob opens his seal");
    assert!(
        body.contains("RESOLVE (both open"),
        "both open → resolve is one turn away: {body}"
    );
    let (_, body) = post(&app, &act, "resolve", 0, "alice").await;
    assert!(body.contains("Turn committed"), "the resolution lands");
    assert!(
        body.contains("Automatafl — turn 1"),
        "the resolved turn counter advanced in the browser: {body}"
    );
    assert!(body.contains("coordgrid"), "the resolved board re-paints");

    // The whole committed chain re-verifies over HTTP through the merged app.
    let (status, verify) = get(&app, &format!("{base}/verify")).await;
    assert_eq!(status, StatusCode::OK);
    assert!(
        verify.contains("\"verified\":true"),
        "the committed automatafl match verifies through the merged app: {verify}"
    );
}

/// **A live Descent run submits over HTTP and appears on the board.** A stranger POSTs a run's
/// reproducible input (day + player + the winning move sequence) to `/descent/submit`; it is
/// re-executed + no-cheat-verified before it can rank; the response links the shareable run-card;
/// and the new player then appears on `GET /descent` and its run-card re-verifies to PASS. A forged
/// (illegal) submission is rejected 400 and never reaches the board. This runs node-free — the demo
/// settles `Local` (no `DREGG_NODE_URL`), so submit + rank + board are entirely in-process replay.
#[tokio::test]
async fn a_live_run_submits_and_reaches_the_leaderboard() {
    let app = app();

    // The honest winning line for the demo day (the same source the seeded winner uses).
    let (win_moves, level, class) = demo_win();
    let moves_json = serde_json::to_string(&win_moves).unwrap();
    let body = format!(
        "{{\"day\":\"today\",\"player\":\"stranger\",\"level\":{level},\"class\":{class},\"moves\":{moves_json}}}"
    );

    let (status, resp) = post_json(&app, "/descent/submit", &body).await;
    assert_eq!(
        status,
        StatusCode::OK,
        "the honest submit is accepted: {resp}"
    );
    assert!(resp.contains("\"ranked\":true"), "the run ranks: {resp}");
    // The response links the shareable run-card.
    let v: serde_json::Value = serde_json::from_str(&resp).unwrap();
    let run_id = v["run_id"]
        .as_str()
        .expect("a run_id came back")
        .to_string();
    assert!(
        v["share"].as_str().unwrap().contains(&run_id),
        "the response links the shareable run-card: {resp}"
    );

    // The submitted player now appears on the no-cheat board (re-verified on render).
    let (status, board) = get(&app, "/descent").await;
    assert_eq!(status, StatusCode::OK);
    assert!(
        board.contains("stranger"),
        "the freshly-submitted run appears on /descent: {board}"
    );

    // Its run-card independently re-verifies to PASS.
    let (status, card) = get(&app, &format!("/descent/run/{run_id}")).await;
    assert_eq!(status, StatusCode::OK);
    assert!(
        card.contains("Independent verification — PASS"),
        "the submitted run re-executes to PASS: {card}"
    );

    // A FORGED submission (an illegal opening move) is rejected 400 and never ranks.
    let forged_body =
        "{\"day\":\"today\",\"player\":\"cheater\",\"level\":1,\"class\":0,\"moves\":[99]}";
    let (status, resp) = post_json(&app, "/descent/submit", forged_body).await;
    assert_eq!(
        status,
        StatusCode::BAD_REQUEST,
        "a forged/illegal run is rejected fail-closed: {resp}"
    );
    let (_, board) = get(&app, "/descent").await;
    assert!(
        !board.contains("cheater"),
        "the rejected forgery never reaches the board: {board}"
    );
}
