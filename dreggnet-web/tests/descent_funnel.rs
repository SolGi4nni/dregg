//! THE DESCENT FUNNEL, driven end to end — acquire → play → share.
//!
//! Three joints were severed (docs/MATURATION-BACKLOG-2026-07-19.md §2). This suite drives the two
//! that are testable with no network, against the REAL merged app (`make_app`, axum `oneshot`):
//!
//! 1. **CTA reachability** — the product's "Play" affordances point at `/descent/play` (the served,
//!    in-tab game), not at `/descent` (the no-cheat *board*). Before, nothing on the site linked to
//!    the play page at all: it was built, mounted, and unreachable.
//! 2. **The H2 share link** — a run played in the day the SHARED `(day_key, seed)` helper resolves,
//!    submitted the way the Discord bot now submits it (WITH its `day`), re-executes here and RANKS,
//!    so the run-card share link exists. Before, the bot omitted `day` and the web opened a
//!    hardcoded `daily_seed(&[3;32])` demo world, so the re-execution could never verify:
//!    `ranked:false`, no link, every time.
//!
//! The exclusion legs are what make these non-vacuous: a run submitted against a DIFFERENT
//! (re-derivable, in-window) day does NOT rank, and a hostile day key is refused outright.

use axum::body::Body;
use axum::http::{Request, StatusCode};
use tower::ServiceExt; // oneshot

use dreggnet_web::{DESCENT_PLAY_PATH, demo_win, make_app};

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
    (status, String::from_utf8_lossy(&bytes).to_string())
}

async fn post_json(
    app: &axum::Router,
    uri: &str,
    body: serde_json::Value,
) -> (StatusCode, serde_json::Value) {
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
    (
        status,
        serde_json::from_slice(&bytes).unwrap_or(serde_json::Value::Null),
    )
}

/// **JOINT 1 — the play page is REACHABLE.** The landing, the catalog, and the Telegram shelf all
/// carry a CTA to `/descent/play`, and the page itself serves. Before this, every "Play The Descent"
/// affordance landed on the no-cheat board and `/descent/play` had no inbound link anywhere.
#[tokio::test]
async fn the_play_page_is_linked_from_the_front_doors_and_serves() {
    let app = make_app();

    for (page, what) in [("/", "the landing"), ("/offerings", "the catalog")] {
        let (status, body) = get(&app, page).await;
        assert_eq!(status, StatusCode::OK, "{what} serves");
        assert!(
            body.contains(&format!("href=\"{DESCENT_PLAY_PATH}\"")),
            "{what} links the PLAY page, not just the board"
        );
        // The board is still reachable — the funnel gained a front door, it did not lose the board.
        assert!(
            body.contains("href=\"/descent\""),
            "{what} still links the board"
        );
    }

    // And the page a CTA now points at actually serves the game shell.
    let (status, play) = get(&app, DESCENT_PLAY_PATH).await;
    assert_eq!(status, StatusCode::OK, "the play page serves");
    assert!(
        play.contains("id=\"descent-play-root\"") && play.contains("/descent/play/static/app.js"),
        "it mounts the native wasm controller"
    );
    assert!(
        !play.contains("<dregg-descent"),
        "the obsolete procgen custom element must not return"
    );
}

/// **JOINT 3 — `/descent/play` opens TODAY'S committed descriptor.** Procgen play and the
/// Lean-native browser are distinct rulesets, but both are deterministically bound to the shared
/// day: the full epoch re-derives the procgen seed, while the native controller receives the exact
/// little-endian prefix that `NativeDescentOffering::open` normalizes.
#[tokio::test]
async fn the_play_page_opens_todays_real_day() {
    let app = make_app();
    let day = dreggnet_web::descent::todays_day();

    let (status, v) = {
        let (s, body) = get(&app, "/descent/play/static/day.json").await;
        (s, serde_json::from_str::<serde_json::Value>(&body).unwrap())
    };
    assert_eq!(status, StatusCode::OK);
    assert_eq!(
        v["key"], day.key,
        "the page serves the cross-process day key"
    );
    assert_eq!(v["epochHex"], day.epoch_hex());
    // Procgen provenance remains exact.
    assert_eq!(
        procgen_dregg::daily_seed(&day.epoch).as_bytes(),
        day.seed.as_bytes(),
        "the published epoch derives the day's seed"
    );
    // The native shell receives the same committed day label plus the raw seed input its own
    // Offering normalizes. It does not pretend to open the procgen URI/world.
    let bytes = day.seed.as_bytes();
    let native_seed = u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
    assert_eq!(v["nativeSeed"], native_seed);
    let (_, shell) = get(&app, DESCENT_PLAY_PATH).await;
    assert!(
        shell.contains(&format!("data-day-key=\"{}\"", day.key))
            && shell.contains(&format!("data-native-seed=\"{native_seed}\"")),
        "the shell opens today's native descriptor: {shell}"
    );
    assert!(
        !shell.contains("b3_de5ce0"),
        "the hardcoded demo day is gone: {shell}"
    );
}

/// **JOINT 2 — THE SHARE LINK EMITS.** A run played on the day the shared helper resolves, POSTed
/// the way the bot now POSTs it (carrying its `day` key), re-executes here and RANKS — so the
/// response hands back the `/descent/run/{id}` card a stranger can re-verify, and that card serves.
///
/// This is the exact wire that was dead: the bot sent no `day`, the web played
/// `daily_seed(&[3;32])`, and the re-execution of a real Discord run could never verify.
#[tokio::test]
async fn a_run_submitted_with_its_day_key_ranks_and_yields_a_share_link() {
    let app = make_app();
    let day = dreggnet_web::descent::todays_day();
    // The winning line for TODAY'S world (world-agnostic — it reads the live room + vitals).
    let (moves, level, class) = demo_win();
    assert!(
        !moves.is_empty(),
        "a real winning line exists for today's world"
    );

    let (status, v) = post_json(
        &app,
        "/descent/submit",
        serde_json::json!({
            "day": day.key,          // ← the weld: WHICH WORLD this was played in
            "player": "funnel-tester",
            "level": level,
            "class": class,
            "moves": moves,
        }),
    )
    .await;

    assert_eq!(status, StatusCode::OK, "the honest run is accepted: {v}");
    assert_eq!(v["ranked"], true, "it re-executed to the hoard HERE: {v}");
    let share = v["share"].as_str().expect("a share path is minted");
    assert!(
        share.starts_with("/descent/run/"),
        "the run-card shape: {share}"
    );

    // The link a player is handed actually resolves, and re-proves the run.
    let (status, card) = get(&app, share).await;
    assert_eq!(status, StatusCode::OK, "the shared run-card serves");
    assert!(
        card.contains("PASS"),
        "the stranger sees the run PROVEN: {card}"
    );

    // …and the run now ranks on the board a share link points people back to.
    let (_, board) = get(&app, "/descent").await;
    assert!(board.contains("funnel-tester"), "the run ranks: {board}");
}

/// **NON-VACUOUS.** The same winning moves submitted against a DIFFERENT (real, re-derivable,
/// in-window) day do NOT rank — the world is what decides, and the day key is load-bearing rather
/// than decorative. This is precisely the silent failure the missing `day` produced.
#[tokio::test]
async fn the_same_run_does_not_rank_in_a_different_days_world() {
    let app = make_app();
    let today = dreggnet_web::descent::todays_day();
    let (moves, _l, _c) = demo_win();

    // Tomorrow's day: a genuine, re-derivable world — just not the one these moves were played in.
    let other = procgen_dregg::descent_day::offline_day(today.utc_day + 1);
    assert_ne!(other.seed.as_bytes(), today.seed.as_bytes());

    let (status, v) = post_json(
        &app,
        "/descent/submit",
        serde_json::json!({
            "day": other.key,
            "player": "wrong-world",
            "moves": moves,
        }),
    )
    .await;
    assert_eq!(status, StatusCode::BAD_REQUEST, "refused: {v}");
    assert_eq!(
        v["ranked"], false,
        "a run cannot rank in a world it never played"
    );
}

#[tokio::test]
async fn target_wide_procgen_move_indices_are_anti_ghost() {
    let app = make_app();
    let day = dreggnet_web::descent::todays_day();
    let (status, response) = post_json(
        &app,
        "/descent/submit",
        serde_json::json!({
            "day": day.key,
            "player": "wide-index-hostile",
            "moves": [u64::MAX],
        }),
    )
    .await;
    assert_eq!(status, StatusCode::BAD_REQUEST, "{response}");
    assert_eq!(response["ranked"], false);

    let (_, board) = get(&app, "/descent").await;
    assert!(
        !board.contains("wide-index-hostile"),
        "a hostile stable move index must not create a board row"
    );
}

/// A HOSTILE day key is refused, and refused WITHOUT the endpoint reaching for the network: a
/// malformed key, a far-away day (the round-space walk), and a hand-picked off-schedule round all
/// fail closed. `/descent/submit` is unauthenticated, so a caller-supplied key must never be able to
/// steer it.
#[tokio::test]
async fn a_hostile_day_key_is_refused() {
    let app = make_app();
    let (moves, _l, _c) = demo_win();
    let today = procgen_dregg::beacon::current_utc_day();

    for key in [
        "not-a-day".to_string(),
        "d-off".to_string(),
        // A day far outside the ±1 window — the walk across the drand round space.
        format!("d{}-r{}", today + 5000, 42),
        // Today, but a round the schedule does not bind to today (a favourable-round pick).
        format!("d{today}-r1"),
    ] {
        let (status, v) = post_json(
            &app,
            "/descent/submit",
            serde_json::json!({ "day": key, "player": "hostile", "moves": moves }),
        )
        .await;
        assert_eq!(
            status,
            StatusCode::BAD_REQUEST,
            "`{key}` must be refused: {v}"
        );
        assert_eq!(v["ranked"], false, "`{key}` must not rank");
    }
}

/// A DAYLESS submit still works (the browser / manual path) and lands on today's world — the bot's
/// `day` is an added guarantee, not a new requirement.
#[tokio::test]
async fn a_dayless_submit_still_lands_on_todays_world() {
    let app = make_app();
    let (moves, _l, _c) = demo_win();
    let (status, v) = post_json(
        &app,
        "/descent/submit",
        serde_json::json!({ "player": "dayless", "moves": moves }),
    )
    .await;
    assert_eq!(status, StatusCode::OK, "{v}");
    assert_eq!(
        v["ranked"], true,
        "today's world is what a dayless submit gets: {v}"
    );
}
