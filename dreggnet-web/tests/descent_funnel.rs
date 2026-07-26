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
//! The exclusion legs are what make these non-vacuous: a run submitted against a day whose world it
//! cannot win does NOT rank, a run files under the day it names and never onto today's board, and a
//! hostile day key is refused outright.
//!
//! ⚑ 2026-07-25 — the old exclusion leg ("the same run does not rank in a DIFFERENT day's world",
//! submitted against tomorrow) was a **coin flip** and it lost: today's tape ranked in tomorrow's
//! world. `daily_scene` draws only `warden_hp ∈ {45,60}` and `deepening_rooms ∈ {1,2,3}`, so two
//! real days are mechanically identical about one time in six and one tape wins in both. The
//! measurement is now a test of its own (`two_distinct_daily_worlds_can_accept_one_winning_tape`)
//! and the exclusion leg is stated against a world that genuinely differs, so it is deterministic
//! on every day of the year.

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

/// The world-shape a procgen day draws — the ONLY two parameters of `daily_scene` that a move tape
/// can feel. Everything else the seed draws (the theme, the warden's name, every room's prose) is
/// display: it changes the scene source and therefore the day's content-addressed `UniverseId`,
/// but it does not change which choice index wins at which passage.
fn day_shape(seed: &procgen_dregg::CommittedSeed) -> (u64, usize) {
    let world = dreggnet_offerings::daily_descent::daily_scene(seed);
    (world.warden_hp, world.deepening_rooms)
}

/// The winning move tape for a day's world — what a player submits.
fn winning_tape(seed: procgen_dregg::CommittedSeed) -> Vec<usize> {
    dreggnet_web::demo_win_for_seed(seed).0
}

/// The first real, re-derivable day at or after `from` that `want` accepts.
fn find_day(
    from: u64,
    want: impl Fn(&procgen_dregg::descent_day::DescentDay) -> bool,
) -> procgen_dregg::descent_day::DescentDay {
    (from..from + 512)
        .map(procgen_dregg::descent_day::offline_day)
        .find(&want)
        .expect("the 2x3 shape space is dense in the day space")
}

/// **THE DAY IS LOAD-BEARING — a tape is refused by a world it cannot win.**
///
/// ⚑ This REPLACES `the_same_run_does_not_rank_in_a_different_days_world`, which submitted today's
/// tape against TOMORROW and required a refusal. That assertion was a **coin flip**, and on
/// 2026-07-25 it lost: today's tape ranked in tomorrow's world (`{"ranked":true,"turns":11}`). The
/// cause is measured by `two_distinct_daily_worlds_can_accept_one_winning_tape` below — `daily_scene`
/// draws only `warden_hp ∈ {45,60}` and `deepening_rooms ∈ {1,2,3}`, so two different days are
/// mechanically identical about one time in six, and the old test had been passing on luck.
///
/// The load-bearing property survives and is asserted HERE, deterministically: against a day whose
/// world genuinely differs, the tape is refused by the executor and NOTHING ingests. The control day
/// is opened on the state directly because `/descent/submit` only re-derives keys inside a ±1-day
/// window — which is exactly why no in-window exclusion leg is guaranteed to exist on any given day.
#[tokio::test]
async fn a_tape_is_refused_by_a_day_whose_world_actually_differs() {
    let today = dreggnet_web::descent::todays_day();
    let (moves, _l, _c) = demo_win();
    let (my_hp, my_corridors) = day_shape(&today.seed);

    // ⚑ THE CONTROL DAY IS CHOSEN SO THE REFUSAL IS PROVABLE, NOT LIKELY. Two near-misses that a
    // weaker rule walks straight into:
    //
    //  * "a different SHAPE" is not enough. The gate's extra moves are ABSORBED: the 11-move tape
    //    for a (60 hp, 2 corridor) world is a legal, winning 11-move line in a (45, 2) world too —
    //    three blows fell the weaker warden, the fourth heal and fifth blow are simply wasted, and
    //    `press past` still passes its `warden_hp <= 0` guard. That is exactly the transfer that
    //    made the deleted test go red on 2026-07-25.
    //  * "a different tape LENGTH" is not enough either, because the choice indices ALIAS:
    //    `CORRIDOR_ON`, `HOARD_FORCE` and `HOARD_SEIZE` are all `0`, so a miscounted corridor walk
    //    slides along the winning line instead of erroring where you would expect it to.
    //
    // What IS airtight: the SAME warden (so the gate prefix replays move-for-move) and a DIFFERENT
    // corridor count. Too few corridors in the tape and the run is exhausted before `END` (no win);
    // too many and the surplus moves land on an ended scene (an illegal move). Both are refusals,
    // and such a day exists for every warden HP because the corridor draw covers 1..=3.
    let other = find_day(today.utc_day + 1, |d| {
        day_shape(&d.seed) != (my_hp, my_corridors) && day_shape(&d.seed).0 == my_hp
    });

    let state = std::sync::Arc::new(dreggnet_web::DescentState::new());
    state.ensure_today(); // today's world stays the default board
    state.open_day(&other.key, other.seed);
    let app = dreggnet_web::make_app_with_descent(state);

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
        "a run cannot rank in a world its moves do not win: {v}"
    );

    // …and nothing was retained on EITHER board.
    for board in [
        "/descent".to_string(),
        format!("/descent/leaderboard?day={}", other.key),
    ] {
        let (_, body) = get(&app, &board).await;
        assert!(
            !body.contains("wrong-world"),
            "a refused run must not create a row on {board}"
        );
    }

    // POSITIVE CONTROL — the control day is a perfectly good, open, submittable world; it is the
    // TAPE that it refused. Without this leg the refusal above would also be satisfied by a day the
    // endpoint could not open at all, and the test would prove nothing about the world deciding.
    let (status, v) = post_json(
        &app,
        "/descent/submit",
        serde_json::json!({
            "day": other.key,
            "player": "right-world",
            "moves": winning_tape(other.seed),
        }),
    )
    .await;
    assert_eq!(
        status,
        StatusCode::OK,
        "the control day itself is fine: {v}"
    );
    assert_eq!(v["ranked"], true, "its OWN winning tape ranks there: {v}");
}

/// **THE DAY IS THE BOARD — a run ranks on the day it names, and never on today's.**
///
/// This is the day-isolation property the product claim actually needs ("today's dungeon, the same
/// for everyone, and yesterday's run does not count"), and unlike the tape-transfer property it is
/// enforced by construction rather than by procgen luck: `ingest_run` files a run under its day key
/// and the board renders one day at a time. It is deterministic on every day of the year.
#[tokio::test]
async fn a_run_ranks_on_the_day_it_names_and_never_on_todays_board() {
    let today = dreggnet_web::descent::todays_day();
    let (moves, level, class) = demo_win();

    // A real day that is mechanically IDENTICAL to today — so the tape genuinely wins there and the
    // run really does rank. That is the strongest form of this test: the run is admitted on the
    // other day's board and STILL must not appear on today's.
    let mine = day_shape(&today.seed);
    let twin = find_day(today.utc_day + 1, |d| day_shape(&d.seed) == mine);

    let state = std::sync::Arc::new(dreggnet_web::DescentState::new());
    state.ensure_today();
    state.open_day(&twin.key, twin.seed);
    let app = dreggnet_web::make_app_with_descent(state);

    let (status, v) = post_json(
        &app,
        "/descent/submit",
        serde_json::json!({
            "day": twin.key,
            "player": "other-day-runner",
            "level": level,
            "class": class,
            "moves": moves,
        }),
    )
    .await;
    assert_eq!(status, StatusCode::OK, "{v}");
    assert_eq!(v["ranked"], true, "it wins in that day's world: {v}");

    let (_, other_board) = get(&app, &format!("/descent/leaderboard?day={}", twin.key)).await;
    assert!(
        other_board.contains("other-day-runner"),
        "the run ranks on the day it named"
    );
    let (_, todays_board) = get(&app, "/descent").await;
    assert!(
        !todays_board.contains("other-day-runner"),
        "a run filed under another day must NEVER appear on today's board: {todays_board}"
    );
}

/// **THE MEASURED LIMIT — two DIFFERENT days can accept ONE winning tape.**
///
/// Stated out loud because it silently broke a test that had been green for weeks. `daily_scene`
/// draws exactly two mechanical parameters — `warden_hp ∈ {45, 60}` and `deepening_rooms ∈ {1,2,3}`
/// — so the daily world has **six** playable shapes. The theme, the warden's name and every room's
/// prose also vary (the two worlds below are genuinely different objects: different seeds, different
/// scene sources, different `UniverseId`s), but none of that is reachable by a move tape. So a tape
/// that wins on one day wins on any other day sharing its shape, and "a run played yesterday cannot
/// be submitted for today" is FALSE for roughly one adjacent day-pair in six.
///
/// This is a LIMIT, not a hole: the day's world is public and deterministic, so a winning tape can
/// always be computed offline without playing — cross-day transfer buys an attacker nothing that
/// solving today's world does not already give them. What the board enforces is the claim it makes:
/// every ranked row is a move sequence that provably wins THAT day's world.
///
/// Falsifier: if `daily_scene` ever becomes day-discriminating (a per-day parameter a tape can
/// feel), this test goes red — and the in-window exclusion leg deleted above becomes viable again.
#[tokio::test]
async fn two_distinct_daily_worlds_can_accept_one_winning_tape() {
    let today = dreggnet_web::descent::todays_day();
    let mine = day_shape(&today.seed);
    let twin = find_day(today.utc_day + 1, |d| day_shape(&d.seed) == mine);

    // The two worlds are DISTINCT objects — this is not "the same day twice".
    assert_ne!(twin.seed.as_bytes(), today.seed.as_bytes());
    let (a, b) = (
        dreggnet_offerings::daily_descent::daily_scene(&today.seed),
        dreggnet_offerings::daily_descent::daily_scene(&twin.seed),
    );
    assert_ne!(
        a.source, b.source,
        "different days, different scene sources"
    );
    println!(
        "day {} [{}] warden_hp={} corridors={}  ==  day {} [{}] warden_hp={} corridors={}",
        today.key,
        a.title,
        a.warden_hp,
        a.deepening_rooms,
        twin.key,
        b.title,
        b.warden_hp,
        b.deepening_rooms
    );
    // The local calendar window, so the record shows the collision structure rather than asserting
    // it from arithmetic. Adjacent days collide about one pair in six; when they do, the deleted
    // exclusion leg went red for the day and green again the next — with no code change at all.
    for offset in -2i64..=2 {
        let d = procgen_dregg::descent_day::offline_day(
            u64::try_from(i64::try_from(today.utc_day).expect("a sane utc day") + offset)
                .expect("a sane utc day"),
        );
        println!("  {} shape = {:?}", d.key, day_shape(&d.seed));
    }

    // …and mechanically identical, so ONE tape wins in both.
    let (moves, _, _) = demo_win();
    let (twin_moves, _, _) = dreggnet_web::demo_win_for_seed(twin.seed);
    assert_eq!(
        moves, twin_moves,
        "same shape {mine:?} ⇒ the same winning tape, in two different days' worlds"
    );

    let state = std::sync::Arc::new(dreggnet_web::DescentState::new());
    state.ensure_today();
    state.open_day(&twin.key, twin.seed);
    let app = dreggnet_web::make_app_with_descent(state);
    for (day, player) in [
        (today.key.clone(), "shape-a"),
        (twin.key.clone(), "shape-b"),
    ] {
        let (status, v) = post_json(
            &app,
            "/descent/submit",
            serde_json::json!({ "day": day, "player": player, "moves": moves }),
        )
        .await;
        assert_eq!(status, StatusCode::OK, "the one tape wins in {day}: {v}");
        assert_eq!(v["ranked"], true, "{day}: {v}");
    }
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
