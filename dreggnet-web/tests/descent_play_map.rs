//! **The play page must SHOW the dungeon — and its numbers must be the game's numbers.**
//!
//! `/descent/play` is the flagship front door: a stranger opens a URL and presses a button. The
//! page paints its surface in the browser (the wasm-driven controller builds DOM directly), so the
//! shaft map and the light clock live in `app.js`, not in a server-rendered `ViewNode`. That buys
//! reactivity and costs a MIRROR: the page carries the world's constants (`BREATH`, `CAP`,
//! `FLOORS`, `RELICS`, the custody codes) in order to size a bar and label a row.
//!
//! A mirror nobody checks is a bug with a delay fuse — the day the game's light clock changes, the
//! page keeps drawing the old ceiling and lies to every player. So this suite pins EACH mirrored
//! constant against the Rust constant it mirrors, by reading the ACTUAL served script. It also
//! pins that the map and the meters are in that script at all, so the picture cannot quietly
//! regress to the four bare stat boxes and a row of custody integers it replaced.
//!
//! **What may be mirrored at all is the second question this suite answers.** Guardian vitality is
//! NOT a world constant — it is drawn from the committed day-seed, sixteen maps of it — so it
//! cannot live in the script as a literal, and a mirror test that pinned it there certified a
//! number wrong on fifteen days in sixteen. That pin is now inverted: the script must carry no
//! day-0 table, must take the day's vitalities from the served descriptor, and must open no world
//! when it cannot.
//!
//! What this does NOT claim: that the browser paints correctly (no DOM is exercised here — the
//! action-menu module has its own `descent_play_actions.mjs` suite). It claims the served script
//! contains the map and the meters, and that every world number in it equals the game's.

use axum::body::Body;
use axum::http::{Request, StatusCode};
use tower::ServiceExt; // oneshot

use dreggnet_web::make_app;
use dungeon_on_dregg::descent::{BANKED, BREATH, CAP, CARRIED, FLOORS, RELICS, guard_hp};

const APP_JS: &str = "/descent/play/static/app.js";

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

async fn play_script() -> String {
    let app = make_app();
    let (status, body) = get(&app, APP_JS).await;
    assert_eq!(status, StatusCode::OK, "the play controller serves");
    body
}

/// **The mirror is PINNED.** Every world number the browser controller carries is the number the
/// game carries. Change `BREATH` in the Lean-sourced constants and this fails until the page agrees.
#[tokio::test]
async fn the_browser_mirror_of_the_worlds_constants_matches_the_game() {
    let js = play_script().await;

    for (name, value) in [
        ("FLOORS", FLOORS),
        ("RELICS", RELICS as u64),
        ("BREATH", BREATH),
        ("CAP", CAP),
        ("CARRIED", CARRIED),
        ("BANKED", BANKED),
    ] {
        let decl = format!("const {name} = {value};");
        assert!(
            js.contains(&decl),
            "the play page mirrors {name} as `{decl}` — it does not, so its bars are sized against \
             a number the game no longer uses"
        );
    }
}

/// **THE GUARDIAN TABLE IS NOT A CONSTANT AND MUST NOT BE MIRRORED AS ONE.**
///
/// Guardian vitality is DRAWN FROM THE COMMITTED DAY-SEED — sixteen maps, and day 0 is one of
/// them. The page used to carry `const GUARD_HP = [0, 1, 1, 2, 2];`, day 0's table, and this suite
/// used to PIN it, so the mirror check certified a number that was wrong on fifteen days in
/// sixteen: a `0/1` guardian bar over a two-point guardian, and a hoard still shut after the blow
/// the picture promised would open it.
///
/// So the pin inverts. The script must carry NO day-0 table at all; it must take the day's
/// vitalities from the served descriptor (or the shell's fallback attribute) and REFUSE TO OPEN A
/// WORLD if neither resolves — never silently fall back to a default table, which is the same bug
/// with a comment on it. What the numbers must equal is pinned where the server can compare them
/// to a real deployed session (`descent_play::tests::the_descriptor_publishes_the_days_own_guardian_vitalities`).
#[tokio::test]
async fn the_browser_takes_todays_guardian_vitalities_from_the_day_and_never_a_literal() {
    let js = play_script().await;

    // The exact literal the page used to ship, plus any other hard-coded table shaped like a
    // guardian row. Its return is the regression this test exists to catch.
    let day_zero = format!(
        "[{}]",
        (0..=FLOORS)
            .map(|d| guard_hp(d).to_string())
            .collect::<Vec<_>>()
            .join(", ")
    );
    assert!(
        !js.contains(&format!("const GUARD_HP = {day_zero};")),
        "the play page hard-codes day 0's guardian table `{day_zero}` again — it is right on one \
         drawn day in sixteen and draws the wrong guardian on the rest"
    );
    assert!(
        js.contains("let GUARD_HP = null;"),
        "the guardian table is a per-day value the page receives, so it starts EMPTY"
    );

    // It arrives from the day, both ways: the descriptor the tab fetches, and the shell attribute
    // that keeps a failed fetch honest rather than defaulting.
    assert!(
        js.contains("today.guardHp") && js.contains("root.dataset.guardHp"),
        "the page reads the day's vitalities from `day.json` with the shell's `data-guard-hp` as \
         the fallback"
    );
    // FAIL-CLOSED: no map, no world. A page that opened a run anyway would be drawing a guardian
    // it made up.
    assert!(
        js.contains("if (!GUARD_HP) {") && js.contains("no world was opened"),
        "a page that cannot resolve today's guardians opens no world at all"
    );

    // And the meter/pressure/glyph readers all go through it rather than a re-derived rule.
    for reader in ["GUARD_HP[floor]", "GUARD_HP[sim.depth]"] {
        assert!(
            js.contains(reader),
            "the guardian picture is sized off the day's table (`{reader}`)"
        );
    }
}

/// **The map is on the page.** Not "a map function exists somewhere" — the shaft grid, one column
/// per relic, the pack row and the vault row, and the legend that makes the glyphs mean something.
#[tokio::test]
async fn the_play_page_paints_the_shaft_with_one_column_per_relic() {
    let js = play_script().await;

    assert!(
        js.contains("function buildMap(") && js.contains("nd-map"),
        "the shaft map is built and mounted"
    );
    assert!(
        js.contains("const MAP_COLS = 3 + RELICS;"),
        "the board is marker + way + guardian, then ONE COLUMN PER RELIC — that fixed column is \
         what lets a player watch a relic travel out of the dark"
    );
    for row_marker in ["GLYPH_PACK", "GLYPH_VAULT"] {
        assert!(
            js.contains(row_marker),
            "the {row_marker} row is on the map: carried-but-losable and banked-and-yours are \
             different states and must LOOK different"
        );
    }
    assert!(
        js.contains("nd-legend"),
        "the glyph legend rides with the board"
    );
    // The board marks what can be acted on from the OFFERING's own action list, never from a rule
    // re-derived in the browser. This is the line that keeps the picture honest.
    assert!(
        js.contains("a.enabled === true"),
        "the actionable marks are read off the offering's action list, not guessed"
    );
}

/// **The light clock and the carry ceiling are meters.** The page used to show `light spent 8` with
/// no denominator anywhere — the single most important number in the game, unreadable.
#[tokio::test]
async fn the_play_page_paints_the_light_and_the_carry_ceiling_as_meters() {
    let js = play_script().await;

    assert!(
        js.contains("function meter(") && js.contains("nd-meter-fill"),
        "there is a real filled meter, not a bare integer"
    );
    assert!(
        js.contains("meter(\"light\", Math.max(0, BREATH - sim.spent), BREATH"),
        "the light meter shows REMAINING light against the full clock, so the bar EMPTIES as it \
         burns down"
    );
    assert!(
        js.contains("meter(\"pack\", carried, Math.max(0, CAP - sim.depth)"),
        "the carry meter's CEILING attenuates with depth (`pack + depth <= CAP`) — a fixed \
         denominator would hide half the game's tension"
    );
    assert!(
        js.contains("function pressures("),
        "the page says out loud what the player is about to lose to"
    );
    // The regression guard: the old surface.
    assert!(
        !js.contains("stat(\"light spent\""),
        "the denominator-less stat boxes are gone"
    );
    assert!(
        !js.contains("sim.custody.join("),
        "the raw custody integer list (`4 · 1 · 2 · 3 · …`, meaningless to a human) is gone"
    );
}

/// The page's stylesheet has to actually carry the classes the controller mounts, or the map paints
/// as a column of undecorated spans.
#[tokio::test]
async fn the_shell_styles_the_map_and_the_meters() {
    let app = make_app();
    let (status, page) = get(&app, "/descent/play").await;
    assert_eq!(status, StatusCode::OK);
    for class in [
        ".nd-map",
        ".nd-cell",
        ".nd-cell.actionable",
        ".nd-meter-track",
        ".nd-meter-fill",
        ".nd-pill",
        ".nd-legend",
    ] {
        assert!(
            page.contains(class),
            "the play shell styles `{class}` — the controller mounts it"
        );
    }
}
