//! THE DESCENT — the spectator/provenance web surface, driven end to end.
//!
//! A stranger opens a URL and INDEPENDENTLY re-verifies someone's run of the daily descent — the
//! flagship's growth artifact (docs/GAME-STRATEGY.md Phase 3.2). This drives it with NO real network
//! (axum `ServiceExt::oneshot`):
//! - real runs are played on the substrate ([`DailyDescentOffering`] over a fixed daily seed — no
//!   live beacon), then their recorded playthroughs are ingested (UNTRUSTED) into the surface;
//! - `GET /descent/leaderboard` ranks only the runs that RE-VERIFY to the hoard on render — the
//!   honest winner appears, a forged run and a lost run do NOT (non-vacuous exclusion);
//! - `GET /descent/run/{id}` re-executes the recorded run: an honest run (won or lost) shows PASS,
//!   a tampered run shows FAIL — the verification is INDEPENDENT (re-execution, not a stored flag);
//! - a different day's seed yields a different board.

use std::sync::Arc;

use axum::body::Body;
use axum::http::{Request, StatusCode};

use dreggnet_offerings::DreggIdentity;
use dreggnet_offerings::character::{CharacterStore, InMemoryCharacterStore};
use dreggnet_offerings::daily_descent::{
    CORRIDOR_ON, DailyDescentOffering, DailyRun, GATE_FALL, GATE_HEAL, GATE_MEASURED, GATE_PRESS,
    GATE_RECKLESS, HOARD_FORCE, HOARD_SEIZE, KEY_TAKE,
};
use dreggnet_web::{DescentState, descent_router};
use dungeon_on_dregg::progression::WARRIOR;
use procgen_dregg::daily_seed;
use tower::ServiceExt; // oneshot

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

/// Drive a CAREFUL winning line to the hoard (works for any beacon-drawn warden HP / depth) — the
/// same shape `dreggnet-offerings`' own driven test uses.
fn drive_win<S: CharacterStore>(off: &DailyDescentOffering<S>, run: &mut DailyRun) {
    for _ in 0..64 {
        let Some(room) = run.current_room() else {
            break;
        };
        let ci = match room.as_str() {
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
            r if r.starts_with("corridor") => CORRIDOR_ON,
            other => panic!("unexpected room in a winning line: {other}"),
        };
        assert!(
            off.advance(run, ci).landed(),
            "a careful move was refused in {room}"
        );
    }
}

/// Drive a LOSING line: a reckless opener burns HP to the fall threshold, then fall into defeat.
fn drive_loss<S: CharacterStore>(off: &DailyDescentOffering<S>, run: &mut DailyRun) {
    assert!(
        off.advance(run, GATE_RECKLESS).landed(),
        "the reckless opener commits"
    );
    assert!(
        off.advance(run, GATE_FALL).landed(),
        "the fall into defeat commits"
    );
    assert_eq!(run.current_room().as_deref(), Some("downed"));
    assert!(off.advance(run, 0).landed(), "the defeat passage ends");
}

fn player(name: &str) -> DreggIdentity {
    DreggIdentity(name.to_string())
}

/// A won run, a lost run, and a FORGED (tampered) run for one day — the material a spectator surface
/// re-verifies. Returns the built `DescentState` (day "today" opened + all three ingested).
fn state_with_three_runs() -> Arc<DescentState> {
    let seed = daily_seed(&[3; 32]); // warden HP 45 (no field-dressing) -> a replay-clean honest win
    let off = DailyDescentOffering::new(InMemoryCharacterStore::new());

    // An honest WON run.
    let mut win = off.open_from_seed(player("alice"), seed).expect("open");
    off.choose_class(&win, WARRIOR).expect("class");
    drive_win(&off, &mut win);
    assert!(win.is_won(), "the careful line reached the hoard");
    assert!(
        off.verify(&win).verified,
        "OFFERING replay of the won run: {:?}",
        off.verify(&win).detail
    );

    // An honest LOST run.
    let mut lost = off.open_from_seed(player("bob"), seed).expect("open");
    drive_loss(&off, &mut lost);
    assert!(lost.is_ended() && !lost.is_won(), "a real lost run");

    // A FORGED run — swap the opening measured blow for a reckless one; the recorded chain no
    // longer replays. (Same forgery `dreggnet-offerings`' board test uses.)
    let mut forged_play = win.playthrough();
    if let Some(first) = forged_play.steps.first_mut() {
        first.choice_index = GATE_RECKLESS;
    }

    let state = Arc::new(DescentState::new());
    state.open_day("today", seed);
    state.ingest_run(
        "today",
        "today-alice",
        "alice",
        win.character().level(),
        win.character().class(),
        win.playthrough(),
    );
    state.ingest_run(
        "today",
        "today-bob",
        "bob",
        lost.character().level(),
        lost.character().class(),
        lost.playthrough(),
    );
    state.ingest_run("today", "today-mallory", "mallory", 1, 0, forged_play);
    state
}

/// The leaderboard ranks the re-verified winner and EXCLUDES a forged run and a lost run — the
/// re-verification happens on render (a forged/lost entry never trusts a stored flag), and it is
/// non-vacuous: the honest winner shows.
#[tokio::test]
async fn the_board_ranks_the_verified_winner_and_excludes_forgeries_and_losses() {
    let app = descent_router(state_with_three_runs());
    let (status, body) = get(&app, "/descent/leaderboard").await;
    assert_eq!(status, StatusCode::OK);

    // Non-vacuous: the honest winner is ranked and links to its run-card.
    assert!(
        body.contains("alice"),
        "the verified winner appears: {body}"
    );
    assert!(
        body.contains("/descent/run/today-alice"),
        "the winning row links to its run-card: {body}"
    );

    // Excluded: the forged run is not on the board...
    assert!(
        !body.contains("mallory"),
        "a forged run does NOT appear on the no-cheat board: {body}"
    );
    // ...and neither is the lost run (it never reached the hoard).
    assert!(
        !body.contains("today-bob"),
        "a lost run does NOT rank (it did not reach the hoard): {body}"
    );
    assert!(
        body.contains("no-cheat"),
        "the board states its no-cheat property"
    );
}

/// A run-card PROVES an honest run (re-executed to PASS) and FAILS a forged one — the verification is
/// independent re-execution, not a trusted flag.
#[tokio::test]
async fn a_run_card_proves_an_honest_run_and_fails_a_forgery() {
    let app = descent_router(state_with_three_runs());

    // The honest WON run: PASS + the survived-to-the-hoard outcome.
    let (status, won) = get(&app, "/descent/run/today-alice").await;
    assert_eq!(status, StatusCode::OK);
    assert!(
        won.contains("Independent verification · PASS"),
        "an honest run re-executes to PASS: {won}"
    );
    assert!(won.contains("SURVIVED"), "the won outcome shows: {won}");
    assert!(won.contains("hoard"), "the hoard seize shows: {won}");

    // The honest LOST run: still PASS (an honest record re-verifies), outcome FELL / dead.
    let (_s, lost) = get(&app, "/descent/run/today-bob").await;
    assert!(
        lost.contains("Independent verification · PASS"),
        "an honest lost run also re-verifies to PASS: {lost}"
    );
    assert!(lost.contains("FELL"), "the lost outcome shows: {lost}");
    assert!(lost.contains("dead"), "the hardcore death shows: {lost}");

    // The FORGED run: FAIL — not a fake pass.
    let (_s, forged) = get(&app, "/descent/run/today-mallory").await;
    assert!(
        forged.contains("Independent verification · FAIL"),
        "a tampered run shows FAIL: {forged}"
    );
    assert!(
        !forged.contains("Independent verification · PASS"),
        "a tampered run is NOT a fake pass: {forged}"
    );
    assert!(
        forged.contains("forged") || forged.contains("tampered"),
        "the failure is named: {forged}"
    );
}

/// A different day's seed yields a different world — its board is a different page (different title /
/// players), proving the day selector is real.
#[tokio::test]
async fn a_different_days_board_differs() {
    let seed_a = daily_seed(&[3; 32]); // Rimebound, warden 45, depth 1
    let seed_b = daily_seed(&[22; 32]); // Ember, warden 45, depth 3
    let off = DailyDescentOffering::new(InMemoryCharacterStore::new());

    let mut a = off.open_from_seed(player("anna"), seed_a).expect("open a");
    drive_win(&off, &mut a);
    let mut b = off.open_from_seed(player("boris"), seed_b).expect("open b");
    drive_win(&off, &mut b);

    let state = Arc::new(DescentState::new());
    state.open_day("day-a", seed_a);
    state.open_day("day-b", seed_b);
    state.ingest_run(
        "day-a",
        "a-anna",
        "anna",
        a.character().level(),
        a.character().class(),
        a.playthrough(),
    );
    state.ingest_run(
        "day-b",
        "b-boris",
        "boris",
        b.character().level(),
        b.character().class(),
        b.playthrough(),
    );

    let app = descent_router(state);
    let (_s, board_a) = get(&app, "/descent/leaderboard?day=day-a").await;
    let (_s, board_b) = get(&app, "/descent/leaderboard?day=day-b").await;

    assert!(
        board_a.contains("anna") && !board_a.contains("boris"),
        "day-a shows only its runs"
    );
    assert!(
        board_b.contains("boris") && !board_b.contains("anna"),
        "day-b shows only its runs"
    );
    assert_ne!(board_a, board_b, "the two days' boards differ");
}
