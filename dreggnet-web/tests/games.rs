//! **BOTH PORTFOLIO GAMES, DRIVEN THROUGH THE WEB CATALOG.**
//!
//! `catalog.rs` proved the three heterogeneous offerings (dungeon / council / market) play in the
//! browser. This proves the two GAMES do — with no real network (axum `ServiceExt::oneshot`):
//!
//! - `GET /offerings` lists **tug** and **automatafl** beside the rest;
//! - **automatafl** opens, paints its board as a clickable `CoordGrid` (a real POST button per
//!   affordance-bearing square), and a full simultaneous turn plays through the browser:
//!   `select` → `commit` (both seats) → `reveal` (both) → `resolve` — each POST a real landed turn,
//!   the board visibly moving; an ILLEGAL move (a diagonal) is REFUSED and commits nothing;
//! - **tug** opens and a real play LANDS for a browser user (the seat-claiming adapter), while a
//!   third browser user is refused as a spectator;
//! - `verify` holds for both committed chains.

use std::sync::Arc;

use axum::body::Body;
use axum::http::{Request, StatusCode};
use dreggnet_web::{CatalogState, catalog_router};
use tower::ServiceExt; // oneshot

mod common;

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

/// POST a `{turn, arg}` affordance form as web user `user` (a `dregg_user` cookie), carrying the
/// route authority the play surface stamped into its own form. Both games here (`automatafl`,
/// `tug`) are SPINED keys: a bare `turn=&arg=` is `409 invalid game reference`, and every play
/// line in this file would stop before the executor.
async fn post(
    app: &axum::Router,
    uri: &str,
    turn: &str,
    arg: i64,
    user: &str,
) -> (StatusCode, String) {
    common::post_act(app, uri, turn, arg, user).await
}

fn app() -> axum::Router {
    common::guard(catalog_router(Arc::new(CatalogState::new())))
}

/// **POST an act as `user`, carrying the route authority read off `authority_of`'s page.**
///
/// ⚑ WHY THE TWO IDENTITIES ARE SEPARATE HERE. `common::post_act` reads the authority off the
/// POSTER's own page, which is right for a player and impossible for a SPECTATOR: a viewer holding
/// no seat is served the viewer-blind public projection, which carries no control at all and
/// therefore no `game_*` fields — so a spectator posting through `post_act` presents no authority,
/// is answered `409 invalid game reference`, and never reaches the seat gate the test is about. (The
/// shared silent-`/act` tripwire catches exactly that and killed this test until it was split, which
/// is the tripwire doing its job.)
///
/// The authority is bound to `{offering, session, incarnation, generation, pre-head}` and NOT to the
/// viewer (`common::authority_suffix`), so a seat's page is where a real attacker would get one:
/// a shoulder-surfed form, a shared screen, a copied `curl`. Posting THAT as a third identity is the
/// honest spectator attack — everything about the request is valid except who is making it.
async fn post_act_as_other(
    app: &axum::Router,
    act_uri: &str,
    turn: &str,
    arg: i64,
    user: &str,
    authority_of: &str,
) -> (StatusCode, String) {
    let authority =
        common::authority_suffix(app, act_uri, Some(&format!("dregg_user={authority_of}"))).await;
    assert!(
        !authority.is_empty(),
        "the seat's own page must carry a route authority, or this posts nothing to refuse"
    );
    let cookie = format!("dregg_user={user}");
    let response = app
        .clone()
        .oneshot(
            Request::builder()
                .method("POST")
                .uri(act_uri)
                .header("content-type", "application/x-www-form-urlencoded")
                .header("cookie", &cookie)
                .body(Body::from(format!("turn={turn}&arg={arg}{authority}")))
                .unwrap(),
        )
        .await
        .unwrap();
    let status = response.status();
    let bytes = axum::body::to_bytes(response.into_body(), usize::MAX)
        .await
        .unwrap();
    (status, String::from_utf8_lossy(&bytes).to_string())
}

/// GET a play surface AS `user` — the page that user's browser would be looking at, and therefore
/// the only page whose controls are theirs to press.
async fn get_as(app: &axum::Router, uri: &str, user: &str) -> String {
    let (status, body) =
        common::get_with_cookie(app, uri, Some(&format!("dregg_user={user}"))).await;
    assert_eq!(status, StatusCode::OK, "{body}");
    body
}

/// **THE OUTCOME, not the copy** — how many turns the offering's own replay proof accepts on this
/// session's committed chain right now (`GET …/verify` → `{"verified":…,"turns":N}`).
///
/// Every "did that land?" / "did that commit nothing?" assertion in this file is anchored here
/// rather than on a banner string: a rendered notice is what the page SAYS, and this is what the
/// chain HOLDS. A refusal that quietly committed, or a landing that quietly did not, moves this
/// number and no amount of correct-looking copy hides it.
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

/// **The `{turn, arg}` this user's own page OFFERS them, ENABLED** — derived, never a literal.
///
/// ⚑ `arg` is an INDEX into the offering's LIVE decision list, not a stable move name. `games.rs`
/// posted a hardcoded `("comp", 3)` schedule, which was legal only while tug ran a fixed per-seat
/// action order; since the seats CHOOSE, index 3 names whatever the deal put there, so the press was
/// refused — correctly — as a control that is not on the current surface, and every assertion after
/// it was about a turn that never happened. Reading the pair off the served form is what a browser
/// does, so this test is about "a browser user's offered play lands" and not about the engine's
/// ordering. (`common::first_offered_act`'s own doc records the same drift on `demo_playthrough`.)
fn live_press(page: &str) -> Option<(String, i64)> {
    common::offered_acts(page)
        .into_iter()
        .find(|act| act.enabled)
        .map(|act| (act.turn, act.arg))
}

async fn offered_press(app: &axum::Router, base: &str, user: &str) -> Option<(String, i64)> {
    live_press(&get_as(app, base, user).await)
}

/// **Which of these browser users is offered a live control, and what it is.** Tug ALTERNATES —
/// only the seat that owes the next move is offered an enabled row, and after a cut it is the
/// RESPONDER who owes it, not the next seat in a rota — so "whose turn is it" is a question for the
/// served pages, never for a schedule written into a test. `None` when neither is owed anything,
/// which is how a driven round knows it is over.
///
/// `just_pressed` is consulted LAST. A tug open + advance is seconds of real Lean work per call, so
/// the page fetches here dominate this file's wall clock: asking the other seat first is right far
/// more often than not (a cut is answered by the opponent) and roughly halves the renders.
async fn whoever_moves(
    app: &axum::Router,
    base: &str,
    users: [&'static str; 2],
    just_pressed: Option<&str>,
) -> Option<(&'static str, String, i64)> {
    let mut order = users;
    if just_pressed == Some(order[0]) {
        order.swap(0, 1);
    }
    for user in order {
        if let Some((turn, arg)) = offered_press(app, base, user).await {
            return Some((user, turn, arg));
        }
    }
    None
}

/// The automatafl board index of `(x, y)` — derived from the board's OWN width
/// ([`dregg_automatafl::game::N`], the stock two-player game), never a literal, so a board-size
/// change moves this test with it instead of silently addressing the wrong squares.
fn idx(x: i64, y: i64) -> i64 {
    y * dregg_automatafl::game::N as i64 + x
}

/// BOTH games appear in the catalog, each with a play link.
#[tokio::test]
async fn the_catalog_lists_both_portfolio_games() {
    let app = app();
    let (status, body) = get(&app, "/offerings").await;
    assert_eq!(status, StatusCode::OK);
    // ⚑ THE LINK IS THE TABLE DOOR, not a shared session id. Both of these are SEAT-LOCKED
    // two-player hidden-move games, so the catalog advertises their table-minting front door
    // *instead of* `/offerings/{key}/session/{key}-web`: the printed shared id was a seat race,
    // and an asserted-label identity could render the opponent's private projection on it.
    for key in ["tug", "automatafl"] {
        let door = dreggnet_web::table_seats::lock_for_key(key)
            .unwrap_or_else(|| panic!("{key} is a seat-locked table game"));
        assert!(
            body.contains(&format!("href=\"{}\"", door.route)),
            "the catalog opens a {key} table at {}: {body}",
            door.route
        );
        assert!(
            !body.contains(&format!("/offerings/{key}/session/")),
            "and never re-advertises a shared, guessable {key} table id: {body}"
        );
    }
    assert!(
        body.contains("Automatafl"),
        "the automatafl card is present"
    );
    assert!(body.contains("Multiway-Tug"), "the tug card is present");
}

/// **A full automatafl turn plays in the browser.** The board paints as a clickable CoordGrid; two
/// seats seal a move, both reveal, the turn resolves — every POST a real landed turn — and the board
/// visibly changes. An illegal (diagonal) move is REFUSED, nothing committed.
#[tokio::test]
async fn a_full_automatafl_turn_plays_through_the_catalog() {
    let app = app();
    let base = "/offerings/automatafl/session/auto-1";

    // The board renders: a CoordGrid of clickable squares (a POST button per affordance-bearing
    // cell), the automaton marked, and the goal squares painted.
    let (status, body) = get(&app, base).await;
    assert_eq!(status, StatusCode::OK);
    assert!(
        body.contains("coordgrid"),
        "the board paints as a CoordGrid"
    );
    assert!(
        body.contains("name=\"turn\" value=\"select\""),
        "a board square is a real POST affordance (clickable)"
    );
    assert!(body.contains('@'), "the automaton is painted");
    assert!(
        body.contains("COMMIT (both seats seal a move)"),
        "the match opens in the commit phase"
    );

    // ── Seat A (browser user `alice`): select the stock attractor at (3,1), seal a move to (3,3).
    let (_, body) = post(&app, &format!("{base}/act"), "select", idx(3, 1), "alice").await;
    assert!(
        body.contains("Turn committed"),
        "the select lands a real turn: {body}"
    );
    // With a piece selected, its ROOK LINE is lit — the legal-move highlight-set reaches the HTML.
    assert!(
        body.contains("highlighted"),
        "the selected piece lights its legal moves in the browser"
    );

    // An ILLEGAL move — (3,1) → (4,2) is a diagonal. REFUSED; nothing commits.
    //
    // ⚑ THE REFEREE'S OWN SENTENCE, and the CHAIN — not the concatenation. This asserted
    // `contains("Refused: illegal move")`, which is not a claim about the referee at all: the notice
    // is `Refused: {what you pressed} · {why}`, so naming the pressed control (a real improvement,
    // and the thing that tells a blind player WHICH of four buttons was refused) split the literal
    // and reddened this line while the rule it is about was working perfectly. The refusal had NOT
    // broken. What is checked now is the referee's verdict, quoted from the rule it enforces, plus
    // the only thing that actually settles "nothing committed": the committed chain did not grow.
    let before = committed_turns(&app, base).await;
    let (_, body) = post(&app, &format!("{base}/act"), "commit", idx(4, 2), "alice").await;
    assert!(
        body.contains("Refused")
            && body.contains(&format!("illegal move ({},{}) → ({},{})", 3, 1, 4, 2)),
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

    // The legal seal lands. The POST re-renders AS alice (the viewer-aware host boundary), so the
    // sealer sees HER OWN move revealed — the opponent, not the sealer, is the one kept in the fog.
    let (_, body) = post(&app, &format!("{base}/act"), "commit", idx(3, 3), "alice").await;
    assert!(body.contains("Turn committed"), "the seal lands: {body}");
    assert!(
        body.contains("YOUR sealed move"),
        "the sealer sees THEIR OWN sealed move on their own surface (per-viewer, not viewer-blind fog): {body}"
    );

    // ── Seat B (browser user `bob`): select (7,1), seal to (7,3).
    let (_, body) = post(&app, &format!("{base}/act"), "select", idx(7, 1), "bob").await;
    assert!(body.contains("Turn committed"), "bob claims seat B: {body}");
    let (_, body) = post(&app, &format!("{base}/act"), "commit", idx(7, 3), "bob").await;
    assert!(body.contains("Turn committed"));
    // Rendered AS bob now: bob sees HIS own seal, and ALICE's sealed move is FOG to him (only the
    // commitment shows) — the simultaneous-secret fog, correctly keyed to the OPPONENT's viewpoint.
    assert!(
        body.contains("move SEALED"),
        "the opponent's sealed move is fog to bob (only the commitment shows): {body}"
    );
    assert!(
        body.contains("REVEAL (both moves sealed"),
        "both seals in → the reveal phase: {body}"
    );

    // ── The reveals, then the resolution.
    let (_, body) = post(&app, &format!("{base}/act"), "reveal", 0, "alice").await;
    assert!(body.contains("Turn committed"), "alice opens her seal");
    let (_, body) = post(&app, &format!("{base}/act"), "reveal", 0, "bob").await;
    assert!(body.contains("Turn committed"), "bob opens his seal");
    assert!(
        body.contains("RESOLVE (both open"),
        "both open → the resolution is one turn away: {body}"
    );

    let (_, body) = post(&app, &format!("{base}/act"), "resolve", 0, "alice").await;
    assert!(body.contains("Turn committed"), "the resolution lands");
    assert!(
        body.contains("Automatafl · turn 1"),
        "the resolved turn counter advanced in the browser: {body}"
    );
    // The board MOVED: the attractor that was at (3,1) is gone from that square, and the pieces
    // landed. (The reference `apply_turn` decides exactly where; the in-crate tests pin that.)
    assert!(body.contains("coordgrid"), "the resolved board re-paints");

    // The whole committed chain re-verifies by the offering's own proof.
    let (status, body) = get(&app, &format!("{base}/verify")).await;
    assert_eq!(status, StatusCode::OK);
    assert!(
        body.contains("\"verified\":true"),
        "the committed automatafl match verifies: {body}"
    );
}

/// **The server-form automatafl board renders as a POLISHED, clickable grid — not the minimal prior
/// CSS.** This pins the ACTUAL deployed no-JS path (`render_catalog_forms` → `.coordgrid`/`.cell`/
/// `tag-*` + the page `STYLE`): the board is a centered framed grid of SQUARE cells (`aspect-ratio:
/// 1/1`), the clickable squares (`form.cell`) get a hover/lift + pointer cursor, a highlighted legal
/// move gets a green ring, and the role tints paint (automaton = cyan glow, selected = amber, target
/// = green, vacant = dim). The design is ported from deos-view's `.deos-cell`, but onto THIS path —
/// the one the deployed demo actually serves.
#[tokio::test]
async fn the_server_form_automatafl_board_is_polished() {
    let app = app();
    let base = "/offerings/automatafl/session/auto-css";

    // Open the board and light a piece's legal moves (so a `highlighted` legal-move cell is present).
    let (status, body) = get(&app, base).await;
    assert_eq!(status, StatusCode::OK);
    let (_, body_after) = post(&app, &format!("{base}/act"), "select", idx(3, 1), "alice").await;

    // ── THE MARKUP: a coordgrid of square cells, clickable POST forms, tinted + highlighted.
    // N-GENERIC: the expected markup is built from the board's own width, and the `checkered` class
    // (the odd-width checkerboard) is decided by the renderer rather than by a board size in CSS.
    let n = dregg_automatafl::game::N;
    assert!(
        body.contains(&format!(
            "<div class=\"coordgrid checkered\" style=\"grid-template-columns:repeat({n},1fr)\">"
        )),
        "the board is an {n}-wide coordgrid (the board's own width): {body}"
    );
    assert!(
        body.contains("<form class=\"cell") && body.contains("<button type=\"submit\">"),
        "clickable squares are POST forms with a submit button"
    );
    assert!(
        body.contains("tag-accent") && body.contains('@'),
        "the automaton paints with the accent tint"
    );
    assert!(
        body_after.contains("cell highlighted")
            || body_after.contains("highlighted good")
            || body_after.contains("tag-good"),
        "a selected piece lights its legal moves (highlighted / good tint): {body_after}"
    );

    // ── THE CSS: the polished board rules are present (NOT the minimal prior stylesheet).
    // The grid frame + square cells.
    assert!(
        body.contains(".coordgrid{display:grid")
            && body.contains("max-width:32rem")
            && body.contains("border-radius:14px"),
        "the board is a centered, framed grid"
    );
    assert!(
        body.contains(".coordgrid .cell{") && body.contains("aspect-ratio:1/1"),
        "cells are square (aspect-ratio:1/1)"
    );
    // Clickable cells: pointer cursor + a hover lift.
    assert!(
        body.contains(".coordgrid form.cell{padding:0;cursor:pointer}"),
        "clickable squares get a pointer cursor"
    );
    assert!(
        body.contains(".coordgrid form.cell:hover{") && body.contains("transform:translateY(-1px)"),
        "clickable squares lift on hover"
    );
    // The highlighted legal-move ring.
    assert!(
        body.contains(".coordgrid .cell.highlighted{")
            && body.contains("box-shadow:inset 0 0 0 1px var(--good)"),
        "a highlighted legal move gets a green ring"
    );
    // The role tints: accent (cyan automaton glow), warn (amber selected), good (green), muted (dim).
    assert!(
        body.contains(".coordgrid .cell.tag-accent{") && body.contains("radial-gradient"),
        "the automaton cell has a cyan radial glow"
    );
    assert!(
        body.contains(".coordgrid .cell.tag-warn{") && body.contains("var(--warn)"),
        "the selected cell tints amber"
    );
    assert!(
        body.contains(".coordgrid .cell.tag-good{") && body.contains(".coordgrid .cell.tag-muted{"),
        "legal-target (green) + vacant (dim) tints are defined"
    );
}

/// **A tug play lands for a browser user.** The seat-claiming adapter seats the first two browser
/// users; a third is a spectator (refused, nothing commits), and the chain verifies.
///
/// ⚑ The three presses are settled by ONE exact count on the committed chain at the end, not by
/// three banners: `genesis + 2` means both plays landed AND the spectator's press committed nothing.
/// It is one number because it has to be — `verify` REPLAYS the round (a fresh open plus one real
/// executor turn per committed turn), so a count taken between every press would make this test
/// quadratic in real Lean work against a live kill budget.
#[tokio::test]
async fn a_tug_play_lands_for_a_browser_user() {
    let app = app();
    let base = "/offerings/tug/session/tug-1";

    // ⚑ ONE page fetch, and the opening press is read off IT. A tug open and a tug advance are each
    // seconds of real Lean work, so every avoidable round-trip here is spent against this file's
    // budget: the page that proves the surface renders is the same page that names the move.
    let opened = get_as(&app, base, "alice").await;
    assert!(opened.contains("Multiway-Tug"), "the tug surface renders");
    assert!(
        opened.contains("Guild 0") && opened.contains("Guild 6"),
        "the seven guild lanes paint"
    );

    // A browser user CLAIMS seat A by acting — and the play lands a REAL turn (before the adapter,
    // every web play was refused as "actor holds no seat"). The press is whatever ALICE'S OWN PAGE
    // offers her; see `offered_press` for why a literal pair cannot be used here.
    let (turn, arg) =
        live_press(&opened).expect("the opening surface offers a claimable-seat move");
    let (_, body) = post(&app, &format!("{base}/act"), &turn, arg, "alice").await;
    assert!(
        body.contains("Turn committed"),
        "a browser user's play lands a real turn ({turn} {arg}): {body}"
    );

    // Seat B is claimed by the next browser user, off HIS OWN page: in an alternating game the
    // re-render of seat A's act is not seat B's move, so re-reading A's response would hand B a
    // control that is not theirs.
    let (turn, arg) = offered_press(&app, base, "bob")
        .await
        .expect("with seat A taken, the second browser user is offered the other seat's move");
    let (_, body) = post(&app, &format!("{base}/act"), &turn, arg, "bob").await;
    assert!(
        body.contains("Turn committed"),
        "the second browser user claims seat B and plays ({turn} {arg}): {body}"
    );

    // ── THE REFUSAL POLE, in this same process and on this same chain. A THIRD browser user is a
    // spectator. Carol posts the EXACT control the seat to move is legitimately offered, carrying
    // that seat's own valid route authority (see `post_act_as_other`) — so the ONLY thing that
    // differs between the two landings above and the refusal here is WHO is pressing, which is what
    // makes this a test of the SEAT gate and not of a stale argument or a missing form token.
    let (mover, turn, arg) = whoever_moves(&app, base, ["alice", "bob"], Some("bob"))
        .await
        .expect("with both seats held, one of them owes the next move");
    let (status, body) =
        post_act_as_other(&app, &format!("{base}/act"), &turn, arg, "carol", mover).await;
    assert_eq!(status, StatusCode::OK, "{body}");
    assert!(
        body.contains("Refused") && body.contains("spectator"),
        "a third browser user is refused AS A SPECTATOR, not for some other reason ({turn} {arg}): {body}"
    );

    // THE OUTCOME, and it settles all three presses at once: EXACTLY the genesis plus the two seat
    // claims. Bigger and the spectator's refusal committed something; smaller and one of the two
    // "Turn committed" banners was over a chain that never grew. (That carol was answered as a
    // SPECTATOR is itself only reachable once both seats are genuinely held.)
    assert_eq!(
        committed_turns(&app, base).await,
        3,
        "genesis + seat A's play + seat B's play, and the spectator's press on neither side of it"
    );
}

/// A browser match now reaches an executor-scored terminal result rather than
/// stopping after the eighth placement with no winner, no charm, and a stale
/// "to move" banner. Both browser identities keep their claimed seats across
/// the full alternating round. The browser then fires the separately surfaced
/// SCORE affordance, preserving the Offering invariant that one press is one
/// executor turn and one receipt; `/verify` re-drives every input.
///
/// ⚑ **THE ROUND IS DRIVEN OFF THE SERVED PAGES, NOT OFF A SCHEDULE.** This test used to POST a
/// literal `[("comp",3), ("comp",3), ("gift",2), …]` list, which described an engine that no longer
/// exists twice over: `arg` is an INDEX into the acting seat's LIVE `legal_decisions()` (so no fixed
/// index names a fixed move), and the round is not eight presses — a Gift or a Competition PRESENTS
/// a cut that the OPPONENT then answers, so [`dregg_multiway_tug::reference::ROUND_TURNS`] committed
/// turns are 8 actions plus 4 responses. The old schedule was therefore refused on its first press
/// and, had it not been, would have asserted a nine-turn chain against a fourteen-turn round.
///
/// What is asserted is the invariant, derived rather than transcribed: each press is exactly one
/// committed executor turn, the round runs to its own end, and the whole chain replays.
#[tokio::test]
async fn a_full_tug_match_scores_and_replays_through_the_web_surface() {
    let app = app();
    let base = "/offerings/tug/session/tug-full-scored";

    // Drive the round to its end: at each step ask the two browser identities' OWN pages which of
    // them is offered a live control, and press it. ⚑ The chain is read ONCE, at the end, not per
    // press: a tug open and a tug advance are seconds of real Lean work apiece, and `/verify`
    // REPLAYS the whole chain, so a per-press verify makes this file quadratic against a real kill
    // budget. `turns == genesis + presses` at the end says the same thing about every press.
    let mut presses = 0_u64;
    let mut last_actor: Option<&'static str> = None;
    while let Some((actor, turn, arg)) =
        whoever_moves(&app, base, ["alice", "bob"], last_actor).await
    {
        let (status, body) = post(&app, &format!("{base}/act"), &turn, arg, actor).await;
        assert_eq!(status, StatusCode::OK);
        assert!(
            body.contains("Turn committed"),
            "{actor} press #{presses} ({turn} {arg}) did not land: {body}"
        );
        presses += 1;
        last_actor = Some(actor);
        assert!(
            presses <= 64,
            "the round must terminate; it is still offering moves after {presses} presses"
        );
    }

    // The shape the engine itself declares: every round turn, plus the separately surfaced SCORE.
    let round_turns = dregg_multiway_tug::reference::ROUND_TURNS;
    assert_eq!(
        presses,
        round_turns + 1,
        "the whole round plus the score press ({round_turns} round turns + 1)"
    );

    let (status, body) = get(&app, base).await;
    assert_eq!(status, StatusCode::OK);
    assert!(body.contains("ROUND COMPLETE"), "{body}");
    assert!(
        body.contains("WINNER:") || body.contains("DRAW"),
        "the public result is explicit: {body}"
    );
    assert!(
        body.contains("Influence A:"),
        "final influence renders: {body}"
    );

    // THE OUTCOME: the whole chain replays, and it is exactly the genesis plus ONE turn per press —
    // the Offering invariant this test exists for, stated over the round that was actually played
    // rather than over a transcribed count.
    assert_eq!(
        committed_turns(&app, base).await,
        1 + presses,
        "genesis + ONE executor turn per press, and nothing else on the chain"
    );
}
