//! **The driven MULTI-OFFERING web catalog — three heterogeneous offerings, in the browser.**
//!
//! The single-offering `driven.rs` proved ONE offering plays over the web. This proves the
//! frontend-agnostic [`OfferingHost`] lifted to the core: the web catalog registers THREE distinct
//! offerings (a dungeon, a council, a market — heterogeneous `Session` types, one registry) and
//! plays each in the browser through the SAME `open/advance/render/verify` verbs, with NO real
//! network (axum `ServiceExt::oneshot`) and NO Discord:
//! - `GET /offerings` lists all three;
//! - a full winning DUNGEON line plays through `/offerings/dungeon/...` (POSTs land real turns);
//! - a COUNCIL propose → vote (2 members) → enact plays through `/offerings/council/...`;
//! - a MARKET list → sealed bids → settle clears through `/offerings/market/...`;
//! - `verify` holds for each committed chain.

use std::sync::Arc;

use axum::body::Body;
use axum::http::{Request, StatusCode};
use dreggnet_web::{CatalogState, catalog_router};
use tower::ServiceExt; // oneshot

use dungeon_on_dregg::{KP_CLAIM_RED, KP_DESCEND, KP_PRESS_ON, KP_SEIZE};

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

/// POST a `{turn, arg}` affordance form to `uri` as web user `user` (a `dregg_user` cookie),
/// carrying the route authority the surface stamped into its own form. `dungeon`, `council` and
/// `market` are all SPINED game keys, so a bare `turn=&arg=` here is `409 invalid game reference`
/// and none of this file's play lines would ever reach the executor.
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

/// `GET /offerings` lists the three registered offerings, each with a play link.
#[tokio::test]
async fn the_catalog_lists_the_registered_offerings() {
    let app = app();
    let (status, body) = get(&app, "/offerings").await;
    assert_eq!(status, StatusCode::OK);
    for key in ["dungeon", "council", "market"] {
        assert!(
            body.contains(&format!("/offerings/{key}/session/")),
            "the catalog lists a play link for {key}: {body}"
        );
    }
    assert!(body.contains("Warden"), "the dungeon card is present");
    assert!(body.contains("Council"), "the council card is present");
    assert!(body.contains("Market"), "the market card is present");
}

/// A full winning DUNGEON line plays through the catalog — each POST lands a real turn, the Keep
/// clears, and the committed chain re-verifies by replay.
#[tokio::test]
async fn a_dungeon_line_plays_through_the_catalog() {
    let app = app();
    let base = "/offerings/dungeon/session/d1";
    let act = format!("{base}/act");

    // Open + render the gatehall (two affordance forms POSTing to the act route).
    let (status, body) = get(&app, base).await;
    assert_eq!(status, StatusCode::OK);
    assert!(body.contains("Warden"), "the Keep names itself: {body}");
    assert!(
        body.contains(&format!("action=\"{act}\"")),
        "each affordance POSTs to the offering act route: {body}"
    );

    // Play the winning line: press on → claim crown → descend → seize.
    for arg in [KP_PRESS_ON, KP_CLAIM_RED, KP_DESCEND] {
        let (s, body) = post(&app, &act, "choose", arg as i64, "alice").await;
        assert_eq!(s, StatusCode::OK);
        assert!(
            body.contains("Turn committed"),
            "move {arg} committed: {body}"
        );
    }
    let (_s, body) = post(&app, &act, "choose", KP_SEIZE as i64, "alice").await;
    assert!(
        body.contains("objective") || body.contains("cleared") || body.contains("committed"),
        "the Keep clears: {body}"
    );

    // The whole committed chain re-verifies by replay, over HTTP.
    let (status, verify) = get(&app, &format!("{base}/verify")).await;
    assert_eq!(status, StatusCode::OK);
    assert!(
        verify.contains("\"verified\":true"),
        "dungeon re-verifies: {verify}"
    );
    assert!(
        verify.contains("\"turns\":5"),
        "genesis + four turns: {verify}"
    );
}

/// A COUNCIL propose → vote (two members) → enact plays through the catalog — a real quorum vote,
/// the enactment a real committed cell-state effect, and the decision chain re-verifies.
#[tokio::test]
async fn a_council_propose_vote_enact_plays_through_the_catalog() {
    let app = app();
    let base = "/offerings/council/session/c1";
    let act = format!("{base}/act");

    // Open the council + render.
    let (status, body) = get(&app, base).await;
    assert_eq!(status, StatusCode::OK);
    assert!(body.contains("Council"), "the council renders: {body}");

    // alice proposes catalog item 0 ("Fund the archive").
    let (_s, body) = post(&app, &act, "propose", 0, "alice").await;
    assert!(
        body.contains("Turn committed"),
        "the proposal opened: {body}"
    );

    // Both members approve proposal 0 (quorum M = 2).
    let (_s, b1) = post(&app, &act, "approve", 0, "alice").await;
    assert!(
        b1.contains("Turn committed"),
        "alice's approve landed: {b1}"
    );
    let (_s, b2) = post(&app, &act, "approve", 0, "bob").await;
    assert!(b2.contains("Turn committed"), "bob's approve landed: {b2}");

    // A non-member cannot vote — a real executor refusal (nothing commits).
    let (_s, bm) = post(&app, &act, "approve", 0, "mallory").await;
    assert!(
        bm.contains("Refused") && bm.contains("not a council member"),
        "a non-member is refused: {bm}"
    );

    // Enact — quorum reached, the policy effect commits as a real turn.
    let (_s, be) = post(&app, &act, "enact", 0, "alice").await;
    assert!(be.contains("Turn committed"), "the proposal enacted: {be}");
    assert!(
        be.contains("ENACTED"),
        "the surface shows the enacted proposal: {be}"
    );

    // The decision chain re-verifies.
    let (status, verify) = get(&app, &format!("{base}/verify")).await;
    assert_eq!(status, StatusCode::OK);
    assert!(
        verify.contains("\"verified\":true"),
        "council re-verifies: {verify}"
    );
}

/// A MARKET list → sealed bids → settle clears through the catalog — the value moves through the
/// verified per-asset ring settlement, and the cleared chain re-verifies.
#[tokio::test]
async fn a_market_list_bid_settle_plays_through_the_catalog() {
    let app = app();
    let base = "/offerings/market/session/m1";
    let act = format!("{base}/act");

    // Open + render (only a LIST affordance before listing).
    let (status, body) = get(&app, base).await;
    assert_eq!(status, StatusCode::OK);
    assert!(body.contains("Market"), "the market renders: {body}");

    // alice lists an item with reserve 100.
    let (_s, bl) = post(&app, &act, "list", 100, "alice").await;
    assert!(
        bl.contains("Turn committed"),
        "the listing came alive: {bl}"
    );

    // Two distinct bidders place sealed bids (500 and 300 — distinct web users → distinct handles).
    let (_s, bb) = post(&app, &act, "bid", 500, "bob").await;
    assert!(
        bb.contains("Turn committed"),
        "bob's sealed bid landed: {bb}"
    );
    let (_s, bc) = post(&app, &act, "bid", 300, "carol").await;
    assert!(
        bc.contains("Turn committed"),
        "carol's sealed bid landed: {bc}"
    );

    // Settle — reveal + clear to the high bid (bob, 500 ≥ reserve 100), value conserved.
    let (_s, bs) = post(&app, &act, "settle", 0, "alice").await;
    assert!(
        bs.contains("committed") || bs.contains("objective"),
        "the auction cleared: {bs}"
    );
    assert!(
        bs.contains("Cleared") || bs.contains("winner"),
        "the winner is shown: {bs}"
    );

    // The cleared chain re-verifies (winner is the real high bid, conservation holds).
    let (status, verify) = get(&app, &format!("{base}/verify")).await;
    assert_eq!(status, StatusCode::OK);
    assert!(
        verify.contains("\"verified\":true"),
        "market re-verifies: {verify}"
    );
}

/// A POST for an affordance the current surface does NOT offer is an honest frontend-level refusal,
/// before the substrate — the executor is not even reached.
#[tokio::test]
async fn an_unoffered_turn_is_refused_before_the_substrate() {
    let app = app();
    let act = "/offerings/dungeon/session/x1/act";
    let _ = get(&app, "/offerings/dungeon/session/x1").await;
    let (status, body) = post(&app, act, "not-a-real-turn", 0, "alice").await;
    assert_eq!(status, StatusCode::OK);
    assert!(
        body.contains("not on the current surface"),
        "an unoffered turn is refused before the substrate: {body}"
    );
}
