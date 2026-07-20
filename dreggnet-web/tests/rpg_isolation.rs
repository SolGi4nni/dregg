//! **THE PER-VIEWER INVENTORY ISOLATION FALSIFIER, DRIVEN THROUGH THE WEB CATALOG.**
//!
//! The bot↔game review's last live CRITICAL: every web (and Telegram) player shared ONE
//! inventory, because the eight RPG feature surfaces (trade / inventory / craft / …) were mounted
//! on the ONE shared `SharedWorld::demo("Adventurer")` catalog host — so player A could forge an
//! item and it appeared in player B's inventory. This proves the fix over the real HTTP surface
//! (no network — axum `ServiceExt::oneshot`):
//!
//! - **(a) ISOLATION** — two different web identities (`alice` / `bob`) on the SAME catalog have
//!   DISJOINT RPG worlds: alice forges a Greatblade on `craft`, it lands in HER `inventory`, and
//!   bob's `inventory` does not hold it.
//! - **(b) THE REGRESSION GUARD** — a SHARED multi-party table (`council`) is still shared, NOT
//!   accidentally split per-identity: alice proposes and bob approves the SAME proposal, reaching
//!   the 2-of-2 quorum and enacting — impossible unless both act on ONE council.
//! - **(c) PARTY IS A SHARED TABLE** — alice and bob claim different roles in the SAME party lobby.
//!   A party routed through the private RPG worlds would strand each claimant in a one-person copy.

use std::sync::Arc;

use axum::body::Body;
use axum::http::{Request, StatusCode};
use dreggnet_web::{CatalogState, catalog_router};
use tower::ServiceExt; // oneshot

/// GET `uri` as web user `user` (the `?user=` identity param — a `dregg_user` cookie works the same).
async fn get_as(app: &axum::Router, uri: &str, user: &str) -> (StatusCode, String) {
    let sep = if uri.contains('?') { '&' } else { '?' };
    let resp = app
        .clone()
        .oneshot(
            Request::builder()
                .uri(format!("{uri}{sep}user={user}"))
                .body(Body::empty())
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

/// POST a `{turn, arg}` affordance form as web user `user` (a `dregg_user` cookie).
async fn post(
    app: &axum::Router,
    uri: &str,
    turn: &str,
    arg: i64,
    user: &str,
) -> (StatusCode, String) {
    let resp = app
        .clone()
        .oneshot(
            Request::builder()
                .method("POST")
                .uri(uri)
                .header("content-type", "application/x-www-form-urlencoded")
                .header("cookie", format!("dregg_user={user}"))
                .body(Body::from(format!("turn={turn}&arg={arg}")))
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

fn app() -> axum::Router {
    catalog_router(Arc::new(CatalogState::new()))
}

/// **(a) Two viewers' RPG worlds are ISOLATED.** Alice forges a Greatblade on `craft`; it is on
/// HER `inventory`, and bob's `inventory` — a real, seeded, live world of his own — does not hold it.
#[tokio::test]
async fn two_viewers_have_isolated_rpg_inventories() {
    let app = app();

    // Alice forges the safe Greatblade (bench recipe 0) — one real landed turn in HER world.
    let (status, body) = post(
        &app,
        "/offerings/craft/session/primary/act",
        "craft",
        0,
        "alice",
    )
    .await;
    assert_eq!(status, StatusCode::OK);
    assert!(
        body.contains("Turn committed"),
        "alice's forge lands a real receipt: {body}"
    );

    // …and it is on ALICE's own inventory shelf (craft → inventory compose over her ONE world).
    let (status, alice_inv) = get_as(&app, "/offerings/inventory/session/primary", "alice").await;
    assert_eq!(status, StatusCode::OK);
    assert!(
        alice_inv.contains("Greatblade"),
        "alice's forged Greatblade is on her own inventory: {alice_inv}"
    );

    // BOB — a different identity on the SAME catalog — has a live, seeded inventory of his own that
    // holds NO note alice forged. (Before the fix, this listed alice's Greatblade: one shared world.)
    let (status, bob_inv) = get_as(&app, "/offerings/inventory/session/primary", "bob").await;
    assert_eq!(status, StatusCode::OK);
    assert!(
        !bob_inv.contains("Greatblade"),
        "bob's inventory holds no note alice forged — the worlds are disjoint: {bob_inv}"
    );
}

/// **(b) THE REGRESSION GUARD — a shared table stays shared.** `council` is a multi-party offering
/// (several identities acting on ONE object), so it must NOT be split per-identity by over-applying
/// the RPG fix. Alice proposes proposal 0 and BOB approves the SAME proposal; the 2-of-2 quorum is
/// reached and it enacts — which is only possible if both act on ONE shared council.
#[tokio::test]
async fn a_shared_council_is_not_split_per_identity() {
    let app = app();
    let act = "/offerings/council/session/shared1/act";

    // alice proposes catalog item 0 ("Fund the archive").
    let (_s, bp) = post(&app, act, "propose", 0, "alice").await;
    assert!(
        bp.contains("Turn committed"),
        "alice's proposal lands: {bp}"
    );

    // BOTH members approve proposal 0 (quorum M = 2). Bob approving the proposal ALICE made only
    // works because it is the SAME council — a per-identity split would give bob a fresh council.
    let (_s, ba) = post(&app, act, "approve", 0, "alice").await;
    assert!(ba.contains("Turn committed"), "alice's approve lands: {ba}");
    let (_s, bb) = post(&app, act, "approve", 0, "bob").await;
    assert!(bb.contains("Turn committed"), "bob's approve lands: {bb}");

    // With quorum reached, alice enacts proposal 0 — the shared-table payoff.
    let (_s, be) = post(&app, act, "enact", 0, "alice").await;
    assert!(
        be.contains("Turn committed"),
        "the 2-of-2 quorum enacts on the ONE shared council: {be}"
    );
}

/// **(c) THE PARTY ROUTING FALSIFIER.** Two web identities claim two roles in the same session and
/// the second response sees both holders. This pins `party` to the shared catalog host while the
/// inventory-bearing surfaces remain per-identity.
#[tokio::test]
async fn a_party_lobby_is_shared_between_identities() {
    let app = app();
    let act = "/offerings/party/session/shared-party/act";

    let (_status, alice) = post(&app, act, "claim-role", 0, "alice").await;
    assert!(
        alice.contains("Turn committed"),
        "alice claims the first shared role: {alice}"
    );

    let (_status, bob) = post(&app, act, "claim-role", 1, "bob").await;
    assert!(
        bob.contains("Turn committed"),
        "bob claims a second role in the same lobby: {bob}"
    );
    assert!(
        bob.contains("alice") && bob.contains("bob") && bob.contains("2 / 4 roles"),
        "the second response renders one shared two-player roster: {bob}"
    );
}
