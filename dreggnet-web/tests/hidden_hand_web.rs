//! # The viewer-blind host boundary, FIXED — driven end-to-end.
//!
//! The bug: `Offering::render_for(session, viewer)` existed, but the type-erased [`OfferingSlot`]
//! trait (and therefore [`OfferingHost`]) only exposed the viewer-BLIND `render`/`actions`. So every
//! production render dropped the viewer at the erasure boundary and the multiway-tug hidden hand
//! painted `surface_for(None)` — BOTH hands fog — for everyone, including the seated player on the
//! web. `render_for`/`actions_for` on the erasure boundary (+ the web call sites switched to them)
//! resurrect the per-viewer projection on the live surface.
//!
//! These tests DRIVE the fix, non-vacuously:
//! 1. `OfferingHost::render_for` shows a seated tug player THEIR OWN cards while a different viewer
//!    (and the old viewer-blind `render`) still sees fog — the exact bug, now fixed, proven to bite.
//! 2. The web session page (through `catalog_router` + a `dregg_user` cookie) shows the seated user
//!    their own hand — the live web surface.
//! 3. `OfferingHost::actions_for` threads the viewer through the erasure boundary so a document's
//!    per-actor cap dimming reaches the live path (a capped actor enabled, an uncapped one dimmed).

use std::sync::Arc;

use axum::body::Body;
use axum::http::{Request, StatusCode};
use tower::ServiceExt; // oneshot

mod common;

use dreggnet_offerings::{Action, DreggIdentity, Offering, OfferingHost, SessionConfig, SessionId};
use dreggnet_web::seated::SeatedTug;
use dreggnet_web::{CatalogState, catalog_router, web_identity};

use dreggnet_doc::{DocOffering, Role};

/// The debug text of a session's rendered surface (the same idiom the game crates' surface tests use).
fn text(surface: &dreggnet_offerings::Surface) -> String {
    format!("{:?}", surface.view())
}

// ───────────────────────────────────────────────────────────────────────────────
// 1. THE HOST BOUNDARY — a seated player sees their OWN hand; everyone else sees fog.
// ───────────────────────────────────────────────────────────────────────────────

/// **The exact bug, fixed at the erasure boundary.** A seated tug player renders their OWN cards
/// through `OfferingHost::render_for(id, that_seat)`; a DIFFERENT viewer, and the old viewer-blind
/// `OfferingHost::render`, still see fog. If the boundary were still viewer-blind (the bug), the
/// seated player's own-hand assertion below would FAIL — so this test bites.
#[test]
fn a_seated_tug_player_sees_their_own_hand_through_the_host_others_get_fog() {
    let mut host = OfferingHost::new();
    host.register("tug", "Multiway-Tug", SeatedTug::new());

    let sid = SessionId::new("tug-hidden-1");
    host.ensure_open("tug", &sid).expect("tug session opens");

    // Alice CLAIMS seat A by playing the round's scheduled opening action (Competition).
    let alice = web_identity("alice");
    let out = host
        .advance(
            "tug",
            &sid,
            Action::new("comp", "comp", 3, true),
            alice.clone(),
        )
        .expect("the tug session is live");
    assert!(out.landed(), "alice's play lands and claims seat A");

    // AS ALICE: her own hand is revealed (card ids), and the opponent stays fog.
    let alice_view = text(&host.render_for("tug", &sid, &alice).expect("live"));
    assert!(
        alice_view.contains("Your hand") && alice_view.contains("card #"),
        "the seated player sees their OWN card ids: {alice_view}"
    );
    assert!(
        alice_view.contains("Opponent (hidden hand)") && alice_view.contains("committed root"),
        "the opponent's hand is fog (a count + committed root), not their cards: {alice_view}"
    );
    // Seat B's cards (ids 6..11) are NEVER in seat A's view — the opponent is genuinely fogged.
    assert!(
        !alice_view.contains("card #8"),
        "seat A must not see seat B's card ids: {alice_view}"
    );

    // AS A DIFFERENT VIEWER (a stranger holding no seat): seat A's hand is FOG — the commitment,
    // not the cards. (This is what every viewer wrongly got before the fix.)
    let stranger = web_identity("stranger");
    let stranger_view = text(&host.render_for("tug", &sid, &stranger).expect("live"));
    assert!(
        !stranger_view.contains("Your hand") && !stranger_view.contains("card #"),
        "a non-seat viewer never sees anyone's card ids: {stranger_view}"
    );
    assert!(
        stranger_view.contains("committed root"),
        "a non-seat viewer still renders the fog (a count + committed root): {stranger_view}"
    );

    // THE OLD VIEWER-BLIND PATH — `OfferingHost::render` (still present) — fogs BOTH hands. This is
    // the dead-everywhere path the production surface used to take; render_for is the fix.
    let blind_view = text(&host.render("tug", &sid).expect("live"));
    assert!(
        !blind_view.contains("card #"),
        "the viewer-blind render fogs everyone (the bug the fix bypasses): {blind_view}"
    );
}

// ───────────────────────────────────────────────────────────────────────────────
// 2. THE LIVE WEB SURFACE — the seated user sees their hand on the session page.
// ───────────────────────────────────────────────────────────────────────────────

async fn get_as(app: &axum::Router, uri: &str, user: Option<&str>) -> (StatusCode, String) {
    let mut req = Request::builder().uri(uri);
    if let Some(u) = user {
        req = req.header("cookie", format!("dregg_user={u}"));
    }
    let resp = app
        .clone()
        .oneshot(req.body(Body::empty()).unwrap())
        .await
        .unwrap();
    let status = resp.status();
    let bytes = axum::body::to_bytes(resp.into_body(), usize::MAX)
        .await
        .unwrap();
    (status, String::from_utf8(bytes.to_vec()).unwrap())
}

fn hidden_value<'a>(html: &'a str, name: &str) -> Option<&'a str> {
    let marker = format!("name=\"{name}\" value=\"");
    Some(html.split_once(&marker)?.1.split_once('"')?.0)
}

/// Post one turn as `user`.
///
/// ⚠ THIS HELPER WAS DARK. `tug` is a SPINED game key (`game_spine::game_kind`), so `POST …/act`
/// requires the server-presented route authority (`{incarnation, generation, pre-head, token}`)
/// the play surface stamps into its own form. Posting a bare `turn=&arg=` was answered `409
/// invalid game reference`, so the seated-user own-hand assertion below never reached a landed
/// turn. It now reads the authority off that user's live page, as their browser would.
async fn post_as(
    app: &axum::Router,
    uri: &str,
    turn: &str,
    arg: i64,
    user: &str,
) -> (StatusCode, String) {
    let surface_uri = uri.strip_suffix("/act").unwrap_or(uri);
    let (_, surface) = get_as(app, surface_uri, Some(user)).await;
    let authority = [
        "game_host_incarnation",
        "game_session_generation",
        "game_expected_pre_head",
        "game_form_token",
    ]
    .iter()
    .map(|name| hidden_value(&surface, name).map(|value| format!("&{name}={value}")))
    .collect::<Option<String>>()
    .unwrap_or_default();
    let resp = app
        .clone()
        .oneshot(
            Request::builder()
                .method("POST")
                .uri(uri)
                .header("content-type", "application/x-www-form-urlencoded")
                .header("cookie", format!("dregg_user={user}"))
                .body(Body::from(format!("turn={turn}&arg={arg}{authority}")))
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

/// **The web session page now serves the seated user their own hand.** Alice POSTs a play (claiming
/// seat A); the POST re-render AND a subsequent GET carrying her `dregg_user` cookie both paint her
/// own card ids. A stranger's GET (and an anonymous GET) still see fog — the bug, fixed on the live
/// web surface.
#[tokio::test]
async fn the_web_session_page_shows_the_seated_user_their_own_hand() {
    let app = common::guard(catalog_router(Arc::new(CatalogState::new())));
    let base = "/offerings/tug/session/tug-web-hidden";

    // Alice claims seat A by playing — the POST re-renders AS alice, so her hand is on the page.
    let (_, body) = post_as(&app, &format!("{base}/act"), "comp", 3, "alice").await;
    assert!(
        body.contains("Turn committed"),
        "alice's play lands: {body}"
    );
    assert!(
        body.contains("Your hand") && body.contains("card #"),
        "the POST re-render shows alice HER OWN hand: {body}"
    );

    // A GET carrying alice's cookie renders AS alice — her own hand, not fog.
    let (status, alice_page) = get_as(&app, base, Some("alice")).await;
    assert_eq!(status, StatusCode::OK);
    assert!(
        alice_page.contains("Your hand") && alice_page.contains("card #"),
        "GET as the seated user shows their own hand: {alice_page}"
    );

    // A STRANGER's GET (holds no seat) — fog. And an anonymous GET — fog. The reveal is per-viewer.
    let (_, stranger_page) = get_as(&app, base, Some("stranger")).await;
    assert!(
        !stranger_page.contains("card #"),
        "a non-seat viewer sees fog on the web, never the cards: {stranger_page}"
    );
    let (_, anon_page) = get_as(&app, base, None).await;
    assert!(
        !anon_page.contains("card #"),
        "an anonymous viewer sees fog on the web: {anon_page}"
    );
}

// ───────────────────────────────────────────────────────────────────────────────
// 3. actions_for — the per-actor cap dimming reaches the live host path.
// ───────────────────────────────────────────────────────────────────────────────

/// **The viewer threads through the erasure boundary for AFFORDANCES too.** A document's per-actor
/// cap dimming (`DocOffering`) reaches the live path: a capped editor sees its edit affordances
/// enabled where an uncapped actor sees the SAME affordances dimmed — and `OfferingHost::actions_for`
/// carries that per-viewer view across the erased slot, where the viewer-blind `actions` cannot.
#[test]
fn actions_for_threads_the_viewer_so_doc_cap_dimming_reaches_the_host() {
    let off = DocOffering::new();
    let mut s = off.open(SessionConfig::with_seed(7)).expect("doc opens");

    let editor = DreggIdentity("editor".to_string());
    let commenter = DreggIdentity("commenter".to_string());
    s.invite(editor.clone(), Role::Editor);
    s.invite(commenter.clone(), Role::Commenter);

    // The TRAIT `actions_for` override (routes to the per-actor cap-gated view). UFCS names the
    // trait method (the inherent `DocOffering::actions_for` takes an `Option` and wins bare dispatch).
    let for_editor = <DocOffering as Offering>::actions_for(&off, &s, &editor);
    let for_commenter = <DocOffering as Offering>::actions_for(&off, &s, &commenter);
    assert!(
        !for_editor.is_empty() && for_editor.iter().all(|a| a.enabled),
        "the capped editor sees its edit affordances ENABLED"
    );
    assert_eq!(
        for_editor.len(),
        for_commenter.len(),
        "the same affordance set is shown to both (the cap tooth is a decoration, not a hide)"
    );
    assert!(
        for_commenter.iter().all(|a| !a.enabled),
        "the uncapped commenter sees the SAME affordances DIMMED"
    );

    // Now through the ERASURE BOUNDARY: the host threads the viewer to `actions_for`, where the
    // viewer-blind `actions` (anonymous) cannot dim. A host-opened doc has an empty roster, so any
    // concrete actor is uncapped (dimmed) while the anonymous `actions` view is enabled — proving the
    // viewer genuinely reaches the offering's cap logic across the erased slot.
    let mut host = OfferingHost::new();
    host.register("doc", "DreggNet Doc", DocOffering::new());
    let sid = SessionId::new("doc-1");
    host.ensure_open("doc", &sid).expect("doc session opens");

    let blind = host.actions("doc", &sid).expect("live");
    let stranger = DreggIdentity("nobody".to_string());
    let for_stranger = host.actions_for("doc", &sid, &stranger).expect("live");

    assert!(
        !blind.is_empty() && blind.iter().all(|a| a.enabled),
        "the viewer-blind host view is the anonymous, fully-enabled set"
    );
    assert!(
        for_stranger.iter().all(|a| !a.enabled),
        "threaded through the host, an uncapped actor's affordances are DIMMED"
    );
    assert_ne!(
        blind.iter().map(|a| a.enabled).collect::<Vec<_>>(),
        for_stranger.iter().map(|a| a.enabled).collect::<Vec<_>>(),
        "the viewer changed the result — actions_for is not the viewer-blind actions"
    );
}
