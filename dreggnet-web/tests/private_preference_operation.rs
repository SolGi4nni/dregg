//! A real private party vote crosses the shared web/Telegram/Discord operation
//! transport and changes the ordinary live dungeon surface.

#![cfg(feature = "private-preference-operation")]

use std::sync::Arc;

use axum::{Router, body::Body, http::Request};
use dreggnet_offerings::dungeon::{
    DungeonOffering, PRIVATE_PREFERENCE_DISCLOSURE, PRIVATE_PREFERENCE_MEDIA_TYPE,
    PRIVATE_PREFERENCE_OPERATION, private_preference_session_for_seed,
};
use dreggnet_offerings::{OfferingHost, SessionConfig, SessionId};
use dreggnet_web::discord_activity::{DiscordActivityState, discord_activity_router};
use dreggnet_web::telegram_miniapp::{TgMiniAppState, tg_miniapp_router};
use dreggnet_web::{CatalogState, catalog_router, fhegg_operation, web_identity};
use dungeon_on_dregg::private_preference::{PrivateBallot, prove_private_preference};
use dungeon_on_dregg::{KP_PRESS_ON, KP_PRIVATE_COUNSEL_DESCEND};
use tower::ServiceExt;

mod common;

const OFFERING: &str = "dungeon";
const SESSION: &str = "private-party-counsel";
const SEED: u64 = 0xC011EC7;

fn ballots() -> [PrivateBallot; 4] {
    [
        PrivateBallot::try_new([3, 2, 0, 1]).unwrap(),
        PrivateBallot::try_new([2, 3, 0, 1]).unwrap(),
        PrivateBallot::try_new([0, 3, 2, 1]).unwrap(),
        PrivateBallot::try_new([1, 2, 3, 0]).unwrap(),
    ]
}

fn catalog() -> Arc<CatalogState> {
    Arc::new(CatalogState::with_host(|| {
        let mut host = OfferingHost::new();
        host.register(OFFERING, "The Warden's Keep", DungeonOffering::new());
        host.open_session(
            OFFERING,
            SessionId::new(SESSION),
            SessionConfig::with_seed(SEED),
        )
        .unwrap();
        host
    }))
}

async fn response(app: &Router, request: Request<Body>) -> (u16, Vec<u8>) {
    let response = app.clone().oneshot(request).await.unwrap();
    let status = response.status().as_u16();
    let body = axum::body::to_bytes(response.into_body(), usize::MAX)
        .await
        .unwrap()
        .to_vec();
    (status, body)
}

fn upload(path: &str, body: impl Into<Body>) -> Request<Body> {
    Request::builder()
        .method("POST")
        .uri(path)
        .header("content-type", PRIVATE_PREFERENCE_MEDIA_TYPE)
        .header("cookie", "dregg_user=guild-counsel")
        .body(body.into())
        .unwrap()
}

/// One dungeon move, carrying the route authority the play surface stamped into its own form.
/// `dungeon` is a SPINED game key: a bare `turn=&arg=` is `409 invalid game reference`, the world
/// never advances, and the private-operation legs below run against a session still at genesis.
async fn act(app: &Router, path: &str, arg: usize, user: &str) -> Request<Body> {
    let cookie = format!("dregg_user={user}");
    let body = common::act_body(app, path, "choose", arg as i64, Some(&cookie)).await;
    Request::builder()
        .method("POST")
        .uri(path)
        .header("content-type", "application/x-www-form-urlencoded")
        .header("cookie", &cookie)
        .body(Body::from(body))
        .unwrap()
}

#[tokio::test]
async fn shielded_party_choice_is_discoverable_authenticated_and_live() {
    let catalog = catalog();
    let tg = tg_miniapp_router(Arc::new(TgMiniAppState::new(
        Arc::clone(&catalog),
        "test-bot-token",
        [0x61; 32],
        86_400,
    )));
    let da = discord_activity_router(Arc::new(DiscordActivityState::new(
        Arc::clone(&catalog),
        "client",
        "secret",
        [0x62; 32],
        86_400,
    )));
    let app = common::guard(
        Router::new()
            .merge(catalog_router(Arc::clone(&catalog)))
            .merge(fhegg_operation::router(Arc::clone(&catalog)))
            .merge(tg)
            .merge(da),
    );

    let game_path = format!("/offerings/{OFFERING}/session/{SESSION}");
    let act_path = format!("{game_path}/act");
    let (status, entered) = response(
        &app,
        act(&app, &act_path, KP_PRESS_ON, "guild-counsel").await,
    )
    .await;
    assert_eq!(status, 200, "{}", String::from_utf8_lossy(&entered));

    let operations = format!("/offerings/{OFFERING}/session/{SESSION}/operations");
    let (status, descriptors) = response(
        &app,
        Request::builder()
            .uri(&operations)
            .body(Body::empty())
            .unwrap(),
    )
    .await;
    assert_eq!(status, 200);
    let descriptors = String::from_utf8(descriptors).unwrap();
    assert!(descriptors.contains(PRIVATE_PREFERENCE_OPERATION));
    assert!(descriptors.contains(PRIVATE_PREFERENCE_MEDIA_TYPE));
    assert!(descriptors.contains(PRIVATE_PREFERENCE_DISCLOSURE));

    let proof_session = private_preference_session_for_seed(SEED);
    let honest = prove_private_preference(proof_session, &ballots())
        .unwrap()
        .to_postcard()
        .unwrap();
    let route = format!("{operations}/{PRIVATE_PREFERENCE_OPERATION}");

    for prefix in ["/tg", "/da"] {
        let platform_route = format!(
            "{prefix}/offerings/{OFFERING}/session/{SESSION}/operations/{PRIVATE_PREFERENCE_OPERATION}"
        );
        let anonymous = Request::builder()
            .method("POST")
            .uri(platform_route)
            .header("content-type", PRIVATE_PREFERENCE_MEDIA_TYPE)
            .body(Body::from(honest.clone()))
            .unwrap();
        assert_eq!(response(&app, anonymous).await.0, 401);
    }

    let mut corrupt = honest.clone();
    let at = corrupt.len() - 1;
    corrupt[at] ^= 1;
    assert_ne!(response(&app, upload(&route, corrupt)).await.0, 200);

    let (status, applied) = response(&app, upload(&route, honest.clone())).await;
    assert_eq!(status, 200, "{}", String::from_utf8_lossy(&applied));
    let applied = String::from_utf8(applied).unwrap();
    assert!(applied.contains("descend the drowned stair"));
    assert!(applied.contains("winner"));
    assert_eq!(response(&app, upload(&route, honest)).await.0, 409);

    let (status, enacted) = response(
        &app,
        act(&app, &act_path, KP_PRIVATE_COUNSEL_DESCEND, "guild-counsel").await,
    )
    .await;
    assert_eq!(status, 200, "{}", String::from_utf8_lossy(&enacted));
    assert!(
        String::from_utf8(enacted)
            .unwrap()
            .contains("Turn committed")
    );

    let (status, game) = response(
        &app,
        Request::builder()
            .uri(&game_path)
            .header("cookie", "dregg_user=guild-counsel")
            .body(Body::empty())
            .unwrap(),
    )
    .await;
    assert_eq!(status, 200);
    let game = String::from_utf8(game).unwrap();
    assert!(game.contains("Shielded party counsel"));
    assert!(game.contains("the party privately chose #1"));
    assert!(game.contains("descend the drowned stair"));
    assert!(game.contains("depth 2"));
    assert!(game.contains(&web_identity("guild-counsel").0));

    let (status, verified) = response(
        &app,
        Request::builder()
            .uri(format!("{game_path}/verify"))
            .body(Body::empty())
            .unwrap(),
    )
    .await;
    assert_eq!(status, 200);
    assert!(
        String::from_utf8(verified)
            .unwrap()
            .contains("\"verified\":true")
    );
}
