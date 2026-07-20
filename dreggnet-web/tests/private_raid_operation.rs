//! A real hiding raid-role assignment enters the live dungeon through the one
//! hosted-operation adapter and becomes visible on the ordinary game surface.

#![cfg(feature = "private-raid-operation")]

use std::sync::Arc;

use axum::{Router, body::Body, http::Request};
use dreggnet_offerings::dungeon::{
    DungeonOffering, PRIVATE_RAID_DISCLOSURE, PRIVATE_RAID_MEDIA_TYPE, PRIVATE_RAID_OPERATION,
};
use dreggnet_offerings::{OfferingHost, SessionConfig, SessionId};
use dreggnet_web::discord_activity::{DiscordActivityState, discord_activity_router};
use dreggnet_web::telegram_miniapp::{TgMiniAppState, tg_miniapp_router};
use dreggnet_web::{CatalogState, catalog_router, fhegg_operation, web_identity};
use dungeon_on_dregg::private_raid::{RaidRole, prove_private_assignment};
use dungeon_on_dregg::{KP_DESCEND, KP_PRESS_ON, KP_PRIVATE_RAID_MENDER_CHOICES, KP_TRADE_BLOWS};
use tower::ServiceExt;

const OFFERING: &str = "dungeon";
const SESSION: &str = "private-raid-one";
const SEED: u64 = 31_337;

fn scores() -> [[u8; 4]; 4] {
    [[0, 3, 0, 0], [3, 0, 0, 0], [0, 0, 3, 0], [0, 0, 0, 3]]
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
        .expect("private raid dungeon opens");
        host
    }))
}

async fn response(app: &Router, request: Request<Body>) -> (u16, Vec<u8>) {
    let response = app.clone().oneshot(request).await.expect("router response");
    let status = response.status().as_u16();
    let body = axum::body::to_bytes(response.into_body(), usize::MAX)
        .await
        .expect("response body")
        .to_vec();
    (status, body)
}

fn upload(path: &str, body: impl Into<Body>) -> Request<Body> {
    Request::builder()
        .method("POST")
        .uri(path)
        .header("content-type", PRIVATE_RAID_MEDIA_TYPE)
        .header("cookie", "dregg_user=raid-captain")
        .body(body.into())
        .unwrap()
}

fn act(path: &str, arg: usize, user: &str) -> Request<Body> {
    Request::builder()
        .method("POST")
        .uri(path)
        .header("content-type", "application/x-www-form-urlencoded")
        .header("cookie", format!("dregg_user={user}"))
        .body(Body::from(format!("turn=choose&arg={arg}")))
        .unwrap()
}

#[tokio::test]
async fn private_assignment_crosses_the_shared_transport_and_changes_the_live_game() {
    let catalog = catalog();
    let tg = tg_miniapp_router(Arc::new(TgMiniAppState::new(
        Arc::clone(&catalog),
        "test-bot-token",
        [0x71; 32],
        86_400,
    )));
    let da = discord_activity_router(Arc::new(DiscordActivityState::new(
        Arc::clone(&catalog),
        "client",
        "secret",
        [0x72; 32],
        86_400,
    )));
    let app = Router::new()
        .merge(catalog_router(Arc::clone(&catalog)))
        .merge(fhegg_operation::router(Arc::clone(&catalog)))
        .merge(tg)
        .merge(da);

    let game_path = format!("/offerings/{OFFERING}/session/{SESSION}");
    let act_path = format!("{game_path}/act");
    let operations_path = format!("{game_path}/operations");
    let (status, discovered) = response(
        &app,
        Request::builder()
            .uri(&operations_path)
            .body(Body::empty())
            .unwrap(),
    )
    .await;
    assert_eq!(status, 200);
    let discovered = String::from_utf8(discovered).unwrap();
    assert!(discovered.contains(PRIVATE_RAID_OPERATION));
    assert!(discovered.contains(PRIVATE_RAID_MEDIA_TYPE));
    assert!(discovered.contains(PRIVATE_RAID_DISCLOSURE));

    let route = format!("{operations_path}/{PRIVATE_RAID_OPERATION}");
    let proof_session = ((SEED % 2_013_265_920) + 1) as u32;
    let receipt = prove_private_assignment(proof_session, scores(), [[true; 4]; 4])
        .expect("real private assignment proves");
    let mender_seat = receipt
        .statement()
        .roles
        .iter()
        .position(|role| *role == RaidRole::Mender as u8)
        .expect("the proved permutation has exactly one Mender");
    let mender_choice = KP_PRIVATE_RAID_MENDER_CHOICES[mender_seat];
    let honest = receipt.to_postcard().expect("canonical transport");

    let wrong_media = Request::builder()
        .method("POST")
        .uri(&route)
        .header("content-type", "application/octet-stream")
        .header("cookie", "dregg_user=raid-captain")
        .body(Body::from(honest.clone()))
        .unwrap();
    assert_eq!(response(&app, wrong_media).await.0, 415);

    let wrong_session = prove_private_assignment(proof_session + 1, scores(), [[true; 4]; 4])
        .unwrap()
        .to_postcard()
        .unwrap();
    assert_eq!(response(&app, upload(&route, wrong_session)).await.0, 409);

    let mut corrupt = honest.clone();
    let last = corrupt.len() - 1;
    corrupt[last] ^= 1;
    assert_ne!(response(&app, upload(&route, corrupt)).await.0, 200);

    // Both native-platform routes exist and enforce their stronger actor gate
    // before consuming the identical proof body.
    for prefix in ["/tg", "/da"] {
        let platform_route = format!(
            "{prefix}/offerings/{OFFERING}/session/{SESSION}/operations/{PRIVATE_RAID_OPERATION}"
        );
        let anonymous = Request::builder()
            .method("POST")
            .uri(platform_route)
            .header("content-type", PRIVATE_RAID_MEDIA_TYPE)
            .body(Body::from(honest.clone()))
            .unwrap();
        assert_eq!(response(&app, anonymous).await.0, 401);
    }

    // Reach the sanctum with exactly 30 HP through ordinary HTTP turns.  The
    // later proof acceptance is bound to this live timeline cursor.
    for choice in [KP_TRADE_BLOWS, KP_PRESS_ON, KP_DESCEND] {
        let (status, moved) = response(&app, act(&act_path, choice, "raid-captain")).await;
        assert_eq!(status, 200, "{}", String::from_utf8_lossy(&moved));
        assert!(String::from_utf8(moved).unwrap().contains("Turn committed"));
    }

    let (status, applied) = response(&app, upload(&route, honest.clone())).await;
    assert_eq!(status, 200, "{}", String::from_utf8_lossy(&applied));
    let applied = String::from_utf8(applied).unwrap();
    assert!(applied.contains("applied"));
    assert!(applied.contains("Striker"));
    assert!(applied.contains("Bulwark"));
    assert!(applied.contains("Mender"));
    assert!(applied.contains("Pathfinder"));

    assert_eq!(response(&app, upload(&route, honest)).await.0, 409);

    // A different authenticated web actor cannot spend the proof submitter's
    // capability.  The refusal does not consume the Mender recovery.
    let (status, refused) = response(&app, act(&act_path, mender_choice, "raid-thief")).await;
    assert_eq!(status, 200);
    assert!(String::from_utf8(refused).unwrap().contains("Refused"));

    // The exact role-indexed choice then crosses the ordinary action route and
    // spends the verified assignment once: HP 30 -> 50 in a committed turn.
    let (status, healed) = response(&app, act(&act_path, mender_choice, "raid-captain")).await;
    assert_eq!(status, 200, "{}", String::from_utf8_lossy(&healed));
    assert!(
        String::from_utf8(healed)
            .unwrap()
            .contains("Turn committed")
    );

    let (status, reused) = response(&app, act(&act_path, mender_choice, "raid-captain")).await;
    assert_eq!(status, 200);
    assert!(String::from_utf8(reused).unwrap().contains("Refused"));

    // The operation is not a sidecar: the normal playable dungeon surface now
    // renders the proof-produced party roles and the attributed submitter.
    let (status, game) = response(
        &app,
        Request::builder()
            .uri(format!("/offerings/{OFFERING}/session/{SESSION}"))
            .header("cookie", "dregg_user=raid-captain")
            .body(Body::empty())
            .unwrap(),
    )
    .await;
    assert_eq!(status, 200);
    let game = String::from_utf8(game).unwrap();
    assert!(game.contains("Private raid muster"));
    assert!(game.contains("verified roles"));
    assert!(game.contains("submitted by"));
    assert!(game.contains(&web_identity("raid-captain").0));
    assert!(game.contains("HP 50"));

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
