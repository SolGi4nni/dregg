//! The opt-in private Bazaar is reached through the production catalog router,
//! not a manually constructed receipt or an adapter-only rendering fixture.

#![cfg(feature = "private-bazaar-live")]

use std::sync::Arc;

use axum::body::Body;
use axum::http::{Request, StatusCode};
use dreggnet_catalog::PrivateBazaarLiveDeployment;
use dreggnet_market::private_bazaar_journey::{
    PrivateBazaarDeploymentPin, PrivateBazaarRaidPolicy, TURN_ENTER_PRIVATE_BAZAAR,
};
use dreggnet_market::private_bazaar_live_host::PRIVATE_BAZAAR_RAID_KEY;
use dreggnet_market::private_clearing_guild_allocation::{GuildMember, GuildReward, GuildRoster};
use dreggnet_offerings::{DreggIdentity, SessionPolicy, seed_from_id};
use dreggnet_web::{CatalogState, catalog_router};
use dungeon_on_dregg::progression::{
    PRIVATE_BAZAAR_XP_METHOD, deploy_hero, private_bazaar_xp_event_topic,
};
use tower::ServiceExt;

async fn body(response: axum::response::Response) -> (StatusCode, String) {
    let status = response.status();
    let bytes = axum::body::to_bytes(response.into_body(), usize::MAX)
        .await
        .unwrap();
    (status, String::from_utf8(bytes.to_vec()).unwrap())
}

#[tokio::test]
async fn web_catalog_opens_and_drives_the_real_private_bazaar_host() {
    let hero = deploy_hero(0x61);
    hero.set_executor_signing_key([0x62; 32]);
    let roster = GuildRoster::new(vec![GuildMember::new(
        DreggIdentity("web-private-raider".to_owned()),
        hero.cell_id(),
    )])
    .unwrap();
    let reward = GuildReward::new("raid-xp/web/v1", 144).unwrap();
    let pin = PrivateBazaarDeploymentPin::new(
        [0x63; 32],
        roster.digest(),
        PrivateBazaarRaidPolicy::reward_commitment_for_configuration(&reward),
        PRIVATE_BAZAAR_XP_METHOD,
        private_bazaar_xp_event_topic(),
        hero.executor_pubkey().unwrap(),
        hero.federation_id(),
    )
    .unwrap();
    let policy = PrivateBazaarRaidPolicy::load(pin, roster, reward).unwrap();
    let temp = tempfile::tempdir().unwrap();
    let deployment = PrivateBazaarLiveDeployment::open(policy, 1, temp.path()).unwrap();
    let state = Arc::new(CatalogState::with_private_bazaar(deployment.clone()));
    let app = catalog_router(state);

    let session = "web-private-bazaar";
    let base = format!("/offerings/{PRIVATE_BAZAAR_RAID_KEY}/session/{session}");
    let (status, ready) = body(
        app.clone()
            .oneshot(Request::builder().uri(&base).body(Body::empty()).unwrap())
            .await
            .unwrap(),
    )
    .await;
    assert_eq!(status, StatusCode::OK);
    assert!(ready.contains("Dark Bazaar raid"), "{ready}");
    assert!(ready.contains(TURN_ENTER_PRIVATE_BAZAAR), "{ready}");

    let (status, pending) = body(
        app.clone()
            .oneshot(
                Request::builder()
                    .method("POST")
                    .uri(format!("{base}/act"))
                    .header("content-type", "application/x-www-form-urlencoded")
                    .header("cookie", "dregg_user=web-private-raider")
                    .body(Body::from(format!(
                        "turn={TURN_ENTER_PRIVATE_BAZAAR}&arg=0"
                    )))
                    .unwrap(),
            )
            .await
            .unwrap(),
    )
    .await;
    assert_eq!(status, StatusCode::OK);
    assert!(pending.contains("Turn committed"), "{pending}");
    assert!(pending.contains("pending"), "{pending}");
    for forbidden in ["winner", "proof bytes", "witness", "private bid"] {
        assert!(
            !pending.contains(forbidden),
            "web leaked {forbidden}: {pending}"
        );
    }

    assert!(deployment.registry().contains(seed_from_id(session)));
    let (status, verify) = body(
        app.oneshot(
            Request::builder()
                .uri(format!("{base}/verify"))
                .body(Body::empty())
                .unwrap(),
        )
        .await
        .unwrap(),
    )
    .await;
    assert_eq!(status, StatusCode::OK);
    assert!(verify.contains("\"verified\":true"), "{verify}");
}

#[tokio::test]
async fn durable_web_boot_replay_reconstructs_worker_registry() {
    let hero = deploy_hero(0x91);
    hero.set_executor_signing_key([0x92; 32]);
    let roster = GuildRoster::new(vec![GuildMember::new(
        DreggIdentity("web-restarted-raider".to_owned()),
        hero.cell_id(),
    )])
    .unwrap();
    let reward = GuildReward::new("raid-xp/web-restart/v1", 144).unwrap();
    let pin = PrivateBazaarDeploymentPin::new(
        [0x93; 32],
        roster.digest(),
        PrivateBazaarRaidPolicy::reward_commitment_for_configuration(&reward),
        PRIVATE_BAZAAR_XP_METHOD,
        private_bazaar_xp_event_topic(),
        hero.executor_pubkey().unwrap(),
        hero.federation_id(),
    )
    .unwrap();
    let policy = PrivateBazaarRaidPolicy::load(pin, roster, reward).unwrap();
    let root = tempfile::tempdir().unwrap();
    let authority_dir = root.path().join("authority");
    let session_dir = root.path().join("sessions");
    let session = "web-private-bazaar-restart";
    let seed = seed_from_id(session);

    {
        let deployment =
            PrivateBazaarLiveDeployment::open(policy.clone(), 1, &authority_dir).unwrap();
        let state = Arc::new(CatalogState::with_private_bazaar_over(
            deployment.clone(),
            Some(session_dir.clone()),
            SessionPolicy::default(),
        ));
        let app = catalog_router(state);
        let base = format!("/offerings/{PRIVATE_BAZAAR_RAID_KEY}/session/{session}");
        let (status, _) = body(
            app.clone()
                .oneshot(Request::builder().uri(&base).body(Body::empty()).unwrap())
                .await
                .unwrap(),
        )
        .await;
        assert_eq!(status, StatusCode::OK);
        let (status, _) = body(
            app.oneshot(
                Request::builder()
                    .method("POST")
                    .uri(format!("{base}/act"))
                    .header("content-type", "application/x-www-form-urlencoded")
                    .header("cookie", "dregg_user=web-restarted-raider")
                    .body(Body::from(format!(
                        "turn={TURN_ENTER_PRIVATE_BAZAAR}&arg=0"
                    )))
                    .unwrap(),
            )
            .await
            .unwrap(),
        )
        .await;
        assert_eq!(status, StatusCode::OK);
        assert!(deployment.registry().contains(seed));
    }

    let restarted = PrivateBazaarLiveDeployment::open(policy, 1, authority_dir).unwrap();
    let restarted_state = Arc::new(CatalogState::with_private_bazaar_over(
        restarted.clone(),
        Some(session_dir),
        SessionPolicy::default(),
    ));
    let (status, verify) = body(
        catalog_router(restarted_state)
            .oneshot(
                Request::builder()
                    .uri(format!(
                        "/offerings/{PRIVATE_BAZAAR_RAID_KEY}/session/{session}/verify"
                    ))
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap(),
    )
    .await;
    assert_eq!(status, StatusCode::OK);
    assert!(verify.contains("\"verified\":true"), "{verify}");
    assert!(
        restarted.registry().contains(seed),
        "boot resume must replay Enter through the real offering and repopulate the new process registry"
    );
}
