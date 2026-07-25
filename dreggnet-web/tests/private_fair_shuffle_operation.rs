//! A real commit-before-reveal private deal through the generic web operation
//! path, ending in a seat-owned selective opening on the live dungeon.

#![cfg(feature = "private-fair-shuffle-operation")]

use std::sync::Arc;

use axum::{Router, body::Body, http::Request};
use dreggnet_offerings::dungeon::{
    DungeonOffering, PRIVATE_SHUFFLE_COMMIT_MEDIA_TYPE, PRIVATE_SHUFFLE_COMMIT_OPERATION,
    PRIVATE_SHUFFLE_DISCLOSURE, PRIVATE_SHUFFLE_PROOF_MEDIA_TYPE, PRIVATE_SHUFFLE_PROVE_OPERATION,
    PRIVATE_SHUFFLE_REVEAL_MEDIA_TYPE, PRIVATE_SHUFFLE_REVEAL_OPERATION,
    encode_private_shuffle_commitment, private_fair_shuffle_session_for_seed,
};
use dreggnet_offerings::{OfferingHost, SessionConfig, SessionId};
use dreggnet_web::{CatalogState, catalog_router, fhegg_operation};
use dungeon_on_dregg::private_fair_shuffle::{PARTICIPANTS, PreparedFairShuffle};
use dungeon_on_dregg::{
    KP_PRESS_ON, KP_PRIVATE_SHUFFLE_EVEN_INITIATIVE, KP_PRIVATE_SHUFFLE_ODD_INITIATIVE,
};
use tower::ServiceExt;

mod common;

const OFFERING: &str = "dungeon";
const SESSION: &str = "private-fair-deal";
const SEED: u64 = 0xFA17;

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

fn upload(path: &str, media_type: &str, user: &str, body: impl Into<Body>) -> Request<Body> {
    Request::builder()
        .method("POST")
        .uri(path)
        .header("content-type", media_type)
        .header("cookie", format!("dregg_user={user}"))
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
async fn eight_web_actors_commit_then_one_proof_and_one_owned_opening_land() {
    let catalog = catalog();
    let app = common::guard(
        Router::new()
            .merge(catalog_router(Arc::clone(&catalog)))
            .merge(fhegg_operation::router(Arc::clone(&catalog))),
    );
    let game_path = format!("/offerings/{OFFERING}/session/{SESSION}");
    let act_path = format!("{game_path}/act");
    let (status, entered) = response(&app, act(&app, &act_path, KP_PRESS_ON, "seat-6").await).await;
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
    for operation in [
        PRIVATE_SHUFFLE_COMMIT_OPERATION,
        PRIVATE_SHUFFLE_PROVE_OPERATION,
        PRIVATE_SHUFFLE_REVEAL_OPERATION,
    ] {
        assert!(descriptors.contains(operation));
    }
    assert!(descriptors.contains(PRIVATE_SHUFFLE_DISCLOSURE));

    let prepared = PreparedFairShuffle::fresh(
        private_fair_shuffle_session_for_seed(SEED),
        0,
        [12_345, 1, 2, 3, 4, 5, 6, 7],
    )
    .unwrap();
    let commit_route = format!("{operations}/{PRIVATE_SHUFFLE_COMMIT_OPERATION}");
    for participant in 0..PARTICIPANTS {
        let commitment = encode_private_shuffle_commitment(
            participant as u8,
            prepared.participant_commitment(participant).unwrap(),
        );
        assert_eq!(
            response(
                &app,
                upload(
                    &commit_route,
                    PRIVATE_SHUFFLE_COMMIT_MEDIA_TYPE,
                    &format!("seat-{participant}"),
                    commitment,
                ),
            )
            .await
            .0,
            200
        );
    }

    // The proof producer uses the already-published commitments; build a local
    // mirror table to exercise the exact commit-before-proof API.
    let mut mirror = dungeon_on_dregg::private_fair_shuffle::FairShuffleTable::new(
        private_fair_shuffle_session_for_seed(SEED),
    )
    .unwrap();
    for participant in 0..PARTICIPANTS {
        mirror
            .commit(
                participant,
                prepared.participant_commitment(participant).unwrap(),
            )
            .unwrap();
    }
    let proof = prepared
        .prove_receipt(&mirror)
        .unwrap()
        .to_postcard()
        .unwrap();
    let prove_route = format!("{operations}/{PRIVATE_SHUFFLE_PROVE_OPERATION}");
    let (status, body) = response(
        &app,
        upload(
            &prove_route,
            PRIVATE_SHUFFLE_PROOF_MEDIA_TYPE,
            "proof-relay",
            proof,
        ),
    )
    .await;
    assert_eq!(status, 200, "{}", String::from_utf8_lossy(&body));
    assert!(String::from_utf8(body).unwrap().contains("accepted"));

    let prepared_opening = prepared.card_opening(6).unwrap();
    let card = prepared_opening.card;
    let opening = prepared_opening.to_postcard().unwrap();
    let reveal_route = format!("{operations}/{PRIVATE_SHUFFLE_REVEAL_OPERATION}");
    assert_eq!(
        response(
            &app,
            upload(
                &reveal_route,
                PRIVATE_SHUFFLE_REVEAL_MEDIA_TYPE,
                "seat-5",
                opening.clone(),
            ),
        )
        .await
        .0,
        409
    );
    let (status, opened) = response(
        &app,
        upload(
            &reveal_route,
            PRIVATE_SHUFFLE_REVEAL_MEDIA_TYPE,
            "seat-6",
            opening,
        ),
    )
    .await;
    assert_eq!(status, 200, "{}", String::from_utf8_lossy(&opened));
    assert!(String::from_utf8(opened).unwrap().contains("card"));

    let initiative = if card % 2 == 0 {
        KP_PRIVATE_SHUFFLE_EVEN_INITIATIVE
    } else {
        KP_PRIVATE_SHUFFLE_ODD_INITIATIVE
    };
    let (status, enacted) = response(&app, act(&app, &act_path, initiative, "seat-6").await).await;
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
            .header("cookie", "dregg_user=seat-6")
            .body(Body::empty())
            .unwrap(),
    )
    .await;
    assert_eq!(status, 200);
    let game = String::from_utf8(game).unwrap();
    assert!(game.contains("Private fair deal"));
    assert!(game.contains("accepted attempt 0"));
    assert!(game.contains("1 private card opening(s) landed"));
    assert!(game.contains("depth 1"));
    assert!(game.contains(if card % 2 == 0 {
        "crown Red Hand"
    } else {
        "crown Blue Hand"
    }));

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
