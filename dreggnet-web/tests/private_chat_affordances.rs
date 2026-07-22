//! Exact browser affordances for the private preference, fair-shuffle, and
//! semantic-quest receipts that ordinary chat players produce out of band.

#![cfg(all(
    feature = "private-preference-operation",
    feature = "private-fair-shuffle-operation",
    feature = "private-quest-operation",
))]

use std::sync::Arc;

use axum::{body::Body, http::Request};
use dreggnet_offerings::dungeon::{
    DungeonOffering, PRIVATE_PREFERENCE_OPERATION, PRIVATE_QUEST_OPERATION,
    PRIVATE_SHUFFLE_COMMIT_OPERATION, PRIVATE_SHUFFLE_PROVE_OPERATION,
    PRIVATE_SHUFFLE_REVEAL_OPERATION,
};
use dreggnet_offerings::{Offering, SessionConfig, SessionId};
use dreggnet_web::{CatalogState, catalog_router, game_session};
use tower::ServiceExt;

#[tokio::test]
async fn browser_surface_renders_exact_private_preference_shuffle_and_quest_upload_controls() {
    const SESSION: &str = "web-private-operation-affordances";

    let descriptor_offering = DungeonOffering::new();
    let descriptor_session = descriptor_offering
        .open(SessionConfig::with_seed(0x0F_FE12))
        .expect("descriptor fixture opens");
    let operations = descriptor_offering.binary_operations(&descriptor_session);

    let state = Arc::new(CatalogState::with_host(|| {
        let mut host = dreggnet_web::demo_host();
        host.open_session(
            "dungeon",
            SessionId::new(SESSION),
            SessionConfig::with_seed(0x0F_FE12),
        )
        .expect("browser fixture opens");
        host
    }));
    let response = catalog_router(state)
        .oneshot(
            Request::builder()
                .uri(format!("/offerings/dungeon/session/{SESSION}"))
                .header("cookie", "dregg_user=web-private-player")
                .body(Body::empty())
                .unwrap(),
        )
        .await
        .unwrap();
    assert_eq!(response.status(), axum::http::StatusCode::OK);
    let html = String::from_utf8(
        axum::body::to_bytes(response.into_body(), usize::MAX)
            .await
            .unwrap()
            .to_vec(),
    )
    .unwrap();

    for name in [
        PRIVATE_PREFERENCE_OPERATION,
        PRIVATE_SHUFFLE_COMMIT_OPERATION,
        PRIVATE_SHUFFLE_PROVE_OPERATION,
        PRIVATE_SHUFFLE_REVEAL_OPERATION,
        PRIVATE_QUEST_OPERATION,
    ] {
        let operation = operations
            .iter()
            .find(|operation| operation.name == name)
            .unwrap_or_else(|| panic!("missing live descriptor {name}"));
        let action = format!("action=\"/offerings/dungeon/session/{SESSION}/operations/{name}\"");
        assert!(
            html.contains(&action),
            "missing exact browser route {action}"
        );
        assert!(
            html.contains(&format!("data-media=\"{}\"", operation.input_media_type)),
            "missing exact browser media policy for {name}"
        );
        assert!(
            html.contains(&format!("accept=\"{}\"", operation.input_media_type)),
            "missing exact file-picker media affordance for {name}"
        );
        assert!(
            html.contains(game_session::public_operation_title(&operation.name)),
            "missing exact browser control title for {name}"
        );
        assert!(
            html.contains(&operation.disclosure),
            "missing exact disclosure for {name}"
        );
        assert!(
            html.contains(&format!(
                "Maximum canonical input: {} bytes.",
                operation.max_input_bytes
            )),
            "missing exact browser cap for {name}"
        );
    }
}
