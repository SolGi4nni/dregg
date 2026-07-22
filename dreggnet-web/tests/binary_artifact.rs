//! Canonical read-only artifacts over the generic web/Telegram/Discord hosting seam.

#![cfg(feature = "hosted-binary-operations")]

use std::sync::Arc;

use axum::{Router, body::Body, http::Request};
use deos_view::ViewNode;
use dreggnet_offerings::{
    Action, BinaryArtifactDescriptor, BinaryArtifactError, BinaryArtifactVisibility, DreggIdentity,
    Offering, OfferingError, OfferingHost, Outcome, RunCost, SessionConfig, SessionId, Surface,
    VerifyReport,
};
use dreggnet_web::discord_activity::{
    DiscordActivityState, DiscordCodeExchange, DiscordTokenExchange, OAuthError,
    discord_activity_router,
};
use dreggnet_web::telegram_miniapp::{TgMiniAppState, tg_miniapp_router};
use dreggnet_web::{CatalogState, fhegg_operation};
use tower::ServiceExt;

const PUBLIC: &str = "collective-decision-task.v1";
const MEMBER: &str = "committee-task.v1";
const BODY: &[u8] = b"canonical-public-worker-task";

#[derive(Clone, Copy)]
enum Fixture {
    Valid,
    Oversized,
    BadMedia,
}

struct ArtifactOffering(Fixture);

struct NoopDiscordExchange;

impl DiscordTokenExchange for NoopDiscordExchange {
    fn exchange(
        &self,
        _client_id: &str,
        _client_secret: &str,
        _code: &str,
    ) -> Result<DiscordCodeExchange, OAuthError> {
        Err(OAuthError::TokenStatus(401))
    }
}

impl ArtifactOffering {
    fn descriptor(name: &str, visibility: BinaryArtifactVisibility) -> BinaryArtifactDescriptor {
        BinaryArtifactDescriptor {
            name: name.to_string(),
            title: "Collective decision worker task".to_string(),
            media_type: "application/vnd.dregg.collective-decision-task-v1".to_string(),
            max_bytes: 64,
            disclosure: "Public state bindings only; no key shares or decrypted values."
                .to_string(),
            visibility,
        }
    }
}

impl Offering for ArtifactOffering {
    type Session = ();

    fn open(&self, _cfg: SessionConfig) -> Result<Self::Session, OfferingError> {
        Ok(())
    }

    fn actions(&self, _session: &Self::Session) -> Vec<Action> {
        Vec::new()
    }

    fn advance(
        &self,
        _session: &mut Self::Session,
        _input: Action,
        _actor: DreggIdentity,
    ) -> Outcome {
        Outcome::Refused("read-only".to_string())
    }

    fn verify(&self, _session: &Self::Session) -> VerifyReport {
        VerifyReport::ok(0)
    }

    fn render(&self, _session: &Self::Session) -> Surface {
        Surface(ViewNode::Text("artifact fixture".to_string()))
    }

    fn binary_artifacts(&self, _session: &Self::Session) -> Vec<BinaryArtifactDescriptor> {
        let mut public = Self::descriptor(PUBLIC, BinaryArtifactVisibility::Public);
        if matches!(self.0, Fixture::Oversized) {
            public.max_bytes = 8;
        }
        if matches!(self.0, Fixture::BadMedia) {
            public.media_type = "not a media type".to_string();
        }
        vec![
            public,
            Self::descriptor(MEMBER, BinaryArtifactVisibility::Authenticated),
        ]
    }

    fn export_binary_artifact(
        &self,
        _session: &Self::Session,
        name: &str,
    ) -> Result<Vec<u8>, BinaryArtifactError> {
        match name {
            PUBLIC => Ok(BODY.to_vec()),
            MEMBER => Ok(b"attributed-member-task".to_vec()),
            _ => Err(BinaryArtifactError::UnknownArtifact(name.to_string())),
        }
    }

    fn price(&self, _input: &Action) -> RunCost {
        RunCost::free()
    }
}

fn catalog() -> Arc<CatalogState> {
    Arc::new(CatalogState::with_host(|| {
        let mut host = OfferingHost::new();
        for (key, fixture) in [
            ("valid", Fixture::Valid),
            ("oversized", Fixture::Oversized),
            ("bad-media", Fixture::BadMedia),
        ] {
            host.register(key, "Artifact fixture", ArtifactOffering(fixture));
            host.open_session(key, SessionId::new("live"), SessionConfig::default())
                .expect("fixture session opens");
        }
        host
    }))
}

fn game_catalog() -> Arc<CatalogState> {
    Arc::new(CatalogState::with_host(|| {
        let mut host = OfferingHost::new();
        host.register(
            "dungeon",
            "Artifact game fixture",
            ArtifactOffering(Fixture::Valid),
        );
        host.open_session(
            "dungeon",
            SessionId::new("artifact-epoch"),
            SessionConfig::default(),
        )
        .expect("fixture game session opens");
        host
    }))
}

fn get(path: &str) -> Request<Body> {
    Request::builder().uri(path).body(Body::empty()).unwrap()
}

#[tokio::test]
async fn public_get_returns_exact_canonical_body_media_digest_etag_and_no_store() {
    let app = Router::new().merge(fhegg_operation::router(catalog()));
    let response = app
        .clone()
        .oneshot(get(&format!(
            "/offerings/valid/session/live/artifacts/{PUBLIC}"
        )))
        .await
        .expect("artifact response");
    assert_eq!(response.status(), 200);
    assert_eq!(
        response.headers()["content-type"],
        "application/vnd.dregg.collective-decision-task-v1"
    );
    assert_eq!(response.headers()["cache-control"], "no-store");
    let digest = blake3::hash(BODY).to_hex().to_string();
    assert_eq!(response.headers()["etag"], format!("\"{digest}\""));
    assert_eq!(
        response.headers()["x-dregg-artifact-digest"],
        format!("blake3:{digest}")
    );
    let bytes = axum::body::to_bytes(response.into_body(), usize::MAX)
        .await
        .expect("bounded response body");
    assert_eq!(bytes.as_ref(), BODY);

    let discovery = app
        .clone()
        .oneshot(get("/offerings/valid/session/live/artifacts"))
        .await
        .unwrap();
    assert_eq!(discovery.status(), 200);
    let discovery = axum::body::to_bytes(discovery.into_body(), usize::MAX)
        .await
        .unwrap();
    let discovery = String::from_utf8(discovery.to_vec()).unwrap();
    assert!(discovery.contains("\"visibility\":\"public\""));
    assert!(discovery.contains("\"visibility\":\"authenticated\""));
    assert!(discovery.contains("X-Dregg-Artifact-Digest"));
}

#[tokio::test]
async fn routing_visibility_size_and_media_policy_refuse_before_any_ambiguous_response() {
    let app = Router::new().merge(fhegg_operation::router(catalog()));

    for path in [
        format!("/offerings/valid/session/absent/artifacts/{PUBLIC}"),
        "/offerings/valid/session/live/artifacts/not-this-task.v1".to_string(),
    ] {
        assert_eq!(app.clone().oneshot(get(&path)).await.unwrap().status(), 404);
    }

    let member_path = format!("/offerings/valid/session/live/artifacts/{MEMBER}");
    assert_eq!(
        app.clone()
            .oneshot(get(&member_path))
            .await
            .unwrap()
            .status(),
        401
    );
    let attributed = Request::builder()
        .uri(&member_path)
        .header("cookie", "dregg_user=committee-worker")
        .body(Body::empty())
        .unwrap();
    assert_eq!(app.clone().oneshot(attributed).await.unwrap().status(), 200);

    assert_eq!(
        app.clone()
            .oneshot(get(&format!(
                "/offerings/oversized/session/live/artifacts/{PUBLIC}"
            )))
            .await
            .unwrap()
            .status(),
        500
    );
    assert_eq!(
        app.oneshot(get(&format!(
            "/offerings/bad-media/session/live/artifacts/{PUBLIC}"
        )))
        .await
        .unwrap()
        .status(),
        500
    );
}

#[tokio::test]
async fn telegram_and_discord_wrappers_authenticate_before_export() {
    let catalog = catalog();
    let app = Router::new()
        .merge(tg_miniapp_router(Arc::new(TgMiniAppState::new(
            Arc::clone(&catalog),
            "artifact-test-bot-token",
            [0x51; 32],
            86_400,
        ))))
        .merge(discord_activity_router(Arc::new(
            DiscordActivityState::with_oauth(
                Arc::clone(&catalog),
                "artifact-client",
                "artifact-secret",
                [0x52; 32],
                86_400,
                Arc::new(NoopDiscordExchange),
            ),
        )));

    for prefix in ["/tg", "/da"] {
        let path = format!("{prefix}/offerings/valid/session/live/artifacts/{PUBLIC}");
        assert_eq!(app.clone().oneshot(get(&path)).await.unwrap().status(), 401);
    }
}

#[tokio::test]
async fn game_artifact_url_is_bound_to_its_presented_generation_and_head() {
    let catalog = game_catalog();
    let app = Router::new().merge(fhegg_operation::router(Arc::clone(&catalog)));
    let discovery_path = "/offerings/dungeon/session/artifact-epoch/artifacts";
    let export_path = format!("{discovery_path}/{PUBLIC}");

    async fn authority_query(app: &Router, path: &str) -> String {
        let response = app.clone().oneshot(get(path)).await.unwrap();
        assert_eq!(response.status(), 200);
        let bytes = axum::body::to_bytes(response.into_body(), usize::MAX)
            .await
            .unwrap();
        let discovery: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
        discovery[0]["gameAuthority"]["query"]
            .as_str()
            .expect("game artifact discovery carries an epoch/head query")
            .to_string()
    }

    let generation_one_query = authority_query(&app, discovery_path).await;
    assert_eq!(
        app.clone()
            .oneshot(get(&export_path))
            .await
            .unwrap()
            .status(),
        409,
        "a game artifact cannot be exported without its presented authority"
    );
    let mut tampered_query = generation_one_query.clone();
    let last = tampered_query.pop().expect("authority query is non-empty");
    tampered_query.push(if last == '0' { '1' } else { '0' });
    assert_eq!(
        app.clone()
            .oneshot(get(&format!("{export_path}?{tampered_query}")))
            .await
            .unwrap()
            .status(),
        409,
        "a modified game artifact authority token must fail closed"
    );
    assert_eq!(
        app.clone()
            .oneshot(get(&format!("{export_path}?{generation_one_query}")))
            .await
            .unwrap()
            .status(),
        200
    );

    assert!(
        catalog
            .close_game_session(
                "dungeon",
                &SessionId::new("artifact-epoch"),
                &DreggIdentity("artifact-reader".to_string()),
            )
            .unwrap()
    );
    let generation_two_query = authority_query(&app, discovery_path).await;
    assert_ne!(generation_one_query, generation_two_query);
    assert_eq!(
        app.clone()
            .oneshot(get(&format!("{export_path}?{generation_one_query}")))
            .await
            .unwrap()
            .status(),
        409,
        "a bookmarked generation-one export URL must not read generation two"
    );
    assert_eq!(
        app.oneshot(get(&format!("{export_path}?{generation_two_query}")))
            .await
            .unwrap()
            .status(),
        200
    );
}
