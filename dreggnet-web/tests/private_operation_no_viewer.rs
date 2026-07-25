//! A private-operation descriptor may be context-bound internally, but the
//! ordinary browser and anonymous discovery payload never echo its bound actor.

#![cfg(feature = "private-preference-operation")]

use std::sync::Arc;

use axum::Router;
use axum::body::Body;
use axum::http::{Request, StatusCode};
use deos_view::ViewNode;
use dreggnet_offerings::{
    Action, BinaryOperationDescriptor, BinaryOperationError, BinaryOperationReceipt, DreggIdentity,
    Offering, OfferingError, OfferingHost, Outcome, RunCost, SessionConfig, SessionId, Surface,
    VerifyReport,
};
use dreggnet_web::{CatalogState, catalog_router, fhegg_operation, web_identity};
use serde_json::Value;
use tower::ServiceExt;

mod common;

const HOSTILE_OPERATION: &str = "test.private-result-boundary.v1";
const HOSTILE_MEDIA_TYPE: &str = "application/vnd.dregg.test-private-result.v1";

struct HostileResultOffering;

impl Offering for HostileResultOffering {
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
        Outcome::Refused("this fixture exposes only an opaque operation".to_string())
    }

    fn verify(&self, _session: &Self::Session) -> VerifyReport {
        VerifyReport::ok(0)
    }

    fn render(&self, _session: &Self::Session) -> Surface {
        Surface(ViewNode::Text(
            "private result boundary fixture".to_string(),
        ))
    }

    fn binary_operations(&self, _session: &Self::Session) -> Vec<BinaryOperationDescriptor> {
        vec![BinaryOperationDescriptor {
            name: HOSTILE_OPERATION.to_string(),
            title: "actor-bound title must not be trusted".to_string(),
            input_media_type: HOSTILE_MEDIA_TYPE.to_string(),
            max_input_bytes: 8,
            disclosure: "fixture".to_string(),
        }]
    }

    fn invoke_binary_operation(
        &self,
        _session: &mut Self::Session,
        name: &str,
        _payload: &[u8],
        actor: DreggIdentity,
    ) -> Result<BinaryOperationReceipt, BinaryOperationError> {
        if name != HOSTILE_OPERATION {
            return Err(BinaryOperationError::UnknownOperation(name.to_string()));
        }
        Ok(BinaryOperationReceipt {
            operation: HOSTILE_OPERATION.to_string(),
            receipt_id: [0x52; 32],
            public_fields: vec![
                ("actor".to_string(), actor.0),
                (
                    "submitterHandle".to_string(),
                    "private-player-name".to_string(),
                ),
                (
                    "apparentlyHarmlessNewField".to_string(),
                    "private-value".to_string(),
                ),
                ("proofBytes".to_string(), "private-proof".to_string()),
                ("newRoot".to_string(), "public-root".to_string()),
                ("winner".to_string(), "north".to_string()),
            ],
        })
    }

    fn price(&self, _input: &Action) -> RunCost {
        RunCost::free()
    }
}

async fn response(app: &Router, request: Request<Body>) -> (StatusCode, String) {
    let response = app.clone().oneshot(request).await.expect("router response");
    let status = response.status();
    let body = axum::body::to_bytes(response.into_body(), usize::MAX)
        .await
        .expect("response body");
    (
        status,
        String::from_utf8(body.to_vec()).expect("text response"),
    )
}

#[tokio::test]
async fn private_descriptor_context_is_not_a_public_viewer_payload() {
    let state = Arc::new(CatalogState::new());
    let app =
        common::guard(catalog_router(Arc::clone(&state)).merge(fhegg_operation::router(state)));
    let base = "/offerings/descent/session/no-viewer-private-operation";
    let alice = "private-alice";
    let actor = web_identity(alice).0;

    let (status, _) = response(
        &app,
        Request::builder()
            .uri(base)
            .header("cookie", format!("dregg_user={alice}"))
            .body(Body::empty())
            .unwrap(),
    )
    .await;
    assert_eq!(status, StatusCode::OK);
    // `descent` is a SPINED game key: the POST must carry the route authority the surface stamped
    // into its own form, or it is `409 invalid game reference` and no run is ever bound to an
    // actor — which is the whole premise of the leak assertions below.
    let act_uri = format!("{base}/act");
    let cookie = format!("dregg_user={alice}");
    let (status, _) = response(
        &app,
        Request::builder()
            .method("POST")
            .uri(&act_uri)
            .header("content-type", "application/x-www-form-urlencoded")
            .header("cookie", &cookie)
            .body(Body::from(
                common::act_body(&app, &act_uri, "delve", 0, Some(&cookie)).await,
            ))
            .unwrap(),
    )
    .await;
    assert_eq!(status, StatusCode::OK);

    // A different viewer sees the shared public state, but never the actor
    // interpolated into Native Descent's internal operation descriptor title.
    let (status, page) = response(
        &app,
        Request::builder()
            .uri(base)
            .header("cookie", "dregg_user=private-bob")
            .body(Body::empty())
            .unwrap(),
    )
    .await;
    assert_eq!(status, StatusCode::OK);
    // Native Descent deliberately publishes its committed player on the game
    // surface. The privacy boundary here is narrower and exact: descriptor
    // context must not be echoed by the opaque-operation control shown to a
    // viewer. Inspect that region rather than misclassifying the public player
    // projection as a proof-witness leak.
    let operation_region = page
        .split_once("<section class=\"operation-uploader\">")
        .map(|(_, region)| region)
        .expect("the private-operation uploader is rendered");
    assert!(
        !operation_region.contains(&actor),
        "bound actor leaked into the operation uploader: {operation_region}"
    );
    assert!(
        page.contains("Verify a shielded party preference"),
        "{page}"
    );
    assert!(
        page.contains("data-private-boundary=\"opaque-upload\""),
        "{page}"
    );

    let (status, discovery) = response(
        &app,
        Request::builder()
            .uri(format!("{base}/operations"))
            .body(Body::empty())
            .unwrap(),
    )
    .await;
    assert_eq!(status, StatusCode::OK);
    assert!(
        !discovery.contains(&actor),
        "bound actor leaked into JSON: {discovery}"
    );
    assert!(
        discovery.contains("Verify a shielded party preference"),
        "{discovery}"
    );
}

#[tokio::test]
async fn operation_response_omits_actor_and_every_unreviewed_field_by_default() {
    const SESSION: &str = "hostile-private-result";
    let state = Arc::new(CatalogState::with_host(|| {
        let mut host = OfferingHost::new();
        host.register("dungeon", "Hostile result fixture", HostileResultOffering);
        host.open_session("dungeon", SessionId::new(SESSION), SessionConfig::default())
            .expect("fixture session opens");
        host
    }));
    let app =
        common::guard(catalog_router(Arc::clone(&state)).merge(fhegg_operation::router(state)));
    let actor = web_identity("private-response-player").0;
    let session_path = format!("/offerings/dungeon/session/{SESSION}");
    let (status, page) = response(
        &app,
        Request::builder()
            .uri(&session_path)
            .header("cookie", "dregg_user=private-response-player")
            .body(Body::empty())
            .unwrap(),
    )
    .await;
    assert_eq!(status, StatusCode::OK, "{page}");

    let (status, body) = response(
        &app,
        Request::builder()
            .method("POST")
            .uri(format!("{session_path}/operations/{HOSTILE_OPERATION}"))
            .header("content-type", HOSTILE_MEDIA_TYPE)
            .header("cookie", "dregg_user=private-response-player")
            .body(Body::from(vec![1, 2, 3]))
            .unwrap(),
    )
    .await;
    assert_eq!(status, StatusCode::OK, "{body}");
    for private in [
        actor.as_str(),
        "private-player-name",
        "private-value",
        "private-proof",
        "submitterHandle",
        "apparentlyHarmlessNewField",
        "proofBytes",
    ] {
        assert!(
            !body.contains(private),
            "response leaked {private:?}: {body}"
        );
    }
    let body: Value = serde_json::from_str(&body).expect("operation response is JSON");
    assert_eq!(body["status"], "applied");
    assert_eq!(body["gameFamily"], "dungeon");
    assert_eq!(body["attribution"], "asserted");
    assert_eq!(body["result"]["kind"], "operation");
    assert_eq!(
        body["result"]["fields"]
            .as_array()
            .expect("typed public fields is an array")
            .len(),
        0,
        "an unknown operation route cannot promote even otherwise-audited field names"
    );
    for commitment in ["sessionRouteId", "receiptId", "publicationId"] {
        assert_eq!(
            body[commitment]
                .as_str()
                .unwrap_or_else(|| panic!("missing {commitment}"))
                .len(),
            64,
            "{commitment} is a 32-byte hex commitment"
        );
    }
}
