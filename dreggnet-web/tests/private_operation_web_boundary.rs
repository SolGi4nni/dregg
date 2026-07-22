//! The ordinary browser upload seam obeys each live Dungeon operation's exact
//! descriptor before the shared host decoder or mutator sees a byte.

#![cfg(all(
    feature = "private-preference-operation",
    feature = "private-fair-shuffle-operation",
    feature = "private-quest-operation",
))]

use std::sync::Arc;
use std::{
    convert::Infallible,
    pin::Pin,
    task::{Context, Poll},
};

use axum::{
    Router,
    body::{Body, Bytes},
    http::{Request, StatusCode},
};
use dreggnet_offerings::dungeon::{
    DungeonOffering, PRIVATE_PREFERENCE_OPERATION, PRIVATE_QUEST_OPERATION,
    PRIVATE_SHUFFLE_COMMIT_OPERATION, PRIVATE_SHUFFLE_PROVE_OPERATION,
    PRIVATE_SHUFFLE_REVEAL_OPERATION,
};
use dreggnet_offerings::{
    BinaryOperationDescriptor, Offering, OfferingHost, SessionConfig, SessionId,
};
use dreggnet_web::{CatalogState, catalog_router, fhegg_operation, game_session};
use serde_json::Value;
use tower::ServiceExt;

struct GatedBody {
    body_started: Option<tokio::sync::oneshot::Sender<()>>,
    bytes: tokio_stream::wrappers::ReceiverStream<Result<Bytes, Infallible>>,
}

impl tokio_stream::Stream for GatedBody {
    type Item = Result<Bytes, Infallible>;

    fn poll_next(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>> {
        if let Some(body_started) = self.body_started.take() {
            let _ = body_started.send(());
        }
        Pin::new(&mut self.bytes).poll_next(cx)
    }
}

const OFFERING: &str = "dungeon";
const SESSION: &str = "private-operation-web-boundary";
const SEED: u64 = 0x0B_0A_DA_12;
const AUTHENTICATION: &str = "surface-attributed actor; web labels are asserted, while native adapters verify their own envelopes; exact live offering/session path";

fn catalog() -> Arc<CatalogState> {
    Arc::new(CatalogState::with_host(|| {
        let mut host = OfferingHost::new();
        host.register(OFFERING, "The Warden's Keep", DungeonOffering::new());
        host.open_session(
            OFFERING,
            SessionId::new(SESSION),
            SessionConfig::with_seed(SEED),
        )
        .expect("web boundary fixture opens");
        host
    }))
}

fn five_descriptors() -> Vec<BinaryOperationDescriptor> {
    let offering = DungeonOffering::new();
    let session = offering
        .open(SessionConfig::with_seed(SEED))
        .expect("descriptor fixture opens");
    let operations = offering.binary_operations(&session);
    [
        PRIVATE_PREFERENCE_OPERATION,
        PRIVATE_SHUFFLE_COMMIT_OPERATION,
        PRIVATE_SHUFFLE_PROVE_OPERATION,
        PRIVATE_SHUFFLE_REVEAL_OPERATION,
        PRIVATE_QUEST_OPERATION,
    ]
    .into_iter()
    .map(|name| {
        operations
            .iter()
            .find(|operation| operation.name == name)
            .unwrap_or_else(|| panic!("missing live descriptor {name}"))
            .clone()
    })
    .collect()
}

async fn response(app: &Router, request: Request<Body>) -> (StatusCode, Vec<u8>) {
    let response = app.clone().oneshot(request).await.unwrap();
    let status = response.status();
    let body = axum::body::to_bytes(response.into_body(), usize::MAX)
        .await
        .unwrap()
        .to_vec();
    (status, body)
}

fn upload(
    route: &str,
    media_type: &str,
    cookie: Option<&str>,
    content_length: Option<&str>,
    body: impl Into<Body>,
) -> Request<Body> {
    let mut request = Request::builder()
        .method("POST")
        .uri(route)
        .header("content-type", media_type);
    if let Some(cookie) = cookie {
        request = request.header("cookie", cookie);
    }
    if let Some(content_length) = content_length {
        request = request.header("content-length", content_length);
    }
    request.body(body.into()).unwrap()
}

fn error_reason(body: &[u8]) -> String {
    let value: Value = serde_json::from_slice(body).expect("refusal is JSON");
    assert_eq!(value["status"], "refused");
    value["error"]
        .as_str()
        .expect("refusal has a reason")
        .to_string()
}

#[tokio::test]
async fn five_private_operations_share_the_exact_web_discovery_and_refusal_boundary() {
    let descriptors = five_descriptors();
    let catalog = catalog();
    let app = Router::new()
        .merge(catalog_router(Arc::clone(&catalog)))
        .merge(fhegg_operation::router(catalog));
    let session_path = format!("/offerings/{OFFERING}/session/{SESSION}");
    let operations_path = format!("{session_path}/operations");

    // Enter through the ordinary game lifecycle before asking for affordances:
    // discovery is authority-bound to this host incarnation and generation.
    let (status, before) = response(
        &app,
        Request::builder()
            .uri(&session_path)
            .header("cookie", "dregg_user=web-boundary-player")
            .body(Body::empty())
            .unwrap(),
    )
    .await;
    assert_eq!(status, StatusCode::OK);

    let (status, discovery) = response(
        &app,
        Request::builder()
            .uri(&operations_path)
            .body(Body::empty())
            .unwrap(),
    )
    .await;
    assert_eq!(status, StatusCode::OK);
    let discovery: Value = serde_json::from_slice(&discovery).unwrap();
    let discovery = discovery.as_array().expect("operation discovery is a list");
    for descriptor in &descriptors {
        let wire = discovery
            .iter()
            .find(|wire| wire["name"].as_str() == Some(descriptor.name.as_str()))
            .unwrap_or_else(|| panic!("missing discovered operation {}", descriptor.name));
        assert_eq!(
            wire["title"].as_str(),
            Some(game_session::public_operation_title(&descriptor.name))
        );
        assert_eq!(
            wire["inputMediaType"].as_str(),
            Some(descriptor.input_media_type.as_str())
        );
        assert_eq!(
            wire["maxInputBytes"].as_u64(),
            Some(descriptor.max_input_bytes as u64)
        );
        assert_eq!(
            wire["disclosure"].as_str(),
            Some(descriptor.disclosure.as_str())
        );
        assert_eq!(
            wire["uploadPathSuffix"].as_str(),
            Some(fhegg_operation::UPLOAD_PATH_SUFFIX)
        );
        assert_eq!(wire["authentication"].as_str(), Some(AUTHENTICATION));
    }

    for descriptor in &descriptors {
        let route = format!("{operations_path}/{}", descriptor.name);

        let (status, body) = response(
            &app,
            upload(
                &route,
                &descriptor.input_media_type,
                None,
                None,
                Body::empty(),
            ),
        )
        .await;
        assert_eq!(status, StatusCode::UNAUTHORIZED, "{}", descriptor.name);
        assert_eq!(
            error_reason(&body),
            "an attributed web identity is required"
        );

        let (status, body) = response(
            &app,
            upload(
                &route,
                "application/octet-stream",
                Some("dregg_user=web-boundary-player"),
                None,
                Body::empty(),
            ),
        )
        .await;
        assert_eq!(
            status,
            StatusCode::UNSUPPORTED_MEDIA_TYPE,
            "{}",
            descriptor.name
        );
        assert_eq!(
            error_reason(&body),
            format!("content-type must be {}", descriptor.input_media_type)
        );

        let declared_oversize = (descriptor.max_input_bytes as u64 + 1).to_string();
        let (status, body) = response(
            &app,
            upload(
                &route,
                &descriptor.input_media_type,
                Some("dregg_user=web-boundary-player"),
                Some(&declared_oversize),
                Body::empty(),
            ),
        )
        .await;
        assert_eq!(status, StatusCode::PAYLOAD_TOO_LARGE, "{}", descriptor.name);
        assert_eq!(
            error_reason(&body),
            "operation input exceeds the hosted operation limit"
        );

        // Correctly attributed and typed empty input crosses the transport
        // boundary and is refused by the one real Dungeon decoder.
        let (status, _) = response(
            &app,
            upload(
                &route,
                &descriptor.input_media_type,
                Some("dregg_user=web-boundary-player"),
                None,
                Body::empty(),
            ),
        )
        .await;
        assert_eq!(status, StatusCode::BAD_REQUEST, "{}", descriptor.name);
    }

    let first = &descriptors[0];
    let first_route = format!("{operations_path}/{}", first.name);
    let (status, body) = response(
        &app,
        upload(
            &first_route,
            &first.input_media_type,
            Some("dregg_user=web-boundary-player"),
            Some("not-a-number"),
            Body::empty(),
        ),
    )
    .await;
    assert_eq!(status, StatusCode::BAD_REQUEST);
    assert_eq!(error_reason(&body), "invalid content-length");

    for (declared, received) in [("1", Vec::new()), ("0", vec![0])] {
        let (status, body) = response(
            &app,
            upload(
                &first_route,
                &first.input_media_type,
                Some("dregg_user=web-boundary-player"),
                Some(declared),
                received.clone(),
            ),
        )
        .await;
        assert_eq!(status, StatusCode::BAD_REQUEST);
        assert_eq!(
            error_reason(&body),
            format!(
                "operation input changed size during upload ({declared} declared, {} received)",
                received.len()
            )
        );
    }

    let query_route = format!("{first_route}?user=query-boundary-player");
    let (status, _) = response(
        &app,
        upload(
            &query_route,
            &first.input_media_type,
            None,
            None,
            Body::empty(),
        ),
    )
    .await;
    assert_eq!(
        status,
        StatusCode::BAD_REQUEST,
        "an explicit query identity must reach the decoder"
    );

    let smallest = descriptors
        .iter()
        .min_by_key(|descriptor| descriptor.max_input_bytes)
        .unwrap();
    let smallest_route = format!("{operations_path}/{}", smallest.name);
    let (status, body) = response(
        &app,
        upload(
            &smallest_route,
            &smallest.input_media_type,
            Some("dregg_user=web-boundary-player"),
            None,
            vec![0; smallest.max_input_bytes + 1],
        ),
    )
    .await;
    assert_eq!(status, StatusCode::PAYLOAD_TOO_LARGE);
    assert_eq!(
        error_reason(&body),
        "operation input exceeds the hosted operation limit"
    );

    let unknown_route = format!("{operations_path}/dungeon.not-installed.v1");
    let (status, body) = response(
        &app,
        upload(
            &unknown_route,
            "application/octet-stream",
            Some("dregg_user=web-boundary-player"),
            None,
            Body::empty(),
        ),
    )
    .await;
    assert_eq!(status, StatusCode::NOT_FOUND);
    assert_eq!(error_reason(&body), "unknown hosted operation");

    let (status, after) = response(
        &app,
        Request::builder()
            .uri(&session_path)
            .header("cookie", "dregg_user=web-boundary-player")
            .body(Body::empty())
            .unwrap(),
    )
    .await;
    assert_eq!(status, StatusCode::OK);
    assert_eq!(
        after, before,
        "transport and decoder refusals must not mutate the live game"
    );
}

#[tokio::test]
async fn close_reopen_while_upload_body_is_awaited_refuses_the_captured_operation_epoch() {
    let descriptor = five_descriptors().remove(0);
    let catalog = catalog();
    let app = Router::new()
        .merge(catalog_router(Arc::clone(&catalog)))
        .merge(fhegg_operation::router(Arc::clone(&catalog)));
    let session_path = format!("/offerings/{OFFERING}/session/{SESSION}");

    // Establish generation one before the upload captures its descriptor and
    // exact GameOperationRef.
    assert_eq!(
        response(
            &app,
            Request::builder()
                .uri(&session_path)
                .header("cookie", "dregg_user=slow-uploader")
                .body(Body::empty())
                .unwrap(),
        )
        .await
        .0,
        StatusCode::OK
    );

    let (body_started_tx, body_started_rx) = tokio::sync::oneshot::channel();
    let (bytes_tx, bytes_rx) = tokio::sync::mpsc::channel(1);
    let request = upload(
        &format!("{session_path}/operations/{}", descriptor.name),
        &descriptor.input_media_type,
        Some("dregg_user=slow-uploader"),
        None,
        Body::from_stream(GatedBody {
            body_started: Some(body_started_tx),
            bytes: tokio_stream::wrappers::ReceiverStream::new(bytes_rx),
        }),
    );
    let upload_task = tokio::spawn({
        let app = app.clone();
        async move { response(&app, request).await }
    });
    body_started_rx
        .await
        .expect("upload reached its bounded body read after descriptor capture");

    let sid = SessionId::new(SESSION);
    assert!(
        catalog
            .close_game_session(
                OFFERING,
                &sid,
                &dreggnet_offerings::DreggIdentity("slow-uploader".to_string()),
            )
            .expect("close generation one while upload is suspended")
    );
    assert_eq!(
        response(
            &app,
            Request::builder()
                .uri(&session_path)
                .header("cookie", "dregg_user=slow-uploader")
                .body(Body::empty())
                .unwrap(),
        )
        .await
        .0,
        StatusCode::OK,
        "ordinary navigation opens generation two"
    );

    bytes_tx.send(Ok(Bytes::from_static(&[0]))).await.unwrap();
    drop(bytes_tx);
    let (status, body) = upload_task.await.unwrap();
    assert_eq!(status, StatusCode::CONFLICT, "{}", error_reason(&body));
    assert!(
        error_reason(&body).contains("address") || error_reason(&body).contains("generation"),
        "the post-await authority revalidation, not the operation decoder, must refuse: {}",
        error_reason(&body)
    );
}
