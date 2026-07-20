//! Hosted binary operations shared by web, Telegram, and Discord.
//!
//! There is one decoder and mutator: the `dreggnet-market` binary operation
//! installed in the live `OfferingHost`.  This module supplies transport policy
//! (content type and bounded body), discovery JSON, and status mapping. Platform
//! modules authenticate their own request and call [`execute_upload`]; none of
//! them parses or interprets the bundle.

use std::collections::BTreeMap;
use std::sync::Arc;

use axum::{
    Json, Router,
    body::{Body, to_bytes},
    extract::{Path, Query, Request, State},
    http::{StatusCode, header},
    response::{IntoResponse, Response},
    routing::{get, post},
};
#[cfg(feature = "fhegg-settlement")]
use dreggnet_market::fhegg_transport::{FHEGG_SETTLEMENT_OPERATION, FheggSettlementOperation};
use dreggnet_offerings::{
    BinaryArtifactDescriptor, BinaryArtifactError, BinaryOperationDescriptor, BinaryOperationError,
    DreggIdentity, HostArtifactError, HostOperationError, SessionId,
};
use serde::Serialize;

use crate::{CatalogState, WebQuery, web_identity, web_user};

/// Relative suffix every adapter appends to its own authenticated surface
/// prefix. Keeping the prefix out of the descriptor makes discovery byte-equal
/// on web, Telegram, and Discord.
pub const UPLOAD_PATH_SUFFIX: &str =
    "/offerings/{offering}/session/{session}/operations/{operation}";

/// Relative suffix for one live offering's canonical read-only artifact.
pub const ARTIFACT_PATH_SUFFIX: &str =
    "/offerings/{offering}/session/{session}/artifacts/{artifact}";

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
struct ArtifactDescriptorWire {
    name: String,
    title: String,
    media_type: String,
    max_bytes: usize,
    disclosure: String,
    visibility: &'static str,
    download_path_suffix: &'static str,
    cache_policy: &'static str,
    integrity: &'static str,
}

impl From<BinaryArtifactDescriptor> for ArtifactDescriptorWire {
    fn from(value: BinaryArtifactDescriptor) -> Self {
        Self {
            name: value.name,
            title: value.title,
            media_type: value.media_type,
            max_bytes: value.max_bytes,
            disclosure: value.disclosure,
            visibility: value.visibility.as_str(),
            download_path_suffix: ARTIFACT_PATH_SUFFIX,
            cache_policy: "no-store",
            integrity: "BLAKE3 body digest in ETag and X-Dregg-Artifact-Digest",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
struct OperationDescriptorWire {
    name: String,
    title: String,
    input_media_type: String,
    max_input_bytes: usize,
    disclosure: String,
    upload_path_suffix: &'static str,
    authentication: &'static str,
    replay_scope: &'static str,
    durability: &'static str,
}

impl From<BinaryOperationDescriptor> for OperationDescriptorWire {
    fn from(value: BinaryOperationDescriptor) -> Self {
        Self {
            name: value.name,
            title: value.title,
            input_media_type: value.input_media_type,
            max_input_bytes: value.max_input_bytes,
            disclosure: value.disclosure,
            upload_path_suffix: UPLOAD_PATH_SUFFIX,
            authentication: "surface-authenticated actor; exact live offering/session path",
            replay_scope: "durable hosts journal only offering-selected safe replay material; otherwise the operation is refused before mutation",
            durability: "public receipt plus policy-approved replay material restore in timeline order; arbitrary upload bytes are never inferred safe",
        }
    }
}

#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct OperationAppliedWire {
    status: &'static str,
    operation: String,
    receipt_id: String,
    public_fields: BTreeMap<String, String>,
}

#[derive(Debug, Serialize)]
struct OperationErrorWire {
    status: &'static str,
    error: String,
}

fn error(status: StatusCode, reason: impl Into<String>) -> Response {
    (
        status,
        Json(OperationErrorWire {
            status: "refused",
            error: reason.into(),
        }),
    )
        .into_response()
}

fn hex32(bytes: &[u8; 32]) -> String {
    let mut out = String::with_capacity(64);
    for byte in bytes {
        use std::fmt::Write as _;
        let _ = write!(out, "{byte:02x}");
    }
    out
}

/// Static discovery payload used by all three surface routers.
#[cfg(feature = "fhegg-settlement")]
pub async fn get_descriptor(Path(name): Path<String>) -> Response {
    if name != FHEGG_SETTLEMENT_OPERATION {
        return error(StatusCode::NOT_FOUND, "unknown hosted operation");
    }
    Json(OperationDescriptorWire::from(
        FheggSettlementOperation::descriptor(),
    ))
    .into_response()
}

/// Discover operations actually enabled on one live session. Unlike the static
/// descriptor, this reads the host's selected verifier policy and therefore
/// returns an empty list when fhEgg acceptance is not configured.
async fn get_web_session_operations(
    State(catalog): State<Arc<CatalogState>>,
    Path((key, id)): Path<(String, String)>,
) -> Response {
    session_operations(&catalog, key, id)
}

/// Shared session-discovery implementation for platform wrappers.
pub(crate) fn session_operations(catalog: &Arc<CatalogState>, key: String, id: String) -> Response {
    let sid = SessionId::new(id);
    let viewer = DreggIdentity("operation-discovery".to_string());
    let result = {
        let routed_key = key.clone();
        let routed_sid = sid.clone();
        catalog.run_offering(&key, &viewer, move |host| {
            host.binary_operations(&routed_key, &routed_sid)
        })
    };
    match result {
        Ok(descriptors) => Json(
            descriptors
                .into_iter()
                .map(OperationDescriptorWire::from)
                .collect::<Vec<_>>(),
        )
        .into_response(),
        Err(HostOperationError::UnknownOffering(_)) => {
            error(StatusCode::NOT_FOUND, "unknown offering")
        }
        Err(HostOperationError::UnknownSession { .. }) => {
            error(StatusCode::NOT_FOUND, "unknown live session")
        }
        Err(HostOperationError::Operation(_)) => error(
            StatusCode::INTERNAL_SERVER_ERROR,
            "unexpected discovery error",
        ),
    }
}

/// Discover canonical read-only artifacts enabled on one exact live session.
async fn get_web_session_artifacts(
    State(catalog): State<Arc<CatalogState>>,
    Path((key, id)): Path<(String, String)>,
) -> Response {
    session_artifacts(&catalog, key, id)
}

/// Shared artifact discovery used by web, Telegram, and Discord wrappers.
pub(crate) fn session_artifacts(catalog: &Arc<CatalogState>, key: String, id: String) -> Response {
    let sid = SessionId::new(id);
    let viewer = DreggIdentity("artifact-discovery".to_string());
    let result = {
        let routed_key = key.clone();
        let routed_sid = sid.clone();
        catalog.run_offering(&key, &viewer, move |host| {
            host.binary_artifacts(&routed_key, &routed_sid)
        })
    };
    match result {
        Ok(descriptors) => Json(
            descriptors
                .into_iter()
                .map(ArtifactDescriptorWire::from)
                .collect::<Vec<_>>(),
        )
        .into_response(),
        Err(HostArtifactError::UnknownOffering(_)) => {
            error(StatusCode::NOT_FOUND, "unknown offering")
        }
        Err(HostArtifactError::UnknownSession { .. }) => {
            error(StatusCode::NOT_FOUND, "unknown live session")
        }
        Err(HostArtifactError::Artifact(_)) => error(
            StatusCode::INTERNAL_SERVER_ERROR,
            "invalid hosted artifact policy",
        ),
    }
}

/// Shared exact-session artifact export used by all surface wrappers.
pub(crate) fn export_artifact(
    catalog: &Arc<CatalogState>,
    key: String,
    id: String,
    name: String,
    viewer: Option<DreggIdentity>,
) -> Response {
    let sid = SessionId::new(id);
    let routing_viewer = viewer
        .clone()
        .unwrap_or_else(|| DreggIdentity("anonymous-artifact-reader".to_string()));
    let result = {
        let routed_key = key.clone();
        let routed_sid = sid.clone();
        let routed_name = name.clone();
        let routed_viewer = viewer.clone();
        catalog.run_offering(&key, &routing_viewer, move |host| {
            host.export_binary_artifact(
                &routed_key,
                &routed_sid,
                &routed_name,
                routed_viewer.as_ref(),
            )
        })
    };
    match result {
        Ok(artifact) => {
            let digest = hex32(&artifact.digest);
            let etag = format!("\"{digest}\"");
            let content_type = match artifact.media_type.parse::<axum::http::HeaderValue>() {
                Ok(value) => value,
                Err(_) => {
                    return error(
                        StatusCode::INTERNAL_SERVER_ERROR,
                        "invalid hosted artifact media type",
                    );
                }
            };
            let mut response = Response::new(Body::from(artifact.bytes));
            *response.status_mut() = StatusCode::OK;
            let headers = response.headers_mut();
            headers.insert(header::CONTENT_TYPE, content_type);
            headers.insert(
                header::CACHE_CONTROL,
                axum::http::HeaderValue::from_static("no-store"),
            );
            headers.insert(
                header::ETAG,
                axum::http::HeaderValue::from_str(&etag).expect("hex ETag is a valid header"),
            );
            headers.insert(
                axum::http::HeaderName::from_static("x-dregg-artifact-digest"),
                axum::http::HeaderValue::from_str(&format!("blake3:{digest}"))
                    .expect("hex digest is a valid header"),
            );
            response
        }
        Err(HostArtifactError::UnknownOffering(_)) => {
            error(StatusCode::NOT_FOUND, "unknown offering")
        }
        Err(HostArtifactError::UnknownSession { .. }) => {
            error(StatusCode::NOT_FOUND, "unknown live session")
        }
        Err(HostArtifactError::Artifact(BinaryArtifactError::UnknownArtifact(_))) => {
            error(StatusCode::NOT_FOUND, "unknown hosted artifact")
        }
        Err(HostArtifactError::Artifact(BinaryArtifactError::AuthenticationRequired)) => error(
            StatusCode::UNAUTHORIZED,
            "an attributed identity is required for this artifact",
        ),
        Err(HostArtifactError::Artifact(BinaryArtifactError::InvalidArtifact(_))) => error(
            StatusCode::INTERNAL_SERVER_ERROR,
            "invalid hosted artifact policy or body",
        ),
        Err(HostArtifactError::Artifact(BinaryArtifactError::Refused(reason))) => {
            error(StatusCode::CONFLICT, reason)
        }
    }
}

/// Web wrapper: public artifacts remain anonymously reachable; authenticated
/// artifacts receive the existing attributed cookie/query identity or refuse.
async fn get_web_artifact(
    State(catalog): State<Arc<CatalogState>>,
    Path((key, id, name)): Path<(String, String, String)>,
    Query(query): Query<WebQuery>,
    request: Request<Body>,
) -> Response {
    let user = web_user(request.headers(), &query);
    let viewer = (user != "anon").then(|| web_identity(&user));
    export_artifact(&catalog, key, id, name, viewer)
}

/// Read a canonical bundle request without ever formatting or logging its body.
/// Cheap header gates run before body collection; `to_bytes` enforces the same
/// hard cap even when `Content-Length` is missing or dishonest.
async fn read_bundle(
    request: Request<Body>,
    descriptor: &BinaryOperationDescriptor,
) -> Result<Vec<u8>, Response> {
    let content_type = request
        .headers()
        .get(header::CONTENT_TYPE)
        .and_then(|value| value.to_str().ok())
        .unwrap_or("");
    let expected = &descriptor.input_media_type;
    if !content_type.eq_ignore_ascii_case(&expected) {
        return Err(error(
            StatusCode::UNSUPPORTED_MEDIA_TYPE,
            format!("content-type must be {expected}"),
        ));
    }
    if let Some(length) = request.headers().get(header::CONTENT_LENGTH) {
        let length = length
            .to_str()
            .ok()
            .and_then(|value| value.parse::<u64>().ok())
            .ok_or_else(|| error(StatusCode::BAD_REQUEST, "invalid content-length"))?;
        if length > descriptor.max_input_bytes as u64 {
            return Err(error(
                StatusCode::PAYLOAD_TOO_LARGE,
                "operation input exceeds the hosted operation limit",
            ));
        }
    }
    let bytes = to_bytes(request.into_body(), descriptor.max_input_bytes)
        .await
        .map_err(|_| {
            error(
                StatusCode::PAYLOAD_TOO_LARGE,
                "operation input exceeds the hosted operation limit",
            )
        })?;
    Ok(bytes.to_vec())
}

/// The single upload implementation consumed by all surface authentication
/// wrappers. `actor` must already be derived/verified by that surface.
pub(crate) async fn execute_upload(
    catalog: Arc<CatalogState>,
    key: String,
    id: String,
    name: String,
    actor: DreggIdentity,
    request: Request<Body>,
) -> Response {
    // Resolve transport policy from the exact live session before collecting
    // any bytes.  This keeps the adapter generic: future private operations can
    // advertise different media types and limits without growing a second HTTP
    // decoder or weakening the host-selected policy.
    let sid = SessionId::new(id);
    let descriptor = {
        let routed_key = key.clone();
        let routed_sid = sid.clone();
        let routed_name = name.clone();
        let viewer = actor.clone();
        let operations = catalog.run_offering(&key, &viewer, move |host| {
            host.binary_operations(&routed_key, &routed_sid)
        });
        match operations {
            Ok(operations) => match operations
                .into_iter()
                .find(|descriptor| descriptor.name == routed_name)
            {
                Some(descriptor) => descriptor,
                None => return error(StatusCode::NOT_FOUND, "unknown hosted operation"),
            },
            Err(HostOperationError::UnknownOffering(_)) => {
                return error(StatusCode::NOT_FOUND, "unknown offering");
            }
            Err(HostOperationError::UnknownSession { .. }) => {
                return error(StatusCode::NOT_FOUND, "unknown live session");
            }
            Err(HostOperationError::Operation(_)) => {
                return error(
                    StatusCode::INTERNAL_SERVER_ERROR,
                    "unexpected discovery error",
                );
            }
        }
    };
    let payload = match read_bundle(request, &descriptor).await {
        Ok(payload) => payload,
        Err(response) => return response,
    };
    let result = {
        let routed_key = key.clone();
        let routed_sid = sid.clone();
        let routed_name = name.clone();
        let routed_actor = actor.clone();
        catalog.run_offering(&key, &actor, move |host| {
            host.invoke_binary_operation(
                &routed_key,
                &routed_sid,
                &routed_name,
                &payload,
                routed_actor,
            )
        })
    };
    match result {
        Ok(receipt) => Json(OperationAppliedWire {
            status: "applied",
            operation: receipt.operation,
            receipt_id: hex32(&receipt.receipt_id),
            public_fields: receipt.public_fields.into_iter().collect(),
        })
        .into_response(),
        Err(HostOperationError::UnknownOffering(_)) => {
            error(StatusCode::NOT_FOUND, "unknown offering")
        }
        Err(HostOperationError::UnknownSession { .. }) => {
            error(StatusCode::NOT_FOUND, "unknown live session")
        }
        Err(HostOperationError::Operation(BinaryOperationError::UnknownOperation(_))) => {
            error(StatusCode::NOT_FOUND, "unknown hosted operation")
        }
        Err(HostOperationError::Operation(BinaryOperationError::Malformed(reason))) => {
            error(StatusCode::BAD_REQUEST, reason)
        }
        Err(HostOperationError::Operation(BinaryOperationError::Refused(reason))) => {
            error(StatusCode::CONFLICT, reason)
        }
    }
}

/// Browser-cookie wrapper. The existing web catalog's identity is explicitly
/// asserted rather than cryptographic; anonymous uploads are refused. Telegram
/// and Discord call [`execute_upload`] only after their stronger native gates.
async fn post_web_upload(
    State(catalog): State<Arc<CatalogState>>,
    Path((key, id, name)): Path<(String, String, String)>,
    Query(query): Query<WebQuery>,
    request: Request<Body>,
) -> Response {
    let user = web_user(request.headers(), &query);
    if user == "anon" {
        return error(
            StatusCode::UNAUTHORIZED,
            "an attributed web identity is required",
        );
    }
    execute_upload(catalog, key, id, name, web_identity(&user), request).await
}

/// Public web routes. Telegram and Discord mount their own authenticated path
/// prefixes but reuse [`get_descriptor`] and [`execute_upload`].
pub fn router(catalog: Arc<CatalogState>) -> Router {
    let router = Router::new()
        .route(
            "/offerings/{key}/session/{id}/operations",
            get(get_web_session_operations),
        )
        .route(
            "/offerings/{key}/session/{id}/operations/{name}",
            post(post_web_upload),
        )
        .route(
            "/offerings/{key}/session/{id}/artifacts",
            get(get_web_session_artifacts),
        )
        .route(
            "/offerings/{key}/session/{id}/artifacts/{name}",
            get(get_web_artifact),
        );
    #[cfg(feature = "fhegg-settlement")]
    let router = router.route("/operations/{name}", get(get_descriptor));
    router.with_state(catalog)
}
