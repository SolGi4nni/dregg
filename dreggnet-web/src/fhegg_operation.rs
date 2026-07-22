//! Hosted binary operations shared by web, Telegram, and Discord.
//!
//! There is one decoder and mutator: the `dreggnet-market` binary operation
//! installed in the live `OfferingHost`.  This module supplies transport policy
//! (content type and bounded body), discovery JSON, and status mapping. Platform
//! wrappers establish actor attribution at their stated grade and call
//! [`execute_upload`]; none of them parses or interprets the bundle. The web
//! cookie is asserted, while Telegram and Discord verify their native envelopes
//! before calling the shared mutator.

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
use dreggnet_catalog::{
    GameAffordance, GameArtifact, GameAudience, GameCommand, GameResult, GameSessionBinding,
    PublicGameAttribution, PublicGameReceipt, PublicGameReceiptResult,
    execute_bound_asserted_game_command, game_kind, inspect_bound_game_session,
    project_public_game_receipt,
};
#[cfg(feature = "fhegg-settlement")]
use dreggnet_market::fhegg_transport::{FHEGG_SETTLEMENT_OPERATION, FheggSettlementOperation};
use dreggnet_offerings::{
    Attribution, BinaryArtifactDescriptor, BinaryArtifactError, BinaryOperationDescriptor,
    BinaryOperationError, DreggIdentity, HostArtifactError, HostError, HostOperationError,
    SessionId,
};
use serde::{Deserialize, Serialize};

use crate::{CatalogGameError, CatalogState, WebQuery, web_identity, web_user};

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
    #[serde(skip_serializing_if = "Option::is_none")]
    game_authority: Option<GameResourceAuthorityWire>,
}

impl From<BinaryArtifactDescriptor> for ArtifactDescriptorWire {
    fn from(value: BinaryArtifactDescriptor) -> Self {
        let title = crate::game_session::public_operation_title(&value.name).to_string();
        Self {
            name: value.name,
            title,
            media_type: value.media_type,
            max_bytes: value.max_bytes,
            disclosure: value.disclosure,
            visibility: value.visibility.as_str(),
            download_path_suffix: ARTIFACT_PATH_SUFFIX,
            cache_policy: "no-store",
            integrity: "BLAKE3 body digest in ETag and X-Dregg-Artifact-Digest",
            game_authority: None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
struct GameResourceAuthorityWire {
    host_incarnation_hex: String,
    session_generation: u64,
    observed_head_hex: String,
    token_hex: String,
    query: String,
}

impl ArtifactDescriptorWire {
    fn from_game(artifact: GameArtifact, catalog: &CatalogState) -> Result<Self, CatalogGameError> {
        let GameArtifact {
            reference,
            descriptor,
        } = artifact;
        let GameSessionBinding::Bound {
            host_incarnation,
            session_generation,
        } = reference.session.binding()
        else {
            return Err(CatalogGameError::Spine(
                dreggnet_catalog::GameSpineError::BindingContextRequired(reference.session.clone()),
            ));
        };
        let token = catalog.game_resource_token(
            b"artifact-export",
            &reference.session,
            &reference.observed_head,
            &reference.artifact,
        )?;
        let host_incarnation_hex = hex32(host_incarnation.as_bytes());
        let observed_head_hex = hex_bytes(&reference.observed_head);
        let token_hex = hex32(&token);
        let query = format!(
            "game_host_incarnation={host_incarnation_hex}&game_session_generation={session_generation}&game_observed_head={observed_head_hex}&game_resource_token={token_hex}"
        );
        let mut wire = Self::from(descriptor);
        wire.game_authority = Some(GameResourceAuthorityWire {
            host_incarnation_hex,
            session_generation: *session_generation,
            observed_head_hex,
            token_hex,
            query,
        });
        Ok(wire)
    }
}

#[derive(Debug, Clone, Default, Deserialize)]
pub(crate) struct GameResourceAuthorityQuery {
    #[serde(default)]
    pub game_host_incarnation: Option<String>,
    #[serde(default)]
    pub game_session_generation: Option<u64>,
    #[serde(default)]
    pub game_observed_head: Option<String>,
    #[serde(default)]
    pub game_resource_token: Option<String>,
}

impl GameResourceAuthorityQuery {
    fn into_complete(self) -> Result<Option<(String, u64, String, String)>, &'static str> {
        match (
            self.game_host_incarnation,
            self.game_session_generation,
            self.game_observed_head,
            self.game_resource_token,
        ) {
            (None, None, None, None) => Ok(None),
            (Some(incarnation), Some(generation), Some(head), Some(token)) => {
                Ok(Some((incarnation, generation, head, token)))
            }
            _ => Err("game artifact authority query is incomplete"),
        }
    }
}

#[derive(Debug, Clone, Default, Deserialize)]
struct WebArtifactQuery {
    #[serde(default)]
    user: Option<String>,
    #[serde(flatten)]
    authority: GameResourceAuthorityQuery,
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
        let title = crate::game_session::public_operation_title(&value.name).to_string();
        Self {
            name: value.name,
            title,
            input_media_type: value.input_media_type,
            max_input_bytes: value.max_input_bytes,
            disclosure: value.disclosure,
            upload_path_suffix: UPLOAD_PATH_SUFFIX,
            authentication: "surface-attributed actor; web labels are asserted, while native adapters verify their own envelopes; exact live offering/session path",
            replay_scope: "durable hosts journal only offering-selected safe replay material; otherwise the operation is refused before mutation",
            durability: "public receipt plus policy-approved replay material restore in timeline order; arbitrary upload bytes are never inferred safe",
        }
    }
}

#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct PublicGameReceiptWire {
    status: &'static str,
    game_family: &'static str,
    session_route_id: String,
    receipt_id: String,
    publication_id: String,
    attribution: &'static str,
    result: PublicGameResultWire,
}

#[derive(Debug, Serialize)]
#[serde(tag = "kind", rename_all = "kebab-case")]
enum PublicGameResultWire {
    Turn { ended: bool },
    Operation { fields: Vec<PublicGameFieldWire> },
}

#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct PublicGameFieldWire {
    name: &'static str,
    value: String,
}

impl From<PublicGameReceipt> for PublicGameReceiptWire {
    fn from(receipt: PublicGameReceipt) -> Self {
        let result = match receipt.result {
            PublicGameReceiptResult::Turn { ended } => PublicGameResultWire::Turn { ended },
            PublicGameReceiptResult::Operation { fields } => PublicGameResultWire::Operation {
                fields: fields
                    .into_iter()
                    .map(|field| PublicGameFieldWire {
                        name: field.field.as_str(),
                        value: field.value,
                    })
                    .collect(),
            },
        };
        Self {
            status: "applied",
            game_family: receipt.kind.as_str(),
            session_route_id: hex32(&receipt.session_route_id),
            receipt_id: hex32(&receipt.receipt_id),
            publication_id: hex32(&receipt.publication_id),
            attribution: match receipt.attribution {
                PublicGameAttribution::Signed => "signed",
                PublicGameAttribution::Asserted => "asserted",
            },
            result,
        }
    }
}

#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct LegacyOperationAppliedWire {
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

enum HostedOperationResult {
    Game(GameResult),
    Legacy(dreggnet_offerings::BinaryOperationReceipt),
}

enum HostedArtifactDescriptor {
    Game(GameArtifact),
    Legacy(BinaryArtifactDescriptor),
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

fn committed_publication_error(reason: impl Into<String>) -> Response {
    (
        StatusCode::INTERNAL_SERVER_ERROR,
        Json(OperationErrorWire {
            status: "committed",
            error: format!(
                "{}; the operation committed, so do not retry",
                reason.into()
            ),
        }),
    )
        .into_response()
}

fn hex32(bytes: &[u8; 32]) -> String {
    hex_bytes(bytes)
}

fn hex_bytes(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        use std::fmt::Write as _;
        let _ = write!(out, "{byte:02x}");
    }
    out
}

fn ensure_live_session(
    catalog: &CatalogState,
    key: &str,
    sid: &SessionId,
    viewer: &DreggIdentity,
) -> Result<(), Response> {
    if game_kind(key).is_none() {
        return Ok(());
    }
    catalog
        .ensure_open_and_bind(
            key,
            sid,
            viewer,
            Some(Attribution::Asserted {
                label: viewer.0.clone(),
            }),
        )
        .map(|_| ())
        .map_err(|cause| {
            let message = cause.to_string();
            match cause {
                CatalogGameError::Host(HostError::UnknownOffering(_)) => {
                    error(StatusCode::NOT_FOUND, "unknown offering")
                }
                CatalogGameError::Host(HostError::Policy(reason)) => {
                    error(StatusCode::TOO_MANY_REQUESTS, reason.to_string())
                }
                CatalogGameError::Host(HostError::ResumeFailed { .. }) => {
                    error(StatusCode::CONFLICT, message)
                }
                CatalogGameError::Host(_) => error(StatusCode::INTERNAL_SERVER_ERROR, message),
                CatalogGameError::Epoch(_)
                | CatalogGameError::Spine(_)
                | CatalogGameError::Poisoned => error(StatusCode::CONFLICT, message),
            }
        })
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
    if let Err(response) = ensure_live_session(catalog, &key, &sid, &viewer) {
        return response;
    }
    let result = if game_kind(&key).is_some() {
        let inspection_viewer = viewer.clone();
        catalog
            .run_current_bound_game(
                &key,
                &sid,
                &viewer,
                move |host, incarnation, generation, session| {
                    inspect_bound_game_session(
                        host,
                        incarnation,
                        generation,
                        session,
                        &GameAudience::AssertedPrivate(inspection_viewer),
                    )
                    .map(|view| {
                        view.affordances
                            .into_iter()
                            .filter_map(|affordance| match affordance {
                                GameAffordance::Operation { descriptor, .. } => Some(descriptor),
                                GameAffordance::Turn { .. } => None,
                            })
                            .collect::<Vec<_>>()
                    })
                    .map_err(|error| {
                        HostOperationError::Operation(BinaryOperationError::Refused(
                            error.to_string(),
                        ))
                    })
                },
            )
            .map_err(|error| {
                HostOperationError::Operation(BinaryOperationError::Refused(error.to_string()))
            })
            .and_then(|result| result)
    } else {
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
    if let Err(response) = ensure_live_session(catalog, &key, &sid, &viewer) {
        return response;
    }
    let result = if game_kind(&key).is_some() {
        let inspection_viewer = viewer.clone();
        catalog
            .run_current_bound_game(
                &key,
                &sid,
                &viewer,
                move |host, incarnation, generation, session| {
                    inspect_bound_game_session(
                        host,
                        incarnation,
                        generation,
                        session,
                        &GameAudience::AssertedPrivate(inspection_viewer),
                    )
                    .map(|view| {
                        view.artifacts
                            .into_iter()
                            .map(HostedArtifactDescriptor::Game)
                            .collect::<Vec<_>>()
                    })
                    .map_err(|error| {
                        HostArtifactError::Artifact(BinaryArtifactError::Refused(error.to_string()))
                    })
                },
            )
            .map_err(|error| {
                HostArtifactError::Artifact(BinaryArtifactError::Refused(error.to_string()))
            })
            .and_then(|result| result)
    } else {
        let routed_key = key.clone();
        let routed_sid = sid.clone();
        catalog.run_offering(&key, &viewer, move |host| {
            host.binary_artifacts(&routed_key, &routed_sid)
                .map(|artifacts| {
                    artifacts
                        .into_iter()
                        .map(HostedArtifactDescriptor::Legacy)
                        .collect::<Vec<_>>()
                })
        })
    };
    match result {
        Ok(descriptors) => {
            let wires = descriptors
                .into_iter()
                .map(|descriptor| match descriptor {
                    HostedArtifactDescriptor::Game(artifact) => {
                        ArtifactDescriptorWire::from_game(artifact, catalog)
                    }
                    HostedArtifactDescriptor::Legacy(descriptor) => {
                        Ok(ArtifactDescriptorWire::from(descriptor))
                    }
                })
                .collect::<Result<Vec<_>, _>>();
            match wires {
                Ok(wires) => Json(wires).into_response(),
                Err(cause) => error(StatusCode::CONFLICT, cause.to_string()),
            }
        }
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
    authority: GameResourceAuthorityQuery,
) -> Response {
    let sid = SessionId::new(id);
    let routing_viewer = viewer
        .clone()
        .unwrap_or_else(|| DreggIdentity("anonymous-artifact-reader".to_string()));
    let result = if game_kind(&key).is_some() {
        let (host_incarnation, session_generation, observed_head, token) =
            match authority.into_complete() {
                Ok(Some(authority)) => authority,
                Ok(None) => {
                    return error(
                        StatusCode::CONFLICT,
                        "game artifact URL requires its presented epoch/head authority query",
                    );
                }
                Err(reason) => return error(StatusCode::BAD_REQUEST, reason),
            };
        let (presented, observed_head) = match catalog.presented_game_resource(
            b"artifact-export",
            &key,
            &sid,
            &name,
            &host_incarnation,
            session_generation,
            &observed_head,
            &token,
        ) {
            Ok(authority) => authority,
            Err(cause) => return error(StatusCode::CONFLICT, cause.to_string()),
        };
        let routed_name = name.clone();
        let routed_viewer = viewer.clone();
        let audience = routed_viewer
            .clone()
            .map(GameAudience::AssertedPrivate)
            .unwrap_or(GameAudience::Shared);
        catalog
            .run_presented_bound_game(
                presented,
                &routing_viewer,
                Attribution::Asserted {
                    label: routing_viewer.0.clone(),
                },
                move |host, incarnation, generation, session| {
                    let view = inspect_bound_game_session(
                        host,
                        incarnation,
                        generation,
                        session,
                        &audience,
                    )
                    .map_err(|error| {
                        HostArtifactError::Artifact(BinaryArtifactError::Refused(error.to_string()))
                    })?;
                    if !view.artifacts.iter().any(|artifact| {
                        artifact.reference.session == view.session
                            && artifact.reference.artifact == routed_name
                            && artifact.reference.observed_head == observed_head
                            && view.surface_commitment == observed_head
                    }) {
                        return Err(HostArtifactError::Artifact(
                            BinaryArtifactError::UnknownArtifact(routed_name),
                        ));
                    }
                    host.export_binary_artifact(
                        view.session.offering(),
                        view.session.session_id(),
                        &routed_name,
                        routed_viewer.as_ref(),
                    )
                },
            )
            .map_err(|error| {
                HostArtifactError::Artifact(BinaryArtifactError::Refused(error.to_string()))
            })
            .and_then(|result| result)
    } else {
        if let Err(reason) = authority.into_complete() {
            return error(StatusCode::BAD_REQUEST, reason);
        }
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

/// Web wrapper: public artifacts remain anonymously reachable; identity-scoped
/// artifacts receive the existing asserted cookie/query actor or refuse.
async fn get_web_artifact(
    State(catalog): State<Arc<CatalogState>>,
    Path((key, id, name)): Path<(String, String, String)>,
    Query(query): Query<WebArtifactQuery>,
    request: Request<Body>,
) -> Response {
    let user = web_user(
        request.headers(),
        &WebQuery {
            user: query.user.clone(),
        },
    );
    let viewer = (user != "anon").then(|| web_identity(&user));
    export_artifact(&catalog, key, id, name, viewer, query.authority)
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
    let declared_length = if let Some(length) = request.headers().get(header::CONTENT_LENGTH) {
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
        Some(length)
    } else {
        None
    };
    let bytes = to_bytes(request.into_body(), descriptor.max_input_bytes)
        .await
        .map_err(|_| {
            error(
                StatusCode::PAYLOAD_TOO_LARGE,
                "operation input exceeds the hosted operation limit",
            )
        })?;
    if let Some(declared_length) = declared_length
        && declared_length != bytes.len() as u64
    {
        return Err(error(
            StatusCode::BAD_REQUEST,
            format!(
                "operation input changed size during upload ({declared_length} declared, {} received)",
                bytes.len()
            ),
        ));
    }
    Ok(bytes.to_vec())
}

/// The single upload implementation consumed by all surface-attribution
/// wrappers. `actor` must already be selected according to that surface's
/// documented grade; this function does not upgrade asserted web labels into
/// authenticated principals.
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
    if let Err(response) = ensure_live_session(&catalog, &key, &sid, &actor) {
        return response;
    }
    let inspected = if game_kind(&key).is_some() {
        let inspection_viewer = actor.clone();
        catalog
            .run_current_bound_game(
                &key,
                &sid,
                &actor,
                move |host, incarnation, generation, session| {
                    inspect_bound_game_session(
                        host,
                        incarnation,
                        generation,
                        session,
                        &GameAudience::AssertedPrivate(inspection_viewer),
                    )
                    .map(|view| {
                        view.affordances
                            .into_iter()
                            .filter_map(|affordance| match affordance {
                                GameAffordance::Operation {
                                    reference,
                                    descriptor,
                                } => Some((descriptor, Some(reference))),
                                GameAffordance::Turn { .. } => None,
                            })
                            .collect::<Vec<_>>()
                    })
                    .map_err(|error| {
                        HostOperationError::Operation(BinaryOperationError::Refused(
                            error.to_string(),
                        ))
                    })
                },
            )
            .map_err(|error| {
                HostOperationError::Operation(BinaryOperationError::Refused(error.to_string()))
            })
            .and_then(|result| result)
    } else {
        let routed_key = key.clone();
        let routed_sid = sid.clone();
        catalog.run_offering(&key, &actor, move |host| {
            host.binary_operations(&routed_key, &routed_sid)
                .map(|operations| {
                    operations
                        .into_iter()
                        .map(|descriptor| (descriptor, None))
                        .collect()
                })
        })
    };
    let (descriptor, game_operation) = match inspected {
        Ok(operations) => match operations
            .into_iter()
            .find(|(descriptor, _)| descriptor.name == name)
        {
            Some(pair) => pair,
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
    };
    let payload = match read_bundle(request, &descriptor).await {
        Ok(payload) => payload,
        Err(response) => return response,
    };
    let result = if let Some(reference) = game_operation {
        let presented = reference.session.clone();
        let routed_actor = actor.clone();
        catalog
            .run_presented_bound_game(
                presented,
                &actor,
                Attribution::Asserted {
                    label: actor.0.clone(),
                },
                move |host, incarnation, generation, session| {
                    execute_bound_asserted_game_command(
                        host,
                        incarnation,
                        generation,
                        &session,
                        GameCommand::Operation { reference, payload },
                        routed_actor,
                    )
                    .map(HostedOperationResult::Game)
                    .map_err(|error| {
                        HostOperationError::Operation(BinaryOperationError::Refused(
                            error.to_string(),
                        ))
                    })
                },
            )
            .map_err(|error| {
                HostOperationError::Operation(BinaryOperationError::Refused(error.to_string()))
            })
            .and_then(|result| result)
    } else {
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
            .map(HostedOperationResult::Legacy)
        })
    };
    match result {
        Ok(HostedOperationResult::Game(GameResult::Landed(receipt))) => {
            match project_public_game_receipt(&receipt) {
                Ok(publication) => Json(PublicGameReceiptWire::from(publication)).into_response(),
                Err(projection_error) => committed_publication_error(format!(
                    "public game receipt projection refused: {projection_error}"
                )),
            }
        }
        Ok(HostedOperationResult::Game(GameResult::Refused { reason, .. })) => {
            error(StatusCode::CONFLICT, reason)
        }
        Ok(HostedOperationResult::Legacy(receipt)) => Json(LegacyOperationAppliedWire {
            status: "applied",
            operation: receipt.operation,
            receipt_id: hex32(&receipt.receipt_id),
            public_fields: crate::game_session::public_operation_fields(receipt.public_fields),
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

/// Browser-cookie wrapper. The existing web catalog's actor label is explicitly
/// asserted rather than authenticated; requests with no attributed label are
/// refused. Telegram and Discord call [`execute_upload`] only after their
/// stronger native gates.
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
