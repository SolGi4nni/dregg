//! Path of Angels Galley: audited public projection and exact turn preparation.
//!
//! There is deliberately no Rust Galley reducer here. Reads come from
//! `dregg-persist`'s sealed active-content + complete V2 replay audit and are
//! judged by native Lean. Writes arrive through the ordinary hybrid
//! `SignedTurn` ingress and are recognized here only after node PQ admission;
//! the finalizer then invokes persistence's single atomic Galley apex.

use axum::extract::{DefaultBodyLimit, State};
use axum::http::{HeaderMap, StatusCode};
use axum::response::{IntoResponse, Response};
use axum::routing::{get, post};
use axum::{Json, Router};
use base64::Engine as _;
use serde::{Deserialize, Serialize};
use sha2::{Digest as _, Sha256};

use crate::state::NodeState;
use dregg_turn::poa_galley_carrier::{
    GalleyEventRoute, GalleyPlayerCommandV1, classify_galley_event,
    command_from_exact_galley_signed_turn, galley_player_cell, galley_player_command_turn,
};
use dregg_turn::{Effect, SignedTurn};

pub const GALLEY_API_PATH: &str = "/api/poa/galley/v1";
pub const SESSION_FORMAT: &str = "POA-GALLEY-SESSION-V1";
pub const STATUS_FORMAT: &str = "POA-GALLEY-STATUS-V1";
pub const COMMAND_PREPARE_FORMAT: &str = "POA-GALLEY-COMMAND-PREPARE-V1";
pub const UNSIGNED_TURN_FORMAT: &str = "POA-GALLEY-UNSIGNED-TURN-V1";
pub const DREGG_ACTOR_HEADER: &str = "x-dregg-actor";

const MAX_COMMAND_BODY_BYTES: usize = 16 * 1024;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FinalizedGalleyRoute {
    Ordinary,
    PublicPerform,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum FinalizedGalleyRouteError {
    MalformedReserved(String),
    Multiple,
    NonCanonicalCarrier(String),
    UnsupportedCommand,
}

impl FinalizedGalleyRouteError {
    pub(crate) const fn code(&self) -> &'static str {
        match self {
            Self::MalformedReserved(_) => "poa-galley-reserved-marker-malformed",
            Self::Multiple => "poa-galley-multiple-effects",
            Self::NonCanonicalCarrier(_) => "poa-galley-noncanonical-carrier",
            Self::UnsupportedCommand => "poa-galley-command-not-activated",
        }
    }
}

impl std::fmt::Display for FinalizedGalleyRouteError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MalformedReserved(error) => write!(formatter, "{error}"),
            Self::Multiple => formatter.write_str("multiple reserved Galley effects"),
            Self::NonCanonicalCarrier(error) => write!(formatter, "{error}"),
            Self::UnsupportedCommand => {
                formatter.write_str("this exact Galley command has no finalized writer")
            }
        }
    }
}

/// Classify the complete signed carrier after hybrid actor validation and
/// before executor mutation. Once a reserved marker appears it cannot fall
/// through as an ordinary `EmitEvent`, even when nested or malformed.
pub(crate) fn classify_finalized_galley(
    signed: &SignedTurn,
) -> Result<FinalizedGalleyRoute, FinalizedGalleyRouteError> {
    fn collect(
        effect: &Effect,
        found: &mut Option<GalleyPlayerCommandV1>,
    ) -> Result<(), FinalizedGalleyRouteError> {
        match effect {
            Effect::EmitEvent { event, .. } => match classify_galley_event(event)
                .map_err(|error| FinalizedGalleyRouteError::MalformedReserved(error.to_string()))?
            {
                GalleyEventRoute::Ordinary => {}
                GalleyEventRoute::PlayerCommand(command) => {
                    if found.replace(command).is_some() {
                        return Err(FinalizedGalleyRouteError::Multiple);
                    }
                }
            },
            Effect::ExerciseViaCapability { inner_effects, .. } => {
                for inner in inner_effects {
                    collect(inner, found)?;
                }
            }
            // Pipeline resolution removes this wrapper and promotes the
            // enclosed action to a new call-forest root. Scan the same nested
            // effects now, before executor mutation, so a reserved Galley
            // carrier cannot become visible only after classification.
            Effect::PipelinedSend { action, .. } => {
                for inner in &action.effects {
                    collect(inner, found)?;
                }
            }
            _ => {}
        }
        Ok(())
    }

    let mut found = None;
    for effect in signed.turn.call_forest.total_effects() {
        collect(effect, &mut found)?;
    }
    let Some(scanned) = found else {
        return Ok(FinalizedGalleyRoute::Ordinary);
    };
    let exact = command_from_exact_galley_signed_turn(signed)
        .map_err(|error| FinalizedGalleyRouteError::NonCanonicalCarrier(error.to_string()))?;
    if exact != scanned {
        return Err(FinalizedGalleyRouteError::NonCanonicalCarrier(
            "Galley scan and exact signed carrier disagree".into(),
        ));
    }
    match exact {
        GalleyPlayerCommandV1::Perform { .. } => Ok(FinalizedGalleyRoute::PublicPerform),
        GalleyPlayerCommandV1::PublicVote { .. }
        | GalleyPlayerCommandV1::VisitCommons { .. }
        | GalleyPlayerCommandV1::HolderSponsorship { .. } => {
            Err(FinalizedGalleyRouteError::UnsupportedCommand)
        }
    }
}

#[derive(Debug)]
enum GalleyApiError {
    ActorRequired,
    MalformedActor,
    MalformedRequest(&'static str),
    StaleAction,
    ActorCellMismatch,
    ActorPqIdentityMissing,
    Backend(String),
}

impl GalleyApiError {
    const fn status(&self) -> StatusCode {
        match self {
            Self::ActorRequired => StatusCode::UNAUTHORIZED,
            Self::MalformedActor | Self::MalformedRequest(_) => StatusCode::BAD_REQUEST,
            Self::StaleAction | Self::ActorCellMismatch | Self::ActorPqIdentityMissing => {
                StatusCode::CONFLICT
            }
            Self::Backend(_) => StatusCode::SERVICE_UNAVAILABLE,
        }
    }

    const fn code(&self) -> &'static str {
        match self {
            Self::ActorRequired => "poa-galley-actor-required",
            Self::MalformedActor => "poa-galley-actor-malformed",
            Self::MalformedRequest(_) => "poa-galley-command-malformed",
            Self::StaleAction => "poa-galley-action-stale",
            Self::ActorCellMismatch => "poa-galley-actor-cell-mismatch",
            Self::ActorPqIdentityMissing => "poa-galley-actor-pq-identity-missing",
            Self::Backend(_) => "poa-galley-observation-unavailable",
        }
    }
}

impl std::fmt::Display for GalleyApiError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ActorRequired => formatter.write_str("X-Dregg-Actor is required"),
            Self::MalformedActor => formatter
                .write_str("X-Dregg-Actor must occur once as 64 lowercase hexadecimal digits"),
            Self::MalformedRequest(message) => formatter.write_str(message),
            Self::StaleAction => formatter.write_str("the Galley action is absent or expired"),
            Self::ActorCellMismatch => {
                formatter.write_str("the derived Galley player cell is bound to another public key")
            }
            Self::ActorPqIdentityMissing => formatter
                .write_str("the existing Galley player cell has no enrolled ML-DSA identity"),
            Self::Backend(message) => formatter.write_str(message),
        }
    }
}

#[derive(Serialize)]
struct ErrorBody<'a> {
    code: &'static str,
    message: &'a str,
}

impl IntoResponse for GalleyApiError {
    fn into_response(self) -> Response {
        let status = self.status();
        let message = self.to_string();
        (
            status,
            Json(ErrorBody {
                code: self.code(),
                message: &message,
            }),
        )
            .into_response()
    }
}

fn actor_from_headers(headers: &HeaderMap) -> Result<[u8; 32], GalleyApiError> {
    let mut values = headers.get_all(DREGG_ACTOR_HEADER).iter();
    let value = values.next().ok_or(GalleyApiError::ActorRequired)?;
    if values.next().is_some() {
        return Err(GalleyApiError::MalformedActor);
    }
    let value = value.to_str().map_err(|_| GalleyApiError::MalformedActor)?;
    decode_hex32(value).ok_or(GalleyApiError::MalformedActor)
}

fn decode_hex32(value: &str) -> Option<[u8; 32]> {
    if value.len() != 64
        || !value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return None;
    }
    let mut output = [0u8; 32];
    for (index, pair) in value.as_bytes().chunks_exact(2).enumerate() {
        output[index] = (hex_nibble(pair[0])? << 4) | hex_nibble(pair[1])?;
    }
    (output != [0; 32]).then_some(output)
}

const fn hex_nibble(value: u8) -> Option<u8> {
    match value {
        b'0'..=b'9' => Some(value - b'0'),
        b'a'..=b'f' => Some(value - b'a' + 10),
        _ => None,
    }
}

fn hex(value: impl AsRef<[u8]>) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let value = value.as_ref();
    let mut output = String::with_capacity(value.len() * 2);
    for byte in value {
        output.push(DIGITS[(byte >> 4) as usize] as char);
        output.push(DIGITS[(byte & 0x0f) as usize] as char);
    }
    output
}

#[derive(Serialize)]
struct GalleyActionResponse {
    kind: &'static str,
    action_token: String,
    expires_after_sequence: u64,
}

#[derive(Serialize)]
struct ReplayResponse {
    audited: bool,
    event_count: usize,
    total_event_count: u64,
    from_sequence: u64,
    through_sequence: u64,
    head_digest: String,
}

#[derive(Serialize)]
struct GalleyCurrentResponse {
    federation_id: String,
    daily_id: String,
    aggregate_id: String,
    schema_version: u64,
    sequence: u64,
    semantic_head: String,
    projection_digest: String,
    projection: serde_json::Value,
    actions: Vec<GalleyActionResponse>,
    replay: ReplayResponse,
}

#[derive(Serialize)]
struct GalleySessionResponse {
    format: &'static str,
    #[serde(flatten)]
    current: GalleyCurrentResponse,
}

#[derive(Serialize)]
struct GalleyReceiptResponse {
    index: u64,
    postcard_base64: String,
    sha256: String,
}

#[derive(Serialize)]
struct GalleyEventResponse {
    sequence: u64,
    turn_hash: String,
    receipt_hash: String,
    event_digest: String,
    payload_digest: String,
    payload: serde_json::Value,
    receipt: GalleyReceiptResponse,
}

#[derive(Serialize)]
struct GalleyStatusResponse {
    format: &'static str,
    #[serde(flatten)]
    current: GalleyCurrentResponse,
    events: Vec<GalleyEventResponse>,
}

fn observation_responses(
    observed: &dregg_persist::poa_galley_authority::PoaGalleyObservationV1,
) -> Result<(GalleyCurrentResponse, Vec<GalleyEventResponse>), GalleyApiError> {
    let projection = serde_json::from_slice(observed.projection_json()).map_err(|error| {
        GalleyApiError::Backend(format!("audited projection is not JSON: {error}"))
    })?;
    let actions = observed
        .actions()
        .iter()
        .map(|action| GalleyActionResponse {
            kind: "perform",
            action_token: hex(action.token()),
            expires_after_sequence: action.expires_after_sequence(),
        })
        .collect();
    let mut events = Vec::with_capacity(observed.events().len());
    for event in observed.events() {
        let coordinate = event.coordinate();
        let postcard = event.receipt_postcard();
        let payload = serde_json::from_slice(event.payload_json()).map_err(|error| {
            GalleyApiError::Backend(format!("audited Galley payload is not JSON: {error}"))
        })?;
        events.push(GalleyEventResponse {
            sequence: event.sequence(),
            turn_hash: hex(coordinate.turn_hash()),
            receipt_hash: hex(coordinate.receipt_hash()),
            event_digest: hex(event.event_digest()),
            payload_digest: hex(event.payload_digest()),
            payload,
            receipt: GalleyReceiptResponse {
                index: event.receipt_index(),
                postcard_base64: base64::engine::general_purpose::STANDARD.encode(postcard),
                sha256: hex(Sha256::digest(postcard)),
            },
        });
    }
    let sequence = observed.sequence();
    let current = GalleyCurrentResponse {
        federation_id: hex(observed.world().federation_id()),
        daily_id: hex(observed.daily_id()),
        aggregate_id: format!("galley:{}", hex(observed.daily_id())),
        schema_version: 1,
        sequence,
        semantic_head: hex(observed.semantic_head()),
        projection_digest: hex(observed.projection_digest()),
        projection,
        actions,
        replay: ReplayResponse {
            audited: true,
            event_count: events.len(),
            total_event_count: sequence,
            from_sequence: events.first().map_or(0, |event| event.sequence),
            through_sequence: events.last().map_or(0, |event| event.sequence),
            head_digest: hex(observed.semantic_head()),
        },
    };
    Ok((current, events))
}

async fn observe(
    state: &NodeState,
    headers: &HeaderMap,
) -> Result<dregg_persist::poa_galley_authority::PoaGalleyObservationV1, GalleyApiError> {
    let actor = actor_from_headers(headers)?;
    let state = state.read().await;
    state
        .store
        .observe_active_poa_galley_v1(actor)
        .map_err(|error| GalleyApiError::Backend(error.to_string()))
}

async fn get_session(
    State(state): State<NodeState>,
    headers: HeaderMap,
) -> Result<Json<GalleySessionResponse>, GalleyApiError> {
    let observed = observe(&state, &headers).await?;
    let (current, _) = observation_responses(&observed)?;
    Ok(Json(GalleySessionResponse {
        format: SESSION_FORMAT,
        current,
    }))
}

async fn get_status(
    State(state): State<NodeState>,
    headers: HeaderMap,
) -> Result<Json<GalleyStatusResponse>, GalleyApiError> {
    let observed = observe(&state, &headers).await?;
    let (current, events) = observation_responses(&observed)?;
    Ok(Json(GalleyStatusResponse {
        format: STATUS_FORMAT,
        current,
        events,
    }))
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct GalleyCommandPrepareRequest {
    format: String,
    action_token: String,
}

#[derive(Serialize)]
struct GalleyUnsignedTurnResponse {
    format: &'static str,
    intent_id: String,
    federation_id: String,
    preparation_digest: String,
    turn_postcard_base64: String,
    expires_after_sequence: u64,
}

async fn post_command(
    State(state): State<NodeState>,
    headers: HeaderMap,
    Json(request): Json<GalleyCommandPrepareRequest>,
) -> Result<Json<GalleyUnsignedTurnResponse>, GalleyApiError> {
    if request.format != COMMAND_PREPARE_FORMAT {
        return Err(GalleyApiError::MalformedRequest(
            "unsupported Galley command preparation format",
        ));
    }
    let actor = actor_from_headers(&headers)?;
    let token = decode_hex32(&request.action_token).ok_or(GalleyApiError::MalformedRequest(
        "action_token must be 64 lowercase hexadecimal digits and nonzero",
    ))?;
    let state_guard = state.read().await;
    let observed = state_guard
        .store
        .observe_active_poa_galley_v1(actor)
        .map_err(|error| GalleyApiError::Backend(error.to_string()))?;
    let offered = observed
        .actions()
        .iter()
        .filter(|action| {
            action.token() == token && action.expires_after_sequence() == observed.sequence()
        })
        .collect::<Vec<_>>();
    if offered.len() != 1 {
        return Err(GalleyApiError::StaleAction);
    }
    let player_cell = galley_player_cell(&actor);
    let (nonce, previous_receipt_hash) = match state_guard.ledger.get(&player_cell) {
        Some(cell) => {
            if cell.public_key() != &actor {
                return Err(GalleyApiError::ActorCellMismatch);
            }
            if cell.pq_identity().is_none() {
                return Err(GalleyApiError::ActorPqIdentityMissing);
            }
            (
                cell.state.nonce(),
                state_guard.cclerk.agent_receipt_head_hash(&player_cell),
            )
        }
        None => (0, None),
    };
    let mut turn = galley_player_command_turn(
        &actor,
        nonce,
        previous_receipt_hash,
        GalleyPlayerCommandV1::Perform {
            action_token: dregg_turn::poa_galley_carrier::GalleyActionToken::from_bytes(token),
            action_content_id: observed.public_action_content_id(),
        },
    );
    // Materialize canonical call hashes before encoding the unsigned carrier;
    // the extension replaces only action authorization and re-materializes the
    // corresponding signed hashes.
    turn.call_forest.hash();
    let postcard = postcard::to_stdvec(&turn)
        .map_err(|error| GalleyApiError::Backend(format!("Turn postcard failed: {error}")))?;
    let preparation_digest: [u8; 32] = Sha256::digest(&postcard).into();
    let mut intent = blake3::Hasher::new_derive_key("dregg-poa-galley-intent-v1");
    intent.update(&observed.world().federation_id());
    intent.update(&observed.daily_id());
    intent.update(&observed.sequence().to_le_bytes());
    intent.update(&observed.semantic_head());
    intent.update(&actor);
    intent.update(&token);
    intent.update(&preparation_digest);
    Ok(Json(GalleyUnsignedTurnResponse {
        format: UNSIGNED_TURN_FORMAT,
        intent_id: hex(intent.finalize().as_bytes()),
        federation_id: hex(observed.world().federation_id()),
        preparation_digest: hex(preparation_digest),
        turn_postcard_base64: base64::engine::general_purpose::STANDARD.encode(postcard),
        expires_after_sequence: offered[0].expires_after_sequence(),
    }))
}

pub(crate) fn routes() -> Router<NodeState> {
    Router::new()
        .route(&format!("{GALLEY_API_PATH}/session"), get(get_session))
        .route(&format!("{GALLEY_API_PATH}/status"), get(get_status))
        .route(&format!("{GALLEY_API_PATH}/command"), post(post_command))
        .layer(DefaultBodyLimit::max(MAX_COMMAND_BODY_BYTES))
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_turn::poa_galley_carrier::{GalleyActionToken, galley_command_event};
    use dregg_types::{SigningKey, sign};
    use ed25519_dalek::Signer as _;

    fn assert_canonical_hex(value: &str, byte_len: usize) {
        assert_eq!(value.len(), byte_len * 2, "hex width must be canonical");
        assert!(
            value
                .bytes()
                .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte)),
            "hex must contain only lowercase hexadecimal digits: {value}",
        );
    }

    fn exact_signed(command: GalleyPlayerCommandV1) -> SignedTurn {
        let key = SigningKey::from_bytes(&[0x51; 32]);
        let signer = key.public_key();
        let mut turn = galley_player_command_turn(&signer.0, 0, None, command);
        turn.call_forest.hash();
        let signature = sign(&key, &turn.hash());
        SignedTurn {
            turn,
            signature,
            signer,
            pq_signature: Vec::new(),
            pq_signer: Vec::new(),
        }
    }

    fn live_policy_json(federation_id: [u8; 32]) -> String {
        format!(
            "{{\"deployment_id\":\"{}\",\"federation_id\":\"{}\",\"daily_id\":\"{}\",\"genesis_head\":\"{}\",\"dregg_mint\":5,\"snapshot_slot\":6,\"content_epoch\":1,\"event_id\":\"{}\",\"rules_digest\":\"{}\",\"public_activity_id\":\"{}\",\"scene_content_id\":\"{}\",\"public_action_content_id\":\"{}\",\"sponsor_action_content_id\":\"{}\",\"complete_content_id\":\"{}\",\"public_service\":3,\"sponsor_service\":2,\"service_target\":10,\"power_root\":\"{}\",\"loot_root\":\"{}\",\"canon_root\":\"{}\",\"canon_revision\":18}}",
            hex([1; 32]),
            hex(federation_id),
            hex([3; 32]),
            hex([4; 32]),
            hex([9; 32]),
            hex([10; 32]),
            hex([10; 32]),
            hex([11; 32]),
            hex([12; 32]),
            hex([13; 32]),
            hex([14; 32]),
            hex([15; 32]),
            hex([16; 32]),
            hex([17; 32]),
        )
    }

    fn live_world_bundle(federation_id: [u8; 32]) -> (dregg_persist::PoaWorldIdentityV2, Vec<u8>) {
        let policy = live_policy_json(federation_id);
        let component_digest: [u8; 32] = Sha256::digest(policy.as_bytes()).into();
        let manifest = format!(
            concat!(
                "{{\"format\":\"POA-ACTIVATED-CONTENT-MANIFEST-1\",",
                "\"scope\":{{\"federation_id\":\"{}\",\"content_session\":\"{}\",",
                "\"content_epoch\":1}},\"legacy_whole_pack_sha256\":null,",
                "\"components\":[{{\"name\":\"poa.galley-maintenance-daily.policy.v1\",",
                "\"sha256\":\"{}\",\"bytes_utf8\":{}}}]}}"
            ),
            hex(federation_id),
            hex([0x53; 32]),
            hex(component_digest),
            serde_json::to_string(&policy).expect("quoted policy"),
        )
        .into_bytes();
        let world = dregg_persist::PoaWorldIdentityV2::new(
            federation_id,
            Sha256::digest(&manifest).into(),
            [0x52; 32],
            [0x53; 32],
            1,
        )
        .expect("Galley world");
        (world, manifest)
    }

    fn install_live_world(
        store: &dregg_persist::PersistentStore,
        world: dregg_persist::PoaWorldIdentityV2,
        manifest: Vec<u8>,
    ) {
        let curator = ed25519_dalek::SigningKey::from_bytes(&[0x71; 32]);
        store
            .install_poa_world_curator_pin_v1(curator.verifying_key().to_bytes())
            .expect("curator pin");
        let statement = dregg_persist::PoaWorldActivationStatementV1::new(
            world,
            1,
            [0; 32],
            dregg_persist::PoaWorldActivationKindV1::Advance,
            None,
        )
        .expect("activation statement");
        let signature = curator.sign(&statement.signing_message().expect("activation message"));
        let envelope = dregg_persist::SignedPoaWorldActivationEnvelopeV1::new(
            statement,
            curator.verifying_key().to_bytes(),
            signature.to_bytes(),
        )
        .expect("activation envelope");
        store
            .install_poa_world_activation_v1(envelope)
            .expect("active Galley world");
        store
            .install_poa_activated_content_v1(manifest)
            .expect("activated Galley content");
    }

    #[test]
    fn actor_header_is_single_lowercase_nonzero_key() {
        assert!(
            crate::api::CORS_ALLOWED_REQUEST_HEADERS
                .split(',')
                .any(|header| header.trim().eq_ignore_ascii_case(DREGG_ACTOR_HEADER)),
            "the extension actor header must survive browser CORS preflight",
        );
        let mut headers = HeaderMap::new();
        assert!(matches!(
            actor_from_headers(&headers),
            Err(GalleyApiError::ActorRequired)
        ));
        headers.insert(DREGG_ACTOR_HEADER, "11".repeat(32).parse().unwrap());
        assert_eq!(actor_from_headers(&headers).unwrap(), [0x11; 32]);
        headers.append(DREGG_ACTOR_HEADER, "22".repeat(32).parse().unwrap());
        assert!(matches!(
            actor_from_headers(&headers),
            Err(GalleyApiError::MalformedActor)
        ));
        headers.remove(DREGG_ACTOR_HEADER);
        headers.insert(DREGG_ACTOR_HEADER, "AA".repeat(32).parse().unwrap());
        assert!(matches!(
            actor_from_headers(&headers),
            Err(GalleyApiError::MalformedActor)
        ));
    }

    #[test]
    fn hex_is_canonical_lowercase_with_exact_two_digits_per_byte() {
        let encoded = hex([0x00, 0x01, 0x0f, 0x10, 0xab, 0xcd, 0xef, 0xff]);
        assert_eq!(encoded, "00010f10abcdefff");
        assert_canonical_hex(&encoded, 8);

        let digest = hex([0xa5; 32]);
        assert_eq!(digest, "a5".repeat(32));
        assert_canonical_hex(&digest, 32);
    }

    #[test]
    fn finalized_classifier_registers_only_exact_public_perform() {
        let perform = exact_signed(GalleyPlayerCommandV1::Perform {
            action_token: GalleyActionToken::from_bytes([0xa1; 32]),
            action_content_id: [0xb2; 32],
        });
        assert_eq!(
            classify_finalized_galley(&perform),
            Ok(FinalizedGalleyRoute::PublicPerform)
        );
        let vote = exact_signed(GalleyPlayerCommandV1::PublicVote {
            action_token: GalleyActionToken::from_bytes([0xa1; 32]),
            choice: dregg_turn::poa_galley_carrier::PublicVoteChoice::Yes,
        });
        assert!(matches!(
            classify_finalized_galley(&vote),
            Err(FinalizedGalleyRouteError::UnsupportedCommand)
        ));
    }

    #[test]
    fn malformed_or_piggybacked_reserved_marker_never_falls_through() {
        let mut malformed = exact_signed(GalleyPlayerCommandV1::Perform {
            action_token: GalleyActionToken::from_bytes([0xa1; 32]),
            action_content_id: [0xb2; 32],
        });
        let Effect::EmitEvent { event, .. } =
            &mut malformed.turn.call_forest.roots[0].action.effects[0]
        else {
            panic!("fixture event")
        };
        event.data.clear();
        assert!(matches!(
            classify_finalized_galley(&malformed),
            Err(FinalizedGalleyRouteError::MalformedReserved(_))
        ));

        let mut piggyback = exact_signed(GalleyPlayerCommandV1::Perform {
            action_token: GalleyActionToken::from_bytes([0xa1; 32]),
            action_content_id: [0xb2; 32],
        });
        let extra = galley_command_event(GalleyPlayerCommandV1::Perform {
            action_token: GalleyActionToken::from_bytes([0xc3; 32]),
            action_content_id: [0xd4; 32],
        });
        piggyback.turn.call_forest.roots[0]
            .action
            .effects
            .push(Effect::EmitEvent {
                cell: piggyback.turn.agent,
                event: extra,
            });
        assert!(matches!(
            classify_finalized_galley(&piggyback),
            Err(FinalizedGalleyRouteError::Multiple)
        ));
    }

    fn pipelined_carrier(inner_actions: Vec<dregg_turn::action::Action>) -> SignedTurn {
        let mut carrier = exact_signed(GalleyPlayerCommandV1::Perform {
            action_token: GalleyActionToken::from_bytes([0xa1; 32]),
            action_content_id: [0xb2; 32],
        });
        carrier.turn.call_forest.roots[0].action.effects = inner_actions
            .into_iter()
            .enumerate()
            .map(|(index, action)| Effect::PipelinedSend {
                target: dregg_turn::eventual::EventualRef::new([0x71; 32], index as u32),
                action: Box::new(action),
            })
            .collect();
        carrier
    }

    #[test]
    fn pipelined_reserved_carriers_are_scanned_before_executor_promotion() {
        let exact = exact_signed(GalleyPlayerCommandV1::Perform {
            action_token: GalleyActionToken::from_bytes([0xa1; 32]),
            action_content_id: [0xb2; 32],
        });
        let inner = exact.turn.call_forest.roots[0].action.clone();

        let nested_valid = pipelined_carrier(vec![inner.clone()]);
        assert!(matches!(
            classify_finalized_galley(&nested_valid),
            Err(FinalizedGalleyRouteError::NonCanonicalCarrier(_))
        ));

        let mut malformed_inner = inner.clone();
        let Effect::EmitEvent { event, .. } = &mut malformed_inner.effects[0] else {
            panic!("fixture event")
        };
        event.data.clear();
        let nested_malformed = pipelined_carrier(vec![malformed_inner]);
        assert!(matches!(
            classify_finalized_galley(&nested_malformed),
            Err(FinalizedGalleyRouteError::MalformedReserved(_))
        ));

        let nested_duplicate = pipelined_carrier(vec![inner.clone(), inner]);
        assert!(matches!(
            classify_finalized_galley(&nested_duplicate),
            Err(FinalizedGalleyRouteError::Multiple)
        ));
    }

    fn assert_native_galley_runtime_available() {
        use dregg_lean_ffi::{
            poa_activated_content_ffi::poa_activated_content_runtime_available,
            poa_event_batch_ffi::{
                poa_event_batch_initial_heads_digest_available, poa_event_batch_runtime_available,
            },
            poa_galley_ffi::poa_galley_daily_available,
            poa_world_activation_ffi::poa_world_activation_available,
        };
        assert!(
            poa_world_activation_available()
                && poa_activated_content_runtime_available()
                && poa_galley_daily_available()
                && poa_event_batch_runtime_available()
                && poa_event_batch_initial_heads_digest_available(),
            "the production Galley contract test requires every linked native Lean authority",
        );
    }

    #[test]
    fn production_galley_test_cannot_silently_skip_missing_lean_authority() {
        assert_native_galley_runtime_available();
    }

    #[tokio::test(flavor = "multi_thread", worker_threads = 4)]
    async fn production_finalizer_commits_exact_galley_and_observation_replays_it() {
        assert_native_galley_runtime_available();
        let _ = rustls::crypto::ring::default_provider().install_default();
        let directory = tempfile::tempdir().expect("node directory");
        let state = crate::state::NodeState::new(directory.path(), Vec::new()).expect("node state");
        let actor_seed = *blake3::hash(b"poa-galley:production-finalizer").as_bytes();
        let actor =
            dregg_sdk::AgentCipherclerk::from_key_bytes(zeroize::Zeroizing::new(actor_seed));
        let actor_key = actor.public_key().0;
        let player_cell = galley_player_cell(&actor_key);
        let federation_id;
        {
            let mut node = state.write().await;
            node.lean_producer_enabled = false;
            let local_key = node.cclerk.public_key();
            let local_seed = node.cclerk.gossip_signing_key().to_bytes();
            let local_pq: [u8; dregg_pq::ML_DSA_PK_LEN] =
                dregg_turn::pq::MlDsaTurnKey::from_ed25519_seed(&local_seed)
                    .public_bytes()
                    .try_into()
                    .expect("local PQ key");
            node.set_federation_keys_hybrid(
                vec![local_key],
                vec![dregg_federation::frost::MlDsaPublicKey(local_pq)],
            );
            federation_id = crate::executor_setup::federation_id_for_executor(&node);
            node.ledger
                .insert_cell(
                    dregg_cell::Cell::with_hybrid_balance(
                        actor_key,
                        &actor.ml_dsa_public_bytes(),
                        *blake3::hash(b"default").as_bytes(),
                        1_000_000,
                    )
                    .expect("hybrid Galley player"),
                )
                .expect("fund Galley player");
            let (world, manifest) = live_world_bundle(federation_id);
            install_live_world(&node.store, world, manifest);
        }

        let observed = {
            let node = state.read().await;
            node.store
                .observe_active_poa_galley_v1(actor_key)
                .expect("sequence-zero view")
        };
        let action = observed.actions().first().expect("offered public action");
        let mut headers = HeaderMap::new();
        headers.insert(
            DREGG_ACTOR_HEADER,
            hex(actor_key).parse().expect("actor header"),
        );
        let Json(session) = get_session(State(state.clone()), headers.clone())
            .await
            .expect("session response");
        assert_eq!(session.format, SESSION_FORMAT);
        assert_canonical_hex(&session.current.federation_id, 32);
        assert_canonical_hex(&session.current.daily_id, 32);
        assert_canonical_hex(&session.current.semantic_head, 32);
        assert_canonical_hex(&session.current.projection_digest, 32);
        assert_canonical_hex(&session.current.replay.head_digest, 32);
        assert_canonical_hex(
            session
                .current
                .aggregate_id
                .strip_prefix("galley:")
                .expect("aggregate id prefix"),
            32,
        );
        assert!(
            session.current.actions.iter().all(|action| {
                assert_canonical_hex(&action.action_token, 32);
                true
            }),
            "every advertised action token must use canonical 32-byte hex",
        );
        let stale = post_command(
            State(state.clone()),
            headers.clone(),
            Json(GalleyCommandPrepareRequest {
                format: COMMAND_PREPARE_FORMAT.into(),
                action_token: hex([0xee; 32]),
            }),
        )
        .await;
        assert!(matches!(stale, Err(GalleyApiError::StaleAction)));
        let mut wrong_actor_headers = HeaderMap::new();
        wrong_actor_headers.insert(
            DREGG_ACTOR_HEADER,
            hex([0x44; 32]).parse().expect("wrong actor header"),
        );
        let substituted_actor = post_command(
            State(state.clone()),
            wrong_actor_headers,
            Json(GalleyCommandPrepareRequest {
                format: COMMAND_PREPARE_FORMAT.into(),
                action_token: hex(action.token()),
            }),
        )
        .await;
        assert!(matches!(
            substituted_actor,
            Err(GalleyApiError::StaleAction)
        ));
        assert_eq!(
            state
                .read()
                .await
                .store
                .commit_cursor()
                .expect("commit cursor before valid command"),
            0,
        );
        let Json(prepared) = post_command(
            State(state.clone()),
            headers.clone(),
            Json(GalleyCommandPrepareRequest {
                format: COMMAND_PREPARE_FORMAT.into(),
                action_token: hex(action.token()),
            }),
        )
        .await
        .expect("node command preparation");
        assert_canonical_hex(&prepared.intent_id, 32);
        assert_canonical_hex(&prepared.federation_id, 32);
        assert_canonical_hex(&prepared.preparation_digest, 32);
        let turn_bytes = base64::engine::general_purpose::STANDARD
            .decode(&prepared.turn_postcard_base64)
            .expect("prepared postcard base64");
        let mut turn: dregg_turn::Turn =
            postcard::from_bytes(&turn_bytes).expect("prepared canonical Turn");
        let prepared_digest: [u8; 32] = Sha256::digest(&turn_bytes).into();
        assert_eq!(hex(prepared_digest), prepared.preparation_digest);
        assert_eq!(prepared.expires_after_sequence, observed.sequence());
        let unsigned_action = turn.call_forest.roots[0].action.clone();
        turn.call_forest.roots[0].action =
            actor.sign_action_hybrid(unsigned_action, &federation_id, turn.nonce);
        turn.call_forest.roots[0].hash = [0; 32];
        turn.call_forest.forest_hash = [0; 32];
        turn.call_forest.hash();
        let signed = actor.sign_turn(&turn);
        assert_eq!(signed.turn.agent, player_cell);
        let turn_hash = signed.turn.hash();
        let bytes = postcard::to_stdvec(&signed).expect("signed Galley postcard");
        let outcome = crate::blocklace_sync::finalize_admitted_turn_for_test(
            &state,
            dregg_blocklace::finality::BlockId([0x31; 32]),
            &bytes,
        )
        .await;
        assert!(
            matches!(
                outcome,
                crate::execution_cursor::FinalizedExecutionOutcome::Committed { .. }
            ),
            "exact Galley turn must reach the production atomic apex: {outcome:?}"
        );

        let replayed = {
            let node = state.read().await;
            node.store
                .observe_active_poa_galley_v1(actor_key)
                .expect("replayed committed view")
        };
        assert_eq!(replayed.sequence(), 1);
        assert_eq!(replayed.events().len(), 1);
        assert_eq!(replayed.events()[0].coordinate().turn_hash(), turn_hash);
        assert_eq!(replayed.events()[0].receipt_index(), 0);
        assert!(!replayed.events()[0].receipt_postcard().is_empty());

        let Json(status) = get_status(State(state.clone()), headers)
            .await
            .expect("status response after finality");
        assert_eq!(status.format, STATUS_FORMAT);
        assert_canonical_hex(&status.current.federation_id, 32);
        assert_canonical_hex(&status.current.daily_id, 32);
        assert_canonical_hex(&status.current.semantic_head, 32);
        assert_canonical_hex(&status.current.projection_digest, 32);
        assert_canonical_hex(&status.current.replay.head_digest, 32);
        assert_eq!(status.events.len(), 1);
        let event = &status.events[0];
        assert_canonical_hex(&event.turn_hash, 32);
        assert_eq!(event.turn_hash, hex(turn_hash));
        assert_ne!(event.turn_hash, prepared.preparation_digest);
        assert_canonical_hex(&event.receipt_hash, 32);
        assert_canonical_hex(&event.event_digest, 32);
        assert_canonical_hex(&event.payload_digest, 32);
        assert_canonical_hex(&event.receipt.sha256, 32);
    }
}
