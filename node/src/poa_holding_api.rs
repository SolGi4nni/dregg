//! Public, rate-limited Path of Angels `$DREGG` beta admission.
//!
//! This module is transport and durability glue only. It does not reimplement
//! holding, signature, replay, or capability semantics: those remain in
//! `poa-solana-gate`, which in turn reuses Dregg's existing Solana and
//! governance primitives. The browser supplies a wallet, then an issued id and
//! signature. It never supplies balance, slot, mint, cluster, or token-account
//! bytes.

use std::collections::{BTreeMap, BTreeSet};
use std::future::Future;
use std::net::SocketAddr;
use std::pin::Pin;
use std::sync::Arc;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use axum::extract::{ConnectInfo, Path, State};
use axum::http::{HeaderMap, StatusCode};
use axum::response::{IntoResponse, Response};
use axum::routing::{get, post};
use axum::{Json, Router};
use base64::Engine as _;
use poa_solana_gate::{
    AdmissionStore, Bytes32, CapabilityIssue, CapabilityStatus, CapabilityUse, Challenge,
    ChallengeIssue, Commitment, ConsensusAdmissionCheckpoint, ConsensusCapabilityIssue,
    ConsensusHoldingCapability, ConsensusPrivilegeReservation, ConsensusReservationIssue,
    ConsensusReservationReceipt, DREGG_MINT_BASE58, Gate, GateConfig, GateError, HoldingCapability,
    RpcAccountSet, RpcTokenAccount, TrustTier, decode_pubkey, encode_pubkey, validate_rpc_snapshot,
};
use serde::{Deserialize, Serialize};
use sha2::{Digest as _, Sha256};
use tokio::sync::Semaphore;

use crate::api::RateLimiter;
use crate::signed_turn_validation::ValidatedSignedTurn;
use crate::state::NodeState;

/// V1 intentionally remains unread: it did not bind a capability to a Dregg
/// player and therefore can never authorize sponsorship. V2 is read only for
/// an exact one-time migration into the append-only V3 lineage.
const ADMISSION_STATE_KEY: &str = "poa_dregg_holding_admission_v2";
const ADMISSION_STATE_ANCHOR_KEY: &str = "poa_dregg_holding_admission_anchor_v3";
const ADMISSION_STATE_VERSION: u16 = 3;
const MAX_ADMISSION_STATE_BYTES: usize = 8 * 1024 * 1024;
const MAX_ADMISSION_JOURNAL_RECORDS: usize = 8192;
const ADMISSION_JOURNAL_DOMAIN: &[u8] = b"path-of-angels/dregg-holding/admission-journal/v3\0";
// Bound the live blob independently of traffic volume. Expired rows are pruned,
// but live authority is never evicted by unrelated traffic: at capacity the
// newcomer is refused and can retry after the short TTL.
const MAX_LIVE_CHALLENGES: usize = 4096;
const MAX_LIVE_CAPABILITIES: usize = 4096;
const REQUESTS_PER_MINUTE: u32 = 10;
const MAX_IN_FLIGHT_RPC: usize = 4;
const MAX_REQUEST_BYTES: usize = 4096;
const MAX_RPC_RESPONSE_BYTES: usize = 4 * 1024 * 1024;
const RPC_URL_ENV: &str = "DREGG_POA_SOLANA_RPC_URL";
const ENDPOINT_ID_DOMAIN: &[u8] = b"poa-solana-rpc-endpoint-v1";
const CONSENSUS_AUTHORITY_STATE_KEY: &str = "poa_dregg_consensus_authority_v1";
const CONSENSUS_AUTHORITY_VERSION: u16 = 1;
const CONSENSUS_AUTHORITY_JOURNAL_DOMAIN: &[u8] =
    b"path-of-angels/dregg-holding/consensus-authority-journal/v1\0";
const MAX_CONSENSUS_AUTHORITY_BYTES: usize = 8 * 1024 * 1024;
const MAX_CONSENSUS_AUTHORITY_RECORDS: usize = 8192;
const MAX_CONSENSUS_RESERVATIONS: usize = 4096;
const MAX_CONSENSUS_CAPABILITIES: usize = 4096;

type RpcFuture<T> = Pin<Box<dyn Future<Output = Result<T, String>> + Send>>;

trait SolanaHoldingRpc: Clone + Send + Sync + 'static {
    fn endpoint_id(&self) -> Result<Bytes32, String>;
    fn finalized_slot(&self) -> RpcFuture<u64>;
    fn holding_snapshot(&self, challenge: Challenge) -> RpcFuture<RpcAccountSet>;
}

#[derive(Clone)]
struct HttpSolanaRpc {
    endpoint: Result<String, String>,
    client: Result<reqwest::Client, String>,
}

impl HttpSolanaRpc {
    fn from_env() -> Self {
        let endpoint = std::env::var(RPC_URL_ENV)
            .map_err(|_| format!("{RPC_URL_ENV} is not configured"))
            .and_then(|value| {
                let trimmed = value.trim();
                if trimmed.starts_with("https://") || trimmed.starts_with("http://127.0.0.1:") {
                    Ok(trimmed.to_owned())
                } else {
                    Err(format!(
                        "{RPC_URL_ENV} must be HTTPS (or loopback HTTP for a local test service)"
                    ))
                }
            });
        let client = reqwest::Client::builder()
            .connect_timeout(Duration::from_secs(5))
            .timeout(Duration::from_secs(10))
            .build()
            .map_err(|error| format!("could not build Solana RPC client: {error}"));
        Self { endpoint, client }
    }

    fn endpoint(&self) -> Result<&str, String> {
        self.endpoint.as_deref().map_err(Clone::clone)
    }

    async fn call(
        &self,
        method: &str,
        params: serde_json::Value,
    ) -> Result<serde_json::Value, String> {
        let endpoint = self.endpoint()?;
        let client = self.client.as_ref().map_err(Clone::clone)?;
        let mut response = client
            .post(endpoint)
            .json(&serde_json::json!({
                "jsonrpc": "2.0",
                "id": 1,
                "method": method,
                "params": params,
            }))
            .send()
            .await
            .map_err(|error| format!("{method} transport failed: {error}"))?;
        if !response.status().is_success() {
            return Err(format!("{method} returned HTTP {}", response.status()));
        }
        if response
            .content_length()
            .is_some_and(|length| length > MAX_RPC_RESPONSE_BYTES as u64)
        {
            return Err(format!("{method} response exceeds size ceiling"));
        }
        let mut encoded = Vec::new();
        while let Some(chunk) = response
            .chunk()
            .await
            .map_err(|error| format!("{method} response body failed: {error}"))?
        {
            let next_len = encoded
                .len()
                .checked_add(chunk.len())
                .ok_or_else(|| format!("{method} response length overflow"))?;
            if next_len > MAX_RPC_RESPONSE_BYTES {
                return Err(format!("{method} response exceeds size ceiling"));
            }
            encoded.extend_from_slice(&chunk);
        }
        let body: serde_json::Value = serde_json::from_slice(&encoded)
            .map_err(|error| format!("{method} returned invalid JSON: {error}"))?;
        if let Some(error) = body.get("error") {
            return Err(format!("{method} RPC error: {error}"));
        }
        body.get("result")
            .cloned()
            .ok_or_else(|| format!("{method} response omitted result"))
    }
}

impl SolanaHoldingRpc for HttpSolanaRpc {
    fn endpoint_id(&self) -> Result<Bytes32, String> {
        let mut hash = Sha256::new();
        hash.update(ENDPOINT_ID_DOMAIN);
        hash.update(self.endpoint()?.as_bytes());
        Ok(hash.finalize().into())
    }

    fn finalized_slot(&self) -> RpcFuture<u64> {
        let this = self.clone();
        Box::pin(async move {
            this.call(
                "getSlot",
                serde_json::json!([{ "commitment": "finalized" }]),
            )
            .await?
            .as_u64()
            .ok_or_else(|| "getSlot result is not a u64".to_owned())
        })
    }

    fn holding_snapshot(&self, challenge: Challenge) -> RpcFuture<RpcAccountSet> {
        let this = self.clone();
        Box::pin(async move {
            let endpoint_id = this.endpoint_id()?;
            let genesis_text = this
                .call("getGenesisHash", serde_json::json!([]))
                .await?
                .as_str()
                .ok_or_else(|| "getGenesisHash result is not a string".to_owned())?
                .to_owned();
            let genesis_hash = decode_pubkey(&genesis_text)
                .map_err(|error| format!("getGenesisHash returned an invalid hash: {error}"))?;
            let minimum_slot = challenge.min_context_slot();
            let result = this
                .call(
                    "getTokenAccountsByOwner",
                    serde_json::json!([
                        encode_pubkey(&challenge.wallet()),
                        { "mint": DREGG_MINT_BASE58 },
                        {
                            "commitment": "finalized",
                            "encoding": "base64",
                            "minContextSlot": minimum_slot,
                        }
                    ]),
                )
                .await?;
            decode_token_accounts_response(result, endpoint_id, genesis_hash, minimum_slot)
        })
    }
}

fn decode_token_accounts_response(
    result: serde_json::Value,
    endpoint_id: Bytes32,
    genesis_hash: Bytes32,
    requested_min_context_slot: u64,
) -> Result<RpcAccountSet, String> {
    let context_slot = result
        .pointer("/context/slot")
        .and_then(serde_json::Value::as_u64)
        .ok_or_else(|| "getTokenAccountsByOwner omitted context.slot".to_owned())?;
    let values = result
        .get("value")
        .and_then(serde_json::Value::as_array)
        .ok_or_else(|| "getTokenAccountsByOwner result.value is not an array".to_owned())?;
    let mut accounts = Vec::with_capacity(values.len());
    for value in values {
        let address = decode_pubkey(
            value
                .get("pubkey")
                .and_then(serde_json::Value::as_str)
                .ok_or_else(|| "token account omitted pubkey".to_owned())?,
        )
        .map_err(|error| format!("token account pubkey is invalid: {error}"))?;
        let account = value
            .get("account")
            .ok_or_else(|| "token account omitted account object".to_owned())?;
        let owner_program = decode_pubkey(
            account
                .get("owner")
                .and_then(serde_json::Value::as_str)
                .ok_or_else(|| "token account omitted owner program".to_owned())?,
        )
        .map_err(|error| format!("token owner program is invalid: {error}"))?;
        let encoded = account
            .get("data")
            .and_then(serde_json::Value::as_array)
            .ok_or_else(|| "token account data is not base64 tuple".to_owned())?;
        if encoded.len() != 2
            || encoded.get(1).and_then(serde_json::Value::as_str) != Some("base64")
        {
            return Err("token account data encoding is not exact base64".to_owned());
        }
        let data = base64::engine::general_purpose::STANDARD
            .decode(
                encoded
                    .first()
                    .and_then(serde_json::Value::as_str)
                    .ok_or_else(|| "token account omitted base64 data".to_owned())?,
            )
            .map_err(|error| format!("token account base64 is invalid: {error}"))?;
        accounts.push(RpcTokenAccount {
            address,
            account: dregg_pay::watcher::FetchedAccount {
                data,
                owner_program,
                slot: context_slot,
            },
        });
    }
    Ok(RpcAccountSet {
        endpoint_id,
        genesis_hash,
        commitment: Commitment::Finalized,
        requested_min_context_slot,
        context_slot,
        accounts,
    })
}

#[derive(Clone)]
struct HoldingLimits {
    per_ip: RateLimiter,
    in_flight: Arc<Semaphore>,
}

impl HoldingLimits {
    fn new() -> Self {
        Self {
            per_ip: RateLimiter::new(REQUESTS_PER_MINUTE, 60),
            in_flight: Arc::new(Semaphore::new(MAX_IN_FLIGHT_RPC)),
        }
    }
}

pub(crate) fn routes() -> Router<NodeState> {
    routes_with_rpc(HttpSolanaRpc::from_env())
}

fn routes_with_rpc<R: SolanaHoldingRpc>(rpc: R) -> Router<NodeState> {
    let limits = HoldingLimits::new();
    Router::new()
        .route(
            "/api/poa/holding/challenge",
            post({
                let rpc = rpc.clone();
                let limits = limits.clone();
                move |peer, headers, state, body| {
                    post_challenge(peer, headers, state, body, rpc.clone(), limits.clone())
                }
            }),
        )
        .route(
            "/api/poa/holding/verify",
            post({
                let rpc = rpc.clone();
                let limits = limits.clone();
                move |peer, headers, state, body| {
                    post_verify(peer, headers, state, body, rpc.clone(), limits.clone())
                }
            }),
        )
        .route(
            "/api/poa/holding/status/{receipt_id}",
            get({
                let limits = limits.clone();
                move |peer, headers, state, path| {
                    get_status(peer, headers, state, path, limits.clone())
                }
            }),
        )
        .layer(axum::extract::DefaultBodyLimit::max(MAX_REQUEST_BYTES))
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct ChallengeRequest {
    wallet: String,
    player: String,
}

#[derive(Debug, Serialize)]
struct ChallengeResponse {
    format: &'static str,
    challenge_id: String,
    wallet: String,
    player: String,
    player_cell: String,
    signing_message_base64: String,
    mint: &'static str,
    cluster: String,
    minimum_raw_balance: String,
    min_context_slot: u64,
    issued_at: u64,
    expires_at: u64,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct VerifyRequest {
    challenge_id: String,
    signature_base64: String,
}

#[derive(Debug, Serialize)]
struct CapabilityResponse {
    format: &'static str,
    receipt_id: String,
    trust: &'static str,
    wallet: String,
    player: String,
    player_cell: String,
    mint: String,
    snapshot_slot: u64,
    issued_at: u64,
    expires_at: u64,
    governance_weight_bearing: bool,
}

#[derive(Debug, Serialize)]
struct HoldingStatusResponse {
    format: &'static str,
    receipt_id: String,
    state: &'static str,
    trust: &'static str,
    expires_at: u64,
    governance_weight_bearing: bool,
}

#[derive(Debug, Serialize)]
struct ErrorBody {
    code: &'static str,
    message: String,
}

#[derive(Debug)]
struct ApiError {
    status: StatusCode,
    code: &'static str,
    message: String,
}

impl ApiError {
    fn new(status: StatusCode, code: &'static str, message: impl Into<String>) -> Self {
        Self {
            status,
            code,
            message: message.into(),
        }
    }
}

impl IntoResponse for ApiError {
    fn into_response(self) -> Response {
        (
            self.status,
            Json(ErrorBody {
                code: self.code,
                message: self.message,
            }),
        )
            .into_response()
    }
}

async fn post_challenge<R: SolanaHoldingRpc>(
    ConnectInfo(peer): ConnectInfo<SocketAddr>,
    headers: HeaderMap,
    State(state): State<NodeState>,
    Json(request): Json<ChallengeRequest>,
    rpc: R,
    limits: HoldingLimits,
) -> Result<(StatusCode, Json<ChallengeResponse>), ApiError> {
    admit_request(peer, &headers, &limits).await?;
    let _permit =
        limits.in_flight.clone().try_acquire_owned().map_err(|_| {
            ApiError::new(StatusCode::TOO_MANY_REQUESTS, "busy", "holding RPC is busy")
        })?;
    let wallet = decode_pubkey(&request.wallet).map_err(|error| {
        ApiError::new(StatusCode::BAD_REQUEST, "invalid_wallet", error.to_string())
    })?;
    let player = decode_pubkey(&request.player).map_err(|error| {
        ApiError::new(StatusCode::BAD_REQUEST, "invalid_player", error.to_string())
    })?;
    let endpoint_id = rpc.endpoint_id().map_err(rpc_unavailable)?;
    let min_context_slot = rpc.finalized_slot().await.map_err(rpc_bad_gateway)?;
    let now = unix_time()?;
    let (federation_id, store) = node_admission_context(&state).await?;
    let config = GateConfig::path_of_angels_mainnet(federation_id, endpoint_id);
    let mut nonce = [0u8; 32];
    getrandom::fill(&mut nonce).map_err(|error| {
        ApiError::new(
            StatusCode::INTERNAL_SERVER_ERROR,
            "entropy_unavailable",
            error.to_string(),
        )
    })?;
    let challenge = {
        // Serialize every read-modify-write of the one durable admission blob
        // against other node handlers. No network await occurs under this lock.
        let _node_write = state.write().await;
        let mut gate = Gate::with_store(RedbAdmissionStore::new(store));
        gate.issue(&config, wallet, player, nonce, min_context_slot, now)
            .map_err(map_gate_error)?
    };
    Ok((
        StatusCode::CREATED,
        Json(ChallengeResponse {
            format: "poa-dregg-holding-challenge-v2",
            challenge_id: encode_id(&challenge.id()),
            wallet: encode_pubkey(&challenge.wallet()),
            player: encode_pubkey(&challenge.player()),
            player_cell: encode_id(&challenge.player_cell()),
            signing_message_base64: base64::engine::general_purpose::STANDARD
                .encode(challenge.signing_message()),
            mint: DREGG_MINT_BASE58,
            cluster: config.cluster,
            minimum_raw_balance: config.minimum_raw_balance.to_string(),
            min_context_slot,
            issued_at: now,
            expires_at: challenge.expires_at(),
        }),
    ))
}

async fn post_verify<R: SolanaHoldingRpc>(
    ConnectInfo(peer): ConnectInfo<SocketAddr>,
    headers: HeaderMap,
    State(state): State<NodeState>,
    Json(request): Json<VerifyRequest>,
    rpc: R,
    limits: HoldingLimits,
) -> Result<Json<CapabilityResponse>, ApiError> {
    admit_request(peer, &headers, &limits).await?;
    let _permit =
        limits.in_flight.clone().try_acquire_owned().map_err(|_| {
            ApiError::new(StatusCode::TOO_MANY_REQUESTS, "busy", "holding RPC is busy")
        })?;
    let challenge_id = decode_id(&request.challenge_id, "invalid_challenge_id")?;
    let signature = decode_signature(&request.signature_base64)?;
    let endpoint_id = rpc.endpoint_id().map_err(rpc_unavailable)?;
    let now = unix_time()?;
    let (federation_id, store) = node_admission_context(&state).await?;
    let config = GateConfig::path_of_angels_mainnet(federation_id, endpoint_id);
    let challenge = Gate::with_store(RedbAdmissionStore::new(Arc::clone(&store)))
        .issued_challenge(&challenge_id)
        .map_err(map_gate_error)?
        .ok_or_else(|| {
            ApiError::new(
                StatusCode::NOT_FOUND,
                "unknown_challenge",
                "challenge was not issued by this node",
            )
        })?;
    let binding = dregg_governance::holding_weight::OwnerBinding {
        voter: challenge.player(),
        sig: signature,
    };
    Gate::with_store(RedbAdmissionStore::new(Arc::clone(&store)))
        .preflight_beta(&config, &challenge, &binding, now)
        .map_err(map_gate_error)?;
    let snapshot = rpc
        .holding_snapshot(challenge.clone())
        .await
        .map_err(rpc_bad_gateway)?;
    let observation =
        validate_rpc_snapshot(&config, &challenge, &snapshot).map_err(map_gate_error)?;
    let capability = {
        let _node_write = state.write().await;
        let mut gate = Gate::with_store(RedbAdmissionStore::new(store));
        gate.admit_beta(&config, &challenge, &binding, observation, now)
            .map_err(map_gate_error)?
    };
    Ok(Json(capability_response(&capability)))
}

async fn get_status(
    ConnectInfo(peer): ConnectInfo<SocketAddr>,
    headers: HeaderMap,
    State(state): State<NodeState>,
    Path(receipt_id): Path<String>,
    limits: HoldingLimits,
) -> Result<Json<HoldingStatusResponse>, ApiError> {
    admit_request(peer, &headers, &limits).await?;
    let receipt_id = decode_id(&receipt_id, "invalid_receipt_id")?;
    let now = unix_time()?;
    let (_, store) = node_admission_context(&state).await?;
    let gate = Gate::with_store(RedbAdmissionStore::new(store));
    let (state_name, capability) = match gate
        .capability_status(&receipt_id, now)
        .map_err(map_gate_error)?
    {
        CapabilityStatus::Unknown => {
            return Err(ApiError::new(
                StatusCode::NOT_FOUND,
                "unknown_receipt",
                "receipt was not issued by this node",
            ));
        }
        CapabilityStatus::Active(capability) => ("active", capability),
        CapabilityStatus::Expired(capability) => ("expired", capability),
        CapabilityStatus::Consumed(capability) => ("consumed", capability),
    };
    Ok(Json(status_response(state_name, &capability)))
}

async fn admit_request(
    peer: SocketAddr,
    headers: &HeaderMap,
    limits: &HoldingLimits,
) -> Result<(), ApiError> {
    if !limits.per_ip.check_request(peer.ip(), headers).await {
        return Err(ApiError::new(
            StatusCode::TOO_MANY_REQUESTS,
            "rate_limited",
            "holding admission limit exceeded",
        ));
    }
    Ok(())
}

async fn node_admission_context(
    state: &NodeState,
) -> Result<(Bytes32, Arc<dregg_persist::PersistentStore>), ApiError> {
    let node = state.read().await;
    if !node.federation_configured || node.federation_id == [0; 32] {
        return Err(ApiError::new(
            StatusCode::SERVICE_UNAVAILABLE,
            "federation_unconfigured",
            "node has no configured federation identity",
        ));
    }
    Ok((node.federation_id, Arc::clone(&node.store)))
}

fn unix_time() -> Result<u64, ApiError> {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|duration| duration.as_secs())
        .map_err(|error| {
            ApiError::new(
                StatusCode::INTERNAL_SERVER_ERROR,
                "clock_before_epoch",
                error.to_string(),
            )
        })
}

fn encode_id(id: &Bytes32) -> String {
    base64::engine::general_purpose::URL_SAFE_NO_PAD.encode(id)
}

fn decode_id(text: &str, code: &'static str) -> Result<Bytes32, ApiError> {
    let decoded = base64::engine::general_purpose::URL_SAFE_NO_PAD
        .decode(text)
        .map_err(|error| ApiError::new(StatusCode::BAD_REQUEST, code, error.to_string()))?;
    if base64::engine::general_purpose::URL_SAFE_NO_PAD.encode(&decoded) != text {
        return Err(ApiError::new(
            StatusCode::BAD_REQUEST,
            code,
            "id must use canonical base64url without padding",
        ));
    }
    decoded
        .try_into()
        .map_err(|_| ApiError::new(StatusCode::BAD_REQUEST, code, "id must decode to 32 bytes"))
}

fn decode_signature(text: &str) -> Result<[u8; 64], ApiError> {
    let decoded = base64::engine::general_purpose::STANDARD
        .decode(text)
        .map_err(|error| {
            ApiError::new(
                StatusCode::BAD_REQUEST,
                "invalid_signature",
                error.to_string(),
            )
        })?;
    if base64::engine::general_purpose::STANDARD.encode(&decoded) != text {
        return Err(ApiError::new(
            StatusCode::BAD_REQUEST,
            "invalid_signature",
            "signature must use canonical standard base64",
        ));
    }
    decoded.try_into().map_err(|_| {
        ApiError::new(
            StatusCode::BAD_REQUEST,
            "invalid_signature",
            "signature must decode to 64 bytes",
        )
    })
}

fn capability_response(capability: &HoldingCapability) -> CapabilityResponse {
    CapabilityResponse {
        format: "poa-dregg-holding-capability-v2",
        receipt_id: encode_id(&capability.receipt_id()),
        trust: trust_name(capability.trust()),
        wallet: encode_pubkey(&capability.wallet()),
        player: encode_pubkey(&capability.player()),
        player_cell: encode_id(&capability.player_cell()),
        mint: encode_pubkey(&capability.mint()),
        snapshot_slot: capability.snapshot_slot(),
        issued_at: capability.issued_at(),
        expires_at: capability.expires_at(),
        governance_weight_bearing: capability.is_governance_weight_bearing(),
    }
}

fn status_response(state: &'static str, capability: &HoldingCapability) -> HoldingStatusResponse {
    let response = capability_response(capability);
    HoldingStatusResponse {
        format: "poa-dregg-holding-status-v2",
        receipt_id: response.receipt_id,
        state,
        trust: response.trust,
        expires_at: response.expires_at,
        governance_weight_bearing: response.governance_weight_bearing,
    }
}

fn trust_name(trust: TrustTier) -> &'static str {
    match trust {
        TrustTier::BetaRpcAttested => "beta-rpc-attested",
        TrustTier::ConsensusVerified => "consensus-verified",
    }
}

fn rpc_unavailable(_detail: String) -> ApiError {
    ApiError::new(
        StatusCode::SERVICE_UNAVAILABLE,
        "rpc_unavailable",
        "Solana holding RPC is unavailable",
    )
}

fn rpc_bad_gateway(_detail: String) -> ApiError {
    ApiError::new(
        StatusCode::BAD_GATEWAY,
        "rpc_refused",
        "Solana holding RPC refused the finalized evidence request",
    )
}

fn map_gate_error(error: GateError) -> ApiError {
    let (status, code) = match error {
        GateError::UnknownChallenge => (StatusCode::NOT_FOUND, "unknown_challenge"),
        GateError::ChallengeExpired | GateError::CapabilityExpired => (StatusCode::GONE, "expired"),
        GateError::NonceAlreadyIssued
        | GateError::ChallengeReplay
        | GateError::CapabilityReplay
        | GateError::CapabilityIdCollision => (StatusCode::CONFLICT, "replay"),
        GateError::AdmissionCapacity => (StatusCode::SERVICE_UNAVAILABLE, "admission_full"),
        GateError::BadWalletSignature => (StatusCode::FORBIDDEN, "bad_wallet_signature"),
        GateError::InsufficientBalance => (StatusCode::FORBIDDEN, "insufficient_dregg"),
        GateError::BadBase58
        | GateError::BadPubkeyLength
        | GateError::WeakNonce
        | GateError::InvalidPlayer => (StatusCode::BAD_REQUEST, "invalid_request"),
        GateError::Store(_) => (StatusCode::INTERNAL_SERVER_ERROR, "admission_store_failed"),
        GateError::InvalidConfiguration | GateError::TimeOverflow => (
            StatusCode::INTERNAL_SERVER_ERROR,
            "admission_configuration_failed",
        ),
        GateError::RpcSource(_) => (StatusCode::BAD_GATEWAY, "rpc_refused"),
        GateError::WrongRpcEndpoint
        | GateError::WrongCluster
        | GateError::NotFinalized
        | GateError::StaleSlot
        | GateError::MixedSlots
        | GateError::WrongTokenProgram
        | GateError::DuplicateTokenAccount
        | GateError::MalformedTokenAccount
        | GateError::WrongMint
        | GateError::WrongOwner
        | GateError::BalanceOverflow => (StatusCode::BAD_GATEWAY, "rpc_evidence_refused"),
        GateError::ChallengeMutation
        | GateError::ObservationMismatch
        | GateError::ForgedCapability => (StatusCode::FORBIDDEN, "evidence_mismatch"),
    };
    let message = match code {
        "admission_store_failed" => "durable admission storage failed".to_owned(),
        "admission_configuration_failed" => "holding admission is misconfigured".to_owned(),
        "rpc_refused" => "Solana holding RPC refused the evidence request".to_owned(),
        _ => error.to_string(),
    };
    ApiError::new(status, code, message)
}

/// Checked, non-serializable holder intent beside one exact finalized Galley
/// event.  This is deliberately *not* a persistence carrier: the raw prepared
/// persistence constructor is crate-private to `dregg-persist`, so a future
/// Galley adapter must add a Lean-authored semantic binding before anything can
/// be consumed.  Keeping all intent/event coordinates here prevents that future
/// seam from dropping beneficiary, action, activated content, or event scope.
#[derive(Debug, PartialEq, Eq)]
pub(crate) struct AuthorizedPoaHoldingConsumptionV1 {
    capability_receipt_id: Bytes32,
    holder_wallet: Bytes32,
    player: Bytes32,
    player_cell: Bytes32,
    action_token: Bytes32,
    beneficiary_player_id: Bytes32,
    world_federation_id: Bytes32,
    content_root: Bytes32,
    activation_digest: Bytes32,
    content_session: Bytes32,
    content_epoch: u64,
    event_scope_nullifier: Bytes32,
    intent_event_binding: Bytes32,
    batch_digest: Bytes32,
    event_index: u32,
    stream_digest: Bytes32,
    event_sequence: u64,
    event_digest: Bytes32,
}

/// Fail-closed holder-admission boundary for a future Galley finalization
/// adapter.
///
/// `validated_turn` must come from the node's complete signed-turn perimeter,
/// `receipt` from the executor-produced finalized authority.  Time comes from
/// the node itself rather than a caller-supplied integer.  This function
/// re-welds all of those coordinates to the Lean-prepared batch before
/// consulting node-owned admission storage under the global node write lock.
/// It neither consumes the capability nor exposes a transport: the exact
/// prepared carrier must subsequently be committed atomically with `batch`, at
/// which point persistence performs the one-shot nullifier transition.
///
/// The current Galley runtime emits exactly one event per accepted command.  A
/// multi-event holder batch is refused until Lean exports an explicit sponsor
/// event selector; Rust must not guess which event consumed the receipt.
pub(crate) async fn authorize_poa_holding_finalization_v1(
    state: &NodeState,
    signed: &dregg_sdk::SignedTurn,
    validated_turn: ValidatedSignedTurn,
    receipt: &dregg_turn::TurnReceipt,
    batch: &dregg_persist::PreparedPoaEventBatchV2,
) -> Result<AuthorizedPoaHoldingConsumptionV1, PoaHoldingFinalizationError> {
    let server_now =
        unix_time().map_err(|error| PoaHoldingFinalizationError::Clock(error.message))?;
    authorize_poa_holding_finalization_at_v1(
        state,
        server_now,
        signed,
        validated_turn,
        receipt,
        batch,
    )
    .await
}

async fn authorize_poa_holding_finalization_at_v1(
    state: &NodeState,
    server_now: u64,
    signed: &dregg_sdk::SignedTurn,
    validated_turn: ValidatedSignedTurn,
    receipt: &dregg_turn::TurnReceipt,
    batch: &dregg_persist::PreparedPoaEventBatchV2,
) -> Result<AuthorizedPoaHoldingConsumptionV1, PoaHoldingFinalizationError> {
    let command = dregg_sdk::poa_galley::command_from_exact_galley_signed_turn(signed)
        .map_err(|_| PoaHoldingFinalizationError::InvalidGalleyCarrier)?;
    let (action_token, capability_receipt_id, beneficiary_player_id) = match command {
        dregg_sdk::poa_galley::GalleyPlayerCommandV1::HolderSponsorship {
            action_token,
            holder_receipt_id,
            beneficiary_player_id,
        } => (
            action_token.to_bytes(),
            holder_receipt_id.to_bytes(),
            beneficiary_player_id,
        ),
        _ => return Err(PoaHoldingFinalizationError::NotHolderSponsorship),
    };
    if action_token == [0; 32] || beneficiary_player_id == [0; 32] {
        return Err(PoaHoldingFinalizationError::InvalidHolderIntent);
    }

    let turn_hash = signed.turn.hash();
    let coordinate = batch.coordinate();
    let signer = signed.signer.0;
    let canonical_player_cell =
        dregg_cell::CellId::derive_raw(&signer, blake3::hash(b"default").as_bytes());
    if validated_turn.turn_hash() != turn_hash
        || receipt.turn_hash != turn_hash
        || receipt.receipt_hash() != coordinate.receipt_hash()
        || receipt.agent != signed.turn.agent
        || receipt.agent != canonical_player_cell
        || receipt.pre_state_hash != coordinate.actor_root()
        || coordinate.turn_hash() != turn_hash
        || coordinate.signer() != signer
        || coordinate.world().federation_id() != receipt.federation_id
    {
        return Err(PoaHoldingFinalizationError::FinalizedContextMismatch);
    }

    let [event] = batch.events() else {
        return Err(PoaHoldingFinalizationError::AmbiguousHolderEvent);
    };
    if event.event_index() != 0 {
        return Err(PoaHoldingFinalizationError::AmbiguousHolderEvent);
    }

    // Serialize capability lookup/status and construction against every other
    // admission blob RMW.  No network or proof work occurs while this lock is
    // held.  The later exact persistence transaction remains the authority that
    // wins a concurrent one-shot race.
    let node = state.write().await;
    if !node.federation_configured || node.federation_id == [0; 32] {
        return Err(PoaHoldingFinalizationError::FederationUnconfigured);
    }
    if node.federation_id != receipt.federation_id {
        return Err(PoaHoldingFinalizationError::FinalizedContextMismatch);
    }
    let admission = RedbAdmissionStore::new(Arc::clone(&node.store));
    let durable = admission
        .load()
        .map_err(PoaHoldingFinalizationError::Store)?;
    let lineage = durable
        .replay_journal()
        .map_err(PoaHoldingFinalizationError::Store)?;
    let capability = lineage
        .capabilities
        .get(&capability_receipt_id)
        .cloned()
        .ok_or(PoaHoldingFinalizationError::UnknownCapability)?;
    if admission
        .capability_consumed(&capability_receipt_id)
        .map_err(PoaHoldingFinalizationError::Store)?
    {
        return Err(PoaHoldingFinalizationError::CapabilityReplay);
    }
    if server_now < capability.issued_at() || server_now > capability.expires_at() {
        return Err(PoaHoldingFinalizationError::CapabilityExpired);
    }

    let challenge = lineage.challenges.get(&capability.challenge_id());
    let challenge_backed = lineage
        .spent_challenges
        .contains(&capability.challenge_id())
        && challenge.is_some_and(|challenge| {
            challenge.player() == capability.player()
                && challenge.player_cell() == capability.player_cell()
                && challenge.wallet() == capability.wallet()
        });
    let mainnet_mint = decode_pubkey(DREGG_MINT_BASE58)
        .expect("the compile-time Path of Angels DREGG mint must decode");
    if capability.receipt_id() != capability_receipt_id
        || !challenge_backed
        || capability.trust() != TrustTier::ConsensusVerified
        || capability.mint() != mainnet_mint
        || capability.origin() != "https://beta.pathofangels.network"
        || capability.domain() != "pathofangels.network"
        || capability.cluster() != "solana:mainnet-beta"
        || capability.federation_id() != node.federation_id
        || capability.federation_id() != coordinate.world().federation_id()
        || capability.player() != signer
        || capability.player_cell() != canonical_player_cell.0
    {
        return Err(PoaHoldingFinalizationError::CapabilityPolicyMismatch);
    }

    let world = coordinate.world();
    let event_scope_nullifier =
        dregg_persist::poa_holding_consumption::derive_poa_holding_event_scope_nullifier_v1(
            capability.wallet(),
            world.federation_id(),
            world.content_root(),
            world.activation_digest(),
            world.content_session(),
            world.content_epoch(),
            batch.batch_digest(),
            event.event_index(),
            event.stream_digest(),
            event.sequence(),
            event.event_digest(),
        );
    let intent_event_binding =
        dregg_persist::poa_holding_consumption::derive_poa_holding_intent_event_binding_v1(
            capability_receipt_id,
            capability.wallet(),
            signer,
            canonical_player_cell.0,
            action_token,
            beneficiary_player_id,
            world.federation_id(),
            world.content_root(),
            world.activation_digest(),
            world.content_session(),
            world.content_epoch(),
            batch.batch_digest(),
            event.event_index(),
            event.stream_digest(),
            event.sequence(),
            event.event_digest(),
        );
    Ok(AuthorizedPoaHoldingConsumptionV1 {
        capability_receipt_id,
        holder_wallet: capability.wallet(),
        player: signer,
        player_cell: canonical_player_cell.0,
        action_token,
        beneficiary_player_id,
        world_federation_id: world.federation_id(),
        content_root: world.content_root(),
        activation_digest: world.activation_digest(),
        content_session: world.content_session(),
        content_epoch: world.content_epoch(),
        event_scope_nullifier,
        intent_event_binding,
        batch_digest: batch.batch_digest(),
        event_index: event.event_index(),
        stream_digest: event.stream_digest(),
        event_sequence: event.sequence(),
        event_digest: event.event_digest(),
    })
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum PoaHoldingFinalizationError {
    InvalidGalleyCarrier,
    NotHolderSponsorship,
    InvalidHolderIntent,
    AmbiguousHolderEvent,
    FinalizedContextMismatch,
    FederationUnconfigured,
    UnknownCapability,
    CapabilityExpired,
    CapabilityReplay,
    CapabilityPolicyMismatch,
    Clock(String),
    Store(String),
}

impl std::fmt::Display for PoaHoldingFinalizationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let message = match self {
            Self::InvalidGalleyCarrier => "Galley signed carrier is malformed",
            Self::NotHolderSponsorship => "Galley command is not holder sponsorship",
            Self::InvalidHolderIntent => "Galley holder intent has a zero action or beneficiary",
            Self::AmbiguousHolderEvent => "Galley holder batch does not identify exactly one event",
            Self::FinalizedContextMismatch => {
                "finalized Galley signer, receipt, actor, world, or batch coordinates disagree"
            }
            Self::FederationUnconfigured => "node has no configured federation identity",
            Self::UnknownCapability => "holding capability was not issued by this node",
            Self::CapabilityExpired => {
                "holding capability is expired at authenticated finalization time"
            }
            Self::CapabilityReplay => "holding capability has already been consumed",
            Self::CapabilityPolicyMismatch => {
                "holding capability is not consensus-verified or does not match the exact PoA policy/finalized player"
            }
            Self::Clock(detail) => return write!(f, "holding authority clock failed: {detail}"),
            Self::Store(detail) => return write!(f, "holding authority store failed: {detail}"),
        };
        f.write_str(message)
    }
}

impl std::error::Error for PoaHoldingFinalizationError {}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
struct DurableAdmissionState {
    /// Bounded working indexes. These may forget expired rows, but every row
    /// must be an exact projection of `journal` and may never invent authority.
    challenges: BTreeMap<Bytes32, Challenge>,
    used_nonces: BTreeSet<Bytes32>,
    spent_challenges: BTreeSet<Bytes32>,
    capabilities: BTreeMap<Bytes32, HoldingCapability>,
    spent_capabilities: BTreeSet<Bytes32>,
    /// Canonical append-only authority lineage. Unlike the working indexes,
    /// this is never TTL-pruned. At its explicit ceiling admission refuses;
    /// unrelated traffic may not evict the evidence behind an old receipt.
    journal: Vec<AdmissionJournalRecord>,
    journal_head: Bytes32,
}

impl DurableAdmissionState {
    fn prune_expired(&mut self, now: u64) {
        self.capabilities
            .retain(|_, capability| capability.expires_at() >= now);
        self.challenges
            .retain(|_, challenge| challenge.expires_at() >= now);
        self.compact_indexes();
    }

    fn compact_indexes(&mut self) {
        self.used_nonces = self.challenges.values().map(Challenge::nonce).collect();
        self.spent_capabilities
            .retain(|id| self.capabilities.contains_key(id));
        self.spent_challenges.retain(|id| {
            self.challenges.contains_key(id)
                || self
                    .capabilities
                    .values()
                    .any(|capability| capability.challenge_id() == *id)
        });
    }

    fn replay_journal(&self) -> Result<AdmissionJournalProjection, String> {
        if self.journal.len() > MAX_ADMISSION_JOURNAL_RECORDS {
            return Err("durable admission journal exceeds its record ceiling".to_owned());
        }
        let mut projection = AdmissionJournalProjection::default();
        let mut previous = [0; 32];
        for (index, record) in self.journal.iter().enumerate() {
            let ordinal = u64::try_from(index)
                .map_err(|_| "durable admission journal ordinal overflow".to_owned())?;
            if record.ordinal != ordinal {
                return Err("durable admission journal ordinal is not dense".to_owned());
            }
            if record.previous_digest != previous {
                return Err("durable admission journal predecessor mismatch".to_owned());
            }
            let expected =
                admission_journal_digest(record.ordinal, record.previous_digest, &record.event)?;
            if record.digest != expected {
                return Err("durable admission journal digest mismatch".to_owned());
            }
            match &record.event {
                AdmissionJournalEvent::ChallengeIssued { challenge } => {
                    if projection.challenges.contains_key(&challenge.id())
                        || !projection.used_nonces.insert(challenge.nonce())
                    {
                        return Err(
                            "durable admission journal reissues a challenge or nonce".to_owned()
                        );
                    }
                    projection
                        .challenges
                        .insert(challenge.id(), challenge.clone());
                }
                AdmissionJournalEvent::CapabilityIssued {
                    challenge_id,
                    capability,
                } => {
                    let Some(challenge) = projection.challenges.get(challenge_id) else {
                        return Err(
                            "durable admission journal capability precedes its challenge"
                                .to_owned(),
                        );
                    };
                    if capability.challenge_id() != *challenge_id
                        || capability.player() != challenge.player()
                        || capability.player_cell() != challenge.player_cell()
                        || capability.wallet() != challenge.wallet()
                        || capability.issued_at() < challenge.issued_at()
                        || capability.issued_at() > challenge.expires_at()
                    {
                        return Err(
                            "durable admission journal capability/challenge binding mismatch"
                                .to_owned(),
                        );
                    }
                    if !projection.spent_challenges.insert(*challenge_id) {
                        return Err(
                            "durable admission journal spends one challenge twice".to_owned()
                        );
                    }
                    if projection
                        .capabilities
                        .insert(capability.receipt_id(), capability.clone())
                        .is_some()
                    {
                        return Err(
                            "durable admission journal reissues a capability receipt".to_owned()
                        );
                    }
                }
            }
            previous = record.digest;
        }
        if self.journal_head != previous {
            return Err("durable admission journal head mismatch".to_owned());
        }
        Ok(projection)
    }

    fn validate(&self) -> Result<(), String> {
        let projection = self.replay_journal()?;
        for (id, challenge) in &self.challenges {
            if projection.challenges.get(id) != Some(challenge) {
                return Err("live challenge index invents or mutates authority".to_owned());
            }
        }
        for (id, capability) in &self.capabilities {
            if projection.capabilities.get(id) != Some(capability) {
                return Err("live capability index invents or mutates authority".to_owned());
            }
        }
        let expected_nonces = self.challenges.values().map(Challenge::nonce).collect();
        if self.used_nonces != expected_nonces {
            return Err("live nonce index is not the exact challenge projection".to_owned());
        }
        let expected_spent_challenges = projection
            .spent_challenges
            .iter()
            .copied()
            .filter(|id| {
                self.challenges.contains_key(id)
                    || self
                        .capabilities
                        .values()
                        .any(|capability| capability.challenge_id() == *id)
            })
            .collect();
        if self.spent_challenges != expected_spent_challenges {
            return Err(
                "live spent-challenge index is not the exact lineage projection".to_owned(),
            );
        }
        if !self
            .spent_capabilities
            .iter()
            .all(|id| projection.capabilities.contains_key(id))
        {
            return Err("live spent-capability index invents authority".to_owned());
        }
        Ok(())
    }

    fn append(&mut self, event: AdmissionJournalEvent) -> Result<(), String> {
        if self.journal.len() >= MAX_ADMISSION_JOURNAL_RECORDS {
            return Err("durable admission journal capacity exhausted".to_owned());
        }
        let ordinal = u64::try_from(self.journal.len())
            .map_err(|_| "durable admission journal ordinal overflow".to_owned())?;
        let digest = admission_journal_digest(ordinal, self.journal_head, &event)?;
        self.journal.push(AdmissionJournalRecord {
            ordinal,
            previous_digest: self.journal_head,
            event,
            digest,
        });
        self.journal_head = digest;
        Ok(())
    }

    fn historical_challenge(&self, id: &Bytes32) -> Result<Option<Challenge>, String> {
        Ok(self.replay_journal()?.challenges.get(id).cloned())
    }

    fn historical_capability(&self, id: &Bytes32) -> Result<Option<HoldingCapability>, String> {
        Ok(self.replay_journal()?.capabilities.get(id).cloned())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
enum AdmissionJournalEvent {
    ChallengeIssued {
        challenge: Challenge,
    },
    CapabilityIssued {
        challenge_id: Bytes32,
        capability: HoldingCapability,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct AdmissionJournalRecord {
    ordinal: u64,
    previous_digest: Bytes32,
    event: AdmissionJournalEvent,
    digest: Bytes32,
}

#[derive(Default)]
struct AdmissionJournalProjection {
    challenges: BTreeMap<Bytes32, Challenge>,
    used_nonces: BTreeSet<Bytes32>,
    spent_challenges: BTreeSet<Bytes32>,
    capabilities: BTreeMap<Bytes32, HoldingCapability>,
}

fn admission_journal_digest(
    ordinal: u64,
    previous_digest: Bytes32,
    event: &AdmissionJournalEvent,
) -> Result<Bytes32, String> {
    // The event bytes are postcard's deterministic struct/enum encoding. The
    // explicit domain, ordinal, predecessor and length make concatenation
    // unambiguous; load additionally demands byte-exact envelope re-encoding.
    let event_bytes = postcard::to_stdvec(event)
        .map_err(|error| format!("journal event encode failed: {error}"))?;
    let event_len =
        u64::try_from(event_bytes.len()).map_err(|_| "journal event length overflow".to_owned())?;
    let mut hash = Sha256::new();
    hash.update(ADMISSION_JOURNAL_DOMAIN);
    hash.update(ordinal.to_be_bytes());
    hash.update(previous_digest);
    hash.update(event_len.to_be_bytes());
    hash.update(event_bytes);
    Ok(hash.finalize().into())
}

#[derive(Serialize, Deserialize)]
struct DurableAdmissionEnvelope {
    version: u16,
    state: DurableAdmissionState,
}

#[derive(Serialize, Deserialize)]
struct DurableAdmissionStateV2 {
    challenges: BTreeMap<Bytes32, Challenge>,
    used_nonces: BTreeSet<Bytes32>,
    spent_challenges: BTreeSet<Bytes32>,
    capabilities: BTreeMap<Bytes32, HoldingCapability>,
    spent_capabilities: BTreeSet<Bytes32>,
}

#[derive(Serialize, Deserialize)]
struct DurableAdmissionEnvelopeV2 {
    version: u16,
    state: DurableAdmissionStateV2,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct DurableAdmissionAnchor {
    version: u16,
    journal_len: u64,
    journal_head: Bytes32,
}

impl DurableAdmissionAnchor {
    fn from_state(state: &DurableAdmissionState) -> Result<Self, String> {
        Ok(Self {
            version: ADMISSION_STATE_VERSION,
            journal_len: u64::try_from(state.journal.len())
                .map_err(|_| "durable admission journal length overflow".to_owned())?,
            journal_head: state.journal_head,
        })
    }
}

/// Separate lineage for consensus-grade authority. Keeping it outside the V3
/// beta blob avoids silently reinterpreting any already-issued RPC capability.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
struct DurableConsensusAuthorityState {
    reservations: BTreeMap<Bytes32, ConsensusReservationReceipt>,
    reservation_by_challenge: BTreeMap<Bytes32, Bytes32>,
    reservation_by_nullifier: BTreeMap<Bytes32, Bytes32>,
    capabilities: BTreeMap<Bytes32, ConsensusHoldingCapability>,
    capability_by_reservation: BTreeMap<Bytes32, Bytes32>,
    observed_time_floor: u64,
    journal: Vec<ConsensusAuthorityJournalRecord>,
    journal_head: Bytes32,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
enum ConsensusAuthorityJournalEvent {
    ReservationIssued {
        reservation: ConsensusPrivilegeReservation,
    },
    CapabilityIssued {
        reservation_id: Bytes32,
        capability: ConsensusHoldingCapability,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct ConsensusAuthorityJournalRecord {
    ordinal: u64,
    previous_digest: Bytes32,
    observed_time_floor: u64,
    event: ConsensusAuthorityJournalEvent,
    digest: Bytes32,
}

#[derive(Default)]
struct ConsensusAuthorityProjection {
    reservations: BTreeMap<Bytes32, ConsensusReservationReceipt>,
    reservation_by_challenge: BTreeMap<Bytes32, Bytes32>,
    reservation_by_nullifier: BTreeMap<Bytes32, Bytes32>,
    capabilities: BTreeMap<Bytes32, ConsensusHoldingCapability>,
    capability_by_reservation: BTreeMap<Bytes32, Bytes32>,
    observed_time_floor: u64,
}

#[derive(Serialize, Deserialize)]
struct DurableConsensusAuthorityEnvelope {
    version: u16,
    state: DurableConsensusAuthorityState,
}

impl DurableConsensusAuthorityState {
    fn replay_journal(&self) -> Result<ConsensusAuthorityProjection, String> {
        if self.journal.len() > MAX_CONSENSUS_AUTHORITY_RECORDS {
            return Err("consensus authority journal exceeds its record ceiling".to_owned());
        }
        let mut projection = ConsensusAuthorityProjection::default();
        let mut previous = [0; 32];
        for (index, record) in self.journal.iter().enumerate() {
            let ordinal = u64::try_from(index)
                .map_err(|_| "consensus authority journal ordinal overflow".to_owned())?;
            if record.ordinal != ordinal || record.previous_digest != previous {
                return Err("consensus authority journal is not a dense hash chain".to_owned());
            }
            if record.observed_time_floor < projection.observed_time_floor {
                return Err("consensus authority observed-time floor moved backwards".to_owned());
            }
            let expected = consensus_authority_journal_digest(
                record.ordinal,
                record.previous_digest,
                record.observed_time_floor,
                &record.event,
            )?;
            if record.digest != expected {
                return Err("consensus authority journal digest mismatch".to_owned());
            }
            projection.observed_time_floor = record.observed_time_floor;
            match &record.event {
                ConsensusAuthorityJournalEvent::ReservationIssued { reservation } => {
                    let id = reservation.reservation_id();
                    if projection.reservations.contains_key(&id)
                        || projection
                            .reservation_by_challenge
                            .contains_key(&reservation.challenge_id())
                        || projection
                            .reservation_by_nullifier
                            .contains_key(&reservation.privilege_nullifier())
                    {
                        return Err(
                            "consensus authority reissues a reservation/challenge/nullifier"
                                .to_owned(),
                        );
                    }
                    let receipt = ConsensusReservationReceipt::from_durable_record(
                        reservation.clone(),
                        ConsensusAdmissionCheckpoint {
                            journal_len: ordinal
                                .checked_add(1)
                                .ok_or_else(|| "consensus checkpoint length overflow".to_owned())?,
                            journal_head: record.digest,
                            observed_time_floor: record.observed_time_floor,
                        },
                    );
                    projection
                        .reservation_by_challenge
                        .insert(reservation.challenge_id(), id);
                    projection
                        .reservation_by_nullifier
                        .insert(reservation.privilege_nullifier(), id);
                    projection.reservations.insert(id, receipt);
                }
                ConsensusAuthorityJournalEvent::CapabilityIssued {
                    reservation_id,
                    capability,
                } => {
                    let Some(receipt) = projection.reservations.get(reservation_id) else {
                        return Err(
                            "consensus capability precedes its exact reservation".to_owned()
                        );
                    };
                    if capability.reservation() != receipt.reservation()
                        || capability.trust() != TrustTier::ConsensusVerified
                        || capability.wallet() != receipt.reservation().wallet()
                        || capability.player() != receipt.reservation().player()
                        || capability.player_cell() != receipt.reservation().player_cell()
                        || capability.federation_id() != receipt.reservation().federation_id()
                        || projection
                            .capability_by_reservation
                            .insert(*reservation_id, capability.receipt_id())
                            .is_some()
                        || projection
                            .capabilities
                            .insert(capability.receipt_id(), capability.clone())
                            .is_some()
                    {
                        return Err(
                            "consensus capability/reservation binding is not one-to-one".to_owned()
                        );
                    }
                }
            }
            previous = record.digest;
        }
        if self.journal_head != previous
            || self.observed_time_floor != projection.observed_time_floor
        {
            return Err("consensus authority journal head/time floor mismatch".to_owned());
        }
        Ok(projection)
    }

    fn validate(&self) -> Result<(), String> {
        let projection = self.replay_journal()?;
        if self.reservations != projection.reservations
            || self.reservation_by_challenge != projection.reservation_by_challenge
            || self.reservation_by_nullifier != projection.reservation_by_nullifier
            || self.capabilities != projection.capabilities
            || self.capability_by_reservation != projection.capability_by_reservation
        {
            return Err("consensus authority indexes are not exact journal projections".to_owned());
        }
        Ok(())
    }

    fn append(
        &mut self,
        observed_time_floor: u64,
        event: ConsensusAuthorityJournalEvent,
    ) -> Result<ConsensusAdmissionCheckpoint, String> {
        if self.journal.len() >= MAX_CONSENSUS_AUTHORITY_RECORDS {
            return Err("consensus authority journal capacity exhausted".to_owned());
        }
        if observed_time_floor < self.observed_time_floor {
            return Err("consensus authority clock rollback refused".to_owned());
        }
        let ordinal = u64::try_from(self.journal.len())
            .map_err(|_| "consensus authority journal ordinal overflow".to_owned())?;
        let digest = consensus_authority_journal_digest(
            ordinal,
            self.journal_head,
            observed_time_floor,
            &event,
        )?;
        self.journal.push(ConsensusAuthorityJournalRecord {
            ordinal,
            previous_digest: self.journal_head,
            observed_time_floor,
            event,
            digest,
        });
        self.journal_head = digest;
        self.observed_time_floor = observed_time_floor;
        Ok(ConsensusAdmissionCheckpoint {
            journal_len: ordinal
                .checked_add(1)
                .ok_or_else(|| "consensus checkpoint length overflow".to_owned())?,
            journal_head: digest,
            observed_time_floor,
        })
    }
}

fn consensus_authority_journal_digest(
    ordinal: u64,
    previous_digest: Bytes32,
    observed_time_floor: u64,
    event: &ConsensusAuthorityJournalEvent,
) -> Result<Bytes32, String> {
    let event_bytes = postcard::to_stdvec(event)
        .map_err(|error| format!("consensus journal event encode failed: {error}"))?;
    let mut hash = Sha256::new();
    hash.update(CONSENSUS_AUTHORITY_JOURNAL_DOMAIN);
    hash.update(ordinal.to_be_bytes());
    hash.update(previous_digest);
    hash.update(observed_time_floor.to_be_bytes());
    hash.update(
        u64::try_from(event_bytes.len())
            .map_err(|_| "consensus journal event length overflow".to_owned())?
            .to_be_bytes(),
    );
    hash.update(event_bytes);
    Ok(hash.finalize().into())
}

fn consensus_reservation_static_eq(
    left: &ConsensusPrivilegeReservation,
    right: &ConsensusPrivilegeReservation,
) -> bool {
    left.reservation_id() == right.reservation_id()
        && left.challenge_id() == right.challenge_id()
        && left.wallet() == right.wallet()
        && left.player() == right.player()
        && left.player_cell() == right.player_cell()
        && left.federation_id() == right.federation_id()
        && left.intent() == right.intent()
        && left.privilege_nullifier() == right.privilege_nullifier()
}

fn consensus_capability_static_eq(
    left: &ConsensusHoldingCapability,
    right: &ConsensusHoldingCapability,
) -> bool {
    left.receipt_id() == right.receipt_id()
        && consensus_reservation_static_eq(left.reservation(), right.reservation())
        && left.evidence_grade() == right.evidence_grade()
        && left.token_account() == right.token_account()
        && left.token_program() == right.token_program()
        && left.evidence_digest() == right.evidence_digest()
        && left.anchor_epoch() == right.anchor_epoch()
        && left.anchor_stake_table_root() == right.anchor_stake_table_root()
        && left.require_poh() == right.require_poh()
        && left.external_checkpoint() == right.external_checkpoint()
}

struct RedbAdmissionStore {
    store: Arc<dregg_persist::PersistentStore>,
}

impl RedbAdmissionStore {
    fn new(store: Arc<dregg_persist::PersistentStore>) -> Self {
        Self { store }
    }

    fn load(&self) -> Result<DurableAdmissionState, String> {
        let Some(bytes) = self
            .store
            .get_config(ADMISSION_STATE_KEY)
            .map_err(|error| error.to_string())?
        else {
            if self.load_anchor()?.is_some() {
                return Err("durable admission state is missing behind its anchor".to_owned());
            }
            return Ok(DurableAdmissionState::default());
        };
        if bytes.len() > MAX_ADMISSION_STATE_BYTES {
            return Err("durable admission state exceeds its size ceiling".to_owned());
        }
        if let Ok(envelope) = postcard::from_bytes::<DurableAdmissionEnvelope>(&bytes) {
            if envelope.version == ADMISSION_STATE_VERSION {
                let canonical = postcard::to_stdvec(&envelope)
                    .map_err(|error| format!("encode failed: {error}"))?;
                if canonical != bytes {
                    return Err("durable admission state is not canonically encoded".to_owned());
                }
                envelope.state.validate()?;
                self.validate_or_advance_anchor(&envelope.state)?;
                return Ok(envelope.state);
            }
        }

        let legacy: DurableAdmissionEnvelopeV2 =
            postcard::from_bytes(&bytes).map_err(|error| format!("decode failed: {error}"))?;
        if legacy.version != 2 {
            return Err(format!(
                "unsupported durable admission version {}",
                legacy.version
            ));
        }
        if self.load_anchor()?.is_some() {
            return Err("legacy admission state cannot replace an anchored V3 lineage".to_owned());
        }
        let canonical = postcard::to_stdvec(&legacy)
            .map_err(|error| format!("legacy encode failed: {error}"))?;
        if canonical != bytes {
            return Err("legacy durable admission state is not canonically encoded".to_owned());
        }
        let migrated = Self::migrate_v2(legacy.state)?;
        self.save(&migrated)?;
        Ok(migrated)
    }

    fn migrate_v2(legacy: DurableAdmissionStateV2) -> Result<DurableAdmissionState, String> {
        let DurableAdmissionStateV2 {
            challenges,
            used_nonces,
            spent_challenges,
            capabilities,
            spent_capabilities,
        } = legacy;
        if used_nonces != challenges.values().map(Challenge::nonce).collect() {
            return Err("legacy durable admission nonce index is inconsistent".to_owned());
        }
        if !spent_capabilities
            .iter()
            .all(|id| capabilities.contains_key(id))
        {
            return Err("legacy durable admission spent capability is unknown".to_owned());
        }
        let mut migrated = DurableAdmissionState::default();
        for challenge in challenges.values() {
            migrated.append(AdmissionJournalEvent::ChallengeIssued {
                challenge: challenge.clone(),
            })?;
        }
        for capability in capabilities.values() {
            if !spent_challenges.contains(&capability.challenge_id()) {
                return Err("legacy capability has no spent challenge".to_owned());
            }
            migrated.append(AdmissionJournalEvent::CapabilityIssued {
                challenge_id: capability.challenge_id(),
                capability: capability.clone(),
            })?;
        }
        migrated.challenges = challenges;
        migrated.used_nonces = used_nonces;
        migrated.spent_challenges = spent_challenges;
        migrated.capabilities = capabilities;
        migrated.spent_capabilities = spent_capabilities;
        migrated.validate()?;
        Ok(migrated)
    }

    fn load_anchor(&self) -> Result<Option<DurableAdmissionAnchor>, String> {
        let Some(bytes) = self
            .store
            .get_config(ADMISSION_STATE_ANCHOR_KEY)
            .map_err(|error| error.to_string())?
        else {
            return Ok(None);
        };
        let anchor: DurableAdmissionAnchor = postcard::from_bytes(&bytes)
            .map_err(|error| format!("admission anchor decode failed: {error}"))?;
        let canonical = postcard::to_stdvec(&anchor)
            .map_err(|error| format!("admission anchor encode failed: {error}"))?;
        if canonical != bytes || anchor.version != ADMISSION_STATE_VERSION {
            return Err("durable admission anchor is noncanonical or unsupported".to_owned());
        }
        Ok(Some(anchor))
    }

    fn store_anchor(&self, anchor: DurableAdmissionAnchor) -> Result<(), String> {
        let bytes = postcard::to_stdvec(&anchor)
            .map_err(|error| format!("admission anchor encode failed: {error}"))?;
        self.store
            .set_config(ADMISSION_STATE_ANCHOR_KEY, &bytes)
            .map_err(|error| error.to_string())
    }

    fn validate_or_advance_anchor(&self, state: &DurableAdmissionState) -> Result<(), String> {
        let current = DurableAdmissionAnchor::from_state(state)?;
        let Some(anchor) = self.load_anchor()? else {
            // Empty legacy databases and the narrow crash window after the
            // first V3 state write acquire their anchor from the fully audited
            // journal, never from an unaudited live snapshot.
            self.store_anchor(current)?;
            return Ok(());
        };
        if anchor == current {
            return Ok(());
        }
        if anchor.journal_len > current.journal_len {
            return Err("durable admission state rolled back behind its anchor".to_owned());
        }
        let anchored_head = if anchor.journal_len == 0 {
            [0; 32]
        } else {
            let index = usize::try_from(anchor.journal_len - 1)
                .map_err(|_| "durable admission anchor length overflow".to_owned())?;
            state
                .journal
                .get(index)
                .map(|record| record.digest)
                .ok_or_else(|| "durable admission state rolled back behind its anchor".to_owned())?
        };
        if anchored_head != anchor.journal_head {
            return Err("durable admission state diverges from its anchored prefix".to_owned());
        }
        // `save` writes the complete audited state first and its anchor second.
        // A crash between those commits is recovered only when the old anchor
        // is an exact prefix of the new valid lineage.
        self.store_anchor(current)
    }

    fn save(&self, state: &DurableAdmissionState) -> Result<(), String> {
        state.validate()?;
        let bytes = postcard::to_stdvec(&DurableAdmissionEnvelope {
            version: ADMISSION_STATE_VERSION,
            state: state.clone(),
        })
        .map_err(|error| format!("encode failed: {error}"))?;
        if bytes.len() > MAX_ADMISSION_STATE_BYTES {
            return Err("durable admission state exceeds its size ceiling".to_owned());
        }
        self.store
            .set_config(ADMISSION_STATE_KEY, &bytes)
            .map_err(|error| error.to_string())?;
        self.store_anchor(DurableAdmissionAnchor::from_state(state)?)
    }

    fn mutate<T>(
        &mut self,
        change: impl FnOnce(&mut DurableAdmissionState) -> Result<T, String>,
    ) -> Result<T, String> {
        let mut state = self.load()?;
        let original_journal = state.journal.clone();
        let result = change(&mut state)?;
        if !state.journal.starts_with(&original_journal) {
            return Err("durable admission journal mutation or rollback refused".to_owned());
        }
        self.save(&state)?;
        Ok(result)
    }
}

impl AdmissionStore for RedbAdmissionStore {
    type Error = String;

    fn insert_challenge_once(
        &mut self,
        nonce: Bytes32,
        challenge: Challenge,
    ) -> Result<ChallengeIssue, Self::Error> {
        self.mutate(|state| {
            state.prune_expired(challenge.issued_at());
            let projection = state.replay_journal()?;
            // Live issued authority is never evicted by unrelated traffic.
            // At capacity the newcomer loses and can retry after expiry.
            if state.challenges.len() >= MAX_LIVE_CHALLENGES
                || state.journal.len() >= MAX_ADMISSION_JOURNAL_RECORDS
            {
                return Ok(ChallengeIssue::CapacityExceeded);
            }
            if projection.used_nonces.contains(&nonce)
                || projection.challenges.contains_key(&challenge.id())
            {
                return Ok(ChallengeIssue::Replay);
            }
            let challenge_id = challenge.id();
            state.append(AdmissionJournalEvent::ChallengeIssued {
                challenge: challenge.clone(),
            })?;
            state.used_nonces.insert(nonce);
            state.challenges.insert(challenge_id, challenge);
            Ok(ChallengeIssue::Issued)
        })
    }

    fn challenge(&self, id: &Bytes32) -> Result<Option<Challenge>, Self::Error> {
        self.load()?.historical_challenge(id)
    }

    fn challenge_consumed(&self, id: &Bytes32) -> Result<bool, Self::Error> {
        Ok(self.load()?.replay_journal()?.spent_challenges.contains(id))
    }

    fn issue_capability_once(
        &mut self,
        challenge_id: Bytes32,
        capability: HoldingCapability,
    ) -> Result<CapabilityIssue, Self::Error> {
        self.mutate(|state| {
            state.prune_expired(capability.issued_at());
            let projection = state.replay_journal()?;
            if !projection.challenges.contains_key(&challenge_id) {
                return Ok(CapabilityIssue::UnknownChallenge);
            }
            if projection.spent_challenges.contains(&challenge_id) {
                return Ok(CapabilityIssue::ChallengeReplay);
            }
            if capability.challenge_id() != challenge_id {
                return Ok(CapabilityIssue::ChallengeMismatch);
            }
            if state.capabilities.len() >= MAX_LIVE_CAPABILITIES
                || state.journal.len() >= MAX_ADMISSION_JOURNAL_RECORDS
            {
                return Ok(CapabilityIssue::CapacityExceeded);
            }
            let id = capability.receipt_id();
            if projection.capabilities.contains_key(&id) {
                return Ok(CapabilityIssue::CapabilityCollision);
            }
            state.append(AdmissionJournalEvent::CapabilityIssued {
                challenge_id,
                capability: capability.clone(),
            })?;
            state.spent_challenges.insert(challenge_id);
            state.capabilities.insert(id, capability);
            Ok(CapabilityIssue::Issued)
        })
    }

    fn capability(&self, id: &Bytes32) -> Result<Option<HoldingCapability>, Self::Error> {
        self.load()?.historical_capability(id)
    }

    fn capability_consumed(&self, id: &Bytes32) -> Result<bool, Self::Error> {
        if self
            .store
            .load_poa_holding_consumption(id)
            .map_err(|error| error.to_string())?
            .is_some()
        {
            return Ok(true);
        }
        Ok(self.load()?.spent_capabilities.contains(id))
    }

    fn consume_capability_once(&mut self, _id: Bytes32) -> Result<CapabilityUse, Self::Error> {
        Err("PoA holding capabilities may only be consumed by finalized-turn weld".to_owned())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use axum::body::Body;
    use axum::http::Request;
    use ed25519_dalek::{Signer as _, SigningKey};
    use http_body_util::BodyExt as _;
    use tower::ServiceExt as _;

    #[derive(Clone)]
    struct FakeRpc {
        endpoint_id: Bytes32,
        wallet: Bytes32,
        amount: u64,
        slot: u64,
    }

    impl SolanaHoldingRpc for FakeRpc {
        fn endpoint_id(&self) -> Result<Bytes32, String> {
            Ok(self.endpoint_id)
        }

        fn finalized_slot(&self) -> RpcFuture<u64> {
            let slot = self.slot;
            Box::pin(async move { Ok(slot) })
        }

        fn holding_snapshot(&self, challenge: Challenge) -> RpcFuture<RpcAccountSet> {
            let this = self.clone();
            Box::pin(async move {
                let config = GateConfig::path_of_angels_mainnet([7; 32], this.endpoint_id);
                let slot = this.slot + 1;
                let mut data = vec![0u8; 165];
                data[..32].copy_from_slice(&config.mint);
                data[32..64].copy_from_slice(&this.wallet);
                data[64..72].copy_from_slice(&this.amount.to_le_bytes());
                data[108] = 1;
                Ok(RpcAccountSet {
                    endpoint_id: this.endpoint_id,
                    genesis_hash: config.genesis_hash,
                    commitment: Commitment::Finalized,
                    requested_min_context_slot: challenge.min_context_slot(),
                    context_slot: slot,
                    accounts: vec![RpcTokenAccount {
                        address: [44; 32],
                        account: dregg_pay::watcher::FetchedAccount {
                            data,
                            owner_program: config.token_program,
                            slot,
                        },
                    }],
                })
            })
        }
    }

    #[derive(Clone)]
    struct NoSnapshotRpc {
        endpoint_id: Bytes32,
        slot: u64,
    }

    impl SolanaHoldingRpc for NoSnapshotRpc {
        fn endpoint_id(&self) -> Result<Bytes32, String> {
            Ok(self.endpoint_id)
        }

        fn finalized_slot(&self) -> RpcFuture<u64> {
            let slot = self.slot;
            Box::pin(async move { Ok(slot) })
        }

        fn holding_snapshot(&self, _challenge: Challenge) -> RpcFuture<RpcAccountSet> {
            panic!("bad wallet signatures must be refused before the holding RPC")
        }
    }

    async fn configured_state() -> (NodeState, tempfile::TempDir) {
        let dir = tempfile::tempdir().expect("tempdir");
        let state = NodeState::new(dir.path(), vec![]).expect("state");
        {
            let mut node = state.write().await;
            node.federation_configured = true;
            node.federation_id = [7; 32];
        }
        (state, dir)
    }

    async fn json_request(
        app: Router,
        method: &str,
        uri: &str,
        body: serde_json::Value,
    ) -> (StatusCode, serde_json::Value) {
        let response = app
            .oneshot(
                Request::builder()
                    .method(method)
                    .uri(uri)
                    .header("content-type", "application/json")
                    .extension(ConnectInfo(SocketAddr::from(([127, 0, 0, 1], 31337))))
                    .body(Body::from(body.to_string()))
                    .expect("request"),
            )
            .await
            .expect("response");
        let status = response.status();
        let bytes = response
            .into_body()
            .collect()
            .await
            .expect("body")
            .to_bytes();
        let json = serde_json::from_slice(&bytes).unwrap_or_else(|_| serde_json::json!({}));
        (status, json)
    }

    #[tokio::test]
    async fn challenge_verify_status_uses_server_rpc_and_survives_reopen() {
        let key = SigningKey::from_bytes(&[3; 32]);
        let wallet = key.verifying_key().to_bytes();
        let player = SigningKey::from_bytes(&[0x51; 32])
            .verifying_key()
            .to_bytes();
        let rpc = FakeRpc {
            endpoint_id: [8; 32],
            wallet,
            amount: 17,
            slot: 1000,
        };
        let (state, dir) = configured_state().await;
        let app = routes_with_rpc(rpc.clone()).with_state(state.clone());
        let (status, challenge) = json_request(
            app.clone(),
            "POST",
            "/api/poa/holding/challenge",
            serde_json::json!({
                "wallet": encode_pubkey(&wallet),
                "player": encode_pubkey(&player),
            }),
        )
        .await;
        assert_eq!(status, StatusCode::CREATED, "{challenge}");
        let message = base64::engine::general_purpose::STANDARD
            .decode(
                challenge["signing_message_base64"]
                    .as_str()
                    .expect("message"),
            )
            .expect("message base64");
        assert!(
            message.len() > 32 * 8,
            "challenge must commit its full context"
        );
        let signature = key.sign(&message).to_bytes();
        let (status, capability) = json_request(
            app,
            "POST",
            "/api/poa/holding/verify",
            serde_json::json!({
                "challenge_id": challenge["challenge_id"],
                "signature_base64": base64::engine::general_purpose::STANDARD.encode(signature),
            }),
        )
        .await;
        assert_eq!(status, StatusCode::OK, "{capability}");
        assert!(capability.get("raw_balance").is_none());
        assert_eq!(capability["governance_weight_bearing"], false);
        assert_eq!(capability["player"], encode_pubkey(&player));
        drop(state);

        let reopened = NodeState::new(dir.path(), vec![]).expect("reopen");
        {
            let mut node = reopened.write().await;
            node.federation_configured = true;
            node.federation_id = [7; 32];
        }
        let receipt = capability["receipt_id"].as_str().expect("receipt");
        let reopened_app = routes_with_rpc(rpc).with_state(reopened);
        let (replay_status, replay_body) = json_request(
            reopened_app.clone(),
            "POST",
            "/api/poa/holding/verify",
            serde_json::json!({
                "challenge_id": challenge["challenge_id"],
                "signature_base64": base64::engine::general_purpose::STANDARD.encode(signature),
            }),
        )
        .await;
        assert_eq!(replay_status, StatusCode::CONFLICT, "{replay_body}");
        let response = reopened_app
            .oneshot(
                Request::builder()
                    .uri(format!("/api/poa/holding/status/{receipt}"))
                    .extension(ConnectInfo(SocketAddr::from(([127, 0, 0, 1], 31337))))
                    .body(Body::empty())
                    .expect("request"),
            )
            .await
            .expect("status response");
        assert_eq!(response.status(), StatusCode::OK);
        let bytes = response
            .into_body()
            .collect()
            .await
            .expect("body")
            .to_bytes();
        let status: serde_json::Value = serde_json::from_slice(&bytes).expect("status json");
        assert_eq!(status["state"], "active");
        for private_field in [
            "raw_balance",
            "wallet",
            "player",
            "player_cell",
            "mint",
            "snapshot_slot",
            "issued_at",
        ] {
            assert!(
                status.get(private_field).is_none(),
                "public status leaked {private_field}"
            );
        }
    }

    #[tokio::test]
    async fn durable_store_prunes_expired_rows_without_disturbing_live_status() {
        let dir = tempfile::tempdir().expect("tempdir");
        let path = dir.path().join("admission.redb");
        let store = Arc::new(dregg_persist::PersistentStore::open(&path).expect("store"));
        let config = GateConfig::path_of_angels_mainnet([7; 32], [8; 32]);
        let key = SigningKey::from_bytes(&[3; 32]);
        let wallet = key.verifying_key().to_bytes();
        let player = SigningKey::from_bytes(&[0x51; 32])
            .verifying_key()
            .to_bytes();
        let old_challenge = {
            let mut gate = Gate::with_store(RedbAdmissionStore::new(Arc::clone(&store)));
            gate.issue(&config, wallet, player, [9; 32], 1000, 10)
                .expect("old challenge")
        };
        let snapshot = FakeRpc {
            endpoint_id: [8; 32],
            wallet,
            amount: 17,
            slot: 1000,
        }
        .holding_snapshot(old_challenge.clone())
        .await
        .expect("snapshot");
        let observation =
            validate_rpc_snapshot(&config, &old_challenge, &snapshot).expect("observation");
        let binding = dregg_governance::holding_weight::OwnerBinding {
            voter: old_challenge.player(),
            sig: key.sign(&old_challenge.signing_message()).to_bytes(),
        };
        let old_capability = {
            let mut gate = Gate::with_store(RedbAdmissionStore::new(Arc::clone(&store)));
            gate.admit_beta(&config, &old_challenge, &binding, observation, 11)
                .expect("capability")
        };
        assert!(matches!(
            Gate::with_store(RedbAdmissionStore::new(Arc::clone(&store)))
                .capability_status(&old_capability.receipt_id(), 12)
                .expect("live status"),
            CapabilityStatus::Active(_)
        ));

        let current_challenge = {
            let mut gate = Gate::with_store(RedbAdmissionStore::new(Arc::clone(&store)));
            gate.issue(&config, wallet, player, [10; 32], 2000, 1000)
                .expect("current challenge")
        };
        let durable = RedbAdmissionStore::new(Arc::clone(&store))
            .load()
            .expect("durable state");
        assert_eq!(durable.challenges.len(), 1);
        assert_eq!(durable.used_nonces.len(), 1);
        assert!(durable.challenges.contains_key(&current_challenge.id()));
        assert!(durable.capabilities.is_empty());
        assert!(durable.spent_challenges.is_empty());
        assert!(durable.spent_capabilities.is_empty());
        assert_eq!(durable.journal.len(), 3);

        let lineage = durable.replay_journal().expect("complete lineage");
        assert_eq!(
            lineage.challenges.get(&old_challenge.id()),
            Some(&old_challenge)
        );
        assert_eq!(
            lineage.capabilities.get(&old_capability.receipt_id()),
            Some(&old_capability)
        );
        assert!(lineage.spent_challenges.contains(&old_challenge.id()));

        // Expiring the live cache must not turn an issued receipt into an
        // unknown one or reopen its consumed challenge, including after the
        // redb process image is closed and reopened.
        drop(durable);
        drop(store);
        let reopened = Arc::new(dregg_persist::PersistentStore::open(&path).expect("reopen"));
        let reopened_gate = Gate::with_store(RedbAdmissionStore::new(Arc::clone(&reopened)));
        assert!(matches!(
            reopened_gate
                .capability_status(&old_capability.receipt_id(), 1000)
                .expect("historical status"),
            CapabilityStatus::Expired(capability) if capability == old_capability
        ));
        assert_eq!(
            reopened_gate.preflight_beta(&config, &old_challenge, &binding, 11),
            Err(GateError::ChallengeReplay)
        );
    }

    #[test]
    fn admission_journal_refuses_state_rollback_and_frame_corruption() {
        let store = Arc::new(dregg_persist::PersistentStore::open_in_memory().expect("store"));
        let config = GateConfig::path_of_angels_mainnet([7; 32], [8; 32]);
        let wallet = SigningKey::from_bytes(&[3; 32]).verifying_key().to_bytes();
        let player = SigningKey::from_bytes(&[0x51; 32])
            .verifying_key()
            .to_bytes();
        let first = Gate::with_store(RedbAdmissionStore::new(Arc::clone(&store)))
            .issue(&config, wallet, player, [9; 32], 1000, 10)
            .expect("first challenge");
        let old_state = store
            .get_config(ADMISSION_STATE_KEY)
            .expect("old state read")
            .expect("old state");
        let old_anchor = store
            .get_config(ADMISSION_STATE_ANCHOR_KEY)
            .expect("old anchor read")
            .expect("old anchor");

        Gate::with_store(RedbAdmissionStore::new(Arc::clone(&store)))
            .issue(&config, wallet, player, [10; 32], 1001, 11)
            .expect("second challenge");
        let latest_state = store
            .get_config(ADMISSION_STATE_KEY)
            .expect("latest state read")
            .expect("latest state");
        let latest_anchor = store
            .get_config(ADMISSION_STATE_ANCHOR_KEY)
            .expect("anchor read")
            .expect("anchor");

        // `save` orders the atomic redb state replacement before the anchor
        // replacement. Simulate a crash in that one inter-transaction window:
        // recovery may advance the old anchor only because it is an exact
        // prefix of the fully decoded, canonically rehashed new journal.
        store
            .set_config(ADMISSION_STATE_ANCHOR_KEY, &old_anchor)
            .expect("simulate pre-anchor crash");
        RedbAdmissionStore::new(Arc::clone(&store))
            .load()
            .expect("exact state extension recovers its lagging anchor");
        assert_eq!(
            store
                .get_config(ADMISSION_STATE_ANCHOR_KEY)
                .expect("recovered anchor read")
                .expect("recovered anchor"),
            latest_anchor
        );

        store
            .set_config(ADMISSION_STATE_KEY, &old_state)
            .expect("simulate state-only rollback");
        let rollback = RedbAdmissionStore::new(Arc::clone(&store))
            .load()
            .expect_err("state behind monotonic anchor must refuse");
        assert!(rollback.contains("rolled back"), "{rollback}");

        store
            .set_config(ADMISSION_STATE_KEY, &latest_state)
            .expect("restore latest state");
        store
            .set_config(ADMISSION_STATE_ANCHOR_KEY, &latest_anchor)
            .expect("restore latest anchor");
        let mut envelope: DurableAdmissionEnvelope =
            postcard::from_bytes(&latest_state).expect("decode latest envelope");
        assert_eq!(
            envelope.state.journal[0].event,
            AdmissionJournalEvent::ChallengeIssued { challenge: first }
        );
        envelope.state.journal[0].digest[0] ^= 1;
        let corrupted = postcard::to_stdvec(&envelope).expect("encode corruption");
        store
            .set_config(ADMISSION_STATE_KEY, &corrupted)
            .expect("install corrupt frame");
        let corruption = RedbAdmissionStore::new(store)
            .load()
            .expect_err("corrupt journal frame must refuse");
        assert!(corruption.contains("digest mismatch"), "{corruption}");
    }

    #[test]
    fn admission_journal_refuses_reorder_and_live_index_invention() {
        let store = Arc::new(dregg_persist::PersistentStore::open_in_memory().expect("store"));
        let config = GateConfig::path_of_angels_mainnet([7; 32], [8; 32]);
        let wallet = SigningKey::from_bytes(&[3; 32]).verifying_key().to_bytes();
        let player = SigningKey::from_bytes(&[0x51; 32])
            .verifying_key()
            .to_bytes();
        for (nonce, now) in [([9; 32], 10), ([10; 32], 11)] {
            Gate::with_store(RedbAdmissionStore::new(Arc::clone(&store)))
                .issue(&config, wallet, player, nonce, 1000, now)
                .expect("challenge");
        }
        let bytes = store
            .get_config(ADMISSION_STATE_KEY)
            .expect("state read")
            .expect("state");
        let mut envelope: DurableAdmissionEnvelope =
            postcard::from_bytes(&bytes).expect("decode state");
        envelope.state.journal.swap(0, 1);
        store
            .set_config(
                ADMISSION_STATE_KEY,
                &postcard::to_stdvec(&envelope).expect("encode reorder"),
            )
            .expect("install reorder");
        assert!(
            RedbAdmissionStore::new(Arc::clone(&store))
                .load()
                .expect_err("reordered journal must refuse")
                .contains("ordinal")
        );

        let mut envelope: DurableAdmissionEnvelope =
            postcard::from_bytes(&bytes).expect("decode clean state");
        let invented = Gate::new()
            .issue(&config, wallet, player, [88; 32], 1000, 12)
            .expect("detached challenge");
        envelope
            .state
            .challenges
            .insert(invented.id(), invented.clone());
        envelope.state.used_nonces.insert(invented.nonce());
        store
            .set_config(
                ADMISSION_STATE_KEY,
                &postcard::to_stdvec(&envelope).expect("encode invention"),
            )
            .expect("install invention");
        assert!(
            RedbAdmissionStore::new(store)
                .load()
                .expect_err("live snapshot invention must refuse")
                .contains("invents")
        );
    }

    #[tokio::test]
    async fn legacy_v2_migrates_only_complete_live_authority_into_v3_lineage() {
        let config = GateConfig::path_of_angels_mainnet([7; 32], [8; 32]);
        let key = SigningKey::from_bytes(&[3; 32]);
        let wallet = key.verifying_key().to_bytes();
        let player = SigningKey::from_bytes(&[0x51; 32])
            .verifying_key()
            .to_bytes();
        let mut source = Gate::new();
        let challenge = source
            .issue(&config, wallet, player, [9; 32], 1000, 10)
            .expect("challenge");
        let observation = validate_rpc_snapshot(
            &config,
            &challenge,
            &FakeRpc {
                endpoint_id: [8; 32],
                wallet,
                amount: 17,
                slot: 1000,
            }
            .holding_snapshot(challenge.clone())
            .await
            .expect("snapshot"),
        )
        .expect("observation");
        let binding = dregg_governance::holding_weight::OwnerBinding {
            voter: challenge.player(),
            sig: key.sign(&challenge.signing_message()).to_bytes(),
        };
        let capability = source
            .admit_beta(&config, &challenge, &binding, observation, 11)
            .expect("capability");
        let legacy = DurableAdmissionEnvelopeV2 {
            version: 2,
            state: DurableAdmissionStateV2 {
                challenges: BTreeMap::from([(challenge.id(), challenge.clone())]),
                used_nonces: BTreeSet::from([challenge.nonce()]),
                spent_challenges: BTreeSet::from([challenge.id()]),
                capabilities: BTreeMap::from([(capability.receipt_id(), capability.clone())]),
                spent_capabilities: BTreeSet::new(),
            },
        };
        let store = Arc::new(dregg_persist::PersistentStore::open_in_memory().expect("store"));
        store
            .set_config(
                ADMISSION_STATE_KEY,
                &postcard::to_stdvec(&legacy).expect("legacy encode"),
            )
            .expect("legacy install");
        let migrated = RedbAdmissionStore::new(Arc::clone(&store))
            .load()
            .expect("migration");
        assert_eq!(migrated.journal.len(), 2);
        assert_eq!(
            migrated
                .historical_challenge(&challenge.id())
                .expect("challenge lookup"),
            Some(challenge)
        );
        assert_eq!(
            migrated
                .historical_capability(&capability.receipt_id())
                .expect("capability lookup"),
            Some(capability)
        );
        assert!(
            store
                .get_config(ADMISSION_STATE_ANCHOR_KEY)
                .expect("anchor read")
                .is_some()
        );
    }

    #[test]
    fn admission_journal_capacity_refuses_without_evicting_its_prefix() {
        let config = GateConfig::path_of_angels_mainnet([7; 32], [8; 32]);
        let challenge = Gate::new()
            .issue(
                &config,
                SigningKey::from_bytes(&[3; 32]).verifying_key().to_bytes(),
                SigningKey::from_bytes(&[0x51; 32])
                    .verifying_key()
                    .to_bytes(),
                [9; 32],
                1000,
                10,
            )
            .expect("challenge");
        let event = AdmissionJournalEvent::ChallengeIssued { challenge };
        let mut state = DurableAdmissionState::default();
        state.append(event.clone()).expect("first frame");
        let first = state.journal[0].clone();
        state
            .journal
            .resize(MAX_ADMISSION_JOURNAL_RECORDS, first.clone());
        let before = state.journal.clone();
        assert_eq!(
            state.append(event),
            Err("durable admission journal capacity exhausted".to_owned())
        );
        assert_eq!(state.journal, before);
        assert_eq!(state.journal[0], first);
    }

    #[tokio::test]
    async fn unknown_challenge_short_signature_and_unknown_receipt_refuse() {
        let (state, _dir) = configured_state().await;
        let rpc = FakeRpc {
            endpoint_id: [8; 32],
            wallet: [3; 32],
            amount: 1,
            slot: 1000,
        };
        let app = routes_with_rpc(rpc).with_state(state);
        let (status, body) = json_request(
            app.clone(),
            "POST",
            "/api/poa/holding/verify",
            serde_json::json!({
                "challenge_id": encode_id(&[9; 32]),
                "signature_base64": base64::engine::general_purpose::STANDARD.encode([1; 7]),
            }),
        )
        .await;
        assert_eq!(status, StatusCode::BAD_REQUEST, "{body}");
        let response = app
            .oneshot(
                Request::builder()
                    .uri(format!("/api/poa/holding/status/{}", encode_id(&[9; 32])))
                    .extension(ConnectInfo(SocketAddr::from(([127, 0, 0, 1], 31337))))
                    .body(Body::empty())
                    .expect("request"),
            )
            .await
            .expect("response");
        assert_eq!(response.status(), StatusCode::NOT_FOUND);
    }

    #[tokio::test]
    async fn verify_schema_refuses_a_client_asserted_balance() {
        let (state, _dir) = configured_state().await;
        let rpc = FakeRpc {
            endpoint_id: [8; 32],
            wallet: [3; 32],
            amount: 1,
            slot: 1000,
        };
        let (status, body) = json_request(
            routes_with_rpc(rpc).with_state(state),
            "POST",
            "/api/poa/holding/verify",
            serde_json::json!({
                "challenge_id": encode_id(&[9; 32]),
                "signature_base64": base64::engine::general_purpose::STANDARD.encode([1; 64]),
                "balance": u64::MAX,
            }),
        )
        .await;
        assert_eq!(status, StatusCode::UNPROCESSABLE_ENTITY, "{body}");
    }

    #[tokio::test]
    async fn bad_wallet_signature_is_refused_before_holding_rpc() {
        let key = SigningKey::from_bytes(&[3; 32]);
        let wallet = key.verifying_key().to_bytes();
        let player = SigningKey::from_bytes(&[0x51; 32])
            .verifying_key()
            .to_bytes();
        let rpc = NoSnapshotRpc {
            endpoint_id: [8; 32],
            slot: 1000,
        };
        let (state, _dir) = configured_state().await;
        let app = routes_with_rpc(rpc).with_state(state);
        let (status, challenge) = json_request(
            app.clone(),
            "POST",
            "/api/poa/holding/challenge",
            serde_json::json!({
                "wallet": encode_pubkey(&wallet),
                "player": encode_pubkey(&player),
            }),
        )
        .await;
        assert_eq!(status, StatusCode::CREATED, "{challenge}");
        let (status, body) = json_request(
            app,
            "POST",
            "/api/poa/holding/verify",
            serde_json::json!({
                "challenge_id": challenge["challenge_id"],
                "signature_base64": base64::engine::general_purpose::STANDARD.encode([1; 64]),
            }),
        )
        .await;
        assert_eq!(status, StatusCode::FORBIDDEN, "{body}");
        assert_eq!(body["code"], "bad_wallet_signature");
    }

    #[test]
    fn rpc_decoder_refuses_json_parsed_or_malformed_account_data() {
        let result = serde_json::json!({
            "context": { "slot": 10 },
            "value": [{
                "pubkey": encode_pubkey(&[4; 32]),
                "account": {
                    "owner": encode_pubkey(&[5; 32]),
                    "data": { "parsed": { "clientAmount": u64::MAX } }
                }
            }]
        });
        assert!(decode_token_accounts_response(result, [1; 32], [2; 32], 9).is_err());
    }

    #[test]
    fn rpc_decoder_preserves_raw_token_2022_evidence_for_the_gate() {
        let config = GateConfig::path_of_angels_mainnet([7; 32], [8; 32]);
        let wallet = SigningKey::from_bytes(&[3; 32]).verifying_key().to_bytes();
        let player = SigningKey::from_bytes(&[0x51; 32])
            .verifying_key()
            .to_bytes();
        let challenge = Gate::new()
            .issue(&config, wallet, player, [9; 32], 1000, 10)
            .expect("challenge");
        let mut account_data = vec![0u8; 165];
        account_data[..32].copy_from_slice(&config.mint);
        account_data[32..64].copy_from_slice(&wallet);
        account_data[64..72].copy_from_slice(&17u64.to_le_bytes());
        account_data[108] = 1;
        let result = serde_json::json!({
            "context": { "slot": 1001 },
            "value": [{
                "pubkey": encode_pubkey(&[44; 32]),
                "account": {
                    "owner": encode_pubkey(&config.token_program),
                    "data": [
                        base64::engine::general_purpose::STANDARD.encode(&account_data),
                        "base64"
                    ]
                }
            }]
        });
        let decoded = decode_token_accounts_response(
            result,
            config.rpc_endpoint_id,
            config.genesis_hash,
            challenge.min_context_slot(),
        )
        .expect("raw RPC account set");
        validate_rpc_snapshot(&config, &challenge, &decoded)
            .expect("exact Token-2022 evidence must pass the canonical gate");
    }

    #[test]
    fn wire_ids_and_wallet_signatures_require_canonical_base64() {
        assert_eq!(decode_id(&encode_id(&[7; 32]), "bad").expect("id"), [7; 32]);
        assert!(decode_id(&format!("{}=", encode_id(&[7; 32])), "bad").is_err());

        let canonical = base64::engine::general_purpose::STANDARD.encode([1; 64]);
        assert_eq!(decode_signature(&canonical).expect("signature"), [1; 64]);
        let mut noncanonical = canonical.into_bytes();
        let low_bits = noncanonical.len() - 3;
        noncanonical[low_bits] = if noncanonical[low_bits] == b'Q' {
            b'R'
        } else {
            b'B'
        };
        assert!(decode_signature(std::str::from_utf8(&noncanonical).expect("ascii")).is_err());
    }

    #[tokio::test]
    async fn production_router_registers_the_status_route() {
        let (state, _dir) = configured_state().await;
        let recorder = metrics_exporter_prometheus::PrometheusBuilder::new().build_recorder();
        let response = crate::api::router_with_cors(
            state,
            false,
            recorder.handle(),
            std::collections::HashSet::new(),
        )
        .oneshot(
            Request::builder()
                .uri(format!("/api/poa/holding/status/{}", encode_id(&[9; 32])))
                .extension(ConnectInfo(SocketAddr::from(([127, 0, 0, 1], 31337))))
                .body(Body::empty())
                .expect("request"),
        )
        .await
        .expect("response");
        assert_eq!(response.status(), StatusCode::NOT_FOUND);
    }
}
