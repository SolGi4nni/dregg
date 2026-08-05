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
    ChallengeIssue, Commitment, DREGG_MINT_BASE58, Gate, GateConfig, GateError, HoldingCapability,
    RpcAccountSet, RpcTokenAccount, TrustTier, decode_pubkey, encode_pubkey, validate_rpc_snapshot,
};
use serde::{Deserialize, Serialize};
use sha2::{Digest as _, Sha256};
use tokio::sync::Semaphore;

use crate::api::RateLimiter;
use crate::state::NodeState;

/// V1 intentionally remains unread: it did not bind a capability to a Dregg
/// player and therefore can never authorize sponsorship.
const ADMISSION_STATE_KEY: &str = "poa_dregg_holding_admission_v2";
const ADMISSION_STATE_VERSION: u16 = 2;
const MAX_ADMISSION_STATE_BYTES: usize = 8 * 1024 * 1024;
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

#[derive(Default, Serialize, Deserialize)]
struct DurableAdmissionState {
    challenges: BTreeMap<Bytes32, Challenge>,
    used_nonces: BTreeSet<Bytes32>,
    spent_challenges: BTreeSet<Bytes32>,
    capabilities: BTreeMap<Bytes32, HoldingCapability>,
    spent_capabilities: BTreeSet<Bytes32>,
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
}

#[derive(Serialize, Deserialize)]
struct DurableAdmissionEnvelope {
    version: u16,
    state: DurableAdmissionState,
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
            return Ok(DurableAdmissionState::default());
        };
        if bytes.len() > MAX_ADMISSION_STATE_BYTES {
            return Err("durable admission state exceeds its size ceiling".to_owned());
        }
        let envelope: DurableAdmissionEnvelope =
            postcard::from_bytes(&bytes).map_err(|error| format!("decode failed: {error}"))?;
        if envelope.version != ADMISSION_STATE_VERSION {
            return Err(format!(
                "unsupported durable admission version {}",
                envelope.version
            ));
        }
        Ok(envelope.state)
    }

    fn save(&self, state: DurableAdmissionState) -> Result<(), String> {
        let bytes = postcard::to_stdvec(&DurableAdmissionEnvelope {
            version: ADMISSION_STATE_VERSION,
            state,
        })
        .map_err(|error| format!("encode failed: {error}"))?;
        if bytes.len() > MAX_ADMISSION_STATE_BYTES {
            return Err("durable admission state exceeds its size ceiling".to_owned());
        }
        self.store
            .set_config(ADMISSION_STATE_KEY, &bytes)
            .map_err(|error| error.to_string())
    }

    fn mutate<T>(
        &mut self,
        change: impl FnOnce(&mut DurableAdmissionState) -> T,
    ) -> Result<T, String> {
        let mut state = self.load()?;
        let result = change(&mut state);
        self.save(state)?;
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
            // Live issued authority is never evicted by unrelated traffic.
            // At capacity the newcomer loses and can retry after expiry.
            if state.challenges.len() >= MAX_LIVE_CHALLENGES {
                return ChallengeIssue::CapacityExceeded;
            }
            if !state.used_nonces.insert(nonce) || state.challenges.contains_key(&challenge.id()) {
                return ChallengeIssue::Replay;
            }
            let challenge_id = challenge.id();
            state.challenges.insert(challenge_id, challenge);
            ChallengeIssue::Issued
        })
    }

    fn challenge(&self, id: &Bytes32) -> Result<Option<Challenge>, Self::Error> {
        Ok(self.load()?.challenges.get(id).cloned())
    }

    fn challenge_consumed(&self, id: &Bytes32) -> Result<bool, Self::Error> {
        Ok(self.load()?.spent_challenges.contains(id))
    }

    fn issue_capability_once(
        &mut self,
        challenge_id: Bytes32,
        capability: HoldingCapability,
    ) -> Result<CapabilityIssue, Self::Error> {
        self.mutate(|state| {
            state.prune_expired(capability.issued_at());
            if !state.challenges.contains_key(&challenge_id) {
                return CapabilityIssue::UnknownChallenge;
            }
            if state.spent_challenges.contains(&challenge_id) {
                return CapabilityIssue::ChallengeReplay;
            }
            if capability.challenge_id() != challenge_id {
                return CapabilityIssue::ChallengeMismatch;
            }
            if state.capabilities.len() >= MAX_LIVE_CAPABILITIES {
                return CapabilityIssue::CapacityExceeded;
            }
            let id = capability.receipt_id();
            if state.capabilities.contains_key(&id) {
                return CapabilityIssue::CapabilityCollision;
            }
            state.spent_challenges.insert(challenge_id);
            state.capabilities.insert(id, capability);
            CapabilityIssue::Issued
        })
    }

    fn capability(&self, id: &Bytes32) -> Result<Option<HoldingCapability>, Self::Error> {
        Ok(self.load()?.capabilities.get(id).cloned())
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
        let store = Arc::new(
            dregg_persist::PersistentStore::open(&dir.path().join("admission.redb"))
                .expect("store"),
        );
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
        let durable = RedbAdmissionStore::new(store)
            .load()
            .expect("durable state");
        assert_eq!(durable.challenges.len(), 1);
        assert_eq!(durable.used_nonces.len(), 1);
        assert!(durable.challenges.contains_key(&current_challenge.id()));
        assert!(durable.capabilities.is_empty());
        assert!(durable.spent_challenges.is_empty());
        assert!(durable.spent_capabilities.is_empty());
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
