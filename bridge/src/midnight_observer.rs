//! Midnight observation node: watches finalized Midnight blocks for bridge events.
//!
//! # Design (mirrors Midnight's own Cardano bridge observation)
//!
//! Midnight's `c2m-bridge` pallet uses a `TransferHandler` trait that receives
//! pre-parsed bridge transfers from the Partner Chains substrate runtime. Their
//! node watches the Cardano mainchain via an SPO (stake pool operator) and feeds
//! observed transactions as inherent data.
//!
//! We follow the same pattern but in reverse:
//! - Watch Midnight's Substrate chain via WebSocket RPC.
//! - Subscribe to finalized block headers (GRANDPA finality).
//! - For each finalized block, query events for the bridge contract.
//! - Parse `BridgeLock` events into `MidnightToDreggMessage`.
//! - Submit to dregg federation consensus.
//!
//! # Integration
//!
//! This module defines the observer as a standalone async task (`run_observer`).
//! It can be spawned from the dregg node binary or run as a sidecar process.
//! The submission callback is generic to allow both direct integration and
//! message-passing architectures.
//!
//! # Crash Recovery
//!
//! The observer persists `ObserverState` (last processed height + dedup set).
//! On restart, it resumes from `last_processed_height + 1` and skips any
//! already-processed events. This provides at-least-once delivery with
//! idempotent deduplication on the federation side.

use crate::midnight::{
    MidnightBridgeConfig, MidnightBridgeError, MidnightBridgeEvent, MidnightToDreggMessage,
    ObserverState, validate_midnight_to_dregg,
};

use std::future::Future;

// ============================================================================
// Observer trait (submission callback)
// ============================================================================

/// Trait for submitting observed bridge events to the dregg federation.
///
/// Implementors handle the actual submission (e.g., direct consensus proposal,
/// RPC to the local node, message queue).
pub trait BridgeEventSubmitter: Send + Sync + 'static {
    /// Submit a validated bridge message for minting on dregg.
    ///
    /// Returns Ok(()) if the message was accepted for processing.
    /// The actual minting happens asynchronously through federation consensus.
    fn submit(
        &self,
        message: MidnightToDreggMessage,
    ) -> impl Future<Output = Result<(), MidnightBridgeError>> + Send;
}

// ============================================================================
// Mock Substrate RPC types (stand-in until we add jsonrpsee/subxt)
// ============================================================================

/// A finalized block header from a Substrate chain.
///
/// This is a simplified representation; the real Substrate header includes
/// parent_hash, state_root, extrinsics_root, digest, etc.
#[derive(Clone, Debug)]
pub struct SubstrateBlockHeader {
    /// Block number.
    pub number: u64,
    /// Block hash (Blake2-256).
    pub hash: [u8; 32],
    /// Parent block hash.
    pub parent_hash: [u8; 32],
}

/// A system event from a Substrate block.
///
/// In a real integration, this would be decoded from the SCALE-encoded event
/// records via subxt or manual SCALE decoding.
#[derive(Clone, Debug)]
pub struct SubstrateEvent {
    /// The pallet index that emitted the event.
    pub pallet_index: u8,
    /// The event variant index within the pallet.
    pub variant_index: u8,
    /// The SCALE-encoded event data.
    pub data: Vec<u8>,
    /// The extrinsic index within the block (for tx_hash correlation).
    pub extrinsic_index: Option<u32>,
}

/// Trait abstracting the Substrate RPC connection.
///
/// This allows mocking the Midnight node for testing without an actual
/// WebSocket connection.
pub trait SubstrateRpcClient: Send + Sync + 'static {
    /// Subscribe to finalized block headers.
    ///
    /// Returns a stream of finalized headers. In production, this would use
    /// `chain_subscribeFinalizedHeads` via jsonrpsee.
    fn subscribe_finalized_heads(
        &self,
    ) -> impl Future<Output = Result<FinalizedHeadStream, MidnightBridgeError>> + Send;

    /// Get all system events for a given block hash.
    ///
    /// In production, this queries `system.events()` storage at the block.
    fn get_events(
        &self,
        block_hash: [u8; 32],
    ) -> impl Future<Output = Result<Vec<SubstrateEvent>, MidnightBridgeError>> + Send;

    /// Get the extrinsic hash for a given block and extrinsic index.
    ///
    /// Used to compute the tx_hash for the `MidnightToDreggMessage`.
    fn get_extrinsic_hash(
        &self,
        block_hash: [u8; 32],
        extrinsic_index: u32,
    ) -> impl Future<Output = Result<[u8; 32], MidnightBridgeError>> + Send;
}

/// A stream of finalized block headers.
///
/// In production, this would be a `jsonrpsee::core::client::Subscription<Header>`.
/// For our purposes, we define it as a trait object that yields headers.
pub struct FinalizedHeadStream {
    /// Internal: boxed async iterator. In production, this wraps a jsonrpsee subscription.
    pub(crate) _inner: Box<dyn FinalizedHeadIterator>,
}

/// Async iterator over finalized heads (object-safe portion).
pub trait FinalizedHeadIterator: Send {
    /// Get the next finalized header, or None if the stream ended.
    fn next(
        &mut self,
    ) -> std::pin::Pin<Box<dyn Future<Output = Option<SubstrateBlockHeader>> + Send + '_>>;
}

// ============================================================================
// Event parsing (Midnight bridge contract events → our types)
// ============================================================================

/// The pallet index for our bridge contract on Midnight.
///
/// In a real deployment, this would be configured based on the runtime metadata.
/// For now, it's a placeholder constant.
const BRIDGE_PALLET_INDEX: u8 = 42;

/// Event variant indices within the bridge pallet.
const EVENT_BRIDGE_LOCK: u8 = 0;
const EVENT_BRIDGE_UNLOCK: u8 = 1;

/// Parse a Substrate event into a `MidnightBridgeEvent` if it belongs to the bridge pallet.
///
/// Returns `None` if the event is from a different pallet or has an unknown variant.
pub fn parse_bridge_event(event: &SubstrateEvent) -> Option<MidnightBridgeEvent> {
    if event.pallet_index != BRIDGE_PALLET_INDEX {
        return None;
    }

    match event.variant_index {
        EVENT_BRIDGE_LOCK => parse_lock_event(&event.data),
        EVENT_BRIDGE_UNLOCK => parse_unlock_event(&event.data),
        _ => None,
    }
}

/// Parse a `BridgeLock` event from SCALE-encoded data.
///
/// Expected layout (packed, little-endian):
/// - amount: u64 (8 bytes)
/// - dregg_recipient: [u8; 32] (32 bytes)
/// - nonce: u64 (8 bytes)
///
/// Total: 48 bytes minimum.
fn parse_lock_event(data: &[u8]) -> Option<MidnightBridgeEvent> {
    if data.len() < 48 {
        return None;
    }

    let amount = u64::from_le_bytes(data[0..8].try_into().ok()?);
    let dregg_recipient: [u8; 32] = data[8..40].try_into().ok()?;
    let nonce = u64::from_le_bytes(data[40..48].try_into().ok()?);

    Some(MidnightBridgeEvent::Lock {
        amount,
        dregg_recipient,
        nonce,
    })
}

/// Parse a `BridgeUnlock` event from SCALE-encoded data.
///
/// Expected layout:
/// - amount: u64 (8 bytes)
/// - midnight_recipient_len: u32 (4 bytes, SCALE compact would differ but we simplify)
/// - midnight_recipient: [u8; midnight_recipient_len]
/// - nullifier: [u8; 32]
fn parse_unlock_event(data: &[u8]) -> Option<MidnightBridgeEvent> {
    if data.len() < 44 {
        // Minimum: 8 + 4 + 0 + 32 = 44 (empty recipient)
        return None;
    }

    let amount = u64::from_le_bytes(data[0..8].try_into().ok()?);
    let recipient_len = u32::from_le_bytes(data[8..12].try_into().ok()?) as usize;

    let expected_len = 12 + recipient_len + 32;
    if data.len() < expected_len {
        return None;
    }

    let midnight_recipient = data[12..12 + recipient_len].to_vec();
    let nullifier: [u8; 32] = data[12 + recipient_len..12 + recipient_len + 32]
        .try_into()
        .ok()?;

    Some(MidnightBridgeEvent::Unlock {
        amount,
        midnight_recipient,
        nullifier,
    })
}

// ============================================================================
// Observer main loop
// ============================================================================

/// Run the Midnight bridge observer as an async task.
///
/// This function subscribes to finalized Midnight blocks, parses bridge events,
/// validates them, and submits valid `MidnightToDreggMessage`s to the federation.
///
/// # Arguments
///
/// * `rpc` - The Substrate RPC client (connects to Midnight node).
/// * `submitter` - The bridge event submitter (sends validated messages to federation).
/// * `config` - Bridge configuration (contract address, limits, etc.).
/// * `state` - Mutable observer state (persisted for crash recovery).
///
/// # Returns
///
/// This function runs indefinitely (or until the RPC stream ends / errors out).
/// On error, it returns the error so the caller can decide whether to retry.
pub async fn run_observer<R, S>(
    rpc: R,
    submitter: S,
    config: MidnightBridgeConfig,
    state: &mut ObserverState,
) -> Result<(), MidnightBridgeError>
where
    R: SubstrateRpcClient,
    S: BridgeEventSubmitter,
{
    let mut head_stream = rpc.subscribe_finalized_heads().await?;

    while let Some(header) = head_stream._inner.next().await {
        // Skip blocks we've already processed (crash recovery).
        if header.number <= state.last_processed_height {
            continue;
        }

        // Fetch events for this block.
        let events = rpc.get_events(header.hash).await?;

        // Process each event.
        for (log_index, event) in events.iter().enumerate() {
            let Some(bridge_event) = parse_bridge_event(event) else {
                continue;
            };

            // We only care about Lock events (Midnight → dregg direction).
            let MidnightBridgeEvent::Lock {
                amount,
                dregg_recipient,
                nonce: _,
            } = bridge_event
            else {
                continue;
            };

            // Compute tx_hash for this event.
            let tx_hash = if let Some(ext_idx) = event.extrinsic_index {
                rpc.get_extrinsic_hash(header.hash, ext_idx).await?
            } else {
                // If no extrinsic index, use block_hash as fallback (less ideal).
                header.hash
            };

            let message = MidnightToDreggMessage {
                midnight_tx_hash: tx_hash,
                amount,
                dregg_recipient,
                midnight_height: header.number,
                log_index: log_index as u32,
            };

            // Validate before submission.
            if let Err(e) = validate_midnight_to_dregg(
                &message,
                &config,
                state,
                header.number, // finalized_height = current header (it IS finalized)
            ) {
                // Log and skip invalid/duplicate events.
                // In production, this would use tracing.
                eprintln!(
                    "midnight observer: skipping event at height {}, log {}: {}",
                    header.number, log_index, e
                );
                continue;
            }

            // Submit to federation.
            submitter.submit(message.clone()).await?;

            // Mark as processed (for dedup on restart).
            state.mark_processed(tx_hash, log_index as u32);
        }

        // Advance the watermark.
        state.advance_height(header.number);

        // Periodic pruning of the dedup set (keep it bounded).
        state.prune_if_large(10_000);
    }

    Ok(())
}

// ============================================================================
// The real Substrate JSON-RPC client (live impl behind `SubstrateRpcClient`)
// ============================================================================
//
// This is the cross-chain analogue of `solana_relayer::SolanaJsonRpc`: a REAL
// Substrate/Midnight JSON-RPC client that builds the genuine request envelopes
// (`chain_getFinalizedHead` / `chain_getHeader` / `chain_getBlockHash` /
// `state_getStorage` / `chain_getBlock`) and parses the genuine response shapes
// (hex block hashes, hex block numbers, SCALE-encoded `System::Events`),
// delegating the actual bytes to an injected [`SubstrateRpcTransport`].
//
// # The trust boundary (named precisely, like the Solana lane)
//
// The client mints/observes against the chain's OWN finality: it follows
// `chain_getFinalizedHead` (GRANDPA-rooted) and never reads un-finalized state,
// so the finality gate is STRUCTURAL — an un-finalized block is simply never
// yielded by the head follower. This is the re-executing-observer trust level:
// it trusts the RPC's finalized commitment. For a dregg LIGHT client (not a
// re-executing observer) to witness the Midnight transition, the Substrate
// finality + event inclusion must be folded into the EffectVM — that weld is the
// parallel circuit swarm's (NOT this module's). See `midnight_verified.rs`.
//
// # Why a polling follower (the dependency-light WS equivalent)
//
// `chain_subscribeFinalizedHeads` is a streaming WS subscription. Rather than
// pull `jsonrpsee`/`tokio`/TLS into the verified core, the live client FOLLOWS
// the finalized head by polling `chain_getFinalizedHead` and walking
// `chain_getBlockHash(n)` block-by-block. This observes the SAME finalized state
// a subscription would, over the SAME injected request/response byte-pipe. A real
// async WS transport (jsonrpsee) is a drop-in [`SubstrateRpcTransport`] the deploy
// harness injects (REVIEWED-GO — the live mainnet observer); the dependency-free
// [`StdHttpRpcTransport`] ships for `http://` dev nodes (Substrate's HTTP JSON-RPC
// on `:9933` exposes the identical methods).

use std::collections::HashMap;
use std::pin::Pin;
use std::sync::Arc;
use std::time::Duration;

use serde_json::{Value, json};

/// The byte-pipe under [`LiveSubstrateRpc`]: POST one JSON-RPC request body and
/// return the response body. This is the ONE seam where the network lives, so TLS
/// / async-WS is a deploy concern, not a verified-core dependency.
/// [`StdHttpRpcTransport`] ships for `http://` endpoints (the local dev node); an
/// `https`/WS transport (jsonrpsee) is injected by the deploy harness (REVIEWED-GO
/// — the live mainnet Midnight observer).
pub trait SubstrateRpcTransport: Send + Sync + 'static {
    /// POST `body` (a JSON-RPC request envelope) and return the response body.
    fn post(
        &self,
        body: String,
    ) -> impl Future<Output = Result<String, MidnightBridgeError>> + Send;
}

/// The well-known `System::Events` storage key — `twox128("System") ++
/// twox128("Events")`. Runtime-independent (the pallet/storage names are fixed),
/// so it needs no metadata.
const SYSTEM_EVENTS_KEY: &str =
    "0x26aa394eea5630e07c48ae0c9558cef780d41e5e16056765bc8461851072c9d7";

/// Build + send one JSON-RPC call, surfacing a node `error` object or a missing
/// `result` as a connection failure (the observer's "RPC failed" bucket).
async fn rpc_call<T: SubstrateRpcTransport>(
    transport: &T,
    method: &str,
    params: Value,
) -> Result<Value, MidnightBridgeError> {
    let req = json!({ "jsonrpc": "2.0", "id": 1, "method": method, "params": params });
    let body = serde_json::to_string(&req).map_err(|e| MidnightBridgeError::ConnectionFailed {
        reason: e.to_string(),
    })?;
    let resp = transport.post(body).await?;
    let v: Value =
        serde_json::from_str(&resp).map_err(|e| MidnightBridgeError::ConnectionFailed {
            reason: e.to_string(),
        })?;
    if let Some(err) = v.get("error") {
        let code = err.get("code").and_then(|c| c.as_i64()).unwrap_or(0);
        let message = err.get("message").and_then(|m| m.as_str()).unwrap_or("");
        return Err(MidnightBridgeError::ConnectionFailed {
            reason: format!("rpc error {code}: {message}"),
        });
    }
    v.get("result")
        .cloned()
        .ok_or_else(|| MidnightBridgeError::ConnectionFailed {
            reason: "missing `result`".into(),
        })
}

/// `chain_getHeader(hash)` → `{ number: "0x..", parentHash: "0x.." }`.
async fn fetch_header<T: SubstrateRpcTransport>(
    transport: &T,
    hash: &[u8; 32],
) -> Result<SubstrateBlockHeader, MidnightBridgeError> {
    let h = rpc_call(transport, "chain_getHeader", json!([hex0x(hash)])).await?;
    let number = h
        .get("number")
        .and_then(|n| n.as_str())
        .and_then(parse_hex_u64)
        .ok_or_else(|| MidnightBridgeError::ConnectionFailed {
            reason: "header.number".into(),
        })?;
    let parent_hash = h
        .get("parentHash")
        .and_then(|p| p.as_str())
        .and_then(decode_hash32)
        .ok_or_else(|| MidnightBridgeError::ConnectionFailed {
            reason: "header.parentHash".into(),
        })?;
    Ok(SubstrateBlockHeader {
        number,
        hash: *hash,
        parent_hash,
    })
}

/// `chain_getFinalizedHead` → header → finalized block number.
async fn fetch_finalized_number<T: SubstrateRpcTransport>(
    transport: &T,
) -> Result<u64, MidnightBridgeError> {
    let head = rpc_call(transport, "chain_getFinalizedHead", json!([])).await?;
    let hash = head.as_str().and_then(decode_hash32).ok_or_else(|| {
        MidnightBridgeError::ConnectionFailed {
            reason: "chain_getFinalizedHead".into(),
        }
    })?;
    Ok(fetch_header(transport, &hash).await?.number)
}

/// `chain_getBlockHash(number)` → hash, or `None` if the block is absent.
async fn fetch_block_hash<T: SubstrateRpcTransport>(
    transport: &T,
    number: u64,
) -> Result<Option<[u8; 32]>, MidnightBridgeError> {
    let v = rpc_call(transport, "chain_getBlockHash", json!([number])).await?;
    match v {
        Value::Null => Ok(None),
        Value::String(s) => {
            decode_hash32(&s)
                .map(Some)
                .ok_or_else(|| MidnightBridgeError::ConnectionFailed {
                    reason: "chain_getBlockHash".into(),
                })
        }
        _ => Err(MidnightBridgeError::ConnectionFailed {
            reason: "chain_getBlockHash shape".into(),
        }),
    }
}

/// The live Substrate RPC client over an injected [`SubstrateRpcTransport`].
/// Implements the existing async [`SubstrateRpcClient`] trait, so the observer
/// (`run_observer`) drives it byte-identically to the mock — the only swap is the
/// transport.
pub struct LiveSubstrateRpc<T: SubstrateRpcTransport> {
    transport: Arc<T>,
    start_height: u64,
    follow: bool,
    poll_delay: Duration,
    layouts: Arc<EventLayouts>,
}

impl<T: SubstrateRpcTransport> LiveSubstrateRpc<T> {
    /// Build a live client that follows the finalized head from `start_height`.
    ///
    /// `follow = true` keeps the head stream open (re-polling every `poll_delay`
    /// once caught up to the finalized tip — suited to a dedicated observer thread
    /// / `spawn_blocking`); `follow = false` drains the backlog up to the current
    /// finalized tip and ends the stream (the supervisor re-invokes to continue).
    pub fn new(transport: T, start_height: u64, follow: bool) -> Self {
        Self {
            transport: Arc::new(transport),
            start_height,
            follow,
            poll_delay: Duration::from_secs(6),
            layouts: Arc::new(EventLayouts::with_bridge()),
        }
    }

    /// Override the catch-up poll delay (default 6s, ~one Substrate block).
    pub fn with_poll_delay(mut self, delay: Duration) -> Self {
        self.poll_delay = delay;
        self
    }

    /// Override the event-layout table (e.g. register foreign-pallet event sizes
    /// from the runtime metadata so the `System::Events` decode can advance past
    /// them). The bridge-pallet layouts are always present.
    pub fn with_layouts(mut self, layouts: EventLayouts) -> Self {
        self.layouts = Arc::new(layouts);
        self
    }
}

impl<T: SubstrateRpcTransport> SubstrateRpcClient for LiveSubstrateRpc<T> {
    fn subscribe_finalized_heads(
        &self,
    ) -> impl Future<Output = Result<FinalizedHeadStream, MidnightBridgeError>> + Send {
        let transport = self.transport.clone();
        let next_number = self.start_height;
        let follow = self.follow;
        let poll_delay = self.poll_delay;
        async move {
            // Probe finality once up front: a node we cannot reach surfaces here as
            // a clean `Err` (the at-subscribe disconnect), not a mid-stream stall.
            let _ = fetch_finalized_number(&*transport).await?;
            Ok(FinalizedHeadStream {
                _inner: Box::new(PollingHeadIterator {
                    transport,
                    next_number,
                    follow,
                    poll_delay,
                    errored: false,
                }),
            })
        }
    }

    fn get_events(
        &self,
        block_hash: [u8; 32],
    ) -> impl Future<Output = Result<Vec<SubstrateEvent>, MidnightBridgeError>> + Send {
        let transport = self.transport.clone();
        let layouts = self.layouts.clone();
        async move {
            let result = rpc_call(
                &*transport,
                "state_getStorage",
                json!([SYSTEM_EVENTS_KEY, hex0x(&block_hash)]),
            )
            .await?;
            let hex_str = match result {
                // No `System::Events` at this block (or pruned) → no events.
                Value::Null => return Ok(Vec::new()),
                Value::String(s) => s,
                _ => {
                    return Err(MidnightBridgeError::ConnectionFailed {
                        reason: "state_getStorage shape".into(),
                    });
                }
            };
            let bytes =
                decode_hex(&hex_str).ok_or_else(|| MidnightBridgeError::ConnectionFailed {
                    reason: "state_getStorage hex".into(),
                })?;
            decode_event_records(&bytes, &layouts)
        }
    }

    fn get_extrinsic_hash(
        &self,
        block_hash: [u8; 32],
        extrinsic_index: u32,
    ) -> impl Future<Output = Result<[u8; 32], MidnightBridgeError>> + Send {
        let transport = self.transport.clone();
        async move {
            let result =
                rpc_call(&*transport, "chain_getBlock", json!([hex0x(&block_hash)])).await?;
            let exts = result
                .get("block")
                .and_then(|b| b.get("extrinsics"))
                .and_then(|e| e.as_array())
                .ok_or_else(|| MidnightBridgeError::ConnectionFailed {
                    reason: "block.extrinsics".into(),
                })?;
            let ext_hex = exts
                .get(extrinsic_index as usize)
                .and_then(|x| x.as_str())
                .ok_or_else(|| MidnightBridgeError::ConnectionFailed {
                    reason: format!("extrinsic {extrinsic_index} absent"),
                })?;
            let ext_bytes =
                decode_hex(ext_hex).ok_or_else(|| MidnightBridgeError::ConnectionFailed {
                    reason: "extrinsic hex".into(),
                })?;
            // A Substrate extrinsic hash is BlakeTwo256 of the SCALE-encoded bytes.
            Ok(blake2_256(&ext_bytes))
        }
    }
}

/// The polling finalized-head follower (the dependency-light equivalent of
/// `chain_subscribeFinalizedHeads`). Yields each finalized header in order from
/// `next_number`; only ever reads `chain_getFinalizedHead`, so it NEVER yields an
/// un-finalized block (the structural finality gate).
struct PollingHeadIterator<T: SubstrateRpcTransport> {
    transport: Arc<T>,
    next_number: u64,
    follow: bool,
    poll_delay: Duration,
    errored: bool,
}

impl<T: SubstrateRpcTransport> FinalizedHeadIterator for PollingHeadIterator<T> {
    fn next(&mut self) -> Pin<Box<dyn Future<Output = Option<SubstrateBlockHeader>> + Send + '_>> {
        Box::pin(async move {
            if self.errored {
                return None;
            }
            loop {
                // The current finalized tip. A transport failure (disconnect) ends
                // the stream cleanly: `run_observer` returns `Ok`, the supervisor
                // re-invokes (reconnect) from the persisted watermark. No panic.
                let finalized = match fetch_finalized_number(&*self.transport).await {
                    Ok(n) => n,
                    Err(_) => {
                        self.errored = true;
                        return None;
                    }
                };
                if self.next_number <= finalized {
                    let hash = match fetch_block_hash(&*self.transport, self.next_number).await {
                        Ok(Some(h)) => h,
                        // A hole below the finalized tip is a forging/inconsistent
                        // node — refuse rather than skip.
                        Ok(None) | Err(_) => {
                            self.errored = true;
                            return None;
                        }
                    };
                    let header = match fetch_header(&*self.transport, &hash).await {
                        Ok(h) => h,
                        Err(_) => {
                            self.errored = true;
                            return None;
                        }
                    };
                    self.next_number += 1;
                    return Some(header);
                }
                // Caught up to the finalized tip.
                if !self.follow {
                    return None;
                }
                std::thread::sleep(self.poll_delay);
            }
        })
    }
}

// ----------------------------------------------------------------------------
// SCALE `System::Events` decode (real, metadata-light)
// ----------------------------------------------------------------------------

/// How many bytes an event's fields occupy — the cursor needs this to walk past
/// every record in the SCALE `Vec<EventRecord>`. Fixed-layout events register a
/// byte count; a length-prefixed event (`u32` length embedded in the fields)
/// registers the surrounding fixed bytes.
#[derive(Clone, Copy, Debug)]
pub enum FieldLen {
    /// A fixed number of field bytes.
    Fixed(usize),
    /// `before` fixed bytes, then a `u32` LE length, then that many bytes, then
    /// `after` fixed bytes (the bridge `Unlock` shape: `amount ‖ len ‖ recipient
    /// ‖ nullifier`).
    PrefixedU32 { before: usize, after: usize },
}

/// The `(pallet_index, variant_index) → field length` table the SCALE event
/// decoder needs to advance past each record. Seeded with the bridge pallet; a
/// real runtime registers its other emitting pallets' event sizes (from
/// metadata) so the decoder can skip them.
#[derive(Clone, Debug, Default)]
pub struct EventLayouts {
    map: HashMap<(u8, u8), FieldLen>,
}

impl EventLayouts {
    /// A table seeded with the bridge pallet's two event layouts.
    pub fn with_bridge() -> Self {
        let mut map = HashMap::new();
        // Lock: amount(u64) ‖ dregg_recipient([u8;32]) ‖ nonce(u64) = 48.
        map.insert(
            (BRIDGE_PALLET_INDEX, EVENT_BRIDGE_LOCK),
            FieldLen::Fixed(48),
        );
        // Unlock: amount(u64) ‖ len(u32) ‖ recipient[len] ‖ nullifier([u8;32]).
        map.insert(
            (BRIDGE_PALLET_INDEX, EVENT_BRIDGE_UNLOCK),
            FieldLen::PrefixedU32 {
                before: 8,
                after: 32,
            },
        );
        Self { map }
    }

    /// Register a foreign pallet's fixed-size event (from runtime metadata) so the
    /// decoder can advance past it.
    pub fn register_fixed(&mut self, pallet: u8, variant: u8, len: usize) -> &mut Self {
        self.map.insert((pallet, variant), FieldLen::Fixed(len));
        self
    }

    /// The field byte-length of `(pallet, variant)`, reading the embedded length
    /// from `rest` (the bytes at the start of the fields) for prefixed layouts.
    fn field_len(&self, pallet: u8, variant: u8, rest: &[u8]) -> Option<usize> {
        match self.map.get(&(pallet, variant))? {
            FieldLen::Fixed(n) => Some(*n),
            FieldLen::PrefixedU32 { before, after } => {
                let raw = rest.get(*before..*before + 4)?;
                let len = u32::from_le_bytes(raw.try_into().ok()?) as usize;
                Some(*before + 4 + len + *after)
            }
        }
    }
}

/// Read a SCALE compact-encoded `u32`, advancing `pos`.
fn read_compact_u32(b: &[u8], pos: &mut usize) -> Option<u32> {
    let first = *b.get(*pos)?;
    match first & 0b11 {
        0 => {
            *pos += 1;
            Some((first >> 2) as u32)
        }
        1 => {
            let raw = b.get(*pos..*pos + 2)?;
            let v = u16::from_le_bytes(raw.try_into().ok()?);
            *pos += 2;
            Some((v >> 2) as u32)
        }
        2 => {
            let raw = b.get(*pos..*pos + 4)?;
            let v = u32::from_le_bytes(raw.try_into().ok()?);
            *pos += 4;
            Some(v >> 2)
        }
        _ => {
            // Big-integer mode: (first >> 2) + 4 length bytes follow (LE).
            let n = (first >> 2) as usize + 4;
            if n > 4 {
                return None; // beyond u32
            }
            *pos += 1;
            let mut val = 0u32;
            for i in 0..n {
                val |= (*b.get(*pos + i)? as u32) << (8 * i);
            }
            *pos += n;
            Some(val)
        }
    }
}

/// Decode a SCALE-encoded `Vec<EventRecord>` (`System::Events`) into the
/// [`SubstrateEvent`]s the observer consumes. Each record is `phase ‖ event ‖
/// topics`; `phase = ApplyExtrinsic(u32) | Finalization | Initialization`; the
/// event is `pallet_index ‖ variant_index ‖ fields`. The [`EventLayouts`] table
/// sizes the fields so the cursor can advance past every record.
fn decode_event_records(
    bytes: &[u8],
    layouts: &EventLayouts,
) -> Result<Vec<SubstrateEvent>, MidnightBridgeError> {
    let err = |reason: &str| MidnightBridgeError::ConnectionFailed {
        reason: format!("event decode: {reason}"),
    };
    let mut pos = 0usize;
    let n = read_compact_u32(bytes, &mut pos).ok_or_else(|| err("record count"))?;
    let mut out = Vec::with_capacity(n as usize);
    for _ in 0..n {
        // phase
        let tag = *bytes.get(pos).ok_or_else(|| err("phase tag"))?;
        pos += 1;
        let extrinsic_index = match tag {
            0 => {
                let raw = bytes.get(pos..pos + 4).ok_or_else(|| err("phase index"))?;
                pos += 4;
                Some(u32::from_le_bytes(raw.try_into().unwrap()))
            }
            1 | 2 => None, // Finalization / Initialization carry no extrinsic.
            _ => return Err(err("unknown phase")),
        };
        // event: pallet ‖ variant ‖ fields
        let pallet = *bytes.get(pos).ok_or_else(|| err("pallet index"))?;
        let variant = *bytes.get(pos + 1).ok_or_else(|| err("variant index"))?;
        pos += 2;
        let field_len = layouts
            .field_len(pallet, variant, bytes.get(pos..).unwrap_or(&[]))
            .ok_or_else(|| MidnightBridgeError::ConnectionFailed {
                reason: format!(
                    "event decode: unregistered event ({pallet}, {variant}) — register its \
                         size from runtime metadata"
                ),
            })?;
        let data = bytes
            .get(pos..pos + field_len)
            .ok_or_else(|| err("event fields"))?
            .to_vec();
        pos += field_len;
        // topics: Vec<H256>
        let topics = read_compact_u32(bytes, &mut pos).ok_or_else(|| err("topics count"))?;
        pos = pos
            .checked_add(topics as usize * 32)
            .ok_or_else(|| err("topics overflow"))?;
        if pos > bytes.len() {
            return Err(err("topics truncated"));
        }
        out.push(SubstrateEvent {
            pallet_index: pallet,
            variant_index: variant,
            data,
            extrinsic_index,
        });
    }
    Ok(out)
}

// ----------------------------------------------------------------------------
// Hex / hash helpers
// ----------------------------------------------------------------------------

/// BlakeTwo256 (`blake2b-256`) of `bytes` — the Substrate extrinsic-hash function.
fn blake2_256(bytes: &[u8]) -> [u8; 32] {
    use blake2::Digest;
    let mut h = blake2::Blake2b::<blake2::digest::consts::U32>::new();
    h.update(bytes);
    let out = h.finalize();
    let mut o = [0u8; 32];
    o.copy_from_slice(&out);
    o
}

fn hexval(c: u8) -> Option<u8> {
    match c {
        b'0'..=b'9' => Some(c - b'0'),
        b'a'..=b'f' => Some(c - b'a' + 10),
        b'A'..=b'F' => Some(c - b'A' + 10),
        _ => None,
    }
}

/// Decode an optionally-`0x`-prefixed hex string into bytes.
fn decode_hex(s: &str) -> Option<Vec<u8>> {
    let s = s.strip_prefix("0x").unwrap_or(s);
    if s.len() % 2 != 0 {
        return None;
    }
    let b = s.as_bytes();
    let mut out = Vec::with_capacity(b.len() / 2);
    let mut i = 0;
    while i < b.len() {
        out.push((hexval(b[i])? << 4) | hexval(b[i + 1])?);
        i += 2;
    }
    Some(out)
}

/// Decode a `0x`-hex string into exactly 32 bytes (a block hash / H256).
fn decode_hash32(s: &str) -> Option<[u8; 32]> {
    let v = decode_hex(s)?;
    if v.len() != 32 {
        return None;
    }
    let mut h = [0u8; 32];
    h.copy_from_slice(&v);
    Some(h)
}

/// Parse a `0x`-hex integer (Substrate encodes block numbers this way).
fn parse_hex_u64(s: &str) -> Option<u64> {
    let s = s.strip_prefix("0x").unwrap_or(s);
    if s.is_empty() {
        return Some(0);
    }
    u64::from_str_radix(s, 16).ok()
}

/// Encode `bytes` as a `0x`-prefixed lowercase hex string.
fn hex0x(bytes: &[u8]) -> String {
    use std::fmt::Write;
    let mut s = String::with_capacity(2 + bytes.len() * 2);
    s.push_str("0x");
    for b in bytes {
        let _ = write!(s, "{b:02x}");
    }
    s
}

/// A dependency-free blocking HTTP/1.1 transport over `std::net::TcpStream`, for
/// **`http://`** Substrate dev nodes (the node's HTTP JSON-RPC on `:9933` exposes
/// the same methods as the WS endpoint). It speaks `Connection: close` and reads
/// to EOF, then de-chunks a `Transfer-Encoding: chunked` body. `https://` returns
/// a clear error asking for an injected TLS/WS transport — TLS is a deploy concern
/// (REVIEWED-GO), not a verified-core dependency. Mirrors
/// `solana_relayer::StdHttpTransport`.
pub struct StdHttpRpcTransport {
    /// The RPC endpoint, e.g. `http://127.0.0.1:9933`.
    pub url: String,
    /// Connect/read/write timeout.
    pub timeout: Duration,
}

impl StdHttpRpcTransport {
    /// Build a transport for `url` (default 20s timeout).
    pub fn new(url: impl Into<String>) -> Self {
        Self {
            url: url.into(),
            timeout: Duration::from_secs(20),
        }
    }

    fn post_blocking(&self, body: &str) -> Result<String, MidnightBridgeError> {
        use std::io::{Read, Write};
        use std::net::TcpStream;

        let conn = |reason: String| MidnightBridgeError::ConnectionFailed { reason };
        let rest = self.url.strip_prefix("http://").ok_or_else(|| {
            conn(format!(
                "StdHttpRpcTransport only handles http:// (got `{}`); inject a TLS/WS transport \
                 for https/wss endpoints",
                self.url
            ))
        })?;
        let (authority, path) = match rest.find('/') {
            Some(i) => (&rest[..i], &rest[i..]),
            None => (rest, "/"),
        };
        let (host, port) = match authority.rsplit_once(':') {
            Some((h, p)) => (
                h,
                p.parse::<u16>()
                    .map_err(|e| conn(format!("bad port: {e}")))?,
            ),
            None => (authority, 80u16),
        };

        let mut stream = TcpStream::connect((host, port))
            .map_err(|e| conn(format!("connect {host}:{port}: {e}")))?;
        stream
            .set_read_timeout(Some(self.timeout))
            .map_err(|e| conn(e.to_string()))?;
        stream
            .set_write_timeout(Some(self.timeout))
            .map_err(|e| conn(e.to_string()))?;

        let req = format!(
            "POST {path} HTTP/1.1\r\nHost: {host}\r\nContent-Type: application/json\r\n\
             Accept: application/json\r\nContent-Length: {}\r\nConnection: close\r\n\r\n{body}",
            body.len()
        );
        stream
            .write_all(req.as_bytes())
            .map_err(|e| conn(format!("write: {e}")))?;

        let mut raw = Vec::new();
        stream
            .read_to_end(&mut raw)
            .map_err(|e| conn(format!("read: {e}")))?;

        let split = raw
            .windows(4)
            .position(|w| w == b"\r\n\r\n")
            .ok_or_else(|| conn("no header/body boundary".into()))?;
        let headers = String::from_utf8_lossy(&raw[..split]).to_ascii_lowercase();
        let body_bytes = &raw[split + 4..];
        let body = if headers.contains("transfer-encoding: chunked") {
            dechunk(body_bytes)?
        } else {
            body_bytes.to_vec()
        };
        String::from_utf8(body).map_err(|e| conn(format!("utf8 body: {e}")))
    }
}

impl SubstrateRpcTransport for StdHttpRpcTransport {
    fn post(
        &self,
        body: String,
    ) -> impl Future<Output = Result<String, MidnightBridgeError>> + Send {
        // The dependency-light path is blocking std::net I/O; run it on a
        // dedicated observer thread / `spawn_blocking`. A real async WS transport
        // (jsonrpsee) is the injected REVIEWED-GO alternative.
        let out = self.post_blocking(&body);
        async move { out }
    }
}

/// De-chunk an HTTP/1.1 `Transfer-Encoding: chunked` body.
fn dechunk(mut b: &[u8]) -> Result<Vec<u8>, MidnightBridgeError> {
    let err = |reason: &str| MidnightBridgeError::ConnectionFailed {
        reason: reason.to_string(),
    };
    let mut out = Vec::new();
    loop {
        let nl = b
            .windows(2)
            .position(|w| w == b"\r\n")
            .ok_or_else(|| err("chunk size line"))?;
        let size_str = std::str::from_utf8(&b[..nl])
            .map_err(|_| err("chunk size utf8"))?
            .trim();
        let size_hex = size_str.split(';').next().unwrap_or("");
        let size = usize::from_str_radix(size_hex, 16).map_err(|_| err("chunk size hex"))?;
        b = &b[nl + 2..];
        if size == 0 {
            break;
        }
        if b.len() < size {
            return Err(err("truncated chunk"));
        }
        out.extend_from_slice(&b[..size]);
        b = &b[size..];
        if b.len() >= 2 && &b[..2] == b"\r\n" {
            b = &b[2..];
        }
    }
    Ok(out)
}

// ============================================================================
// In-memory test double (the live-client test support; mirrors `MockSolanaRpc`)
// ============================================================================

/// Test/dev support for the live client: an in-memory Substrate node speaking the
/// REAL JSON-RPC wire (so [`LiveSubstrateRpc`]'s genuine request/response codec is
/// exercised without a network), plus SCALE encoders that build a real
/// `System::Events` blob the real decoder parses. Gated on `test-utils` so
/// integration tests can use it.
#[cfg(any(test, feature = "test-utils"))]
pub mod live_support {
    use super::*;

    /// One finalized block in the in-memory node.
    #[derive(Clone, Debug)]
    pub struct CannedBlock {
        /// Block number.
        pub number: u64,
        /// Block hash.
        pub hash: [u8; 32],
        /// Parent hash.
        pub parent_hash: [u8; 32],
        /// The `System::Events` storage value as a `0x`-hex SCALE blob.
        pub events_hex: String,
        /// The block's SCALE-encoded extrinsics (raw bytes), for `chain_getBlock`.
        pub extrinsics: Vec<Vec<u8>>,
    }

    /// An in-memory Substrate node: it answers `chain_getFinalizedHead`,
    /// `chain_getHeader`, `chain_getBlockHash`, `state_getStorage`, and
    /// `chain_getBlock` over the REAL JSON-RPC envelope shapes. `fail = true`
    /// simulates a disconnected node (every call errors).
    #[derive(Clone, Debug, Default)]
    pub struct CannedSubstrateNode {
        blocks: Vec<CannedBlock>,
        finalized_hash: [u8; 32],
        fail: bool,
    }

    impl CannedSubstrateNode {
        /// An empty node.
        pub fn new() -> Self {
            Self::default()
        }

        /// A node whose every RPC call fails (the disconnect case).
        pub fn disconnected() -> Self {
            Self {
                fail: true,
                ..Self::default()
            }
        }

        /// Append a finalized block (the latest added becomes the finalized head).
        pub fn push_block(&mut self, block: CannedBlock) -> &mut Self {
            self.finalized_hash = block.hash;
            self.blocks.push(block);
            self
        }

        fn result_for(&self, method: &str, params: &Value) -> Value {
            match method {
                "chain_getFinalizedHead" => Value::String(hex0x(&self.finalized_hash)),
                "chain_getHeader" => {
                    let hash = params
                        .get(0)
                        .and_then(|p| p.as_str())
                        .and_then(decode_hash32);
                    match hash.and_then(|h| self.blocks.iter().find(|b| b.hash == h)) {
                        Some(b) => json!({
                            "number": format!("0x{:x}", b.number),
                            "parentHash": hex0x(&b.parent_hash),
                            "stateRoot": hex0x(&[0u8; 32]),
                            "extrinsicsRoot": hex0x(&[0u8; 32]),
                            "digest": { "logs": [] },
                        }),
                        None => Value::Null,
                    }
                }
                "chain_getBlockHash" => {
                    let n = params.get(0).and_then(|p| p.as_u64());
                    match n.and_then(|n| self.blocks.iter().find(|b| b.number == n)) {
                        Some(b) => Value::String(hex0x(&b.hash)),
                        None => Value::Null,
                    }
                }
                "state_getStorage" => {
                    let at = params
                        .get(1)
                        .and_then(|p| p.as_str())
                        .and_then(decode_hash32);
                    match at.and_then(|h| self.blocks.iter().find(|b| b.hash == h)) {
                        Some(b) if !b.events_hex.is_empty() => Value::String(b.events_hex.clone()),
                        _ => Value::Null,
                    }
                }
                "chain_getBlock" => {
                    let hash = params
                        .get(0)
                        .and_then(|p| p.as_str())
                        .and_then(decode_hash32);
                    match hash.and_then(|h| self.blocks.iter().find(|b| b.hash == h)) {
                        Some(b) => {
                            let exts: Vec<Value> = b
                                .extrinsics
                                .iter()
                                .map(|e| Value::String(hex0x(e)))
                                .collect();
                            json!({ "block": { "header": {}, "extrinsics": exts }, "justifications": Value::Null })
                        }
                        None => Value::Null,
                    }
                }
                _ => Value::Null,
            }
        }
    }

    impl SubstrateRpcTransport for CannedSubstrateNode {
        fn post(
            &self,
            body: String,
        ) -> impl Future<Output = Result<String, MidnightBridgeError>> + Send {
            let out = (|| {
                if self.fail {
                    return Err(MidnightBridgeError::ConnectionFailed {
                        reason: "simulated disconnect".into(),
                    });
                }
                let req: Value = serde_json::from_str(&body).map_err(|e| {
                    MidnightBridgeError::ConnectionFailed {
                        reason: e.to_string(),
                    }
                })?;
                let method = req.get("method").and_then(|m| m.as_str()).unwrap_or("");
                let params = req.get("params").cloned().unwrap_or(Value::Null);
                let result = self.result_for(method, &params);
                Ok(json!({ "jsonrpc": "2.0", "id": 1, "result": result }).to_string())
            })();
            async move { out }
        }
    }

    /// SCALE compact-encode a `u32` length (small-value modes).
    pub fn compact_u32(v: u32) -> Vec<u8> {
        if v < 0b0100_0000 {
            vec![(v << 2) as u8]
        } else if v < 0b0100_0000_0000_0000 {
            ((v << 2) | 0b01).to_le_bytes()[..2].to_vec()
        } else {
            ((v << 2) | 0b10).to_le_bytes().to_vec()
        }
    }

    /// Build one `EventRecord` for a bridge `Lock` event (phase
    /// `ApplyExtrinsic(extrinsic_index)`, no topics) — the real SCALE bytes the
    /// live decoder parses.
    pub fn bridge_lock_record(
        extrinsic_index: u32,
        amount: u64,
        dregg_recipient: [u8; 32],
        nonce: u64,
    ) -> Vec<u8> {
        let mut r = Vec::new();
        r.push(0u8); // phase: ApplyExtrinsic
        r.extend_from_slice(&extrinsic_index.to_le_bytes());
        r.push(BRIDGE_PALLET_INDEX);
        r.push(EVENT_BRIDGE_LOCK);
        r.extend_from_slice(&amount.to_le_bytes());
        r.extend_from_slice(&dregg_recipient);
        r.extend_from_slice(&nonce.to_le_bytes());
        r.push(0u8); // topics: empty Vec
        r
    }

    /// Build an `EventRecord` for an arbitrary fixed-size foreign event (to prove
    /// the decoder walks PAST registered foreign events to reach a later bridge
    /// event).
    pub fn foreign_fixed_record(pallet: u8, variant: u8, fields: &[u8]) -> Vec<u8> {
        let mut r = Vec::new();
        r.push(2u8); // phase: Initialization (no extrinsic index)
        r.push(pallet);
        r.push(variant);
        r.extend_from_slice(fields);
        r.push(0u8); // topics
        r
    }

    /// Assemble `records` into the `0x`-hex `System::Events` storage value (the
    /// `Vec<EventRecord>` SCALE blob).
    pub fn system_events_hex(records: &[Vec<u8>]) -> String {
        let mut blob = compact_u32(records.len() as u32);
        for r in records {
            blob.extend_from_slice(r);
        }
        hex0x(&blob)
    }
}

// ============================================================================
// Mock implementations for testing
// ============================================================================

#[cfg(test)]
pub mod mock {
    use super::*;
    use std::sync::{Arc, Mutex};

    /// A mock RPC client that yields pre-configured blocks and events.
    pub struct MockRpcClient {
        pub headers: Vec<SubstrateBlockHeader>,
        pub events: std::collections::HashMap<[u8; 32], Vec<SubstrateEvent>>,
    }

    impl SubstrateRpcClient for MockRpcClient {
        fn subscribe_finalized_heads(
            &self,
        ) -> impl Future<Output = Result<FinalizedHeadStream, MidnightBridgeError>> + Send {
            let headers = self.headers.clone();
            async move {
                Ok(FinalizedHeadStream {
                    _inner: Box::new(MockHeadIterator { headers, index: 0 }),
                })
            }
        }

        fn get_events(
            &self,
            block_hash: [u8; 32],
        ) -> impl Future<Output = Result<Vec<SubstrateEvent>, MidnightBridgeError>> + Send {
            let events = self.events.get(&block_hash).cloned().unwrap_or_default();
            async move { Ok(events) }
        }

        fn get_extrinsic_hash(
            &self,
            block_hash: [u8; 32],
            extrinsic_index: u32,
        ) -> impl Future<Output = Result<[u8; 32], MidnightBridgeError>> + Send {
            // Deterministic hash from block_hash + index for testing.
            let mut hasher = blake3::Hasher::new();
            hasher.update(&block_hash);
            hasher.update(&extrinsic_index.to_le_bytes());
            let hash = *hasher.finalize().as_bytes();
            async move { Ok(hash) }
        }
    }

    struct MockHeadIterator {
        headers: Vec<SubstrateBlockHeader>,
        index: usize,
    }

    impl FinalizedHeadIterator for MockHeadIterator {
        fn next(
            &mut self,
        ) -> std::pin::Pin<Box<dyn Future<Output = Option<SubstrateBlockHeader>> + Send + '_>>
        {
            Box::pin(async move {
                if self.index < self.headers.len() {
                    let header = self.headers[self.index].clone();
                    self.index += 1;
                    Some(header)
                } else {
                    None
                }
            })
        }
    }

    /// A mock submitter that collects submitted messages.
    #[derive(Clone, Default)]
    pub struct MockSubmitter {
        pub messages: Arc<Mutex<Vec<MidnightToDreggMessage>>>,
    }

    impl BridgeEventSubmitter for MockSubmitter {
        fn submit(
            &self,
            message: MidnightToDreggMessage,
        ) -> impl Future<Output = Result<(), MidnightBridgeError>> + Send {
            self.messages.lock().unwrap().push(message);
            async { Ok(()) }
        }
    }

    /// Build a mock lock event (SCALE-like encoding matching our parser).
    pub fn make_lock_event_data(amount: u64, dregg_recipient: [u8; 32], nonce: u64) -> Vec<u8> {
        let mut data = Vec::with_capacity(48);
        data.extend_from_slice(&amount.to_le_bytes());
        data.extend_from_slice(&dregg_recipient);
        data.extend_from_slice(&nonce.to_le_bytes());
        data
    }
}

#[cfg(test)]
mod tests {
    use super::mock::*;
    use super::*;

    #[test]
    fn test_parse_lock_event() {
        let recipient = [0xAA; 32];
        let data = make_lock_event_data(5_000_000, recipient, 42);
        let event = SubstrateEvent {
            pallet_index: BRIDGE_PALLET_INDEX,
            variant_index: EVENT_BRIDGE_LOCK,
            data,
            extrinsic_index: Some(1),
        };

        let parsed = parse_bridge_event(&event).unwrap();
        match parsed {
            MidnightBridgeEvent::Lock {
                amount,
                dregg_recipient,
                nonce,
            } => {
                assert_eq!(amount, 5_000_000);
                assert_eq!(dregg_recipient, recipient);
                assert_eq!(nonce, 42);
            }
            _ => panic!("expected Lock event"),
        }
    }

    #[test]
    fn test_parse_lock_event_wrong_pallet() {
        let data = make_lock_event_data(100, [0xBB; 32], 1);
        let event = SubstrateEvent {
            pallet_index: 99, // wrong pallet
            variant_index: EVENT_BRIDGE_LOCK,
            data,
            extrinsic_index: None,
        };
        assert!(parse_bridge_event(&event).is_none());
    }

    #[test]
    fn test_parse_lock_event_too_short() {
        let event = SubstrateEvent {
            pallet_index: BRIDGE_PALLET_INDEX,
            variant_index: EVENT_BRIDGE_LOCK,
            data: vec![0u8; 10], // too short
            extrinsic_index: None,
        };
        assert!(parse_bridge_event(&event).is_none());
    }

    #[test]
    fn test_parse_unlock_event() {
        let mut data = Vec::new();
        let amount: u64 = 1_000_000;
        let recipient = vec![0xCC; 32];
        let nullifier = [0xDD; 32];

        data.extend_from_slice(&amount.to_le_bytes());
        data.extend_from_slice(&(recipient.len() as u32).to_le_bytes());
        data.extend_from_slice(&recipient);
        data.extend_from_slice(&nullifier);

        let event = SubstrateEvent {
            pallet_index: BRIDGE_PALLET_INDEX,
            variant_index: EVENT_BRIDGE_UNLOCK,
            data,
            extrinsic_index: Some(0),
        };

        let parsed = parse_bridge_event(&event).unwrap();
        match parsed {
            MidnightBridgeEvent::Unlock {
                amount: a,
                midnight_recipient,
                nullifier: n,
            } => {
                assert_eq!(a, 1_000_000);
                assert_eq!(midnight_recipient, recipient);
                assert_eq!(n, nullifier);
            }
            _ => panic!("expected Unlock event"),
        }
    }

    #[tokio::test]
    async fn test_observer_processes_lock_events() {
        let recipient = [0xEE; 32];
        let block_hash = [0x01; 32];

        let rpc = MockRpcClient {
            headers: vec![SubstrateBlockHeader {
                number: 100,
                hash: block_hash,
                parent_hash: [0x00; 32],
            }],
            events: {
                let mut m = std::collections::HashMap::new();
                m.insert(
                    block_hash,
                    vec![SubstrateEvent {
                        pallet_index: BRIDGE_PALLET_INDEX,
                        variant_index: EVENT_BRIDGE_LOCK,
                        data: make_lock_event_data(5_000_000, recipient, 1),
                        extrinsic_index: Some(0),
                    }],
                );
                m
            },
        };

        let submitter = MockSubmitter::default();
        let config = crate::midnight::MidnightBridgeConfig {
            contract_address: [0xCC; 32],
            midnight_rpc_url: "ws://localhost:9944".to_string(),
            confirmations: 0,
            federation_keys: vec![],
            min_amount: 1_000_000,
            max_amount: 1_000_000_000_000,
        };

        let mut state = ObserverState::default();

        let result = run_observer(rpc, submitter.clone(), config, &mut state).await;
        assert!(result.is_ok());

        let messages = submitter.messages.lock().unwrap();
        assert_eq!(messages.len(), 1);
        assert_eq!(messages[0].amount, 5_000_000);
        assert_eq!(messages[0].dregg_recipient, recipient);
        assert_eq!(messages[0].midnight_height, 100);
        assert_eq!(state.last_processed_height, 100);
    }

    #[tokio::test]
    async fn test_observer_skips_already_processed() {
        let recipient = [0xFF; 32];
        let block_hash = [0x02; 32];

        let rpc = MockRpcClient {
            headers: vec![SubstrateBlockHeader {
                number: 50,
                hash: block_hash,
                parent_hash: [0x01; 32],
            }],
            events: {
                let mut m = std::collections::HashMap::new();
                m.insert(
                    block_hash,
                    vec![SubstrateEvent {
                        pallet_index: BRIDGE_PALLET_INDEX,
                        variant_index: EVENT_BRIDGE_LOCK,
                        data: make_lock_event_data(2_000_000, recipient, 1),
                        extrinsic_index: Some(0),
                    }],
                );
                m
            },
        };

        let submitter = MockSubmitter::default();
        let config = crate::midnight::MidnightBridgeConfig {
            contract_address: [0xCC; 32],
            midnight_rpc_url: "ws://localhost:9944".to_string(),
            confirmations: 0,
            federation_keys: vec![],
            min_amount: 1_000_000,
            max_amount: 1_000_000_000_000,
        };

        // State already at height 100 → block 50 should be skipped.
        let mut state = ObserverState {
            last_processed_height: 100,
            processed_events: vec![],
        };

        let result = run_observer(rpc, submitter.clone(), config, &mut state).await;
        assert!(result.is_ok());

        let messages = submitter.messages.lock().unwrap();
        assert_eq!(
            messages.len(),
            0,
            "already-processed block should be skipped"
        );
    }

    #[tokio::test]
    async fn test_observer_skips_below_minimum() {
        let recipient = [0xAB; 32];
        let block_hash = [0x03; 32];

        let rpc = MockRpcClient {
            headers: vec![SubstrateBlockHeader {
                number: 200,
                hash: block_hash,
                parent_hash: [0x02; 32],
            }],
            events: {
                let mut m = std::collections::HashMap::new();
                m.insert(
                    block_hash,
                    vec![SubstrateEvent {
                        pallet_index: BRIDGE_PALLET_INDEX,
                        variant_index: EVENT_BRIDGE_LOCK,
                        data: make_lock_event_data(100, recipient, 1), // below minimum
                        extrinsic_index: Some(0),
                    }],
                );
                m
            },
        };

        let submitter = MockSubmitter::default();
        let config = crate::midnight::MidnightBridgeConfig {
            contract_address: [0xCC; 32],
            midnight_rpc_url: "ws://localhost:9944".to_string(),
            confirmations: 0,
            federation_keys: vec![],
            min_amount: 1_000_000,
            max_amount: 1_000_000_000_000,
        };

        let mut state = ObserverState::default();

        let result = run_observer(rpc, submitter.clone(), config, &mut state).await;
        assert!(result.is_ok());

        let messages = submitter.messages.lock().unwrap();
        assert_eq!(messages.len(), 0, "below-minimum event should be skipped");
    }

    #[tokio::test]
    async fn test_observer_multiple_blocks_and_events() {
        let recipient1 = [0x11; 32];
        let recipient2 = [0x22; 32];
        let block1 = [0x10; 32];
        let block2 = [0x20; 32];

        let rpc = MockRpcClient {
            headers: vec![
                SubstrateBlockHeader {
                    number: 1,
                    hash: block1,
                    parent_hash: [0x00; 32],
                },
                SubstrateBlockHeader {
                    number: 2,
                    hash: block2,
                    parent_hash: block1,
                },
            ],
            events: {
                let mut m = std::collections::HashMap::new();
                m.insert(
                    block1,
                    vec![SubstrateEvent {
                        pallet_index: BRIDGE_PALLET_INDEX,
                        variant_index: EVENT_BRIDGE_LOCK,
                        data: make_lock_event_data(3_000_000, recipient1, 1),
                        extrinsic_index: Some(0),
                    }],
                );
                m.insert(
                    block2,
                    vec![
                        SubstrateEvent {
                            pallet_index: BRIDGE_PALLET_INDEX,
                            variant_index: EVENT_BRIDGE_LOCK,
                            data: make_lock_event_data(7_000_000, recipient2, 2),
                            extrinsic_index: Some(0),
                        },
                        // Non-bridge event (different pallet).
                        SubstrateEvent {
                            pallet_index: 10,
                            variant_index: 0,
                            data: vec![1, 2, 3],
                            extrinsic_index: Some(1),
                        },
                    ],
                );
                m
            },
        };

        let submitter = MockSubmitter::default();
        let config = crate::midnight::MidnightBridgeConfig {
            contract_address: [0xCC; 32],
            midnight_rpc_url: "ws://localhost:9944".to_string(),
            confirmations: 0,
            federation_keys: vec![],
            min_amount: 1_000_000,
            max_amount: 1_000_000_000_000,
        };

        let mut state = ObserverState::default();

        let result = run_observer(rpc, submitter.clone(), config, &mut state).await;
        assert!(result.is_ok());

        let messages = submitter.messages.lock().unwrap();
        assert_eq!(messages.len(), 2);
        assert_eq!(messages[0].dregg_recipient, recipient1);
        assert_eq!(messages[0].amount, 3_000_000);
        assert_eq!(messages[1].dregg_recipient, recipient2);
        assert_eq!(messages[1].amount, 7_000_000);
        assert_eq!(state.last_processed_height, 2);
    }
}

// ============================================================================
// Tests: the REAL live client (genuine JSON-RPC wire + SCALE decode)
// ============================================================================

#[cfg(test)]
mod live_tests {
    use super::live_support::*;
    use super::mock::MockSubmitter;
    use super::*;

    const RECIPIENT: [u8; 32] = [0xEE; 32];

    fn block(number: u64, hash: u8, parent: u8, records: &[Vec<u8>]) -> CannedBlock {
        CannedBlock {
            number,
            hash: [hash; 32],
            parent_hash: [parent; 32],
            events_hex: system_events_hex(records),
            // One extrinsic so `ApplyExtrinsic(0)` events resolve a tx hash.
            extrinsics: vec![vec![0xDE, 0xAD, 0xBE, 0xEF]],
        }
    }

    fn config() -> crate::midnight::MidnightBridgeConfig {
        crate::midnight::MidnightBridgeConfig {
            contract_address: [0xCC; 32],
            midnight_rpc_url: "ws://localhost:9944".to_string(),
            confirmations: 0,
            federation_keys: vec![],
            min_amount: 1_000_000,
            max_amount: 1_000_000_000_000,
        }
    }

    /// The genuine `chain_getHeader` response shape (hex number, hex parentHash)
    /// parses, and the genuine `state_getStorage` SCALE blob decodes to the bridge
    /// Lock event — over the REAL request/response codec, no network.
    #[tokio::test]
    async fn live_rpc_parses_header_and_decodes_events() {
        let mut node = CannedSubstrateNode::new();
        node.push_block(block(
            7,
            0x07,
            0x06,
            &[bridge_lock_record(0, 5_000_000, RECIPIENT, 1)],
        ));
        let rpc = LiveSubstrateRpc::new(node, 7, false);

        // chain_getHeader shape → number/parent decoded.
        let header = fetch_header(&*rpc.transport, &[0x07; 32]).await.unwrap();
        assert_eq!(header.number, 7);
        assert_eq!(header.parent_hash, [0x06; 32]);

        // state_getStorage SCALE blob → the bridge Lock event.
        let events = rpc.get_events([0x07; 32]).await.unwrap();
        assert_eq!(events.len(), 1);
        let parsed = parse_bridge_event(&events[0]).unwrap();
        match parsed {
            MidnightBridgeEvent::Lock {
                amount,
                dregg_recipient,
                ..
            } => {
                assert_eq!(amount, 5_000_000);
                assert_eq!(dregg_recipient, RECIPIENT);
            }
            _ => panic!("expected Lock"),
        }
        assert_eq!(events[0].extrinsic_index, Some(0));
    }

    /// The decoder walks PAST a registered foreign event to reach a later bridge
    /// event (the metadata-light multi-pallet block case).
    #[tokio::test]
    async fn live_rpc_skips_registered_foreign_event() {
        let foreign = foreign_fixed_record(10, 3, &[1, 2, 3, 4, 5]);
        let lock = bridge_lock_record(2, 9_000_000, RECIPIENT, 7);
        let mut node = CannedSubstrateNode::new();
        node.push_block(CannedBlock {
            number: 4,
            hash: [0x04; 32],
            parent_hash: [0x03; 32],
            events_hex: system_events_hex(&[foreign, lock]),
            extrinsics: vec![],
        });
        let mut layouts = EventLayouts::with_bridge();
        layouts.register_fixed(10, 3, 5);
        let rpc = LiveSubstrateRpc::new(node, 4, false).with_layouts(layouts);

        let events = rpc.get_events([0x04; 32]).await.unwrap();
        assert_eq!(events.len(), 2);
        // The bridge event after the foreign one is reached + parses.
        assert_eq!(events[1].pallet_index, BRIDGE_PALLET_INDEX);
        let parsed = parse_bridge_event(&events[1]).unwrap();
        assert!(matches!(parsed, MidnightBridgeEvent::Lock { amount, .. } if amount == 9_000_000));
    }

    /// An unregistered foreign event is REFUSED (honest metadata boundary) rather
    /// than silently mis-decoded.
    #[tokio::test]
    async fn live_rpc_refuses_unregistered_event() {
        let foreign = foreign_fixed_record(77, 1, &[0xAB; 4]);
        let mut node = CannedSubstrateNode::new();
        node.push_block(CannedBlock {
            number: 2,
            hash: [0x02; 32],
            parent_hash: [0x01; 32],
            events_hex: system_events_hex(&[foreign]),
            extrinsics: vec![],
        });
        let rpc = LiveSubstrateRpc::new(node, 2, false);
        assert!(matches!(
            rpc.get_events([0x02; 32]).await.unwrap_err(),
            MidnightBridgeError::ConnectionFailed { .. }
        ));
    }

    /// The extrinsic hash is BlakeTwo256 of the SCALE extrinsic bytes.
    #[tokio::test]
    async fn live_rpc_extrinsic_hash_is_blake2_256() {
        let ext = vec![0x11u8, 0x22, 0x33, 0x44];
        let mut node = CannedSubstrateNode::new();
        node.push_block(CannedBlock {
            number: 1,
            hash: [0x01; 32],
            parent_hash: [0x00; 32],
            events_hex: String::new(),
            extrinsics: vec![ext.clone()],
        });
        let rpc = LiveSubstrateRpc::new(node, 1, false);
        let got = rpc.get_extrinsic_hash([0x01; 32], 0).await.unwrap();
        assert_eq!(got, blake2_256(&ext));
    }

    /// The full observe round-trip over the LIVE client + an in-memory node:
    /// follow finalized head → decode events → validate → submit. The finalized
    /// head follower yields ONLY finalized blocks (structural finality gate).
    #[tokio::test]
    async fn live_observer_round_trip() {
        let mut node = CannedSubstrateNode::new();
        node.push_block(block(1, 0x01, 0x00, &[]));
        node.push_block(block(
            2,
            0x02,
            0x01,
            &[bridge_lock_record(0, 5_000_000, RECIPIENT, 1)],
        ));
        // `follow = false`: drain to the finalized tip (block 2) then end.
        let rpc = LiveSubstrateRpc::new(node, 1, false);
        let submitter = MockSubmitter::default();
        let mut state = ObserverState::default();

        run_observer(rpc, submitter.clone(), config(), &mut state)
            .await
            .expect("the live observer drains the finalized backlog");

        let messages = submitter.messages.lock().unwrap();
        assert_eq!(messages.len(), 1);
        assert_eq!(messages[0].amount, 5_000_000);
        assert_eq!(messages[0].dregg_recipient, RECIPIENT);
        assert_eq!(messages[0].midnight_height, 2);
        assert_eq!(state.last_processed_height, 2);
    }

    /// A disconnected node at subscribe surfaces as a clean `Err`, not a panic.
    #[tokio::test]
    async fn live_observer_handles_disconnect_at_subscribe() {
        let rpc = LiveSubstrateRpc::new(CannedSubstrateNode::disconnected(), 1, false);
        let submitter = MockSubmitter::default();
        let mut state = ObserverState::default();
        let err = run_observer(rpc, submitter.clone(), config(), &mut state)
            .await
            .unwrap_err();
        assert!(matches!(err, MidnightBridgeError::ConnectionFailed { .. }));
        assert_eq!(submitter.messages.lock().unwrap().len(), 0);
    }
}
