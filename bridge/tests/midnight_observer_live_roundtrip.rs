//! The live Midnight/Substrate observer round-trip — the cross-chain analogue of
//! `solana_relayer_roundtrip.rs`.
//!
//! This proves the REAL `LiveSubstrateRpc` (the live impl behind the async
//! `SubstrateRpcClient` trait) drives the full inbound observation the library was
//! missing, over the GENUINE Substrate JSON-RPC wire (an in-memory node speaking
//! `chain_getFinalizedHead` / `chain_getHeader` / `chain_getBlockHash` /
//! `state_getStorage`), with NO network:
//!
//! 1. a finalized block carrying a real SCALE-encoded `BridgeLock` event → the
//!    observer follows the finalized head, decodes `System::Events`, validates,
//!    and submits the `MidnightToDreggMessage`;
//! 2. the finalized-head follower yields ONLY finalized blocks (the structural
//!    finality gate — an un-finalized block past the finalized tip is never seen);
//! 3. a disconnected node surfaces as a clean `Err` at subscribe, not a panic.
//!
//! The same `subscribe → get_events → validate → submit` path runs against a real
//! Substrate node in production — the only swap is the injected
//! [`SubstrateRpcTransport`] (a jsonrpsee WS transport; REVIEWED-GO — the live
//! mainnet observer). The in-circuit witness of Midnight finality (so a dregg
//! LIGHT client, not a re-executing observer, sees the backing) is the circuit
//! swarm's weld — out of scope here.

use dregg_bridge::midnight::{
    MidnightBridgeConfig, MidnightBridgeError, MidnightToDreggMessage, ObserverState,
};
use dregg_bridge::midnight_observer::live_support::{
    CannedBlock, CannedSubstrateNode, bridge_lock_record, system_events_hex,
};
use dregg_bridge::midnight_observer::{BridgeEventSubmitter, LiveSubstrateRpc, run_observer};
use std::future::Future;
use std::sync::{Arc, Mutex};

const RECIPIENT: [u8; 32] = [0xEE; 32];

/// A submitter that collects the messages the observer accepts.
#[derive(Clone, Default)]
struct CollectingSubmitter {
    messages: Arc<Mutex<Vec<MidnightToDreggMessage>>>,
}

impl BridgeEventSubmitter for CollectingSubmitter {
    fn submit(
        &self,
        message: MidnightToDreggMessage,
    ) -> impl Future<Output = Result<(), MidnightBridgeError>> + Send {
        self.messages.lock().unwrap().push(message);
        async { Ok(()) }
    }
}

fn config() -> MidnightBridgeConfig {
    MidnightBridgeConfig {
        contract_address: [0xCC; 32],
        midnight_rpc_url: "ws://localhost:9944".to_string(),
        confirmations: 0,
        federation_keys: vec![],
        min_amount: 1_000_000,
        max_amount: 1_000_000_000_000,
    }
}

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

#[tokio::test]
async fn live_observer_finalized_block_to_submitted_message() {
    let mut node = CannedSubstrateNode::new();
    node.push_block(block(10, 0x0a, 0x09, &[]));
    node.push_block(block(
        11,
        0x0b,
        0x0a,
        &[bridge_lock_record(0, 5_000_000, RECIPIENT, 1)],
    ));

    // `follow = false`: drain the finalized backlog (heights 10..=11) and end.
    let rpc = LiveSubstrateRpc::new(node, 10, false);
    let submitter = CollectingSubmitter::default();
    let mut state = ObserverState::default();

    run_observer(rpc, submitter.clone(), config(), &mut state)
        .await
        .expect("the live observer drains the finalized backlog");

    let messages = submitter.messages.lock().unwrap();
    assert_eq!(messages.len(), 1, "exactly the one finalized BridgeLock");
    assert_eq!(messages[0].amount, 5_000_000);
    assert_eq!(messages[0].dregg_recipient, RECIPIENT);
    assert_eq!(messages[0].midnight_height, 11);
    assert_eq!(state.last_processed_height, 11);
}

#[tokio::test]
async fn live_observer_only_yields_finalized_blocks() {
    // The node's finalized head is block 5; block 6 is NOT yet finalized (absent
    // from the node), so even starting the follower at 5 it processes only 5.
    let mut node = CannedSubstrateNode::new();
    node.push_block(block(
        5,
        0x05,
        0x04,
        &[bridge_lock_record(0, 2_000_000, RECIPIENT, 1)],
    ));
    let rpc = LiveSubstrateRpc::new(node, 5, false);
    let submitter = CollectingSubmitter::default();
    let mut state = ObserverState::default();

    run_observer(rpc, submitter.clone(), config(), &mut state)
        .await
        .expect("drain to finalized tip");

    // Only the finalized block 5 was observed; the watermark stops at the tip.
    assert_eq!(state.last_processed_height, 5);
    assert_eq!(submitter.messages.lock().unwrap().len(), 1);
}

#[tokio::test]
async fn live_observer_refuses_disconnected_node() {
    let rpc = LiveSubstrateRpc::new(CannedSubstrateNode::disconnected(), 1, false);
    let submitter = CollectingSubmitter::default();
    let mut state = ObserverState::default();

    let err = run_observer(rpc, submitter.clone(), config(), &mut state)
        .await
        .expect_err("a disconnected node surfaces as Err, not a panic");
    assert!(matches!(err, MidnightBridgeError::ConnectionFailed { .. }));
    assert_eq!(submitter.messages.lock().unwrap().len(), 0);
}
