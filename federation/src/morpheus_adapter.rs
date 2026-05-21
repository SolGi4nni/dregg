//! Morpheus consensus adapter for the federation crate.
//!
//! The morpheus adapter provides full DAG-based BFT with BLS threshold signatures.
//! Without this feature (`morpheus`), the simplified round-robin consensus is used.
//!
//! This module bridges the morpheus protocol's message types and process lifecycle
//! into the federation's existing `ConsensusState` / `FederationTransport` interface.
//! It allows a federation node to use the morpheus consensus engine for block
//! finalization instead of the simplified single-round-per-block approach.
//!
//! # Usage
//!
//! ```ignore
//! use pyana_federation::morpheus_adapter::MorpheusAdapter;
//!
//! let adapter = MorpheusAdapter::new(config, node_id);
//! adapter.submit_event(revocation_event);
//!
//! // In the message processing loop:
//! adapter.handle_incoming(raw_bytes);
//! for block in adapter.take_finalized() {
//!     // apply to state
//! }
//! ```

use std::collections::VecDeque;

use pyana_morpheus::test_harness::TestTransaction;
use pyana_morpheus::{Identity, KeyBook, Message, MorpheusProcess, ViewNum};

use crate::consensus::ConsensusConfig;
use crate::types::RevocationEvent;

/// Configuration for the Morpheus adapter.
#[derive(Clone, Debug)]
pub struct MorpheusAdapterConfig {
    /// The federation consensus config (node count, threshold, etc.)
    pub federation_config: ConsensusConfig,
    /// The node's index in the federation (0-based).
    pub node_id: usize,
    /// Network delay parameter (delta) in logical time units.
    pub delta: u128,
}

/// Wraps a `MorpheusProcess` to provide the federation with DAG-based BFT consensus.
///
/// The adapter translates between the federation's revocation-event-based interface
/// and the morpheus protocol's generic transaction block machinery.
pub struct MorpheusAdapter {
    /// The underlying morpheus process instance.
    process: MorpheusProcess<TestTransaction>,
    /// Outbound messages produced by the morpheus process, waiting to be sent
    /// via the federation transport layer.
    outbox: VecDeque<(Message<TestTransaction>, Option<Identity>)>,
    /// Blocks that morpheus has finalized but the federation layer has not yet consumed.
    finalized_blocks: VecDeque<FinalizedMorpheusBlock>,
    /// Pending revocation events to be included in the next transaction block.
    pending_events: Vec<RevocationEvent>,
    /// Adapter configuration.
    config: MorpheusAdapterConfig,
}

/// A block finalized by the morpheus consensus engine, translated into federation terms.
#[derive(Clone, Debug)]
pub struct FinalizedMorpheusBlock {
    /// The view in which this block was finalized.
    pub view: i64,
    /// The height of the finalized block.
    pub height: usize,
    /// The revocation events contained in this block (if it was a transaction block).
    pub events: Vec<RevocationEvent>,
}

impl MorpheusAdapter {
    /// Create a new morpheus adapter for a federation node.
    ///
    /// # Arguments
    ///
    /// * `config` - Adapter configuration including node identity and federation params.
    /// * `keybook` - The BLS key material for the morpheus threshold signature scheme.
    pub fn new(config: MorpheusAdapterConfig, keybook: KeyBook) -> Self {
        let n = config.federation_config.num_nodes as u32;
        let f = config.federation_config.max_faults as u32;
        let id = Identity(config.node_id as u32 + 1); // morpheus uses 1-indexed identities

        let mut process = MorpheusProcess::new(keybook, id, n, f);
        process.delta = config.delta;

        MorpheusAdapter {
            process,
            outbox: VecDeque::new(),
            finalized_blocks: VecDeque::new(),
            pending_events: Vec::new(),
            config,
        }
    }

    /// Submit a revocation event to be included in the next morpheus transaction block.
    pub fn submit_event(&mut self, event: RevocationEvent) {
        self.pending_events.push(event);
    }

    /// Advance the morpheus process's logical clock.
    pub fn set_time(&mut self, now: u128) {
        self.process.set_now(now);
    }

    /// Feed an incoming morpheus protocol message from the transport layer.
    ///
    /// Returns true if the message was processed successfully.
    pub fn handle_incoming(&mut self, message: Message<TestTransaction>, sender: Identity) -> bool {
        let mut to_send = Vec::new();
        let result = self.process.process_message(message, sender, &mut to_send);
        self.outbox.extend(to_send.into_iter());
        result
    }

    /// Check protocol timeouts and produce any necessary view-change messages.
    pub fn check_timeouts(&mut self) {
        let mut to_send = Vec::new();
        self.process.check_timeouts(&mut to_send);
        self.outbox.extend(to_send.into_iter());
    }

    /// Attempt to produce a new block if the process has pending transactions
    /// and the protocol state allows it.
    pub fn try_produce_block(&mut self) {
        // Convert pending revocation events into morpheus test transactions.
        // In a full integration, we'd define a proper Transaction type; for now
        // we serialize events into the TestTransaction payload.
        if !self.pending_events.is_empty() {
            for event in self.pending_events.drain(..) {
                let payload = postcard::to_stdvec(&event).unwrap_or_default();
                self.process
                    .ready_transactions
                    .push(TestTransaction(payload));
            }
        }

        let mut to_send = Vec::new();
        self.process.try_produce_blocks(&mut to_send);
        self.outbox.extend(to_send.into_iter());
    }

    /// Drain outbound messages that need to be sent via the federation transport.
    ///
    /// Each entry is (message, optional_target). If target is None, broadcast to all.
    pub fn drain_outbox(
        &mut self,
    ) -> impl Iterator<Item = (Message<TestTransaction>, Option<Identity>)> + '_ {
        self.outbox.drain(..)
    }

    /// Take all finalized blocks that have not yet been consumed by the federation layer.
    pub fn take_finalized(&mut self) -> Vec<FinalizedMorpheusBlock> {
        self.finalized_blocks.drain(..).collect()
    }

    /// Get a reference to the underlying morpheus process (for inspection/debugging).
    pub fn process(&self) -> &MorpheusProcess<TestTransaction> {
        &self.process
    }

    /// Get the current view of the morpheus process.
    pub fn current_view(&self) -> ViewNum {
        self.process.view_i
    }

    /// Get the number of finalized blocks tracked by the morpheus process.
    pub fn finalized_count(&self) -> usize {
        self.process.index.finalized.len()
    }
}
