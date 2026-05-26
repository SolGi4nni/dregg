//! Batch execution trait for apps that act as delegated turn executors.
//!
//! Some apps (e.g. a rollup sequencer, a compute-exchange provider) collect
//! turns from multiple clients and execute them in batches for efficiency.
//! Apps implement [`BatchExecutor`] to hook into the framework's collection
//! and proof pipeline.
//!
//! # Usage
//!
//! ```ignore
//! use dregg_app_framework::batch_executor::{BatchExecutor, ClientTurnRequest, BatchExecution};
//!
//! impl BatchExecutor for MySequencer {
//!     type Error = MyError;
//!     fn collect_batch(&mut self, max_size: usize) -> Vec<ClientTurnRequest> { ... }
//!     fn execute_batch(&mut self, batch: Vec<ClientTurnRequest>) -> Result<BatchExecution, MyError> { ... }
//! }
//! ```

use dregg_types::CellId;

/// A single turn request from a client, queued for batch execution.
#[derive(Clone, Debug)]
pub struct ClientTurnRequest {
    /// The client cell submitting the turn.
    pub client: CellId,
    /// Serialized turn bytes (format determined by the app's turn schema).
    pub turn_bytes: Vec<u8>,
    /// Optional deadline block height; turns past their deadline may be dropped.
    pub deadline_height: Option<u64>,
}

/// The result of executing a batch of turns.
#[derive(Clone, Debug)]
pub struct BatchExecution {
    /// Content-addressed identifier for this batch (e.g. hash of all turn bytes).
    pub batch_id: [u8; 32],
    /// Number of turns successfully included in this batch.
    pub turn_count: usize,
    /// Optional proof over the batch state transition.
    /// `None` means the executor is running in optimistic (non-proven) mode.
    pub proof: Option<Vec<u8>>,
}

/// Trait for apps that batch client turns and execute them as a group.
///
/// The framework calls `collect_batch` to gather pending turns (up to
/// `max_size`), then `execute_batch` to run them and produce a proof.
/// Apps are free to order, filter, or prioritize turns inside these methods.
pub trait BatchExecutor {
    /// Error type returned by batch operations.
    type Error: std::fmt::Debug;

    /// Collect up to `max_size` pending turn requests from the internal queue.
    ///
    /// Returns an empty `Vec` if no turns are pending. Must not block.
    fn collect_batch(&mut self, max_size: usize) -> Vec<ClientTurnRequest>;

    /// Execute a batch of turns and return the execution result (+ optional proof).
    ///
    /// Implementations should apply the turns to their state, compute the batch
    /// ID (e.g. `blake3` of all turn bytes), and optionally generate a STARK
    /// proof over the state transition.
    fn execute_batch(
        &mut self,
        batch: Vec<ClientTurnRequest>,
    ) -> Result<BatchExecution, Self::Error>;
}

#[cfg(test)]
mod tests {
    use super::*;

    struct EchoBatchExecutor {
        queue: Vec<ClientTurnRequest>,
    }

    #[derive(Debug)]
    struct NoError;

    impl BatchExecutor for EchoBatchExecutor {
        type Error = NoError;

        fn collect_batch(&mut self, max_size: usize) -> Vec<ClientTurnRequest> {
            let n = max_size.min(self.queue.len());
            self.queue.drain(..n).collect()
        }

        fn execute_batch(
            &mut self,
            batch: Vec<ClientTurnRequest>,
        ) -> Result<BatchExecution, NoError> {
            let mut hasher = blake3::Hasher::new();
            for req in &batch {
                hasher.update(&req.turn_bytes);
            }
            Ok(BatchExecution {
                batch_id: *hasher.finalize().as_bytes(),
                turn_count: batch.len(),
                proof: None,
            })
        }
    }

    #[test]
    fn collect_and_execute_roundtrip() {
        let mut exec = EchoBatchExecutor {
            queue: vec![
                ClientTurnRequest {
                    client: CellId([1u8; 32]),
                    turn_bytes: b"turn_a".to_vec(),
                    deadline_height: None,
                },
                ClientTurnRequest {
                    client: CellId([2u8; 32]),
                    turn_bytes: b"turn_b".to_vec(),
                    deadline_height: Some(9999),
                },
            ],
        };

        let batch = exec.collect_batch(10);
        assert_eq!(batch.len(), 2);

        let result = exec.execute_batch(batch).unwrap();
        assert_eq!(result.turn_count, 2);
        assert!(result.proof.is_none());
        // batch_id is deterministic
        assert_ne!(result.batch_id, [0u8; 32]);
    }
}
