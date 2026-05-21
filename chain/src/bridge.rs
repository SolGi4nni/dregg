//! Base bridge integration: connects the pyana node to the PyanaVault on Base L2.
//!
//! This module provides the top-level entry point for the Base bridge, which:
//! 1. Watches for deposit events on Base (via `VaultEventListener`)
//! 2. Creates corresponding notes in the pyana ledger
//! 3. Handles withdrawal proof generation and on-chain submission
//!
//! # Usage from the node
//!
//! ```rust,no_run
//! use pyana_chain::bridge::{BaseBridgeConfig, start_base_bridge};
//!
//! # async fn example() {
//! let config = BaseBridgeConfig {
//!     rpc_url: "https://mainnet.base.org".to_string(),
//!     vault_address: "0x1234...".to_string(),
//!     program_vkey: [0u8; 32],
//!     poll_interval_secs: 12,
//!     confirmations: 2,
//! };
//!
//! let handle = start_base_bridge(config).await.expect("bridge start failed");
//! // The bridge runs in the background. `handle` can be used to await completion.
//! # }
//! ```

use crate::error::ChainError;
use crate::listener::{ListenerConfig, NoteCreationRequest, VaultEventListener};
use serde::{Deserialize, Serialize};
use tokio::sync::mpsc;
use tokio::task::JoinHandle;

/// Configuration for the Base bridge integration.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct BaseBridgeConfig {
    /// JSON-RPC endpoint for Base L2 (e.g., "https://mainnet.base.org").
    pub rpc_url: String,
    /// Address of the deployed PyanaVault contract (hex with 0x prefix).
    pub vault_address: String,
    /// SP1 program verification key (identifies the correct guest program).
    pub program_vkey: [u8; 32],
    /// Poll interval in seconds for checking new deposit events.
    pub poll_interval_secs: u64,
    /// Number of block confirmations before processing a deposit.
    pub confirmations: u64,
}

impl Default for BaseBridgeConfig {
    fn default() -> Self {
        Self {
            rpc_url: "https://mainnet.base.org".to_string(),
            vault_address: String::new(),
            program_vkey: [0u8; 32],
            poll_interval_secs: 12,
            confirmations: 2,
        }
    }
}

impl BaseBridgeConfig {
    /// Create a config for Base Sepolia testnet.
    pub fn sepolia(vault_address: &str) -> Self {
        Self {
            rpc_url: "https://sepolia.base.org".to_string(),
            vault_address: vault_address.to_string(),
            poll_interval_secs: 12,
            confirmations: 1,
            ..Default::default()
        }
    }

    /// Validate the configuration.
    pub fn validate(&self) -> Result<(), ChainError> {
        if self.rpc_url.is_empty() {
            return Err(ChainError::OnChainError(
                "rpc_url cannot be empty".to_string(),
            ));
        }
        if self.vault_address.is_empty() {
            return Err(ChainError::OnChainError(
                "vault_address cannot be empty".to_string(),
            ));
        }
        let hex = self
            .vault_address
            .strip_prefix("0x")
            .unwrap_or(&self.vault_address);
        if hex.len() != 40 {
            return Err(ChainError::OnChainError(format!(
                "vault_address must be 40 hex chars (got {})",
                hex.len()
            )));
        }
        if self.poll_interval_secs == 0 {
            return Err(ChainError::OnChainError(
                "poll_interval_secs must be > 0".to_string(),
            ));
        }
        Ok(())
    }
}

/// Handle to the running bridge, allowing the caller to monitor or stop it.
pub struct BridgeHandle {
    /// The background task running the event listener.
    pub listener_task: JoinHandle<Result<(), ChainError>>,
    /// The background task processing note creation requests.
    pub processor_task: JoinHandle<()>,
    /// Channel for submitting withdrawal requests (if needed in the future).
    _shutdown_tx: mpsc::Sender<()>,
}

impl BridgeHandle {
    /// Check if the bridge tasks are still running.
    pub fn is_running(&self) -> bool {
        !self.listener_task.is_finished() && !self.processor_task.is_finished()
    }

    /// Wait for the bridge to complete (blocks until error or shutdown).
    pub async fn join(self) -> Result<(), ChainError> {
        tokio::select! {
            result = self.listener_task => {
                match result {
                    Ok(Ok(())) => Ok(()),
                    Ok(Err(e)) => Err(e),
                    Err(e) => Err(ChainError::Other(anyhow::anyhow!("listener task panicked: {e}"))),
                }
            }
            _ = self.processor_task => {
                Err(ChainError::Other(anyhow::anyhow!("processor task exited unexpectedly")))
            }
        }
    }
}

/// Start the Base bridge integration.
///
/// This spawns background tasks that:
/// 1. Watch for deposit events on Base (via the VaultEventListener)
/// 2. Process each deposit event into a note creation in the pyana ledger
///
/// Returns a `BridgeHandle` that can be used to monitor or await the bridge.
///
/// # Arguments
/// * `config` - Bridge configuration (RPC URL, vault address, etc.)
///
/// # Returns
/// A `BridgeHandle` with the spawned background tasks.
pub async fn start_base_bridge(
    config: BaseBridgeConfig,
) -> Result<BridgeHandle, ChainError> {
    config.validate()?;

    tracing::info!(
        rpc = %config.rpc_url,
        vault = %config.vault_address,
        poll_interval = config.poll_interval_secs,
        confirmations = config.confirmations,
        "starting Base bridge"
    );

    // Channel for deposit events from the listener to the processor.
    let (note_tx, note_rx) = mpsc::channel::<NoteCreationRequest>(256);
    let (_shutdown_tx, _shutdown_rx) = mpsc::channel::<()>(1);

    // Create the event listener.
    let listener_config = ListenerConfig {
        rpc_url: config.rpc_url.clone(),
        vault_address: config.vault_address.clone(),
        poll_interval_secs: config.poll_interval_secs,
        from_block: 0,
        confirmations: config.confirmations,
    };
    let listener = VaultEventListener::with_config(listener_config, note_tx);

    // Spawn the listener task.
    let listener_task = tokio::spawn(async move { listener.run().await });

    // Spawn the processor task.
    let processor_task = tokio::spawn(process_note_requests(note_rx));

    Ok(BridgeHandle {
        listener_task,
        processor_task,
        _shutdown_tx,
    })
}

/// Process incoming note creation requests from the event listener.
///
/// In a full implementation, this would:
/// - Verify the deposit event against the on-chain state
/// - Create a corresponding note in the pyana ledger
/// - Update the local note tree to match the on-chain tree
///
/// For now, it logs the events and tracks statistics.
async fn process_note_requests(mut rx: mpsc::Receiver<NoteCreationRequest>) {
    let mut processed_count: u64 = 0;
    let mut total_value: u64 = 0;

    tracing::info!("note request processor started");

    while let Some(req) = rx.recv().await {
        processed_count += 1;
        total_value = total_value.saturating_add(req.amount);

        let commitment_hex: String = req
            .note_commitment
            .iter()
            .take(8)
            .map(|b| format!("{b:02x}"))
            .collect();

        tracing::info!(
            block = req.block_number,
            amount = req.amount,
            leaf_index = req.leaf_index,
            commitment = %commitment_hex,
            total_processed = processed_count,
            "deposit event -> note creation"
        );

        // TODO: Integrate with the pyana node's ledger:
        // 1. Verify the deposit was confirmed on-chain (re-check via RPC)
        // 2. Create a NoteCell in the pyana ledger
        // 3. Update the local Merkle tree
        // 4. Notify the federation of the new note commitment
    }

    tracing::warn!(
        processed = processed_count,
        total_value = total_value,
        "note request processor channel closed"
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_config_validation_valid() {
        let config = BaseBridgeConfig {
            rpc_url: "https://mainnet.base.org".to_string(),
            vault_address: "0x3B6041173B80E77f038f3F2C0f9744f04837185e".to_string(),
            program_vkey: [0; 32],
            poll_interval_secs: 12,
            confirmations: 2,
        };
        assert!(config.validate().is_ok());
    }

    #[test]
    fn test_config_validation_empty_rpc() {
        let config = BaseBridgeConfig {
            rpc_url: "".to_string(),
            vault_address: "0x3B6041173B80E77f038f3F2C0f9744f04837185e".to_string(),
            ..Default::default()
        };
        assert!(config.validate().is_err());
    }

    #[test]
    fn test_config_validation_empty_vault() {
        let config = BaseBridgeConfig {
            rpc_url: "https://mainnet.base.org".to_string(),
            vault_address: "".to_string(),
            ..Default::default()
        };
        assert!(config.validate().is_err());
    }

    #[test]
    fn test_config_validation_bad_vault_address() {
        let config = BaseBridgeConfig {
            rpc_url: "https://mainnet.base.org".to_string(),
            vault_address: "0x1234".to_string(), // Too short
            ..Default::default()
        };
        assert!(config.validate().is_err());
    }

    #[test]
    fn test_config_validation_zero_poll_interval() {
        let config = BaseBridgeConfig {
            rpc_url: "https://mainnet.base.org".to_string(),
            vault_address: "0x3B6041173B80E77f038f3F2C0f9744f04837185e".to_string(),
            poll_interval_secs: 0,
            ..Default::default()
        };
        assert!(config.validate().is_err());
    }

    #[test]
    fn test_sepolia_config() {
        let config = BaseBridgeConfig::sepolia("0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef");
        assert!(config.rpc_url.contains("sepolia"));
        assert_eq!(config.confirmations, 1);
    }

    #[tokio::test]
    async fn test_process_note_requests_handles_close() {
        let (tx, rx) = mpsc::channel(16);

        // Send a few requests then drop the sender.
        tx.send(NoteCreationRequest {
            token: [0; 20],
            amount: 100,
            note_commitment: [0xAA; 32],
            depositor: [0; 20],
            block_number: 1,
            leaf_index: 0,
        })
        .await
        .unwrap();

        drop(tx);

        // Processor should handle the close gracefully.
        process_note_requests(rx).await;
    }
}
