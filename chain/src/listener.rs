//! Vault event listener: watches for deposit events on Base and creates pyana notes.
//!
//! The listener polls the PyanaVault contract for `Deposit` events and converts each
//! into a `NoteCreationRequest` that the pyana node processes to mirror the deposit
//! in its private note tree.
//!
//! # Architecture
//!
//! ```text
//! Base L2 (PyanaVault contract)
//!   │
//!   │  emits Deposit(token, amount, noteCommitment, leafIndex)
//!   │
//!   v
//! VaultEventListener (this module)
//!   │
//!   │  polls via eth_getLogs / eth_subscribe
//!   │
//!   v
//! NoteCreationRequest -> node note tree
//! ```
//!
//! # Usage
//!
//! ```rust,no_run
//! use pyana_chain::listener::{VaultEventListener, NoteCreationRequest};
//! use tokio::sync::mpsc;
//!
//! # async fn example() {
//! let (note_tx, mut note_rx) = mpsc::channel::<NoteCreationRequest>(256);
//!
//! let listener = VaultEventListener::new(
//!     "https://mainnet.base.org",
//!     "0x1234567890abcdef1234567890abcdef12345678",
//!     note_tx,
//! );
//!
//! // Spawn the listener in a background task.
//! tokio::spawn(async move {
//!     listener.run().await.expect("listener failed");
//! });
//!
//! // Process incoming note creation requests.
//! while let Some(req) = note_rx.recv().await {
//!     println!("New deposit: {} tokens at commitment {:?}", req.amount, req.note_commitment);
//! }
//! # }
//! ```

use crate::error::ChainError;
use serde::{Deserialize, Serialize};
use tokio::sync::mpsc;

/// A 20-byte Ethereum address.
pub type Address = [u8; 20];

/// Request to create a note in the pyana ledger mirroring an on-chain deposit.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct NoteCreationRequest {
    /// The ERC-20 token address (all zeros for native ETH).
    pub token: Address,
    /// The deposited amount (in token's smallest unit).
    pub amount: u64,
    /// The Poseidon2 note commitment (matches on-chain noteCommitment).
    pub note_commitment: [u8; 32],
    /// The depositor's Ethereum address.
    pub depositor: Address,
    /// The Base L2 block number where the deposit was confirmed.
    pub block_number: u64,
    /// The leaf index in the on-chain note commitment tree.
    pub leaf_index: u64,
}

/// Configuration for the vault event listener.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ListenerConfig {
    /// JSON-RPC endpoint for Base L2.
    pub rpc_url: String,
    /// Address of the PyanaVault contract (hex string with 0x prefix).
    pub vault_address: String,
    /// Poll interval in seconds (for chains without WebSocket subscription support).
    pub poll_interval_secs: u64,
    /// Starting block number (0 = latest).
    pub from_block: u64,
    /// Number of confirmations to wait before processing a deposit.
    pub confirmations: u64,
}

impl Default for ListenerConfig {
    fn default() -> Self {
        Self {
            rpc_url: "https://mainnet.base.org".to_string(),
            vault_address: String::new(),
            poll_interval_secs: 12,
            from_block: 0,
            confirmations: 2,
        }
    }
}

/// Watches for vault deposit events on Base and sends note creation requests.
///
/// The listener maintains a cursor (last processed block) and polls for new
/// `Deposit` events. Each event is converted into a `NoteCreationRequest` and
/// sent through the provided channel.
pub struct VaultEventListener {
    config: ListenerConfig,
    /// Channel to send note creation requests to the pyana node.
    note_tx: mpsc::Sender<NoteCreationRequest>,
    /// Last processed block number (persisted across restarts via the node).
    last_block: u64,
}

impl VaultEventListener {
    /// Create a new vault event listener.
    ///
    /// # Arguments
    /// * `rpc_url` - Base L2 JSON-RPC endpoint
    /// * `vault_address` - PyanaVault contract address (hex with 0x prefix)
    /// * `note_tx` - Channel for sending note creation requests to the node
    pub fn new(
        rpc_url: &str,
        vault_address: &str,
        note_tx: mpsc::Sender<NoteCreationRequest>,
    ) -> Self {
        Self {
            config: ListenerConfig {
                rpc_url: rpc_url.to_string(),
                vault_address: vault_address.to_string(),
                ..Default::default()
            },
            note_tx,
            last_block: 0,
        }
    }

    /// Create a listener with full configuration.
    pub fn with_config(config: ListenerConfig, note_tx: mpsc::Sender<NoteCreationRequest>) -> Self {
        let from_block = config.from_block;
        Self {
            config,
            note_tx,
            last_block: from_block,
        }
    }

    /// Start polling for Deposit events.
    ///
    /// This runs indefinitely, polling the RPC endpoint at the configured interval.
    /// For each `Deposit` event found, it sends a `NoteCreationRequest` through the channel.
    ///
    /// # Errors
    /// Returns `ChainError::RpcError` if the RPC connection fails persistently.
    pub async fn run(&self) -> Result<(), ChainError> {
        tracing::info!(
            vault = %self.config.vault_address,
            rpc = %self.config.rpc_url,
            poll_interval = self.config.poll_interval_secs,
            "vault event listener starting"
        );

        let poll_interval =
            tokio::time::Duration::from_secs(self.config.poll_interval_secs);

        // Parse the vault address.
        let vault_addr = parse_address(&self.config.vault_address)?;

        // Deposit event topic: keccak256("Deposit(address,uint256,bytes32,uint256)")
        let deposit_topic = compute_event_topic(
            "Deposit(address,uint256,bytes32,uint256)",
        );

        let mut cursor = self.last_block;
        let mut consecutive_errors = 0u32;

        loop {
            match self
                .poll_events(vault_addr, &deposit_topic, cursor)
                .await
            {
                Ok(events) => {
                    consecutive_errors = 0;
                    for event in &events {
                        if let Err(e) = self.note_tx.send(event.clone()).await {
                            tracing::error!(error = %e, "failed to send note creation request (channel closed)");
                            return Err(ChainError::Other(anyhow::anyhow!(
                                "note channel closed"
                            )));
                        }
                        if event.block_number > cursor {
                            cursor = event.block_number;
                        }
                    }
                    if !events.is_empty() {
                        tracing::info!(
                            count = events.len(),
                            latest_block = cursor,
                            "processed deposit events"
                        );
                    }
                }
                Err(e) => {
                    consecutive_errors += 1;
                    tracing::warn!(
                        error = %e,
                        consecutive_errors = consecutive_errors,
                        "failed to poll vault events"
                    );
                    // Back off on persistent errors.
                    if consecutive_errors > 10 {
                        return Err(e);
                    }
                }
            }

            tokio::time::sleep(poll_interval).await;
        }
    }

    /// Poll for deposit events from the given block onwards.
    ///
    /// In the `on-chain` feature mode, this uses alloy to make real RPC calls.
    /// In mock mode, it returns an empty vec (no real chain to poll).
    async fn poll_events(
        &self,
        _vault_addr: Address,
        _deposit_topic: &[u8; 32],
        _from_block: u64,
    ) -> Result<Vec<NoteCreationRequest>, ChainError> {
        #[cfg(feature = "on-chain")]
        {
            return self
                .poll_events_real(_vault_addr, _deposit_topic, _from_block)
                .await;
        }

        #[cfg(not(feature = "on-chain"))]
        {
            // Mock mode: no real events to poll.
            Ok(Vec::new())
        }
    }

    /// Real event polling using alloy (requires `on-chain` feature).
    #[cfg(feature = "on-chain")]
    async fn poll_events_real(
        &self,
        vault_addr: Address,
        deposit_topic: &[u8; 32],
        from_block: u64,
    ) -> Result<Vec<NoteCreationRequest>, ChainError> {
        use alloy::primitives::{Address as AlloyAddress, FixedBytes, U256};
        use alloy::providers::{Provider, ProviderBuilder};
        use alloy::rpc::types::{Filter, Log};

        let provider = ProviderBuilder::new()
            .connect(&self.config.rpc_url)
            .await
            .map_err(|e| ChainError::RpcError(format!("connection failed: {e}")))?;

        // Get latest block for confirmation check.
        let latest_block = provider
            .get_block_number()
            .await
            .map_err(|e| ChainError::RpcError(format!("get_block_number failed: {e}")))?;

        let safe_block = latest_block.saturating_sub(self.config.confirmations);
        if from_block >= safe_block {
            return Ok(Vec::new());
        }

        // Build the log filter.
        let contract_addr = AlloyAddress::from_slice(&vault_addr);
        let topic0 = FixedBytes::<32>::from_slice(deposit_topic);

        let filter = Filter::new()
            .address(contract_addr)
            .event_signature(topic0)
            .from_block(from_block + 1)
            .to_block(safe_block);

        let logs = provider
            .get_logs(&filter)
            .await
            .map_err(|e| ChainError::RpcError(format!("get_logs failed: {e}")))?;

        // Parse each log into a NoteCreationRequest.
        let mut requests = Vec::with_capacity(logs.len());
        for log in logs {
            if let Some(req) = parse_deposit_log(&log) {
                requests.push(req);
            }
        }

        Ok(requests)
    }
}

/// Parse a raw deposit log into a NoteCreationRequest.
#[cfg(feature = "on-chain")]
fn parse_deposit_log(log: &alloy::rpc::types::Log) -> Option<NoteCreationRequest> {
    use alloy::primitives::U256;

    let block_number = log.block_number?;
    let data = log.data();

    // Deposit event ABI:
    //   event Deposit(address indexed token, uint256 amount, bytes32 noteCommitment, uint256 leafIndex)
    // Indexed params are in topics[1..], non-indexed are in data.

    // topics[0] = event signature
    // topics[1] = token address (indexed, padded to 32 bytes)
    let token_topic = log.topics().get(1)?;
    let mut token = [0u8; 20];
    token.copy_from_slice(&token_topic[12..32]);

    // data = abi.encode(uint256 amount, bytes32 noteCommitment, uint256 leafIndex)
    let data_bytes = data.data.as_ref();
    if data_bytes.len() < 96 {
        return None;
    }

    let amount = U256::from_be_slice(&data_bytes[0..32]);
    let mut note_commitment = [0u8; 32];
    note_commitment.copy_from_slice(&data_bytes[32..64]);
    let leaf_index = U256::from_be_slice(&data_bytes[64..96]);

    // Extract depositor from the transaction (not available in basic log).
    // For now, use zeros; the node can look it up from the tx receipt if needed.
    let depositor = [0u8; 20];

    Some(NoteCreationRequest {
        token,
        amount: amount.try_into().unwrap_or(u64::MAX),
        note_commitment,
        depositor,
        block_number,
        leaf_index: leaf_index.try_into().unwrap_or(0),
    })
}

// ─── Helpers ────────────────────────────────────────────────────────────────

/// Parse a hex address string (with or without 0x prefix) into a 20-byte array.
fn parse_address(hex_str: &str) -> Result<Address, ChainError> {
    let hex = hex_str.strip_prefix("0x").unwrap_or(hex_str);
    if hex.len() != 40 {
        return Err(ChainError::OnChainError(format!(
            "invalid address length: expected 40 hex chars, got {}",
            hex.len()
        )));
    }
    let bytes = hex::decode(hex)
        .map_err(|e| ChainError::OnChainError(format!("invalid address hex: {e}")))?;
    let mut addr = [0u8; 20];
    addr.copy_from_slice(&bytes);
    Ok(addr)
}

/// Compute the keccak256 topic hash for an event signature.
///
/// Uses a simplified keccak256 implementation (or falls back to the one from
/// the alloy feature). For the mock feature, we use blake3 as a stand-in since
/// the exact topic value doesn't matter in mock mode.
fn compute_event_topic(signature: &str) -> [u8; 32] {
    #[cfg(feature = "on-chain")]
    {
        use alloy::primitives::keccak256;
        *keccak256(signature.as_bytes())
    }

    #[cfg(not(feature = "on-chain"))]
    {
        // In mock mode, use blake3 as a stand-in for keccak256.
        // The actual topic value is irrelevant without real chain interaction.
        *blake3::hash(signature.as_bytes()).as_bytes()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_address_with_prefix() {
        let addr = parse_address("0x3B6041173B80E77f038f3F2C0f9744f04837185e").unwrap();
        assert_eq!(addr[0], 0x3B);
        assert_eq!(addr[19], 0x5e);
    }

    #[test]
    fn test_parse_address_without_prefix() {
        let addr = parse_address("3B6041173B80E77f038f3F2C0f9744f04837185e").unwrap();
        assert_eq!(addr[0], 0x3B);
    }

    #[test]
    fn test_parse_address_invalid_length() {
        assert!(parse_address("0x1234").is_err());
    }

    #[test]
    fn test_note_creation_request_serialization() {
        let req = NoteCreationRequest {
            token: [0u8; 20],
            amount: 1_000_000,
            note_commitment: [0xAA; 32],
            depositor: [0xBB; 20],
            block_number: 12345,
            leaf_index: 0,
        };
        let json = serde_json::to_string(&req).unwrap();
        let decoded: NoteCreationRequest = serde_json::from_str(&json).unwrap();
        assert_eq!(decoded.amount, 1_000_000);
        assert_eq!(decoded.note_commitment, [0xAA; 32]);
    }

    #[tokio::test]
    async fn test_listener_creation() {
        let (tx, _rx) = mpsc::channel(16);
        let listener = VaultEventListener::new(
            "https://mainnet.base.org",
            "0x3B6041173B80E77f038f3F2C0f9744f04837185e",
            tx,
        );
        assert_eq!(listener.config.rpc_url, "https://mainnet.base.org");
        assert_eq!(listener.config.poll_interval_secs, 12);
    }
}
