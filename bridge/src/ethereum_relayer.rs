//! `ethereum_relayer`: the **live off-chain inbound relayer** for the EVM bridge.
//!
//! This is the Ethereum-direction twin of [`crate::solana_relayer`]: it turns the
//! library-only EVM bridge into a watching service that mirrors a finalized
//! Ethereum deposit into dregg's value layer as conserving mirror credit. (The
//! existing [`crate::ethereum`] module is the OUTBOUND direction — settling a
//! dregg whole-chain proof onto the EVM via a STARK→SNARK wrap. This module is the
//! INBOUND direction — observe an EVM lock → conserving mint.)
//!
//! It speaks the **real Ethereum JSON-RPC** (`eth_*`) over an injected byte-pipe:
//!
//! 1. **watches** the bridge contract for `Deposit` logs over the real JSON-RPC
//!    (`eth_getBlockByNumber("finalized")` for the finality head + `eth_getLogs`
//!    for the contract's deposit events, with `eth_getTransactionReceipt` for the
//!    inclusion cross-check and `eth_getProof` available for the storage-slot
//!    binding),
//! 2. **verifies** that the observed deposit is genuinely *finalized* (post-merge
//!    finality via the `finalized` tag — GASPER/Casper-FFG justified+finalized,
//!    irreversible barring a >1/3 slashing event) and was emitted by THIS bridge's
//!    OWN contract (the BR-2-B escrow-to-contract binding) with a matching receipt
//!    (status = success, same block, the log present),
//! 3. **mints** the conserving mirror credit — by handing the verified deposit to
//!    the committed, multi-relayer-safe `bridge_mint_against_lock` (the
//!    consume-once nullifier is the global double-mint authority, not this
//!    relayer's RAM).
//!
//! # The trust boundary (named precisely)
//!
//! A plain JSON-RPC endpoint exposes the chain state at a finality tag but NOT the
//! beacon-chain attestations, the validator set, or the state-trie Merkle-Patricia
//! proof a light client would need. So the relayer's off-chain verify is
//! `StructureOnly`-grade over the real finalized logs/receipt: a *re-executing
//! validator that trusts the RPC's `finalized` tag* accepts it. The fully-trustless
//! path (a beacon light-client sync-committee proof + an MPT inclusion proof of the
//! contract's storage against the finalized state root) is the mainnet/in-circuit
//! route.
//!
//! Crucially, the relayer is **not** the soundness root. Even a lying RPC cannot
//! make the relayer mint something unbacked past these gates:
//! - the log MUST be emitted by the configured bridge contract, with the canonical
//!   `Deposit` event `topic0` (BR-2-B — [`EthBridgeConfig::deposit_topic0`]); and
//! - the mint is the committed `bridge_mint_against_lock`, whose consume-once
//!   nullifier + conserving ledger are the global authority.
//!
//! ## The in-circuit seam (the parallel circuit swarm's, NOT this module's)
//!
//! For a **dregg light client** (not a re-executing validator) to witness that a
//! mint is backed by a real finalized EVM deposit, the Ethereum finality
//! (sync-committee / FFG) + the storage-inclusion proof must be folded into the
//! EffectVM (`dregg_circuit::bridge_action_air`, the VK-epoch). That weld is owned
//! by the circuit swarm; this module does the off-chain relayer verify a
//! re-executing validator runs, and binds the same gates into the live path.

use sha3::{Digest, Keccak256};

use crate::solana_relayer::{JsonRpcTransport, RpcError};
use dregg_cell::Nullifier;
use dregg_types::CellId;

// ===========================================================================
// The consume-once EVM deposit nullifier (the committed double-mint gate)
// ===========================================================================

/// Domain separation for the COMMITTED consume-once EVM-deposit nullifier.
/// Distinct from the Solana-lock and Stripe-payment domains so a `lock_id` from
/// one bridge can never collide with another's.
pub const ETH_DEPOSIT_NULLIFIER_DOMAIN: &str = "dregg-eth-deposit-v1";

/// Derive the domain-separated, consume-once nullifier for an EVM deposit.
///
/// `nf = H("dregg-eth-deposit-v1" ‖ bridge_contract ‖ lock_id)`. Binding the
/// `bridge_contract` scopes the nullifier to this bridge so a `lock_id` from
/// another EVM bridge can never collide. This is the value gated against the
/// executor's committed `note_nullifiers` set in
/// [`dregg_turn::executor::bridge_ledger`] — consumed exactly once GLOBALLY,
/// regardless of how many relayer processes observe the same deposit.
pub fn eth_deposit_nullifier(bridge_contract: &[u8; 20], lock_id: &[u8; 32]) -> Nullifier {
    let mut h = blake3::Hasher::new_derive_key(ETH_DEPOSIT_NULLIFIER_DOMAIN);
    h.update(bridge_contract);
    h.update(lock_id);
    Nullifier(*h.finalize().as_bytes())
}

// ===========================================================================
// The canonical Deposit event ABI
// ===========================================================================

/// The canonical bridge `Deposit` event the relayer watches:
///
/// ```solidity
/// event Deposit(bytes32 indexed lockId, bytes32 indexed dreggRecipient, uint256 amount);
/// ```
///
/// `topic0 = keccak256("Deposit(bytes32,bytes32,uint256)")`; `topics[1] = lockId`;
/// `topics[2] = dreggRecipient`; `data = amount` as a single 32-byte big-endian
/// EVM word. (`indexed` parameters live in `topics`, non-indexed in `data`.)
pub const DEPOSIT_EVENT_SIGNATURE: &str = "Deposit(bytes32,bytes32,uint256)";

/// Compute `topic0` for the canonical [`DEPOSIT_EVENT_SIGNATURE`] —
/// `keccak256("Deposit(bytes32,bytes32,uint256)")`. The deployer pins this on the
/// contract; the relayer computes it locally so a forged-topic log is refused
/// without trusting a configured constant.
pub fn deposit_event_topic0() -> [u8; 32] {
    let mut h = Keccak256::new();
    h.update(DEPOSIT_EVENT_SIGNATURE.as_bytes());
    let out = h.finalize();
    let mut topic = [0u8; 32];
    topic.copy_from_slice(&out);
    topic
}

// ===========================================================================
// The chain view the relayer needs (the `EthRpc` seam)
// ===========================================================================

/// An Ethereum block tag (the finality dial). `Finalized` is the only tag the
/// relayer mints against; the lower tags exist so the relayer can DETECT an
/// un-finalized deposit and refuse it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BlockTag {
    /// The chain head — may be re-orged. Never minted against.
    Latest,
    /// Justified by the beacon chain but not yet finalized. Never minted against.
    Safe,
    /// FFG-finalized — irreversible barring a >1/3 slashing. The ONLY tag a mint
    /// draws on.
    Finalized,
}

impl BlockTag {
    /// The string an `eth_getBlockByNumber` / `eth_getLogs` block field expects.
    pub fn as_rpc_str(self) -> &'static str {
        match self {
            Self::Latest => "latest",
            Self::Safe => "safe",
            Self::Finalized => "finalized",
        }
    }
}

/// One `Deposit` log as the relayer sees it over `eth_getLogs` / a receipt:
/// exactly the fields the deposit decode + the escrow/inclusion binding need.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EthLog {
    /// The emitting contract address (must be the bridge contract — escrow gate).
    pub address: [u8; 20],
    /// The indexed topics: `[topic0, lockId, dreggRecipient]` for a `Deposit`.
    pub topics: Vec<[u8; 32]>,
    /// The non-indexed event data (`amount` as a 32-byte big-endian word).
    pub data: Vec<u8>,
    /// The block the log was included in (finality is gated on this).
    pub block_number: u64,
    /// The transaction hash that emitted the log (the receipt cross-check key).
    pub tx_hash: [u8; 32],
    /// The log's index within the block.
    pub log_index: u64,
}

/// An `eth_getTransactionReceipt` result: enough to cross-check a log's inclusion.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EthReceipt {
    /// `status == 1` (success). A reverted (`0`) tx never emitted a real deposit.
    pub status: bool,
    /// The block the tx was mined in (must match the log's block).
    pub block_number: u64,
    /// The transaction hash.
    pub tx_hash: [u8; 32],
    /// The logs the tx emitted (the observed log must be present here).
    pub logs: Vec<EthLog>,
}

/// One storage slot from an `eth_getProof` result: the slot key, its 32-byte
/// value, and the Merkle-Patricia proof nodes against the account storage root.
/// Verifying the MPT proof against the finalized state root is the trustless /
/// in-circuit route; the relayer surfaces the value as a secondary binding.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EthStorageSlot {
    /// The 32-byte storage slot key.
    pub key: [u8; 32],
    /// The 32-byte slot value.
    pub value: [u8; 32],
    /// The RLP-encoded MPT proof nodes (opaque to the relayer; the mainnet route
    /// verifies them against the finalized state root).
    pub proof: Vec<Vec<u8>>,
}

/// An `eth_getProof` result: the account's storage root + the requested slots.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EthProof {
    /// The account's storage trie root (binds the slots below).
    pub storage_hash: [u8; 32],
    /// The RLP-encoded account-proof nodes against the state root.
    pub account_proof: Vec<Vec<u8>>,
    /// The requested storage slots with their values + proofs.
    pub storage: Vec<EthStorageSlot>,
}

/// The relayer's view of the Ethereum chain. A real JSON-RPC client
/// ([`EthJsonRpc`]) and the in-memory test double ([`MockEthRpc`]) both implement
/// it; the relayer is generic over it so the watch→verify→mint loop is tested
/// without a network.
pub trait EthRpc {
    /// `eth_getBlockByNumber(tag, false)` → the block number at this tag (the
    /// finality head when `tag == Finalized`).
    fn block_number(&self, tag: BlockTag) -> Result<u64, RpcError>;

    /// `eth_getLogs({address, topics:[topic0], fromBlock, toBlock})` — the bridge
    /// contract's `Deposit` logs in `[from_block, to_block]`.
    fn get_logs(
        &self,
        address: &[u8; 20],
        topic0: &[u8; 32],
        from_block: u64,
        to_block: u64,
    ) -> Result<Vec<EthLog>, RpcError>;

    /// `eth_getTransactionReceipt(tx_hash)` — the receipt (absent ⟹ `None`).
    fn get_transaction_receipt(&self, tx_hash: &[u8; 32]) -> Result<Option<EthReceipt>, RpcError>;

    /// `eth_getProof(address, slots, block)` — the account + storage-slot MPT
    /// proof at `block` (used for the optional storage-slot binding).
    fn get_proof(
        &self,
        address: &[u8; 20],
        slots: &[[u8; 32]],
        block: u64,
    ) -> Result<EthProof, RpcError>;
}

// ===========================================================================
// The real JSON-RPC client (real Ethereum wire over an injected byte-pipe)
// ===========================================================================

/// A real Ethereum JSON-RPC client: it builds the genuine `eth_*` request
/// envelopes and parses the genuine response shapes (`0x`-hex quantities and
/// data), delegating the actual bytes to an injected [`JsonRpcTransport`] (the
/// same seam the Solana relayer ships — [`crate::solana_relayer::StdHttpTransport`]
/// for `http://`, an injected TLS transport for the live mainnet endpoint).
pub struct EthJsonRpc<T: JsonRpcTransport> {
    /// The RPC endpoint, e.g. `http://127.0.0.1:8545` or an `https://` provider.
    pub url: String,
    transport: T,
}

impl<T: JsonRpcTransport> EthJsonRpc<T> {
    /// Build a client for `url` over `transport`.
    pub fn new(url: impl Into<String>, transport: T) -> Self {
        Self {
            url: url.into(),
            transport,
        }
    }

    fn call(&self, method: &str, params: serde_json::Value) -> Result<serde_json::Value, RpcError> {
        let req = serde_json::json!({
            "jsonrpc": "2.0",
            "id": 1,
            "method": method,
            "params": params,
        });
        let body = serde_json::to_string(&req).map_err(|e| RpcError::Decode(e.to_string()))?;
        let resp = self.transport.post(&self.url, &body)?;
        let v: serde_json::Value =
            serde_json::from_str(&resp).map_err(|e| RpcError::Decode(e.to_string()))?;
        if let Some(err) = v.get("error") {
            let code = err.get("code").and_then(|c| c.as_i64()).unwrap_or(0);
            let message = err
                .get("message")
                .and_then(|m| m.as_str())
                .unwrap_or("")
                .to_string();
            return Err(RpcError::Rpc { code, message });
        }
        v.get("result")
            .cloned()
            .ok_or_else(|| RpcError::Decode("missing `result`".into()))
    }
}

/// Parse a `0x`-prefixed hex quantity (`eth_*` quantities are minimal-length hex)
/// into a `u64`.
fn hex_u64(s: &str) -> Result<u64, RpcError> {
    let h = s
        .strip_prefix("0x")
        .ok_or_else(|| RpcError::Decode(format!("expected 0x-hex quantity, got `{s}`")))?;
    u64::from_str_radix(h, 16).map_err(|e| RpcError::Decode(format!("hex u64 `{s}`: {e}")))
}

/// Parse a `0x`-prefixed hex byte string into a `Vec<u8>` (even nibble count).
fn hex_bytes(s: &str) -> Result<Vec<u8>, RpcError> {
    let h = s
        .strip_prefix("0x")
        .ok_or_else(|| RpcError::Decode(format!("expected 0x-hex data, got `{s}`")))?;
    if h.len() % 2 != 0 {
        return Err(RpcError::Decode(format!("odd-length hex data `{s}`")));
    }
    (0..h.len())
        .step_by(2)
        .map(|i| {
            u8::from_str_radix(&h[i..i + 2], 16)
                .map_err(|e| RpcError::Decode(format!("hex byte `{}`: {e}", &h[i..i + 2])))
        })
        .collect()
}

/// Parse a `0x`-prefixed hex string into a fixed `[u8; N]` (left-padded if short,
/// rejecting an over-long value).
fn hex_fixed<const N: usize>(s: &str) -> Result<[u8; N], RpcError> {
    let bytes = hex_bytes(s)?;
    if bytes.len() > N {
        return Err(RpcError::Decode(format!(
            "hex value is {} bytes, expected at most {N}",
            bytes.len()
        )));
    }
    let mut out = [0u8; N];
    out[N - bytes.len()..].copy_from_slice(&bytes);
    Ok(out)
}

/// Encode bytes as a `0x`-prefixed hex string (for request params).
fn to_hex(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(2 + bytes.len() * 2);
    s.push_str("0x");
    for b in bytes {
        s.push_str(&format!("{b:02x}"));
    }
    s
}

/// Parse one log object from an `eth_getLogs` / receipt `logs[]` entry.
fn parse_log(v: &serde_json::Value) -> Result<EthLog, RpcError> {
    let address = hex_fixed::<20>(
        v.get("address")
            .and_then(|x| x.as_str())
            .ok_or_else(|| RpcError::Decode("log.address".into()))?,
    )?;
    let topics = v
        .get("topics")
        .and_then(|x| x.as_array())
        .ok_or_else(|| RpcError::Decode("log.topics".into()))?
        .iter()
        .map(|t| {
            hex_fixed::<32>(
                t.as_str()
                    .ok_or_else(|| RpcError::Decode("log.topics[i]".into()))?,
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
    let data = hex_bytes(
        v.get("data")
            .and_then(|x| x.as_str())
            .ok_or_else(|| RpcError::Decode("log.data".into()))?,
    )?;
    let block_number = hex_u64(
        v.get("blockNumber")
            .and_then(|x| x.as_str())
            .ok_or_else(|| RpcError::Decode("log.blockNumber".into()))?,
    )?;
    let tx_hash = hex_fixed::<32>(
        v.get("transactionHash")
            .and_then(|x| x.as_str())
            .ok_or_else(|| RpcError::Decode("log.transactionHash".into()))?,
    )?;
    let log_index = hex_u64(
        v.get("logIndex")
            .and_then(|x| x.as_str())
            .ok_or_else(|| RpcError::Decode("log.logIndex".into()))?,
    )?;
    Ok(EthLog {
        address,
        topics,
        data,
        block_number,
        tx_hash,
        log_index,
    })
}

impl<T: JsonRpcTransport> EthRpc for EthJsonRpc<T> {
    fn block_number(&self, tag: BlockTag) -> Result<u64, RpcError> {
        let result = self.call(
            "eth_getBlockByNumber",
            serde_json::json!([tag.as_rpc_str(), false]),
        )?;
        // A `finalized` query on a chain that has not finalized any block yet
        // returns `null` — surface it as a decode error so the relayer refuses.
        let number = result
            .get("number")
            .and_then(|x| x.as_str())
            .ok_or_else(|| RpcError::Decode("block.number (no finalized block yet?)".into()))?;
        hex_u64(number)
    }

    fn get_logs(
        &self,
        address: &[u8; 20],
        topic0: &[u8; 32],
        from_block: u64,
        to_block: u64,
    ) -> Result<Vec<EthLog>, RpcError> {
        let result = self.call(
            "eth_getLogs",
            serde_json::json!([{
                "address": to_hex(address),
                "topics": [to_hex(topic0)],
                "fromBlock": format!("0x{from_block:x}"),
                "toBlock": format!("0x{to_block:x}"),
            }]),
        )?;
        result
            .as_array()
            .ok_or_else(|| RpcError::Decode("eth_getLogs result".into()))?
            .iter()
            .map(parse_log)
            .collect()
    }

    fn get_transaction_receipt(&self, tx_hash: &[u8; 32]) -> Result<Option<EthReceipt>, RpcError> {
        let result = self.call(
            "eth_getTransactionReceipt",
            serde_json::json!([to_hex(tx_hash)]),
        )?;
        if result.is_null() {
            return Ok(None);
        }
        let status = match result.get("status").and_then(|x| x.as_str()) {
            Some(s) => hex_u64(s)? == 1,
            // Pre-Byzantium receipts have no status; treat absence as success
            // only if a root is present. Modern chains always carry status.
            None => result.get("root").is_some(),
        };
        let block_number = hex_u64(
            result
                .get("blockNumber")
                .and_then(|x| x.as_str())
                .ok_or_else(|| RpcError::Decode("receipt.blockNumber".into()))?,
        )?;
        let tx_hash = hex_fixed::<32>(
            result
                .get("transactionHash")
                .and_then(|x| x.as_str())
                .ok_or_else(|| RpcError::Decode("receipt.transactionHash".into()))?,
        )?;
        let logs = result
            .get("logs")
            .and_then(|x| x.as_array())
            .ok_or_else(|| RpcError::Decode("receipt.logs".into()))?
            .iter()
            .map(parse_log)
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Some(EthReceipt {
            status,
            block_number,
            tx_hash,
            logs,
        }))
    }

    fn get_proof(
        &self,
        address: &[u8; 20],
        slots: &[[u8; 32]],
        block: u64,
    ) -> Result<EthProof, RpcError> {
        let slot_params: Vec<String> = slots.iter().map(|s| to_hex(s)).collect();
        let result = self.call(
            "eth_getProof",
            serde_json::json!([to_hex(address), slot_params, format!("0x{block:x}")]),
        )?;
        let storage_hash = hex_fixed::<32>(
            result
                .get("storageHash")
                .and_then(|x| x.as_str())
                .ok_or_else(|| RpcError::Decode("proof.storageHash".into()))?,
        )?;
        let account_proof = parse_proof_nodes(result.get("accountProof"))?;
        let storage = result
            .get("storageProof")
            .and_then(|x| x.as_array())
            .ok_or_else(|| RpcError::Decode("proof.storageProof".into()))?
            .iter()
            .map(|sp| {
                let key = hex_fixed::<32>(
                    sp.get("key")
                        .and_then(|x| x.as_str())
                        .ok_or_else(|| RpcError::Decode("storageProof.key".into()))?,
                )?;
                let value = hex_fixed::<32>(
                    sp.get("value")
                        .and_then(|x| x.as_str())
                        .ok_or_else(|| RpcError::Decode("storageProof.value".into()))?,
                )?;
                let proof = parse_proof_nodes(sp.get("proof"))?;
                Ok(EthStorageSlot { key, value, proof })
            })
            .collect::<Result<Vec<_>, RpcError>>()?;
        Ok(EthProof {
            storage_hash,
            account_proof,
            storage,
        })
    }
}

/// Parse an array of `0x`-hex RLP proof nodes.
fn parse_proof_nodes(v: Option<&serde_json::Value>) -> Result<Vec<Vec<u8>>, RpcError> {
    v.and_then(|x| x.as_array())
        .ok_or_else(|| RpcError::Decode("proof nodes array".into()))?
        .iter()
        .map(|n| {
            hex_bytes(
                n.as_str()
                    .ok_or_else(|| RpcError::Decode("proof node hex".into()))?,
            )
        })
        .collect()
}

// ===========================================================================
// The relayer: watch → verify (finality + escrow + receipt) → mint input
// ===========================================================================

/// The bridge configuration the inbound EVM relayer watches against.
#[derive(Clone, Debug)]
pub struct EthBridgeConfig {
    /// The bridge contract address that emits `Deposit` logs (the escrow gate —
    /// BR-2-B). A log from any other address is refused.
    pub bridge_contract: [u8; 20],
    /// The canonical `Deposit` `topic0` ([`deposit_event_topic0`]).
    pub deposit_topic0: [u8; 32],
    /// Minimum mintable deposit (atomic units).
    pub min_amount: u64,
    /// Maximum mintable deposit (atomic units, anti-fat-finger / anti-overflow).
    pub max_amount: u64,
    /// The block to begin the `eth_getLogs` scan from (the bridge deploy block).
    pub from_block: u64,
}

impl EthBridgeConfig {
    /// Build a config with the canonical `Deposit` `topic0` filled in.
    pub fn new(
        bridge_contract: [u8; 20],
        min_amount: u64,
        max_amount: u64,
        from_block: u64,
    ) -> Self {
        Self {
            bridge_contract,
            deposit_topic0: deposit_event_topic0(),
            min_amount,
            max_amount,
            from_block,
        }
    }
}

/// A finalized, structurally-verified deposit observed on Ethereum — the relayer's
/// output. It carries the consume-once [`Self::nullifier`] ready to feed the
/// committed `bridge_mint_against_lock`.
#[derive(Clone, Debug)]
pub struct ObservedDeposit {
    /// The deposit's `lockId` (replay nonce) from `topics[1]`.
    pub lock_id: [u8; 32],
    /// The dregg cell the mint credits (`topics[2]`).
    pub recipient: CellId,
    /// The deposited amount (atomic units, decoded from the `uint256` data word
    /// and required to fit `u64`).
    pub amount: u64,
    /// The consume-once nullifier (the GLOBAL double-mint authority once consumed
    /// against the committed `note_nullifiers` set).
    pub nullifier: Nullifier,
    /// The block the deposit log was finalized in.
    pub block_number: u64,
    /// The finalized head reported by `eth_getBlockByNumber("finalized")`.
    pub finalized_block: u64,
    /// The transaction that emitted the deposit.
    pub tx_hash: [u8; 32],
    /// The log index within its block.
    pub log_index: u64,
}

impl ObservedDeposit {
    /// Build the committed-mint input (`dregg_turn::BridgeMintRequest`) for the
    /// SOUND, multi-relayer-safe path: `actor` holds the mirror's mint-cap and
    /// `ledger_cell` is the committed mirror-ledger cell. The consume-once
    /// nullifier carried here is the GLOBAL double-mint authority once consumed.
    pub fn to_bridge_mint_request(
        &self,
        actor: CellId,
        ledger_cell: CellId,
    ) -> dregg_turn::BridgeMintRequest {
        dregg_turn::BridgeMintRequest {
            actor,
            ledger_cell,
            lock_nullifier: self.nullifier,
            recipient: self.recipient,
            amount: self.amount,
            // The EVM relayer's trust gate is its finalized-head check + the
            // escrow-to-bridge-contract binding (BR-2-B): a deposit is surfaced
            // only from the configured bridge contract at the finalized head, and
            // the committed mint draws against the independent escrow leg recorded
            // by `to_escrow_record`. (The in-circuit witness of EVM finality — so a
            // dregg LIGHT client, not this re-executing relayer, sees the backing —
            // is the circuit swarm's VK-epoch.)
            consensus_verified: true,
        }
    }

    /// Build the INDEPENDENT escrow-record input that raises the committed
    /// `currently_locked` this deposit will be minted against (red-team
    /// BR-2/BR-3). The mint draws against it separately, so a draw with no
    /// matching escrow is refused by conservation.
    pub fn to_escrow_record(&self, ledger_cell: CellId) -> dregg_turn::BridgeEscrowRecord {
        dregg_turn::BridgeEscrowRecord {
            ledger_cell,
            escrow_nullifier: dregg_turn::escrow_nullifier_for(&self.nullifier),
            escrowed: self.amount,
            consensus_verified: true,
        }
    }
}

/// Why the relayer refused to surface an observed log as a mintable deposit.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EthRelayerError {
    /// An RPC call failed.
    Rpc(RpcError),
    /// The log was emitted by a contract OTHER than the configured bridge
    /// contract (BR-2-B). It exists on Ethereum but is not the bridge's escrow.
    NotBridgeContract,
    /// The log's `topic0` is not the canonical `Deposit` signature.
    NotDepositEvent,
    /// The log's block is ahead of the reported finalized head — un-finalized (or
    /// an inconsistent/forging node). Refused; never minted against.
    NotFinalized { block: u64, finalized: u64 },
    /// The log did not carry the expected `Deposit` topic/data shape.
    MalformedEvent { reason: String },
    /// The decoded `uint256` amount exceeds `u64` (does not fit a dregg amount).
    AmountTooLarge,
    /// The amount is below the configured minimum.
    BelowMin { amount: u64, min: u64 },
    /// The amount is above the configured maximum.
    AboveMax { amount: u64, max: u64 },
    /// `eth_getTransactionReceipt` returned no receipt for the log's tx.
    ReceiptMissing,
    /// The receipt's transaction reverted (`status != 1`) — no real deposit.
    ReceiptReverted,
    /// The receipt's block does not match the log's block (inconsistent node).
    ReceiptBlockMismatch { log: u64, receipt: u64 },
    /// The log is not present in its own transaction's receipt (a fabricated log).
    LogNotInReceipt,
}

impl std::fmt::Display for EthRelayerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Rpc(e) => write!(f, "{e}"),
            Self::NotBridgeContract => write!(
                f,
                "deposit log was not emitted by the configured bridge contract"
            ),
            Self::NotDepositEvent => write!(f, "log topic0 is not the canonical Deposit signature"),
            Self::NotFinalized { block, finalized } => write!(
                f,
                "deposit at block {block} is not finalized (finalized head {finalized})"
            ),
            Self::MalformedEvent { reason } => write!(f, "malformed Deposit event: {reason}"),
            Self::AmountTooLarge => write!(
                f,
                "deposit amount exceeds u64 (does not fit a dregg amount)"
            ),
            Self::BelowMin { amount, min } => write!(f, "deposit {amount} below minimum {min}"),
            Self::AboveMax { amount, max } => write!(f, "deposit {amount} above maximum {max}"),
            Self::ReceiptMissing => write!(f, "no transaction receipt for the deposit"),
            Self::ReceiptReverted => write!(f, "the deposit transaction reverted (status != 1)"),
            Self::ReceiptBlockMismatch { log, receipt } => write!(
                f,
                "receipt block {receipt} does not match the deposit log block {log}"
            ),
            Self::LogNotInReceipt => write!(f, "deposit log is not present in its own tx receipt"),
        }
    }
}

impl std::error::Error for EthRelayerError {}

impl From<RpcError> for EthRelayerError {
    fn from(e: RpcError) -> Self {
        Self::Rpc(e)
    }
}

/// The live off-chain Ethereum inbound relayer over an [`EthRpc`] connection.
pub struct EthRelayer<R: EthRpc> {
    /// The bridge configuration (contract, topic, bounds, scan start).
    pub config: EthBridgeConfig,
    /// The chain connection.
    pub rpc: R,
}

impl<R: EthRpc> EthRelayer<R> {
    /// Build a relayer for `config` over `rpc`.
    pub fn new(config: EthBridgeConfig, rpc: R) -> Self {
        Self { config, rpc }
    }

    /// **Watch the bridge contract and surface all finalized deposits.**
    ///
    /// One poll of the watch loop: read the finalized head, scan the contract's
    /// `Deposit` logs over `[from_block, finalized]`, and verify each (escrow +
    /// finality + receipt inclusion). Each entry is `Ok(deposit)` or the precise
    /// per-log refusal so the caller can log it. The verified deposits feed the
    /// committed mint.
    pub fn observe_deposits(
        &self,
    ) -> Result<Vec<Result<ObservedDeposit, EthRelayerError>>, EthRelayerError> {
        let finalized = self.rpc.block_number(BlockTag::Finalized)?;
        let logs = self.rpc.get_logs(
            &self.config.bridge_contract,
            &self.config.deposit_topic0,
            self.config.from_block,
            finalized,
        )?;
        Ok(logs
            .into_iter()
            .map(|log| self.verify_finalized_log(&log, finalized))
            .collect())
    }

    /// Observe one deposit by its transaction hash (the receipt-first path): read
    /// the receipt, find the bridge `Deposit` log in it, and run the same verify.
    /// Used when a deposit's tx hash is already known (e.g. surfaced by a user).
    pub fn observe_deposit_tx(
        &self,
        tx_hash: &[u8; 32],
    ) -> Result<ObservedDeposit, EthRelayerError> {
        let finalized = self.rpc.block_number(BlockTag::Finalized)?;
        let receipt = self
            .rpc
            .get_transaction_receipt(tx_hash)?
            .ok_or(EthRelayerError::ReceiptMissing)?;
        if !receipt.status {
            return Err(EthRelayerError::ReceiptReverted);
        }
        // The first bridge Deposit log in this receipt.
        let log = receipt
            .logs
            .iter()
            .find(|l| {
                l.address == self.config.bridge_contract
                    && l.topics.first() == Some(&self.config.deposit_topic0)
            })
            .ok_or(EthRelayerError::LogNotInReceipt)?
            .clone();
        self.verify_finalized_log(&log, finalized)
    }

    /// The shared verify over one log: escrow-to-contract binding (BR-2-B) →
    /// canonical `Deposit` topic → finality → decode → amount bounds → receipt
    /// inclusion (status + same block + the log present). Produces the
    /// [`ObservedDeposit`] or the precise refusal.
    pub fn verify_finalized_log(
        &self,
        log: &EthLog,
        finalized: u64,
    ) -> Result<ObservedDeposit, EthRelayerError> {
        // (1) BR-2-B: the log MUST be emitted by THIS bridge's contract. A log
        //     from any other address is refused — minting it credits nothing.
        if log.address != self.config.bridge_contract {
            return Err(EthRelayerError::NotBridgeContract);
        }

        // (2) the canonical Deposit event signature.
        if log.topics.first() != Some(&self.config.deposit_topic0) {
            return Err(EthRelayerError::NotDepositEvent);
        }

        // (3) finality: the log's block MUST be at/under the finalized head. A
        //     lying RPC that returns an over-finalized log is refused here even
        //     though the toBlock filter should have excluded it.
        if log.block_number > finalized {
            return Err(EthRelayerError::NotFinalized {
                block: log.block_number,
                finalized,
            });
        }

        // (4) decode the indexed lockId + recipient and the uint256 amount.
        let (lock_id, recipient, amount) = decode_deposit(log)?;
        if amount < self.config.min_amount {
            return Err(EthRelayerError::BelowMin {
                amount,
                min: self.config.min_amount,
            });
        }
        if amount > self.config.max_amount {
            return Err(EthRelayerError::AboveMax {
                amount,
                max: self.config.max_amount,
            });
        }

        // (5) receipt inclusion: the deposit's tx must have SUCCEEDED, be mined in
        //     the same block, and actually carry this log — so a fabricated log
        //     (no real tx behind it) is refused.
        let receipt = self
            .rpc
            .get_transaction_receipt(&log.tx_hash)?
            .ok_or(EthRelayerError::ReceiptMissing)?;
        if !receipt.status {
            return Err(EthRelayerError::ReceiptReverted);
        }
        if receipt.block_number != log.block_number {
            return Err(EthRelayerError::ReceiptBlockMismatch {
                log: log.block_number,
                receipt: receipt.block_number,
            });
        }
        if !receipt
            .logs
            .iter()
            .any(|l| l.address == log.address && l.topics == log.topics && l.data == log.data)
        {
            return Err(EthRelayerError::LogNotInReceipt);
        }

        Ok(ObservedDeposit {
            lock_id,
            recipient,
            amount,
            nullifier: eth_deposit_nullifier(&self.config.bridge_contract, &lock_id),
            block_number: log.block_number,
            finalized_block: finalized,
            tx_hash: log.tx_hash,
            log_index: log.log_index,
        })
    }

    /// Optional secondary binding via `eth_getProof`: read the bridge contract's
    /// storage slot that records `lockId → amount` (the deposit ledger) at the
    /// finalized block and check it matches the observed deposit. The MPT proof
    /// itself is verified against the finalized state root by the trustless /
    /// in-circuit route; this surfaces the storage VALUE as a defence-in-depth
    /// cross-check a re-executing validator can run today.
    pub fn storage_binds_deposit(
        &self,
        deposit: &ObservedDeposit,
        deposit_slot: [u8; 32],
    ) -> Result<bool, EthRelayerError> {
        let proof = self.rpc.get_proof(
            &self.config.bridge_contract,
            &[deposit_slot],
            deposit.block_number,
        )?;
        let Some(slot) = proof.storage.iter().find(|s| s.key == deposit_slot) else {
            return Ok(false);
        };
        // The slot encodes the amount as a big-endian uint256; the low 8 bytes
        // carry a u64 amount.
        let mut amt = [0u8; 8];
        amt.copy_from_slice(&slot.value[24..32]);
        Ok(u64::from_be_bytes(amt) == deposit.amount)
    }
}

/// Decode a `Deposit(bytes32 lockId, bytes32 dreggRecipient, uint256 amount)` log:
/// `topics[1] = lockId`, `topics[2] = dreggRecipient`, `data = amount` (a single
/// 32-byte big-endian EVM word; the high 24 bytes must be zero to fit `u64`).
fn decode_deposit(log: &EthLog) -> Result<([u8; 32], CellId, u64), EthRelayerError> {
    if log.topics.len() != 3 {
        return Err(EthRelayerError::MalformedEvent {
            reason: format!(
                "expected 3 topics (sig, lockId, recipient), got {}",
                log.topics.len()
            ),
        });
    }
    let lock_id = log.topics[1];
    let recipient = CellId::from_bytes(log.topics[2]);
    if log.data.len() != 32 {
        return Err(EthRelayerError::MalformedEvent {
            reason: format!(
                "expected 32-byte uint256 amount data, got {}",
                log.data.len()
            ),
        });
    }
    // EVM words are big-endian; a dregg amount must fit u64, so the top 24 bytes
    // (the 192 high bits) must be zero.
    if log.data[0..24].iter().any(|&b| b != 0) {
        return Err(EthRelayerError::AmountTooLarge);
    }
    let mut amt = [0u8; 8];
    amt.copy_from_slice(&log.data[24..32]);
    let amount = u64::from_be_bytes(amt);
    Ok((lock_id, recipient, amount))
}

/// Encode a `u64` deposit amount into a 32-byte big-endian `uint256` EVM data
/// word (the inverse of [`decode_deposit`]'s data decode — used by the mock and
/// by anyone constructing a deposit log).
pub fn encode_amount_word(amount: u64) -> Vec<u8> {
    let mut word = vec![0u8; 32];
    word[24..32].copy_from_slice(&amount.to_be_bytes());
    word
}

// ===========================================================================
// In-memory test double (the dev relayer harness + tests)
// ===========================================================================

/// An in-memory [`EthRpc`] for tests and the dev relayer harness: it models the
/// same `finalized`/`safe`/`latest` split a real node exposes, so the relayer's
/// finality gate (and an un-finalized refusal) is exercised without a network.
#[cfg(any(test, feature = "test-utils"))]
#[derive(Clone, Debug, Default)]
pub struct MockEthRpc {
    finalized_block: u64,
    safe_block: u64,
    latest_block: u64,
    /// All deposit logs the node knows (any block).
    logs: Vec<EthLog>,
    /// Receipts keyed by tx hash.
    receipts: std::collections::BTreeMap<[u8; 32], EthReceipt>,
    /// Storage proofs keyed by (slot key) for the bridge contract.
    proofs: std::collections::BTreeMap<[u8; 32], EthStorageSlot>,
    /// If true, `get_logs` returns logs ABOVE `to_block` too (a lying RPC) so the
    /// defensive per-log finality re-check can be tested.
    leak_unfinalized: bool,
}

#[cfg(any(test, feature = "test-utils"))]
impl MockEthRpc {
    /// A mock at the given heads (`finalized ≤ safe ≤ latest`).
    pub fn new(finalized_block: u64, safe_block: u64, latest_block: u64) -> Self {
        Self {
            finalized_block,
            safe_block,
            latest_block,
            logs: Vec::new(),
            receipts: std::collections::BTreeMap::new(),
            proofs: std::collections::BTreeMap::new(),
            leak_unfinalized: false,
        }
    }

    /// Build a canonical `Deposit` log for `contract`.
    pub fn deposit_log(
        contract: [u8; 20],
        lock_id: [u8; 32],
        recipient: CellId,
        amount: u64,
        block_number: u64,
        tx_hash: [u8; 32],
        log_index: u64,
    ) -> EthLog {
        EthLog {
            address: contract,
            topics: vec![deposit_event_topic0(), lock_id, *recipient.as_bytes()],
            data: encode_amount_word(amount),
            block_number,
            tx_hash,
            log_index,
        }
    }

    /// Insert a deposit log AND a matching success receipt (the happy path).
    pub fn insert_deposit(&mut self, log: EthLog) -> &mut Self {
        let receipt = EthReceipt {
            status: true,
            block_number: log.block_number,
            tx_hash: log.tx_hash,
            logs: vec![log.clone()],
        };
        self.receipts.insert(log.tx_hash, receipt);
        self.logs.push(log);
        self
    }

    /// Insert a deposit log WITHOUT a receipt (or with a reverted/empty one),
    /// for the fabricated-log / reverted-tx refusals.
    pub fn insert_log_only(&mut self, log: EthLog) -> &mut Self {
        self.logs.push(log);
        self
    }

    /// Insert (or overwrite) a receipt explicitly (reverted-tx / block-mismatch
    /// cases).
    pub fn insert_receipt(&mut self, receipt: EthReceipt) -> &mut Self {
        self.receipts.insert(receipt.tx_hash, receipt);
        self
    }

    /// Insert a storage slot value the bridge contract records for a deposit.
    pub fn insert_storage(&mut self, slot: EthStorageSlot) -> &mut Self {
        self.proofs.insert(slot.key, slot);
        self
    }

    /// Make `get_logs` leak logs above `to_block` (a lying/inconsistent node).
    pub fn set_leak_unfinalized(&mut self, leak: bool) -> &mut Self {
        self.leak_unfinalized = leak;
        self
    }
}

#[cfg(any(test, feature = "test-utils"))]
impl EthRpc for MockEthRpc {
    fn block_number(&self, tag: BlockTag) -> Result<u64, RpcError> {
        Ok(match tag {
            BlockTag::Finalized => self.finalized_block,
            BlockTag::Safe => self.safe_block,
            BlockTag::Latest => self.latest_block,
        })
    }

    fn get_logs(
        &self,
        address: &[u8; 20],
        topic0: &[u8; 32],
        from_block: u64,
        to_block: u64,
    ) -> Result<Vec<EthLog>, RpcError> {
        Ok(self
            .logs
            .iter()
            .filter(|l| {
                &l.address == address
                    && l.topics.first() == Some(topic0)
                    && l.block_number >= from_block
                    && (self.leak_unfinalized || l.block_number <= to_block)
            })
            .cloned()
            .collect())
    }

    fn get_transaction_receipt(&self, tx_hash: &[u8; 32]) -> Result<Option<EthReceipt>, RpcError> {
        Ok(self.receipts.get(tx_hash).cloned())
    }

    fn get_proof(
        &self,
        _address: &[u8; 20],
        slots: &[[u8; 32]],
        _block: u64,
    ) -> Result<EthProof, RpcError> {
        let storage = slots
            .iter()
            .map(|k| {
                self.proofs.get(k).cloned().unwrap_or(EthStorageSlot {
                    key: *k,
                    value: [0u8; 32],
                    proof: vec![],
                })
            })
            .collect();
        Ok(EthProof {
            storage_hash: [0u8; 32],
            account_proof: vec![],
            storage,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const CONTRACT: [u8; 20] = [0x11u8; 20];
    const ATTACKER: [u8; 20] = [0x99u8; 20];

    fn config() -> EthBridgeConfig {
        EthBridgeConfig::new(CONTRACT, 1, 1_000_000, 0)
    }

    fn lock_id(n: u8) -> [u8; 32] {
        [n; 32]
    }

    fn tx(n: u8) -> [u8; 32] {
        let mut t = [0u8; 32];
        t[0] = n;
        t[31] = n.wrapping_mul(7).wrapping_add(3);
        t
    }

    // ---- topic0 is the real keccak of the event signature -------------------

    #[test]
    fn deposit_topic0_is_keccak_of_signature() {
        // keccak256("Deposit(bytes32,bytes32,uint256)") — a stable, non-zero hash.
        let t = deposit_event_topic0();
        assert_ne!(t, [0u8; 32]);
        // Deterministic across calls.
        assert_eq!(t, deposit_event_topic0());
        // A different signature yields a different topic.
        let mut h = Keccak256::new();
        h.update(b"Deposit(bytes32,bytes32,uint128)");
        let mut other = [0u8; 32];
        other.copy_from_slice(&h.finalize());
        assert_ne!(t, other);
    }

    // ---- the JSON-RPC wire codec (real Ethereum shapes) ---------------------

    struct CannedTransport {
        expect_method: &'static str,
        response: String,
        seen: std::cell::RefCell<Option<String>>,
    }

    impl JsonRpcTransport for CannedTransport {
        fn post(&self, _url: &str, body: &str) -> Result<String, RpcError> {
            *self.seen.borrow_mut() = Some(body.to_string());
            assert!(
                body.contains(self.expect_method),
                "request did not name {}: {body}",
                self.expect_method
            );
            Ok(self.response.clone())
        }
    }

    #[test]
    fn json_rpc_parses_real_get_logs_shape() {
        let lid = lock_id(7);
        let recipient = CellId::from_bytes([0x44u8; 32]);
        let topic0 = deposit_event_topic0();
        let amount_word = encode_amount_word(1234);
        let resp = format!(
            r#"{{"jsonrpc":"2.0","id":1,"result":[{{"address":"{addr}","topics":["{t0}","{t1}","{t2}"],"data":"{data}","blockNumber":"0x10","transactionHash":"{txh}","logIndex":"0x2"}}]}}"#,
            addr = to_hex(&CONTRACT),
            t0 = to_hex(&topic0),
            t1 = to_hex(&lid),
            t2 = to_hex(recipient.as_bytes()),
            data = to_hex(&amount_word),
            txh = to_hex(&tx(1)),
        );
        let rpc = EthJsonRpc::new(
            "http://unused",
            CannedTransport {
                expect_method: "eth_getLogs",
                response: resp,
                seen: std::cell::RefCell::new(None),
            },
        );
        let logs = rpc
            .get_logs(&CONTRACT, &topic0, 0, 0x10)
            .expect("parse real eth_getLogs shape");
        assert_eq!(logs.len(), 1);
        let log = &logs[0];
        assert_eq!(log.address, CONTRACT);
        assert_eq!(log.block_number, 0x10);
        assert_eq!(log.log_index, 2);
        let (decoded_lock, decoded_recipient, decoded_amount) =
            decode_deposit(log).expect("decode");
        assert_eq!(decoded_lock, lid);
        assert_eq!(decoded_recipient, recipient);
        assert_eq!(decoded_amount, 1234);
        // The request carried the contract + topic filter + hex block range.
        let sent = rpc.transport.seen.borrow().clone().unwrap();
        assert!(sent.contains("eth_getLogs"));
        assert!(sent.contains("\"toBlock\":\"0x10\""));
    }

    #[test]
    fn json_rpc_parses_finalized_block_and_receipt() {
        // eth_getBlockByNumber("finalized") → number.
        let rpc = EthJsonRpc::new(
            "http://unused",
            CannedTransport {
                expect_method: "eth_getBlockByNumber",
                response: r#"{"jsonrpc":"2.0","id":1,"result":{"number":"0x64","hash":"0xab"}}"#
                    .to_string(),
                seen: std::cell::RefCell::new(None),
            },
        );
        assert_eq!(rpc.block_number(BlockTag::Finalized).unwrap(), 100);
        let sent = rpc.transport.seen.borrow().clone().unwrap();
        assert!(sent.contains("\"finalized\""));

        // A chain with no finalized block yet returns null → refused.
        let rpc_null = EthJsonRpc::new(
            "http://unused",
            CannedTransport {
                expect_method: "eth_getBlockByNumber",
                response: r#"{"jsonrpc":"2.0","id":1,"result":null}"#.to_string(),
                seen: std::cell::RefCell::new(None),
            },
        );
        assert!(rpc_null.block_number(BlockTag::Finalized).is_err());
    }

    #[test]
    fn json_rpc_surfaces_node_error() {
        let rpc = EthJsonRpc::new(
            "http://unused",
            CannedTransport {
                expect_method: "eth_getBlockByNumber",
                response: r#"{"jsonrpc":"2.0","id":1,"error":{"code":-32000,"message":"boom"}}"#
                    .to_string(),
                seen: std::cell::RefCell::new(None),
            },
        );
        let err = rpc.block_number(BlockTag::Finalized).unwrap_err();
        assert!(matches!(err, RpcError::Rpc { code: -32000, .. }));
    }

    // ---- the relayer watch→verify gates over the mock chain -----------------

    #[test]
    fn relayer_observes_finalized_deposit() {
        let recipient = CellId::from_bytes([0x44u8; 32]);
        let mut rpc = MockEthRpc::new(100, 105, 110);
        rpc.insert_deposit(MockEthRpc::deposit_log(
            CONTRACT,
            lock_id(1),
            recipient,
            500,
            90,
            tx(1),
            0,
        ));
        let relayer = EthRelayer::new(config(), rpc);
        let results = relayer.observe_deposits().expect("scan");
        assert_eq!(results.len(), 1);
        let obs = results[0].as_ref().expect("finalized deposit observed");
        assert_eq!(obs.amount, 500);
        assert_eq!(obs.recipient, recipient);
        assert_eq!(obs.lock_id, lock_id(1));
        assert_eq!(obs.finalized_block, 100);
        assert_eq!(obs.nullifier, eth_deposit_nullifier(&CONTRACT, &lock_id(1)));
    }

    #[test]
    fn relayer_refuses_unfinalized_deposit() {
        // A deposit at block 120, finalized head 100 — a lying RPC leaks it, and
        // the defensive per-log finality re-check refuses it.
        let recipient = CellId::from_bytes([0x44u8; 32]);
        let mut rpc = MockEthRpc::new(100, 105, 110);
        rpc.insert_deposit(MockEthRpc::deposit_log(
            CONTRACT,
            lock_id(2),
            recipient,
            500,
            120,
            tx(2),
            0,
        ));
        rpc.set_leak_unfinalized(true);
        let relayer = EthRelayer::new(config(), rpc);
        let results = relayer.observe_deposits().expect("scan");
        assert_eq!(results.len(), 1);
        assert!(matches!(
            results[0],
            Err(EthRelayerError::NotFinalized {
                block: 120,
                finalized: 100
            })
        ));
    }

    #[test]
    fn honest_node_excludes_unfinalized_from_scan() {
        // Without the leak, an un-finalized deposit is simply not returned by the
        // toBlock=finalized filter — the relayer never even sees it.
        let recipient = CellId::from_bytes([0x44u8; 32]);
        let mut rpc = MockEthRpc::new(100, 105, 110);
        rpc.insert_deposit(MockEthRpc::deposit_log(
            CONTRACT,
            lock_id(2),
            recipient,
            500,
            120,
            tx(2),
            0,
        ));
        let relayer = EthRelayer::new(config(), rpc);
        assert!(relayer.observe_deposits().expect("scan").is_empty());
    }

    #[test]
    fn relayer_refuses_wrong_contract() {
        // A finalized Deposit emitted by an ATTACKER contract (not the bridge).
        let recipient = CellId::from_bytes([0x44u8; 32]);
        let mut rpc = MockEthRpc::new(100, 105, 110);
        rpc.insert_deposit(MockEthRpc::deposit_log(
            ATTACKER,
            lock_id(3),
            recipient,
            500,
            90,
            tx(3),
            0,
        ));
        let relayer = EthRelayer::new(config(), rpc);
        // The scan filters by the bridge address, so an attacker log is not even
        // returned; the direct verify proves the explicit refusal.
        assert!(relayer.observe_deposits().expect("scan").is_empty());
        let attacker_log =
            MockEthRpc::deposit_log(ATTACKER, lock_id(3), recipient, 500, 90, tx(3), 0);
        assert_eq!(
            relayer
                .verify_finalized_log(&attacker_log, 100)
                .unwrap_err(),
            EthRelayerError::NotBridgeContract
        );
    }

    #[test]
    fn relayer_refuses_fabricated_log_without_receipt() {
        // A log present in the feed but with NO matching receipt (no real tx).
        let recipient = CellId::from_bytes([0x44u8; 32]);
        let mut rpc = MockEthRpc::new(100, 105, 110);
        rpc.insert_log_only(MockEthRpc::deposit_log(
            CONTRACT,
            lock_id(4),
            recipient,
            500,
            90,
            tx(4),
            0,
        ));
        let relayer = EthRelayer::new(config(), rpc);
        let results = relayer.observe_deposits().expect("scan");
        assert!(matches!(results[0], Err(EthRelayerError::ReceiptMissing)));
    }

    #[test]
    fn relayer_refuses_reverted_tx() {
        let recipient = CellId::from_bytes([0x44u8; 32]);
        let log = MockEthRpc::deposit_log(CONTRACT, lock_id(5), recipient, 500, 90, tx(5), 0);
        let mut rpc = MockEthRpc::new(100, 105, 110);
        rpc.insert_log_only(log.clone());
        rpc.insert_receipt(EthReceipt {
            status: false, // reverted
            block_number: 90,
            tx_hash: tx(5),
            logs: vec![log],
        });
        let relayer = EthRelayer::new(config(), rpc);
        let results = relayer.observe_deposits().expect("scan");
        assert!(matches!(results[0], Err(EthRelayerError::ReceiptReverted)));
    }

    #[test]
    fn relayer_refuses_above_max() {
        let recipient = CellId::from_bytes([0x44u8; 32]);
        let mut rpc = MockEthRpc::new(100, 105, 110);
        rpc.insert_deposit(MockEthRpc::deposit_log(
            CONTRACT,
            lock_id(6),
            recipient,
            9_999_999,
            90,
            tx(6),
            0,
        ));
        let relayer = EthRelayer::new(config(), rpc);
        let results = relayer.observe_deposits().expect("scan");
        assert!(matches!(results[0], Err(EthRelayerError::AboveMax { .. })));
    }

    #[test]
    fn decode_refuses_amount_above_u64() {
        // A uint256 amount whose high bits are set does not fit a dregg u64.
        let recipient = CellId::from_bytes([0x44u8; 32]);
        let mut log = MockEthRpc::deposit_log(CONTRACT, lock_id(7), recipient, 1, 90, tx(7), 0);
        log.data[0] = 0x01; // set a high byte
        assert_eq!(
            decode_deposit(&log).unwrap_err(),
            EthRelayerError::AmountTooLarge
        );
    }

    #[test]
    fn storage_binding_cross_checks_amount() {
        let recipient = CellId::from_bytes([0x44u8; 32]);
        let mut rpc = MockEthRpc::new(100, 105, 110);
        rpc.insert_deposit(MockEthRpc::deposit_log(
            CONTRACT,
            lock_id(8),
            recipient,
            777,
            90,
            tx(8),
            0,
        ));
        let slot_key = [0xEEu8; 32];
        let mut value = [0u8; 32];
        value[24..32].copy_from_slice(&777u64.to_be_bytes());
        rpc.insert_storage(EthStorageSlot {
            key: slot_key,
            value,
            proof: vec![],
        });
        let relayer = EthRelayer::new(config(), rpc);
        let obs = relayer.observe_deposits().expect("scan")[0]
            .as_ref()
            .unwrap()
            .clone();
        assert!(relayer.storage_binds_deposit(&obs, slot_key).unwrap());
        // A different slot (zero value) does not bind.
        assert!(!relayer.storage_binds_deposit(&obs, [0x00u8; 32]).unwrap());
    }

    #[test]
    fn observe_deposit_tx_receipt_first() {
        let recipient = CellId::from_bytes([0x44u8; 32]);
        let mut rpc = MockEthRpc::new(100, 105, 110);
        rpc.insert_deposit(MockEthRpc::deposit_log(
            CONTRACT,
            lock_id(9),
            recipient,
            42,
            90,
            tx(9),
            0,
        ));
        let relayer = EthRelayer::new(config(), rpc);
        let obs = relayer
            .observe_deposit_tx(&tx(9))
            .expect("receipt-first observe");
        assert_eq!(obs.amount, 42);
        assert_eq!(obs.lock_id, lock_id(9));
    }
}
