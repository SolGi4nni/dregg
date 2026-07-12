//! The execution-payload-header side of finality-following: an Altair/Capella+
//! `LightClientHeader` carries not only the beacon `BeaconBlockHeader` but a
//! post-Bellatrix `ExecutionPayloadHeader` plus an `execution_branch` proving that
//! header into the beacon block **body** root. Verifying that branch is what turns a
//! consensus-verified finalized *beacon* header into a trusted **EVM execution
//! state root** — the state root the EIP-1186 proof-of-holdings then opens against.
//!
//! ## Ground truth (consensus-specs, `capella`/`deneb` light-client + beacon-chain)
//!
//! * `EXECUTION_PAYLOAD_GINDEX = get_generalized_index(BeaconBlockBody, 'execution_payload') = 25`.
//!   `BeaconBlockBody` has ≤ 16 fields through Deneb/Electra (padded to 16), with
//!   `execution_payload` at field index 9, so gindex = 16 + 9 = 25 → depth 4,
//!   subtree index 25 % 16 = 9. Stable across Capella…Electra.
//! * `ExecutionPayloadHeader` (Deneb/Electra) is a 17-field SSZ `Container`. Field
//!   ORDER and TYPES are load-bearing for the root — a single reordering or a wrong
//!   basic-type width changes the leaf and the proof fails closed.

use crate::ssz::{
    self, htr_bytelist_le32, htr_bytes20, htr_logs_bloom, htr_u64, is_valid_merkle_branch,
    merkleize,
};
use crate::Error;

/// `EXECUTION_PAYLOAD_GINDEX` — generalized index of `execution_payload` in
/// `BeaconBlockBody` (Capella…Electra).
pub const EXECUTION_PAYLOAD_GINDEX: u64 = 25;
/// Merkle-branch depth for the execution payload = `floor(log2(25)) = 4`.
pub const EXECUTION_PAYLOAD_DEPTH: usize = 4;
/// Subtree index used by `is_valid_merkle_branch` = `25 % 2^4 = 9`.
pub const EXECUTION_PAYLOAD_SUBTREE_INDEX: u64 =
    EXECUTION_PAYLOAD_GINDEX % (1 << EXECUTION_PAYLOAD_DEPTH);

/// A post-Bellatrix `ExecutionPayloadHeader` (Deneb/Electra 17-field layout).
///
/// This is the beacon chain's commitment to the *execution* block: crucially it
/// carries `state_root` — the EVM/MPT world-state root that
/// [`crate::evm::verify_erc20_holding`] opens an `eth_getProof` chain against.
///
/// The `hash_tree_root` here reproduces the SSZ container root exactly, so it can
/// serve as the leaf of the `execution_branch` inclusion proof into `body_root`.
/// Every field participates in the root; changing `state_root` (or any field)
/// changes the leaf, which is exactly why the light client can trust the state root
/// it recovers.
#[derive(Debug, Clone)]
pub struct ExecutionPayloadHeader {
    pub parent_hash: [u8; 32],
    /// `ExecutionAddress` (20 bytes).
    pub fee_recipient: [u8; 20],
    /// The EVM world-state MPT root — the value the proof-of-holdings opens against.
    pub state_root: [u8; 32],
    pub receipts_root: [u8; 32],
    /// `Vector[byte, 256]`.
    pub logs_bloom: [u8; 256],
    pub prev_randao: [u8; 32],
    pub block_number: u64,
    pub gas_limit: u64,
    pub gas_used: u64,
    pub timestamp: u64,
    /// `List[byte, MAX_EXTRA_DATA_BYTES = 32]`.
    pub extra_data: Vec<u8>,
    /// `uint256`, SSZ little-endian 32-byte encoding (a single chunk).
    pub base_fee_per_gas: [u8; 32],
    pub block_hash: [u8; 32],
    pub transactions_root: [u8; 32],
    pub withdrawals_root: [u8; 32],
    /// Deneb.
    pub blob_gas_used: u64,
    /// Deneb.
    pub excess_blob_gas: u64,
}

impl ExecutionPayloadHeader {
    /// SSZ `hash_tree_root` of the 17-field container (Deneb/Electra).
    pub fn hash_tree_root(&self) -> [u8; 32] {
        let base_fee_chunk = self.base_fee_per_gas; // already the 32-byte LE uint256 chunk
        let chunks: Vec<[u8; 32]> = vec![
            self.parent_hash,
            htr_bytes20(&self.fee_recipient),
            self.state_root,
            self.receipts_root,
            htr_logs_bloom(&self.logs_bloom),
            self.prev_randao,
            htr_u64(self.block_number),
            htr_u64(self.gas_limit),
            htr_u64(self.gas_used),
            htr_u64(self.timestamp),
            htr_bytelist_le32(&self.extra_data),
            base_fee_chunk,
            self.block_hash,
            self.transactions_root,
            self.withdrawals_root,
            htr_u64(self.blob_gas_used),
            htr_u64(self.excess_blob_gas),
        ];
        merkleize(chunks)
    }
}

/// Verify the `execution_branch` proves `execution` against a beacon block
/// `body_root`, and return the recovered EVM execution `state_root`.
///
/// Fail-closed on a wrong-depth branch or a branch that does not reconstruct
/// `body_root` from `hash_tree_root(execution)` at subtree index 9.
pub fn verify_execution_payload(
    execution: &ExecutionPayloadHeader,
    execution_branch: &[[u8; 32]],
    body_root: &[u8; 32],
) -> Result<[u8; 32], Error> {
    if execution_branch.len() != EXECUTION_PAYLOAD_DEPTH {
        return Err(Error::WrongBranchLength {
            got: execution_branch.len(),
            expected: EXECUTION_PAYLOAD_DEPTH,
        });
    }
    let leaf = execution.hash_tree_root();
    if is_valid_merkle_branch(
        &leaf,
        execution_branch,
        EXECUTION_PAYLOAD_SUBTREE_INDEX,
        body_root,
    ) {
        Ok(execution.state_root)
    } else {
        Err(Error::BadExecutionBranch)
    }
}

/// Re-export the merkle root helper so tests can construct self-consistent branch
/// KATs (the constructive inverse of `is_valid_merkle_branch`).
pub fn compute_branch_root(leaf: &[u8; 32], branch: &[[u8; 32]], index: u64) -> [u8; 32] {
    let mut value = *leaf;
    for (i, node) in branch.iter().enumerate() {
        if (index >> i) & 1 == 1 {
            value = ssz::hash_pair(node, &value);
        } else {
            value = ssz::hash_pair(&value, node);
        }
    }
    value
}
