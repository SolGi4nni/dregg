//! Finality-following: verify an Altair `LightClientUpdate`'s finality proof so the
//! light client advances to a **consensus-verified finalized beacon header** and,
//! through its execution branch, to the **finalized EVM execution state root**.
//!
//! A `LightClientUpdate` carries:
//!   * `attested_header` — the beacon header the current sync committee signed;
//!   * `finalized_header` — the beacon header the attested state finalizes;
//!   * `finality_branch` — an SSZ inclusion proof of `finalized_checkpoint.root`
//!     (= `hash_tree_root(finalized_header.beacon)`) against `attested_header.state_root`;
//!   * `sync_aggregate` — the ≥ 2/3 BLS aggregate over `attested_header`.
//!
//! ## Ground truth (consensus-specs `altair`/`electra` light-client)
//!
//! * Altair..Deneb: `FINALIZED_ROOT_GINDEX = get_generalized_index(BeaconState,
//!   'finalized_checkpoint', 'root') = 105` → depth 6, subtree index `105 % 2^6 = 41`.
//! * Electra+ (the current mainnet fork family, incl. Fulu): the `BeaconState`
//!   layout deepened, so `FINALIZED_ROOT_GINDEX_ELECTRA = 169` → depth 7, subtree
//!   index `169 % 2^7 = 41`. **The subtree index is 41 in BOTH** (the finalized
//!   checkpoint stays the same left/right walk, one level deeper), so the only
//!   observable difference is the branch LENGTH (6 vs 7). Real post-Electra
//!   `finality_update`s carry a 7-node branch — we accept either depth, fail-closed
//!   on any other length.
//! * The signed message is `attested_header.beacon` under the sync-committee domain
//!   (handled by [`crate::verify_sync_aggregate`], which enforces the 2/3 floor).
//!
//! Verifying finality on top of the sync-aggregate is what makes the followed header
//! *final* rather than merely *attested* — a re-org cannot revert it. The recovered
//! execution `state_root` is then the anchor for [`crate::evm::verify_erc20_holding`].

use crate::execution::{verify_execution_payload, ExecutionPayloadHeader};
use crate::ssz::is_valid_merkle_branch;
use crate::{verify_sync_aggregate, BeaconBlockHeader, Error, SyncAggregate};

/// `FINALIZED_ROOT_GINDEX` — generalized index of `finalized_checkpoint.root` in
/// `BeaconState` (Altair..Deneb).
pub const FINALIZED_ROOT_GINDEX: u64 = 105;
/// Merkle-branch depth for the Altair..Deneb finalized root = `floor(log2(105)) = 6`.
pub const FINALIZED_ROOT_DEPTH: usize = 6;
/// `FINALIZED_ROOT_GINDEX` in Electra+ (the deepened `BeaconState`): 169.
pub const FINALIZED_ROOT_GINDEX_ELECTRA: u64 = 169;
/// Merkle-branch depth for the Electra+ finalized root = `floor(log2(169)) = 7`.
pub const FINALIZED_ROOT_DEPTH_ELECTRA: usize = 7;
/// Subtree index used by `is_valid_merkle_branch` = `105 % 2^6 = 169 % 2^7 = 41`.
/// Identical across the fork boundary — only the branch length differs.
pub const FINALIZED_ROOT_SUBTREE_INDEX: u64 = FINALIZED_ROOT_GINDEX % (1 << FINALIZED_ROOT_DEPTH);

/// A Capella+ `LightClientHeader`: the beacon header plus the execution payload
/// header and the branch that proves it into the beacon block body.
#[derive(Debug, Clone)]
pub struct LightClientHeader {
    pub beacon: BeaconBlockHeader,
    pub execution: ExecutionPayloadHeader,
    /// The `execution_branch` (depth 4) proving `execution` into `beacon.body_root`.
    pub execution_branch: Vec<[u8; 32]>,
}

/// The subset of an Altair/Capella `LightClientUpdate` this light client verifies:
/// the sync-signed attested header, the finalized header (with execution), and the
/// finality branch binding them.
#[derive(Debug, Clone)]
pub struct LightClientUpdate {
    /// The header the sync committee signed (only its beacon part is signed).
    pub attested_header: BeaconBlockHeader,
    /// The header the attested state finalizes, plus its execution payload header.
    pub finalized_header: LightClientHeader,
    /// SSZ inclusion proof (depth 6) of `finalized_header.beacon` root against
    /// `attested_header.state_root`.
    pub finality_branch: Vec<[u8; 32]>,
    /// The ≥ 2/3 BLS aggregate over `attested_header`.
    pub sync_aggregate: SyncAggregate,
}

/// The result of a verified finality-following step: the light client now trusts
/// this finalized beacon header and the EVM execution state root beneath it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FinalizedExecution {
    /// The finalized beacon slot.
    pub finalized_slot: u64,
    /// `hash_tree_root(finalized_header.beacon)` — the proven finalized block root.
    pub finalized_beacon_root: [u8; 32],
    /// The finalized execution block number.
    pub execution_block_number: u64,
    /// The finalized execution block hash.
    pub execution_block_hash: [u8; 32],
    /// The finalized EVM world-state MPT root — the anchor for proof-of-holdings.
    pub execution_state_root: [u8; 32],
}

/// Verify ONLY the finality branch: `hash_tree_root(finalized_beacon)` includes into
/// `attested_state_root` at the finalized-root gindex. Fail-closed on wrong depth or a
/// branch that does not reconstruct the attested state root.
pub fn verify_finality_branch(
    finalized_beacon: &BeaconBlockHeader,
    finality_branch: &[[u8; 32]],
    attested_state_root: &[u8; 32],
) -> Result<(), Error> {
    // Accept the Altair..Deneb depth (6) OR the Electra+ depth (7). Both walk to the
    // same subtree index 41; the Electra tree is simply one level deeper. Any other
    // length is fail-closed.
    if finality_branch.len() != FINALIZED_ROOT_DEPTH
        && finality_branch.len() != FINALIZED_ROOT_DEPTH_ELECTRA
    {
        return Err(Error::WrongBranchLength {
            got: finality_branch.len(),
            expected: FINALIZED_ROOT_DEPTH_ELECTRA,
        });
    }
    // Sanity: the subtree index is invariant across the fork boundary.
    debug_assert_eq!(
        FINALIZED_ROOT_GINDEX % (1 << FINALIZED_ROOT_DEPTH),
        FINALIZED_ROOT_GINDEX_ELECTRA % (1 << FINALIZED_ROOT_DEPTH_ELECTRA)
    );
    let leaf = finalized_beacon.hash_tree_root();
    if is_valid_merkle_branch(
        &leaf,
        finality_branch,
        FINALIZED_ROOT_SUBTREE_INDEX,
        attested_state_root,
    ) {
        Ok(())
    } else {
        Err(Error::BadFinalityBranch)
    }
}

/// **Finality-following + execution-state recovery.**
///
/// Given a `LightClientUpdate` and the CURRENT trusted sync-committee pubkeys, this:
///   1. verifies the sync-committee BLS aggregate over `attested_header` at the ≥ 2/3
///      threshold ([`verify_sync_aggregate`] — fail-closed on sub-quorum / bad sig);
///   2. verifies the finality branch proving `finalized_header.beacon` against
///      `attested_header.state_root` ([`verify_finality_branch`]);
///   3. verifies the execution branch proving `finalized_header.execution` against
///      `finalized_header.beacon.body_root`, recovering the EVM `state_root`.
///
/// On success the light client has advanced to a verified FINALIZED beacon header and
/// its finalized EVM execution state root. Any failure returns `Err` — never a
/// partial/asserted advance (fail closed).
pub fn verify_finalized_update(
    update: &LightClientUpdate,
    committee_pubkeys: &[[u8; 48]],
    fork_version: [u8; 4],
    genesis_validators_root: [u8; 32],
) -> Result<FinalizedExecution, Error> {
    // (1) The sync committee must have signed the attested header with ≥ 2/3
    //     participation. This is the consensus authority for the whole update.
    verify_sync_aggregate(
        &update.attested_header,
        &update.sync_aggregate,
        committee_pubkeys,
        fork_version,
        genesis_validators_root,
    )?;

    // (2) The attested state finalizes the finalized header.
    verify_finality_branch(
        &update.finalized_header.beacon,
        &update.finality_branch,
        &update.attested_header.state_root,
    )?;

    // (3) Recover and bind the EVM execution state root under the finalized header.
    let execution_state_root = verify_execution_payload(
        &update.finalized_header.execution,
        &update.finalized_header.execution_branch,
        &update.finalized_header.beacon.body_root,
    )?;

    Ok(FinalizedExecution {
        finalized_slot: update.finalized_header.beacon.slot,
        finalized_beacon_root: update.finalized_header.beacon.hash_tree_root(),
        execution_block_number: update.finalized_header.execution.block_number,
        execution_block_hash: update.finalized_header.execution.block_hash,
        execution_state_root,
    })
}
