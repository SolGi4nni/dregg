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
//!   (the `blst` aggregate verify runs in [`crate::sync_projection`]; the 2/3 floor over its
//!   result is enforced by the verified Lean gate, see [`crate::verified_gate`]).
//!
//! Verifying finality on top of the sync-aggregate is what makes the followed header
//! *final* rather than merely *attested* — a re-org cannot revert it. The recovered
//! execution `state_root` is then the anchor for [`crate::evm::verify_erc20_holding`].

use crate::execution::{
    execution_branch_reconstructs, ExecutionPayloadHeader, EXECUTION_PAYLOAD_DEPTH,
};
use crate::ssz::is_valid_merkle_branch;
use crate::verified_gate::{self, EthProjections};
use crate::{sync_projection, BeaconBlockHeader, Error, SyncAggregate};

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
///
/// **Unforgeable by construction.** All fields are PRIVATE, so external code can
/// neither build one by struct literal nor MUTATE a legitimately-obtained one (a bare
/// private seal would still allow `f.execution_state_root = fabricated`). The only
/// ways to obtain one are [`verify_finalized_update`] (the real light-client path) and
/// the loud, greppable [`FinalizedExecution::new_unchecked`]. This makes "the root came
/// from a verified update" a type-level property, not a doc-convention — the exact
/// unforgeable-`VerifiedHeader` discipline the Cosmos light client uses. Read the fields
/// through the accessors.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FinalizedExecution {
    finalized_slot: u64,
    finalized_beacon_root: [u8; 32],
    execution_block_number: u64,
    execution_block_hash: [u8; 32],
    execution_state_root: [u8; 32],
    execution_timestamp: u64,
}

impl FinalizedExecution {
    /// Construct a `FinalizedExecution` WITHOUT light-client verification — the caller
    /// ASSERTS these values came from a genuinely verified finality update (the
    /// `from_utf8_unchecked` idiom). Production code obtains one ONLY from
    /// [`verify_finalized_update`]; every other construction site is a loud, greppable
    /// `new_unchecked` (tests, or a caller wiring its own verified update).
    pub fn new_unchecked(
        finalized_slot: u64,
        finalized_beacon_root: [u8; 32],
        execution_block_number: u64,
        execution_block_hash: [u8; 32],
        execution_state_root: [u8; 32],
        execution_timestamp: u64,
    ) -> Self {
        FinalizedExecution {
            finalized_slot,
            finalized_beacon_root,
            execution_block_number,
            execution_block_hash,
            execution_state_root,
            execution_timestamp,
        }
    }

    /// The finalized beacon slot.
    pub fn finalized_slot(&self) -> u64 {
        self.finalized_slot
    }
    /// `hash_tree_root(finalized_header.beacon)` — the proven finalized block root.
    pub fn finalized_beacon_root(&self) -> [u8; 32] {
        self.finalized_beacon_root
    }
    /// The finalized execution block number.
    pub fn execution_block_number(&self) -> u64 {
        self.execution_block_number
    }
    /// The finalized execution block hash.
    pub fn execution_block_hash(&self) -> [u8; 32] {
        self.execution_block_hash
    }
    /// The finalized EVM world-state MPT root — the anchor for proof-of-holdings.
    pub fn execution_state_root(&self) -> [u8; 32] {
        self.execution_state_root
    }
    /// The finalized execution block's TIMESTAMP (`ExecutionPayloadHeader.timestamp`,
    /// proven under the execution branch like the state root). This is the
    /// consensus-verified clock the Base fault-proof airgap predicate compares
    /// `resolvedAt` against ([`crate::base_fault_proof`]) — a caller-supplied wall
    /// clock would be forgeable.
    pub fn execution_timestamp(&self) -> u64 {
        self.execution_timestamp
    }
}

/// The finality-branch RECONSTRUCTION CARRIER: fold `hash_tree_root(finalized_beacon)` up the
/// supplied branch at subtree index 41 and compare against the attested state root. This is the
/// `EthLeaf.hashPairCR` crypto primitive — it reports whether the branch reconstructs and
/// **decides nothing** about whether the branch is an admissible depth.
pub fn finality_branch_reconstructs(
    finalized_beacon: &BeaconBlockHeader,
    finality_branch: &[[u8; 32]],
    attested_state_root: &[u8; 32],
) -> bool {
    // Sanity: the subtree index is invariant across the fork boundary.
    debug_assert_eq!(
        FINALIZED_ROOT_GINDEX % (1 << FINALIZED_ROOT_DEPTH),
        FINALIZED_ROOT_GINDEX_ELECTRA % (1 << FINALIZED_ROOT_DEPTH_ELECTRA)
    );
    let leaf = finalized_beacon.hash_tree_root();
    is_valid_merkle_branch(
        &leaf,
        finality_branch,
        FINALIZED_ROOT_SUBTREE_INDEX,
        attested_state_root,
    )
}

/// Verify ONLY the finality branch: `hash_tree_root(finalized_beacon)` includes into
/// `attested_state_root` at the finalized-root gindex — **decided by the verified Lean gate**.
///
/// The depth admissibility (Altair..Deneb 6 OR Electra+ 7, both walking to subtree index 41;
/// any other length fail-closed) is `LightClientEthGate.finalityDecision`, which
/// `finalityDecision_refines` proves is `LightClientEth.verifyFinalityBranch`. Rust supplies the
/// branch length and the [`finality_branch_reconstructs`] result; the archive renders the
/// verdict, and refuses to render one at all when it is absent
/// ([`Error::VerifiedGateUnavailable`]).
pub fn verify_finality_branch(
    finalized_beacon: &BeaconBlockHeader,
    finality_branch: &[[u8; 32]],
    attested_state_root: &[u8; 32],
) -> Result<(), Error> {
    let reconstructs =
        finality_branch_reconstructs(finalized_beacon, finality_branch, attested_state_root);
    verified_gate::gate(
        &verified_gate::finality_only(finality_branch.len(), reconstructs),
        None,
    )
}

/// Project a `LightClientUpdate` onto the eight facts the verified gate decides over —
/// `LightClientEthGate.ethProjectedDecision`, field for field. Three of the eight are the crypto
/// carriers' RESULTS (`blst` aggregate verify, two SHA-256 branch reconstructions); the other
/// five are lengths and a popcount. **Nothing here decides.**
///
/// Also returned: the `blst` carrier's own failure classification, for the non-authoritative
/// refusal diagnostic (the boolean projection erases `BadPubkey` vs `BadSignature`).
pub fn project_update(
    update: &LightClientUpdate,
    committee_pubkeys: &[[u8; 48]],
    fork_version: [u8; 4],
    genesis_validators_root: [u8; 32],
) -> (EthProjections, Option<Error>) {
    let sp = sync_projection(
        &update.attested_header,
        &update.sync_aggregate,
        committee_pubkeys,
        fork_version,
        genesis_validators_root,
    );
    let finality_ok = finality_branch_reconstructs(
        &update.finalized_header.beacon,
        &update.finality_branch,
        &update.attested_header.state_root,
    );
    let exec_ok = execution_branch_reconstructs(
        &update.finalized_header.execution,
        &update.finalized_header.execution_branch,
        &update.finalized_header.beacon.body_root,
    );
    (
        EthProjections {
            committee_len: sp.committee_len,
            bits_len: sp.bits_len,
            participant_count: sp.participant_count,
            bls_ok: sp.bls_ok,
            finality_len: update.finality_branch.len(),
            finality_ok,
            exec_len: update.finalized_header.execution_branch.len(),
            exec_ok,
        },
        sp.bls_err,
    )
}

/// **Finality-following + execution-state recovery — decided by the verified Lean gate.**
///
/// Given a `LightClientUpdate` and the CURRENT trusted sync-committee pubkeys, this computes the
/// three crypto primitives and makes **one** call to `@[export] dregg_eth_lc_verify` over the
/// update's true projections:
///   1. the sync-committee BLS aggregate over `attested_header` and the ≥ 2/3 threshold;
///   2. the finality branch proving `finalized_header.beacon` against
///      `attested_header.state_root`;
///   3. the execution branch proving `finalized_header.execution` against
///      `finalized_header.beacon.body_root`, recovering the EVM `state_root`.
///
/// The projections passed are exactly `LightClientEthGate.ethProjectedDecision`'s, and
/// `ethVerifyDecision_refines` proves (by `rfl`) that the gate's decision over them IS
/// `LightClientEth.verifyFinalizedUpdate` — so an `Ok` here is, given the named `blsSound` /
/// `hashPairCR` carriers, the `EthValidAt` no-forgery conclusion of
/// `ethVerifyDecision_no_forgery`, by construction rather than by resemblance.
///
/// On success the light client has advanced to a verified FINALIZED beacon header and its
/// finalized EVM execution state root. Any failure returns `Err` — never a partial/asserted
/// advance. **A missing archive is also a failure** ([`Error::VerifiedGateUnavailable`]): the
/// Rust rules that used to decide here were the twin, and they are gone.
pub fn verify_finalized_update(
    update: &LightClientUpdate,
    committee_pubkeys: &[[u8; 48]],
    fork_version: [u8; 4],
    genesis_validators_root: [u8; 32],
) -> Result<FinalizedExecution, Error> {
    let (projections, bls_err) = project_update(
        update,
        committee_pubkeys,
        fork_version,
        genesis_validators_root,
    );

    // THE decision. Not a Rust match on Rust rules — the archive's verdict over the same eight
    // projections `ethVerifyDecision_refines` is stated about.
    verified_gate::gate(&projections, bls_err)?;

    // Only past the gate is the receipt minted. `execution_state_root` is READ from the payload
    // header whose inclusion the gate just accepted — the recovery step, not a second decision.
    debug_assert_eq!(projections.exec_len, EXECUTION_PAYLOAD_DEPTH);
    Ok(FinalizedExecution {
        finalized_slot: update.finalized_header.beacon.slot,
        finalized_beacon_root: update.finalized_header.beacon.hash_tree_root(),
        execution_block_number: update.finalized_header.execution.block_number,
        execution_block_hash: update.finalized_header.execution.block_hash,
        execution_state_root: update.finalized_header.execution.state_root,
        execution_timestamp: update.finalized_header.execution.timestamp,
    })
}
