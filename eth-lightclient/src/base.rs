//! **Base (OP-stack L2) proof-of-holdings** — trustless COMPOSITION of the two
//! verifiers this crate already has: the ETH L1 sync-committee light client
//! ([`crate::finality`]) and the EIP-1186 MPT machinery ([`crate::evm`]). No new
//! trust assumption is introduced; a Base holding is proven through a four-link
//! chain, each link fail-closed:
//!
//! 1. **L1 finality** — a [`FinalizedExecution`] from
//!    [`crate::finality::verify_finalized_update`]: ≥ 2/3 sync-committee BLS +
//!    finality branch + execution branch ⇒ the finalized L1 execution `state_root`.
//! 2. **L1-committed output root** — an EIP-1186 storage proof against that L1
//!    state root, opening the OP-stack anchor contract's storage slot that holds
//!    the L2 output root ([`verify_l1_committed_output_root`]). Same audited
//!    `alloy-trie` machinery as the L1 ERC-20 path.
//! 3. **Output-root preimage binding** — the OP-stack v0 output-root commitment
//!    ([`verify_op_output_root`]) opens the trusted output root into its preimage,
//!    binding the claimed **L2 state root**:
//!    `output_root = keccak256(version(32) ‖ l2_state_root(32) ‖
//!    l2_withdrawal_storage_root(32) ‖ l2_latest_block_hash(32))`, version 0 =
//!    32 zero bytes (Optimism specs, proposals.md "L2 Output Commitment
//!    Construction"; same construction as `Hashing.hashOutputRootProof` in
//!    contracts-bedrock and `OutputRoot::hash` in kona-protocol).
//! 4. **L2 holding** — the ordinary EIP-1186 account+storage proof chain
//!    ([`crate::evm::verify_erc20_holding`]) opened against the now-bound L2 state
//!    root. Base's execution layer is the same EVM MPT; the machinery is literally
//!    the same code.
//!
//! ## Which L1 anchor model this verifies (and which it does NOT)
//!
//! This module grounds the **L2OutputOracle `l2Outputs` dynamic-array model**
//! (pre-fault-proofs OP stack): `Types.OutputProposal[] internal l2Outputs` at a
//! declared storage slot (slot **3** in the canonical contracts-bedrock
//! `L2OutputOracle`, [`L2_OUTPUT_ORACLE_L2_OUTPUTS_SLOT`]). Element `i` occupies
//! TWO slots starting at `keccak256(uint256(slot)) + 2*i`:
//!
//! * slot `+0`: `bytes32 outputRoot`
//! * slot `+1`: packed `uint128 timestamp` (low 16 bytes) ‖ `uint128 l2BlockNumber`
//!   (high 16 bytes) — Solidity packs declaration-order fields from the low bytes up.
//!
//! Both element slots are proven, so the snapshot L2 block number is L1-anchored,
//! not caller-claimed. The array LENGTH (held in the declared slot itself) is also
//! proven and the index bounds-checked against it, because `deleteL2Outputs`
//! shrinks the length WITHOUT zeroing element storage — a deleted (disputed)
//! output must not remain provable.
//!
//! **Scope:** the `l2Outputs` model verified here is exact for pre-fault-proof
//! OP-stack chains and for any chain still running an `L2OutputOracle`. Base
//! mainnet migrated to **fault proofs** — the live anchor is a resolved dispute
//! game created by the `DisputeGameFactory`
//! (0x43edB88C4B80fDD2AdFF2412A7BebF9dF42cB40e on L1) with the
//! `AnchorStateRegistry` tracking the latest resolved anchor; verifying THAT model
//! (game status, respected game type, retirement/blacklist exclusion, the airgap)
//! is [`crate::base_fault_proof`], which reuses this module's output-root binding
//! ([`verify_op_output_root`]) and `L1CommittedOutput` shape. Use THIS module for
//! legacy-oracle chains and the fault-proof module for live Base.
//!
//! ## Chain identity at the governance edge
//!
//! The minted [`ProvenErc20Holding`] converts via `to_foreign_fields()` to
//! `chain_tag = 1` (the EVM family, [`crate::evm::CHAIN_TAG_EVM`]); Base is
//! distinguished within the family as `ChainId::Evm(8453)` at the governance edge
//! ([`BASE_MAINNET_CHAIN_ID`]). The `holder`/`asset` addresses in the fields are
//! **L2 (Base) addresses** and the `snapshot` is the **L2 block number** proven
//! from L1 storage.

use crate::evm::{
    verify_erc20_holding, verify_evm_account_proof, verify_evm_storage_slot, AccountClaim,
    Erc20ProofError, HoldingTrust, ProvenErc20Holding,
};
use crate::finality::FinalizedExecution;
use alloy_primitives::{keccak256, U256};

/// The OP-stack output-root version this module supports: **v0 = 32 zero bytes**
/// (the only version the protocol has ever defined). Any other version fails closed.
pub const OUTPUT_ROOT_VERSION_V0: [u8; 32] = [0u8; 32];

/// The declared storage slot of `Types.OutputProposal[] internal l2Outputs` in the
/// canonical contracts-bedrock `L2OutputOracle`: slot **3** (slot 0 =
/// `Initializable` packing, 1 = `startingBlockNumber`, 2 = `startingTimestamp`,
/// 3 = `l2Outputs`). Callers verifying a canonical oracle pass this; the slot stays
/// a PARAMETER because proxied/forked deployments may differ.
pub const L2_OUTPUT_ORACLE_L2_OUTPUTS_SLOT: u64 = 3;

/// Base mainnet's EVM chain id — the `ChainId::Evm(8453)` discriminant at the
/// governance edge (documentation constant; the proof itself is chain-id-agnostic:
/// it binds whatever L2 the oracle contract at `oracle_address` commits).
pub const BASE_MAINNET_CHAIN_ID: u64 = 8453;

/// Why a Base proof-of-holdings observation was refused. A refusal NEVER yields a
/// [`ProvenErc20Holding`] (fail closed).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BaseProofError {
    /// The claimed output-root version is not v0 (32 zero bytes). Accepting an
    /// unknown version would let a future/forged preimage layout alias a different
    /// L2 state root under the same trusted root — refused.
    UnsupportedOutputRootVersion { got: [u8; 32] },
    /// `keccak256(version ‖ l2_state_root ‖ l2_withdrawal_storage_root ‖
    /// l2_block_hash)` does not equal the L1-committed output root — the claimed L2
    /// state root is NOT the one L1 committed (a forged L2 root, a swapped field, or
    /// tampered preimage material).
    OutputRootMismatch {
        recomputed: [u8; 32],
        trusted: [u8; 32],
    },
    /// The claimed L1-committed output root is all-zero. A zero slot is what an
    /// UNSET array element reads as — accepting it would let an out-of-bounds index
    /// "commit" a zero root (and a keccak preimage for zero is unknown anyway).
    ZeroOutputRoot,
    /// The L1 account proof does not open the oracle contract's account (wrong
    /// address, tampered node, wrong account fields, or wrong L1 state root).
    L1OracleAccountProofInvalid,
    /// The L1 storage proof does not open the `l2Outputs` array LENGTH slot to the
    /// claimed length under the oracle's storage hash.
    L1OutputsLengthProofInvalid,
    /// `output_index >= l2Outputs.length`. Deleted outputs are the live threat
    /// here: `deleteL2Outputs` SHRINKS the array length WITHOUT zeroing storage, so
    /// a challenger-deleted (i.e. disputed) output root would still sit readable in
    /// its old slot — provable by a storage proof unless the index is bounds-checked
    /// against the proven CURRENT length. Fail closed.
    OutputIndexOutOfBounds { index: u64, length: u64 },
    /// The L1 storage proof does not open the `outputRoot` element slot to the
    /// claimed output root under the oracle's storage hash.
    L1OutputRootSlotProofInvalid,
    /// The L1 storage proof does not open the packed `timestamp ‖ l2BlockNumber`
    /// element slot to the claimed metadata (so the claimed L2 block number is NOT
    /// the one L1 committed for this output).
    L1OutputMetaSlotProofInvalid,
    /// The L2 (Base) EIP-1186 holding proof failed against the bound L2 state root.
    L2Holding(Erc20ProofError),
}

impl core::fmt::Display for BaseProofError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::UnsupportedOutputRootVersion { .. } => {
                write!(f, "output-root version is not v0 — refused (unknown preimage layout)")
            }
            Self::OutputRootMismatch { .. } => write!(
                f,
                "recomputed OP output root does not match the L1-committed one — the claimed L2 state root is not committed"
            ),
            Self::ZeroOutputRoot => {
                write!(f, "claimed L1-committed output root is zero (unset slot) — refused")
            }
            Self::L1OutputsLengthProofInvalid => write!(
                f,
                "L1 storage proof does not open the l2Outputs length slot under the anchor contract's storage hash"
            ),
            Self::OutputIndexOutOfBounds { index, length } => write!(
                f,
                "output index {index} is not below the proven l2Outputs length {length} — a deleted/disputed output is not a commitment"
            ),
            Self::L1OracleAccountProofInvalid => write!(
                f,
                "L1 account proof does not open the OP anchor contract under the finalized L1 state root"
            ),
            Self::L1OutputRootSlotProofInvalid => write!(
                f,
                "L1 storage proof does not open the outputRoot slot under the anchor contract's storage hash"
            ),
            Self::L1OutputMetaSlotProofInvalid => write!(
                f,
                "L1 storage proof does not open the timestamp/l2BlockNumber slot for this output"
            ),
            Self::L2Holding(e) => write!(f, "L2 holding proof failed: {e}"),
        }
    }
}

impl std::error::Error for BaseProofError {}

/// Compute the OP-stack **v0 output root**:
/// `keccak256( 32 zero bytes ‖ l2_state_root ‖ l2_withdrawal_storage_root ‖
/// l2_latest_block_hash )`.
///
/// Field order is LOAD-BEARING (Optimism specs proposals.md; `Hashing.
/// hashOutputRootProof` encodes `(version, stateRoot, messagePasserStorageRoot,
/// latestBlockhash)`) — a swapped field yields a different root and the binding
/// fails closed. The test suite pins this against the kona-protocol KAT.
pub fn compute_op_output_root_v0(
    l2_state_root: [u8; 32],
    l2_withdrawal_storage_root: [u8; 32],
    l2_block_hash: [u8; 32],
) -> [u8; 32] {
    let mut preimage = [0u8; 128];
    // [0..32] = version v0 = 32 zero bytes (already zeroed).
    preimage[32..64].copy_from_slice(&l2_state_root);
    preimage[64..96].copy_from_slice(&l2_withdrawal_storage_root);
    preimage[96..128].copy_from_slice(&l2_block_hash);
    keccak256(preimage).0
}

/// **The output-root core binding.** Verify that a CLAIMED L2 output-root preimage
/// (`version`, `l2_state_root`, `l2_withdrawal_storage_root`, `l2_block_hash`)
/// keccak-commits to `trusted_output_root`. On success the caller may treat
/// `l2_state_root` as bound by whatever authority vouches for the trusted root
/// (here: an L1 storage proof under the finalized L1 state root).
///
/// Fail-closed on: `version != v0`, a zero trusted root, or any preimage field that
/// does not recompute the trusted root.
pub fn verify_op_output_root(
    version: [u8; 32],
    l2_state_root: [u8; 32],
    l2_withdrawal_storage_root: [u8; 32],
    l2_block_hash: [u8; 32],
    trusted_output_root: [u8; 32],
) -> Result<(), BaseProofError> {
    if version != OUTPUT_ROOT_VERSION_V0 {
        return Err(BaseProofError::UnsupportedOutputRootVersion { got: version });
    }
    if trusted_output_root == [0u8; 32] {
        return Err(BaseProofError::ZeroOutputRoot);
    }
    let recomputed =
        compute_op_output_root_v0(l2_state_root, l2_withdrawal_storage_root, l2_block_hash);
    if recomputed != trusted_output_root {
        return Err(BaseProofError::OutputRootMismatch {
            recomputed,
            trusted: trusted_output_root,
        });
    }
    Ok(())
}

/// 32-byte big-endian encoding of a u64 slot number (Solidity `uint256` slot).
fn u64_slot_be32(slot: u64) -> [u8; 32] {
    let mut b = [0u8; 32];
    b[24..].copy_from_slice(&slot.to_be_bytes());
    b
}

/// The storage slot holding `l2Outputs[output_index].outputRoot`:
/// `keccak256(uint256(l2_outputs_slot)) + 2*output_index` (each `OutputProposal`
/// occupies two slots). Addition wraps mod 2^256 — exactly Solidity's unchecked
/// slot arithmetic.
pub fn l2_output_root_slot(l2_outputs_slot: u64, output_index: u64) -> [u8; 32] {
    let base = U256::from_be_bytes(keccak256(u64_slot_be32(l2_outputs_slot)).0);
    base.wrapping_add(U256::from(output_index) << 1)
        .to_be_bytes()
}

/// The storage slot holding the packed `l2Outputs[output_index].{timestamp,
/// l2BlockNumber}` word: the `outputRoot` slot + 1.
pub fn l2_output_meta_slot(l2_outputs_slot: u64, output_index: u64) -> [u8; 32] {
    let base = U256::from_be_bytes(keccak256(u64_slot_be32(l2_outputs_slot)).0);
    let element_offset: U256 = U256::from(output_index) << 1;
    base.wrapping_add(element_offset.wrapping_add(U256::ONE))
        .to_be_bytes()
}

/// Pack the `OutputProposal` metadata word as Solidity stores it:
/// `uint128 timestamp` in the LOW 16 bytes, `uint128 l2BlockNumber` in the HIGH 16
/// bytes (declaration order packs from the low bytes up).
pub fn pack_output_meta(timestamp: u128, l2_block_number: u64) -> U256 {
    U256::from(timestamp) | (U256::from(l2_block_number) << 128)
}

/// An OP-stack output commitment proven out of **finalized L1 state**: the output
/// root and the L2 block number it commits, both opened by EIP-1186 storage proofs
/// under the light-client-verified L1 execution state root.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct L1CommittedOutput {
    /// The trusted output root read out of L1 storage.
    pub output_root: [u8; 32],
    /// The L2 block number this output commits (from the packed metadata slot).
    pub l2_block_number: u64,
    /// The L1 timestamp at which the output was proposed (packed metadata slot).
    pub timestamp: u128,
}

/// Everything needed to open the L1-committed output root: the oracle contract's
/// identity + account claim + EIP-1186 proofs, and the claimed `OutputProposal`
/// contents (verified against L1 storage, never trusted bare).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OpOutputAnchor {
    /// The L1 address of the `L2OutputOracle` (or equivalent anchor) contract.
    pub oracle_address: [u8; 20],
    /// The oracle contract's account fields from `eth_getProof` on L1.
    pub oracle_account: AccountClaim,
    /// EIP-1186 `accountProof` for the oracle contract under the L1 state root.
    pub oracle_account_proof: Vec<Vec<u8>>,
    /// The declared slot of the `l2Outputs` array
    /// ([`L2_OUTPUT_ORACLE_L2_OUTPUTS_SLOT`] for the canonical contract).
    pub l2_outputs_slot: u64,
    /// The claimed CURRENT length of `l2Outputs` (verified against the array's
    /// declared slot, which holds the length). Needed because `deleteL2Outputs`
    /// shrinks the length without zeroing element storage — see
    /// [`BaseProofError::OutputIndexOutOfBounds`].
    pub l2_outputs_length: u64,
    /// EIP-1186 storage proof for the array-length slot (the declared slot itself).
    pub outputs_length_slot_proof: Vec<Vec<u8>>,
    /// The index of the output proposal being opened (must be `< l2_outputs_length`).
    pub output_index: u64,
    /// The claimed `outputRoot` at that index (verified against L1 storage).
    pub output_root: [u8; 32],
    /// The claimed proposal timestamp (verified against the packed slot).
    pub timestamp: u128,
    /// The claimed L2 block number (verified against the packed slot).
    pub l2_block_number: u64,
    /// EIP-1186 storage proof for the `outputRoot` element slot.
    pub output_root_slot_proof: Vec<Vec<u8>>,
    /// EIP-1186 storage proof for the packed `timestamp ‖ l2BlockNumber` slot.
    pub output_meta_slot_proof: Vec<Vec<u8>>,
}

/// **Open the L1-committed output root** out of finalized L1 state: verify the
/// oracle contract's account proof under `l1_finalized.execution_state_root()`,
/// then THREE storage proofs under the oracle's `storage_hash` — the array LENGTH
/// (+ an `index < length` bounds check, refusing challenger-deleted outputs whose
/// bytes linger in storage) and the two `OutputProposal` element slots. Returns
/// the [`L1CommittedOutput`] — the trusted output root plus the L2 block number it
/// commits. This REUSES the exact EIP-1186 machinery of the ERC-20 path
/// ([`verify_evm_account_proof`] / [`verify_evm_storage_slot`]).
///
/// Fail-closed on: a zero claimed output root (unset slot), an account proof that
/// does not open the oracle under the finalized L1 root, an out-of-bounds index,
/// or any storage proof failing to open its claimed value.
pub fn verify_l1_committed_output_root(
    l1_finalized: &FinalizedExecution,
    anchor: &OpOutputAnchor,
) -> Result<L1CommittedOutput, BaseProofError> {
    // An all-zero output root is what an unset/out-of-bounds array element reads
    // as — refuse before any trie work.
    if anchor.output_root == [0u8; 32] {
        return Err(BaseProofError::ZeroOutputRoot);
    }

    // (1) L1 ACCOUNT PROOF: finalized L1 state_root --MPT--> oracle account,
    //     binding the oracle's storage_hash.
    verify_evm_account_proof(
        l1_finalized.execution_state_root(),
        anchor.oracle_address,
        &anchor.oracle_account,
        &anchor.oracle_account_proof,
    )
    .map_err(|_| BaseProofError::L1OracleAccountProofInvalid)?;

    // (2) ARRAY LENGTH + BOUNDS: storage_hash --MPT--> l2Outputs.length, then
    //     require index < length. Without this, a challenger-DELETED (disputed)
    //     output would remain provable: deletion shrinks the length but leaves the
    //     element slots' bytes in place.
    verify_evm_storage_slot(
        anchor.oracle_account.storage_hash,
        u64_slot_be32(anchor.l2_outputs_slot),
        U256::from(anchor.l2_outputs_length),
        &anchor.outputs_length_slot_proof,
    )
    .map_err(|_| BaseProofError::L1OutputsLengthProofInvalid)?;
    if anchor.output_index >= anchor.l2_outputs_length {
        return Err(BaseProofError::OutputIndexOutOfBounds {
            index: anchor.output_index,
            length: anchor.l2_outputs_length,
        });
    }

    // (3) OUTPUT-ROOT SLOT: storage_hash --MPT--> l2Outputs[i].outputRoot.
    let root_slot = l2_output_root_slot(anchor.l2_outputs_slot, anchor.output_index);
    verify_evm_storage_slot(
        anchor.oracle_account.storage_hash,
        root_slot,
        U256::from_be_bytes(anchor.output_root),
        &anchor.output_root_slot_proof,
    )
    .map_err(|_| BaseProofError::L1OutputRootSlotProofInvalid)?;

    // (4) METADATA SLOT: storage_hash --MPT--> packed timestamp ‖ l2BlockNumber,
    //     so the snapshot height is L1-anchored, never caller-claimed.
    let meta_slot = l2_output_meta_slot(anchor.l2_outputs_slot, anchor.output_index);
    verify_evm_storage_slot(
        anchor.oracle_account.storage_hash,
        meta_slot,
        pack_output_meta(anchor.timestamp, anchor.l2_block_number),
        &anchor.output_meta_slot_proof,
    )
    .map_err(|_| BaseProofError::L1OutputMetaSlotProofInvalid)?;

    Ok(L1CommittedOutput {
        output_root: anchor.output_root,
        l2_block_number: anchor.l2_block_number,
        timestamp: anchor.timestamp,
    })
}

/// The claimed L2 output-root preimage: the version plus the three committed
/// fields. `verify_op_output_root` binds these to the L1-committed root; only then
/// is `l2_state_root` a trusted anchor for L2 MPT proofs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct L2StateCommitment {
    /// The claimed output-root version (only v0 is accepted).
    pub version: [u8; 32],
    /// The claimed L2 execution state root (the anchor being established).
    pub l2_state_root: [u8; 32],
    /// The claimed `L2ToL1MessagePasser` predeploy storage root.
    pub l2_withdrawal_storage_root: [u8; 32],
    /// The claimed L2 latest block hash at this output.
    pub l2_block_hash: [u8; 32],
}

/// **The Base proof-of-holdings composition** — L1 finality → L1-committed output
/// root → bound L2 state root → L2 ERC-20 MPT proof. Mints a
/// [`HoldingTrust::ConsensusProven`] holding ONLY when every link verifies:
///
/// 1. `l1_finalized` is a light-client-verified [`FinalizedExecution`] (the type is
///    unforgeable — see `finality.rs`).
/// 2. [`verify_l1_committed_output_root`]: the output root + L2 block number are
///    opened out of L1 storage under that finalized root.
/// 3. [`verify_op_output_root`]: the claimed L2 state root keccak-binds to the
///    committed output root (v0 preimage, exact field order).
/// 4. [`verify_erc20_holding`]: the ordinary EIP-1186 account+storage chain on the
///    L2 (Base) side, opened against the bound L2 state root, at the L1-proven L2
///    block number.
///
/// The minted holding's `state_root` is the **L2** state root and `block_number`
/// the **L2** block number; `to_foreign_fields()` yields `chain_tag = 1` (EVM
/// family — Base is `ChainId::Evm(8453)` at the governance edge).
///
/// Any link failing returns `Err` — never a partial/downgraded holding.
#[allow(clippy::too_many_arguments)]
pub fn verify_base_erc20_holding(
    l1_finalized: &FinalizedExecution,
    anchor: &OpOutputAnchor,
    l2_commitment: &L2StateCommitment,
    l2_account_proof: &[Vec<u8>],
    l2_storage_proof: &[Vec<u8>],
    token: [u8; 20],
    holder: [u8; 20],
    balances_slot: u64,
    token_account: &AccountClaim,
    claimed_balance: U256,
) -> Result<ProvenErc20Holding, BaseProofError> {
    // (1)+(2) L1 finality is carried by the unforgeable FinalizedExecution; open
    // the output root (and the L2 block number) out of finalized L1 storage.
    let committed = verify_l1_committed_output_root(l1_finalized, anchor)?;

    // (3) Bind the claimed L2 state root to the committed output root.
    verify_op_output_root(
        l2_commitment.version,
        l2_commitment.l2_state_root,
        l2_commitment.l2_withdrawal_storage_root,
        l2_commitment.l2_block_hash,
        committed.output_root,
    )?;

    // (4) The ordinary EVM holding proof, against the now-trusted L2 state root at
    // the L1-proven L2 block number. This mints StructureOnly; the upgrade to
    // ConsensusProven below is justified by links (1)-(3).
    let mut holding = verify_erc20_holding(
        l2_commitment.l2_state_root,
        l2_account_proof,
        l2_storage_proof,
        token,
        holder,
        balances_slot,
        token_account,
        claimed_balance,
        committed.l2_block_number,
    )
    .map_err(BaseProofError::L2Holding)?;
    holding.trust = HoldingTrust::ConsensusProven;
    Ok(holding)
}
