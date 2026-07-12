//! **EVM proof-of-holdings** — the ETH/Base analog of the non-custodial Solana
//! `prove_holding_consensus`. Given a light-client-verified execution `state_root`
//! (from [`crate::finality::verify_finalized_update`]) and an EIP-1186 `eth_getProof`
//! proof chain, prove that a holder holds `balance` of an ERC-20 `token` at that
//! finalized state — **with custody intact** (nothing moves; we open a proof over the
//! holder's balance slot in the token contract's own storage trie).
//!
//! ## The EIP-1186 proof chain
//!
//! 1. **Account (state) trie**: `state_root --MPT--> keccak256(token) -> RLP([nonce,
//!    balance, storageHash, codeHash])`. This binds the token contract account and, in
//!    particular, its `storageHash` — the root of the contract's storage trie.
//! 2. **Storage trie**: `storageHash --MPT--> keccak256(slot_key) -> RLP(balance)` where
//!    `slot_key = keccak256(pad32(holder) ‖ pad32(balances_slot))` is the Solidity
//!    `mapping(address => uint256)` slot for `balances[holder]`.
//!
//! The Merkle-Patricia trie verification is done by the maintained **`alloy-trie`**
//! (`verify_proof`) and RLP by **`alloy-rlp`** — the same code path Reth/Alloy use.
//! We do NOT hand-roll the Patricia trie.
//!
//! ## The forgery this binds against (Solana lesson, ported)
//!
//! `bridge/src/solana_holdings.rs` learned that a balance blob is only authoritative if
//! it sits under the RIGHT owner (the SPL Token program), else an attacker forges any
//! balance from an account under their own program. The EVM analog: a `balance` value is
//! only authoritative if it is proven at `keccak256(pad(holder) ‖ pad(slot))` inside the
//! storage trie whose root is the token CONTRACT's `storageHash`, which is itself proven
//! at `keccak256(token)` inside the light-client-verified `state_root`. Point the storage
//! proof at the wrong contract, the wrong slot, or an unrelated state root and every step
//! fails closed. Custody stays with the holder — we only open a read proof.

use crate::finality::FinalizedExecution;
use alloy_primitives::{keccak256, U256};
use alloy_trie::{proof::verify_proof, Nibbles, TrieAccount};

/// Re-exported so downstream code and tests can build balances without depending on
/// `alloy-primitives` directly.
pub use alloy_primitives::U256 as Uint256;

/// How much authority backs a [`ProvenErc20Holding`] — the EVM analog of the Solana
/// bridge's `LockProofTrust` rungs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HoldingTrust {
    /// The EIP-1186 MPT proofs verified, but the `state_root` they were opened against
    /// was CALLER-ASSERTED (a bare root, e.g. echoed by an RPC node) — consensus was
    /// NOT established by this crate. Grants ZERO governance weight downstream.
    StructureOnly,
    /// The MPT proofs verified against an execution state root recovered by the full
    /// light-client finality path ([`crate::finality::verify_finalized_update`]):
    /// ≥ 2/3 sync-committee BLS + finality branch + execution branch.
    ConsensusProven,
}

impl HoldingTrust {
    /// True iff a real light-client consensus proof backs the holding.
    pub fn is_consensus_proven(self) -> bool {
        matches!(self, HoldingTrust::ConsensusProven)
    }
}

/// A proven, NON-CUSTODIAL ERC-20 holding: at the state identified by
/// `state_root`/`block_number`, `holder` held `balance` atomic units of `token`. The
/// holder never moved anything — this is a read proof over the token contract's storage.
///
/// Shaped after `bridge::solana_holdings::ProvenHolding`: `trust` records which verify
/// path minted it. Only [`verify_erc20_holding_finalized`] — which takes the
/// [`FinalizedExecution`] the light client actually verified — yields
/// [`HoldingTrust::ConsensusProven`]; the bare-root path ([`verify_erc20_holding`])
/// yields [`HoldingTrust::StructureOnly`], which grants ZERO weight downstream.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProvenErc20Holding {
    /// The holder address (20 bytes) whose balance-slot was opened.
    pub holder: [u8; 20],
    /// The ERC-20 token contract address (20 bytes).
    pub token: [u8; 20],
    /// The proven balance in atomic units (ERC-20 `balanceOf`), big-endian `U256`.
    pub balance: U256,
    /// The execution `state_root` the proof opened against. Only trustworthy as a
    /// finality anchor when `trust` is [`HoldingTrust::ConsensusProven`].
    pub state_root: [u8; 32],
    /// The execution block number (provenance of the snapshot).
    pub block_number: u64,
    /// Which verify path minted this holding (consensus-anchored vs bare-root).
    pub trust: HoldingTrust,
}

/// The token contract's account fields as returned by `eth_getProof` (the RLP account
/// leaf the account proof commits to). All four are needed to reconstruct the exact RLP
/// value in the state trie — a wrong field changes the RLP and the proof fails closed,
/// and `storage_hash` is what the storage proof is verified against.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AccountClaim {
    pub nonce: u64,
    pub balance: U256,
    pub storage_hash: [u8; 32],
    pub code_hash: [u8; 32],
}

/// Why an EVM proof-of-holdings observation was refused. A refusal NEVER yields a
/// [`ProvenErc20Holding`] (fail closed).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Erc20ProofError {
    /// The account MPT proof does not open `keccak256(token)` to the claimed account
    /// RLP under `state_root` (wrong contract, tampered node, or wrong account fields).
    AccountProofInvalid,
    /// The storage MPT proof does not open the balance slot to the claimed balance under
    /// the contract's `storage_hash` (tampered node, wrong slot, or wrong balance).
    StorageProofInvalid,
    /// The account proof succeeded but as an EXCLUSION proof — the token account is
    /// absent from the state trie, so there is no contract to hold a balance.
    AccountAbsent,
    /// A zero balance was claimed. A zero holding grants no weight; we refuse to mint a
    /// `ProvenErc20Holding` for it (the Nomad-law floor: a trivial/empty holding is not a
    /// proof of participation). Callers wanting existence-of-account use the account path.
    ZeroBalance,
}

impl core::fmt::Display for Erc20ProofError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::AccountProofInvalid => write!(
                f,
                "account MPT proof does not open the token contract under the verified state root"
            ),
            Self::StorageProofInvalid => write!(
                f,
                "storage MPT proof does not open the balance slot under the contract storage hash"
            ),
            Self::AccountAbsent => {
                write!(f, "token contract account is absent from the state trie")
            }
            Self::ZeroBalance => write!(f, "claimed balance is zero — refused (no weight)"),
        }
    }
}

impl std::error::Error for Erc20ProofError {}

/// Compute the storage-trie SLOT KEY for `balances[holder]` where `balances` is a
/// Solidity `mapping(address => uint256)` declared at storage slot `balances_slot`:
/// `keccak256( left_pad32(holder) ‖ uint256_be(balances_slot) )`.
pub fn erc20_balance_slot_key(holder: &[u8; 20], balances_slot: u64) -> [u8; 32] {
    let mut preimage = [0u8; 64];
    // pad32(holder): 12 zero bytes then the 20-byte address (left-padded).
    preimage[12..32].copy_from_slice(holder);
    // uint256_be(balances_slot): 32-byte big-endian slot number.
    preimage[56..64].copy_from_slice(&balances_slot.to_be_bytes());
    keccak256(preimage).0
}

/// An MPT proof did not open the claimed key/value under the claimed root. The
/// generalized-helper failure marker — callers ([`verify_erc20_holding`],
/// [`crate::base`]) map it onto their own fail-closed error vocabulary.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MptProofInvalid;

/// **The generalized EIP-1186 ACCOUNT proof open** — `state_root --MPT-->
/// keccak256(address) -> RLP([nonce, balance, storageHash, codeHash])`.
///
/// This is the exact account-trie step of [`verify_erc20_holding`], factored out so
/// the SAME audited machinery verifies both an L1 token account and an OP-stack L1
/// contract account (the Base output-root anchor, [`crate::base`]). Reconstructing
/// the full RLP account leaf binds all four fields at once — a wrong field, wrong
/// address, or wrong state root fails closed.
pub fn verify_evm_account_proof(
    state_root: [u8; 32],
    address: [u8; 20],
    account: &AccountClaim,
    account_proof: &[Vec<u8>],
) -> Result<(), MptProofInvalid> {
    let trie_account = TrieAccount {
        nonce: account.nonce,
        balance: account.balance,
        storage_root: account.storage_hash.into(),
        code_hash: account.code_hash.into(),
    };
    let account_rlp = alloy_rlp::encode(&trie_account);
    let account_key = Nibbles::unpack(keccak256(address));
    let account_proof_bytes: Vec<alloy_primitives::Bytes> = account_proof
        .iter()
        .map(|n| alloy_primitives::Bytes::copy_from_slice(n))
        .collect();
    verify_proof(
        state_root.into(),
        account_key,
        Some(account_rlp),
        &account_proof_bytes,
    )
    .map_err(|_| MptProofInvalid)
}

/// **The generalized EIP-1186 STORAGE-slot proof open** — `storage_hash --MPT-->
/// keccak256(slot_key) -> RLP(value)` where `value` is the slot's `uint256` content
/// (EVM storage values are stored as minimal big-endian RLP).
///
/// `slot_key` is the RAW 32-byte storage slot (pre-keccak): a mapping-derived key
/// ([`erc20_balance_slot_key`]) for ERC-20 balances, or a dynamic-array element slot
/// for the OP-stack `l2Outputs` anchor ([`crate::base`]). Fail-closed: a tampered
/// node, wrong slot, or wrong value refuses.
pub fn verify_evm_storage_slot(
    storage_hash: [u8; 32],
    slot_key: [u8; 32],
    value: U256,
    storage_proof: &[Vec<u8>],
) -> Result<(), MptProofInvalid> {
    let storage_key = Nibbles::unpack(keccak256(slot_key));
    let value_rlp = alloy_rlp::encode(value);
    let storage_proof_bytes: Vec<alloy_primitives::Bytes> = storage_proof
        .iter()
        .map(|n| alloy_primitives::Bytes::copy_from_slice(n))
        .collect();
    verify_proof(
        storage_hash.into(),
        storage_key,
        Some(value_rlp),
        &storage_proof_bytes,
    )
    .map_err(|_| MptProofInvalid)
}

/// **The EIP-1186 storage-slot EXCLUSION proof open** — verify that `slot_key` is
/// **absent** from the storage trie rooted at `storage_hash`, i.e. the slot's value
/// is zero. In the EVM storage MPT a zero-valued slot is not stored at all, so
/// `eth_getProof` answers a zero slot with an exclusion proof: a node path showing
/// the trie does NOT contain `keccak256(slot_key)`. This is the twin of
/// [`verify_evm_storage_slot`] with expected value `None` — needed where a verifier
/// must prove a NEGATIVE (e.g. the Base fault-proof anchor's "this game is NOT
/// blacklisted", [`crate::base_fault_proof`]).
///
/// ## Two gates, both must accept (defense in depth)
///
/// 1. alloy-trie's `verify_proof` with expected value `None` — the audited
///    baseline (node linkage, RLP decoding, path walking).
/// 2. `walk_storage_exclusion` (private) — a STRICT-TERMINATION re-walk over the same
///    alloy node decoders. This exists because alloy-trie 0.9.5's `None` verify
///    accepts a **truncated prefix of a valid inclusion proof** as an exclusion
///    proof (measured; pinned by an adversarial test): its post-walk check
///    collapses a pending hash-continuation and an actual absence-terminal into
///    the same `None`. For a blacklist gate that hole is a forgery vector — an
///    attacker whose game IS blacklisted could truncate the inclusion proof of
///    the blacklist entry and "prove" absence. The re-walk refuses any proof
///    that exhausts while a hash child on the key path is still pending: UNKNOWN
///    is not ABSENT.
///
/// Fail-closed: a proof for a PRESENT key refuses, a truncated/tampered/trailing
/// proof refuses, and an empty proof is accepted only for the canonical EMPTY
/// trie root.
pub fn verify_evm_storage_slot_absent(
    storage_hash: [u8; 32],
    slot_key: [u8; 32],
    storage_proof: &[Vec<u8>],
) -> Result<(), MptProofInvalid> {
    let storage_key = Nibbles::unpack(keccak256(slot_key));
    let storage_proof_bytes: Vec<alloy_primitives::Bytes> = storage_proof
        .iter()
        .map(|n| alloy_primitives::Bytes::copy_from_slice(n))
        .collect();
    // Gate 1: the audited baseline exclusion verify.
    verify_proof(storage_hash.into(), storage_key, None, &storage_proof_bytes)
        .map_err(|_| MptProofInvalid)?;
    // Gate 2: the strict-termination re-walk (refuses truncation).
    walk_storage_exclusion(storage_hash, &storage_key, &storage_proof_bytes)
}

/// The strict-termination MPT exclusion walk (gate 2 of
/// [`verify_evm_storage_slot_absent`] — see there for WHY it exists). Re-walks
/// the proof from `storage_hash` along `key` using alloy-trie's own node
/// decoders (`TrieNode`/`RlpNode` — no hand-rolled RLP or hashing) and accepts
/// ONLY a proof whose final node is a genuine absence terminal for the key:
///
/// * a **branch with no child** at the key's next nibble,
/// * an **extension whose segment diverges** from the key, or
/// * a **leaf whose full path differs** from the key.
///
/// Everything else refuses: a leaf AT the key (present, not absent), a proof
/// that exhausts while a hash child on the key path is pending (truncation —
/// the subtree that would hold the key was never opened), trailing nodes after
/// the terminal, a node that does not hash-link to its parent, or undecodable
/// bytes. In-place (< 32-byte) children are descended within the same proof
/// entry, exactly as alloy's verifier does.
fn walk_storage_exclusion(
    storage_hash: [u8; 32],
    key: &Nibbles,
    proof: &[alloy_primitives::Bytes],
) -> Result<(), MptProofInvalid> {
    use alloy_rlp::Decodable as _;
    use alloy_trie::nodes::{RlpNode, TrieNode, CHILD_INDEX_RANGE};
    use alloy_trie::EMPTY_ROOT_HASH;

    // Empty proof (or the lone RLP empty-string marker): absence holds only for
    // the canonical empty trie root.
    if proof.is_empty() || (proof.len() == 1 && proof[0].as_ref() == [alloy_rlp::EMPTY_STRING_CODE])
    {
        return if alloy_primitives::B256::from(storage_hash) == EMPTY_ROOT_HASH {
            Ok(())
        } else {
            Err(MptProofInvalid)
        };
    }

    let mut walked = Nibbles::new(); // the key prefix consumed so far (on-path)
    let mut expected = RlpNode::word_rlp(&storage_hash.into());
    let mut nodes = proof.iter().peekable();

    while let Some(node_bytes) = nodes.next() {
        // Hash linkage: this node must be the one its parent committed to.
        if RlpNode::from_rlp(node_bytes).as_slice() != expected.as_slice() {
            return Err(MptProofInvalid);
        }
        let mut node = TrieNode::decode(&mut &node_bytes[..]).map_err(|_| MptProofInvalid)?;
        // Descend through in-place children without consuming proof entries.
        loop {
            match node {
                TrieNode::EmptyRoot => return Err(MptProofInvalid),
                TrieNode::Leaf(leaf) => {
                    // A leaf is always terminal — trailing nodes are malformed.
                    if nodes.peek().is_some() {
                        return Err(MptProofInvalid);
                    }
                    let mut full = walked;
                    full.extend(&leaf.key);
                    return if full == *key {
                        // The key IS present — not an exclusion.
                        Err(MptProofInvalid)
                    } else {
                        // A hash-linked leaf occupying the key's position with a
                        // DIFFERENT path: genuine absence.
                        Ok(())
                    };
                }
                TrieNode::Extension(ext) => {
                    let on_path = walked.len() + ext.key.len() <= key.len()
                        && key.slice(walked.len()..walked.len() + ext.key.len()) == ext.key;
                    if !on_path {
                        // Divergence at a hash-linked extension: the trie has no
                        // continuation along our key here — genuine absence, and
                        // it must be the terminal node.
                        return if nodes.peek().is_some() {
                            Err(MptProofInvalid)
                        } else {
                            Ok(())
                        };
                    }
                    walked.extend(&ext.key);
                    if ext.child.is_hash() {
                        expected = ext.child;
                        break; // continue with the next proof node
                    }
                    node = TrieNode::decode(&mut &ext.child[..]).map_err(|_| MptProofInvalid)?;
                }
                TrieNode::Branch(branch) => {
                    // Fixed-width keccak256 keys never terminate AT a branch.
                    let Some(next) = key.get(walked.len()) else {
                        return Err(MptProofInvalid);
                    };
                    if !branch.state_mask.is_bit_set(next) {
                        // No child at our nibble: genuine absence — terminal.
                        return if nodes.peek().is_some() {
                            Err(MptProofInvalid)
                        } else {
                            Ok(())
                        };
                    }
                    // Locate `next`'s entry in the packed child stack (same
                    // iteration alloy's verifier uses).
                    let mut stack_ptr = branch.as_ref().first_child_index();
                    for index in CHILD_INDEX_RANGE {
                        if index == next {
                            break;
                        }
                        if branch.state_mask.is_bit_set(index) {
                            stack_ptr += 1;
                        }
                    }
                    let child = branch
                        .stack
                        .get(stack_ptr)
                        .cloned()
                        .ok_or(MptProofInvalid)?;
                    walked.push(next);
                    if child.is_hash() {
                        expected = child;
                        break; // continue with the next proof node
                    }
                    node = TrieNode::decode(&mut &child[..]).map_err(|_| MptProofInvalid)?;
                }
            }
        }
    }
    // Proof exhausted while a hash child on the key path was still pending: the
    // subtree that would contain the key was never opened. UNKNOWN ≠ ABSENT.
    Err(MptProofInvalid)
}

/// **Prove a holder's ERC-20 balance against a caller-supplied state root —
/// non-custodially.** Mints a [`HoldingTrust::StructureOnly`] holding: the MPT chain is
/// fully verified, but THIS function has no evidence the `state_root` itself is
/// consensus-final (the caller merely asserts it). Use
/// [`verify_erc20_holding_finalized`] — which takes the [`FinalizedExecution`] the
/// light client recovered — to mint a [`HoldingTrust::ConsensusProven`] holding.
///
/// * `account_proof` / `storage_proof` are the RLP-encoded node lists from
///   `eth_getProof` (`accountProof` and `storageProof[i].proof`).
/// * `account` is the token contract's account fields from the same `eth_getProof`.
/// * `balances_slot` is the declared storage slot of the ERC-20 `balances` mapping.
///
/// Fail-closed on: a state root that is not the one the account proof commits to, a
/// wrong/absent token contract, a tampered account or storage node, a wrong balance
/// slot, a claimed balance that the storage trie does not commit to, or a zero balance.
#[allow(clippy::too_many_arguments)]
pub fn verify_erc20_holding(
    state_root: [u8; 32],
    account_proof: &[Vec<u8>],
    storage_proof: &[Vec<u8>],
    token: [u8; 20],
    holder: [u8; 20],
    balances_slot: u64,
    account: &AccountClaim,
    claimed_balance: U256,
    block_number: u64,
) -> Result<ProvenErc20Holding, Erc20ProofError> {
    // Nomad-law floor: a zero holding is not a proof of holding.
    if claimed_balance.is_zero() {
        return Err(Erc20ProofError::ZeroBalance);
    }

    // (1) ACCOUNT PROOF: state_root --MPT--> keccak256(token) -> RLP(account).
    //     Reconstruct the exact RLP account leaf; verify_proof checks the terminal
    //     value equals it. This binds nonce/balance/storageHash/codeHash all at once —
    //     any wrong field (or wrong contract, or wrong state root) fails closed.
    verify_evm_account_proof(state_root, token, account, account_proof)
        .map_err(|_| Erc20ProofError::AccountProofInvalid)?;

    // (2) STORAGE PROOF: storage_hash --MPT--> keccak256(slot_key) -> RLP(balance).
    //     The storage-trie value is the minimal big-endian RLP of the uint256 balance.
    let slot_key = erc20_balance_slot_key(&holder, balances_slot);
    verify_evm_storage_slot(
        account.storage_hash,
        slot_key,
        claimed_balance,
        storage_proof,
    )
    .map_err(|_| Erc20ProofError::StorageProofInvalid)?;

    Ok(ProvenErc20Holding {
        holder,
        token,
        balance: claimed_balance,
        state_root,
        block_number,
        trust: HoldingTrust::StructureOnly,
    })
}

/// **The consensus-anchored proof-of-holdings entry.** Opens the EIP-1186 proof chain
/// against the execution state root the light client itself recovered through the full
/// finality path (≥ 2/3 sync-committee BLS over the attested header, finality branch,
/// execution branch — [`crate::finality::verify_finalized_update`]), and mints a
/// [`HoldingTrust::ConsensusProven`] holding at the finalized block number.
///
/// This is the ONLY path that yields `ConsensusProven`: the state root and block
/// number are taken from the [`FinalizedExecution`], never from the caller's claim.
/// All the fail-closed refusals of [`verify_erc20_holding`] apply unchanged.
pub fn verify_erc20_holding_finalized(
    finalized: &FinalizedExecution,
    account_proof: &[Vec<u8>],
    storage_proof: &[Vec<u8>],
    token: [u8; 20],
    holder: [u8; 20],
    balances_slot: u64,
    account: &AccountClaim,
    claimed_balance: U256,
) -> Result<ProvenErc20Holding, Erc20ProofError> {
    let mut holding = verify_erc20_holding(
        finalized.execution_state_root(),
        account_proof,
        storage_proof,
        token,
        holder,
        balances_slot,
        account,
        claimed_balance,
        finalized.execution_block_number(),
    )?;
    holding.trust = HoldingTrust::ConsensusProven;
    Ok(holding)
}

// ---------------------------------------------------------------------------
// Chain-agnostic foreign-holding fields (the governance edge)
// ---------------------------------------------------------------------------

/// The stable one-byte EVM chain tag — MUST match `dregg-governance`'s
/// `ChainId::Evm.tag()` (Solana = 0, **EVM = 1**, Cosmos = 2). This crate is a
/// standalone workspace and cannot depend on `dregg-governance`, so the tag is
/// duplicated here as a plain constant; a governance-side test pins the agreement.
pub const CHAIN_TAG_EVM: u8 = 1;

/// The MINIMAL chain-agnostic foreign-holding fields — plain primitives only, so any
/// downstream (dregg-governance's `ProvenForeignHolding`, a wire codec, a circuit
/// witness) can consume them without importing this crate's EVM types.
///
/// ## 20 → 32 byte padding convention
///
/// `holder` and `asset` are the 20-byte EVM address/token address **LEFT-ZERO-PADDED**
/// into 32 bytes: 12 zero bytes, then the 20 address bytes in positions `[12..32]`
/// (the address occupies the low-order/rightmost bytes). This is the same `pad32`
/// convention Solidity ABI encoding and [`erc20_balance_slot_key`] use, and the
/// convention dregg-governance documents for its EVM column.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ForeignHoldingFields {
    /// One-byte chain tag scoping the holding ([`CHAIN_TAG_EVM`] here).
    pub chain_tag: u8,
    /// The holder identity: the 20-byte EVM address, left-zero-padded to 32 bytes.
    pub holder: [u8; 32],
    /// The asset identity: the 20-byte token contract address, left-zero-padded.
    pub asset: [u8; 32],
    /// The proven balance in atomic units. An ERC-20 balance is a `U256` in the wild;
    /// a balance above `u128::MAX` is REFUSED at conversion — never truncated.
    pub amount: u128,
    /// The finalized snapshot height — the EVM execution block number.
    pub snapshot: u64,
    /// True iff a real light-client consensus proof backs the holding
    /// ([`HoldingTrust::ConsensusProven`]); a structure-only holding converts to
    /// `false` and grants ZERO weight downstream — fail closed, always.
    pub consensus_proven: bool,
}

/// Why a holding refused to convert into [`ForeignHoldingFields`]. A refusal NEVER
/// yields fields (fail closed).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ForeignFieldsError {
    /// The proven `U256` balance exceeds `u128::MAX`. Truncating would let an attacker
    /// (or a weird token) alias a huge balance onto a small `amount`; we refuse.
    AmountOverflowsU128 { balance: U256 },
}

impl core::fmt::Display for ForeignFieldsError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::AmountOverflowsU128 { balance } => write!(
                f,
                "proven balance {balance} exceeds u128::MAX — refused (never truncated)"
            ),
        }
    }
}

impl std::error::Error for ForeignFieldsError {}

/// Left-zero-pad a 20-byte EVM address into a 32-byte identity: 12 zero bytes, then
/// the address in `[12..32]` (the `pad32` convention — see [`ForeignHoldingFields`]).
pub fn pad_address_32(addr: &[u8; 20]) -> [u8; 32] {
    let mut out = [0u8; 32];
    out[12..].copy_from_slice(addr);
    out
}

impl ProvenErc20Holding {
    /// True iff the full light-client finality path backs this holding.
    pub fn is_consensus_proven(&self) -> bool {
        self.trust.is_consensus_proven()
    }

    /// Convert this EVM holding into the MINIMAL chain-agnostic
    /// [`ForeignHoldingFields`] (the governance edge).
    ///
    /// Fail-closed: a balance above `u128::MAX` REFUSES with
    /// [`ForeignFieldsError::AmountOverflowsU128`] — it is NEVER truncated. Addresses
    /// are left-zero-padded 20 → 32 ([`pad_address_32`]). `consensus_proven` is `true`
    /// ONLY for a [`HoldingTrust::ConsensusProven`] holding (one minted by
    /// [`verify_erc20_holding_finalized`]); a structure-only holding converts to
    /// `consensus_proven: false`.
    pub fn to_foreign_fields(&self) -> Result<ForeignHoldingFields, ForeignFieldsError> {
        let amount =
            u128::try_from(self.balance).map_err(|_| ForeignFieldsError::AmountOverflowsU128 {
                balance: self.balance,
            })?;
        Ok(ForeignHoldingFields {
            chain_tag: CHAIN_TAG_EVM,
            holder: pad_address_32(&self.holder),
            asset: pad_address_32(&self.token),
            amount,
            snapshot: self.block_number,
            consensus_proven: self.trust.is_consensus_proven(),
        })
    }
}
