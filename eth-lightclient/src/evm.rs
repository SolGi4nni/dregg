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

use alloy_primitives::{keccak256, U256};
use alloy_trie::{proof::verify_proof, Nibbles, TrieAccount};

/// Re-exported so downstream code and tests can build balances without depending on
/// `alloy-primitives` directly.
pub use alloy_primitives::U256 as Uint256;

/// A proven, NON-CUSTODIAL ERC-20 holding: at the finalized state identified by
/// `state_root`/`block_number`, `holder` held `balance` atomic units of `token`. The
/// holder never moved anything — this is a read proof over the token contract's storage.
///
/// Shaped after `bridge::solana_holdings::ProvenHolding`: it is only ever produced by
/// the consensus-anchored verify path ([`verify_erc20_holding`]) against a
/// light-client-verified `state_root`; a plain-RPC read must NOT mint one.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProvenErc20Holding {
    /// The holder address (20 bytes) whose balance-slot was opened.
    pub holder: [u8; 20],
    /// The ERC-20 token contract address (20 bytes).
    pub token: [u8; 20],
    /// The proven balance in atomic units (ERC-20 `balanceOf`), big-endian `U256`.
    pub balance: U256,
    /// The finalized execution `state_root` the proof opened against — the anchor the
    /// light client verified; a consumer MUST check this equals the state root it
    /// followed to finality.
    pub state_root: [u8; 32],
    /// The finalized execution block number (provenance of the snapshot).
    pub block_number: u64,
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

/// **Prove a holder's ERC-20 balance at a light-client-verified finalized state —
/// non-custodially.**
///
/// * `state_root` MUST be the execution state root the caller verified via
///   [`crate::finality::verify_finalized_update`]. (Binding the *right* state root is
///   the caller's responsibility, exactly as the Solana path binds the voted bank hash;
///   passing any other root makes the account proof fail closed.)
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
    let trie_account = TrieAccount {
        nonce: account.nonce,
        balance: account.balance,
        storage_root: account.storage_hash.into(),
        code_hash: account.code_hash.into(),
    };
    let account_rlp = alloy_rlp::encode(&trie_account);
    let account_key = Nibbles::unpack(keccak256(token));
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
    .map_err(|_| Erc20ProofError::AccountProofInvalid)?;

    // (2) STORAGE PROOF: storage_hash --MPT--> keccak256(slot_key) -> RLP(balance).
    //     The storage-trie value is the minimal big-endian RLP of the uint256 balance.
    let slot_key = erc20_balance_slot_key(&holder, balances_slot);
    let storage_key = Nibbles::unpack(keccak256(slot_key));
    let balance_rlp = alloy_rlp::encode(claimed_balance);
    let storage_proof_bytes: Vec<alloy_primitives::Bytes> = storage_proof
        .iter()
        .map(|n| alloy_primitives::Bytes::copy_from_slice(n))
        .collect();
    verify_proof(
        account.storage_hash.into(),
        storage_key,
        Some(balance_rlp),
        &storage_proof_bytes,
    )
    .map_err(|_| Erc20ProofError::StorageProofInvalid)?;

    Ok(ProvenErc20Holding {
        holder,
        token,
        balance: claimed_balance,
        state_root,
        block_number,
    })
}
