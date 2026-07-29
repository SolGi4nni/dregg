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
use dregg_lean_ffi::{verified_mpt_lc_verify, MptLcVerdict};

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
///
/// **Unforgeable by construction** — the same discipline as
/// [`crate::finality::FinalizedExecution`], and for the same reason. Every field is PRIVATE, so
/// external code can neither build one by struct literal nor MUTATE a legitimately-obtained one.
/// The paragraph above was the ONLY thing standing between a caller and
///
/// ```text
/// ProvenErc20Holding { balance: whatever, trust: HoldingTrust::ConsensusProven, .. }
/// ```
///
/// — a struct literal that skips `dregg_mpt_lc_verify` AND the entire light-client finality path
/// and converts, via [`ProvenErc20Holding::to_foreign_fields`], straight into
/// `consensus_proven: true` governance weight. A doc-comment is not an access control. The only
/// ways to obtain one are now the three verifying entry points
/// ([`verify_erc20_holding`], [`verify_erc20_holding_wide`], [`verify_erc20_holding_finalized`],
/// plus [`crate::base`] / [`crate::base_fault_proof`] which compose on them) and the loud,
/// greppable [`ProvenErc20Holding::new_unchecked`]. Read the fields through the accessors.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProvenErc20Holding {
    holder: [u8; 20],
    token: [u8; 20],
    balance: U256,
    state_root: [u8; 32],
    block_number: u64,
    trust: HoldingTrust,
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
    /// **FAIL CLOSED — the verified decider is not reachable.** The linked archive does not
    /// export `dregg_mpt_lc_verify` (cold-seed / marshal-only / stale archive, or a target that
    /// cannot link it), so no accept/reject can be rendered for the EVM-inclusion decision.
    /// There is deliberately no Rust fallback: the `is_zero && account_ok && storage_ok`
    /// composition this crate used to decide with WAS the twin `Dregg2.Bridge.LightClientMptGate`
    /// deletes — see [`crate::verified_gate`] for the same posture on the ETH path.
    VerifiedGateUnavailable(String),
    /// The verified gate REFUSED for a conjunct the diagnostic classifier does not model. In this
    /// integration the anchor bindings (state-root / token / mapping-slot) hold by construction
    /// — the proof is opened against the trusted anchors themselves — so this arm is unreachable
    /// unless the gate's decision drifted from the classifier. The REFUSAL still stands
    /// (fail-closed).
    VerifiedGateRefused,
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
            Self::VerifiedGateUnavailable(why) => write!(
                f,
                "verified EVM-inclusion gate `dregg_mpt_lc_verify` is not reachable ({why}) — \
                 refused (fail-closed; there is no unverified Rust twin to fall back to)"
            ),
            Self::VerifiedGateRefused => write!(
                f,
                "verified EVM-inclusion gate refused for an unclassified conjunct — refused \
                 (fail-closed)"
            ),
        }
    }
}

impl std::error::Error for Erc20ProofError {}

/// Compute the storage-trie SLOT KEY for `balances[holder]` where `balances` is a
/// Solidity `mapping(address => uint256)` declared at storage slot `balances_slot`:
/// `keccak256( left_pad32(holder) ‖ uint256_be(balances_slot) )`.
///
/// This is the SMALL-slot convenience over [`erc20_balance_slot_key_wide`]: a
/// `mapping` whose declared base slot fits in a `u64` (slots `0..3` for a hand-written
/// ERC-20, the common case). It delegates to the wide form with the slot padded into a
/// 32-byte big-endian word — the two agree exactly.
pub fn erc20_balance_slot_key(holder: &[u8; 20], balances_slot: u64) -> [u8; 32] {
    let mut base = [0u8; 32];
    // uint256_be(balances_slot): the slot number in the low-order 8 bytes.
    base[24..32].copy_from_slice(&balances_slot.to_be_bytes());
    erc20_balance_slot_key_wide(holder, &base)
}

/// Compute the storage-trie SLOT KEY for `balances[holder]` where the `balances`
/// `mapping(address => uint256)` sits at an ARBITRARY 32-byte base slot:
/// `keccak256( left_pad32(holder) ‖ balances_base_slot )`.
///
/// ## Why the wide form exists (Robinhood-Chain / OZ-v5 glue)
///
/// A Solidity `mapping` element is stored at `keccak256(pad(key) ‖ pad(base_slot))`
/// where `base_slot` is a full `uint256`. [`erc20_balance_slot_key`] restricts the base
/// slot to a `u64` — fine for a hand-written ERC-20 whose `_balances` lives at slot 0..3,
/// but WRONG for a token using OpenZeppelin v5's **ERC-7201 namespaced storage**
/// (`@custom:storage-location erc7201:openzeppelin.storage.ERC20`), where the `ERC20`
/// struct — and thus the `_balances` mapping base slot — is the 32-byte namespace value
/// `keccak256("openzeppelin.storage.ERC20") - 1 & ~0xff`
/// (`0x52c6…bace00`), which does NOT fit in a `u64`.
///
/// Robinhood Chain's tokenized-stock ERC-20s (PLTR, NFLX, AMZN, AMD, TSLA on the testnet)
/// use exactly this OZ-v5 upgradeable layout, so their `balances[holder]` slot key can
/// only be computed with a 32-byte base. This helper is that computation; it is a strict
/// generalization — `erc20_balance_slot_key(h, s) == erc20_balance_slot_key_wide(h, &s_be32)`.
pub fn erc20_balance_slot_key_wide(holder: &[u8; 20], balances_base_slot: &[u8; 32]) -> [u8; 32] {
    let mut preimage = [0u8; 64];
    // pad32(holder): 12 zero bytes then the 20-byte address (left-padded).
    preimage[12..32].copy_from_slice(holder);
    // the full 32-byte mapping base slot.
    preimage[32..64].copy_from_slice(balances_base_slot);
    keccak256(preimage).0
}

/// An MPT proof did not open the claimed key/value under the claimed root — the internal
/// failure marker of the private exclusion re-walk. **Not public**: the three MPT primitives
/// below report a `bool`, deliberately (see [`evm_account_proof_reconstructs`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct MptProofInvalid;

/// **The generalized EIP-1186 ACCOUNT-proof RECONSTRUCTION CARRIER** — does
/// `state_root --MPT--> keccak256(address)` open to `RLP([nonce, balance, storageHash,
/// codeHash])`? Reconstructing the full RLP account leaf binds all four fields at once, so a
/// wrong field, wrong address or wrong state root answers `false`.
///
/// # It returns a `bool`, and that is the point
///
/// This used to be `verify_evm_account_proof(..) -> Result<(), MptProofInvalid>`. Nothing was
/// unsound about it, but the SHAPE lied: an `Ok(())` from a function named `verify_…` reads as a
/// permission, and `verify_evm_account_proof(..)?; verify_evm_storage_slot(..)?;` was a shorter,
/// `?`-chainable spelling of a proof chain that LOOKS gated and never touches
/// `dregg_mpt_lc_verify` — a shorter ungated spelling sitting next to the gated one is how the
/// next defect gets written. A `bool` cannot be mistaken for a permission. These are now named
/// and shaped like this crate's other crypto carriers
/// ([`crate::finality::finality_branch_reconstructs`],
/// [`crate::committee_rotation_reconstructs`]).
///
/// **What it does NOT establish**, stated exactly: it says only that these bytes open under
/// THIS root. It does not say the root is consensus-final (that is
/// [`crate::finality::verify_finalized_update`]), it does not apply the Nomad-law nonzero-balance
/// floor, it does not bind the anchors, and it mints nothing. The accept/reject over these
/// results is `LightClientMptGate.mptVerifyDecision`, rendered by the archive in
/// [`verify_erc20_holding`] — and a [`ProvenErc20Holding`] can only come from there.
///
/// The old permission-shaped spelling no longer exists — the `?`-chain that looked gated and was
/// not cannot be written:
/// ```compile_fail
/// # use eth_lightclient::evm::{evm_account_proof_reconstructs, AccountClaim, Uint256};
/// fn looks_gated(sr: [u8; 32], t: [u8; 20], a: &AccountClaim, p: &[Vec<u8>]) -> Result<(), ()> {
///     evm_account_proof_reconstructs(sr, t, a, p)?;
///     Ok(())
/// }
/// ```
pub fn evm_account_proof_reconstructs(
    state_root: [u8; 32],
    address: [u8; 20],
    account: &AccountClaim,
    account_proof: &[Vec<u8>],
) -> bool {
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
    .is_ok()
}

/// **The generalized EIP-1186 STORAGE-slot RECONSTRUCTION CARRIER** — does
/// `storage_hash --MPT--> keccak256(slot_key)` open to `RLP(value)` (EVM storage values are
/// stored as minimal big-endian RLP)?
///
/// `slot_key` is the RAW 32-byte storage slot (pre-keccak): a mapping-derived key
/// ([`erc20_balance_slot_key`]) for ERC-20 balances, or a dynamic-array element slot
/// for the OP-stack `l2Outputs` anchor ([`crate::base`]). A tampered node, wrong slot,
/// or wrong value answers `false`.
///
/// A `bool`, and what it does NOT establish: see [`evm_account_proof_reconstructs`]. In
/// particular an opened slot is NOT a proven holding — the zero-balance floor and the anchor
/// bindings are the archive's, in [`verify_erc20_holding`]:
/// ```compile_fail
/// # use eth_lightclient::evm::{evm_storage_slot_reconstructs, Uint256};
/// fn looks_gated(sh: [u8; 32], k: [u8; 32], v: Uint256, p: &[Vec<u8>]) -> Result<(), ()> {
///     evm_storage_slot_reconstructs(sh, k, v, p)?;
///     Ok(())
/// }
/// ```
pub fn evm_storage_slot_reconstructs(
    storage_hash: [u8; 32],
    slot_key: [u8; 32],
    value: U256,
    storage_proof: &[Vec<u8>],
) -> bool {
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
    .is_ok()
}

/// **The EIP-1186 storage-slot EXCLUSION RECONSTRUCTION CARRIER** — is `slot_key`
/// **absent** from the storage trie rooted at `storage_hash`, i.e. is the slot's value
/// zero? In the EVM storage MPT a zero-valued slot is not stored at all, so
/// `eth_getProof` answers a zero slot with an exclusion proof: a node path showing
/// the trie does NOT contain `keccak256(slot_key)`. This is the twin of
/// [`evm_storage_slot_reconstructs`] with expected value `None` — needed where a verifier
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
/// Answers `false` for: a proof for a PRESENT key, a truncated/tampered/trailing
/// proof, and an empty proof against anything but the canonical EMPTY trie root.
///
/// A `bool`, and what it does NOT establish: see [`evm_account_proof_reconstructs`]. ⚠ Absence in
/// a trie is only as meaningful as the ROOT it is taken under — this says nothing about where
/// `storage_hash` came from. In [`crate::base_fault_proof`] the root is the ASR account's proven
/// `storageHash` under a light-client-finalized L1 state; anywhere else that binding is the
/// caller's to make.
/// ```compile_fail
/// # use eth_lightclient::evm::evm_storage_slot_absence_reconstructs;
/// fn looks_gated(sh: [u8; 32], k: [u8; 32], p: &[Vec<u8>]) -> Result<(), ()> {
///     evm_storage_slot_absence_reconstructs(sh, k, p)?;
///     Ok(())
/// }
/// ```
pub fn evm_storage_slot_absence_reconstructs(
    storage_hash: [u8; 32],
    slot_key: [u8; 32],
    storage_proof: &[Vec<u8>],
) -> bool {
    let storage_key = Nibbles::unpack(keccak256(slot_key));
    let storage_proof_bytes: Vec<alloy_primitives::Bytes> = storage_proof
        .iter()
        .map(|n| alloy_primitives::Bytes::copy_from_slice(n))
        .collect();
    // Gate 1: the audited baseline exclusion verify.
    if verify_proof(storage_hash.into(), storage_key, None, &storage_proof_bytes).is_err() {
        return false;
    }
    // Gate 2: the strict-termination re-walk (refuses truncation).
    walk_storage_exclusion(storage_hash, &storage_key, &storage_proof_bytes).is_ok()
}

/// The strict-termination MPT exclusion walk (gate 2 of
/// [`evm_storage_slot_absence_reconstructs`] — see there for WHY it exists). Re-walks
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

// ---------------------------------------------------------------------------
// The verified EVM-inclusion decision — the Lean gate is the decider
// ---------------------------------------------------------------------------
//
// `Dregg2.Bridge.LightClientMpt.mptVerify` proves `mpt_noForgery` / `mpt_balance_binding`, and
// `LightClientMptGate.mptVerifyDecision_refines` proves (by `rfl`) that the `@[export]
// dregg_mpt_lc_verify` decision, fed an update's true projections, IS `mptVerify`:
//
//     (bal != 0) && (sr == tsr) && (tk == ttk) && (ms == tms) && account_ok && storage_ok
//
// Until now `verify_erc20_holding` decided that composition in Rust — the Nomad-law zero floor
// (`claimed_balance.is_zero()`) `&&`-ed with the two alloy-trie `verify_proof` results. That Rust
// `&&`-composition is the twin. It is gone: this crate now COMPUTES the two keccak-interleaved
// path-walk RESULTS (`account_ok` / `storage_ok`, the `CryptoLeaf.hashCR` carriers) and hands them,
// with the balance/anchor scalars, to the archive; the gate renders accept/reject.
//
// The anchor bindings (`sr == tsr` &c.) hold BY CONSTRUCTION here: `verify_erc20_holding` opens the
// proof against a SINGLE trusted anchor (there is no separately-carried update root to compare), so
// the update's anchor IS the trusted one and the same value is supplied for both wire fields. The
// decision the gate genuinely renders over this integration is therefore the zero floor composed
// with the two path walks — exactly the composition deleted from Rust.
//
// Fail-closed: an archive that does not export the gate ⇒ `Err(VerifiedGateUnavailable)` and the
// holding is REFUSED. There is no unverified Rust fallback — the Rust rules WERE the twin.

/// The MPT gate route-through, shared by [`verify_erc20_holding`] and [`verify_erc20_holding_wide`].
/// Computes the two keccak path-walk RESULTS (dominated-conjunct short-circuited, monotone-safe),
/// hands the balance/anchor scalars + those results to `@[export] dregg_mpt_lc_verify`, and mints a
/// [`HoldingTrust::StructureOnly`] holding ONLY on the gate's accept. `slot_key` is the already-
/// derived storage-trie slot key (narrow or wide); `slot_decimal` is that mapping-slot's decimal
/// `Nat` encoding for the wire (supplied for both trusted and carried — equal by construction).
#[allow(clippy::too_many_arguments)]
fn mpt_gate_holding(
    state_root: [u8; 32],
    account_proof: &[Vec<u8>],
    storage_proof: &[Vec<u8>],
    token: [u8; 20],
    holder: [u8; 20],
    slot_key: [u8; 32],
    slot_decimal: String,
    account: &AccountClaim,
    claimed_balance: U256,
    block_number: u64,
) -> Result<ProvenErc20Holding, Erc20ProofError> {
    // DOMINATED-CONJUNCT SHORT-CIRCUIT (mirrors `verified_gate`'s ETH pattern): the zero floor and
    // a failed account walk each dominate the `mptVerify` conjunction, so reporting `false` for the
    // work below them is monotone-downward — it can only make the gate refuse more, never admit.
    let dominated_zero = claimed_balance.is_zero();
    let account_ok = if dominated_zero {
        false
    } else {
        evm_account_proof_reconstructs(state_root, token, account, account_proof)
    };
    let storage_ok = if dominated_zero || !account_ok {
        false
    } else {
        evm_storage_slot_reconstructs(
            account.storage_hash,
            slot_key,
            claimed_balance,
            storage_proof,
        )
    };

    // The model's projections are `Nat` decimals; the digest/identifier scalars are the decimal
    // encodings of the 256-bit / 160-bit values (they do not fit a fixed integer, hence `&str`).
    // Carried == trusted by construction (see the note above), so the same value is supplied twice.
    let bal = claimed_balance.to_string();
    let sr = U256::from_be_bytes(state_root).to_string();
    let tk = U256::from_be_slice(&token).to_string();

    match verified_mpt_lc_verify(
        &bal,
        &sr,
        &sr,
        &tk,
        &tk,
        &slot_decimal,
        &slot_decimal,
        account_ok,
        storage_ok,
    ) {
        Ok(MptLcVerdict::Accept) => Ok(ProvenErc20Holding {
            holder,
            token,
            balance: claimed_balance,
            state_root,
            block_number,
            trust: HoldingTrust::StructureOnly,
        }),
        Ok(MptLcVerdict::Reject) => {
            Err(mpt_refusal_reason(claimed_balance, account_ok, storage_ok))
        }
        Err(why) => Err(Erc20ProofError::VerifiedGateUnavailable(why)),
    }
}

/// Attach a specific fail-closed reason to a refusal the VERIFIED gate has ALREADY rendered — the
/// non-authoritative diagnostic for the MPT path (the analog of `verified_gate::refusal_reason`).
/// It is called only after the gate returned `Reject`; every arm returns an `Erc20ProofError` and
/// it has no accepting outcome. The arms follow `mptVerifyDecision`'s `&&` order so the specific
/// error (`ZeroBalance` / `AccountProofInvalid` / `StorageProofInvalid`) matches the deleted Rust
/// path's fail-closed vocabulary exactly.
fn mpt_refusal_reason(
    claimed_balance: U256,
    account_ok: bool,
    storage_ok: bool,
) -> Erc20ProofError {
    if claimed_balance.is_zero() {
        Erc20ProofError::ZeroBalance
    } else if !account_ok {
        Erc20ProofError::AccountProofInvalid
    } else if !storage_ok {
        Erc20ProofError::StorageProofInvalid
    } else {
        // Unreachable in this integration (the anchor bindings hold by construction); the gate
        // nonetheless refused, so the holding stays refused (fail-closed).
        Erc20ProofError::VerifiedGateRefused
    }
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
    // THE DECISION is the verified Lean gate's, not a Rust `&&`-composition. This computes the two
    // keccak path-walk RESULTS and the balance/anchor scalars and routes them through
    // `dregg_mpt_lc_verify` (the zero floor, the anchor bindings and the two walks are
    // `mptVerifyDecision`, which `mptVerifyDecision_refines` proves is `mptVerify`). Fail-closed on
    // a missing archive ([`Erc20ProofError::VerifiedGateUnavailable`]) — no unverified twin remains.
    let slot_key = erc20_balance_slot_key(&holder, balances_slot);
    mpt_gate_holding(
        state_root,
        account_proof,
        storage_proof,
        token,
        holder,
        slot_key,
        balances_slot.to_string(),
        account,
        claimed_balance,
        block_number,
    )
}

/// **Prove a holder's ERC-20 balance where the `balances` mapping sits at an ARBITRARY
/// 32-byte base slot** — the wide analog of [`verify_erc20_holding`]. Identical proof
/// chain and fail-closed refusals; the ONLY difference is that the balance-slot key is
/// [`erc20_balance_slot_key_wide`] over a 32-byte base rather than a `u64`.
///
/// This is the entry point for tokens using OpenZeppelin v5's **ERC-7201 namespaced
/// storage** (the `_balances` mapping base slot is the 32-byte `openzeppelin.storage.ERC20`
/// namespace, `0x52c6…bace00`, not a small slot) — e.g. **Robinhood Chain's tokenized
/// stocks** (chain id 46630: PLTR, NFLX, AMZN, AMD, TSLA). `verify_erc20_holding` cannot
/// address their balance slot; this can. Mints a [`HoldingTrust::StructureOnly`] holding
/// (the `state_root` is caller-supplied — see the trust grading below).
///
/// ## Trust anchor (honest)
///
/// The proof is verified against a **caller-supplied `state_root`**. For an
/// Ethereum-L1 target that root can be recovered by the full Altair sync-committee
/// finality path ([`verify_erc20_holding_finalized`]), yielding `ConsensusProven`. For an
/// **Arbitrum-Orbit L2 like Robinhood Chain there is NO Altair beacon / sync committee**:
/// the honest near-term anchor is **weak-subjectivity** — trust a checkpointed/recent
/// Robinhood-Chain state root (exactly the `StructureOnly` rung, `consensus_proven:false`,
/// ZERO governance weight). The trustless upgrade is to verify the L2 state against its
/// **L1 (Ethereum) Arbitrum-rollup anchor** (the L2 output root posted to the L1
/// `SequencerInbox`/rollup contract, itself opened with the SAME EIP-1186 machinery). This
/// function does NOT establish that; it verifies the MPT chain under whatever root it is
/// handed, and reports `StructureOnly` so downstream weight stays fail-closed.
#[allow(clippy::too_many_arguments)]
pub fn verify_erc20_holding_wide(
    state_root: [u8; 32],
    account_proof: &[Vec<u8>],
    storage_proof: &[Vec<u8>],
    token: [u8; 20],
    holder: [u8; 20],
    balances_base_slot: [u8; 32],
    account: &AccountClaim,
    claimed_balance: U256,
    block_number: u64,
) -> Result<ProvenErc20Holding, Erc20ProofError> {
    // THE DECISION is the verified Lean gate's (see [`verify_erc20_holding`]); the ONLY difference
    // is the WIDE (32-byte-base) balances-mapping slot key. Same fail-closed posture.
    let slot_key = erc20_balance_slot_key_wide(&holder, &balances_base_slot);
    mpt_gate_holding(
        state_root,
        account_proof,
        storage_proof,
        token,
        holder,
        slot_key,
        U256::from_be_bytes(balances_base_slot).to_string(),
        account,
        claimed_balance,
        block_number,
    )
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
    let holding = verify_erc20_holding(
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
    // The promotion is `pub(crate)` and this is one of the three sites that HOLD the evidence:
    // the root and block number came from the `FinalizedExecution` the light client verified,
    // never from the caller.
    Ok(holding.promoted_to_consensus_proven())
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
    /// Construct a `ProvenErc20Holding` **WITHOUT any MPT or light-client verification** — the
    /// caller ASSERTS these values came from a genuinely verified proof chain (the
    /// `from_utf8_unchecked` idiom, exactly as
    /// [`crate::finality::FinalizedExecution::new_unchecked`]). Production code obtains one ONLY
    /// from [`verify_erc20_holding`] / [`verify_erc20_holding_wide`] /
    /// [`verify_erc20_holding_finalized`]; every other construction site is this loud, greppable
    /// name. Passing [`HoldingTrust::ConsensusProven`] here asserts a light-client finality proof
    /// that this function did not see — a grep for `new_unchecked` is the review surface.
    pub fn new_unchecked(
        holder: [u8; 20],
        token: [u8; 20],
        balance: U256,
        state_root: [u8; 32],
        block_number: u64,
        trust: HoldingTrust,
    ) -> Self {
        ProvenErc20Holding {
            holder,
            token,
            balance,
            state_root,
            block_number,
            trust,
        }
    }

    /// The holder address (20 bytes) whose balance slot was opened.
    ///
    /// External code cannot mutate this field directly:
    /// ```compile_fail
    /// # use eth_lightclient::evm::{ProvenErc20Holding, HoldingTrust, Uint256};
    /// let mut h = ProvenErc20Holding::new_unchecked(
    ///     [0u8; 20], [0u8; 20], Uint256::from(1u64), [0u8; 32], 0, HoldingTrust::StructureOnly);
    /// h.holder = [9u8; 20];
    /// ```
    pub fn holder(&self) -> [u8; 20] {
        self.holder
    }

    /// The ERC-20 token contract address (20 bytes).
    ///
    /// External code cannot mutate this field directly:
    /// ```compile_fail
    /// # use eth_lightclient::evm::{ProvenErc20Holding, HoldingTrust, Uint256};
    /// let mut h = ProvenErc20Holding::new_unchecked(
    ///     [0u8; 20], [0u8; 20], Uint256::from(1u64), [0u8; 32], 0, HoldingTrust::StructureOnly);
    /// h.token = [9u8; 20];
    /// ```
    pub fn token(&self) -> [u8; 20] {
        self.token
    }

    /// The proven balance in atomic units (ERC-20 `balanceOf`).
    ///
    /// External code cannot inflate it after the fact:
    /// ```compile_fail
    /// # use eth_lightclient::evm::{ProvenErc20Holding, HoldingTrust, Uint256};
    /// let mut h = ProvenErc20Holding::new_unchecked(
    ///     [0u8; 20], [0u8; 20], Uint256::from(1u64), [0u8; 32], 0, HoldingTrust::StructureOnly);
    /// h.balance = Uint256::MAX;
    /// ```
    pub fn balance(&self) -> U256 {
        self.balance
    }

    /// The execution `state_root` the proof opened against. Only trustworthy as a finality
    /// anchor when [`ProvenErc20Holding::trust`] is [`HoldingTrust::ConsensusProven`].
    pub fn state_root(&self) -> [u8; 32] {
        self.state_root
    }

    /// The execution block number (provenance of the snapshot).
    pub fn block_number(&self) -> u64 {
        self.block_number
    }

    /// Which verify path minted this holding (consensus-anchored vs bare-root).
    ///
    /// **This is the field the seal exists for.** External code cannot promote a structure-only
    /// holding into a consensus-proven one:
    /// ```compile_fail
    /// # use eth_lightclient::evm::{ProvenErc20Holding, HoldingTrust, Uint256};
    /// let mut h = ProvenErc20Holding::new_unchecked(
    ///     [0u8; 20], [0u8; 20], Uint256::from(1u64), [0u8; 32], 0, HoldingTrust::StructureOnly);
    /// h.trust = HoldingTrust::ConsensusProven;
    /// ```
    /// …and cannot mint one by struct literal either:
    /// ```compile_fail
    /// # use eth_lightclient::evm::{ProvenErc20Holding, HoldingTrust, Uint256};
    /// let h = ProvenErc20Holding {
    ///     holder: [0u8; 20],
    ///     token: [0u8; 20],
    ///     balance: Uint256::from(1_000_000u64),
    ///     state_root: [0u8; 32],
    ///     block_number: 0,
    ///     trust: HoldingTrust::ConsensusProven,
    /// };
    /// ```
    pub fn trust(&self) -> HoldingTrust {
        self.trust
    }

    /// Promote a structure-only holding to [`HoldingTrust::ConsensusProven`] — CRATE-INTERNAL,
    /// and reachable only from a path that HOLDS the light-client evidence: the ERC-20 finalized
    /// entry ([`verify_erc20_holding_finalized`], which takes a
    /// [`FinalizedExecution`]) and the Base compositions ([`crate::base`],
    /// [`crate::base_fault_proof`]), which chain L1 finality → L1-committed output root → bound
    /// L2 state root before calling it. `pub(crate)` is the whole point: the promotion is the
    /// governance-weight switch, and no downstream crate can reach it.
    pub(crate) fn promoted_to_consensus_proven(mut self) -> Self {
        self.trust = HoldingTrust::ConsensusProven;
        self
    }

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
