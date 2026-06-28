//! `dregg-bridge::solana_consensus`: the **real** Solana Tower-BFT consensus
//! primitives the trustless bridge ([`crate::solana_trustless`]) verifies.
//!
//! This module is the genuine cryptographic heart of the trustless inbound
//! proof-of-lock. It is self-contained — it uses the same Ed25519 signature
//! scheme Solana uses for vote transactions ([`ed25519_dalek`]) and SHA-256 for
//! PoH/bank-hash (the hashes Solana uses), so the *cryptography and the
//! consensus arithmetic are real*, not stubbed.
//!
//! # What is real here
//!
//! - **Stake-weighted vote verification** ([`verify_supermajority`]): given a
//!   tracked per-epoch [`EpochStakeTable`] (validator vote pubkey → active
//!   stake), each [`ValidatorVote`] for the claimed `(slot, bank_hash)` has its
//!   Ed25519 signature verified for real, duplicate voters are collapsed, and the
//!   stake of the *cryptographically valid* voters is summed and checked against
//!   the ≥ 2/3 super-majority threshold. A forged signature contributes zero
//!   stake, so a vote set that needs a forged vote to clear 2/3 is refused.
//! - **Bank-hash binding** ([`BankHashComponents::compute`]): Solana's
//!   `bank_hash = hashv(parent_bank_hash, accounts_delta_hash, signature_count,
//!   last_blockhash)`. We recompute it from its components and bind it to the
//!   voted `bank_hash`, so the accounts hash the inclusion proof opens into is
//!   cryptographically tied to what the super-majority voted.
//! - **Accounts inclusion** ([`verify_accounts_inclusion`]): a domain-separated
//!   sorted-Merkle inclusion of the vault account's lock record into the
//!   accounts (delta) hash the bank hash commits to. Leaf and node hashes carry
//!   distinct domain tags (so an interior node can never be replayed as a leaf).
//! - **PoH linkage** ([`verify_poh_segment`]): a real SHA-256 tick-chain
//!   re-hash from a prior anchor hash to the slot's `last_blockhash`.
//!
//! # The modeled-vs-mainnet boundary (honest)
//!
//! The *logic and cryptography* of Solana finality are real here, but the exact
//! mainnet **wire encodings** are modeled, not byte-reproduced:
//!
//! - [`vote_message`] is a canonical domain-separated `(slot, bank_hash)`
//!   encoding, not the bincode-serialized vote `Transaction`/`VoteInstruction` a
//!   mainnet authorized voter signs. Verifying that a [`ValidatorVote`] really
//!   corresponds to an on-chain vote transaction is the relayer *ingestion*
//!   layer.
//! - The epoch [`EpochStakeTable`] is *tracked input* — sourcing it from (and
//!   proving its rotation against) Solana's own stake program / bank state is the
//!   stake-table-provenance layer.
//! - [`merkle_node`] is a SHA-256 sorted-pair node; mainnet's accounts hash is a
//!   16-ary fan-out merkle over a version-coupled account-hash preimage.
//!
//! So this module verifies that a *provided* vote set + inclusion + PoH are
//! cryptographically a valid ≥2/3 stake-weighted attestation binding the lock
//! record to the voted bank hash. The remaining trust gap is the *adapter*
//! (mainnet wire-format ingestion + stake-table provenance + PoH anchoring
//! policy), not the consensus arithmetic. See `docs/deos/TRUSTLESS-SOLANA-BRIDGE.md`.

use std::collections::{BTreeMap, BTreeSet};

use ed25519_dalek::{Signature, Verifier, VerifyingKey};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use dregg_types::CellId;

/// Serde helper for `[u8; 64]` (serde derives arrays only up to length 32).
/// Serializes as a byte sequence; round-trips under postcard and self-describing
/// formats alike.
mod sig64 {
    use serde::de::{Error, SeqAccess, Visitor};
    use serde::{Deserializer, Serializer};
    use std::fmt;

    pub fn serialize<S: Serializer>(v: &[u8; 64], s: S) -> Result<S::Ok, S::Error> {
        s.serialize_bytes(v)
    }

    struct Sig64Visitor;
    impl<'de> Visitor<'de> for Sig64Visitor {
        type Value = [u8; 64];
        fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("64 bytes of Ed25519 signature")
        }
        fn visit_bytes<E: Error>(self, v: &[u8]) -> Result<[u8; 64], E> {
            v.try_into()
                .map_err(|_| E::invalid_length(v.len(), &"64 bytes"))
        }
        fn visit_seq<A: SeqAccess<'de>>(self, mut seq: A) -> Result<[u8; 64], A::Error> {
            let mut out = [0u8; 64];
            for (i, slot) in out.iter_mut().enumerate() {
                *slot = seq
                    .next_element()?
                    .ok_or_else(|| A::Error::invalid_length(i, &"64 bytes"))?;
            }
            Ok(out)
        }
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(d: D) -> Result<[u8; 64], D::Error> {
        d.deserialize_bytes(Sig64Visitor)
    }
}

// ============================================================================
// Domain-separation tags
// ============================================================================

/// Domain tag for the canonical Tower-BFT vote message a validator signs.
const VOTE_MSG_TAG: &[u8] = b"dregg-solana-tower-vote:v1";
/// Domain tag for an accounts-inclusion Merkle *leaf* (the lock record).
const ACCT_LEAF_TAG: &[u8] = b"dregg-solana-accounts-leaf:v1";
/// Domain tag for an accounts-inclusion Merkle *interior node*.
const ACCT_NODE_TAG: &[u8] = b"dregg-solana-accounts-node:v1";
/// Domain tag for the bank-hash recomputation.
const BANK_HASH_TAG: &[u8] = b"dregg-solana-bank-hash:v1";

// ============================================================================
// Epoch stake table
// ============================================================================

/// The per-epoch active-stake distribution: a map from a validator's authorized
/// **vote pubkey** to its active stake (the 2/3 threshold's denominator is the
/// sum of all entries).
///
/// In a finished bridge this is *tracked state*, sourced from Solana's stake
/// program / bank state and rotated at epoch boundaries (the sync-committee
/// analogue, heavier). Here it is the verifier's trusted input: the consensus
/// arithmetic over it is real; its *provenance* is the remaining adapter layer.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct EpochStakeTable {
    /// The epoch this table is the active stake for.
    pub epoch: u64,
    /// vote pubkey → active stake (lamports).
    stakes: BTreeMap<[u8; 32], u64>,
}

impl EpochStakeTable {
    /// An empty table for `epoch`.
    pub fn new(epoch: u64) -> Self {
        Self {
            epoch,
            stakes: BTreeMap::new(),
        }
    }

    /// Build from `(vote_pubkey, stake)` entries. Later entries for the same
    /// pubkey overwrite earlier ones.
    pub fn from_entries(epoch: u64, entries: impl IntoIterator<Item = ([u8; 32], u64)>) -> Self {
        let mut t = Self::new(epoch);
        for (k, s) in entries {
            t.stakes.insert(k, s);
        }
        t
    }

    /// Record `stake` for `vote_pubkey`.
    pub fn insert(&mut self, vote_pubkey: [u8; 32], stake: u64) {
        self.stakes.insert(vote_pubkey, stake);
    }

    /// The active stake of `vote_pubkey` (0 if not tracked).
    pub fn stake_of(&self, vote_pubkey: &[u8; 32]) -> u64 {
        self.stakes.get(vote_pubkey).copied().unwrap_or(0)
    }

    /// Total active stake for the epoch (the 2/3 denominator). Summed in `u128`
    /// so a full mainnet stake distribution cannot overflow.
    pub fn total_stake(&self) -> u128 {
        self.stakes.values().map(|s| *s as u128).sum()
    }

    /// Number of tracked validators.
    pub fn len(&self) -> usize {
        self.stakes.len()
    }

    /// Whether the table is empty.
    pub fn is_empty(&self) -> bool {
        self.stakes.is_empty()
    }
}

// ============================================================================
// Validator votes (real Ed25519)
// ============================================================================

/// The canonical message a validator's authorized voter signs to attest it
/// voted `bank_hash` at `slot`.
///
/// **Modeled, not mainnet wire:** on mainnet the signed bytes are the
/// bincode-serialized vote `Transaction`'s `Message`; here we use a
/// domain-separated `(slot, bank_hash)` encoding. The Ed25519 verification over
/// it is real; reproducing the exact transaction preimage is the relayer
/// ingestion layer.
pub fn vote_message(slot: u64, bank_hash: &[u8; 32]) -> Vec<u8> {
    let mut m = Vec::with_capacity(VOTE_MSG_TAG.len() + 8 + 32);
    m.extend_from_slice(VOTE_MSG_TAG);
    m.extend_from_slice(&slot.to_le_bytes());
    m.extend_from_slice(bank_hash);
    m
}

/// One validator's Ed25519-signed vote that it voted `bank_hash` at `slot`.
///
/// `vote_pubkey` is the authorized voter's Ed25519 public key (the key the
/// [`EpochStakeTable`] weights). `signature` is over [`vote_message`].
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ValidatorVote {
    /// The authorized voter's Ed25519 public key (matches the stake-table key).
    pub vote_pubkey: [u8; 32],
    /// The slot voted.
    pub slot: u64,
    /// The bank hash voted (the state commitment for `slot`).
    pub bank_hash: [u8; 32],
    /// Ed25519 signature over [`vote_message(slot, bank_hash)`](vote_message).
    #[serde(with = "sig64")]
    pub signature: [u8; 64],
}

impl ValidatorVote {
    /// Verify this vote's Ed25519 signature under `vote_pubkey` over the
    /// canonical [`vote_message`]. Returns `false` on a malformed key/signature
    /// or a verification failure — never panics.
    pub fn verify_signature(&self) -> bool {
        let Ok(vk) = VerifyingKey::from_bytes(&self.vote_pubkey) else {
            return false;
        };
        let sig = Signature::from_bytes(&self.signature);
        vk.verify(&vote_message(self.slot, &self.bank_hash), &sig)
            .is_ok()
    }

    /// **Relayer/test helper:** produce a genuinely-signed vote for `(slot,
    /// bank_hash)` from an [`ed25519_dalek::SigningKey`].
    pub fn sign(signing_key: &ed25519_dalek::SigningKey, slot: u64, bank_hash: [u8; 32]) -> Self {
        use ed25519_dalek::Signer;
        let sig = signing_key.sign(&vote_message(slot, &bank_hash));
        Self {
            vote_pubkey: signing_key.verifying_key().to_bytes(),
            slot,
            bank_hash,
            signature: sig.to_bytes(),
        }
    }
}

/// The result of tallying a vote set: how much *cryptographically valid* stake
/// voted the target `(slot, bank_hash)`, out of the epoch's total.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VoteTally {
    /// Stake of the distinct validators whose signature verified and who voted
    /// the exact target `(slot, bank_hash)`.
    pub voted_stake: u128,
    /// Total active stake for the epoch (the 2/3 denominator).
    pub total_stake: u128,
    /// Number of distinct valid voters counted.
    pub valid_voters: usize,
}

impl VoteTally {
    /// Whether the counted stake clears the ≥ 2/3 super-majority threshold.
    ///
    /// `voted/total ≥ 2/3 ⟺ 3*voted ≥ 2*total` (computed in `u128`).
    pub fn is_supermajority(&self) -> bool {
        self.voted_stake.saturating_mul(3) >= self.total_stake.saturating_mul(2)
    }
}

/// Why a vote set failed super-majority verification.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VoteSetError {
    /// The stake table has zero total stake (no denominator).
    EmptyStakeTable,
    /// The valid voted stake does not clear the ≥ 2/3 threshold.
    StakeBelowSupermajority {
        /// Cryptographically valid voted stake.
        voted: u128,
        /// Total active stake for the epoch.
        total: u128,
    },
}

/// Tally the *cryptographically valid* stake that voted exactly `(slot,
/// bank_hash)`.
///
/// For each vote: it must target the exact `(slot, bank_hash)`; its
/// `vote_pubkey` must be in `stake` with nonzero stake; it must be the first
/// time we see that voter (duplicates collapse); and its Ed25519 signature must
/// verify. Only then does its stake count. Invalid signatures contribute zero.
pub fn tally_votes(
    stake: &EpochStakeTable,
    slot: u64,
    bank_hash: &[u8; 32],
    votes: &[ValidatorVote],
) -> VoteTally {
    let mut counted: BTreeSet<[u8; 32]> = BTreeSet::new();
    let mut voted_stake: u128 = 0;
    for v in votes {
        if v.slot != slot || &v.bank_hash != bank_hash {
            continue;
        }
        let s = stake.stake_of(&v.vote_pubkey);
        if s == 0 {
            continue;
        }
        if counted.contains(&v.vote_pubkey) {
            continue;
        }
        if !v.verify_signature() {
            continue;
        }
        counted.insert(v.vote_pubkey);
        voted_stake += s as u128;
    }
    VoteTally {
        voted_stake,
        total_stake: stake.total_stake(),
        valid_voters: counted.len(),
    }
}

/// Verify that ≥ 2/3 of the epoch's active stake validly voted `(slot,
/// bank_hash)`. The cryptographic heart of "consensus verified".
pub fn verify_supermajority(
    stake: &EpochStakeTable,
    slot: u64,
    bank_hash: &[u8; 32],
    votes: &[ValidatorVote],
) -> Result<VoteTally, VoteSetError> {
    let tally = tally_votes(stake, slot, bank_hash, votes);
    if tally.total_stake == 0 {
        return Err(VoteSetError::EmptyStakeTable);
    }
    if !tally.is_supermajority() {
        return Err(VoteSetError::StakeBelowSupermajority {
            voted: tally.voted_stake,
            total: tally.total_stake,
        });
    }
    Ok(tally)
}

// ============================================================================
// Bank-hash binding
// ============================================================================

/// The components Solana's bank hash commits to, in the order
/// `Bank::hash_internal_state` hashes them. Recomputing [`Self::compute`] and
/// binding it to the voted bank hash ties the accounts hash (and PoH tail) to
/// what the super-majority attested.
///
/// **Modeled hash:** Solana uses `hashv` (SHA-256 over the concatenation) with a
/// version-coupled field layout; we hash the same fields with a domain tag.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BankHashComponents {
    /// The parent slot's bank hash.
    pub parent_bank_hash: [u8; 32],
    /// The accounts (delta) hash this slot commits to — the root the inclusion
    /// proof opens into.
    pub accounts_hash: [u8; 32],
    /// The number of signatures in the slot (part of the bank-hash preimage).
    pub signature_count: u64,
    /// The slot's `last_blockhash` — the PoH chain tail.
    pub last_blockhash: [u8; 32],
}

impl BankHashComponents {
    /// Recompute the bank hash from its components.
    pub fn compute(&self) -> [u8; 32] {
        let mut h = Sha256::new();
        h.update(BANK_HASH_TAG);
        h.update(self.parent_bank_hash);
        h.update(self.accounts_hash);
        h.update(self.signature_count.to_le_bytes());
        h.update(self.last_blockhash);
        h.finalize().into()
    }

    /// Whether these components recompute to `claimed_bank_hash`.
    pub fn binds(&self, claimed_bank_hash: &[u8; 32]) -> bool {
        &self.compute() == claimed_bank_hash
    }
}

// ============================================================================
// Accounts-hash inclusion (domain-separated sorted Merkle)
// ============================================================================

/// Hash the vault account's lock record into an accounts-Merkle **leaf**.
///
/// Binds `(vault_account, amount, recipient, lock_id)` so the inclusion proof
/// can only open into a leaf carrying exactly this lock record.
pub fn account_leaf(
    vault_account: &[u8; 32],
    amount: u64,
    recipient: &CellId,
    lock_id: &[u8; 32],
) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(ACCT_LEAF_TAG);
    h.update(vault_account);
    h.update(amount.to_le_bytes());
    h.update(recipient.as_bytes());
    h.update(lock_id);
    h.finalize().into()
}

/// Hash two children into a parent node, **order-canonical** (sorted): the dregg
/// sorted-Merkle convention. The distinct [`ACCT_NODE_TAG`] (vs the leaf tag)
/// prevents replaying an interior node as a leaf.
pub fn merkle_node(a: &[u8; 32], b: &[u8; 32]) -> [u8; 32] {
    let (lo, hi) = if a <= b { (a, b) } else { (b, a) };
    let mut h = Sha256::new();
    h.update(ACCT_NODE_TAG);
    h.update(lo);
    h.update(hi);
    h.finalize().into()
}

/// Fold a sibling `path` from `leaf` up to a root using the sorted node hash.
pub fn fold_inclusion(leaf: [u8; 32], path: &[[u8; 32]]) -> [u8; 32] {
    let mut acc = leaf;
    for sib in path {
        acc = merkle_node(&acc, sib);
    }
    acc
}

/// Verify that the lock record for `vault_account` is included in
/// `accounts_hash` via `path`.
pub fn verify_accounts_inclusion(
    vault_account: &[u8; 32],
    amount: u64,
    recipient: &CellId,
    lock_id: &[u8; 32],
    path: &[[u8; 32]],
    accounts_hash: &[u8; 32],
) -> bool {
    let leaf = account_leaf(vault_account, amount, recipient, lock_id);
    &fold_inclusion(leaf, path) == accounts_hash
}

// ============================================================================
// PoH linkage (real SHA-256 tick chain)
// ============================================================================

/// A PoH segment: `num_hashes` SHA-256 iterations from `anchor_hash` should
/// yield `tail_hash`. Solana's PoH is exactly `h_{i+1} = sha256(h_i)` (with
/// mixed-in entries at tick/transaction boundaries — modeled here as a pure tick
/// chain). Verifying it proves the leader did the sequential hashing that orders
/// the slot.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PohSegment {
    /// The verified anchor hash the segment chains from.
    pub anchor_hash: [u8; 32],
    /// The number of sequential SHA-256 iterations in the segment.
    pub num_hashes: u64,
    /// The claimed tail hash after `num_hashes` iterations (the slot's
    /// `last_blockhash`).
    pub tail_hash: [u8; 32],
}

/// The largest PoH segment we will re-hash inline, so a malicious `num_hashes`
/// cannot make the verifier spin unboundedly. Trust-minimized PoH over a full
/// slot (~432k hashes/slot on mainnet) needs a recursive proof or a bounded
/// anchor policy — the remaining PoH work.
pub const MAX_POH_REHASH: u64 = 1 << 20;

/// Why a PoH segment failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PohError {
    /// `num_hashes` exceeds [`MAX_POH_REHASH`] — cannot re-hash inline.
    TooLong {
        /// The requested iteration count.
        num_hashes: u64,
    },
    /// The re-hashed tail does not match the claimed `tail_hash`.
    TailMismatch,
}

/// Verify a PoH segment by re-hashing `num_hashes` SHA-256 iterations from the
/// anchor and checking the result equals `tail_hash`.
pub fn verify_poh_segment(seg: &PohSegment) -> Result<(), PohError> {
    if seg.num_hashes > MAX_POH_REHASH {
        return Err(PohError::TooLong {
            num_hashes: seg.num_hashes,
        });
    }
    let mut cur = seg.anchor_hash;
    for _ in 0..seg.num_hashes {
        let mut h = Sha256::new();
        h.update(cur);
        cur = h.finalize().into();
    }
    if cur == seg.tail_hash {
        Ok(())
    } else {
        Err(PohError::TailMismatch)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ed25519_dalek::SigningKey;

    fn cid(b: u8) -> CellId {
        CellId::from_bytes([b; 32])
    }

    fn key(seed: u8) -> SigningKey {
        SigningKey::from_bytes(&[seed; 32])
    }

    #[test]
    fn valid_vote_signature_verifies() {
        let sk = key(1);
        let v = ValidatorVote::sign(&sk, 42, [9u8; 32]);
        assert!(v.verify_signature());
    }

    #[test]
    fn tampered_vote_signature_fails() {
        let sk = key(1);
        let mut v = ValidatorVote::sign(&sk, 42, [9u8; 32]);
        v.bank_hash[0] ^= 0xFF; // sig no longer matches the message
        assert!(!v.verify_signature());
    }

    #[test]
    fn supermajority_reached_with_two_thirds() {
        let (k1, k2, k3) = (key(1), key(2), key(3));
        let bank = [7u8; 32];
        let stake = EpochStakeTable::from_entries(
            5,
            [
                (k1.verifying_key().to_bytes(), 400),
                (k2.verifying_key().to_bytes(), 400),
                (k3.verifying_key().to_bytes(), 200),
            ],
        );
        // 800/1000 = 80% > 2/3.
        let votes = vec![
            ValidatorVote::sign(&k1, 100, bank),
            ValidatorVote::sign(&k2, 100, bank),
        ];
        let tally = verify_supermajority(&stake, 100, &bank, &votes).expect("supermajority");
        assert_eq!(tally.voted_stake, 800);
        assert_eq!(tally.total_stake, 1000);
        assert_eq!(tally.valid_voters, 2);
    }

    #[test]
    fn below_two_thirds_refused() {
        let (k1, k2, k3) = (key(1), key(2), key(3));
        let bank = [7u8; 32];
        let stake = EpochStakeTable::from_entries(
            5,
            [
                (k1.verifying_key().to_bytes(), 400),
                (k2.verifying_key().to_bytes(), 400),
                (k3.verifying_key().to_bytes(), 200),
            ],
        );
        // Only 400/1000 = 40%.
        let votes = vec![ValidatorVote::sign(&k1, 100, bank)];
        assert_eq!(
            verify_supermajority(&stake, 100, &bank, &votes),
            Err(VoteSetError::StakeBelowSupermajority {
                voted: 400,
                total: 1000
            })
        );
    }

    #[test]
    fn forged_signature_contributes_no_stake() {
        let (k1, k2) = (key(1), key(2));
        let bank = [7u8; 32];
        let stake = EpochStakeTable::from_entries(
            5,
            [
                (k1.verifying_key().to_bytes(), 400),
                (k2.verifying_key().to_bytes(), 400),
            ],
        );
        // k1 votes honestly (400). A forged vote claims to be k2 (the other 400)
        // but the signature is garbage — it must NOT count, leaving 400/800 < 2/3.
        let mut forged = ValidatorVote::sign(&k1, 100, bank);
        forged.vote_pubkey = k2.verifying_key().to_bytes(); // claim k2's stake
        // signature is k1's over k1's identity — invalid under k2's key.
        let votes = vec![ValidatorVote::sign(&k1, 100, bank), forged];
        assert_eq!(
            verify_supermajority(&stake, 100, &bank, &votes),
            Err(VoteSetError::StakeBelowSupermajority {
                voted: 400,
                total: 800
            })
        );
    }

    #[test]
    fn duplicate_voter_counts_once() {
        let k1 = key(1);
        let bank = [7u8; 32];
        let stake = EpochStakeTable::from_entries(5, [(k1.verifying_key().to_bytes(), 700)]);
        let votes = vec![
            ValidatorVote::sign(&k1, 100, bank),
            ValidatorVote::sign(&k1, 100, bank),
        ];
        let tally = tally_votes(&stake, 100, &bank, &votes);
        assert_eq!(tally.voted_stake, 700);
        assert_eq!(tally.valid_voters, 1);
    }

    #[test]
    fn vote_for_other_bank_hash_not_counted() {
        let k1 = key(1);
        let stake = EpochStakeTable::from_entries(5, [(k1.verifying_key().to_bytes(), 700)]);
        let other = ValidatorVote::sign(&k1, 100, [0xAA; 32]);
        let tally = tally_votes(&stake, 100, &[7u8; 32], &[other]);
        assert_eq!(tally.voted_stake, 0);
    }

    #[test]
    fn untracked_validator_not_counted() {
        let (k1, intruder) = (key(1), key(9));
        let bank = [7u8; 32];
        let stake = EpochStakeTable::from_entries(5, [(k1.verifying_key().to_bytes(), 700)]);
        // A perfectly-signed vote from a validator NOT in the stake table.
        let v = ValidatorVote::sign(&intruder, 100, bank);
        let tally = tally_votes(&stake, 100, &bank, &[v]);
        assert_eq!(tally.voted_stake, 0);
    }

    #[test]
    fn bank_hash_recomputes_and_binds() {
        let comp = BankHashComponents {
            parent_bank_hash: [1u8; 32],
            accounts_hash: [2u8; 32],
            signature_count: 17,
            last_blockhash: [3u8; 32],
        };
        let bh = comp.compute();
        assert!(comp.binds(&bh));
        let mut wrong = bh;
        wrong[0] ^= 0xFF;
        assert!(!comp.binds(&wrong));
    }

    #[test]
    fn accounts_inclusion_round_trips() {
        // Build a tiny sorted-Merkle tree: leaf for our lock + one sibling.
        let leaf = account_leaf(&[0x22; 32], 500, &cid(1), &[0x44; 32]);
        let sib = [0xEE; 32];
        let root = merkle_node(&leaf, &sib);
        assert!(verify_accounts_inclusion(
            &[0x22; 32],
            500,
            &cid(1),
            &[0x44; 32],
            &[sib],
            &root
        ));
    }

    #[test]
    fn accounts_inclusion_wrong_record_fails() {
        let leaf = account_leaf(&[0x22; 32], 500, &cid(1), &[0x44; 32]);
        let sib = [0xEE; 32];
        let root = merkle_node(&leaf, &sib);
        // Wrong amount → different leaf → does not re-root.
        assert!(!verify_accounts_inclusion(
            &[0x22; 32],
            501,
            &cid(1),
            &[0x44; 32],
            &[sib],
            &root
        ));
    }

    #[test]
    fn accounts_inclusion_wrong_root_fails() {
        let leaf = account_leaf(&[0x22; 32], 500, &cid(1), &[0x44; 32]);
        let sib = [0xEE; 32];
        let root = merkle_node(&leaf, &sib);
        let mut bad = root;
        bad[0] ^= 0xFF;
        assert!(!verify_accounts_inclusion(
            &[0x22; 32],
            500,
            &cid(1),
            &[0x44; 32],
            &[sib],
            &bad
        ));
    }

    #[test]
    fn poh_segment_verifies() {
        // Build a real 1000-tick chain and check it re-hashes.
        let anchor = [0x55u8; 32];
        let mut cur = anchor;
        for _ in 0..1000u64 {
            let mut h = Sha256::new();
            h.update(cur);
            cur = h.finalize().into();
        }
        let seg = PohSegment {
            anchor_hash: anchor,
            num_hashes: 1000,
            tail_hash: cur,
        };
        assert_eq!(verify_poh_segment(&seg), Ok(()));
    }

    #[test]
    fn poh_segment_wrong_tail_fails() {
        let seg = PohSegment {
            anchor_hash: [0x55u8; 32],
            num_hashes: 1000,
            tail_hash: [0u8; 32],
        };
        assert_eq!(verify_poh_segment(&seg), Err(PohError::TailMismatch));
    }

    #[test]
    fn poh_segment_too_long_refused() {
        let seg = PohSegment {
            anchor_hash: [0x55u8; 32],
            num_hashes: MAX_POH_REHASH + 1,
            tail_hash: [0u8; 32],
        };
        assert_eq!(
            verify_poh_segment(&seg),
            Err(PohError::TooLong {
                num_hashes: MAX_POH_REHASH + 1
            })
        );
    }
}
