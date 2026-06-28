//! `dregg-bridge::solana_wire`: the **mainnet wire-format adapter** for the
//! trustless Solana bridge — pass 2 of the grind.
//!
//! [`crate::solana_consensus`] (pass 1) made the *consensus cryptography* real:
//! stake-weighted Ed25519 super-majority, bank-hash binding, accounts inclusion,
//! PoH. Its honest gap was that the *inputs* were canonical placeholders, not
//! mainnet artifacts. This module closes the two dominant wire-format gaps:
//!
//! 1. **Real vote-transaction ingestion** ([`parse_verified_vote_tx`] /
//!    [`ingest_vote_transaction`]). A real Solana authorized voter signs a
//!    bincode [`solana_vote_interface`] `Transaction` carrying a
//!    [`VoteInstruction`](solana_vote_interface::instruction::VoteInstruction)
//!    (`Vote` / `TowerSync` / `CompactUpdateVoteState` / `UpdateVoteState`) over
//!    its vote account, voting a `(slot, bank_hash)`. We parse the **real wire
//!    bytes** (the compact-`u16` `ShortVec` framing + the bincode message), verify
//!    the **real Ed25519 signature** of the designated vote authority over the
//!    real serialized message, extract the voted `(slot, bank_hash)` + the vote
//!    account + the authorized voter, and produce a
//!    [`ValidatorVote`](crate::solana_consensus::ValidatorVote) carrying a
//!    [`VoteTxWitness`](crate::solana_consensus::VoteTxWitness). The pass-1
//!    [`verify_supermajority`](crate::solana_consensus::verify_supermajority) then
//!    runs over **real vote transactions**, not the placeholder message.
//!
//! 2. **Real accounts-hash format** ([`solana_account_hash`] +
//!    [`verify_account_inclusion_16ary`]). Solana's accounts hash is a **16-ary
//!    fan-out** Merkle (`MERKLE_FANOUT = 16`) over per-account hashes, where each
//!    account hash is `blake3(lamports_le ‖ rent_epoch_le ‖ data ‖ executable ‖
//!    owner ‖ pubkey)` (zero-lamport accounts hash to the all-zero default), and
//!    each interior node is `sha256(child‖child‖…)` over up to 16 children. We
//!    reproduce that exactly, and bind it to the slot's `bank_hash` via the real
//!    `bank_hash = sha256(parent ‖ accounts_delta_hash ‖ signature_count_le ‖
//!    last_blockhash)` recipe (see [`crate::solana_consensus::BankHashComponents`]).
//!
//! # The honest modeled-vs-mainnet boundary (still open after pass 2)
//!
//! - **Authorized-voter binding.** We verify the *real signature* of the key the
//!   vote instruction *designates* as the vote authority, and that it is a real
//!   signer of the transaction. Confirming that this key is genuinely the vote
//!   account's on-chain `authorized_voter` (so a relayer cannot craft a tx naming
//!   an attacker key as authority) requires the vote account's bank state — the
//!   **same provenance family as the stake table**. It is bundled into the
//!   stake-table-provenance pass (pass 3), not closed here.
//! - **Stake-table provenance + epoch rotation, PoH anchoring policy, the
//!   Option-B succinct wrapper** remain as named in
//!   `docs/deos/TRUSTLESS-SOLANA-BRIDGE.md`.
//! - **Account-data lock-record layout.** The vault account's `data` carries the
//!   lock record in an *adapter-defined* layout ([`encode_lock_record`]); the
//!   per-account *hash* and the 16-ary tree are mainnet-faithful, but the lock
//!   program's account schema is a deploy-time choice, not a Solana constant.
//!
//! So pass 2 makes the **vote-transaction wire format + signature** and the
//! **accounts-hash format** mainnet-faithful; the residual trust is bank-state
//! *provenance* (authority + stake), not the wire decoding or the hashing.

use blake3::Hasher as Blake3;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use ed25519_dalek::{Signature, Verifier, VerifyingKey};

use dregg_types::CellId;

use crate::solana_consensus::{ValidatorVote, VoteTxWitness};

// ============================================================================
// Errors
// ============================================================================

/// Why a vote-transaction ingestion or accounts-hash check failed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WireError {
    /// The byte buffer ended before a field could be fully read.
    Truncated,
    /// A compact-`u16` (`ShortVec`) length was malformed (non-canonical or > 3
    /// bytes / overflowing 16 bits).
    BadCompactU16,
    /// The transaction declares a versioned message we do not resolve (only
    /// legacy and v0-without-address-table-lookups vote transactions are
    /// supported; vote transactions never use address lookup tables).
    UnsupportedVersion {
        /// The transaction version byte's low 7 bits.
        version: u8,
    },
    /// The transaction uses address-table lookups; its full account-key set
    /// cannot be resolved from the transaction bytes alone.
    AddressTableLookupsUnsupported,
    /// The transaction carries no instruction to the Vote program.
    NotAVoteTransaction,
    /// The Vote-program instruction data did not bincode-decode to a known
    /// `VoteInstruction`, or is one that carries no vote (e.g. `Authorize`).
    UndecodableVoteInstruction,
    /// The vote carried no voted slot (empty `slots` / `lockouts`).
    EmptyVote,
    /// An account index referenced by the vote instruction is out of range of
    /// the message's account-key array.
    AccountIndexOutOfRange,
    /// The key the vote instruction designates as the vote authority is not one
    /// of the transaction's required signers, so its vote is not authorized by a
    /// signature.
    AuthorityNotSigner,
    /// A required signature did not verify under its account key over the real
    /// serialized message (a forged / corrupt transaction).
    SignatureInvalid,
}

impl std::fmt::Display for WireError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Truncated => write!(f, "transaction bytes truncated"),
            Self::BadCompactU16 => write!(f, "malformed compact-u16 length"),
            Self::UnsupportedVersion { version } => {
                write!(f, "unsupported transaction version {version}")
            }
            Self::AddressTableLookupsUnsupported => {
                write!(f, "address-table lookups cannot be resolved from tx bytes")
            }
            Self::NotAVoteTransaction => write!(f, "no Vote-program instruction present"),
            Self::UndecodableVoteInstruction => {
                write!(f, "instruction data is not a vote-carrying VoteInstruction")
            }
            Self::EmptyVote => write!(f, "vote carries no voted slot"),
            Self::AccountIndexOutOfRange => write!(f, "account index out of range"),
            Self::AuthorityNotSigner => write!(f, "designated vote authority is not a tx signer"),
            Self::SignatureInvalid => write!(f, "a required signature did not verify"),
        }
    }
}

impl std::error::Error for WireError {}

// ============================================================================
// (1) Real transaction wire parse
// ============================================================================

/// A reader over a byte buffer that never panics: every read is bounds-checked
/// and returns [`WireError::Truncated`] past the end.
struct Cursor<'a> {
    buf: &'a [u8],
    pos: usize,
}

impl<'a> Cursor<'a> {
    fn new(buf: &'a [u8]) -> Self {
        Self { buf, pos: 0 }
    }

    fn take(&mut self, n: usize) -> Result<&'a [u8], WireError> {
        let end = self.pos.checked_add(n).ok_or(WireError::Truncated)?;
        if end > self.buf.len() {
            return Err(WireError::Truncated);
        }
        let s = &self.buf[self.pos..end];
        self.pos = end;
        Ok(s)
    }

    fn u8(&mut self) -> Result<u8, WireError> {
        Ok(self.take(1)?[0])
    }

    fn arr32(&mut self) -> Result<[u8; 32], WireError> {
        let mut out = [0u8; 32];
        out.copy_from_slice(self.take(32)?);
        Ok(out)
    }

    fn arr64(&mut self) -> Result<[u8; 64], WireError> {
        let mut out = [0u8; 64];
        out.copy_from_slice(self.take(64)?);
        Ok(out)
    }

    /// Solana's `ShortU16`: a little-endian, 7-bits-per-byte varint that encodes
    /// a `u16` in 1–3 bytes (high bit = continuation). The encoding is canonical:
    /// a continuation bit with no further value bits, or a value exceeding 16
    /// bits, is rejected.
    fn compact_u16(&mut self) -> Result<usize, WireError> {
        let mut val: u32 = 0;
        for i in 0..3usize {
            let byte = self.u8()?;
            let bits = (byte & 0x7f) as u32;
            val |= bits << (i * 7);
            if byte & 0x80 == 0 {
                // Canonicality: a non-final byte must carry continuation; the
                // final byte's bits must fit (the 3rd byte may only set 2 bits).
                if i == 2 && byte > 0x03 {
                    return Err(WireError::BadCompactU16);
                }
                if i > 0 && byte == 0 {
                    return Err(WireError::BadCompactU16);
                }
                if val > u16::MAX as u32 {
                    return Err(WireError::BadCompactU16);
                }
                return Ok(val as usize);
            }
        }
        Err(WireError::BadCompactU16)
    }
}

/// A compiled instruction: a program-id index + account indices + opaque data,
/// all indexing into the message's account-key array.
#[derive(Clone, Debug)]
struct CompiledInstruction {
    program_id_index: u8,
    accounts: Vec<u8>,
    data: Vec<u8>,
}

/// A parsed transaction message (legacy or v0), plus the exact serialized
/// message bytes that were signed.
struct ParsedMessage {
    num_required_signatures: u8,
    account_keys: Vec<[u8; 32]>,
    instructions: Vec<CompiledInstruction>,
    /// The exact bytes the authorized voter signed (the serialized message,
    /// including the version prefix for a versioned transaction).
    signed_message: Vec<u8>,
}

/// A parsed transaction: the signatures + the message.
struct ParsedTransaction {
    signatures: Vec<[u8; 64]>,
    message: ParsedMessage,
}

/// Parse a real bincode-serialized Solana `Transaction` (legacy or v0).
///
/// Handles the compact-`u16` `ShortVec` framing for the signature array, the
/// account-key array, the instruction array, and per-instruction account/data
/// arrays. v0 messages with non-empty address-table lookups are refused (their
/// full key set is not resolvable from the bytes alone; vote transactions never
/// use them).
fn parse_transaction(bytes: &[u8]) -> Result<ParsedTransaction, WireError> {
    let mut c = Cursor::new(bytes);

    // signatures: ShortVec<Signature>
    let n_sigs = c.compact_u16()?;
    let mut signatures = Vec::with_capacity(n_sigs);
    for _ in 0..n_sigs {
        signatures.push(c.arr64()?);
    }

    // The message begins here; Solana signs the serialized message bytes.
    let message_start = c.pos;

    // Detect a versioned message by the high bit of the first message byte.
    let first = *bytes.get(message_start).ok_or(WireError::Truncated)?;
    let versioned = first & 0x80 != 0;
    if versioned {
        let version = first & 0x7f;
        if version != 0 {
            return Err(WireError::UnsupportedVersion { version });
        }
        c.pos += 1; // consume the version prefix
    }

    // MessageHeader: 3 bytes.
    let num_required_signatures = c.u8()?;
    let _num_readonly_signed = c.u8()?;
    let _num_readonly_unsigned = c.u8()?;

    // account_keys: ShortVec<Pubkey>
    let n_keys = c.compact_u16()?;
    let mut account_keys = Vec::with_capacity(n_keys);
    for _ in 0..n_keys {
        account_keys.push(c.arr32()?);
    }

    // recent_blockhash: [u8; 32]
    let _recent_blockhash = c.arr32()?;

    // instructions: ShortVec<CompiledInstruction>
    let n_ix = c.compact_u16()?;
    let mut instructions = Vec::with_capacity(n_ix);
    for _ in 0..n_ix {
        let program_id_index = c.u8()?;
        let n_accts = c.compact_u16()?;
        let accounts = c.take(n_accts)?.to_vec();
        let n_data = c.compact_u16()?;
        let data = c.take(n_data)?.to_vec();
        instructions.push(CompiledInstruction {
            program_id_index,
            accounts,
            data,
        });
    }

    // v0 trailer: address_table_lookups (must be empty for a resolvable vote tx).
    if versioned {
        let n_lookups = c.compact_u16()?;
        if n_lookups != 0 {
            return Err(WireError::AddressTableLookupsUnsupported);
        }
    }

    // The signed message is exactly the slice from the message start to the end
    // of the buffer (a transaction has nothing after its message).
    let signed_message = bytes[message_start..].to_vec();

    Ok(ParsedTransaction {
        signatures,
        message: ParsedMessage {
            num_required_signatures,
            account_keys,
            instructions,
            signed_message,
        },
    })
}

// ============================================================================
// (1) Vote extraction + real signature verification
// ============================================================================

/// A real, signature-verified vote extracted from a mainnet vote transaction.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IngestedVote {
    /// The vote account the stake distribution weights (the `EpochStakeTable`
    /// key). Stake is delegated to this account, not to the signer.
    pub vote_account: [u8; 32],
    /// The key the vote instruction designates as the vote authority and which
    /// signed the transaction. Confirming this is the vote account's on-chain
    /// authorized voter is bank-state provenance (pass 3).
    pub authorized_voter: [u8; 32],
    /// The slot voted (the last/newest voted slot in the tower).
    pub voted_slot: u64,
    /// The bank hash voted (the `hash` field of the vote / vote-state update).
    pub voted_bank_hash: [u8; 32],
}

/// `(vote_account meta index, authority meta index)` for each vote-carrying
/// `VoteInstruction` variant. The meta indices index into the instruction's
/// `accounts` array, which in turn indexes the message's account keys.
fn vote_meta_indices(
    ix: &solana_vote_interface::instruction::VoteInstruction,
) -> Option<(usize, usize, u64, [u8; 32])> {
    use solana_vote_interface::instruction::VoteInstruction as VI;

    // Returns (vote_account_meta, authority_meta, voted_slot, bank_hash).
    let (vote_acct_meta, auth_meta, slot, hash) = match ix {
        // 0: vote account, 1: slot hashes, 2: clock, 3: vote authority
        VI::Vote(v) => (0, 3, v.last_voted_slot()?, v.hash.to_bytes()),
        VI::VoteSwitch(v, _) => (0, 3, v.last_voted_slot()?, v.hash.to_bytes()),
        // 0: vote account, 1: vote authority
        VI::UpdateVoteState(u) => (0, 1, u.last_voted_slot()?, u.hash.to_bytes()),
        VI::UpdateVoteStateSwitch(u, _) => (0, 1, u.last_voted_slot()?, u.hash.to_bytes()),
        VI::CompactUpdateVoteState(u) => (0, 1, u.last_voted_slot()?, u.hash.to_bytes()),
        VI::CompactUpdateVoteStateSwitch(u, _) => (0, 1, u.last_voted_slot()?, u.hash.to_bytes()),
        VI::TowerSync(t) => (0, 1, t.last_voted_slot()?, t.hash.to_bytes()),
        VI::TowerSyncSwitch(t, _) => (0, 1, t.last_voted_slot()?, t.hash.to_bytes()),
        _ => return None,
    };
    Some((vote_acct_meta, auth_meta, slot, hash))
}

/// Parse a real Solana vote transaction and verify it.
///
/// Steps (all real):
/// 1. parse the transaction wire bytes (legacy or v0);
/// 2. **verify every required Ed25519 signature** under its account key over the
///    real serialized message — a forged or corrupt transaction is refused;
/// 3. locate the (first) Vote-program instruction and bincode-decode its
///    `VoteInstruction`;
/// 4. extract the voted `(slot, bank_hash)`, the vote account, and the
///    designated vote authority;
/// 5. require the authority to be one of the verified signers (so the vote is
///    backed by a real signature from the designated authority).
pub fn parse_verified_vote_tx(bytes: &[u8]) -> Result<IngestedVote, WireError> {
    let tx = parse_transaction(bytes)?;
    let msg = &tx.message;

    // (2) verify every required signature over the real serialized message.
    let n_req = msg.num_required_signatures as usize;
    if tx.signatures.len() < n_req || msg.account_keys.len() < n_req {
        return Err(WireError::Truncated);
    }
    for i in 0..n_req {
        let vk = VerifyingKey::from_bytes(&msg.account_keys[i])
            .map_err(|_| WireError::SignatureInvalid)?;
        let sig = Signature::from_bytes(&tx.signatures[i]);
        vk.verify(&msg.signed_message, &sig)
            .map_err(|_| WireError::SignatureInvalid)?;
    }

    // (3) find the Vote-program instruction and decode it.
    let vote_program = solana_vote_interface::program::id().to_bytes();
    for cix in &msg.instructions {
        let pid = *msg
            .account_keys
            .get(cix.program_id_index as usize)
            .ok_or(WireError::AccountIndexOutOfRange)?;
        if pid != vote_program {
            continue;
        }
        let vi: solana_vote_interface::instruction::VoteInstruction =
            bincode::deserialize(&cix.data).map_err(|_| WireError::UndecodableVoteInstruction)?;

        // (4) extract metas + voted (slot, hash).
        let Some((vote_acct_meta, auth_meta, voted_slot, voted_bank_hash)) = vote_meta_indices(&vi)
        else {
            // A Vote-program instruction that carries no vote (Authorize, etc.).
            return Err(WireError::UndecodableVoteInstruction);
        };

        let key_of_meta = |meta: usize| -> Result<(usize, [u8; 32]), WireError> {
            let key_idx = *cix
                .accounts
                .get(meta)
                .ok_or(WireError::AccountIndexOutOfRange)?;
            let key = *msg
                .account_keys
                .get(key_idx as usize)
                .ok_or(WireError::AccountIndexOutOfRange)?;
            Ok((key_idx as usize, key))
        };

        let (_, vote_account) = key_of_meta(vote_acct_meta)?;
        let (auth_key_idx, authorized_voter) = key_of_meta(auth_meta)?;

        // (5) the authority must be a verified signer (its key index is among
        // the first `num_required_signatures` account keys, all of which we
        // verified above).
        if auth_key_idx >= n_req {
            return Err(WireError::AuthorityNotSigner);
        }

        if voted_slot == 0 && voted_bank_hash == [0u8; 32] {
            // Defensive: a vote-state update with no real content.
            return Err(WireError::EmptyVote);
        }

        return Ok(IngestedVote {
            vote_account,
            authorized_voter,
            voted_slot,
            voted_bank_hash,
        });
    }

    Err(WireError::NotAVoteTransaction)
}

/// Ingest a real vote transaction into a [`ValidatorVote`] the pass-1
/// [`verify_supermajority`](crate::solana_consensus::verify_supermajority)
/// consumes.
///
/// The produced vote is **keyed by the vote account** (the stake-table key) and
/// carries a [`VoteTxWitness`] of the raw transaction bytes. When
/// [`ValidatorVote::verify_signature`](crate::solana_consensus::ValidatorVote::verify_signature)
/// is called on it, the **real transaction** is re-parsed and re-verified (and
/// cross-checked to vote exactly the recorded `(slot, bank_hash)` for the
/// recorded vote account), so the super-majority tally runs over genuine
/// mainnet vote transactions.
pub fn ingest_vote_transaction(tx_bytes: &[u8]) -> Result<ValidatorVote, WireError> {
    let v = parse_verified_vote_tx(tx_bytes)?;
    Ok(ValidatorVote {
        vote_pubkey: v.vote_account,
        slot: v.voted_slot,
        bank_hash: v.voted_bank_hash,
        // Unused on the witness path; verification re-derives from the tx.
        signature: [0u8; 64],
        tx_witness: Some(VoteTxWitness {
            tx_bytes: tx_bytes.to_vec(),
        }),
    })
}

/// Verify a vote-transaction witness binds exactly `(vote_account, slot,
/// bank_hash)`. Called by
/// [`ValidatorVote::verify_signature`](crate::solana_consensus::ValidatorVote::verify_signature)
/// when a [`VoteTxWitness`] is present: it re-parses + re-verifies the real
/// transaction and confirms it votes exactly the claimed tuple.
pub fn witness_binds(
    witness: &VoteTxWitness,
    vote_account: &[u8; 32],
    slot: u64,
    bank_hash: &[u8; 32],
) -> bool {
    match parse_verified_vote_tx(&witness.tx_bytes) {
        Ok(v) => {
            &v.vote_account == vote_account
                && v.voted_slot == slot
                && &v.voted_bank_hash == bank_hash
        }
        Err(_) => false,
    }
}

// ============================================================================
// (2) Real accounts-hash format (16-ary fan-out over blake3 account hashes)
// ============================================================================

/// Solana's accounts-hash Merkle fan-out: interior nodes hash up to 16 children.
pub const MERKLE_FANOUT: usize = 16;

/// The real per-account hash Solana commits in its accounts hash:
/// `blake3(lamports_le ‖ rent_epoch_le ‖ data ‖ [executable] ‖ owner ‖ pubkey)`.
///
/// A zero-lamport account hashes to the all-zero default (Solana treats it as
/// absent). This matches Agave's `AccountsDb::hash_account_data`.
pub fn solana_account_hash(
    lamports: u64,
    owner: &[u8; 32],
    executable: bool,
    rent_epoch: u64,
    data: &[u8],
    pubkey: &[u8; 32],
) -> [u8; 32] {
    if lamports == 0 {
        return [0u8; 32];
    }
    let mut h = Blake3::new();
    h.update(&lamports.to_le_bytes());
    h.update(&rent_epoch.to_le_bytes());
    h.update(data);
    h.update(&[executable as u8]);
    h.update(owner);
    h.update(pubkey);
    *h.finalize().as_bytes()
}

/// Hash up to [`MERKLE_FANOUT`] children into an interior node:
/// `sha256(child0 ‖ child1 ‖ …)`. Matches Agave's `compute_merkle_root` node
/// reduction (`solana_sha256_hasher::hashv` over the concatenated child hashes).
pub fn accounts_merkle_node(children: &[[u8; 32]]) -> [u8; 32] {
    let mut h = Sha256::new();
    for c in children {
        h.update(c);
    }
    h.finalize().into()
}

/// Compute the 16-ary accounts-hash Merkle root over `leaves` (the per-account
/// hashes, which Solana sorts by pubkey before hashing). The caller supplies the
/// leaves already in their committed order. An empty leaf set roots to the
/// all-zero default.
pub fn compute_accounts_merkle_root(leaves: &[[u8; 32]]) -> [u8; 32] {
    if leaves.is_empty() {
        return [0u8; 32];
    }
    let mut level: Vec<[u8; 32]> = leaves.to_vec();
    while level.len() > 1 {
        level = level
            .chunks(MERKLE_FANOUT)
            .map(accounts_merkle_node)
            .collect();
    }
    level[0]
}

/// One level of a 16-ary inclusion proof: the running node sits at
/// `position` within a chunk of `siblings.len() + 1 ≤ 16` children; the other
/// children are `siblings`, given in their committed order (the running node is
/// inserted at `position`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MerkleLevel {
    /// The running node's index within its chunk (`0..=siblings.len()`).
    pub position: u8,
    /// The other children of the chunk, in order (length `≤ 15`).
    pub siblings: Vec<[u8; 32]>,
}

/// A 16-ary fan-out inclusion proof from a per-account leaf up to the accounts
/// hash root.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AccountsInclusionProof16 {
    /// The levels from the leaf's chunk up to (and including) the root chunk.
    pub levels: Vec<MerkleLevel>,
}

/// Fold a 16-ary inclusion proof from `leaf` and check it reaches `root`.
///
/// At each level the chunk is reconstructed by inserting the running node at
/// `position` among `siblings` (preserving committed order), then hashed with
/// [`accounts_merkle_node`]. A chunk wider than [`MERKLE_FANOUT`] is rejected.
pub fn fold_account_inclusion_16ary(
    leaf: [u8; 32],
    proof: &AccountsInclusionProof16,
) -> Option<[u8; 32]> {
    let mut acc = leaf;
    for level in &proof.levels {
        let chunk_len = level.siblings.len() + 1;
        if chunk_len > MERKLE_FANOUT {
            return None;
        }
        let pos = level.position as usize;
        if pos >= chunk_len {
            return None;
        }
        let mut chunk: Vec<[u8; 32]> = Vec::with_capacity(chunk_len);
        chunk.extend_from_slice(&level.siblings[..pos]);
        chunk.push(acc);
        chunk.extend_from_slice(&level.siblings[pos..]);
        acc = accounts_merkle_node(&chunk);
    }
    Some(acc)
}

/// Verify that `leaf` (a per-account hash) is included in the accounts-hash
/// `root` via the 16-ary `proof`.
pub fn verify_account_inclusion_16ary(
    leaf: [u8; 32],
    proof: &AccountsInclusionProof16,
    root: &[u8; 32],
) -> bool {
    matches!(fold_account_inclusion_16ary(leaf, proof), Some(r) if &r == root)
}

// ============================================================================
// (2) Adapter-defined lock-record account-data layout
// ============================================================================

/// The number of bytes of the adapter-defined vault-lock record.
pub const LOCK_RECORD_LEN: usize = 32 + 32 + 8;

/// Encode the lock record into the vault account's `data`:
/// `lock_id(32) ‖ recipient(32) ‖ amount_le(8)`.
///
/// This layout is **adapter-defined** (the lock program's account schema is a
/// deploy-time choice). The *hashing* of the account into the accounts hash is
/// mainnet-faithful; only this on-account encoding is the bridge's convention.
pub fn encode_lock_record(lock_id: &[u8; 32], recipient: &CellId, amount: u64) -> Vec<u8> {
    let mut d = Vec::with_capacity(LOCK_RECORD_LEN);
    d.extend_from_slice(lock_id);
    d.extend_from_slice(recipient.as_bytes());
    d.extend_from_slice(&amount.to_le_bytes());
    d
}

/// Decode a vault account's `data` into `(lock_id, recipient, amount)`.
/// Returns `None` if the data is not exactly the lock-record layout.
pub fn decode_lock_record(data: &[u8]) -> Option<([u8; 32], CellId, u64)> {
    if data.len() != LOCK_RECORD_LEN {
        return None;
    }
    let mut lock_id = [0u8; 32];
    lock_id.copy_from_slice(&data[0..32]);
    let mut rec = [0u8; 32];
    rec.copy_from_slice(&data[32..64]);
    let mut amt = [0u8; 8];
    amt.copy_from_slice(&data[64..72]);
    Some((lock_id, CellId::from_bytes(rec), u64::from_le_bytes(amt)))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::solana_consensus::tally_votes;
    use ed25519_dalek::{Signer, SigningKey};
    use solana_vote_interface::instruction::VoteInstruction;
    use solana_vote_interface::state::{TowerSync, Vote};

    fn cid(b: u8) -> CellId {
        CellId::from_bytes([b; 32])
    }

    fn sk(seed: u8) -> SigningKey {
        SigningKey::from_bytes(&[seed; 32])
    }

    // ---- compact-u16 framing ------------------------------------------------

    fn put_compact_u16(out: &mut Vec<u8>, mut v: u16) {
        loop {
            let mut byte = (v & 0x7f) as u8;
            v >>= 7;
            if v != 0 {
                byte |= 0x80;
            }
            out.push(byte);
            if v == 0 {
                break;
            }
        }
    }

    /// Build a real legacy vote `Transaction`'s bytes for a given vote
    /// instruction, vote account, and authorized-voter signing key. The signer
    /// is the fee payer (account_keys[0]) and the vote authority — exactly how a
    /// validator's authorized voter submits a vote.
    ///
    /// Account-key layout (for the Vote/TowerSync variants we test):
    /// `[authority(signer), vote_account, slot_hashes, clock, vote_program]`.
    fn build_vote_tx(
        authority: &SigningKey,
        vote_account: &[u8; 32],
        vi: &VoteInstruction,
    ) -> Vec<u8> {
        let auth_pk = authority.verifying_key().to_bytes();
        let slot_hashes = [0x10u8; 32];
        let clock = [0x11u8; 32];
        let vote_program = solana_vote_interface::program::id().to_bytes();

        // account_keys[0] = authority (the sole required signer / fee payer).
        let account_keys: Vec<[u8; 32]> =
            vec![auth_pk, *vote_account, slot_hashes, clock, vote_program];

        // Instruction account metas index into account_keys.
        let (metas, prog_idx): (Vec<u8>, u8) = match vi {
            VoteInstruction::Vote(_) | VoteInstruction::VoteSwitch(_, _) => {
                // 0: vote account(1), 1: slot hashes(2), 2: clock(3), 3: authority(0)
                (vec![1, 2, 3, 0], 4)
            }
            _ => {
                // 0: vote account(1), 1: authority(0)
                (vec![1, 0], 4)
            }
        };

        let ix_data = bincode::serialize(vi).expect("serialize vote instruction");

        // ---- build the message bytes ----
        let mut msg = Vec::new();
        // header: 1 required sig, 0 readonly-signed, 2 readonly-unsigned
        // (slot_hashes, clock, vote_program are readonly-unsigned).
        msg.push(1u8); // num_required_signatures
        msg.push(0u8); // num_readonly_signed
        msg.push(3u8); // num_readonly_unsigned (slot_hashes, clock, vote_program)
        put_compact_u16(&mut msg, account_keys.len() as u16);
        for k in &account_keys {
            msg.extend_from_slice(k);
        }
        msg.extend_from_slice(&[0x99u8; 32]); // recent_blockhash
        put_compact_u16(&mut msg, 1); // one instruction
        msg.push(prog_idx); // program_id_index
        put_compact_u16(&mut msg, metas.len() as u16);
        msg.extend_from_slice(&metas);
        put_compact_u16(&mut msg, ix_data.len() as u16);
        msg.extend_from_slice(&ix_data);

        // ---- sign the message + frame the transaction ----
        let sig = authority.sign(&msg).to_bytes();
        let mut tx = Vec::new();
        put_compact_u16(&mut tx, 1); // one signature
        tx.extend_from_slice(&sig);
        tx.extend_from_slice(&msg);
        tx
    }

    fn tower_sync_vi(slot: u64, bank_hash: [u8; 32]) -> VoteInstruction {
        let ts = TowerSync::from(vec![(slot - 1, 2u32), (slot, 1u32)]);
        let ts = TowerSync {
            hash: solana_hash::Hash::new_from_array(bank_hash),
            ..ts
        };
        VoteInstruction::TowerSync(ts)
    }

    fn vote_vi(slot: u64, bank_hash: [u8; 32]) -> VoteInstruction {
        let v = Vote::new(
            vec![slot - 1, slot],
            solana_hash::Hash::new_from_array(bank_hash),
        );
        VoteInstruction::Vote(v)
    }

    // ---- (1) real vote-transaction ingestion --------------------------------

    #[test]
    fn real_tower_sync_tx_parses_and_verifies() {
        let auth = sk(7);
        let vote_account = [0x42u8; 32];
        let bank = [0xABu8; 32];
        let slot = 222_333u64;
        let tx = build_vote_tx(&auth, &vote_account, &tower_sync_vi(slot, bank));

        let v = parse_verified_vote_tx(&tx).expect("genuine vote tx verifies");
        assert_eq!(v.vote_account, vote_account);
        assert_eq!(v.authorized_voter, auth.verifying_key().to_bytes());
        assert_eq!(v.voted_slot, slot);
        assert_eq!(v.voted_bank_hash, bank);
    }

    #[test]
    fn real_vote_variant_tx_parses_and_verifies() {
        let auth = sk(8);
        let vote_account = [0x43u8; 32];
        let bank = [0xCDu8; 32];
        let slot = 9_001u64;
        let tx = build_vote_tx(&auth, &vote_account, &vote_vi(slot, bank));

        let v = parse_verified_vote_tx(&tx).expect("genuine Vote tx verifies");
        assert_eq!(v.vote_account, vote_account);
        assert_eq!(v.voted_slot, slot);
        assert_eq!(v.voted_bank_hash, bank);
    }

    #[test]
    fn tampered_vote_tx_signature_refused() {
        let auth = sk(7);
        let vote_account = [0x42u8; 32];
        let bank = [0xABu8; 32];
        let mut tx = build_vote_tx(&auth, &vote_account, &tower_sync_vi(100, bank));
        // Corrupt one byte of the signature (it leads the buffer after the
        // 1-byte sig count).
        tx[5] ^= 0xFF;
        assert_eq!(
            parse_verified_vote_tx(&tx),
            Err(WireError::SignatureInvalid)
        );
    }

    #[test]
    fn tampered_vote_tx_message_refused() {
        let auth = sk(7);
        let vote_account = [0x42u8; 32];
        let bank = [0xABu8; 32];
        let mut tx = build_vote_tx(&auth, &vote_account, &tower_sync_vi(100, bank));
        // Flip a byte deep in the message (the recent_blockhash region) — the
        // signature no longer matches the message.
        let n = tx.len();
        tx[n - 10] ^= 0xFF;
        assert_eq!(
            parse_verified_vote_tx(&tx),
            Err(WireError::SignatureInvalid)
        );
    }

    #[test]
    fn truncated_tx_refused() {
        let auth = sk(7);
        let tx = build_vote_tx(&auth, &[0x42u8; 32], &tower_sync_vi(100, [0xABu8; 32]));
        assert_eq!(
            parse_verified_vote_tx(&tx[..tx.len() - 5]),
            Err(WireError::Truncated)
        );
    }

    #[test]
    fn ingested_vote_feeds_supermajority_over_real_txs() {
        use crate::solana_consensus::EpochStakeTable;

        let bank = [0x77u8; 32];
        let slot = 555_000u64;
        let (a1, a2, a3) = (sk(11), sk(12), sk(13));
        let (va1, va2, va3) = ([0xA1u8; 32], [0xA2u8; 32], [0xA3u8; 32]);

        // Stake keyed by VOTE ACCOUNT (the real Solana weighting).
        let stake = EpochStakeTable::from_entries(9, [(va1, 400u64), (va2, 400), (va3, 200)]);

        // Two big validators submit REAL signed vote transactions for the slot.
        let tx1 = build_vote_tx(&a1, &va1, &tower_sync_vi(slot, bank));
        let tx2 = build_vote_tx(&a2, &va2, &vote_vi(slot, bank));
        let votes = vec![
            ingest_vote_transaction(&tx1).expect("ingest tx1"),
            ingest_vote_transaction(&tx2).expect("ingest tx2"),
        ];

        // The pass-1 super-majority tally runs over the REAL vote txs (it calls
        // verify_signature, which re-verifies each transaction).
        let tally = tally_votes(&stake, slot, &bank, &votes);
        assert_eq!(tally.voted_stake, 800);
        assert_eq!(tally.total_stake, 1000);
        assert_eq!(tally.valid_voters, 2);
        assert!(tally.is_supermajority());
    }

    #[test]
    fn ingested_vote_with_corrupt_witness_contributes_no_stake() {
        use crate::solana_consensus::EpochStakeTable;

        let bank = [0x77u8; 32];
        let slot = 555_000u64;
        let a1 = sk(11);
        let va1 = [0xA1u8; 32];
        let stake = EpochStakeTable::from_entries(9, [(va1, 800u64), ([0xA2u8; 32], 200)]);

        let mut v = ingest_vote_transaction(&build_vote_tx(&a1, &va1, &tower_sync_vi(slot, bank)))
            .expect("ingest");
        // Corrupt the witnessed transaction bytes: verification now fails, so
        // the vote contributes ZERO stake even though the fields claim 800.
        if let Some(w) = v.tx_witness.as_mut() {
            w.tx_bytes[5] ^= 0xFF;
        }
        let tally = tally_votes(&stake, slot, &bank, &[v]);
        assert_eq!(tally.voted_stake, 0);
        assert!(!tally.is_supermajority());
    }

    #[test]
    fn witness_binds_rejects_wrong_tuple() {
        let a1 = sk(11);
        let va1 = [0xA1u8; 32];
        let bank = [0x77u8; 32];
        let slot = 555_000u64;
        let tx = build_vote_tx(&a1, &va1, &tower_sync_vi(slot, bank));
        let w = VoteTxWitness { tx_bytes: tx };
        assert!(witness_binds(&w, &va1, slot, &bank));
        assert!(!witness_binds(&w, &[0xFFu8; 32], slot, &bank)); // wrong account
        assert!(!witness_binds(&w, &va1, slot + 1, &bank)); // wrong slot
        assert!(!witness_binds(&w, &va1, slot, &[0u8; 32])); // wrong bank hash
    }

    // ---- (2) real 16-ary accounts-hash format -------------------------------

    /// Build a 16-ary inclusion proof for the leaf at `index` over `leaves`,
    /// returning the root + proof (the verification mirror).
    fn build_16ary_proof(
        leaves: &[[u8; 32]],
        index: usize,
    ) -> ([u8; 32], AccountsInclusionProof16) {
        let mut levels = Vec::new();
        let mut level: Vec<[u8; 32]> = leaves.to_vec();
        let mut idx = index;
        while level.len() > 1 {
            let chunk_start = (idx / MERKLE_FANOUT) * MERKLE_FANOUT;
            let chunk_end = (chunk_start + MERKLE_FANOUT).min(level.len());
            let pos = idx - chunk_start;
            let mut siblings = Vec::new();
            for (j, h) in level[chunk_start..chunk_end].iter().enumerate() {
                if j != pos {
                    siblings.push(*h);
                }
            }
            levels.push(MerkleLevel {
                position: pos as u8,
                siblings,
            });
            // Ascend.
            level = level
                .chunks(MERKLE_FANOUT)
                .map(accounts_merkle_node)
                .collect();
            idx /= MERKLE_FANOUT;
        }
        (level[0], AccountsInclusionProof16 { levels })
    }

    fn account_leaves(n: usize) -> Vec<[u8; 32]> {
        (0..n)
            .map(|i| {
                solana_account_hash(
                    1000 + i as u64,
                    &[i as u8; 32],
                    false,
                    42,
                    &[i as u8, 0xAA, 0xBB],
                    &[(i as u8).wrapping_mul(3); 32],
                )
            })
            .collect()
    }

    #[test]
    fn account_hash_zero_lamports_is_default() {
        let h = solana_account_hash(0, &[1u8; 32], false, 7, b"data", &[2u8; 32]);
        assert_eq!(h, [0u8; 32]);
    }

    #[test]
    fn account_hash_changes_with_each_field() {
        let base = solana_account_hash(100, &[1u8; 32], false, 7, b"data", &[2u8; 32]);
        assert_ne!(
            base,
            solana_account_hash(101, &[1u8; 32], false, 7, b"data", &[2u8; 32])
        );
        assert_ne!(
            base,
            solana_account_hash(100, &[9u8; 32], false, 7, b"data", &[2u8; 32])
        );
        assert_ne!(
            base,
            solana_account_hash(100, &[1u8; 32], true, 7, b"data", &[2u8; 32])
        );
        assert_ne!(
            base,
            solana_account_hash(100, &[1u8; 32], false, 8, b"data", &[2u8; 32])
        );
        assert_ne!(
            base,
            solana_account_hash(100, &[1u8; 32], false, 7, b"datb", &[2u8; 32])
        );
        assert_ne!(
            base,
            solana_account_hash(100, &[1u8; 32], false, 7, b"data", &[3u8; 32])
        );
    }

    #[test]
    fn inclusion_16ary_round_trips_small() {
        // 5 leaves: a single partial chunk (one level).
        let leaves = account_leaves(5);
        for i in 0..5 {
            let (root, proof) = build_16ary_proof(&leaves, i);
            assert_eq!(root, compute_accounts_merkle_root(&leaves));
            assert!(verify_account_inclusion_16ary(leaves[i], &proof, &root));
        }
    }

    #[test]
    fn inclusion_16ary_round_trips_multilevel() {
        // 40 leaves: 3 chunks at level 0 (16,16,8) → 1 chunk at level 1 → root.
        let leaves = account_leaves(40);
        let root = compute_accounts_merkle_root(&leaves);
        for i in [0usize, 1, 15, 16, 17, 31, 32, 39] {
            let (r, proof) = build_16ary_proof(&leaves, i);
            assert_eq!(r, root);
            assert_eq!(proof.levels.len(), 2);
            assert!(verify_account_inclusion_16ary(leaves[i], &proof, &root));
        }
    }

    #[test]
    fn inclusion_16ary_tamper_refused() {
        let leaves = account_leaves(40);
        let (root, proof) = build_16ary_proof(&leaves, 17);
        // Wrong leaf.
        assert!(!verify_account_inclusion_16ary(leaves[18], &proof, &root));
        // Tampered root.
        let mut bad = root;
        bad[0] ^= 0xFF;
        assert!(!verify_account_inclusion_16ary(leaves[17], &proof, &bad));
        // Tampered sibling.
        let mut bad_proof = proof.clone();
        bad_proof.levels[0].siblings[0][0] ^= 0xFF;
        assert!(!verify_account_inclusion_16ary(
            leaves[17], &bad_proof, &root
        ));
    }

    #[test]
    fn inclusion_16ary_overwide_chunk_refused() {
        // A malicious proof with a chunk of 17 children must be rejected.
        let proof = AccountsInclusionProof16 {
            levels: vec![MerkleLevel {
                position: 0,
                siblings: vec![[0u8; 32]; MERKLE_FANOUT], // 16 siblings + self = 17
            }],
        };
        assert_eq!(fold_account_inclusion_16ary([1u8; 32], &proof), None);
    }

    #[test]
    fn lock_record_round_trips() {
        let lock_id = [0x33u8; 32];
        let recipient = cid(9);
        let data = encode_lock_record(&lock_id, &recipient, 4242);
        assert_eq!(data.len(), LOCK_RECORD_LEN);
        let (lid, rec, amt) = decode_lock_record(&data).expect("decode");
        assert_eq!(lid, lock_id);
        assert_eq!(rec, recipient);
        assert_eq!(amt, 4242);
        assert!(decode_lock_record(&data[..50]).is_none());
    }
}
