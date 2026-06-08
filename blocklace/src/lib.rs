//! # dregg-blocklace
//!
//! # Trust Model
//!
//! This crate operates at the **CONSENSUS-TRUSTLESS** trust level.
//!
//! - **Soundness**: Finality is verified by ALL participants. Once a block reaches
//!   finality (via the constitution's supermajority rule), it cannot be reverted without
//!   violating the BFT assumption (>1/3 Byzantine). The DAG structure is self-validating:
//!   hash links make it impossible to rewrite history without detection.
//! - **Assumptions**: Honest supermajority (2f+1 of 3f+1 nodes). Network eventually
//!   delivers messages (partial synchrony). Block creators sign their blocks (Ed25519).
//!   BLAKE3 is collision-resistant (for content addressing).
//! - **Verifiable by**: Every participant independently. Any node can verify:
//!   - Block integrity (hash matches content)
//!   - Block authenticity (signature matches creator)
//!   - Causal ordering (all predecessors exist and are valid)
//!   - Finality (supermajority acknowledgment per the constitution)
//!
//! ## Trust Boundaries
//! - The blocklace does NOT verify payload semantics (that is the executor's job)
//! - The blocklace DOES guarantee total ordering and finality
//! - Dissemination is best-effort (liveness) but does not affect safety
//!
//! ## Key Invariants
//! 1. A block's ID is a deterministic function of its content (content-addressed)
//! 2. Blocks are inserted only if all predecessors are present (causal closure)
//! 3. Finalized blocks form an immutable prefix of the DAG
//! 4. The topological order is a valid linearization of the causal DAG
//!
//! Blocklace: a DAG-based data structure for Byzantine fault-tolerant consensus.
//!
//! This crate implements:
//! - Block creation and validation (content-addressed, hash-linked DAG)
//! - Cordial dissemination protocol (efficient gossip-based block propagation)
//!
//! ## Cordial Dissemination
//!
//! The key principle from the Cordial Miners paper: "send to others blocks you
//! know and think they need." Block pointers encode what each node knows,
//! enabling efficient catch-up without explicit protocol messages.
//!
//! ## Architecture
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────────────────┐
//! │  Blocklace (DAG of blocks with causal links)                        │
//! │     ↓                                                               │
//! │  Disseminator (cordial dissemination engine)                         │
//! │     ├── blocks_to_send(peer) → causally-closed delta                │
//! │     ├── received_from(peer, block) → update peer knowledge          │
//! │     └── handle_message(msg) → process Push/Pull/PullResponse        │
//! └─────────────────────────────────────────────────────────────────────┘
//! ```

pub mod addressing;
pub mod constitution;
pub mod cross_reference;
pub mod delegation;
pub mod dissemination;
pub mod dregg_bridge;
pub mod finality;
pub mod ordering;

use std::collections::{HashMap, HashSet, VecDeque};

use ed25519_dalek::{Signer, SigningKey, Verifier, VerifyingKey};
use serde::{Deserialize, Serialize};

/// A block identifier: the BLAKE3 hash of the block's canonical encoding.
pub type BlockId = [u8; 32];

/// A node identifier: the public key (32 bytes) of the block creator.
pub type NodeKey = [u8; 32];

/// A block in the blocklace DAG.
///
/// Each block references its predecessors (causal dependencies) and is signed
/// by its creator. The block ID is the BLAKE3 hash of (creator || sequence ||
/// predecessors || payload).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Block {
    /// The creator's public key.
    pub creator: NodeKey,
    /// Monotonic sequence number for this creator (0-indexed).
    pub sequence: u64,
    /// Block IDs this block depends on (causal predecessors).
    pub predecessors: Vec<BlockId>,
    /// Application-level payload.
    pub payload: Vec<u8>,
    /// Signature over the block hash by the creator (64 bytes, Ed25519).
    /// Set to zeros for unsigned/test blocks.
    #[serde(with = "serde_sig64")]
    pub signature: [u8; 64],
}

/// Serde helper for 64-byte arrays (Ed25519 signatures).
/// Serde only implements Serialize/Deserialize for arrays up to [T; 32].
pub(crate) mod serde_sig64 {
    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    pub fn serialize<S: Serializer>(bytes: &[u8; 64], serializer: S) -> Result<S::Ok, S::Error> {
        bytes.as_ref().serialize(serializer)
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(deserializer: D) -> Result<[u8; 64], D::Error> {
        let v: Vec<u8> = Deserialize::deserialize(deserializer)?;
        v.try_into()
            .map_err(|_| serde::de::Error::custom("expected 64 bytes for signature"))
    }
}

impl Block {
    /// Compute the canonical block ID (BLAKE3 hash of the block's content).
    ///
    /// The hash covers: creator, sequence, predecessors (sorted), and payload.
    /// It does NOT cover the signature (so the signature can be verified against
    /// the hash without circular dependency).
    pub fn id(&self) -> BlockId {
        let mut hasher = blake3::Hasher::new_derive_key("dregg-blocklace-block-v1");
        hasher.update(&self.creator);
        hasher.update(&self.sequence.to_le_bytes());
        hasher.update(&(self.predecessors.len() as u32).to_le_bytes());
        let mut sorted_preds = self.predecessors.clone();
        sorted_preds.sort();
        for pred in &sorted_preds {
            hasher.update(pred);
        }
        hasher.update(&(self.payload.len() as u32).to_le_bytes());
        hasher.update(&self.payload);
        *hasher.finalize().as_bytes()
    }

    /// Create a new unsigned block.
    ///
    /// The signature is left zeroed. Such a block is **rejected by
    /// [`Blocklace::insert`]** (feed-integrity requires an authentic Ed25519
    /// signature over `id()`); use [`Block::new_signed`] / [`Block::sign`] for a
    /// block that the strand-integrity write path will accept. `new` remains for
    /// constructing the unsigned skeleton prior to signing and for the unsigned
    /// *ordering projection* (`Blocklace::insert_unverified`), which does not
    /// touch the wire.
    pub fn new(
        creator: NodeKey,
        sequence: u64,
        predecessors: Vec<BlockId>,
        payload: Vec<u8>,
    ) -> Self {
        Self {
            creator,
            sequence,
            predecessors,
            payload,
            signature: [0u8; 64],
        }
    }

    /// Create and Ed25519-sign a block with the given signing key.
    ///
    /// The `creator` is the signing key's public key, and the signature covers
    /// the block's canonical `id()` (BLAKE3 of creator/seq/preds/payload). The
    /// resulting block passes [`Block::verify_signature`] and is accepted by the
    /// feed-integrity [`Blocklace::insert`].
    pub fn new_signed(
        signing_key: &SigningKey,
        sequence: u64,
        predecessors: Vec<BlockId>,
        payload: Vec<u8>,
    ) -> Self {
        let creator = signing_key.verifying_key().to_bytes();
        let mut block = Self::new(creator, sequence, predecessors, payload);
        block.sign(signing_key);
        block
    }

    /// Sign (or re-sign) this block in place with `signing_key`.
    ///
    /// Sets `creator` to the key's public key and `signature` to the Ed25519
    /// signature over `id()`. Returns the signature for convenience.
    pub fn sign(&mut self, signing_key: &SigningKey) -> [u8; 64] {
        self.creator = signing_key.verifying_key().to_bytes();
        let id = self.id();
        let sig = signing_key.sign(&id);
        self.signature = sig.to_bytes();
        self.signature
    }

    /// Whether this block carries a (syntactically) non-zero signature.
    ///
    /// A zeroed signature is the unsigned sentinel produced by [`Block::new`];
    /// it can never be a valid Ed25519 signature, so it is rejected on insert.
    pub fn is_signed(&self) -> bool {
        self.signature != [0u8; 64]
    }

    /// Verify this block's Ed25519 signature against its `creator` pubkey.
    ///
    /// Returns `Ok(())` iff `creator` is a valid Ed25519 public key and
    /// `signature` is a valid signature by it over `id()`. Rejects the unsigned
    /// (zero-signature) sentinel, a malformed pubkey, and any forged/mismatched
    /// signature. This is real Ed25519 verification (`ed25519_dalek`), not a
    /// stub — the §8 crypto seam the design doc calls for, discharged here.
    pub fn verify_signature(&self) -> Result<(), InsertError> {
        if !self.is_signed() {
            return Err(InsertError::Unsigned {
                creator: self.creator,
                sequence: self.sequence,
            });
        }
        let vk = VerifyingKey::from_bytes(&self.creator).map_err(|_| InsertError::BadSignature {
            creator: self.creator,
            sequence: self.sequence,
        })?;
        let sig = ed25519_dalek::Signature::from_bytes(&self.signature);
        vk.verify(&self.id(), &sig)
            .map_err(|_| InsertError::BadSignature {
                creator: self.creator,
                sequence: self.sequence,
            })
    }

    /// Serialize the block to bytes for wire transmission.
    ///
    /// Uses postcard's compact binary format.
    pub fn to_bytes(&self) -> Vec<u8> {
        postcard::to_stdvec(self).expect("block serialization should not fail")
    }

    /// Deserialize a block from bytes.
    ///
    /// Returns `None` if the bytes are malformed.
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        postcard::from_bytes(bytes).ok()
    }
}

/// Proof that a creator equivocated: two distinct blocks at the same
/// `(creator, sequence)`.
///
/// The equivocation is *attributable* (both blocks name `creator`) and
/// *detectable* (the pair is retained in the lace, not overwritten). This is
/// the strand-layer analogue of `finality.rs::EquivocationProof`, and it is the
/// representation `ordering.rs::has_equivocation_in_past` consumes when it
/// scans for two same-creator blocks at one round.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EquivocationProof {
    /// The equivocating creator's public key.
    pub creator: NodeKey,
    /// The sequence number at which the fork occurred.
    pub sequence: u64,
    /// The block already present at `(creator, sequence)`.
    pub existing: BlockId,
    /// The conflicting block presented at the same `(creator, sequence)`.
    pub conflicting: BlockId,
}

/// Why a block could not be inserted as a valid strand extension.
///
/// `insert` is the feed-integrity write path (SSB-style: append-only,
/// Ed25519-signed, monotone-seq, no-equivocation-without-detection). Every
/// rejection is one of these; the previous `Vec<BlockId>` (missing
/// predecessors) is preserved as the [`InsertError::MissingPredecessors`]
/// variant so the dissemination layer can still buffer pending blocks.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InsertError {
    /// Causal closure failed: these predecessor IDs are not yet present.
    MissingPredecessors(Vec<BlockId>),
    /// The block carries no signature (the zeroed sentinel from `Block::new`).
    Unsigned { creator: NodeKey, sequence: u64 },
    /// The block's Ed25519 signature does not verify against `creator`.
    BadSignature { creator: NodeKey, sequence: u64 },
    /// The block's sequence does not extend the creator's known chain
    /// (it regresses to or below the creator's current tip sequence).
    SeqRegression {
        creator: NodeKey,
        /// The sequence the block claims.
        attempted: u64,
        /// The creator's current tip sequence (the block must exceed it).
        tip_sequence: u64,
    },
    /// A second, different block was presented at an existing `(creator,
    /// sequence)`. The block is retained as detectable evidence (NOT silently
    /// overwriting the tip); the proof attributes the fork.
    Equivocation(EquivocationProof),
}

impl InsertError {
    /// If this error is a closure failure, the missing predecessor IDs.
    ///
    /// Lets the dissemination layer buffer a block whose predecessors have not
    /// yet arrived, exactly as the old `Err(Vec<BlockId>)` contract did.
    pub fn missing_predecessors(&self) -> Option<&[BlockId]> {
        match self {
            InsertError::MissingPredecessors(m) => Some(m),
            _ => None,
        }
    }
}

impl std::fmt::Display for InsertError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InsertError::MissingPredecessors(m) => {
                write!(f, "missing {} predecessor(s)", m.len())
            }
            InsertError::Unsigned { sequence, .. } => {
                write!(f, "block at seq {sequence} is unsigned")
            }
            InsertError::BadSignature { sequence, .. } => {
                write!(f, "block at seq {sequence} has an invalid signature")
            }
            InsertError::SeqRegression {
                attempted,
                tip_sequence,
                ..
            } => write!(
                f,
                "seq {attempted} does not extend tip seq {tip_sequence}"
            ),
            InsertError::Equivocation(p) => write!(
                f,
                "equivocation by creator at seq {} (existing vs conflicting block)",
                p.sequence
            ),
        }
    }
}

impl std::error::Error for InsertError {}

/// The local blocklace: stores all known blocks and their relationships.
#[derive(Clone, Debug, Default)]
pub struct Blocklace {
    /// All blocks by their ID.
    pub(crate) blocks: HashMap<BlockId, Block>,
    /// Forward edges: block_id -> set of blocks that reference it as a predecessor.
    successors: HashMap<BlockId, HashSet<BlockId>>,
    /// The latest block ID per creator (tip of each creator's chain).
    tips: HashMap<NodeKey, BlockId>,
    /// The highest sequence number we have accepted per creator (the strand
    /// length). A new block must strictly exceed this to be a valid extension.
    tip_sequence: HashMap<NodeKey, u64>,
    /// Creators caught equivocating (a fork was presented). Once detected, the
    /// creator's tip is withdrawn — there is no single honest feed head.
    equivocators: HashSet<NodeKey>,
    /// Detected equivocation proofs (attributable fork evidence).
    equivocation_proofs: Vec<EquivocationProof>,
    /// Blocks with no successors (the current DAG frontier).
    frontier: HashSet<BlockId>,
}

impl Blocklace {
    /// Create a new empty blocklace.
    pub fn new() -> Self {
        Self::default()
    }

    /// Insert a block into the blocklace, enforcing **feed integrity**.
    ///
    /// This is the strand-integrity write path. A block is accepted only if it
    /// is a valid extension of its creator's append-only, Ed25519-signed,
    /// monotone-sequence feed (a Secure-Scuttlebutt strand). Specifically:
    ///
    /// 1. **Authenticity** — the block's Ed25519 signature must verify against
    ///    its `creator` pubkey (the unsigned sentinel and any forged/mismatched
    ///    signature are rejected: [`InsertError::Unsigned`] /
    ///    [`InsertError::BadSignature`]).
    /// 2. **Causal closure** — all predecessors must already be present
    ///    ([`InsertError::MissingPredecessors`]).
    /// 3. **Sequence monotonicity** — the block's `sequence` must strictly
    ///    exceed the creator's current tip sequence; it may not regress or
    ///    repeat ([`InsertError::SeqRegression`]).
    /// 4. **No silent equivocation** — if a *different* block already exists at
    ///    this `(creator, sequence)`, the new block is **retained as detectable
    ///    evidence** (not used to overwrite the tip), an [`EquivocationProof`]
    ///    is recorded, the creator's tip is withdrawn, and
    ///    [`InsertError::Equivocation`] is returned. The fork is never lost.
    ///
    /// Returns `Ok(block_id)` if the block was inserted (or already exists).
    pub fn insert(&mut self, block: Block) -> Result<BlockId, InsertError> {
        let block_id = block.id();

        // Already have it (idempotent).
        if self.blocks.contains_key(&block_id) {
            return Ok(block_id);
        }

        // (1) Authenticity: real Ed25519 verification against `creator`.
        block.verify_signature()?;

        // (2) Causal closure: all predecessors must be present.
        let missing: Vec<BlockId> = block
            .predecessors
            .iter()
            .filter(|p| !self.blocks.contains_key(*p))
            .copied()
            .collect();
        if !missing.is_empty() {
            return Err(InsertError::MissingPredecessors(missing));
        }

        // (4) Equivocation: a distinct block already present at this
        // (creator, sequence) is a fork. Scan the creator's stored blocks for a
        // same-sequence, different-id block. (Same-creator blocks are sparse;
        // this is the strand-level dual of `ordering.rs::has_equivocation_in_past`,
        // which groups same-creator blocks by round and flags `len > 1`.)
        if let Some(existing_id) = self.find_conflict(&block, block_id) {
            // Retain the conflicting block as DETECTABLE EVIDENCE — do NOT
            // overwrite the tip (the old bug silently replaced tips[creator]).
            self.store_block(block_id, &block);
            self.blocks.insert(block_id, block.clone());
            // Withdraw the creator's honest feed head: there is no single tip.
            self.equivocators.insert(block.creator);
            self.tips.remove(&block.creator);
            let proof = EquivocationProof {
                creator: block.creator,
                sequence: block.sequence,
                existing: existing_id,
                conflicting: block_id,
            };
            self.equivocation_proofs.push(proof.clone());
            return Err(InsertError::Equivocation(proof));
        }

        // (3) Sequence monotonicity: the block must extend the creator's chain.
        // (Skipped for a creator already known to equivocate — they have no
        // honest tip to extend, but the evidence is still retained above.)
        if !self.equivocators.contains(&block.creator) {
            if let Some(&tip_seq) = self.tip_sequence.get(&block.creator) {
                if block.sequence <= tip_seq {
                    return Err(InsertError::SeqRegression {
                        creator: block.creator,
                        attempted: block.sequence,
                        tip_sequence: tip_seq,
                    });
                }
            }
        }

        // All checks passed: link, record the tip, and store.
        self.store_block(block_id, &block);
        if !self.equivocators.contains(&block.creator) {
            self.tips.insert(block.creator, block_id);
            self.tip_sequence.insert(block.creator, block.sequence);
        }
        self.blocks.insert(block_id, block);

        Ok(block_id)
    }

    /// Insert a block WITHOUT signature/sequence/equivocation enforcement.
    ///
    /// This is the **unsigned ordering projection** path: the node mirrors
    /// already-finalized, already-authenticated blocks (from the live
    /// `finality.rs` lace) into a `lib::Blocklace` purely to run `ordering::tau`
    /// over them. Those mirror blocks are unsigned skeletons by construction
    /// (`node/blocklace_sync.rs` rebuilds them from finality blocks) and carry
    /// no wire authority, so feed-integrity does not apply — only causal closure
    /// does. It does NOT touch the wire and is never the reception path.
    ///
    /// Returns `Err(missing)` if predecessors are absent. Like the old `insert`,
    /// it overwrites the tip — acceptable here because the source lace already
    /// enforced integrity.
    pub fn insert_unverified(&mut self, block: Block) -> Result<BlockId, Vec<BlockId>> {
        let block_id = block.id();
        if self.blocks.contains_key(&block_id) {
            return Ok(block_id);
        }
        let missing: Vec<BlockId> = block
            .predecessors
            .iter()
            .filter(|p| !self.blocks.contains_key(*p))
            .copied()
            .collect();
        if !missing.is_empty() {
            return Err(missing);
        }
        self.store_block(block_id, &block);
        self.tips.insert(block.creator, block_id);
        self.tip_sequence
            .entry(block.creator)
            .and_modify(|s| *s = (*s).max(block.sequence))
            .or_insert(block.sequence);
        self.blocks.insert(block_id, block);
        Ok(block_id)
    }

    /// Wire frontier/successor edges for a newly-accepted block.
    fn store_block(&mut self, block_id: BlockId, block: &Block) {
        for pred in &block.predecessors {
            self.frontier.remove(pred);
            self.successors.entry(*pred).or_default().insert(block_id);
        }
        self.frontier.insert(block_id);
        self.successors.entry(block_id).or_default();
    }

    /// Find a stored block by the same creator at the same sequence with a
    /// different id (the fork witness). Returns the existing block's id.
    fn find_conflict(&self, block: &Block, block_id: BlockId) -> Option<BlockId> {
        self.blocks.iter().find_map(|(id, existing)| {
            if existing.creator == block.creator
                && existing.sequence == block.sequence
                && *id != block_id
            {
                Some(*id)
            } else {
                None
            }
        })
    }

    /// Creators caught equivocating (a fork was detected on insert).
    pub fn equivocators(&self) -> &HashSet<NodeKey> {
        &self.equivocators
    }

    /// All recorded equivocation proofs (attributable, detectable fork evidence).
    pub fn equivocation_proofs(&self) -> &[EquivocationProof] {
        &self.equivocation_proofs
    }

    /// The highest accepted sequence number for a creator (its strand length).
    pub fn tip_sequence_for(&self, creator: &NodeKey) -> Option<u64> {
        self.tip_sequence.get(creator).copied()
    }

    /// Check if a block exists in the blocklace.
    pub fn contains(&self, block_id: &BlockId) -> bool {
        self.blocks.contains_key(block_id)
    }

    /// Get a block by its ID.
    pub fn get(&self, block_id: &BlockId) -> Option<&Block> {
        self.blocks.get(block_id)
    }

    /// Get the current frontier (blocks with no successors).
    pub fn frontier(&self) -> &HashSet<BlockId> {
        &self.frontier
    }

    /// Get the tip (latest block) for a given creator.
    pub fn tip_for(&self, creator: &NodeKey) -> Option<&BlockId> {
        self.tips.get(creator)
    }

    /// Get all tips (latest block per creator).
    pub fn tips(&self) -> &HashMap<NodeKey, BlockId> {
        &self.tips
    }

    /// Number of blocks in the blocklace.
    pub fn len(&self) -> usize {
        self.blocks.len()
    }

    /// Whether the blocklace is empty.
    pub fn is_empty(&self) -> bool {
        self.blocks.is_empty()
    }

    /// Get all block IDs.
    pub fn block_ids(&self) -> HashSet<BlockId> {
        self.blocks.keys().copied().collect()
    }

    /// Get the causal past (all ancestors) of a block, inclusive of the block itself.
    pub fn causal_past(&self, block_id: &BlockId) -> HashSet<BlockId> {
        let mut result = HashSet::new();
        let mut queue = VecDeque::new();
        queue.push_back(*block_id);

        while let Some(current) = queue.pop_front() {
            if !result.insert(current) {
                continue;
            }
            if let Some(block) = self.blocks.get(&current) {
                for pred in &block.predecessors {
                    if !result.contains(pred) {
                        queue.push_back(*pred);
                    }
                }
            }
        }

        result
    }

    /// Return blocks in topological order (predecessors before dependents).
    pub fn topological_order(&self) -> Vec<BlockId> {
        let mut in_degree: HashMap<BlockId, usize> = HashMap::new();
        for (id, block) in &self.blocks {
            let pred_count = block
                .predecessors
                .iter()
                .filter(|p| self.blocks.contains_key(*p))
                .count();
            in_degree.insert(*id, pred_count);
        }

        let mut queue: VecDeque<BlockId> = VecDeque::new();
        let mut initial: Vec<BlockId> = in_degree
            .iter()
            .filter(|&(_, &deg)| deg == 0)
            .map(|(&id, _)| id)
            .collect();
        initial.sort();
        queue.extend(initial);

        let mut result = Vec::with_capacity(self.blocks.len());
        while let Some(block_id) = queue.pop_front() {
            result.push(block_id);
            if let Some(succs) = self.successors.get(&block_id) {
                let mut next: Vec<BlockId> = Vec::new();
                for succ in succs {
                    if let Some(deg) = in_degree.get_mut(succ) {
                        *deg -= 1;
                        if *deg == 0 {
                            next.push(*succ);
                        }
                    }
                }
                next.sort();
                queue.extend(next);
            }
        }

        result
    }

    /// Get blocks in topological order, filtered to only include the given set.
    pub fn topological_subset(&self, subset: &HashSet<BlockId>) -> Vec<BlockId> {
        self.topological_order()
            .into_iter()
            .filter(|id| subset.contains(id))
            .collect()
    }
}

#[cfg(test)]
mod finality_tests;

#[cfg(test)]
mod tests {
    use super::*;

    /// A deterministic signing key per creator byte (so `creator` byte ↔ key).
    fn key_for(creator: u8) -> SigningKey {
        SigningKey::from_bytes(&[creator; 32])
    }

    /// A signed block whose `creator` is the pubkey of `key_for(creator)`.
    fn make_block(creator: u8, seq: u64, preds: Vec<BlockId>, payload: &[u8]) -> Block {
        Block::new_signed(&key_for(creator), seq, preds, payload.to_vec())
    }

    #[test]
    fn block_id_deterministic() {
        let b = make_block(1, 0, vec![], b"hello");
        let id1 = b.id();
        let id2 = b.id();
        assert_eq!(id1, id2);
    }

    #[test]
    fn block_id_varies_on_content() {
        let b1 = make_block(1, 0, vec![], b"hello");
        let b2 = make_block(1, 0, vec![], b"world");
        assert_ne!(b1.id(), b2.id());
    }

    #[test]
    fn insert_genesis() {
        let mut lace = Blocklace::new();
        let b = make_block(1, 0, vec![], b"genesis");
        let id = lace.insert(b).unwrap();
        assert!(lace.contains(&id));
        assert_eq!(lace.len(), 1);
        assert!(lace.frontier().contains(&id));
    }

    #[test]
    fn insert_with_predecessor() {
        let mut lace = Blocklace::new();
        let b1 = make_block(1, 0, vec![], b"first");
        let id1 = lace.insert(b1).unwrap();

        let b2 = make_block(1, 1, vec![id1], b"second");
        let id2 = lace.insert(b2).unwrap();

        assert_eq!(lace.len(), 2);
        assert!(!lace.frontier().contains(&id1));
        assert!(lace.frontier().contains(&id2));
    }

    #[test]
    fn insert_missing_predecessor_fails() {
        let mut lace = Blocklace::new();
        let fake_pred = [0xAA; 32];
        let b = make_block(1, 0, vec![fake_pred], b"orphan");
        let err = lace.insert(b).unwrap_err();
        assert_eq!(
            err.missing_predecessors().map(|m| m.to_vec()),
            Some(vec![fake_pred])
        );
    }

    #[test]
    fn causal_past() {
        let mut lace = Blocklace::new();
        let b1 = make_block(1, 0, vec![], b"a");
        let id1 = lace.insert(b1).unwrap();
        let b2 = make_block(2, 0, vec![], b"b");
        let id2 = lace.insert(b2).unwrap();
        let b3 = make_block(1, 1, vec![id1, id2], b"c");
        let id3 = lace.insert(b3).unwrap();

        let past = lace.causal_past(&id3);
        assert!(past.contains(&id1));
        assert!(past.contains(&id2));
        assert!(past.contains(&id3));
        assert_eq!(past.len(), 3);
    }

    #[test]
    fn topological_order_respects_causality() {
        let mut lace = Blocklace::new();
        let b1 = make_block(1, 0, vec![], b"a");
        let id1 = lace.insert(b1).unwrap();
        let b2 = make_block(2, 0, vec![], b"b");
        let id2 = lace.insert(b2).unwrap();
        let b3 = make_block(1, 1, vec![id1, id2], b"c");
        let id3 = lace.insert(b3).unwrap();

        let order = lace.topological_order();
        let pos1 = order.iter().position(|x| *x == id1).unwrap();
        let pos2 = order.iter().position(|x| *x == id2).unwrap();
        let pos3 = order.iter().position(|x| *x == id3).unwrap();
        assert!(pos1 < pos3);
        assert!(pos2 < pos3);
    }

    #[test]
    fn tips_tracking() {
        let mut lace = Blocklace::new();
        let creator = key_for(1).verifying_key().to_bytes();
        let b1 = make_block(1, 0, vec![], b"a");
        let id1 = lace.insert(b1).unwrap();
        assert_eq!(*lace.tip_for(&creator).unwrap(), id1);
        assert_eq!(lace.tip_sequence_for(&creator), Some(0));

        let b2 = make_block(1, 1, vec![id1], b"b");
        let id2 = lace.insert(b2).unwrap();
        assert_eq!(*lace.tip_for(&creator).unwrap(), id2);
        assert_eq!(lace.tip_sequence_for(&creator), Some(1));
    }

    #[test]
    fn duplicate_insert_is_idempotent() {
        let mut lace = Blocklace::new();
        let b = make_block(1, 0, vec![], b"dup");
        let id1 = lace.insert(b.clone()).unwrap();
        let id2 = lace.insert(b).unwrap();
        assert_eq!(id1, id2);
        assert_eq!(lace.len(), 1);
    }

    // ─── Feed-integrity (A1 fix) tests ───────────────────────────────────────

    /// Unsigned blocks (the `Block::new` zero-signature sentinel) are rejected:
    /// the write path requires real Ed25519 authenticity.
    #[test]
    fn unsigned_block_rejected() {
        let mut lace = Blocklace::new();
        let creator = key_for(1).verifying_key().to_bytes();
        let unsigned = Block::new(creator, 0, vec![], b"nosig".to_vec());
        assert!(!unsigned.is_signed());
        match lace.insert(unsigned) {
            Err(InsertError::Unsigned { .. }) => {}
            other => panic!("expected Unsigned rejection, got {other:?}"),
        }
        assert_eq!(lace.len(), 0, "unsigned block must not be stored");
    }

    /// A block whose signature does not verify against `creator` (forged/tampered)
    /// is rejected by real Ed25519 verification.
    #[test]
    fn bad_signature_rejected() {
        let mut lace = Blocklace::new();
        // Sign with key 1, then claim a *different* payload so the signature no
        // longer matches the recomputed id (tamper after signing).
        let mut tampered = make_block(1, 0, vec![], b"original");
        tampered.payload = b"tampered".to_vec(); // id changes, signature stale
        assert!(tampered.is_signed());
        match lace.insert(tampered) {
            Err(InsertError::BadSignature { .. }) => {}
            other => panic!("expected BadSignature rejection, got {other:?}"),
        }

        // Also: a signature by the WRONG key for this creator is rejected.
        let mut wrong_signer = Block::new(
            key_for(1).verifying_key().to_bytes(),
            0,
            vec![],
            b"x".to_vec(),
        );
        let sig = key_for(2).sign(&wrong_signer.id());
        wrong_signer.signature = sig.to_bytes(); // signed by 2, claims creator 1
        match lace.insert(wrong_signer) {
            Err(InsertError::BadSignature { .. }) => {}
            other => panic!("expected BadSignature for wrong signer, got {other:?}"),
        }
        assert_eq!(lace.len(), 0);
    }

    /// A block whose sequence does not extend the creator's chain (regresses to
    /// or below the current tip sequence) is rejected.
    #[test]
    fn seq_regression_rejected() {
        let mut lace = Blocklace::new();
        let creator = key_for(1).verifying_key().to_bytes();

        let g0 = make_block(1, 0, vec![], b"g0");
        let id0 = lace.insert(g0).unwrap();
        let g1 = make_block(1, 5, vec![id0], b"g1"); // jump to seq 5 (allowed: strictly >)
        let id1 = lace.insert(g1).unwrap();
        assert_eq!(lace.tip_sequence_for(&creator), Some(5));

        // A new block at seq 3 (< tip, and no block occupies seq 3) regresses:
        // it does not extend the creator's append-only chain. (A *different*
        // block at an already-occupied seq is an equivocation, tested
        // separately; regression is the un-occupied below-tip case.)
        let stale_lt = make_block(1, 3, vec![id1], b"stale-lt");
        match lace.insert(stale_lt) {
            Err(InsertError::SeqRegression {
                attempted: 3,
                tip_sequence: 5,
                ..
            }) => {}
            other => panic!("expected SeqRegression(3 vs 5), got {other:?}"),
        }

        // A new block at seq 2 (also < tip, unoccupied) likewise regresses.
        let stale_lt2 = make_block(1, 2, vec![id0], b"stale-lt2");
        match lace.insert(stale_lt2) {
            Err(InsertError::SeqRegression {
                attempted: 2,
                tip_sequence: 5,
                ..
            }) => {}
            other => panic!("expected SeqRegression(2 vs 5), got {other:?}"),
        }

        // The honest tip is unchanged and seq 6 still extends fine.
        assert_eq!(*lace.tip_for(&creator).unwrap(), id1);
        let g6 = make_block(1, 6, vec![id1], b"g6");
        assert!(lace.insert(g6).is_ok());
        assert_eq!(lace.tip_sequence_for(&creator), Some(6));
    }

    /// Equivocation (two distinct blocks at the same `(creator, sequence)`) is
    /// DETECTED, not silently lost: the conflicting block is retained as
    /// evidence, an attributable proof is recorded, and the creator's tip is
    /// withdrawn. This is the heart of the A1 fix — the old `insert` silently
    /// overwrote `tips[creator]` and kept both forks as live state.
    #[test]
    fn equivocation_detected_not_lost() {
        let mut lace = Blocklace::new();
        let creator = key_for(9).verifying_key().to_bytes();

        // Shared genesis so both forks are causally closed.
        let g = make_block(1, 0, vec![], b"genesis");
        let gid = lace.insert(g).unwrap();

        // Two distinct seq-1 blocks by creator 9 (a fork).
        let f1 = make_block(9, 1, vec![gid], b"fork-a");
        let f1_id = lace.insert(f1).unwrap();
        assert_eq!(*lace.tip_for(&creator).unwrap(), f1_id);

        let f2 = make_block(9, 1, vec![gid], b"fork-b");
        let f2_id = f2.id();
        let err = lace.insert(f2).unwrap_err();

        // The fork is reported as an attributable, detectable proof.
        match &err {
            InsertError::Equivocation(proof) => {
                assert_eq!(proof.creator, creator);
                assert_eq!(proof.sequence, 1);
                assert_eq!(proof.existing, f1_id);
                assert_eq!(proof.conflicting, f2_id);
            }
            other => panic!("expected Equivocation, got {other:?}"),
        }

        // BOTH forked blocks are retained (evidence is never lost) — this is
        // exactly what `ordering.rs::has_equivocation_in_past` scans for.
        assert!(lace.contains(&f1_id), "first fork retained");
        assert!(lace.contains(&f2_id), "conflicting fork retained as evidence");

        // The creator is flagged and the honest tip is WITHDRAWN (no single
        // live feed head — the old bug left a silently-overwritten tip).
        assert!(lace.equivocators().contains(&creator));
        assert!(lace.tip_for(&creator).is_none(), "tip withdrawn on fork");
        assert_eq!(lace.equivocation_proofs().len(), 1);
    }
}
