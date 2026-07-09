//! Core blocklace data structure: a DAG of signed blocks with equivocation detection.
//!
//! Based on arXiv:2402.08068. The blocklace is a partially-ordered set of signed
//! blocks, where each block contains hash-pointers to its predecessors. Each
//! participant maintains a local view that grows monotonically via CRDT union-merge.

use std::collections::{HashMap, HashSet, VecDeque};

use ed25519_dalek::{Signer, SigningKey, Verifier, VerifyingKey};
use serde::{Deserialize, Serialize};

// ─── Core Types ──────────────────────────────────────────────────────────────

/// A block identity: the blake3 hash of the signed content.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct BlockId(pub [u8; 32]);

impl std::fmt::Debug for BlockId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "BlockId({})",
            self.0[..4]
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect::<String>()
        )
    }
}

impl std::fmt::Display for BlockId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            self.0[..8]
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect::<String>()
        )
    }
}

/// The payload carried by a block.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Payload {
    /// A dregg turn (serialized state transition).
    Turn(Vec<u8>),
    /// A dregg turn plus devnet material produced at commit time.
    ///
    /// The blocklace remains payload-semantic agnostic: these fields are
    /// opaque bytes here and decoded by the node/explorer layer. Keeping raw
    /// `Turn` alongside this variant preserves compatibility with older
    /// blocks and peers that only carry signed turn bytes.
    TurnBundle(TurnArtifactBundle),
    /// An acknowledgment (I've seen these blocks).
    Ack,
    /// A checkpoint (federation root at this height).
    Checkpoint { root: [u8; 32], height: u64 },
    /// A membership vote (join/leave).
    MembershipVote { action: MembershipAction },
    /// Generic application data.
    Data(Vec<u8>),
}

/// Full devnet artifact payload for a turn-bearing block.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TurnArtifactBundle {
    /// Node-encoded `dregg_sdk::SignedTurn` bytes.
    pub signed_turn: Vec<u8>,
    /// Node-encoded `dregg_turn::TurnReceipt`, when a node already has the
    /// committed receipt at block production time.
    pub receipt: Option<Vec<u8>>,
    /// Node-encoded `dregg_turn::WitnessedReceipt` artifacts for the
    /// receipt above. Multiple entries are expected for bilateral/gamma.2
    /// flows that produce per-cell witnessed receipts.
    pub witnessed_receipts: Vec<Vec<u8>>,
}

impl TurnArtifactBundle {
    pub fn new(signed_turn: Vec<u8>) -> Self {
        Self {
            signed_turn,
            receipt: None,
            witnessed_receipts: Vec::new(),
        }
    }

    /// Build the full artifact bundle for a *committed* turn.
    ///
    /// `signed_turn` is the node-encoded `dregg_sdk::SignedTurn`, `receipt` is
    /// the node-encoded committed `dregg_turn::TurnReceipt`, and
    /// `witnessed_receipts` carries one node-encoded
    /// `dregg_turn::WitnessedReceipt` artifact per cell that produced witness
    /// material at commit time. This is the production constructor that wires
    /// per-cell WitnessedReceipts into gossip so a peer's
    /// `materialize_blocklace_artifacts` receives real witnesses (rather than
    /// the empty `new()` vector that left the distributed witness path dead).
    pub fn with_committed(
        signed_turn: Vec<u8>,
        receipt: Option<Vec<u8>>,
        witnessed_receipts: Vec<Vec<u8>>,
    ) -> Self {
        Self {
            signed_turn,
            receipt,
            witnessed_receipts,
        }
    }
}

/// Membership actions for federation changes.
///
/// A `Propose` action initiates a membership change. An `Approve` action votes
/// on an existing proposal (referencing the block that contains the proposal).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum MembershipAction {
    /// Propose adding a node to the federation.
    Join { node_id: [u8; 32] },
    /// Propose removing a node from the federation.
    Leave { node_id: [u8; 32] },
    /// Approve (vote yes on) an existing proposal contained in `proposal_block`.
    Approve { proposal_block: BlockId },
    /// Reject (vote no on) an existing proposal contained in `proposal_block`.
    Reject { proposal_block: BlockId },
}

/// A block in the blocklace.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Block {
    /// The creator's HYBRID identity: `H(ed25519_pubkey ‖ ml_dsa_pubkey)`
    /// ([`dregg_types::hybrid_id_commitment`]). This is the block's IDENTITY
    /// LABEL — the key the roster, tips, equivocation bookkeeping, cohort
    /// counting, votes and gossip `NodeId` all consume. It is NO LONGER the
    /// ed25519 verify key (that is carried separately in [`Self::ed25519`]); the
    /// id cryptographically COMMITS to BOTH the classical and the post-quantum
    /// public key, so an attacker who keeps the honest ed25519 key but presents
    /// their own ML-DSA key produces a DIFFERENT identity that the enroll+pin
    /// commitment check ([`dregg_types::verify_committed_ml_dsa`]) rejects.
    pub creator: [u8; 32],
    /// The creator's Ed25519 verify key (compressed point). Carried SEPARATELY
    /// from [`Self::creator`] (which is now the hybrid id) so it stays usable as
    /// the classical verify key. [`Self::verify_hybrid`] gates that this key,
    /// together with the enrolled ML-DSA key, commits to [`Self::creator`]
    /// BEFORE either signature is checked.
    #[serde(default)]
    pub ed25519: [u8; 32],
    /// Sequence number within this creator's virtual chain.
    pub seq: u64,
    /// The block's payload.
    pub payload: Payload,
    /// Hash pointers to predecessor blocks (what this block "sees").
    pub predecessors: Vec<BlockId>,
    /// Ed25519 signature over (creator, seq, payload_hash, predecessors).
    #[serde(with = "crate::serde_sig64")]
    pub signature: [u8; 64],
    /// The POST-QUANTUM half of the HYBRID block signature: an ML-DSA-65
    /// (FIPS 204) signature over the SAME canonical bytes as the ed25519 half
    /// (`id()`), produced by the key DERIVED from the creator's ed25519 seed
    /// ([`crate::pq::MlDsaSigningKey::from_seed`]). Empty (`vec![]`) is the
    /// PQ-absent sentinel — it fails [`Block::verify_hybrid`] closed. A hybrid
    /// block carries [`crate::pq::SIG_LEN`] (3309) bytes here.
    ///
    /// The live-consensus verifier PINS this against the creator's ENROLLED
    /// ML-DSA public key (the committee roster, [`Blocklace::enroll_pq`] /
    /// [`Blocklace::receive_block_pinned`]), NOT a key carried in the block — so
    /// a quantum adversary who forges the ed25519 half still cannot inject
    /// consensus blocks under another creator's identity. It is DELIBERATELY
    /// excluded from `id()` / [`PartialEq`] (ML-DSA hedged signing is
    /// randomized, so two signings of one block differ in these bytes yet are
    /// the same block).
    #[serde(default)]
    pub pq_signature: Vec<u8>,
}

impl PartialEq for Block {
    fn eq(&self, other: &Block) -> bool {
        self.creator == other.creator
            && self.seq == other.seq
            && self.payload == other.payload
            && self.predecessors == other.predecessors
            && self.signature == other.signature
    }
}

impl Eq for Block {}

/// Finality level for a block in the blocklace.
///
/// Blocks progress through finality levels as they accumulate acknowledgments:
/// Local -> Bilateral -> Attested -> Ordered
///
/// - Local: only the creator knows about this block.
/// - Bilateral: at least one other participant acknowledged it.
/// - Attested: a quorum (2f+1) acknowledged it.
/// - Ordered: the block is in the causal past of a super-ratified leader (total order assigned).
///
/// The ordering is monotone: once a block reaches a level, it never regresses.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum FinalityLevel {
    /// Block is known locally only (just created or received).
    Local,
    /// Block has been acknowledged by at least one other participant.
    Bilateral,
    /// Block has been attested by a quorum (2f+1 acknowledgments).
    Attested,
    /// Block has been included in a total order (consensus).
    Ordered,
}

/// Proof that a creator equivocated (produced conflicting blocks).
#[derive(Clone, Debug)]
pub struct EquivocationProof {
    pub creator: [u8; 32],
    pub block_a: Block,
    pub block_b: Block,
}

/// Metrics snapshot for observability.
#[derive(Clone, Debug)]
pub struct BlocklaceMetrics {
    /// Total number of blocks in the local view.
    pub block_count: usize,
    /// Number of detected equivocators.
    pub equivocator_count: usize,
    /// Finality lag: number of blocks between tip and last finalized.
    pub finality_lag: usize,
    /// Number of blocks that have been totally ordered.
    pub ordered_count: usize,
    /// Number of blocks that have been attested by quorum.
    pub attested_count: usize,
    /// Number of distinct block creators.
    pub creator_count: usize,
}

/// State of ordering for blocks reaching consensus.
#[derive(Clone, Debug, Default)]
pub struct OrderingState {
    /// Blocks that have reached bilateral acknowledgment.
    pub bilateral: HashSet<BlockId>,
    /// Blocks that have been ordered (total order assigned).
    pub ordered: Vec<BlockId>,
    /// Blocks that have been attested by quorum.
    pub attested: HashSet<BlockId>,
}

// ─── Errors ──────────────────────────────────────────────────────────────────

/// Errors when receiving or merging blocks.
#[derive(Debug, thiserror::Error)]
pub enum BlockError {
    #[error("invalid signature on block from creator {creator:?} seq {seq}")]
    InvalidSignature { creator: [u8; 32], seq: u64 },

    #[error("missing predecessor {missing:?} for block from creator {creator:?} seq {seq}")]
    MissingPredecessor {
        creator: [u8; 32],
        seq: u64,
        missing: BlockId,
    },

    #[error("equivocation detected from creator {creator:?} at seq {seq}")]
    Equivocation {
        creator: [u8; 32],
        seq: u64,
        proof: EquivocationProof,
    },

    #[error("block from creator {creator:?} seq {seq} carries no post-quantum signature half")]
    UnsignedPq { creator: [u8; 32], seq: u64 },

    #[error(
        "invalid ML-DSA post-quantum signature on block from creator {creator:?} seq {seq} \
         (not signed by the creator's ENROLLED key)"
    )]
    BadPqSignature { creator: [u8; 32], seq: u64 },

    #[error(
        "no ML-DSA key enrolled for creator {creator:?} (block seq {seq} rejected fail-closed)"
    )]
    UnenrolledCreator { creator: [u8; 32], seq: u64 },
}

/// Errors during delta-merge.
#[derive(Debug, thiserror::Error)]
pub enum MergeError {
    #[error("delta is not causally closed: missing {missing:?}")]
    NotCausallyClosed { missing: BlockId },

    #[error("block error during merge: {0}")]
    Block(#[from] BlockError),
}

// ─── Block Operations ────────────────────────────────────────────────────────

impl Block {
    /// Compute the content that gets signed: (creator, seq, payload_hash, predecessors).
    fn signing_content(
        creator: &[u8; 32],
        seq: u64,
        payload: &Payload,
        predecessors: &[BlockId],
    ) -> Vec<u8> {
        // Hash the payload to keep the signed content compact.
        let payload_hash = blake3::hash(&Self::payload_bytes(payload));
        Self::signing_content_from_payload_hash(creator, seq, payload_hash.as_bytes(), predecessors)
    }

    /// The signing content reconstructed from an already-computed payload
    /// hash. This is what makes a compact equivocation-evidence header
    /// ([`crate::evidence::EvidenceHeader`]) verifiable WITHOUT the payload
    /// (and without the lace): the header carries `(seq, payload_hash,
    /// predecessors, signature)` and any verifier rebuilds the exact signed
    /// bytes from it. Must stay byte-identical to [`Self::signing_content`].
    pub(crate) fn signing_content_from_payload_hash(
        creator: &[u8; 32],
        seq: u64,
        payload_hash: &[u8; 32],
        predecessors: &[BlockId],
    ) -> Vec<u8> {
        let mut buf = Vec::with_capacity(18 + 32 + 8 + 32 + predecessors.len() * 32);
        buf.extend_from_slice(b"dregg-blocklace-v1");
        buf.extend_from_slice(creator);
        buf.extend_from_slice(&seq.to_le_bytes());
        buf.extend_from_slice(payload_hash);
        for pred in predecessors {
            buf.extend_from_slice(&pred.0);
        }
        buf
    }

    /// Serialize a payload into bytes for hashing (deterministic).
    pub(crate) fn payload_bytes(payload: &Payload) -> Vec<u8> {
        let mut buf = Vec::new();
        match payload {
            Payload::Turn(data) => {
                buf.push(0x01);
                buf.extend_from_slice(&(data.len() as u32).to_le_bytes());
                buf.extend_from_slice(data);
            }
            Payload::TurnBundle(bundle) => {
                buf.push(0x06);
                buf.extend_from_slice(&(bundle.signed_turn.len() as u32).to_le_bytes());
                buf.extend_from_slice(&bundle.signed_turn);
                match &bundle.receipt {
                    Some(receipt) => {
                        buf.push(0x01);
                        buf.extend_from_slice(&(receipt.len() as u32).to_le_bytes());
                        buf.extend_from_slice(receipt);
                    }
                    None => buf.push(0x00),
                }
                buf.extend_from_slice(&(bundle.witnessed_receipts.len() as u32).to_le_bytes());
                for witnessed in &bundle.witnessed_receipts {
                    buf.extend_from_slice(&(witnessed.len() as u32).to_le_bytes());
                    buf.extend_from_slice(witnessed);
                }
            }
            Payload::Ack => {
                buf.push(0x02);
            }
            Payload::Checkpoint { root, height } => {
                buf.push(0x03);
                buf.extend_from_slice(root);
                buf.extend_from_slice(&height.to_le_bytes());
            }
            Payload::MembershipVote { action } => {
                buf.push(0x04);
                match action {
                    MembershipAction::Join { node_id } => {
                        buf.push(0x01);
                        buf.extend_from_slice(node_id);
                    }
                    MembershipAction::Leave { node_id } => {
                        buf.push(0x02);
                        buf.extend_from_slice(node_id);
                    }
                    MembershipAction::Approve { proposal_block } => {
                        buf.push(0x03);
                        buf.extend_from_slice(&proposal_block.0);
                    }
                    MembershipAction::Reject { proposal_block } => {
                        buf.push(0x04);
                        buf.extend_from_slice(&proposal_block.0);
                    }
                }
            }
            Payload::Data(data) => {
                buf.push(0x05);
                buf.extend_from_slice(&(data.len() as u32).to_le_bytes());
                buf.extend_from_slice(data);
            }
        }
        buf
    }

    /// Compute this block's ID (blake3 hash of signed content + signature).
    pub fn id(&self) -> BlockId {
        let mut buf =
            Self::signing_content(&self.creator, self.seq, &self.payload, &self.predecessors);
        buf.extend_from_slice(&self.signature);
        BlockId(*blake3::hash(&buf).as_bytes())
    }

    /// Verify this block's Ed25519 signature against the CARRIED ed25519 key
    /// ([`Self::ed25519`]), over the signing content (which commits to the hybrid
    /// [`Self::creator`] id). The ed25519 key is no longer the identity label, so
    /// verification parses [`Self::ed25519`], not `creator`.
    pub fn verify_signature(&self) -> Result<(), BlockError> {
        let content =
            Self::signing_content(&self.creator, self.seq, &self.payload, &self.predecessors);
        let verifying_key =
            VerifyingKey::from_bytes(&self.ed25519).map_err(|_| BlockError::InvalidSignature {
                creator: self.creator,
                seq: self.seq,
            })?;
        let signature = ed25519_dalek::Signature::from_bytes(&self.signature);
        verifying_key
            .verify(&content, &signature)
            .map_err(|_| BlockError::InvalidSignature {
                creator: self.creator,
                seq: self.seq,
            })
    }

    /// Serialize the block to bytes for wire transmission.
    ///
    /// Uses postcard's compact binary format. The result is deterministic
    /// for a given block (same bytes every time).
    pub fn to_bytes(&self) -> Vec<u8> {
        postcard::to_stdvec(self).expect("block serialization should not fail")
    }

    /// Deserialize a block from bytes.
    ///
    /// Returns `None` if the bytes are malformed.
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        postcard::from_bytes(bytes).ok()
    }

    /// Create and HYBRID-sign a new block (ed25519 ∧ ML-DSA-65).
    ///
    /// The ed25519 half signs the compact `signing_content`; the post-quantum
    /// half signs the canonical `id()` (which already commits to the ed25519
    /// signature) with a key DERIVED from the SAME ed25519 seed
    /// (`signing_key.to_bytes()`, [`crate::pq::MlDsaSigningKey::from_seed`]), so
    /// the creator never manages a separate PQ key and the enrolled PQ public
    /// key is a deterministic function of the ed25519 identity. On a transient
    /// OS-entropy failure during hedged ML-DSA signing the PQ half is left empty
    /// — such a block fails [`Block::verify_hybrid`] closed rather than passing
    /// half-signed.
    pub fn new(
        signing_key: &SigningKey,
        seq: u64,
        payload: Payload,
        predecessors: Vec<BlockId>,
    ) -> Self {
        let ed25519: [u8; 32] = signing_key.verifying_key().to_bytes();
        // Derive the ML-DSA key from the SAME ed25519 seed, and bind BOTH public
        // keys into the HYBRID identity `creator = H(ed25519 ‖ ml_dsa)`.
        let (pq_pk, pq_sk) = crate::pq::MlDsaSigningKey::from_seed(&signing_key.to_bytes());
        let creator = dregg_types::hybrid_id_commitment(&ed25519, &pq_pk.0);
        // The ed25519 half signs the content, which commits to the hybrid id.
        let content = Self::signing_content(&creator, seq, &payload, &predecessors);
        let signature = signing_key.sign(&content);
        let mut block = Block {
            creator,
            ed25519,
            seq,
            payload,
            predecessors,
            signature: signature.to_bytes(),
            pq_signature: Vec::new(),
        };
        // POST-QUANTUM half: sign the SAME canonical bytes the verifier pins
        // (`id()`) with the from-seed ML-DSA key.
        let id = block.id();
        block.pq_signature = pq_sk.sign(&id.0).unwrap_or_default();
        block
    }

    /// The HYBRID identity for a creator whose ed25519 signing key is
    /// `signing_key`: `H(ed25519_pubkey ‖ from-seed ml_dsa_pubkey)`. This is the
    /// value [`Block::new`] stamps as `creator`, the key the roster / tips /
    /// votes / gossip `NodeId` are all keyed by. Equal to
    /// [`Block::hybrid_id_from_parts`] on the two derived public keys.
    pub fn hybrid_id(signing_key: &SigningKey) -> [u8; 32] {
        let ed25519 = signing_key.verifying_key().to_bytes();
        let pq_pk = crate::pq::public_from_ed25519_seed(&signing_key.to_bytes());
        dregg_types::hybrid_id_commitment(&ed25519, &pq_pk.0)
    }

    /// The HYBRID identity from an ed25519 verify key and an ML-DSA public key.
    /// Used at committee-learning boundaries (enrollment / participant sets)
    /// where both public halves are known but no secret seed is: the same value
    /// [`Block::new`] produces as `creator`.
    pub fn hybrid_id_from_parts(
        ed25519: &[u8; 32],
        ml_dsa: &crate::pq::MlDsaPublicKey,
    ) -> [u8; 32] {
        dregg_types::hybrid_id_commitment(ed25519, &ml_dsa.0)
    }

    /// The enrollable ML-DSA-65 public key for a creator whose ed25519 signing
    /// key is `signing_key` — the roster entry a verifier PINS this creator's
    /// consensus blocks against ([`Blocklace::enroll_pq`]). Equal to
    /// [`crate::pq::public_from_ed25519_seed`] on the key's seed.
    pub fn pq_public_key(signing_key: &SigningKey) -> crate::pq::MlDsaPublicKey {
        crate::pq::public_from_ed25519_seed(&signing_key.to_bytes())
    }

    /// Whether this block carries BOTH halves of a (syntactically) non-zero
    /// hybrid signature. A zeroed ed25519 signature or an empty ML-DSA half is
    /// the unsigned sentinel; neither can be a valid hybrid signature.
    pub fn is_signed_hybrid(&self) -> bool {
        self.signature != [0u8; 64] && !self.pq_signature.is_empty()
    }

    /// Verify this block's HYBRID signature: Ed25519 against its self-carried
    /// `creator` pubkey AND ML-DSA-65 against the creator's ENROLLED PQ public
    /// key `enrolled_pq` (the committee roster, NOT a key carried in the block).
    ///
    /// Returns `Ok(())` iff BOTH halves verify. Rejects the missing-PQ sentinel
    /// ([`BlockError::UnsignedPq`]), a forged/mismatched ed25519 half
    /// ([`BlockError::InvalidSignature`]), and a PQ half that was not signed by
    /// the enrolled key ([`BlockError::BadPqSignature`]) — the case a quantum
    /// adversary who forges the ed25519 half, or who signs the PQ half under
    /// their OWN fresh ML-DSA key, cannot escape.
    pub fn verify_hybrid(&self, enrolled_pq: &crate::pq::MlDsaPublicKey) -> Result<(), BlockError> {
        // (0) COMMITMENT GATE (out-of-band → cryptographic): the block's `creator`
        // id MUST commit to BOTH the carried ed25519 key AND the enrolled ML-DSA
        // key. An attacker who keeps the honest ed25519 key but signs / presents
        // their OWN ML-DSA key gets an id that does not recompute to `creator`, so
        // this rejects BEFORE either signature is examined. This is what upgrades
        // the roster PIN from a trusted out-of-band binding to a cryptographic one:
        // the id IS the enrollment.
        if !dregg_types::verify_committed_ml_dsa(&self.creator, &self.ed25519, &enrolled_pq.0) {
            return Err(BlockError::BadPqSignature {
                creator: self.creator,
                seq: self.seq,
            });
        }
        // (a) Classical half: real Ed25519 verification against the carried key.
        self.verify_signature()?;
        // (b) Post-quantum half MUST be present (fail-closed, never treated as a
        // valid ed25519-only block).
        if self.pq_signature.is_empty() {
            return Err(BlockError::UnsignedPq {
                creator: self.creator,
                seq: self.seq,
            });
        }
        // (c) ML-DSA-65 PINNED to the ENROLLED roster key over the same `id()`.
        if !enrolled_pq.verify(&self.id().0, &self.pq_signature) {
            return Err(BlockError::BadPqSignature {
                creator: self.creator,
                seq: self.seq,
            });
        }
        Ok(())
    }
}

// ─── Finality Tracker ────────────────────────────────────────────────────────

/// Tracks finality progression for blocks in the blocklace.
///
/// As blocks accumulate acknowledgments from other participants, they progress
/// through finality levels: Local -> Bilateral -> Ordered -> Attested.
#[derive(Clone)]
pub struct FinalityTracker {
    /// How many acks each block has received (counted by unique creators).
    ack_counts: HashMap<BlockId, HashSet<[u8; 32]>>,
    /// Ordering state.
    pub ordering: OrderingState,
    /// Quorum threshold (typically 2f+1 where f = max Byzantine faults).
    quorum_threshold: usize,
}

impl FinalityTracker {
    /// Create a new finality tracker with the given quorum threshold.
    pub fn new(quorum_threshold: usize) -> Self {
        FinalityTracker {
            ack_counts: HashMap::new(),
            ordering: OrderingState::default(),
            quorum_threshold,
        }
    }

    /// Record that a block was acknowledged by a given creator.
    /// Returns the new finality level for the block.
    ///
    /// The returned level is monotone: once a block reaches Attested, subsequent
    /// acks still return Attested (it never regresses to Bilateral).
    pub fn record_ack(&mut self, block_id: BlockId, acker: [u8; 32]) -> FinalityLevel {
        let ackers = self.ack_counts.entry(block_id).or_default();
        ackers.insert(acker);

        if ackers.len() >= self.quorum_threshold {
            self.ordering.attested.insert(block_id);
            FinalityLevel::Attested
        } else {
            // At least one acker is present (we just inserted), so this is Bilateral.
            self.ordering.bilateral.insert(block_id);
            FinalityLevel::Bilateral
        }
    }

    /// Get the finality level for a block.
    ///
    /// Returns the highest level reached. Finality is monotone:
    /// Local < Bilateral < Attested < Ordered.
    pub fn finality_of(&self, block_id: &BlockId) -> FinalityLevel {
        if self.ordering.ordered.contains(block_id) {
            FinalityLevel::Ordered
        } else if self.ordering.attested.contains(block_id) {
            FinalityLevel::Attested
        } else if self.ordering.bilateral.contains(block_id) {
            FinalityLevel::Bilateral
        } else {
            FinalityLevel::Local
        }
    }

    /// Mark a block as ordered (included in total order by consensus).
    pub fn mark_ordered(&mut self, block_id: BlockId) {
        self.ordering.ordered.push(block_id);
    }

    /// Get the total order sequence so far.
    pub fn ordered_sequence(&self) -> &[BlockId] {
        &self.ordering.ordered
    }
}

// ─── Blocklace Container ─────────────────────────────────────────────────────

/// The blocklace: a local view of the global DAG.
///
/// Each node maintains its own Blocklace instance. The blocklace grows monotonically
/// via CRDT union-merge: receiving blocks from peers can only add to the local view,
/// never remove.
///
/// `Clone` is a cheap structural copy (the `self_key` is a 32-byte Ed25519 key) used by
/// the node's `poll_finalized_blocks` to SNAPSHOT the lace and release the read lock
/// before the O(history) verified-Lean tau-order FFI, so block production is never
/// starved (the live-federation round-production halt).
#[derive(Clone)]
pub struct Blocklace {
    /// All known blocks.
    pub(crate) blocks: HashMap<BlockId, Block>,
    /// Per-creator tip tracking (latest block per creator).
    tips: HashMap<[u8; 32], BlockId>,
    /// Detected equivocators.
    equivocators: HashSet<[u8; 32]>,
    /// Our own signing key.
    self_key: SigningKey,
    /// Our own sequence counter.
    self_seq: u64,
    /// Finality tracking.
    pub finality: FinalityTracker,
    /// The ENROLLED ML-DSA-65 committee roster: `creator (ed25519 pubkey) ->
    /// enrolled ML-DSA public key`. The live-consensus reception
    /// [`Blocklace::receive_block_pinned`] PINS a block's post-quantum half to
    /// the enrolled key for its creator; a block whose creator is absent from
    /// the roster is rejected fail-closed ([`BlockError::UnenrolledCreator`]).
    /// Populated out-of-band from the trusted committee roster (genesis /
    /// membership), via [`Blocklace::enroll_pq`] — the block never carries its
    /// own PQ key.
    pq_roster: HashMap<[u8; 32], crate::pq::MlDsaPublicKey>,
}

impl Blocklace {
    /// Create a new blocklace with the given signing key and quorum threshold.
    pub fn new(self_key: SigningKey, quorum_threshold: usize) -> Self {
        Blocklace {
            blocks: HashMap::new(),
            tips: HashMap::new(),
            equivocators: HashSet::new(),
            self_key,
            self_seq: 0,
            finality: FinalityTracker::new(quorum_threshold),
            pq_roster: HashMap::new(),
        }
    }

    /// Enroll a creator's ML-DSA-65 public key into the committee roster.
    ///
    /// After enrollment, [`Blocklace::receive_block_pinned`] PINS every block by
    /// `creator` to `pubkey`. The key comes from trusted out-of-band enrollment
    /// (genesis / membership committee roster); the block never carries its own
    /// PQ key. Re-enrolling replaces the key (committee rotation). The enrollable
    /// key is [`Block::pq_public_key`] on the creator's ed25519 signing key.
    pub fn enroll_pq(&mut self, creator: [u8; 32], pubkey: crate::pq::MlDsaPublicKey) {
        self.pq_roster.insert(creator, pubkey);
    }

    /// The enrolled ML-DSA committee roster (`creator -> enrolled PQ pubkey`).
    pub fn pq_roster(&self) -> &HashMap<[u8; 32], crate::pq::MlDsaPublicKey> {
        &self.pq_roster
    }

    /// Create a blocklace without finality tracking (quorum = 1, for testing).
    pub fn new_simple(self_key: SigningKey) -> Self {
        Self::new(self_key, 1)
    }

    /// Our own HYBRID creator id (`H(ed25519 ‖ ml_dsa)`) — the same value
    /// [`Block::new`] stamps on the blocks we author, so `tips`, cohort counting
    /// and round planning key our own blocks consistently.
    pub fn self_creator(&self) -> [u8; 32] {
        Block::hybrid_id(&self.self_key)
    }

    /// Our own Ed25519 verify key (the CARRIED classical half). Distinct from
    /// [`Self::self_creator`], which is now the hybrid identity.
    pub fn self_ed25519(&self) -> [u8; 32] {
        self.self_key.verifying_key().to_bytes()
    }

    /// Number of blocks in the local view.
    pub fn len(&self) -> usize {
        self.blocks.len()
    }

    /// Whether the blocklace is empty.
    pub fn is_empty(&self) -> bool {
        self.blocks.is_empty()
    }

    /// Get a block by ID.
    pub fn get(&self, id: &BlockId) -> Option<&Block> {
        self.blocks.get(id)
    }

    /// Check if a block is known.
    pub fn contains(&self, id: &BlockId) -> bool {
        self.blocks.contains_key(id)
    }

    /// Get detected equivocators.
    pub fn equivocators(&self) -> &HashSet<[u8; 32]> {
        &self.equivocators
    }

    /// Get metrics about the current blocklace state.
    pub fn metrics(&self) -> BlocklaceMetrics {
        let last_ordered = self.finality.ordering.ordered.last().copied();
        let finality_lag = if last_ordered.is_some() {
            self.blocks.len() - self.finality.ordering.ordered.len()
        } else {
            self.blocks.len()
        };

        BlocklaceMetrics {
            block_count: self.blocks.len(),
            equivocator_count: self.equivocators.len(),
            finality_lag,
            ordered_count: self.finality.ordering.ordered.len(),
            attested_count: self.finality.ordering.attested.len(),
            creator_count: self.tips.len(),
        }
    }

    /// Get current tips (latest known block per creator).
    pub fn tips(&self) -> &HashMap<[u8; 32], BlockId> {
        &self.tips
    }

    /// Get a reference to the signing key.
    pub fn signing_key(&self) -> &SigningKey {
        &self.self_key
    }

    // ─── Block Creation ──────────────────────────────────────────────────

    /// Create a new block with the given payload.
    /// Predecessors = all current tips (what we currently know about).
    pub fn add_block(&mut self, payload: Payload) -> Block {
        self.self_seq += 1;
        let predecessors: Vec<BlockId> = self.tips.values().copied().collect();
        let block = Block::new(&self.self_key, self.self_seq, payload, predecessors);
        let id = block.id();
        self.blocks.insert(id, block.clone());
        self.tips.insert(self.self_creator(), id);
        block
    }

    /// Create a new block with explicit predecessors (for advanced usage).
    pub fn add_block_with_predecessors(
        &mut self,
        payload: Payload,
        predecessors: Vec<BlockId>,
    ) -> Block {
        self.self_seq += 1;
        let block = Block::new(&self.self_key, self.self_seq, payload, predecessors);
        let id = block.id();
        self.blocks.insert(id, block.clone());
        self.tips.insert(self.self_creator(), id);
        block
    }

    // ─── Block Reception ─────────────────────────────────────────────────

    /// Receive a block from a peer.
    ///
    /// Verifies signature, checks closure (all predecessors known), and detects
    /// equivocation. Returns `Ok(())` if the block was successfully inserted
    /// (or was already present).
    pub fn receive_block(&mut self, block: Block) -> Result<(), BlockError> {
        let id = block.id();

        // Already have it.
        if self.blocks.contains_key(&id) {
            return Ok(());
        }

        // Verify signature (ed25519 half).
        block.verify_signature()?;

        self.insert_checked(id, block)
    }

    /// Receive a consensus block on the LIVE wire path, PINNING its post-quantum
    /// half to the creator's ENROLLED ML-DSA key.
    ///
    /// This is the hybrid, quantum-resistant reception used by the node's
    /// consensus ingest (`node/src/blocklace_sync.rs`). Unlike [`receive_block`]
    /// (ed25519-only, for local DAG reconstruction and equivocation
    /// bookkeeping), it FAILS CLOSED when the creator is not in the enrolled
    /// roster ([`BlockError::UnenrolledCreator`]) and verifies BOTH signature
    /// halves ([`Block::verify_hybrid`]) — so a quantum adversary who forges the
    /// classical half cannot inject a block under an enrolled member's identity.
    /// The roster is populated out-of-band from the committee via
    /// [`Blocklace::enroll_pq`]; a self-carried PQ key is never trusted.
    pub fn receive_block_pinned(&mut self, block: Block) -> Result<(), BlockError> {
        let id = block.id();

        // Already have it.
        if self.blocks.contains_key(&id) {
            return Ok(());
        }

        // PIN: the creator's post-quantum half MUST verify against the ENROLLED
        // roster key. No enrolled key ⇒ reject fail-closed (never trust a
        // self-carried or on-the-fly-derived key).
        match self.pq_roster.get(&block.creator) {
            Some(enrolled_pq) => block.verify_hybrid(enrolled_pq)?,
            None => {
                return Err(BlockError::UnenrolledCreator {
                    creator: block.creator,
                    seq: block.seq,
                });
            }
        }

        self.insert_checked(id, block)
    }

    /// Shared post-verification reception body: closure check, equivocation
    /// detection (retaining the conflicting block as evidence), tip update, and
    /// ack accounting. Both [`receive_block`] (after the ed25519 check) and
    /// [`receive_block_pinned`] (after the hybrid + pinned check) call this;
    /// `id` is `block.id()` recomputed by the caller.
    fn insert_checked(&mut self, id: BlockId, block: Block) -> Result<(), BlockError> {
        // Check closure: all predecessors must be known.
        for pred in &block.predecessors {
            if !self.blocks.contains_key(pred) {
                return Err(BlockError::MissingPredecessor {
                    creator: block.creator,
                    seq: block.seq,
                    missing: *pred,
                });
            }
        }

        // Check for equivocation.
        if let Some(proof) = self.detect_equivocation(&block) {
            self.equivocators.insert(block.creator);
            self.tips.remove(&block.creator);
            // Still insert the block (we keep evidence) but report the equivocation.
            self.blocks.insert(id, block);
            return Err(BlockError::Equivocation {
                creator: proof.creator,
                seq: proof.block_a.seq,
                proof,
            });
        }

        // Don't update tips for known equivocators.
        if !self.equivocators.contains(&block.creator) {
            // Update tip if this is the highest seq for this creator.
            let should_update_tip = match self.tips.get(&block.creator) {
                Some(current_tip_id) => {
                    let current_tip = &self.blocks[current_tip_id];
                    block.seq > current_tip.seq
                }
                None => true,
            };
            if should_update_tip {
                self.tips.insert(block.creator, id);
            }
        }

        // Process ack payloads for finality tracking.
        if block.payload == Payload::Ack {
            for pred in &block.predecessors {
                self.finality.record_ack(*pred, block.creator);
            }
        }

        self.blocks.insert(id, block);
        Ok(())
    }

    // ─── CRDT Delta-Merge ────────────────────────────────────────────────

    /// Merge a delta (set of blocks) into our local view.
    ///
    /// The delta must be causally closed: every predecessor in the delta must
    /// either be within the delta itself or already in our blocklace.
    /// Blocks are topologically sorted by the merge process.
    pub fn merge(&mut self, delta: Vec<Block>) -> Result<(), MergeError> {
        // Build a map of delta block IDs for closure checking.
        let delta_ids: HashMap<BlockId, &Block> = delta.iter().map(|b| (b.id(), b)).collect();

        // Check causal closure.
        for block in &delta {
            for pred in &block.predecessors {
                if !self.blocks.contains_key(pred) && !delta_ids.contains_key(pred) {
                    return Err(MergeError::NotCausallyClosed { missing: *pred });
                }
            }
        }

        // Topologically sort the delta so predecessors are inserted first.
        let sorted = topological_sort(&delta, &self.blocks)?;

        // Insert in order.
        for block in sorted {
            let id = block.id();
            // Skip if already present.
            if self.blocks.contains_key(&id) {
                continue;
            }

            // Verify signature.
            block.verify_signature()?;

            // Check for equivocation.
            if let Some(proof) = self.detect_equivocation(&block) {
                // Closes audit gap C in AUDIT-blocklace-consensus.md: merge()
                // must mirror receive_block() and remove the equivocator's
                // tip. Without this, subsequent blocks from the equivocator
                // in the same delta could update tips for a creator we now
                // know to be Byzantine — leaving stale tip state for the
                // dissemination/frontier and multi-group block-creation
                // codepaths to consume.
                self.equivocators.insert(block.creator);
                self.tips.remove(&block.creator);
                self.blocks.insert(id, block);
                let _ = proof;
                continue;
            }

            // Don't update tips for known equivocators (mirrors receive_block).
            if !self.equivocators.contains(&block.creator) {
                // Update tip.
                let should_update_tip = match self.tips.get(&block.creator) {
                    Some(current_tip_id) => {
                        let current_tip = &self.blocks[current_tip_id];
                        block.seq > current_tip.seq
                    }
                    None => true,
                };
                if should_update_tip {
                    self.tips.insert(block.creator, id);
                }
            }

            self.blocks.insert(id, block);
        }

        Ok(())
    }

    // ─── Round Computation (Cordial Miners DAG depth) ────────────────────

    /// Compute Cordial Miners "round" for a single block.
    ///
    /// `round(block) = 1 + max(round(pred))` over the block's predecessors,
    /// or `1` if the block has no predecessors. Bind this into the federation
    /// [`dregg_types::AttestedRoot`] to distinguish forks (closes audit F3).
    ///
    /// This is intentionally a per-block accessor (not a full DAG sweep);
    /// callers wanting the rounds for the whole DAG should iterate.
    pub fn round_of(&self, block_id: &BlockId) -> Option<u64> {
        let block = self.blocks.get(block_id)?;
        if block.predecessors.is_empty() {
            return Some(1);
        }
        // Recursive walk with memoization-free traversal — used per-finalized
        // block, which is sparse, so the O(depth) cost is acceptable.
        let mut stack: Vec<BlockId> = vec![*block_id];
        let mut memo: HashMap<BlockId, u64> = HashMap::new();
        while let Some(id) = stack.last().copied() {
            let b = match self.blocks.get(&id) {
                Some(b) => b,
                None => {
                    stack.pop();
                    continue;
                }
            };
            if b.predecessors.is_empty() {
                memo.insert(id, 1);
                stack.pop();
                continue;
            }
            let mut all_ready = true;
            let mut max_pred = 0u64;
            for pred in &b.predecessors {
                match memo.get(pred) {
                    Some(&r) => max_pred = max_pred.max(r),
                    None => {
                        if self.blocks.contains_key(pred) {
                            stack.push(*pred);
                            all_ready = false;
                        }
                        // Missing predecessor: treat as round 0 contribution
                        // (cannot happen for a closed blocklace, but be
                        // defensive).
                    }
                }
            }
            if all_ready {
                memo.insert(id, 1 + max_pred);
                stack.pop();
            }
        }
        memo.get(block_id).copied()
    }

    // ─── Equivocation Detection ──────────────────────────────────────────

    /// Check if a block equivocates against existing blocks in the blocklace.
    ///
    /// Equivocation (paper Almog–Lewis–Naor–Shapiro arXiv:2402.08068 Def 4.2,
    /// Lean spec `Dregg2/Authority/Blocklace.lean::Equivocation`): two *distinct*
    /// blocks `a, b` by the **same creator** that are **incomparable** under the
    /// happened-before (`≺`, observe) relation — i.e. neither block is in the
    /// other's causal past (`a ⊀ b ∧ b ⊀ a`). The pair is a fork in the
    /// creator's virtual chain.
    ///
    /// This is the *content-independent* definition: it does NOT require the two
    /// blocks to share a sequence number. The earlier `(creator, seq, id≠)`
    /// heuristic is a strict *subset* of this — an equivocator can produce two
    /// incomparable blocks at *different* seq numbers (e.g. fork the chain and
    /// extend one branch) that the seq heuristic misses entirely. We use the
    /// sound incomparability check, reusing the existing `causal_past`
    /// (`≺`) machinery, so every fork is caught regardless of seq.
    ///
    /// Note: a same-seq, same-creator, different-id pair is always incomparable
    /// (two seq-`n` blocks cannot observe each other along an honest virtual
    /// chain, where observation strictly increases seq), so the old cases remain
    /// detected.
    pub fn detect_equivocation(&self, block: &Block) -> Option<EquivocationProof> {
        let id = block.id();

        // The block being ingested is (in general) not yet in `self.blocks`, so
        // `causal_past` cannot resolve it by id. Compute the incoming block's
        // causal past directly from its declared predecessors — these are
        // already present (closure is enforced before detection).
        let block_past = self.causal_past_from_preds(&block.predecessors);

        for (existing_id, existing) in &self.blocks {
            if existing.creator != block.creator || *existing_id == id {
                continue;
            }

            // Incomparability test (paper `a ∥ b ≡ a ⊀ b ∧ b ⊀ a`):
            //   existing ≺ block  ⟺  existing ∈ causal_past(block)
            //   block    ≺ existing ⟺ block ∈ causal_past(existing)
            // If EITHER direction holds the two blocks are causally ordered
            // (honest chain extension), so this is NOT an equivocation.
            let existing_observed_by_block = block_past.contains(existing_id);
            let block_observed_by_existing = self.causal_past(existing_id).contains(&id);

            if !existing_observed_by_block && !block_observed_by_existing {
                // Same creator, distinct, mutually non-preceding ⇒ incomparable
                // ⇒ equivocation (the EquivocationProof witness pair).
                return Some(EquivocationProof {
                    creator: block.creator,
                    block_a: existing.clone(),
                    block_b: block.clone(),
                });
            }
        }
        None
    }

    /// Compute the causal past of a (possibly not-yet-inserted) block given its
    /// declared predecessor ids. This is `causal_past` with the seed frontier
    /// supplied directly rather than looked up by block id, so it works for a
    /// block that is mid-ingest and therefore not yet in `self.blocks`.
    fn causal_past_from_preds(&self, predecessors: &[BlockId]) -> HashSet<BlockId> {
        let mut visited = HashSet::new();
        let mut queue: VecDeque<BlockId> = predecessors.iter().copied().collect();

        while let Some(current) = queue.pop_front() {
            if !visited.insert(current) {
                continue;
            }
            if let Some(block) = self.blocks.get(&current) {
                for pred in &block.predecessors {
                    if !visited.contains(pred) {
                        queue.push_back(*pred);
                    }
                }
            }
        }

        visited
    }

    // ─── Query Operations ────────────────────────────────────────────────

    /// Get a creator's virtual chain: all blocks by that creator, sorted by seq.
    pub fn virtual_chain(&self, creator: &[u8; 32]) -> Vec<&Block> {
        let mut chain: Vec<&Block> = self
            .blocks
            .values()
            .filter(|b| &b.creator == creator)
            .collect();
        chain.sort_by_key(|b| b.seq);
        chain
    }

    /// Compute the causal past of a block: all blocks transitively reachable
    /// via predecessors.
    pub fn causal_past(&self, block_id: &BlockId) -> HashSet<BlockId> {
        let mut visited = HashSet::new();
        let mut queue = VecDeque::new();

        if let Some(block) = self.blocks.get(block_id) {
            for pred in &block.predecessors {
                queue.push_back(*pred);
            }
        }

        while let Some(current) = queue.pop_front() {
            if !visited.insert(current) {
                continue;
            }
            if let Some(block) = self.blocks.get(&current) {
                for pred in &block.predecessors {
                    if !visited.contains(pred) {
                        queue.push_back(*pred);
                    }
                }
            }
        }

        visited
    }

    /// Compute the union of the causal pasts of several blocks in ONE
    /// shared-visited traversal (instead of re-walking overlapping history once
    /// per block), and INCLUSIVE of each seed id itself. This mirrors the
    /// `crate::Blocklace::causal_past_union` reference impl: each seed is
    /// enqueued (so the seeds are in the result), and unknown ids contribute
    /// only themselves. The single shared visited set makes overlapping
    /// histories cheap — the cost is the size of the union, not the sum of the
    /// per-block pasts.
    pub fn causal_past_union<'a, I>(&self, ids: I) -> HashSet<BlockId>
    where
        I: IntoIterator<Item = &'a BlockId>,
    {
        let mut result = HashSet::new();
        let mut queue: VecDeque<BlockId> = VecDeque::new();
        for id in ids {
            queue.push_back(*id);
        }
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

    /// Check if block `a` is in the causal past of block `b`.
    pub fn is_predecessor(&self, a: &BlockId, b: &BlockId) -> bool {
        if a == b {
            return false;
        }
        self.causal_past(b).contains(a)
    }

    /// Get the current frontier: maximal blocks that no other block points to.
    pub fn frontier(&self) -> Vec<BlockId> {
        let mut pointed_to: HashSet<BlockId> = HashSet::new();
        for block in self.blocks.values() {
            for pred in &block.predecessors {
                pointed_to.insert(*pred);
            }
        }

        self.blocks
            .keys()
            .filter(|id| !pointed_to.contains(id))
            .copied()
            .collect()
    }

    /// Check if `block` observes `target` without observing any equivocation
    /// by `target`'s creator.
    ///
    /// "Observes" means target is in block's causal past (`target ≺ block`).
    /// "Without observing equivocation" means the causal past does not contain a
    /// pair of **incomparable** blocks by the same creator (paper Def 4.2 / Lean
    /// `Blocklace.lean::seesBoth` + `observer_detects`). This is the
    /// content-independent definition: two same-creator blocks in the past that
    /// do not observe each other are a fork, *regardless of sequence number*.
    /// (The earlier same-seq heuristic was a strict subset and missed
    /// different-seq forks.)
    pub fn approved_by(&self, block_id: &BlockId, target_id: &BlockId) -> bool {
        let past = self.causal_past(block_id);

        // target must be in the causal past.
        if !past.contains(target_id) {
            return false;
        }

        // Get the target's creator.
        let target_creator = match self.blocks.get(target_id) {
            Some(b) => b.creator,
            None => return false,
        };

        // Gather the target-creator's blocks visible in the causal past, then
        // check no two of them are incomparable (a fork). Caching each block's
        // causal past avoids recomputing it in the inner loop.
        let creator_blocks: Vec<BlockId> = past
            .iter()
            .filter(|id| {
                self.blocks
                    .get(id)
                    .is_some_and(|b| b.creator == target_creator)
            })
            .copied()
            .collect();

        let pasts: Vec<HashSet<BlockId>> = creator_blocks
            .iter()
            .map(|id| self.causal_past(id))
            .collect();

        for i in 0..creator_blocks.len() {
            for j in (i + 1)..creator_blocks.len() {
                let a = &creator_blocks[i];
                let b = &creator_blocks[j];
                // incomparable: a ⊀ b ∧ b ⊀ a (neither in the other's past).
                let a_observes_b = pasts[i].contains(b);
                let b_observes_a = pasts[j].contains(a);
                if !a_observes_b && !b_observes_a {
                    return false;
                }
            }
        }

        true
    }

    /// Remove an equivocator from the blocklace.
    ///
    /// This marks the creator as an equivocator (if not already) and removes
    /// their blocks from the tips map. The blocks themselves are retained as
    /// evidence, but the equivocator will not be considered for tip tracking
    /// or future operations.
    ///
    /// Returns `true` if this was a newly-detected equivocator.
    pub fn remove_equivocator(&mut self, creator: &[u8; 32]) -> bool {
        let was_new = self.equivocators.insert(*creator);
        self.tips.remove(creator);
        was_new
    }

    /// Check if a creator is a known equivocator.
    pub fn is_equivocator(&self, creator: &[u8; 32]) -> bool {
        self.equivocators.contains(creator)
    }

    /// Export all blocks (for delta-merge to a peer).
    pub fn all_blocks(&self) -> Vec<Block> {
        self.blocks.values().cloned().collect()
    }

    /// Export blocks not known to a peer (given a set of known IDs).
    pub fn delta_for(&self, known: &HashSet<BlockId>) -> Vec<Block> {
        self.blocks
            .iter()
            .filter(|(id, _)| !known.contains(id))
            .map(|(_, b)| b.clone())
            .collect()
    }

    /// Iterate over all blocks.
    pub fn iter(&self) -> impl Iterator<Item = (&BlockId, &Block)> {
        self.blocks.iter()
    }

    /// Create a checkpoint of the current blocklace state.
    ///
    /// The checkpoint includes:
    /// - All block data (serialized)
    /// - Current tips per creator
    /// - Detected equivocators
    /// - Ordering state (what has been finalized)
    ///
    /// A new node joining the network can restore from this checkpoint
    /// without replaying the full block history.
    pub fn checkpoint(&self) -> CheckpointData {
        let blocks: Vec<Vec<u8>> = self.blocks.values().map(|b| b.to_bytes()).collect();
        CheckpointData {
            blocks,
            tips: self.tips.clone(),
            equivocators: self.equivocators.iter().copied().collect(),
            ordered_block_ids: self.finality.ordering.ordered.clone(),
            attested_block_ids: self.finality.ordering.attested.iter().copied().collect(),
        }
    }

    /// Restore a blocklace from a checkpoint, **authenticating every block** on
    /// the recovery path exactly as the hardened `receive_block` insert does.
    ///
    /// This is the default loader and the one any **untrusted / peer-supplied**
    /// checkpoint MUST use (e.g. `bootstrap_from_checkpoint`). A checkpoint is
    /// just a bag of serialized blocks; without re-authentication it is an
    /// A1-class recovery-path bypass — a peer could ship a checkpoint containing
    /// a forged block (a block claiming a victim's `creator` with a junk
    /// signature, or one whose predecessor is fiction) and have it sail into the
    /// restored DAG unverified. Here we close that door:
    ///
    /// 1. **Signature** — every block's Ed25519 signature is verified against its
    ///    declared `creator` (rejecting forged/unsigned blocks). Same check as
    ///    `receive_block` step "Verify signature".
    /// 2. **Sequence/closure** — blocks are inserted in topological order; a
    ///    block whose predecessor is absent from the checkpoint (a *dangling*
    ///    predecessor / non-closed view) is rejected. Same check as
    ///    `receive_block` step "Check closure".
    /// 3. **Equivocation** — a same-creator incomparable pair smuggled through
    ///    the checkpoint is detected, the creator recorded as an equivocator, and
    ///    its tip withheld. Same check as `receive_block` step "equivocation".
    ///
    /// `tips`, `equivocators`, and the ordering frontier are then **derived from
    /// the authenticated blocks** rather than copied verbatim from the (untrusted)
    /// checkpoint metadata — a malicious checkpoint cannot assert a tip/ordering
    /// it did not earn. The self-asserted `equivocators` set is folded in as a
    /// lower bound (a checkpoint may declare *more* equivocators than the local
    /// re-derivation observes; it may never *hide* one we detected).
    pub fn from_checkpoint(
        checkpoint: &CheckpointData,
        self_key: SigningKey,
        quorum_threshold: usize,
    ) -> Result<Self, String> {
        let mut lace = Self::new(self_key, quorum_threshold);

        // Deserialize all blocks up front (so we can topo-sort by closure).
        let mut pending: Vec<Block> = Vec::with_capacity(checkpoint.blocks.len());
        for block_bytes in &checkpoint.blocks {
            let block = Block::from_bytes(block_bytes)
                .ok_or_else(|| "failed to deserialize block from checkpoint".to_string())?;
            pending.push(block);
        }

        // (1) Authenticate every block's signature BEFORE it can enter the DAG.
        // A forged/unsigned block claiming a victim creator is rejected here,
        // exactly as the live receive path would reject it.
        for block in &pending {
            block.verify_signature().map_err(|e| {
                format!(
                    "checkpoint block failed signature authentication: {e:?} \
                     (creator={:02x}{:02x}.., seq={})",
                    block.creator[0], block.creator[1], block.seq
                )
            })?;
        }

        // (2)+(3) Insert in topological (closure-respecting) order, rejecting a
        // dangling predecessor and detecting equivocation as we go. We loop,
        // admitting every block whose predecessors are all already present, until
        // either everything is placed or a round makes no progress (⇒ a dangling
        // predecessor, i.e. a non-closed checkpoint — rejected).
        let mut remaining = pending;
        while !remaining.is_empty() {
            let mut progressed = false;
            let mut still_pending: Vec<Block> = Vec::with_capacity(remaining.len());

            for block in remaining.into_iter() {
                let id = block.id();
                if lace.blocks.contains_key(&id) {
                    // Duplicate within the checkpoint — idempotent, drop it.
                    progressed = true;
                    continue;
                }
                let closed = block
                    .predecessors
                    .iter()
                    .all(|pred| lace.blocks.contains_key(pred));
                if !closed {
                    still_pending.push(block);
                    continue;
                }

                // Closure satisfied: run the same equivocation gate as
                // receive_block, then insert.
                if let Some(_proof) = lace.detect_equivocation(&block) {
                    lace.equivocators.insert(block.creator);
                    lace.tips.remove(&block.creator);
                    lace.blocks.insert(id, block);
                } else {
                    if !lace.equivocators.contains(&block.creator) {
                        let should_update_tip = match lace.tips.get(&block.creator) {
                            Some(tip_id) => lace.blocks[tip_id].seq < block.seq,
                            None => true,
                        };
                        if should_update_tip {
                            lace.tips.insert(block.creator, id);
                        }
                    }
                    if block.payload == Payload::Ack {
                        for pred in &block.predecessors {
                            lace.finality.record_ack(*pred, block.creator);
                        }
                    }
                    lace.blocks.insert(id, block);
                }
                progressed = true;
            }

            if !progressed {
                // No block in this round could be placed ⇒ at least one has a
                // predecessor that exists nowhere in the checkpoint: a dangling
                // predecessor / non-closed view. Reject the whole checkpoint
                // (the live receive path returns MissingPredecessor here).
                let example = still_pending
                    .first()
                    .map(|b| {
                        format!(
                            "creator={:02x}{:02x}.., seq={}",
                            b.creator[0], b.creator[1], b.seq
                        )
                    })
                    .unwrap_or_default();
                return Err(format!(
                    "checkpoint is not causally closed: {} block(s) have a dangling \
                     predecessor (first: {example})",
                    still_pending.len()
                ));
            }
            remaining = still_pending;
        }

        // Fold the checkpoint's self-asserted equivocators in as a LOWER bound:
        // a checkpoint may name more equivocators than we re-derived (e.g. ones
        // whose evidence blocks were pruned), but it can never hide one we
        // detected above. We never trust it to UN-flag a creator.
        for e in &checkpoint.equivocators {
            if lace.equivocators.insert(*e) {
                // Newly-named equivocator: withhold its tip too.
                lace.tips.remove(e);
            }
        }

        // Restore ordering state (finality frontier). These are block-id sets
        // over the now-authenticated `blocks`; an id naming a block we did not
        // admit is simply inert (no unverified block backs it).
        lace.finality.ordering.ordered = checkpoint.ordered_block_ids.clone();
        lace.finality.ordering.attested = checkpoint.attested_block_ids.iter().copied().collect();

        // Derive self_seq from our own (authenticated) tip.
        let self_creator = lace.self_creator();
        if let Some(tip_id) = lace.tips.get(&self_creator)
            && let Some(tip_block) = lace.blocks.get(tip_id)
        {
            lace.self_seq = tip_block.seq;
        }

        Ok(lace)
    }

    /// Restore a blocklace from a checkpoint **without** re-authenticating blocks.
    ///
    /// This trusts the checkpoint data verbatim (blocks are NOT re-verified
    /// against signatures, closure is NOT enforced, tips/equivocators are copied
    /// as-is). Use ONLY for a checkpoint whose provenance is already established
    /// to be honest — e.g. one this node itself wrote to local disk and whose
    /// integrity is covered by the persistence layer. NEVER call this on a
    /// peer-supplied / network-fetched checkpoint: route those through
    /// [`Self::from_checkpoint`], which authenticates every block.
    pub fn from_checkpoint_trusted(
        checkpoint: &CheckpointData,
        self_key: SigningKey,
        quorum_threshold: usize,
    ) -> Result<Self, String> {
        let mut lace = Self::new(self_key, quorum_threshold);

        for block_bytes in &checkpoint.blocks {
            let block = Block::from_bytes(block_bytes)
                .ok_or_else(|| "failed to deserialize block from checkpoint".to_string())?;
            let id = block.id();
            lace.blocks.insert(id, block);
        }

        lace.tips = checkpoint.tips.clone();
        lace.equivocators = checkpoint.equivocators.iter().copied().collect();
        lace.finality.ordering.ordered = checkpoint.ordered_block_ids.clone();
        lace.finality.ordering.attested = checkpoint.attested_block_ids.iter().copied().collect();

        let self_creator = lace.self_creator();
        if let Some(tip_id) = lace.tips.get(&self_creator)
            && let Some(tip_block) = lace.blocks.get(tip_id)
        {
            lace.self_seq = tip_block.seq;
        }

        Ok(lace)
    }
}

/// Snapshot of the blocklace state for persistence or new-node catch-up.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CheckpointData {
    /// All blocks in serialized form.
    pub blocks: Vec<Vec<u8>>,
    /// Creator -> tip block ID.
    pub tips: HashMap<[u8; 32], BlockId>,
    /// Known equivocator public keys.
    pub equivocators: Vec<[u8; 32]>,
    /// Block IDs in their total order.
    pub ordered_block_ids: Vec<BlockId>,
    /// Block IDs that have been attested by quorum.
    pub attested_block_ids: Vec<BlockId>,
}

// ─── Helpers ─────────────────────────────────────────────────────────────────

/// Topological sort of blocks, ensuring predecessors come before dependents.
/// Blocks whose predecessors are already in `existing` are considered satisfied.
fn topological_sort(
    blocks: &[Block],
    existing: &HashMap<BlockId, Block>,
) -> Result<Vec<Block>, MergeError> {
    let block_map: HashMap<BlockId, &Block> = blocks.iter().map(|b| (b.id(), b)).collect();
    let mut in_degree: HashMap<BlockId, usize> = HashMap::new();
    let mut dependents: HashMap<BlockId, Vec<BlockId>> = HashMap::new();

    for block in blocks {
        let id = block.id();
        let mut degree = 0;
        for pred in &block.predecessors {
            if !existing.contains_key(pred) {
                // This predecessor is within the delta.
                degree += 1;
                dependents.entry(*pred).or_default().push(id);
            }
        }
        in_degree.insert(id, degree);
    }

    let mut queue: VecDeque<BlockId> = in_degree
        .iter()
        .filter(|&(_, &deg)| deg == 0)
        .map(|(id, _)| *id)
        .collect();

    let mut sorted = Vec::with_capacity(blocks.len());

    while let Some(id) = queue.pop_front() {
        if let Some(block) = block_map.get(&id) {
            sorted.push((*block).clone());
        }
        if let Some(deps) = dependents.get(&id) {
            for dep_id in deps {
                if let Some(deg) = in_degree.get_mut(dep_id) {
                    *deg -= 1;
                    if *deg == 0 {
                        queue.push_back(*dep_id);
                    }
                }
            }
        }
    }

    // If we didn't sort all blocks, there's a missing dependency.
    if sorted.len() < blocks.len() {
        for block in blocks {
            let id = block.id();
            if in_degree.get(&id).copied().unwrap_or(0) > 0 {
                for pred in &block.predecessors {
                    if !existing.contains_key(pred) && !block_map.contains_key(pred) {
                        return Err(MergeError::NotCausallyClosed { missing: *pred });
                    }
                }
            }
        }
    }

    Ok(sorted)
}

// ─── HYBRID PQ (ed25519 ∧ ML-DSA-65) enroll+PIN tests ─────────────────────────
#[cfg(test)]
mod pq_hybrid_tests {
    use super::*;
    use crate::pq;
    use ed25519_dalek::{Signer, SigningKey};

    /// Deterministic per-index test key (mirrors the strand-layer test helper).
    fn key_for(i: u8) -> SigningKey {
        SigningKey::from_bytes(&[i; 32])
    }

    /// A blocklace whose committee (members 1..=8) is pre-enrolled in the
    /// ML-DSA roster, so the pinned live path can verify their blocks.
    fn enrolled_lace() -> Blocklace {
        let mut lace = Blocklace::new(key_for(1), 3);
        for c in 1..=8u8 {
            let k = key_for(c);
            // Roster is keyed by the HYBRID id (== the block's `creator`).
            lace.enroll_pq(Block::hybrid_id(&k), Block::pq_public_key(&k));
        }
        lace
    }

    /// An honest hybrid consensus block — both halves from the creator's
    /// from-seed keys — passes `verify_hybrid` and the pinned live path.
    #[test]
    fn hybrid_honest_block_passes() {
        let creator = key_for(7);
        let enrolled = Block::pq_public_key(&creator);
        let block = Block::new(&creator, 1, Payload::Data(b"honest".to_vec()), vec![]);
        assert!(block.is_signed_hybrid(), "carries both halves");
        assert!(
            !block.pq_signature.is_empty(),
            "PQ half present (~{} bytes)",
            pq::SIG_LEN
        );
        assert!(block.verify_hybrid(&enrolled).is_ok());

        let mut lace = enrolled_lace();
        assert!(lace.receive_block_pinned(block).is_ok());
        assert_eq!(lace.len(), 1);
    }

    /// THE adversarial test: a consensus block with a VALID ed25519 half from
    /// committee member P, but an ML-DSA half signed under an ATTACKER's OWN
    /// fresh key (≠ P's enrolled key) MUST be rejected. The quantum-adversary
    /// scenario: assume the classical half is forgeable, but the PQ half is
    /// pinned to P's enrolled key, which the attacker does not hold.
    #[test]
    fn hybrid_attacker_pq_key_rejected() {
        let p_key = key_for(7); // committee member P
        let p_enrolled = Block::pq_public_key(&p_key); // P's ENROLLED ML-DSA key

        // Honest-looking block: valid ed25519 half by P over its signing content.
        let mut forged = Block::new(&p_key, 1, Payload::Data(b"inject".to_vec()), vec![]);
        // (Block::new already produced P's genuine ed25519 half; re-affirm it.)
        let content = Block::signing_content(
            &forged.creator,
            forged.seq,
            &forged.payload,
            &forged.predecessors,
        );
        forged.signature = p_key.sign(&content).to_bytes();

        // The ATTACKER controls the PQ half but NOT P's from-seed ML-DSA key:
        // they generate their own ML-DSA key (a different seed) and sign id().
        let attacker_seed = [0xAB_u8; 32];
        let (attacker_pq_pub, attacker_pq_sk) = pq::MlDsaSigningKey::from_seed(&attacker_seed);
        forged.pq_signature = attacker_pq_sk.sign(&forged.id().0).unwrap();
        assert_ne!(
            attacker_pq_pub, p_enrolled,
            "attacker key must differ from P's enrolled key"
        );

        // The forged PQ half is a VALID ML-DSA signature — under the ATTACKER's
        // key — so it MUST NOT verify against P's ENROLLED key.
        assert!(
            attacker_pq_pub.verify(&forged.id().0, &forged.pq_signature),
            "sanity: forged sig is valid under the attacker's own key"
        );
        match forged.verify_hybrid(&p_enrolled) {
            Err(BlockError::BadPqSignature { .. }) => {}
            other => panic!("expected BadPqSignature, got {other:?}"),
        }

        // And it is rejected by the pinned live reception path.
        let mut lace = enrolled_lace();
        match lace.receive_block_pinned(forged) {
            Err(BlockError::BadPqSignature { .. }) => {}
            other => panic!("expected BadPqSignature on insert, got {other:?}"),
        }
        assert_eq!(lace.len(), 0, "forged block must not be stored");
    }

    /// THE COMMITMENT ADVERSARIAL TEST (out-of-band → cryptographic upgrade): an
    /// attacker who KEEPS the honest member P's ed25519 key but presents their OWN
    /// ML-DSA key is rejected by the identity commitment — the `creator` id binds
    /// BOTH public halves, so a swapped ML-DSA key no longer recomputes to
    /// `creator`, and forming a fresh id that reuses P's ed25519 key is simply a
    /// DIFFERENT (unenrolled) identity, never P.
    #[test]
    fn hybrid_commitment_rejects_swapped_ml_dsa() {
        let p_key = key_for(7);
        let p_enrolled = Block::pq_public_key(&p_key); // P's committed ML-DSA key
        let block = Block::new(&p_key, 1, Payload::Data(b"x".to_vec()), vec![]);
        // The id genuinely commits to (P_ed, P_mldsa).
        assert!(block.verify_hybrid(&p_enrolled).is_ok());
        assert!(dregg_types::verify_committed_ml_dsa(
            &block.creator,
            &block.ed25519,
            &p_enrolled.0
        ));

        // Attacker keeps P's ed25519 key but presents their OWN ML-DSA key: the
        // commitment does NOT recompute to `creator`, so verify rejects BEFORE any
        // signature is checked.
        let (attacker_mldsa, _sk) = pq::MlDsaSigningKey::from_seed(&[0xCD_u8; 32]);
        assert_ne!(attacker_mldsa, p_enrolled);
        assert!(!dregg_types::verify_committed_ml_dsa(
            &block.creator,
            &block.ed25519,
            &attacker_mldsa.0
        ));
        match block.verify_hybrid(&attacker_mldsa) {
            Err(BlockError::BadPqSignature { .. }) => {}
            other => panic!("commitment gate must reject a swapped ML-DSA key, got {other:?}"),
        }

        // Forming a fresh id that REUSES P's ed25519 key is a DISTINCT creator —
        // not P — so on the pinned live path it is UnenrolledCreator (it never
        // inherits P's enrolled slot).
        let attacker_creator = Block::hybrid_id_from_parts(&block.ed25519, &attacker_mldsa);
        assert_ne!(
            attacker_creator, block.creator,
            "reusing P's ed25519 key yields a distinct hybrid id"
        );
        let mut forged = block.clone();
        forged.creator = attacker_creator;
        let mut lace = enrolled_lace();
        match lace.receive_block_pinned(forged) {
            Err(BlockError::UnenrolledCreator { .. }) => {}
            other => panic!("a reused-ed25519 identity must be UnenrolledCreator, got {other:?}"),
        }
        assert_eq!(lace.len(), 0);
    }

    /// A block with a missing / empty PQ half fails CLOSED — never treated as a
    /// valid ed25519-only block on the pinned path.
    #[test]
    fn hybrid_missing_pq_half_fails_closed() {
        let p_key = key_for(7);
        let enrolled = Block::pq_public_key(&p_key);

        let mut ed_only = Block::new(&p_key, 1, Payload::Data(b"x".to_vec()), vec![]);
        ed_only.pq_signature.clear(); // strip the PQ half
        assert!(!ed_only.is_signed_hybrid());
        match ed_only.verify_hybrid(&enrolled) {
            Err(BlockError::UnsignedPq { .. }) => {}
            other => panic!("expected UnsignedPq (fail-closed), got {other:?}"),
        }
        let mut lace = enrolled_lace();
        match lace.receive_block_pinned(ed_only) {
            Err(BlockError::UnsignedPq { .. }) => {}
            other => panic!("expected UnsignedPq on insert, got {other:?}"),
        }
        assert_eq!(lace.len(), 0);
    }

    /// A creator with NO enrolled ML-DSA key is rejected fail-closed — the
    /// pinned path never trusts a self-carried or on-the-fly-derived PQ key.
    #[test]
    fn hybrid_unenrolled_creator_rejected() {
        // A fully-valid hybrid block by creator 200, but enrolled_lace only
        // enrolls members 1..=8.
        let block = Block::new(
            &key_for(200),
            1,
            Payload::Data(b"stranger".to_vec()),
            vec![],
        );
        assert!(block.is_signed_hybrid());
        let mut lace = enrolled_lace();
        match lace.receive_block_pinned(block) {
            Err(BlockError::UnenrolledCreator { .. }) => {}
            other => panic!("expected UnenrolledCreator, got {other:?}"),
        }
        assert_eq!(lace.len(), 0);
    }

    /// The ed25519-only `receive_block` still accepts an honest block (the
    /// hybrid pin is an ADDITIVE live-path gate; local DAG reconstruction and
    /// the 41 existing reception tests are unaffected).
    #[test]
    fn ed25519_only_receive_block_still_accepts() {
        let block = Block::new(&key_for(3), 1, Payload::Data(b"local".to_vec()), vec![]);
        let mut lace = Blocklace::new(key_for(1), 3);
        assert!(lace.receive_block(block).is_ok());
        assert_eq!(lace.len(), 1);
    }
}
