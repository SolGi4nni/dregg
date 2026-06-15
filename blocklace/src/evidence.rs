//! Equivocation evidence as a FIRST-CLASS WIRE VALUE (CONSENSUS-FLEX §7 item 1,
//! ORGANS §5 adjudication weld).
//!
//! The blocklace already RETAINS fork evidence ([`crate::finality::EquivocationProof`]
//! holds the two conflicting blocks; `blocklace_sync` propagates them and the
//! constitution auto-evicts) — but the evidence dead-ended at the membership
//! layer: it had no codec, so it could not ride a turn, feed a predicate atom,
//! or trigger a slash. This module is the wire shape:
//!
//! [`EvidenceOfEquivocation`] = `(creator, header_a, header_b)` where each
//! [`EvidenceHeader`] carries `(seq, payload_hash, predecessors, signature)`.
//! That is exactly the spec'd `(header_a, header_b, sig_a, sig_b)` value —
//! small (no payloads), self-contained, and **verifiable without the lace**:
//!
//! * two Ed25519 checks (each header's signature over the reconstructed
//!   [`Block::signing_content_from_payload_hash`] bytes, against `creator`),
//! * same author (structural — one `creator` field),
//! * same slot (`header_a.seq == header_b.seq`),
//! * conflicting content (`payload_hash` or `predecessors` differ — the
//!   creator signed two DIFFERENT statements for one slot).
//!
//! ## Scope: the same-slot fork is the lace-free-certifiable core
//!
//! [`crate::finality::Blocklace::detect_equivocation`] implements the paper's
//! content-independent Def 4.2 (incomparable same-creator pair — forks at
//! *different* seq numbers are also caught). Incomparability is a lace-relative
//! fact (it quantifies over causal pasts), so it cannot be checked from a
//! constant-size exhibit. The wire value therefore carries the SAME-SLOT fork
//! — the subset either party can certify with two signatures and three
//! equalities (the verify/find asymmetry CONSENSUS-FLEX §7 names). A
//! different-seq incomparable fork stays on the membership/auto-evict path; a
//! segment-carrying evidence form for it is a named later lane.
//!
//! ## Fail-closed
//!
//! [`EvidenceOfEquivocation::verify`] refuses: a bad/forged signature on either
//! header, mismatched slots, and identical content (two valid signatures over
//! the SAME statement — e.g. a re-signed nonce variant — is not a conflicting
//! story and must not slash). Construction from blocks refuses cross-creator
//! pairs. Malformed wire bytes fail decode.

use ed25519_dalek::{Verifier, VerifyingKey};
use serde::{Deserialize, Serialize};

use crate::finality::{Block, BlockId, EquivocationProof};

/// Domain key for the order-insensitive evidence digest (the no-double-resolve
/// burn key — see [`EvidenceOfEquivocation::digest`]).
const EVIDENCE_DIGEST_DOMAIN: &str = "dregg-equivocation-evidence-digest-v1";

/// One conflicting block, reduced to its signed header: everything needed to
/// re-derive the exact signed bytes (and the block id) WITHOUT the payload.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct EvidenceHeader {
    /// The slot the block claims in its creator's virtual chain.
    pub seq: u64,
    /// blake3 of the block's canonical payload bytes (what the signature
    /// covers in place of the payload itself).
    pub payload_hash: [u8; 32],
    /// The block's declared causal predecessors (part of the signed content).
    pub predecessors: Vec<BlockId>,
    /// The creator's Ed25519 signature over the signing content.
    #[serde(with = "crate::serde_sig64")]
    pub signature: [u8; 64],
}

impl EvidenceHeader {
    /// Reduce a full block to its evidence header.
    pub fn from_block(block: &Block) -> Self {
        Self {
            seq: block.seq,
            payload_hash: *blake3::hash(&Block::payload_bytes(&block.payload)).as_bytes(),
            predecessors: block.predecessors.clone(),
            signature: block.signature,
        }
    }

    /// The exact bytes the creator signed (byte-identical to
    /// `Block::signing_content` for the full block).
    fn signing_content(&self, creator: &[u8; 32]) -> Vec<u8> {
        Block::signing_content_from_payload_hash(
            creator,
            self.seq,
            &self.payload_hash,
            &self.predecessors,
        )
    }

    /// The block id this header denotes — same derivation as [`Block::id`]
    /// (blake3 of signed content ‖ signature).
    pub fn block_id(&self, creator: &[u8; 32]) -> BlockId {
        let mut buf = self.signing_content(creator);
        buf.extend_from_slice(&self.signature);
        BlockId(*blake3::hash(&buf).as_bytes())
    }

    /// Real Ed25519 verification of this header's signature against `creator`.
    /// A malformed creator key or forged signature is `false`.
    pub fn verify_signature(&self, creator: &[u8; 32]) -> bool {
        let Ok(vk) = VerifyingKey::from_bytes(creator) else {
            return false;
        };
        let sig = ed25519_dalek::Signature::from_bytes(&self.signature);
        vk.verify(&self.signing_content(creator), &sig).is_ok()
    }
}

/// Why an alleged equivocation exhibit is NOT grounds to slash.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EvidenceError {
    /// `from_blocks` was given blocks by two different creators.
    CreatorMismatch,
    /// The two headers claim different slots — two blocks at different
    /// positions are (from a constant-size exhibit) just chain extension,
    /// not a certifiable fork.
    PositionMismatch { seq_a: u64, seq_b: u64 },
    /// The two headers sign the SAME statement (equal payload hash AND equal
    /// predecessors). Two signatures over one statement is not a conflicting
    /// story; refusing prevents a nonce-variant re-signature from slashing.
    IdenticalContent,
    /// A header's Ed25519 signature does not verify against the accused
    /// creator (`which` is `'a'` or `'b'`). Forged exhibits land here.
    BadSignature { which: char },
    /// The wire bytes did not decode to an evidence value.
    Malformed,
}

impl std::fmt::Display for EvidenceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EvidenceError::CreatorMismatch => write!(f, "blocks are by different creators"),
            EvidenceError::PositionMismatch { seq_a, seq_b } => {
                write!(f, "headers claim different slots ({seq_a} vs {seq_b})")
            }
            EvidenceError::IdenticalContent => {
                write!(f, "headers sign the same statement (no conflicting story)")
            }
            EvidenceError::BadSignature { which } => {
                write!(
                    f,
                    "header {which} signature does not verify against the accused creator"
                )
            }
            EvidenceError::Malformed => write!(f, "evidence bytes are malformed"),
        }
    }
}

impl std::error::Error for EvidenceError {}

/// **The evidence object as a wire value** (CONSENSUS-FLEX §7 item 1): two
/// signed conflicting block headers from the same author at the same position.
/// Self-contained — verification needs nothing but these bytes.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct EvidenceOfEquivocation {
    /// The accused creator's Ed25519 public key.
    pub creator: [u8; 32],
    /// The first conflicting signed header.
    pub header_a: EvidenceHeader,
    /// The second conflicting signed header.
    pub header_b: EvidenceHeader,
}

impl EvidenceOfEquivocation {
    /// Build (and fully verify) evidence from two retained blocks. Refuses
    /// cross-creator pairs and everything [`Self::verify`] refuses.
    pub fn from_blocks(a: &Block, b: &Block) -> Result<Self, EvidenceError> {
        if a.creator != b.creator {
            return Err(EvidenceError::CreatorMismatch);
        }
        let ev = Self {
            creator: a.creator,
            header_a: EvidenceHeader::from_block(a),
            header_b: EvidenceHeader::from_block(b),
        };
        ev.verify()?;
        Ok(ev)
    }

    /// Build (and fully verify) evidence from a lace-retained
    /// [`EquivocationProof`]. Returns `PositionMismatch` for the
    /// different-seq incomparable forks the lace also detects — those are
    /// not same-slot-certifiable and stay on the membership path.
    pub fn from_proof(proof: &EquivocationProof) -> Result<Self, EvidenceError> {
        Self::from_blocks(&proof.block_a, &proof.block_b)
    }

    /// **The verification rule** (CONSENSUS-FLEX §7 item 2's checklist):
    /// both signatures valid against `creator`, same slot, conflicting
    /// content. Fail-closed: any refusal means the exhibit decides nothing.
    pub fn verify(&self) -> Result<(), EvidenceError> {
        if self.header_a.seq != self.header_b.seq {
            return Err(EvidenceError::PositionMismatch {
                seq_a: self.header_a.seq,
                seq_b: self.header_b.seq,
            });
        }
        if self.header_a.payload_hash == self.header_b.payload_hash
            && self.header_a.predecessors == self.header_b.predecessors
        {
            return Err(EvidenceError::IdenticalContent);
        }
        if !self.header_a.verify_signature(&self.creator) {
            return Err(EvidenceError::BadSignature { which: 'a' });
        }
        if !self.header_b.verify_signature(&self.creator) {
            return Err(EvidenceError::BadSignature { which: 'b' });
        }
        Ok(())
    }

    /// The two conflicting block ids `(id_a, id_b)` this evidence names.
    pub fn block_ids(&self) -> (BlockId, BlockId) {
        (
            self.header_a.block_id(&self.creator),
            self.header_b.block_id(&self.creator),
        )
    }

    /// The ORDER-INSENSITIVE evidence digest — the no-double-resolve burn
    /// key. The same fork presented as `(a, b)` or `(b, a)` derives the SAME
    /// digest (the pair of block ids is sorted), so re-presenting a resolved
    /// exhibit in either order refuses identically (the trustline
    /// draw-digest discipline, `node/src/trustline_service.rs`).
    pub fn digest(&self) -> [u8; 32] {
        let (id_a, id_b) = self.block_ids();
        let (lo, hi) = if id_a.0 <= id_b.0 {
            (id_a.0, id_b.0)
        } else {
            (id_b.0, id_a.0)
        };
        let mut hasher = blake3::Hasher::new_derive_key(EVIDENCE_DIGEST_DOMAIN);
        hasher.update(&self.creator);
        hasher.update(&self.header_a.seq.to_le_bytes());
        hasher.update(&lo);
        hasher.update(&hi);
        *hasher.finalize().as_bytes()
    }

    /// Wire-encode (postcard, the [`Block::to_bytes`] codec discipline).
    pub fn to_bytes(&self) -> Vec<u8> {
        postcard::to_stdvec(self).expect("evidence serialization should not fail")
    }

    /// Wire-decode. `None` on malformed bytes (fail-closed).
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        postcard::from_bytes(bytes).ok()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::finality::Payload;
    use ed25519_dalek::SigningKey;

    fn key(seed: u8) -> SigningKey {
        SigningKey::from_bytes(&[seed; 32])
    }

    fn fork(seed: u8, seq: u64) -> (Block, Block) {
        let k = key(seed);
        let a = Block::new(&k, seq, Payload::Data(b"story A".to_vec()), vec![]);
        let b = Block::new(&k, seq, Payload::Data(b"story B".to_vec()), vec![]);
        (a, b)
    }

    #[test]
    fn valid_same_slot_fork_verifies_and_roundtrips() {
        let (a, b) = fork(7, 3);
        let ev = EvidenceOfEquivocation::from_blocks(&a, &b).expect("real fork certifies");
        ev.verify().expect("verifies");
        // ids match the full blocks' ids — the header IS the block, lace-free.
        assert_eq!(ev.block_ids(), (a.id(), b.id()));
        // wire roundtrip is the identity.
        let decoded = EvidenceOfEquivocation::from_bytes(&ev.to_bytes()).expect("decodes");
        assert_eq!(decoded, ev);
        decoded.verify().expect("decoded evidence still verifies");
    }

    #[test]
    fn digest_is_order_insensitive() {
        let (a, b) = fork(9, 5);
        let ev_ab = EvidenceOfEquivocation::from_blocks(&a, &b).unwrap();
        let ev_ba = EvidenceOfEquivocation::from_blocks(&b, &a).unwrap();
        assert_eq!(
            ev_ab.digest(),
            ev_ba.digest(),
            "the same fork presented in either order burns the same digest"
        );
        // and a DIFFERENT fork derives a different digest.
        let (c, d) = fork(9, 6);
        let other = EvidenceOfEquivocation::from_blocks(&c, &d).unwrap();
        assert_ne!(ev_ab.digest(), other.digest());
    }

    #[test]
    fn forged_signature_refuses() {
        let (a, mut b) = fork(11, 2);
        // forge: replace b's signature with one made by a DIFFERENT key over
        // the same content.
        let attacker = key(99);
        let content = Block::signing_content_from_payload_hash(
            &b.creator,
            b.seq,
            blake3::hash(&Block::payload_bytes(&b.payload)).as_bytes(),
            &b.predecessors,
        );
        use ed25519_dalek::Signer;
        b.signature = attacker.sign(&content).to_bytes();
        assert_eq!(
            EvidenceOfEquivocation::from_blocks(&a, &b),
            Err(EvidenceError::BadSignature { which: 'b' }),
            "a forged exhibit must not certify"
        );
    }

    #[test]
    fn same_payload_refuses() {
        let k = key(13);
        let a = Block::new(&k, 4, Payload::Data(b"same story".to_vec()), vec![]);
        // identical content (payload AND predecessors) — even if the creator
        // re-signed it, there is no conflicting story.
        let b = a.clone();
        assert_eq!(
            EvidenceOfEquivocation::from_blocks(&a, &b),
            Err(EvidenceError::IdenticalContent)
        );
    }

    #[test]
    fn different_positions_refuse() {
        let k = key(17);
        let a = Block::new(&k, 1, Payload::Data(b"x".to_vec()), vec![]);
        let b = Block::new(&k, 2, Payload::Data(b"y".to_vec()), vec![]);
        assert_eq!(
            EvidenceOfEquivocation::from_blocks(&a, &b),
            Err(EvidenceError::PositionMismatch { seq_a: 1, seq_b: 2 })
        );
    }

    #[test]
    fn cross_creator_refuses() {
        let a = Block::new(&key(19), 1, Payload::Data(b"x".to_vec()), vec![]);
        let b = Block::new(&key(23), 1, Payload::Data(b"y".to_vec()), vec![]);
        assert_eq!(
            EvidenceOfEquivocation::from_blocks(&a, &b),
            Err(EvidenceError::CreatorMismatch)
        );
    }

    #[test]
    fn malformed_bytes_fail_decode() {
        assert!(EvidenceOfEquivocation::from_bytes(b"not evidence").is_none());
        assert!(EvidenceOfEquivocation::from_bytes(&[]).is_none());
    }

    #[test]
    fn lace_retained_proof_converts() {
        // The live pipe: the lace detects the fork, retains the proof, and
        // the proof reduces to the wire value.
        let (a, b) = fork(29, 1);
        let mut lace = crate::finality::Blocklace::new_simple(key(1));
        lace.receive_block(a.clone()).expect("first block inserts");
        let err = lace.receive_block(b.clone()).expect_err("fork detected");
        let crate::finality::BlockError::Equivocation { proof, .. } = err else {
            panic!("expected equivocation, got {err:?}");
        };
        let ev = EvidenceOfEquivocation::from_proof(&proof).expect("retained proof certifies");
        ev.verify().expect("wire value verifies lace-free");
        assert_eq!(ev.creator, a.creator);
    }
}
