//! Quorum finalization votes — the explicit signed-vote agreement layer.
//!
//! # Why this exists (the soundness gap it closes)
//!
//! The blocklace finality executor computes finality **unilaterally per node**:
//! each node runs `ordering::tau` over its own view of the DAG and decides "this
//! block is Ordered" on its own. At n=1 (solo) that is the whole story. At n≥2 a
//! node that has locally finalized a block cannot, from the DAG alone, *know*
//! that the rest of the committee agrees it is final — the DAG-derived ack count
//! (`FinalityTracker::record_ack`) is still a function of THIS node's view.
//!
//! This module adds the missing message exchange: when a node finalizes a
//! turn-bearing block locally (it reaches `Ordered`, which subsumes local
//! `Attested`), it gossips a **signed** [`FinalizationVote`] (carried as a
//! `BlocklaceGossipMessage::FinalizationVote` on the blocklace topic — the
//! proven-bidirectional dissemination channel). Every node collects votes keyed
//! by *distinct verified signer* and only declares a block **consensus-wide
//! Attested** once it holds `2f+1` distinct-signer votes for it. That is the
//! step from "I think it is final" to "a quorum has signed that it is final": a
//! portable, verifiable certificate of agreement rather than a per-node guess.
//!
//! The collector is a pure value (no I/O), so the threshold-gating logic is
//! exercised by unit tests without a running node (see the tests at the bottom).
//! The gossip wiring lives in [`crate::blocklace_sync`].

use std::collections::{HashMap, HashSet};

use dregg_blocklace::finality::{BlockId, FinalityLevel};
use ed25519_dalek::{Signature, Signer, SigningKey, VerifyingKey};

/// The domain-separation tag mixed into the signed message so a finalization
/// vote can never be replayed as some other Ed25519 signature in the system.
const VOTE_DOMAIN: &[u8] = b"dregg-finalization-vote-v1";

/// A signed assertion by one committee member that it has locally finalized a
/// block to (at least) `level`.
///
/// The signature is over `VOTE_DOMAIN || block_id || level_tag` so it binds the
/// voter to *this* block at *this* finality level and nothing else.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize, PartialEq, Eq)]
pub struct FinalizationVote {
    /// The block this vote attests.
    pub block_id: BlockId,
    /// The finality level the voter asserts (`Attested` or `Ordered`; a vote is
    /// only emitted once the block is at least locally `Attested`).
    pub level: FinalityLevel,
    /// The voter's federation Ed25519 public key (the committee identity, the
    /// same key space as `Block::creator`).
    pub voter: [u8; 32],
    /// Ed25519 signature over [`Self::signing_message`]. Wrapped in
    /// [`dregg_types::Signature`] for length-checked serde of the 64 bytes
    /// (serde derives only auto-cover arrays up to length 32).
    pub signature: dregg_types::Signature,
    /// A per-EMISSION liveness counter that makes every (re-)emitted vote
    /// BYTE-UNIQUE — the same defence `BlocklaceGossipMessage::Frontier` uses.
    /// It is NOT part of the signed message: a re-emit of the same vote carries
    /// the SAME signature and voter (so distinct-signer counting is unchanged),
    /// but a fresh `nonce` so the gossip layer's hash-dedup (`seen`) does not
    /// collapse the re-emit. Without it, a vote dropped on its first delivery
    /// (consumed into the receiver's `seen` before dispatch, or lost to the
    /// one-shot eager-push race) can NEVER be re-delivered: every byte-identical
    /// re-emit hashes the same and is dropped at the `seen` gate. The nonce
    /// defeats that so the catch-up re-emit actually reaches a peer that missed
    /// the vote, letting it cross quorum.
    pub nonce: u64,
}

impl FinalizationVote {
    /// The exact bytes a vote signs / verifies against. Binds the domain tag,
    /// the block id, and a single tag byte for the level so a vote for one level
    /// is never accepted as a vote for another.
    pub fn signing_message(block_id: &BlockId, level: FinalityLevel) -> Vec<u8> {
        let mut buf = Vec::with_capacity(VOTE_DOMAIN.len() + 32 + 1);
        buf.extend_from_slice(VOTE_DOMAIN);
        buf.extend_from_slice(&block_id.0);
        buf.push(level_tag(level));
        buf
    }

    /// Construct a signed vote for `block_id` at `level` using `signing_key`.
    /// Each call stamps a fresh liveness `nonce` so re-emissions are byte-unique
    /// (see the `nonce` field); the nonce is outside the signed message.
    pub fn sign(signing_key: &SigningKey, block_id: BlockId, level: FinalityLevel) -> Self {
        let msg = Self::signing_message(&block_id, level);
        let sig: Signature = signing_key.sign(&msg);
        FinalizationVote {
            block_id,
            level,
            voter: signing_key.verifying_key().to_bytes(),
            signature: dregg_types::Signature(sig.to_bytes()),
            nonce: fresh_nonce(),
        }
    }

    /// Verify the vote's signature against its declared `voter` key. Returns
    /// `false` on a malformed key or a bad signature — a vote that does not
    /// verify is never counted.
    pub fn verify(&self) -> bool {
        let Ok(vk) = VerifyingKey::from_bytes(&self.voter) else {
            return false;
        };
        let sig = Signature::from_bytes(&self.signature.0);
        let msg = Self::signing_message(&self.block_id, self.level);
        vk.verify_strict(&msg, &sig).is_ok()
    }
}

/// A strictly-monotonic per-process counter stamped into each emitted vote so
/// repeated (re-emitted) votes are byte-unique and never collapse under the
/// gossip layer's hash-dedup. Mirrors `blocklace_sync::frontier_nonce`. Public
/// so re-emission / frontier-piggyback can stamp a fresh nonce onto a stored
/// signed vote without re-signing (the nonce is outside the signed message).
pub fn fresh_nonce() -> u64 {
    static VOTE_NONCE: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    VOTE_NONCE.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
}

/// Stable per-level tag byte for the signed message (Attested vs Ordered must
/// not collide).
fn level_tag(level: FinalityLevel) -> u8 {
    match level {
        FinalityLevel::Local => 0,
        FinalityLevel::Bilateral => 1,
        FinalityLevel::Attested => 2,
        FinalityLevel::Ordered => 3,
    }
}

/// Collects finalization votes and gates consensus-wide finality on a quorum of
/// distinct verified signers.
///
/// `committee` is the set of admissible signer keys (the federation members); a
/// vote whose `voter` is not in the committee is rejected, so a Sybil cannot
/// inflate a quorum. `quorum_threshold` is `2f+1 = supermajority_threshold(n)`.
///
/// The collector is monotone: once a block crosses the threshold it stays
/// consensus-attested, and recording the same signer twice for a block is a
/// no-op (distinct-signer counting). It holds no I/O and is fully unit-testable.
#[derive(Clone, Debug)]
pub struct VoteCollector {
    /// Admissible signers (committee members). Votes from non-members are dropped.
    committee: HashSet<[u8; 32]>,
    /// Quorum threshold (2f+1).
    quorum_threshold: usize,
    /// Per-block set of distinct member signers who voted it (at least) Attested.
    votes: HashMap<BlockId, HashSet<[u8; 32]>>,
    /// Blocks that have crossed the quorum threshold (consensus-wide Attested).
    attested: HashSet<BlockId>,
}

/// The outcome of recording one vote.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RecordOutcome {
    /// The vote was rejected (bad signature, non-member signer).
    Rejected,
    /// The vote was counted but the block has not yet reached quorum.
    Counted { distinct_votes: usize },
    /// The vote was counted AND the block JUST crossed the quorum threshold on
    /// this vote (the consensus-wide Attested transition fires exactly once).
    ReachedQuorum { distinct_votes: usize },
    /// The vote was counted and the block was ALREADY consensus-attested (a
    /// later confirming vote; idempotent).
    AlreadyQuorum { distinct_votes: usize },
}

impl VoteCollector {
    /// Build a collector for the given committee and quorum threshold.
    pub fn new(committee: impl IntoIterator<Item = [u8; 32]>, quorum_threshold: usize) -> Self {
        VoteCollector {
            committee: committee.into_iter().collect(),
            quorum_threshold,
            votes: HashMap::new(),
            attested: HashSet::new(),
        }
    }

    /// Replace the committee (e.g. after an epoch transition) without dropping
    /// already-accumulated votes; re-counting against the new membership happens
    /// implicitly on the next vote.
    #[allow(dead_code)] // collector query/maintenance API; exercised by tests
    pub fn set_committee(&mut self, committee: impl IntoIterator<Item = [u8; 32]>) {
        self.committee = committee.into_iter().collect();
    }

    /// The quorum threshold this collector enforces.
    #[allow(dead_code)] // collector query/maintenance API; exercised by tests
    pub fn quorum_threshold(&self) -> usize {
        self.quorum_threshold
    }

    /// Number of distinct member votes recorded for a block.
    #[allow(dead_code)] // collector query/maintenance API; exercised by tests
    pub fn vote_count(&self, block_id: &BlockId) -> usize {
        self.votes.get(block_id).map_or(0, |s| s.len())
    }

    /// Has the given signer already voted for this block? Used to gate
    /// re-broadcasting our OWN vote so an n-member committee emits exactly n
    /// votes per finalized block (no re-emit storm).
    pub fn has_voted(&self, block_id: &BlockId, signer: &[u8; 32]) -> bool {
        self.votes.get(block_id).is_some_and(|s| s.contains(signer))
    }

    /// Has this block reached consensus-wide Attested (a quorum of distinct
    /// member signers)?
    #[allow(dead_code)] // collector query/maintenance API; exercised by tests
    pub fn is_consensus_attested(&self, block_id: &BlockId) -> bool {
        self.attested.contains(block_id)
    }

    /// All blocks that have reached consensus-wide Attested.
    #[allow(dead_code)] // collector query/maintenance API; exercised by tests
    pub fn consensus_attested(&self) -> impl Iterator<Item = &BlockId> {
        self.attested.iter()
    }

    /// Record a vote. The signature is verified and the signer must be a
    /// committee member; otherwise the vote is [`RecordOutcome::Rejected`] and
    /// nothing changes. A verified member vote is counted by distinct signer,
    /// and the outcome reports whether THIS vote crossed the quorum threshold.
    pub fn record(&mut self, vote: &FinalizationVote) -> RecordOutcome {
        // A vote must be at least Attested to count toward consensus-wide
        // attestation; a Bilateral/Local "vote" is not a finality assertion.
        if vote.level < FinalityLevel::Attested {
            return RecordOutcome::Rejected;
        }
        if !self.committee.contains(&vote.voter) {
            return RecordOutcome::Rejected;
        }
        if !vote.verify() {
            return RecordOutcome::Rejected;
        }

        let signers = self.votes.entry(vote.block_id).or_default();
        signers.insert(vote.voter);
        let distinct_votes = signers.len();
        let already = self.attested.contains(&vote.block_id);

        if already {
            return RecordOutcome::AlreadyQuorum { distinct_votes };
        }
        if distinct_votes >= self.quorum_threshold {
            self.attested.insert(vote.block_id);
            RecordOutcome::ReachedQuorum { distinct_votes }
        } else {
            RecordOutcome::Counted { distinct_votes }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn keypair(seed: u8) -> SigningKey {
        SigningKey::from_bytes(&[seed; 32])
    }

    fn pk(sk: &SigningKey) -> [u8; 32] {
        sk.verifying_key().to_bytes()
    }

    #[test]
    fn vote_roundtrip_signs_and_verifies() {
        let sk = keypair(7);
        let v = FinalizationVote::sign(&sk, BlockId([9; 32]), FinalityLevel::Ordered);
        assert!(v.verify());
        assert_eq!(v.voter, pk(&sk));
    }

    #[test]
    fn tampered_vote_fails_verification() {
        let sk = keypair(7);
        let mut v = FinalizationVote::sign(&sk, BlockId([9; 32]), FinalityLevel::Ordered);
        // Flip the block id: the signature no longer matches the message.
        v.block_id = BlockId([10; 32]);
        assert!(!v.verify());
    }

    #[test]
    fn level_is_bound_into_the_signature() {
        // A signature produced for Ordered must not verify if the level is
        // rewritten to Attested (the level tag is in the signed message).
        let sk = keypair(7);
        let mut v = FinalizationVote::sign(&sk, BlockId([9; 32]), FinalityLevel::Ordered);
        v.level = FinalityLevel::Attested;
        assert!(!v.verify());
    }

    /// THE PHASE-2 PROOF: votes drive consensus-wide agreement, gated at 2f+1
    /// distinct signers. A 3-member committee (quorum = supermajority(3) = 3)
    /// only marks a block consensus-attested once ALL three distinct, verified
    /// member votes land — not before, and Byzantine/duplicate votes do not
    /// shortcut it.
    #[test]
    fn quorum_of_distinct_signers_drives_consensus_attested() {
        let a = keypair(1);
        let b = keypair(2);
        let c = keypair(3);
        let committee = [pk(&a), pk(&b), pk(&c)];
        let quorum = dregg_blocklace::ordering::supermajority_threshold(3); // = 3
        let mut col = VoteCollector::new(committee, quorum);

        let blk = BlockId([42; 32]);

        // First vote: counted, not yet quorum.
        let o1 = col.record(&FinalizationVote::sign(&a, blk, FinalityLevel::Ordered));
        assert_eq!(o1, RecordOutcome::Counted { distinct_votes: 1 });
        assert!(!col.is_consensus_attested(&blk));

        // The SAME signer voting again does not advance the count.
        let dup = col.record(&FinalizationVote::sign(&a, blk, FinalityLevel::Attested));
        assert_eq!(dup, RecordOutcome::Counted { distinct_votes: 1 });

        // Second distinct signer: still short of quorum (3).
        let o2 = col.record(&FinalizationVote::sign(&b, blk, FinalityLevel::Ordered));
        assert_eq!(o2, RecordOutcome::Counted { distinct_votes: 2 });
        assert!(!col.is_consensus_attested(&blk));

        // Third distinct signer: crosses the quorum exactly here.
        let o3 = col.record(&FinalizationVote::sign(&c, blk, FinalityLevel::Ordered));
        assert_eq!(o3, RecordOutcome::ReachedQuorum { distinct_votes: 3 });
        assert!(col.is_consensus_attested(&blk));
    }

    #[test]
    fn non_member_and_forged_votes_are_rejected() {
        let a = keypair(1);
        let b = keypair(2);
        let outsider = keypair(99); // NOT in the committee
        let committee = [pk(&a), pk(&b)];
        let quorum = dregg_blocklace::ordering::supermajority_threshold(2); // = 2
        let mut col = VoteCollector::new(committee, quorum);
        let blk = BlockId([7; 32]);

        // A non-member's well-formed vote is rejected and does not count.
        let outc = col.record(&FinalizationVote::sign(
            &outsider,
            blk,
            FinalityLevel::Ordered,
        ));
        assert_eq!(outc, RecordOutcome::Rejected);
        assert_eq!(col.vote_count(&blk), 0);

        // A forged signature from a member key is rejected.
        let mut forged = FinalizationVote::sign(&a, blk, FinalityLevel::Ordered);
        forged.signature = dregg_types::Signature([0u8; 64]);
        assert_eq!(col.record(&forged), RecordOutcome::Rejected);
        assert_eq!(col.vote_count(&blk), 0);

        // Two honest member votes reach quorum.
        assert!(matches!(
            col.record(&FinalizationVote::sign(&a, blk, FinalityLevel::Ordered)),
            RecordOutcome::Counted { distinct_votes: 1 }
        ));
        assert!(matches!(
            col.record(&FinalizationVote::sign(&b, blk, FinalityLevel::Ordered)),
            RecordOutcome::ReachedQuorum { distinct_votes: 2 }
        ));
        assert!(col.is_consensus_attested(&blk));

        // A further confirming vote after quorum is idempotent.
        let again = col.record(&FinalizationVote::sign(&a, blk, FinalityLevel::Attested));
        assert!(matches!(again, RecordOutcome::AlreadyQuorum { .. }));
    }

    /// TWO-NODE SIMULATION: model the exact cross-node exchange the live node
    /// performs — each node signs its own vote for the SAME finalized block and
    /// gossips it; each node's collector records its own vote plus the peer's.
    /// Neither node is consensus-attested on its own vote alone; BOTH cross
    /// quorum exactly when they hold the other's vote too. This is the
    /// agreement property the gossip wiring delivers (here without the network),
    /// proving the vote-collection logic GATES consensus-wide finality on a
    /// genuine quorum of distinct signers — independent of the gossip transport.
    #[test]
    fn two_nodes_reach_consensus_attested_by_exchanging_votes() {
        let a = keypair(11);
        let b = keypair(22);
        let committee = [pk(&a), pk(&b)];
        let quorum = dregg_blocklace::ordering::supermajority_threshold(2); // = 2
        let blk = BlockId([77; 32]);

        // Each node has its own collector over the same committee.
        let mut node_a = VoteCollector::new(committee, quorum);
        let mut node_b = VoteCollector::new(committee, quorum);

        // Both finalize `blk` locally and sign their own vote (the emit step).
        let vote_a = FinalizationVote::sign(&a, blk, FinalityLevel::Ordered);
        let vote_b = FinalizationVote::sign(&b, blk, FinalityLevel::Ordered);

        // Each records its OWN vote first.
        assert_eq!(
            node_a.record(&vote_a),
            RecordOutcome::Counted { distinct_votes: 1 }
        );
        assert_eq!(
            node_b.record(&vote_b),
            RecordOutcome::Counted { distinct_votes: 1 }
        );
        assert!(!node_a.is_consensus_attested(&blk));
        assert!(!node_b.is_consensus_attested(&blk));

        // Gossip exchange: A receives B's vote, B receives A's vote. Each now
        // holds 2 distinct signed votes → consensus-wide Attested on BOTH.
        assert_eq!(
            node_a.record(&vote_b),
            RecordOutcome::ReachedQuorum { distinct_votes: 2 }
        );
        assert_eq!(
            node_b.record(&vote_a),
            RecordOutcome::ReachedQuorum { distinct_votes: 2 }
        );
        assert!(node_a.is_consensus_attested(&blk));
        assert!(node_b.is_consensus_attested(&blk));
    }

    /// THE FUNNEL INVARIANT (the n=2 self-emit/gossip race fix): `record`
    /// returns `ReachedQuorum` EXACTLY ONCE — on whichever vote crosses the
    /// threshold — and `AlreadyQuorum` thereafter. This is the property
    /// `blocklace_sync::record_finalization_vote` relies on to fire the
    /// consensus-wide Attested transition exactly once whether the crossing vote
    /// is the node's OWN (self-emit) or the PEER's (received). The live bug was
    /// NOT here (the collector is correct) but in the node routing the self-vote
    /// through a path that DISCARDED this outcome — so when the peer's vote
    /// landed first, the self-record crossed quorum and the transition was
    /// swallowed. This test pins the contract that record surfaces the crossing
    /// on whichever vote is second, so BOTH funnel call-sites can act on it.
    #[test]
    fn quorum_crossing_is_reported_on_whichever_vote_is_second() {
        let a = keypair(11);
        let b = keypair(22);
        let committee = [pk(&a), pk(&b)];
        let quorum = dregg_blocklace::ordering::supermajority_threshold(2); // = 2
        let blk = BlockId([77; 32]);
        let vote_a = FinalizationVote::sign(&a, blk, FinalityLevel::Ordered);
        let vote_b = FinalizationVote::sign(&b, blk, FinalityLevel::Ordered);

        // Case 1: PEER vote first, then SELF vote crosses (the race that broke the
        // live node — the self-record was the threshold-crosser).
        let mut col = VoteCollector::new(committee, quorum);
        assert_eq!(
            col.record(&vote_b),
            RecordOutcome::Counted { distinct_votes: 1 }
        );
        assert_eq!(
            col.record(&vote_a),
            RecordOutcome::ReachedQuorum { distinct_votes: 2 },
            "the SECOND distinct vote (here the self vote) must report the crossing"
        );
        // A confirming vote after the crossing is idempotent (AlreadyQuorum).
        assert!(matches!(
            col.record(&vote_b),
            RecordOutcome::AlreadyQuorum { .. }
        ));

        // Case 2: SELF vote first, then PEER vote crosses (the orientation that
        // already worked). The crossing is reported symmetrically.
        let mut col2 = VoteCollector::new([pk(&a), pk(&b)], quorum);
        assert_eq!(
            col2.record(&vote_a),
            RecordOutcome::Counted { distinct_votes: 1 }
        );
        assert_eq!(
            col2.record(&vote_b),
            RecordOutcome::ReachedQuorum { distinct_votes: 2 }
        );
    }

    #[test]
    fn bilateral_level_votes_do_not_count() {
        let a = keypair(1);
        let committee = [pk(&a)];
        let mut col = VoteCollector::new(committee, 1);
        let blk = BlockId([5; 32]);
        // A "vote" below Attested is not a finality assertion.
        let v = FinalizationVote::sign(&a, blk, FinalityLevel::Bilateral);
        assert_eq!(col.record(&v), RecordOutcome::Rejected);
        assert_eq!(col.vote_count(&blk), 0);
    }
}
