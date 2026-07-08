//! epoch_transition_e2e.rs — LIVE validator-set reconfiguration, multi-node.
//!
//! THE BIND. A federation's committee must be reconfigurable as a LIVE on-chain
//! operation — add / remove / rotate a validator while the chain (the blocklace
//! DAG + the cell state) keeps advancing — instead of the disruptive genesis
//! re-roll (new `federation_id`, restart everyone, fresh chain, re-point the
//! bot). The live wiring is two real, individually-proven pieces working
//! together on the deployed consensus path:
//!
//!   * `dregg_blocklace::constitution::ConstitutionManager` — the quorum-gated
//!     membership amendment (proposal → votes from CURRENT participants →
//!     `apply_if_passed` mutates the participant set). Proven safe by
//!     `metatheory/Dregg2/Distributed/MembershipSafety.lean` (and the federation
//!     epoch twin `EpochReconfig.lean::epoch_handoff_no_gap`).
//!   * `crate::finalization_votes::VoteCollector::reconfigure` — the LIVE
//!     consensus-committee advance the node performs (`blocklace_sync.rs
//!     ::apply_passed_proposal` → `apply_committee_change`): the finalization
//!     quorum committee + threshold follow the newly-finalized validator set, so
//!     the added validator's votes COUNT from the new epoch and a removed
//!     validator's no longer do.
//!
//! This test is the in-process, deterministic witness that those bind correctly
//! across a MULTI-NODE federation: every node runs its OWN constitution + its OWN
//! vote collector (exactly as the live node does — see
//! `blocklace_sync::BlocklaceHandle`), votes are exchanged, and the committee
//! advances on every node when (and only when) a quorum of the CURRENT committee
//! ratifies the change.
//!
//! HYBRID-PQ: every finalization vote here is signed with BOTH halves (ed25519 +
//! ML-DSA-65, same seed — the production derivation), and each node's collector
//! carries the ML-DSA committee map alongside the ed25519 set, exactly as
//! `blocklace_sync` builds it from state's genesis-published keys.
//!
//! THE BAR (hard assertions):
//!   [A] ADD — a validator added live: before ratification its finalization vote
//!       is rejected by every node; after a CURRENT-committee quorum ratifies the
//!       Join and each node reconfigures, it is a participant on every node and
//!       its vote counts. The chain CONTINUES — a block finalized BEFORE the
//!       transition stays finalized, and NEW blocks finalize under the new
//!       committee (no fresh chain, no reset).
//!   [B] REMOVE — a validator removed live stops counting toward quorum.
//!   [C] SAFETY — an UNDER-QUORUM (unauthorized) transition does NOT apply: the
//!       committee is unchanged and the would-be validator's votes stay rejected.
//!       The change is gated by the CURRENT committee's quorum, full stop.

#![cfg(test)]

use std::collections::HashMap;

use dregg_blocklace::constitution::{ConstitutionManager, MembershipProposal, MembershipVote};
use dregg_blocklace::finality::{BlockId, FinalityLevel};
use dregg_blocklace::ordering::supermajority_threshold;
use dregg_federation::frost::{MlDsaPublicKey, MlDsaSigningKey};
use ed25519_dalek::SigningKey;

use crate::finalization_votes::{FinalizationVote, RecordOutcome, VoteCollector};

const TIMEOUT_WAVES: u64 = 1000; // large: no spurious timeout-leave during the test

fn keypair(seed: u8) -> SigningKey {
    SigningKey::from_bytes(&[seed; 32])
}

fn pk(sk: &SigningKey) -> [u8; 32] {
    sk.verifying_key().to_bytes()
}

/// The seed's ML-DSA-65 keypair — derived from the SAME `[seed; 32]` as the
/// ed25519 key (the production derivation: genesis publishes the public half,
/// the node re-derives the secret from `node.key`).
fn pq_keypair(seed: u8) -> (MlDsaPublicKey, MlDsaSigningKey) {
    MlDsaSigningKey::from_seed(&[seed; 32])
}

/// Sign a HYBRID (ed25519 + ML-DSA-65) `Ordered` finalization vote as the
/// member with key seed `seed`, over the fixed test root.
fn signed_vote(seed: u8, blk: BlockId) -> FinalizationVote {
    FinalizationVote::sign(
        &keypair(seed),
        &pq_keypair(seed).1,
        blk,
        FinalityLevel::Ordered,
        [0x5A; 32],
    )
    .expect("hedged ML-DSA signing fails only on an OS-entropy failure")
}

/// One node's live consensus state: its own constitution + its own finalization
/// vote collector — exactly the two pieces `BlocklaceHandle` advances. The
/// `pq_published` map plays the role of state's genesis-published
/// `known_federation_ml_dsa_keys`: the universe of ML-DSA keys this node can
/// look a member up in when the committee reconfigures.
struct Node {
    cm: ConstitutionManager,
    votes: VoteCollector,
    pq_published: HashMap<[u8; 32], MlDsaPublicKey>,
}

/// The ML-DSA committee map for `participants`, filtered from the published
/// universe — mirrors `blocklace_sync::pq_committee_for_participants`.
fn pq_for(
    published: &HashMap<[u8; 32], MlDsaPublicKey>,
    participants: &[[u8; 32]],
) -> HashMap<[u8; 32], MlDsaPublicKey> {
    participants
        .iter()
        .filter_map(|p| published.get(p).map(|k| (*p, k.clone())))
        .collect()
}

impl Node {
    /// `committee` = the genesis ed25519 committee (from `seeds`);
    /// `published_seeds` = every validator whose ML-DSA key this node has seen
    /// published (genesis members + any validator that may join later).
    fn new(committee_seeds: &[u8], published_seeds: &[u8]) -> Self {
        let participants: Vec<[u8; 32]> =
            committee_seeds.iter().map(|&s| pk(&keypair(s))).collect();
        let pq_published: HashMap<[u8; 32], MlDsaPublicKey> = published_seeds
            .iter()
            .map(|&s| (pk(&keypair(s)), pq_keypair(s).0))
            .collect();
        let q = supermajority_threshold(participants.len());
        let pq = pq_for(&pq_published, &participants);
        Node {
            cm: ConstitutionManager::from_participants(participants.clone(), TIMEOUT_WAVES),
            votes: VoteCollector::new(participants, pq, q),
            pq_published,
        }
    }

    /// Drive ONE membership amendment through this node exactly as the live path
    /// does: register the proposal, record each approving voter, and — if it
    /// passes — `apply_if_passed` then advance the live committee
    /// (`votes.reconfigure` with the new participants' ML-DSA keys, the same
    /// call `apply_committee_change` makes). Returns whether the committee
    /// actually advanced on this node.
    fn drive_amendment(
        &mut self,
        proposal_block: BlockId,
        proposal: MembershipProposal,
        approvers: &[[u8; 32]],
    ) -> bool {
        self.cm.submit_proposal(proposal_block, proposal);
        let mut passed = false;
        for voter in approvers {
            let vote = MembershipVote {
                proposal_block,
                approve: true,
            };
            if self.cm.submit_vote(&vote, *voter).is_some() {
                passed = true;
            }
        }
        if passed && self.cm.apply_if_passed(&proposal_block) {
            // THE LIVE COMMITTEE ADVANCE (mirrors blocklace_sync::apply_committee_change).
            let participants: Vec<[u8; 32]> = self.cm.current.participants.clone();
            let threshold = self.cm.threshold();
            let pq = pq_for(&self.pq_published, &participants);
            self.votes
                .reconfigure(participants.iter().copied(), pq, threshold);
            true
        } else {
            false
        }
    }
}

/// Record a node's OWN vote plus every peer's vote for `blk`, returning whether
/// the block became consensus-attested on this node (a quorum of distinct
/// committee signers). Models the gossip exchange of finalization votes.
fn finalize_across(nodes: &mut [Node], signer_seeds: &[u8], blk: BlockId) -> Vec<bool> {
    // Every signer signs the block (hybrid); every node records every vote (gossip).
    let votes: Vec<FinalizationVote> = signer_seeds.iter().map(|&s| signed_vote(s, blk)).collect();
    let mut attested = Vec::new();
    for node in nodes.iter_mut() {
        for v in &votes {
            node.votes.record(v);
        }
        attested.push(node.votes.is_consensus_attested(&blk));
    }
    attested
}

/// [A] ADD + chain-continues, and [B] REMOVE, on a live multi-node federation.
#[test]
fn validator_added_and_removed_live_chain_continues() {
    let a = keypair(1);
    let b = keypair(2);
    let c = keypair(3);
    let d = keypair(4); // the validator added live (not in genesis)

    // Three nodes, each with its own constitution + collector over the genesis
    // committee {1,2,3} (quorum = supermajority(3) = 3). All four validators'
    // ML-DSA keys are published (d publishes its key when it asks to join).
    let mut nodes: Vec<Node> = (0..3)
        .map(|_| Node::new(&[1, 2, 3], &[1, 2, 3, 4]))
        .collect();

    // ── The chain is already running: a block finalizes under the 3-committee. ──
    let blk_pre = BlockId([100; 32]);
    let attested_pre = finalize_across(&mut nodes, &[1, 2, 3], blk_pre);
    assert!(
        attested_pre.iter().all(|x| *x),
        "the pre-transition block must finalize under the genesis committee"
    );

    // ── Before ratification, the new validator d cannot influence finality. ──
    for node in &mut nodes {
        assert!(!node.votes.is_committee_member(&pk(&d)));
        let v = signed_vote(4, BlockId([101; 32]));
        assert_eq!(
            node.votes.record(&v),
            RecordOutcome::Rejected,
            "a non-committee validator's vote must be rejected before it is admitted"
        );
    }

    // ── ADD d live: every node ratifies the Join with a quorum of the CURRENT ──
    //    committee {a,b,c} (all three approve — supermajority(3) = 3), then
    //    advances its live committee.
    let genesis = [pk(&a), pk(&b), pk(&c)];
    let join_block = BlockId([0xAA; 32]);
    let join = MembershipProposal::Join {
        node_key: pk(&d),
        justification: vec![],
    };
    for node in &mut nodes {
        let advanced = node.drive_amendment(join_block, join.clone(), &genesis);
        assert!(
            advanced,
            "the Join ratified by the current quorum must apply"
        );
    }

    // Every node now carries the 4-member committee, threshold = supermajority(4) = 3.
    for node in &nodes {
        assert_eq!(node.cm.current.participant_count(), 4);
        assert!(node.cm.current.is_participant(&pk(&d)));
        assert_eq!(node.votes.committee_size(), 4);
        assert_eq!(node.votes.quorum_threshold(), supermajority_threshold(4));
        assert!(node.votes.is_committee_member(&pk(&d)));
    }

    // ── The chain CONTINUES — the pre-transition block stays finalized (no ──
    //    reset / fresh chain) AND a new block finalizes under the NEW committee,
    //    with the freshly-added validator d among the signers.
    for node in &nodes {
        assert!(
            node.votes.is_consensus_attested(&blk_pre),
            "a block finalized before the transition must stay finalized across it"
        );
    }
    let blk_post = BlockId([102; 32]);
    let attested_post = finalize_across(&mut nodes, &[1, 2, 4], blk_post);
    assert!(
        attested_post.iter().all(|x| *x),
        "a new block must finalize under the post-transition committee (chain continues), \
         with the added validator d contributing to quorum"
    );

    // ── REMOVE d live: the now-4-member committee ratifies Leave(d) (quorum 3), ──
    //    and every node drops d again.
    let leave_block = BlockId([0xBB; 32]);
    let leave = MembershipProposal::Leave {
        node_key: pk(&d),
        reason: dregg_blocklace::constitution::LeaveReason::Voluntary,
    };
    let four = [pk(&a), pk(&b), pk(&c), pk(&d)];
    for node in &mut nodes {
        let advanced = node.drive_amendment(leave_block, leave.clone(), &four);
        assert!(
            advanced,
            "the Leave ratified by the current quorum must apply"
        );
    }
    for node in &mut nodes {
        assert_eq!(node.cm.current.participant_count(), 3);
        assert!(!node.cm.current.is_participant(&pk(&d)));
        assert!(!node.votes.is_committee_member(&pk(&d)));
        // d (removed) can no longer contribute to a quorum.
        let v = signed_vote(4, BlockId([103; 32]));
        assert_eq!(node.votes.record(&v), RecordOutcome::Rejected);
    }
}

/// [C] SAFETY — an UNDER-QUORUM transition does NOT reconfigure the committee.
///
/// A would-be validator cannot add itself (or be added) without a quorum of the
/// CURRENT committee's votes. With only 2 of the required 3 approvals, the change
/// is NOT applied: every node keeps the genesis committee and the outsider's
/// votes stay rejected. This is the gate `verify_epoch_transition` /
/// `apply_if_passed` enforce — proposing is not authority.
#[test]
fn under_quorum_transition_is_rejected() {
    let a = keypair(1);
    let b = keypair(2);
    let evil = keypair(9); // wants in without the committee's blessing

    let mut nodes: Vec<Node> = (0..3)
        .map(|_| Node::new(&[1, 2, 3], &[1, 2, 3, 9]))
        .collect();

    let join_block = BlockId([0xE0; 32]);
    let join = MembershipProposal::Join {
        node_key: pk(&evil),
        justification: vec![],
    };
    // Only TWO of the three current members approve — short of supermajority(3) = 3.
    let under_quorum = [pk(&a), pk(&b)];
    for node in &mut nodes {
        let advanced = node.drive_amendment(join_block, join.clone(), &under_quorum);
        assert!(
            !advanced,
            "an under-quorum transition must NOT advance the committee"
        );
    }

    // The committee is unchanged on every node, and `evil` is still an outsider
    // whose finalization votes are rejected.
    for node in &mut nodes {
        assert_eq!(node.cm.current.participant_count(), 3);
        assert!(!node.cm.current.is_participant(&pk(&evil)));
        assert_eq!(node.votes.committee_size(), 3);
        assert!(!node.votes.is_committee_member(&pk(&evil)));
        let v = signed_vote(9, BlockId([0xE1; 32]));
        assert_eq!(
            node.votes.record(&v),
            RecordOutcome::Rejected,
            "an unauthorized validator's votes must never count"
        );
    }
}
