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
//!   [D] ⚑ DRAIN (D7) — a member leaves and the committee CONTINUES at the new
//!       threshold on SURVIVOR votes alone, while the crossing that would have
//!       STRADDLED the boundary (a tally meeting the new, smaller bar only
//!       because the departing member's vote was still in it) is refused. The
//!       straddle is asserted CONSTRUCTED before the verdict is read.
//!   [E] ⚑ NOTHING IS RETRACTED — a quorum that had already crossed under the
//!       old configuration keeps its tally, its pin and its assembled quorum
//!       across the leave, INCLUDING the departed member's signature.
//!
//! ⚠ [D] and [E] are the LEAVE half and they are SLOW: every vote is a real
//! ML-DSA-65 verify (376–1880 ms measured), so all five tests here — including
//! the three that predate the drain — are killed by `[profile.default]`'s
//! 45 s × 4 in a DEBUG build. Run them `--release` (`--profile full`); a timeout
//! from the default profile is a build/profile verdict, not a test verdict.

#![cfg(test)]

use std::collections::HashMap;

use dregg_blocklace::constitution::{ConstitutionManager, MembershipProposal, MembershipVote};
use dregg_blocklace::finality::{BlockId, FinalityLevel};
use dregg_blocklace::ordering::supermajority_threshold;
use dregg_federation::frost::{MlDsaPublicKey, MlDsaSigningKey};
use ed25519_dalek::SigningKey;

use crate::finalization_votes::{DrainReport, FinalizationVote, RecordOutcome, VoteCollector};

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
        // v4: the per-turn value the vote also binds. Fixed here — this harness
        // is about committee membership across an epoch boundary, and members
        // that disagreed on it would (correctly) form no quorum at all.
        Some([0x3D; 32]),
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
    /// call `apply_committee_change` makes). Returns the D7 [`DrainReport`] when
    /// the committee actually advanced on this node, `None` when it did not.
    fn drive_amendment(
        &mut self,
        proposal_block: BlockId,
        proposal: MembershipProposal,
        approvers: &[[u8; 32]],
    ) -> Option<DrainReport> {
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
        if passed && self.cm.apply_if_passed(&proposal_block).unwrap_or(false) {
            // THE LIVE COMMITTEE ADVANCE (mirrors blocklace_sync::apply_committee_change),
            // including the D7 drain that `reconfigure` runs at the install point.
            let participants: Vec<[u8; 32]> = self.cm.current.participants.clone();
            let threshold = self.cm.threshold();
            let pq = pq_for(&self.pq_published, &participants);
            Some(
                self.votes
                    .reconfigure(participants.iter().copied(), pq, threshold),
            )
        } else {
            None
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
///
/// ⚑ THIS TEST WAS RED AT HEAD BEFORE THE DRAIN LANDED, AND THE RED WAS REAL.
/// It was written in `611d104a2` over a genesis committee of THREE, so its remove
/// leg was a `4 -> 3` step. `2fce89d4a` then landed the Lean-authored configuration
/// step bound and **`4 -> 3` is REFUSED BY NAME** — `ConfigBoundary.classifyStep
/// 4 0 1 = .refuseRosterFloor`, because a 3-member roster's Byzantine budget is
/// ZERO, so shrinking a BFT-capable roster onto it buys a committee that tolerates
/// nothing. That commit shipped its own tests (`blocklace/tests/
/// membership_safety_differential.rs` asserts exactly this refusal) and left THIS
/// consumer asserting the opposite: caller committed, callee not, in the test
/// layer. `apply_if_passed` returned `Err(RosterFloor)`, `unwrap_or(false)` turned
/// it into "did not apply", and the assert had been failing ever since.
///
/// FIXED FORWARD, not by deleting the bar: the genesis committee is FOUR, the live
/// add is `4 -> 5` and the live remove is `5 -> 4` — both steps the bound admits
/// (`stepAllowed 4 1 0` and `stepAllowed 5 0 1`). The [B] bar ("a validator removed
/// live stops counting toward quorum") is unchanged; only the roster shape moved
/// to one the consensus rule permits. The refused `4 -> 3` shape now has its own
/// pole below, so nobody restores it by accident.
#[test]
fn validator_added_and_removed_live_chain_continues() {
    let a = keypair(1);
    let b = keypair(2);
    let c = keypair(3);
    let d = keypair(4);
    let e = keypair(5); // the validator added live (not in genesis)

    // Three nodes, each with its own constitution + collector over the genesis
    // committee {1,2,3,4} (quorum = supermajority(4) = 3). All five validators'
    // ML-DSA keys are published (e publishes its key when it asks to join).
    let mut nodes: Vec<Node> = (0..3)
        .map(|_| Node::new(&[1, 2, 3, 4], &[1, 2, 3, 4, 5]))
        .collect();

    // ── The chain is already running: a block finalizes under the 4-committee. ──
    let blk_pre = BlockId([100; 32]);
    let attested_pre = finalize_across(&mut nodes, &[1, 2, 3], blk_pre);
    assert!(
        attested_pre.iter().all(|x| *x),
        "the pre-transition block must finalize under the genesis committee"
    );

    // ── Before ratification, the new validator e cannot influence finality. ──
    for node in &mut nodes {
        assert!(!node.votes.is_committee_member(&pk(&e)));
        let v = signed_vote(5, BlockId([101; 32]));
        assert_eq!(
            node.votes.record(&v),
            RecordOutcome::Rejected,
            "a non-committee validator's vote must be rejected before it is admitted"
        );
    }

    // ── ADD e live: every node ratifies the Join with a quorum of the CURRENT ──
    //    committee {a,b,c,d} (supermajority(4) = 3), then advances its live
    //    committee. `4 -> 5` is an allowed step (Lean `stepAllowed 4 1 0`).
    let genesis = [pk(&a), pk(&b), pk(&c), pk(&d)];
    let join_block = BlockId([0xAA; 32]);
    let join = MembershipProposal::Join {
        node_key: pk(&e),
        justification: vec![],
    };
    for node in &mut nodes {
        let drain = node.drive_amendment(join_block, join.clone(), &genesis);
        let drain = drain.expect("the Join ratified by the current quorum must apply");
        assert!(
            drain.is_noop(),
            "a JOIN removes nobody, so the D7 drain must be inert (Lean \
             LeaveDrain.drain_join_is_identity); got {drain:?}"
        );
    }

    // Every node now carries the 5-member committee, threshold = supermajority(5) = 4.
    for node in &nodes {
        assert_eq!(node.cm.current.participant_count(), 5);
        assert!(node.cm.current.is_participant(&pk(&e)));
        assert_eq!(node.votes.committee_size(), 5);
        assert_eq!(node.votes.quorum_threshold(), supermajority_threshold(5));
        assert!(node.votes.is_committee_member(&pk(&e)));
    }

    // ── The chain CONTINUES — the pre-transition block stays finalized (no ──
    //    reset / fresh chain) AND a new block finalizes under the NEW committee,
    //    with the freshly-added validator e among the signers.
    for node in &nodes {
        assert!(
            node.votes.is_consensus_attested(&blk_pre),
            "a block finalized before the transition must stay finalized across it"
        );
    }
    let blk_post = BlockId([102; 32]);
    let attested_post = finalize_across(&mut nodes, &[1, 2, 3, 5], blk_post);
    assert!(
        attested_post.iter().all(|x| *x),
        "a new block must finalize under the post-transition committee (chain continues), \
         with the added validator e contributing to quorum"
    );

    // ── REMOVE e live: the now-5-member committee ratifies Leave(e) (quorum 4), ──
    //    and every node drops e again. `5 -> 4` is an allowed step.
    let leave_block = BlockId([0xBB; 32]);
    let leave = MembershipProposal::Leave {
        node_key: pk(&e),
        reason: dregg_blocklace::constitution::LeaveReason::Voluntary,
    };
    let five = [pk(&a), pk(&b), pk(&c), pk(&d), pk(&e)];
    for node in &mut nodes {
        node.drive_amendment(leave_block, leave.clone(), &five)
            .expect("the Leave ratified by the current quorum must apply");
    }
    for node in &mut nodes {
        assert_eq!(node.cm.current.participant_count(), 4);
        assert_eq!(node.votes.quorum_threshold(), supermajority_threshold(4));
        assert!(!node.cm.current.is_participant(&pk(&e)));
        assert!(!node.votes.is_committee_member(&pk(&e)));
        // e (removed) can no longer contribute to a quorum.
        let v = signed_vote(5, BlockId([103; 32]));
        assert_eq!(node.votes.record(&v), RecordOutcome::Rejected);
    }
}

/// [F] ⚑ **THE STEP BOUND REFUSES A LEAVE BY NAME, on the live multi-node path.**
///
/// The shape the test above used to assert would apply: a ratified `Leave` that
/// shrinks a 4-member committee to 3. The Lean-authored bound refuses it —
/// `ConfigBoundary.classifyStep 4 0 1 = .refuseRosterFloor` — because `f(3) = 0`:
/// the surviving roster would tolerate no faults at all, which is the teeth for
/// the NON-CONTIGUOUS leave trap (at `n = 7`, `l = 4` passes the counting bound
/// only VACUOUSLY for the same reason, while `l = 3` fails it outright).
///
/// ⚠ MUTATION ASSERTED PRESENT BEFORE THE VERDICT. A committee that did not shrink
/// because nobody voted proves nothing, so this pins that the proposal genuinely
/// REACHED QUORUM (`has_passed` under the current committee) and that the member is
/// genuinely IN the roster — and only then reads "unchanged" as a refusal. It also
/// reads the refusal's NAME off `apply_if_passed`, not merely its falsity.
#[test]
fn a_leave_that_would_breach_the_roster_floor_is_refused_by_name() {
    use dregg_blocklace::constitution::StepRefusal;

    let victim = pk(&keypair(4));
    let four = [pk(&keypair(1)), pk(&keypair(2)), pk(&keypair(3)), victim];
    let mut nodes: Vec<Node> = (0..3)
        .map(|_| Node::new(&[1, 2, 3, 4], &[1, 2, 3, 4]))
        .collect();

    let leave_block = BlockId([0xF0; 32]);
    let leave = MembershipProposal::Leave {
        node_key: victim,
        reason: dregg_blocklace::constitution::LeaveReason::Voluntary,
    };

    for node in &mut nodes {
        // MUTATION PRESENT (1/2): the member really is in the roster.
        assert!(node.cm.current.is_participant(&victim));
        node.cm.submit_proposal(leave_block, leave.clone());
        for voter in &four {
            let vote = MembershipVote {
                proposal_block: leave_block,
                approve: true,
            };
            node.cm.submit_vote(&vote, *voter);
        }
        // MUTATION PRESENT (2/2): the proposal really did reach quorum.
        assert!(
            node.cm.votes.has_passed(&leave_block, &node.cm.current),
            "the Leave must actually PASS — a refusal read off a proposal that never \
             reached quorum would be a vacuous green"
        );
        // THE VERDICT, by name.
        assert_eq!(
            node.cm.apply_if_passed(&leave_block),
            Err(StepRefusal::RosterFloor {
                roster: 4,
                survivors: 3
            }),
            "a ratified 4 -> 3 Leave must be REFUSED BY NAME, not silently applied \
             and not silently ignored"
        );
        // And NOTHING mutated: the roster, the threshold and the collector all hold.
        assert_eq!(node.cm.current.participant_count(), 4);
        assert_eq!(node.cm.threshold(), supermajority_threshold(4));
        assert!(node.cm.current.is_participant(&victim));
        assert!(node.votes.is_committee_member(&victim));
        assert_eq!(node.votes.config_seq(), 0, "no install happened");
    }
}

/// [D] ⚑ **THE DRAIN POLE (D7)** — a member leaves and the committee CONTINUES at
/// the correct threshold, on survivor votes alone; and the crossing that would
/// have STRADDLED the boundary is refused.
///
/// The shape is the one the reading doc's §5.3 hazard takes in the LEAVE
/// direction, which the `config_seq` pin (a join-direction fix) does not reach:
/// `record` counts DISTINCT RECORDED SIGNERS against the LIVE threshold, while
/// `assembled_quorum` drops any signer the governing configuration holds no key
/// for. `n = 5 → 4` moves the bar from `T(5) = 4` down to `T(4) = 3`, so a block
/// sitting at two survivor votes plus the departing member's vote — three
/// recorded signers, below the old bar — would MEET the new bar the instant the
/// leave installed, and then assemble to nothing.
///
/// ⚠ THE MUTATION IS ASSERTED PRESENT BEFORE THE VERDICT IS READ. The test first
/// pins that the departing member's vote really is in the tally and that the
/// tally really does meet the post-leave bar — i.e. that the straddle is
/// constructed, not hoped for — and only then reads the drain's verdict. Without
/// that, a harness whose setup silently stopped producing the hazard would pass
/// while checking nothing (the falsifier-that-stopped-falsifying class).
///
/// Lean: `Dregg2.Distributed.LeaveDrain` —
/// `straddle_crosses_without_drain` ∧ `straddle_unassemblable_without_drain` are
/// the two halves this constructs; `drain_closes_the_straddle` is the verdict;
/// `survivors_can_still_cross` is the continuation.
#[test]
fn leave_drains_the_departing_members_in_flight_votes_and_the_committee_continues() {
    let members: Vec<SigningKey> = (1..=5).map(keypair).collect();
    let leaver = pk(&members[4]); // seed 5 — the member that departs
    let five: Vec<[u8; 32]> = members.iter().map(pk).collect();

    let mut nodes: Vec<Node> = (0..3)
        .map(|_| Node::new(&[1, 2, 3, 4, 5], &[1, 2, 3, 4, 5]))
        .collect();
    for node in &nodes {
        assert_eq!(node.votes.quorum_threshold(), supermajority_threshold(5));
    }

    // ── A block goes IN FLIGHT: survivors 1 and 2 vote, and so does the member ──
    //    about to leave. Three recorded signers — one short of T(5) = 4.
    let blk = BlockId([0xD7; 32]);
    let in_flight = finalize_across(&mut nodes, &[1, 2, 5], blk);
    assert!(
        in_flight.iter().all(|x| !*x),
        "three votes are below T(5) = 4, so the block must NOT be attested yet"
    );

    // ⚠ MUTATION PRESENT — the straddle is really constructed:
    for node in &nodes {
        assert_eq!(node.votes.vote_count(&blk), 3, "three recorded signers");
        assert!(
            node.votes.has_voted(&blk, &leaver),
            "the DEPARTING member's vote must be in the tally — without it there is no \
             straddle to close and this test would verify nothing"
        );
        assert!(
            node.votes.vote_count(&blk) >= supermajority_threshold(4),
            "and the tally must MEET the post-leave bar T(4) = 3, so that an undrained \
             install would declare a quorum on it"
        );
        assert!(
            node.votes.assembled_quorum(&blk).is_none(),
            "it has not crossed, so nothing is assembled yet"
        );
    }

    // ── The 5-member committee ratifies Leave(5). T(5) = 4 approvals. ──
    let leave_block = BlockId([0xBE; 32]);
    let leave = MembershipProposal::Leave {
        node_key: leaver,
        reason: dregg_blocklace::constitution::LeaveReason::Voluntary,
    };
    for node in &mut nodes {
        let drain = node
            .drive_amendment(leave_block, leave.clone(), &five)
            .expect("the Leave ratified by the current quorum must apply");
        // ── THE VERDICT: the drain ran, and it closed exactly one straddle. ──
        assert_eq!(drain.departed, 1, "exactly one member left");
        assert_eq!(
            drain.votes_retired, 1,
            "the departing member's one in-flight vote must be retired"
        );
        assert_eq!(
            drain.straddles_closed, 1,
            "and it must be counted as a STRADDLE closed: the tally met the new bar only \
             because that vote was still in it"
        );
    }

    for node in &nodes {
        assert_eq!(node.cm.current.participant_count(), 4);
        assert_eq!(node.votes.quorum_threshold(), supermajority_threshold(4));
        assert!(!node.votes.is_committee_member(&leaver));
        assert_eq!(
            node.votes.vote_count(&blk),
            2,
            "the departing member's vote is GONE from the in-flight tally"
        );
        assert!(
            !node.votes.has_voted(&blk, &leaver),
            "retired, not merely un-counted"
        );
        // ⚑ THE REFUSAL: no quorum was declared on the straddling tally, and none
        // could be assembled from it either. Both, because either alone is the
        // defect: attested-with-no-assemblable-quorum is precisely the state
        // "one node has it final, another cannot reconstruct that it ever was".
        assert!(
            !node.votes.is_consensus_attested(&blk),
            "REFUSED: a quorum must never be declared out of two configurations"
        );
        assert!(
            node.votes.assembled_quorum(&blk).is_none(),
            "and nothing assembles from the drained tally either"
        );
    }

    // ── THE COMMITTEE CONTINUES at the correct threshold, on SURVIVORS ALONE. ──
    //    One more survivor vote carries the block — the obligation the drain put
    //    on the survivors, discharged (`LeaveDrain.survivors_can_still_cross`).
    let carried = finalize_across(&mut nodes, &[3], blk);
    assert!(
        carried.iter().all(|x| *x),
        "T(4) = 3 survivor votes must finalize the block after the leave — the drain \
         delays the block by one vote, it never strands it"
    );
    for node in &nodes {
        let (_pair, sigs) = node
            .votes
            .assembled_quorum(&blk)
            .expect("the survivor-only quorum must assemble");
        assert!(
            sigs.len() >= supermajority_threshold(4),
            "assembled at the NEW threshold"
        );
        assert!(
            sigs.iter().all(|s| s.voter.0 != leaver),
            "and NOT ONE signature in it belongs to the departed member — the quorum lies \
             entirely inside the new configuration (DZ §III.E same-configuration delivery, \
             Lean drained_crossing_is_assemblable)"
        );
    }

    // ── And a NEW block finalizes under the survivor committee: the federation ──
    //    kept running across the departure.
    let after = BlockId([0xD8; 32]);
    let after_attested = finalize_across(&mut nodes, &[1, 2, 3], after);
    assert!(
        after_attested.iter().all(|x| *x),
        "the committee continues after the leave"
    );
}

/// [E] ⚑ **NOTHING IS RETRACTED** — the other half of the drain rule, which is
/// what stops it from being a blunt "forget the leaver".
///
/// A block that had ALREADY crossed under the 5-member configuration keeps its
/// tally, its pin and its assembled quorum after the leave — INCLUDING the
/// departed member's signature, because that quorum is a fact about the
/// configuration that produced it and is assembled against that configuration's
/// snapshot. Retiring it would make finality lie backwards in time.
///
/// Lean: `LeaveDrain.drain_preserves_pinned`, `pinned_survives_the_boundary`.
#[test]
fn a_crossed_quorum_survives_the_leave_with_the_departed_members_signature_intact() {
    let members: Vec<SigningKey> = (1..=5).map(keypair).collect();
    let leaver = pk(&members[4]);
    let five: Vec<[u8; 32]> = members.iter().map(pk).collect();

    let mut nodes: Vec<Node> = (0..3)
        .map(|_| Node::new(&[1, 2, 3, 4, 5], &[1, 2, 3, 4, 5]))
        .collect();

    // A block CROSSES under the 5-committee with the departing member among the
    // four signers — so the pin is load-bearing rather than decorative.
    let blk = BlockId([0xC5; 32]);
    let attested = finalize_across(&mut nodes, &[1, 2, 3, 5], blk);
    assert!(attested.iter().all(|x| *x), "four votes meet T(5) = 4");
    for node in &nodes {
        assert!(
            node.votes.has_voted(&blk, &leaver),
            "mutation present: the \
            departing member is one of the four signers of the crossed quorum"
        );
        assert_eq!(node.votes.attested_config(&blk), Some(0));
    }

    let leave_block = BlockId([0xBF; 32]);
    let leave = MembershipProposal::Leave {
        node_key: leaver,
        reason: dregg_blocklace::constitution::LeaveReason::Voluntary,
    };
    for node in &mut nodes {
        let drain = node
            .drive_amendment(leave_block, leave.clone(), &five)
            .expect("the Leave must apply");
        assert_eq!(drain.departed, 1);
        assert_eq!(
            drain.votes_retired, 0,
            "an ALREADY-CROSSED tally is pinned and untouched — the drain must retire \
             nothing from it"
        );
        assert_eq!(drain.pinned_blocks, 1, "and it must be counted as pinned");
    }

    for node in &nodes {
        assert!(
            node.votes.is_consensus_attested(&blk),
            "a block finalized before the leave stays finalized across it"
        );
        assert_eq!(
            node.votes.attested_config(&blk),
            Some(0),
            "still judged against the configuration that produced it"
        );
        assert!(
            node.votes.has_voted(&blk, &leaver),
            "the departed member's signature is STILL in the tally — retirement is not \
             retroactive"
        );
        let (_pair, sigs) = node
            .votes
            .assembled_quorum(&blk)
            .expect("the pinned quorum must still assemble against config 0");
        assert!(
            sigs.iter().any(|s| s.voter.0 == leaver),
            "and the departed member's signature is part of it — that is what makes the \
             persisted quorum re-verifiable on restart"
        );
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
            advanced.is_none(),
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
