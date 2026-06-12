//! Rust differential for `Dregg2/Distributed/MembershipSafety.lean`.
//!
//! The Lean module `Dregg2.Distributed.MembershipSafety` is a FAITHFUL, EXECUTABLE model of THIS
//! crate's governed-membership / constitution rule (`src/constitution.rs`). It proves, kernel-clean:
//!
//!   * the H-rule `required_votes_for(AmendThreshold T→T') = max(T, T')` is a genuine lower bound;
//!   * threshold-recomputation correctness: after Join / Leave the threshold is exactly the
//!     supermajority `compute_threshold(n) = 2n/3 + 1` of the new participant count;
//!   * distinct-current-member admission: a passed proposal needs `required_votes_for` approvals
//!     from a `Nodup` set of keys that are all current participants.
//!
//! and ships the same `#guard` golden vectors this test re-asserts against the REAL
//! `constitution.rs` functions. AGREEMENT here is the model⟺node differential: the verified Lean
//! rule reproduces, value-for-value, the numbers the running constitution computes. (These mirror
//! the in-crate unit tests, but pinned as the cross-checked golden vectors the Lean `#guard`s
//! encode — if either side drifts, this test fails.)

use dregg_blocklace::constitution::{Constitution, MembershipProposal, compute_threshold};

const TIMEOUT: u64 = 10;

fn key(b: u8) -> [u8; 32] {
    [b; 32]
}

fn participants(n: u8) -> Vec<[u8; 32]> {
    (1..=n).map(key).collect()
}

/// `compute_threshold` golden table — matches the Lean `#guard computeThreshold _ == _`
/// at every populated size. Since the #170 quorum unification the real
/// `compute_threshold` DELEGATES to `dregg_blocklace::supermajority_threshold` (THE one
/// quorum formula), whose `n = 0` is 1 (fail-closed: an empty constitution can never
/// ratify) where the Lean transcription's `n = 0 ↦ 0` guard is 0 — pinned EXPLICITLY
/// here, same discipline as the federation diffs' `3 ∣ n` pins. Residual lane: lift
/// the Lean `computeThreshold` n=0 guard and drop this carve-out (HORIZONLOG).
#[test]
fn differential_compute_threshold_table() {
    // Lean: computeThreshold {1,3,4,7,10} == {1,3,3,5,7} — agreement for all n ≥ 1.
    assert_eq!(compute_threshold(1), 1);
    assert_eq!(compute_threshold(3), 3);
    assert_eq!(compute_threshold(4), 3);
    assert_eq!(compute_threshold(7), 5);
    assert_eq!(compute_threshold(10), 7);
    // Lean: computeThreshold 0 == 0 (vacuous); real: 1 (fail-closed, strictly
    // safe-side — no empty vote set can meet it).
    assert_eq!(compute_threshold(0), 1);
}

/// The federations carry the thresholds the Lean `fed3 / fed4 / fed1` carry.
#[test]
fn differential_federation_thresholds() {
    assert_eq!(Constitution::new(participants(3), TIMEOUT).threshold, 3); // Lean fed3.threshold
    assert_eq!(Constitution::new(participants(4), TIMEOUT).threshold, 3); // Lean fed4.threshold
    assert_eq!(Constitution::new(participants(1), TIMEOUT).threshold, 1); // Lean fed1.threshold (n=1)
}

/// H-rule golden vectors — matches the Lean
/// `requiredVotesFor {fed4 with threshold:=2} (.amendThreshold 3) == 3` and
/// `requiredVotesFor fed4 (.amendThreshold 2) == 3`.
#[test]
fn differential_h_rule_required_votes() {
    let mut c = Constitution::new(participants(4), TIMEOUT);
    c.threshold = 2;
    // amending UP 2 -> 3 needs max(2,3) = 3.
    assert_eq!(
        c.required_votes_for(&MembershipProposal::AmendThreshold { new_threshold: 3 }),
        3
    );

    let c = Constitution::new(participants(4), TIMEOUT); // threshold 3
    // amending DOWN 3 -> 2 ALSO needs max(3,2) = 3 (the current bar wins — no minority lowering).
    assert_eq!(
        c.required_votes_for(&MembershipProposal::AmendThreshold { new_threshold: 2 }),
        3
    );

    // The H-rule LOWER-BOUND property the Lean `h_rule_dominates_both` proves, exhaustively
    // exhibited: for a spread of (current, new), required >= both.
    for cur in 1..=6usize {
        for new in 1..=6usize {
            let mut cc = Constitution::new(participants(6), TIMEOUT);
            cc.threshold = cur;
            let req =
                cc.required_votes_for(&MembershipProposal::AmendThreshold { new_threshold: new });
            assert!(req >= cur, "H-rule: required {req} < current {cur}");
            assert!(req >= new, "H-rule: required {req} < new {new}");
            assert_eq!(req, cur.max(new));
        }
    }
}

/// Join threshold recompute — Lean
/// `(applyProposal fed3 (.join 4)).1.{participants.length, threshold, version} == {4, 3, 1}`,
/// and joining an existing member is a no-op.
#[test]
fn differential_join_threshold_recompute() {
    let mut c = Constitution::new(participants(3), TIMEOUT);
    let applied = c.apply_proposal(&MembershipProposal::Join {
        node_key: key(4),
        justification: vec![],
    });
    assert!(applied);
    assert_eq!(c.participant_count(), 4);
    assert_eq!(c.threshold, 3);
    assert_eq!(c.version, 1);

    // joining an existing member is a no-op (Lean: (applyProposal fed3 (.join 2)).2 == false).
    let mut c2 = Constitution::new(participants(3), TIMEOUT);
    let applied2 = c2.apply_proposal(&MembershipProposal::Join {
        node_key: key(2),
        justification: vec![],
    });
    assert!(!applied2);

    // n=1 -> n=2: peer joins, threshold rises to 2 (Lean: (applyProposal fed1 (.join 2)).threshold==2).
    let mut c1 = Constitution::new(participants(1), TIMEOUT);
    c1.apply_proposal(&MembershipProposal::Join {
        node_key: key(2),
        justification: vec![],
    });
    assert_eq!(c1.threshold, 2);
}

/// Leave threshold recompute — Lean
/// `(applyProposal fed4 (.leave 4)).1.{participants.length, threshold} == {3, 3}` and n=2 -> n=1.
#[test]
fn differential_leave_threshold_recompute() {
    let mut c = Constitution::new(participants(4), TIMEOUT);
    let applied = c.apply_proposal(&MembershipProposal::Leave {
        node_key: key(4),
        reason: dregg_blocklace::constitution::LeaveReason::Voluntary,
    });
    assert!(applied);
    assert_eq!(c.participant_count(), 3);
    assert_eq!(c.threshold, 3);

    // n=2 -> n=1: peer leaves, threshold drops to 1.
    let mut c2 = Constitution::new(participants(2), 5);
    c2.apply_proposal(&MembershipProposal::Leave {
        node_key: key(2),
        reason: dregg_blocklace::constitution::LeaveReason::Voluntary,
    });
    assert_eq!(c2.threshold, 1);
}

/// AmendThreshold validity guards — Lean
/// `(applyProposal fed4 (.amendThreshold {0,5,3})).2 == false`, `(.amendThreshold 2).2 == true`.
#[test]
fn differential_amend_threshold_guards() {
    let reject = |t: usize| {
        let mut c = Constitution::new(participants(4), TIMEOUT); // threshold 3, n=4
        !c.apply_proposal(&MembershipProposal::AmendThreshold { new_threshold: t })
    };
    assert!(reject(0)); // t = 0 rejected
    assert!(reject(5)); // t > n=4 rejected
    assert!(reject(3)); // t = current rejected

    // a valid down-amend applies.
    let mut c = Constitution::new(participants(4), TIMEOUT);
    assert!(c.apply_proposal(&MembershipProposal::AmendThreshold { new_threshold: 2 }));
    assert_eq!(c.threshold, 2);
}

/// Distinct-current-member admission on a concrete vote trace — Lean §10:
/// 3 distinct member approvals PASS the n=3 join (threshold 3); 2 FAIL; a Byzantine trace
/// (non-member + double-vote) collapses to ONE distinct approval. We use the real `VoteTracker`
/// (via `ConstitutionManager`) so the `is_participant` gate + per-proposal `HashSet<voter>` dedup
/// are exercised exactly as the node runs them.
#[test]
fn differential_distinct_member_admission() {
    use dregg_blocklace::constitution::{ConstitutionManager, MembershipVote};
    use dregg_blocklace::finality::BlockId;

    let mk = || ConstitutionManager::from_participants(participants(3), TIMEOUT); // threshold 3
    let prop_block = BlockId([0xAA; 32]);
    let join = MembershipProposal::Join {
        node_key: key(4),
        justification: vec![],
    };
    let vote = MembershipVote {
        proposal_block: prop_block,
        approve: true,
    };

    // 3 DISTINCT current-member approvals ⇒ passes (Lean: distinctApprovers .length == 3 ≥ 3).
    let mut m = mk();
    m.submit_proposal(prop_block, join.clone());
    m.submit_vote(&vote, key(1));
    m.submit_vote(&vote, key(2));
    assert_eq!(m.submit_vote(&vote, key(3)), Some(prop_block)); // reaches threshold

    // only 2 distinct approvals ⇒ FAILS (Lean: distinctApprovers votes2 .length == 2 < 3).
    let mut m2 = mk();
    m2.submit_proposal(prop_block, join.clone());
    assert_eq!(m2.submit_vote(&vote, key(1)), None);
    assert_eq!(m2.submit_vote(&vote, key(2)), None);

    // Byzantine: a NON-member (key 9) + a DOUBLE vote by member 1 ⇒ exactly ONE distinct member
    // approval (Lean: distinctApprovers votesByz == [1], length 1). Non-member dropped, dup deduped.
    let mut m3 = mk();
    m3.submit_proposal(prop_block, join);
    m3.submit_vote(&vote, key(1)); // member 1
    m3.submit_vote(&vote, key(1)); // member 1 AGAIN — deduped
    m3.submit_vote(&vote, key(9)); // NON-member — dropped by is_participant gate
    assert_eq!(m3.votes.approval_count(&prop_block), 1);
}
