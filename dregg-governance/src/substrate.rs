//! # The executor substrate — the constitution face over the CANONICAL engine
//!
//! The reconciliation of the two `VoteEngine`s (the census's weld #2,
//! `docs/FINDING-chain-participation-census.md` §5): **`collective-choice`'s
//! executor-backed engine is the canonical vote substrate**, and this module
//! runs `dregg-governance`'s constitution face — proposal → committee vote →
//! 2n/3+1 threshold → auto-enact — over it.
//!
//! What each accepted vote here IS: a real ballot-cap turn on the embedded
//! verified executor. Eligibility is holding a ballot cap (minted only to an
//! electorate member); one-vote is the ballot's `WriteOnce(VOTE)` + the
//! nullifier set; the tally is `Monotonic` poll-cell slots; and the
//! constitutional threshold is an in-cell **per-option `AffineLe` gate**
//! ([`collective_choice::CollectiveChoice::open_poll_gated`]):
//! `required·RESOLVED − TALLY_APPROVE ≤ 0`, so the decision-turn itself cannot
//! commit until APPROVE reaches the constitutional `required_votes_for`
//! (the 2n/3+1 supermajority, honoring the H-rule).
//!
//! Two gates provably agree, exactly as in the in-memory face: every accepted
//! cast mirrors into the REAL distinct-voter
//! [`dregg_blocklace::constitution::VoteTracker`], and
//! [`ExecutorEnactReactor::react`] enacts only when BOTH the executor's
//! decision-turn committed AND the constitution reports the proposal passed.
//! Fail-closed below quorum: the executor refuses the decision-turn, the
//! reactor produces [`EnactOutcome::NoReaction`], nothing is enacted.

use std::collections::HashMap;

use dregg_blocklace::constitution::{ConstitutionManager, MembershipProposal, MembershipVote};
use dregg_blocklace::finality::BlockId;

use collective_choice::{
    CollectiveChoice as ExecutorEngine, Decision, PollId as ExecutorPollId,
    PollSpec as ExecutorPollSpec, Tally as ExecutorTally, TurnReceipt,
    VoteEngine as ExecutorVoteEngine, VoteError,
};

use crate::VoterId;
use crate::governance::DEFAULT_TIMEOUT_WAVES;
use crate::reactor::EnactOutcome;

/// The `reject` option index on an executor-backed governance poll.
pub const EXEC_REJECT: usize = 0;
/// The `approve` option index on an executor-backed governance poll (the gated
/// option — the constitutional threshold gate watches THIS tally slot).
pub const EXEC_APPROVE: usize = 1;

/// A federation governing itself over the CANONICAL executor-backed engine:
/// the real [`ConstitutionManager`] (the authority for membership, threshold,
/// and enactment) plus [`collective_choice::CollectiveChoice`] (the substrate
/// every ballot is a verified turn on).
///
/// The executor twin of [`crate::governance::FederationGovernance`] — same
/// face (propose / vote / resolve / auto-enact), different substrate: here a
/// double vote is a nullifier refusal and quorum is an in-cell `AffineLe`,
/// not in-memory bookkeeping.
pub struct ExecutorGovernance {
    /// The REAL constitutional consensus state.
    pub constitution: ConstitutionManager,
    /// The canonical executor-backed vote engine.
    pub engine: ExecutorEngine,
    /// Open governance polls → the constitution proposal block they enact.
    proposals: HashMap<ExecutorPollId, (BlockId, MembershipProposal)>,
}

impl ExecutorGovernance {
    /// Stand up a federation of `participants` under a fresh constitution, with
    /// its own embedded executor as the vote substrate.
    pub fn new(participants: Vec<VoterId>) -> Self {
        let federation_id = federation_id(&participants);
        ExecutorGovernance {
            constitution: ConstitutionManager::from_participants(
                participants,
                DEFAULT_TIMEOUT_WAVES,
            ),
            engine: ExecutorEngine::new(federation_id),
            proposals: HashMap::new(),
        }
    }

    /// The current committee (the constitution's participant set).
    pub fn committee(&self) -> Vec<VoterId> {
        self.constitution.participants().to_vec()
    }

    /// Open a governance proposal: register it with the real constitution and
    /// open the matching `{reject, approve}` poll on the executor engine, with
    /// the constitutional `required_votes_for` baked in as the per-option
    /// `AffineLe` gate on the APPROVE tally.
    pub fn propose(
        &mut self,
        proposal_block: BlockId,
        proposal: MembershipProposal,
        question: &str,
    ) -> Result<ExecutorPollId, VoteError> {
        // The constitutional threshold for THIS proposal (encodes 2n/3+1 and
        // the H-rule for a threshold amendment).
        let required = self.constitution.current.required_votes_for(&proposal) as u64;

        let spec = ExecutorPollSpec {
            question: question.into(),
            options: vec!["reject".into(), "approve".into()],
            electorate: self.committee(),
            quorum_m: required,
        };
        // Gate on APPROVE: the decision-turn cannot commit until the APPROVE
        // tally itself reaches `required` — `required` REJECT ballots never
        // arm RESOLVED.
        let poll = self.engine.open_poll_gated(spec, EXEC_APPROVE)?;

        // Register with the constitution only after the poll actually opened,
        // so a refused spec leaves the constitution untouched.
        self.constitution
            .submit_proposal(proposal_block, proposal.clone());
        self.proposals.insert(poll, (proposal_block, proposal));
        Ok(poll)
    }

    /// A committee member casts an approve/reject ballot **as a real
    /// ballot-cap turn** on the embedded executor.
    ///
    /// - A non-committee voter holds no ballot cap → [`VoteError::Ineligible`].
    /// - A second ballot from the same voter → [`VoteError::DoubleVote`] (the
    ///   nullifier / `WriteOnce(VOTE)` depths).
    /// - An accepted cast mirrors into the REAL distinct-voter `VoteTracker`,
    ///   so the executor tally and the constitutional tally are the same count.
    pub fn vote(
        &mut self,
        poll: ExecutorPollId,
        voter: VoterId,
        approve: bool,
    ) -> Result<TurnReceipt, VoteError> {
        // Eligibility gate: `issue_ballot` refuses a voter outside the poll's
        // electorate (idempotent for one already holding a ballot).
        let cap = self.engine.issue_ballot(poll, voter)?;
        let option = if approve { EXEC_APPROVE } else { EXEC_REJECT };
        let receipt = self.engine.cast(poll, &cap, option)?;

        // Mirror into the real constitution ONLY after the executor accepted
        // (so a refused turn never reaches the VoteTracker).
        if let Some((proposal_block, _)) = self.proposals.get(&poll) {
            let mv = MembershipVote {
                proposal_block: *proposal_block,
                approve,
            };
            self.constitution.submit_vote(&mv, voter);
        }
        Ok(receipt)
    }

    /// Attempt the decision-turn. `Ok(None)` while the APPROVE tally is below
    /// the constitutional threshold (the in-cell `AffineLe` refused the turn).
    pub fn resolve(&mut self, poll: ExecutorPollId) -> Result<Option<Decision>, VoteError> {
        self.engine.resolve(poll)
    }

    /// The executor's monotone tally (`[reject, approve]`).
    pub fn tally(&self, poll: ExecutorPollId) -> Result<ExecutorTally, VoteError> {
        self.engine.tally(poll)
    }

    /// The constitution proposal block a poll enacts (if any).
    pub fn proposal_block(&self, poll: ExecutorPollId) -> Option<BlockId> {
        self.proposals.get(&poll).map(|(b, _)| *b)
    }

    /// Whether the REAL constitution reports this poll's proposal as passed —
    /// the authority-side gate. By construction this agrees with the
    /// executor's decision-turn (every accepted cast mirrored a `submit_vote`).
    pub fn constitution_has_passed(&self, poll: ExecutorPollId) -> bool {
        match self.proposals.get(&poll) {
            Some((pb, _)) => self
                .constitution
                .votes
                .has_passed(pb, &self.constitution.current),
            None => false,
        }
    }
}

/// Watches an [`ExecutorGovernance`] poll and auto-enacts the proposal at
/// quorum — the executor twin of [`crate::reactor::GovernanceEnactReactor`].
///
/// Fail-closed at every step: below quorum the executor's `AffineLe` refuses
/// the decision-turn (→ [`EnactOutcome::NoReaction`]); a decided poll whose
/// winner is not APPROVE never enacts; and the real constitution's own
/// `has_passed` must independently agree before `apply_if_passed` fires.
#[derive(Clone, Copy, Debug, Default)]
pub struct ExecutorEnactReactor;

impl ExecutorEnactReactor {
    /// Attempt one reactor step against `poll`.
    pub fn react(&self, gov: &mut ExecutorGovernance, poll: ExecutorPollId) -> EnactOutcome {
        // Gate 1: the executor's decision-turn (the per-option AffineLe on the
        // APPROVE tally). Below the constitutional threshold this is a real
        // executor refusal → nothing to react to.
        let decision = match gov.engine.resolve(poll) {
            Ok(Some(d)) => d,
            _ => return EnactOutcome::NoReaction,
        };
        if decision.winner != EXEC_APPROVE {
            return EnactOutcome::NoReaction;
        }
        let proposal_block = match gov.proposal_block(poll) {
            Some(b) => b,
            None => return EnactOutcome::NoReaction,
        };
        // Gate 2: the REAL constitution's distinct-voter count must agree.
        if !gov
            .constitution
            .votes
            .has_passed(&proposal_block, &gov.constitution.current)
        {
            return EnactOutcome::NoReaction;
        }
        match gov.constitution.apply_if_passed(&proposal_block) {
            Ok(true) => EnactOutcome::Enacted {
                new_version: gov.constitution.version(),
            },
            // `Err` = the configuration step bound REFUSED the change BY NAME
            // (Lean `ConfigBoundary.classifyStep`; already logged at the
            // constitution choke point). Distinct from a proposal that has not
            // passed, but both are "not enacted" to this reactor.
            Ok(false) | Err(_) => EnactOutcome::NotApplied,
        }
    }
}

/// A stable federation id for the embedded executor, derived from the founding
/// participant set.
fn federation_id(participants: &[VoterId]) -> [u8; 32] {
    let mut h = blake3::Hasher::new_derive_key("dregg-governance-executor-federation-v1");
    h.update(&(participants.len() as u64).to_be_bytes());
    for p in participants {
        h.update(p);
    }
    *h.finalize().as_bytes()
}
