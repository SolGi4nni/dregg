//! # The REAL cell-backed vote engine, behind the local seam
//!
//! [`CollectiveChoiceEngine`] adapts the canonical [`collective_choice`] engine — the
//! federation-grade voting substrate assembled from privacy-voting `WriteOnce`
//! ballots, `Monotonic` tallies, and the polis `AffineLe` quorum gate — to this
//! crate's [`VoteEngine`] seam. Wiring it in makes the crowd-vote that picks a story
//! branch **the same engine that governs a federation**: each ballot is a real
//! cap-bounded turn on a factory-born ballot cell, each tally a monotone verified
//! turn, and a decision certifies only once the quorum gate admits the `RESOLVED`
//! turn (SPWEEN-ON-DREGG §2.3 / §4.2).
//!
//! The single-poll-at-a-time [`VoteEngine`] shape maps onto the multi-poll backing
//! engine by holding the current [`PollId`] and re-opening a fresh poll each round;
//! voters are an electorate configured at construction (each voter id → a
//! deterministic public key), and casting issues (idempotently) that voter's single
//! ballot cap before exercising it.

use collective_choice::{
    CollectiveChoice, PollId, PollSpec, VoteEngine as CcVoteEngine, VoteError as CcVoteError,
};

use crate::vote::{VoteEngine, VoteError, VoteOption};

/// The federation the backing engine's ballot/tally turns commit under.
const ENGINE_FEDERATION: [u8; 32] = [0xCC; 32];

/// A voter's deterministic electorate public key (so a voter id maps to a stable
/// electorate member across rounds).
fn voter_pk(voter: &str) -> [u8; 32] {
    *blake3::hash(voter.as_bytes()).as_bytes()
}

/// **The real cell-backed [`VoteEngine`]** — every ballot and tally is a verified turn
/// on the [`collective_choice`] substrate. Construct it with the electorate (the
/// voters allowed to hold a ballot) and the quorum threshold, then drive it with
/// [`crate::run_collective`] exactly like the stub.
pub struct CollectiveChoiceEngine {
    inner: CollectiveChoice,
    /// voter id → electorate public key.
    electorate: Vec<(String, [u8; 32])>,
    quorum_m: u64,
    current: Option<PollId>,
    round: u64,
}

impl CollectiveChoiceEngine {
    /// A fresh engine over `voters` (the electorate) with quorum threshold `quorum_m`
    /// (`>= 1`; a branch resolves once `Σ votes ≥ quorum_m`).
    pub fn new(voters: &[&str], quorum_m: u64) -> Self {
        let electorate = voters
            .iter()
            .map(|v| (v.to_string(), voter_pk(v)))
            .collect();
        CollectiveChoiceEngine {
            inner: CollectiveChoice::new(ENGINE_FEDERATION),
            electorate,
            quorum_m: quorum_m.max(1),
            current: None,
            round: 0,
        }
    }

    /// The backing engine (for light-client tally / inspection).
    pub fn inner(&self) -> &CollectiveChoice {
        &self.inner
    }

    /// The currently-open poll on the backing engine, if any.
    pub fn current_poll(&self) -> Option<PollId> {
        self.current
    }

    fn pk_of(&self, voter: &str) -> Option<[u8; 32]> {
        self.electorate
            .iter()
            .find(|(id, _)| id == voter)
            .map(|(_, pk)| *pk)
    }
}

/// Map a backing-engine refusal into the local [`VoteError`].
fn map_err(e: CcVoteError) -> VoteError {
    match e {
        CcVoteError::NoSuchPoll => VoteError::NoPoll,
        CcVoteError::BadOption => VoteError::Engine("option out of range".into()),
        other => VoteError::Engine(other.to_string()),
    }
}

impl VoteEngine for CollectiveChoiceEngine {
    fn open_poll(&mut self, options: &[VoteOption]) -> Result<(), VoteError> {
        self.round += 1;
        let spec = PollSpec {
            question: format!("story-branch-{}", self.round),
            options: options.iter().map(|o| o.label.clone()).collect(),
            electorate: self.electorate.iter().map(|(_, pk)| *pk).collect(),
            quorum_m: self.quorum_m,
        };
        let poll = self.inner.open_poll(spec).map_err(map_err)?;
        self.current = Some(poll);
        Ok(())
    }

    fn cast(&mut self, voter: &str, option: usize) -> Result<(), VoteError> {
        let poll = self.current.ok_or(VoteError::NoPoll)?;
        let pk = self
            .pk_of(voter)
            .ok_or_else(|| VoteError::Engine(format!("voter `{voter}` not in electorate")))?;
        // Eligibility + single-ballot: issue (idempotently) this voter's cap, then
        // exercise it. A second vote hits the ballot's consumed nullifier and is
        // refused — the one-vote-per-ballot tooth, host-side.
        let cap = self.inner.issue_ballot(poll, pk).map_err(map_err)?;
        self.inner.cast(poll, &cap, option).map_err(map_err)?;
        Ok(())
    }

    fn tally(&self) -> Vec<u64> {
        match self.current {
            Some(poll) => self
                .inner
                .tally(poll)
                .map(|t| t.per_option)
                .unwrap_or_default(),
            None => Vec::new(),
        }
    }

    fn resolve(&mut self) -> Result<usize, VoteError> {
        let poll = self.current.ok_or(VoteError::NoPoll)?;
        match self.inner.resolve(poll).map_err(map_err)? {
            // The quorum `AffineLe` gate admitted the decision-turn.
            Some(decision) => Ok(decision.winner),
            // Below quorum: the executor refused the RESOLVED turn.
            None => Err(VoteError::Unresolvable),
        }
    }
}
