//! **The quorum — no single operator owns the authority.**
//!
//! A ruling is a record; it becomes *final* only when a committee of `n` genuinely independent
//! operators super-ratifies it. This module is the `VoteEngine`-shaped core of that finality:
//! a poll is opened over a ruling's 32-byte commitment (its [`crate::Receipt::id`]), operators
//! cast ratifications, and [`RulingVoteEngine::resolve`] certifies the ruling ONLY once
//! `⌊2n/3⌋+1` distinct operators have ratified *that exact commitment*.
//!
//! The threshold is the same `supermajorityThreshold = ⌊2n/3⌋+1` as the real blocklace
//! consensus (`metatheory/Dregg2/Distributed/QuorumThreshold.lean`); the interface mirrors
//! `collective-choice::VoteEngine` (`open_poll` / `cast` / `tally` / `resolve`). This is the
//! standalone STUB of that real finality — the live independent-operator federation deploy is
//! the named operational remainder (`docs/deos/UNCENSORABLE-UTILITY.md` §4).
//!
//! ## The teeth
//!
//! * **No single operator (nor any `f = ⌊(n−1)/3⌋`-sized minority) can finalize a ruling.**
//!   Below the threshold, [`RulingVoteEngine::resolve`] returns `None` — the gate refused.
//! * **A forged ruling cannot be finalized.** A ratification of a *different* commitment than
//!   the poll's true ruling does NOT count toward its quorum: [`QuorumCommittee::tally`] counts
//!   only operators who ratified the true commitment. Even `n` operators ratifying a forged
//!   commitment never finalize the true ruling.

use std::collections::BTreeMap;

/// A poll handle.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct PollId(pub u64);

/// A finalized ruling — the true commitment plus the operators whose ratifications carried it
/// past the supermajority threshold.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Finalized {
    /// The ruling commitment ([`crate::Receipt::id`]) that reached quorum.
    pub ruling: [u8; 32],
    /// The distinct operators who ratified it (≥ the threshold).
    pub ratifiers: Vec<usize>,
}

/// Why a quorum operation refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum QuorumError {
    /// No poll with that id is open.
    NoSuchPoll,
    /// The operator index is outside `0..n` — not a committee member.
    UnknownOperator(usize),
}

impl std::fmt::Display for QuorumError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            QuorumError::NoSuchPoll => write!(f, "no such poll"),
            QuorumError::UnknownOperator(i) => write!(f, "operator {i} is not on the committee"),
        }
    }
}

impl std::error::Error for QuorumError {}

/// **The `VoteEngine`-shaped ruling-finality interface** (mirrors `collective-choice::
/// VoteEngine`). A ruling is opened as a poll over its commitment; operators cast
/// ratifications; the ruling is certified only at quorum.
pub trait RulingVoteEngine {
    /// The engine's refusal type.
    type Error;

    /// Open a poll over a ruling's 32-byte commitment (its [`crate::Receipt::id`]).
    fn open_poll(&mut self, ruling: [u8; 32]) -> Result<PollId, Self::Error>;

    /// Cast one operator's ratification of `commitment` against `poll`. A ratification of a
    /// commitment other than the poll's true ruling is recorded but does not count toward
    /// finality (the forged-ruling tooth). A double-vote by the same operator is idempotent.
    fn cast(
        &mut self,
        poll: PollId,
        operator: usize,
        commitment: [u8; 32],
    ) -> Result<(), Self::Error>;

    /// The tally a light client verifies: the number of DISTINCT operators who ratified the
    /// poll's true ruling commitment.
    fn tally(&self, poll: PollId) -> Result<usize, Self::Error>;

    /// Certify the ruling — `Some(Finalized)` iff the tally has reached the supermajority
    /// threshold `⌊2n/3⌋+1`, else `None` (the gate refused: below quorum).
    fn resolve(&self, poll: PollId) -> Result<Option<Finalized>, Self::Error>;
}

/// **The committee** — `n` genuinely independent operators, finality at `⌊2n/3⌋+1`. Holds one
/// open poll per opened ruling; each poll records, per operator, the commitment it ratified.
pub struct QuorumCommittee {
    n: usize,
    threshold: usize,
    polls: BTreeMap<u64, Poll>,
    next: u64,
}

struct Poll {
    /// The true ruling commitment this poll is over.
    ruling: [u8; 32],
    /// Per operator, the commitment it ratified (last write wins — a re-vote is idempotent).
    ballots: BTreeMap<usize, [u8; 32]>,
}

impl QuorumCommittee {
    /// A committee of `n` operators. The supermajority threshold is `⌊2n/3⌋+1` — the same rule
    /// as the real blocklace consensus. `n` should be ≥ 1; the tolerated fault bound is
    /// `f = ⌊(n−1)/3⌋`.
    pub fn new(n: usize) -> QuorumCommittee {
        QuorumCommittee {
            n,
            threshold: supermajority_threshold(n),
            polls: BTreeMap::new(),
            next: 0,
        }
    }

    /// The number of operators on the committee.
    pub fn operators(&self) -> usize {
        self.n
    }

    /// The supermajority threshold `⌊2n/3⌋+1` a ruling must reach to be final.
    pub fn threshold(&self) -> usize {
        self.threshold
    }

    /// The tolerated Byzantine bound `f = ⌊(n−1)/3⌋` — the minority that CANNOT finalize,
    /// censor, or forge.
    pub fn fault_bound(&self) -> usize {
        self.n.saturating_sub(1) / 3
    }

    fn poll_mut(&mut self, poll: PollId) -> Result<&mut Poll, QuorumError> {
        self.polls.get_mut(&poll.0).ok_or(QuorumError::NoSuchPoll)
    }

    fn poll_ref(&self, poll: PollId) -> Result<&Poll, QuorumError> {
        self.polls.get(&poll.0).ok_or(QuorumError::NoSuchPoll)
    }
}

/// The supermajority threshold `⌊2n/3⌋+1` — byte-for-byte the Lean `supermajorityThreshold`
/// (`metatheory/Dregg2/Distributed/QuorumThreshold.lean`).
pub fn supermajority_threshold(n: usize) -> usize {
    (2 * n) / 3 + 1
}

impl RulingVoteEngine for QuorumCommittee {
    type Error = QuorumError;

    fn open_poll(&mut self, ruling: [u8; 32]) -> Result<PollId, QuorumError> {
        let id = self.next;
        self.next += 1;
        self.polls.insert(
            id,
            Poll {
                ruling,
                ballots: BTreeMap::new(),
            },
        );
        Ok(PollId(id))
    }

    fn cast(
        &mut self,
        poll: PollId,
        operator: usize,
        commitment: [u8; 32],
    ) -> Result<(), QuorumError> {
        if operator >= self.n {
            return Err(QuorumError::UnknownOperator(operator));
        }
        let p = self.poll_mut(poll)?;
        p.ballots.insert(operator, commitment);
        Ok(())
    }

    fn tally(&self, poll: PollId) -> Result<usize, QuorumError> {
        let p = self.poll_ref(poll)?;
        // Count ONLY operators who ratified the true ruling commitment — a forged-commitment
        // ratification does not count.
        Ok(p.ballots.values().filter(|c| **c == p.ruling).count())
    }

    fn resolve(&self, poll: PollId) -> Result<Option<Finalized>, QuorumError> {
        let p = self.poll_ref(poll)?;
        let mut ratifiers: Vec<usize> = p
            .ballots
            .iter()
            .filter(|(_, c)| **c == p.ruling)
            .map(|(op, _)| *op)
            .collect();
        ratifiers.sort_unstable();
        if ratifiers.len() >= self.threshold {
            Ok(Some(Finalized {
                ruling: p.ruling,
                ratifiers,
            }))
        } else {
            Ok(None)
        }
    }
}
