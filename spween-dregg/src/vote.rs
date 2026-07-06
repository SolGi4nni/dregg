//! # The `VoteEngine` seam + a local stub
//!
//! The collective-CYOA mode consumes a **`VoteEngine`**: the audience opens a poll
//! over the available choices, casts ballots, and resolves a winner. This mirrors the
//! privacy-voting shape from SPWEEN-ON-DREGG §2.3 / §4.2 — a poll cell with monotone
//! tallies and one-vote-per-ballot — as a trait so the real cell-backed engine
//! (`collective-choice` lane) wires in later without touching the branch loop.
//!
//! [`StubVoteEngine`] is a faithful in-memory stand-in: one vote per voter (the
//! `WriteOnce VOTE_SLOT` tooth), monotone tallies, argmax resolution. It lets the
//! branch loop and its teeth run standalone.

use std::collections::{BTreeMap, BTreeSet};

/// One option on the ballot: which spween choice it advances, and its display text.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VoteOption {
    /// The spween choice index this option resolves to (the index
    /// `spween::Runtime::select_choice` / [`crate::WorldCell::apply_choice`] takes).
    pub choice_index: usize,
    /// Human-readable choice text.
    pub label: String,
}

/// Why a vote operation failed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VoteError {
    /// No poll is open.
    NoPoll,
    /// The option index is out of range for the open poll.
    BadOption { option: usize, options: usize },
    /// This voter already cast a ballot in the open poll (the one-vote-per-ballot
    /// tooth — the local analogue of `WriteOnce VOTE_SLOT`).
    DoubleVote { voter: String },
    /// The poll cannot resolve (no options, no votes cast, or — for the real
    /// cell-backed engine — quorum not met).
    Unresolvable,
    /// A backing engine (the real cell-backed [`collective_choice`] engine) refused;
    /// the reason is carried verbatim.
    Engine(String),
}

impl std::fmt::Display for VoteError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            VoteError::NoPoll => write!(f, "no poll is open"),
            VoteError::BadOption { option, options } => {
                write!(f, "option {option} out of range (0..{options})")
            }
            VoteError::DoubleVote { voter } => write!(f, "voter `{voter}` already voted"),
            VoteError::Unresolvable => write!(f, "poll has no resolvable winner"),
            VoteError::Engine(m) => write!(f, "vote engine: {m}"),
        }
    }
}

impl std::error::Error for VoteError {}

/// **The collective-decision engine the branch loop consumes.** A poll opens over the
/// available choices, the audience casts ballots, and `resolve` reads the winning
/// option off the (monotone) tally. The real implementation is a dregg poll cell +
/// ballot cells (`collective-choice` lane); [`StubVoteEngine`] is the local stand-in.
pub trait VoteEngine {
    /// Open a fresh poll over `options` (closing/replacing any prior poll).
    fn open_poll(&mut self, options: &[VoteOption]) -> Result<(), VoteError>;

    /// Cast `voter`'s ballot for option index `option`. One vote per voter.
    fn cast(&mut self, voter: &str, option: usize) -> Result<(), VoteError>;

    /// The current tally, one count per option (in option order).
    fn tally(&self) -> Vec<u64>;

    /// Close and resolve the poll to the winning option index (into the `options`
    /// passed to [`open_poll`](VoteEngine::open_poll)).
    fn resolve(&mut self) -> Result<usize, VoteError>;
}

/// A faithful in-memory [`VoteEngine`]: one vote per voter, monotone tallies, argmax
/// (lowest index wins a tie).
#[derive(Debug, Default)]
pub struct StubVoteEngine {
    options: usize,
    tallies: Vec<u64>,
    voters: BTreeSet<String>,
    open: bool,
}

impl StubVoteEngine {
    /// A fresh engine with no poll open.
    pub fn new() -> Self {
        Self::default()
    }
}

impl VoteEngine for StubVoteEngine {
    fn open_poll(&mut self, options: &[VoteOption]) -> Result<(), VoteError> {
        self.options = options.len();
        self.tallies = vec![0; options.len()];
        self.voters = BTreeSet::new();
        self.open = true;
        Ok(())
    }

    fn cast(&mut self, voter: &str, option: usize) -> Result<(), VoteError> {
        if !self.open {
            return Err(VoteError::NoPoll);
        }
        if option >= self.options {
            return Err(VoteError::BadOption {
                option,
                options: self.options,
            });
        }
        if self.voters.contains(voter) {
            return Err(VoteError::DoubleVote {
                voter: voter.to_string(),
            });
        }
        self.voters.insert(voter.to_string());
        // Monotone: a tally only ever increases.
        self.tallies[option] += 1;
        Ok(())
    }

    fn tally(&self) -> Vec<u64> {
        self.tallies.clone()
    }

    fn resolve(&mut self) -> Result<usize, VoteError> {
        if !self.open || self.options == 0 {
            return Err(VoteError::Unresolvable);
        }
        let total: u64 = self.tallies.iter().sum();
        if total == 0 {
            return Err(VoteError::Unresolvable);
        }
        // argmax, lowest index breaks ties.
        let mut best = 0usize;
        let mut best_count = self.tallies[0];
        for (i, &c) in self.tallies.iter().enumerate() {
            if c > best_count {
                best = i;
                best_count = c;
            }
        }
        self.open = false;
        Ok(best)
    }
}

/// A count of how the round's ballots fell (option label → votes), for reporting.
pub fn labeled_tally(options: &[VoteOption], tally: &[u64]) -> BTreeMap<String, u64> {
    options
        .iter()
        .zip(tally.iter())
        .map(|(o, &c)| (o.label.clone(), c))
        .collect()
}
