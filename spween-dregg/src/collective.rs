//! # Collective CYOA — the vote-driven branch loop (the killer mode)
//!
//! At each choice passage: open a poll over the *available* choices → the audience
//! votes → the winning choice's turn fires and the world advances. A crowd
//! collectively and verifiably authors the story: every branch is a poll that
//! resolves to a real turn on the world-cell, and no operator can pick a different
//! branch than the crowd chose (SPWEEN-ON-DREGG §4.2).
//!
//! The loop drives the stock [`Driver`] (so availability + navigation come from the
//! unmodified `spween::Runtime`) and consumes any [`VoteEngine`]; the winning choice
//! lands via the same one-verified-turn path as single-player.

use crate::vote::{VoteEngine, VoteError, VoteOption, labeled_tally};
use crate::world::{Driver, StepReceipt, WorldError};

/// The context handed to the ballot source each round.
#[derive(Clone, Debug)]
pub struct PollContext {
    /// The passage the poll is over.
    pub passage: String,
    /// The options on the ballot (available choices only).
    pub options: Vec<VoteOption>,
    /// Which round this is (0-based).
    pub round: usize,
}

/// One resolved collective round.
#[derive(Clone, Debug)]
pub struct CollectiveRound {
    /// The passage voted at.
    pub passage: String,
    /// The ballot options.
    pub options: Vec<VoteOption>,
    /// The final tally (option label → votes).
    pub tally: std::collections::BTreeMap<String, u64>,
    /// The winning option position (into `options`).
    pub winning_option: usize,
    /// The spween choice index the winner resolved to.
    pub winning_choice: usize,
    /// The committed turn for the winning choice.
    pub step: StepReceipt,
}

impl CollectiveRound {
    /// The winning choice's display text.
    pub fn winner_label(&self) -> &str {
        &self.options[self.winning_option].label
    }
}

/// Why a collective run stopped early (other than a clean end / no-choices).
#[derive(Clone, Debug)]
pub enum CollectiveError {
    /// A vote-engine operation failed.
    Vote(VoteError),
    /// The world-cell refused the winning choice's turn.
    World(WorldError),
}

impl std::fmt::Display for CollectiveError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CollectiveError::Vote(e) => write!(f, "vote engine: {e}"),
            CollectiveError::World(e) => write!(f, "world-cell: {e}"),
        }
    }
}

impl std::error::Error for CollectiveError {}

impl From<VoteError> for CollectiveError {
    fn from(e: VoteError) -> Self {
        CollectiveError::Vote(e)
    }
}

impl From<WorldError> for CollectiveError {
    fn from(e: WorldError) -> Self {
        CollectiveError::World(e)
    }
}

/// A single ballot cast by the audience: a voter id and the option position they pick.
pub type Ballot = (String, usize);

/// **Run the vote-driven branch loop to the end of the story.** Each round: gather the
/// available choices, open a poll, collect the audience's ballots (from `ballots`),
/// resolve the winner, and fire it as one verified turn. Stops when the scene ends or
/// a passage offers no available choice. Double-votes from `ballots` are rejected by
/// the engine and skipped (the one-vote-per-ballot tooth); a poll with no valid votes
/// stops the run with [`VoteError::Unresolvable`].
///
/// `ballots` is the audience: given the [`PollContext`], it returns the ballots for
/// that round. (In production these arrive as `cast_vote` turns on ballot cells; here
/// the caller supplies them.)
pub fn run_collective<E, B>(
    driver: &mut Driver<'_>,
    engine: &mut E,
    mut ballots: B,
) -> Result<Vec<CollectiveRound>, CollectiveError>
where
    E: VoteEngine,
    B: FnMut(&PollContext) -> Vec<Ballot>,
{
    let mut rounds = Vec::new();
    let mut round = 0usize;
    while !driver.is_ended() {
        let Some(passage) = driver.current_passage() else {
            break;
        };
        // Only AVAILABLE choices go on the ballot (gates already enforced upstream).
        let options: Vec<VoteOption> = driver
            .choices()
            .into_iter()
            .filter(|c| c.available)
            .map(|c| VoteOption {
                choice_index: c.index,
                label: c.text.to_string(),
            })
            .collect();
        if options.is_empty() {
            break;
        }

        engine.open_poll(&options)?;
        let ctx = PollContext {
            passage: passage.clone(),
            options: options.clone(),
            round,
        };
        for (voter, option) in ballots(&ctx) {
            // A double vote / bad option is refused; skip it (the ballot did not count).
            let _ = engine.cast(&voter, option);
        }
        let tally = labeled_tally(&options, &engine.tally());
        let winning_option = engine.resolve()?;
        let winning_choice = options[winning_option].choice_index;

        let step = driver.advance(winning_choice)?;
        rounds.push(CollectiveRound {
            passage,
            options,
            tally,
            winning_option,
            winning_choice,
            step,
        });
        round += 1;
    }
    Ok(rounds)
}
