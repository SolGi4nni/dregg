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
use crate::world::{Driver, StepReceipt, WorldError, decision_commitment};

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
        let raw_tally = engine.tally();
        let tally = labeled_tally(&options, &raw_tally);
        let winning_option = engine.resolve()?;
        let winning_choice = options[winning_option].choice_index;

        // BIND the certified winner to the world turn: the same turn that advances the
        // world by the winner's choice commits to the decision that authored it. The
        // commitment is minted from the SAME (winner, tally) the crowd certified, so an
        // operator who later swaps the applied choice is caught by
        // [`verify_collective_certified`] (the committed slot no longer matches).
        let winner_tally = raw_tally.get(winning_option).copied().unwrap_or(0);
        let total: u64 = raw_tally.iter().sum();
        let commitment = decision_commitment(
            winning_option as u64,
            winning_choice as u64,
            winner_tally,
            total,
        );
        let step = driver.advance_certified(winning_choice, commitment)?;
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

/// A way the certified-winner check failed — an operator applied a choice the crowd did
/// not certify.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CollectiveVerifyBreak {
    /// The world turn at this round did not commit to the certified winner: the round's
    /// [`DECISION_EXT_KEY`](crate::DECISION_EXT_KEY) commitment is absent (a plain,
    /// un-bound advance) or does not equal `commitment(certified winner)` — the world was
    /// advanced by a choice other than the one the crowd certified.
    DecisionBindingBroken { round: usize },
    /// The applied choice index differs from the certified winner's choice index (the
    /// world moved to a branch the crowd did not certify).
    AppliedChoiceMismatch {
        /// Which round.
        round: usize,
        /// The spween choice the world was actually advanced by.
        applied: usize,
        /// The spween choice the crowd's certified winner resolves to.
        certified: usize,
    },
}

impl std::fmt::Display for CollectiveVerifyBreak {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CollectiveVerifyBreak::DecisionBindingBroken { round } => write!(
                f,
                "round {round}: the world turn is not bound to the certified winner \
                 (the decision-commitment slot is absent or mismatched)"
            ),
            CollectiveVerifyBreak::AppliedChoiceMismatch {
                round,
                applied,
                certified,
            } => write!(
                f,
                "round {round}: applied choice {applied} != the certified winner's choice {certified}"
            ),
        }
    }
}

impl std::error::Error for CollectiveVerifyBreak {}

/// **The certified-winner tooth.** For each resolved [`CollectiveRound`], confirm the
/// world turn that advanced the story was BOUND to the crowd's certified winner: the
/// applied choice equals the certified winner's choice, AND the turn's committed
/// [`DECISION_EXT_KEY`](crate::DECISION_EXT_KEY) commitment equals the
/// [`decision_commitment`] recomputed from that round's certified winner (option +
/// choice + winning tally + total).
///
/// This closes the vote→branch leak: with only the receipt chain + replay, an operator
/// could resolve a poll to winner `W` yet advance the world by a DIFFERENT choice `X`
/// and the record still verified (replay re-drives whatever choices were recorded). A
/// choice advanced by the plain (un-bound) path leaves the decision slot zero, and a
/// choice bound to a different winner mints a different commitment — either way this
/// check refuses it. Run it ALONGSIDE [`crate::verify`] (chain-linkage + replay), which
/// pins the committed decision slot itself un-retconnably.
pub fn verify_collective_certified(
    rounds: &[CollectiveRound],
) -> Result<(), CollectiveVerifyBreak> {
    for (i, r) in rounds.iter().enumerate() {
        // The world must have advanced by the certified winner's choice.
        if r.step.choice_index != r.winning_choice {
            return Err(CollectiveVerifyBreak::AppliedChoiceMismatch {
                round: i,
                applied: r.step.choice_index,
                certified: r.winning_choice,
            });
        }
        // The committed turn must be bound to THIS certified winner's commitment.
        let winner_tally = r.tally.get(r.winner_label()).copied().unwrap_or(0);
        let total: u64 = r.tally.values().copied().sum();
        let expected = decision_commitment(
            r.winning_option as u64,
            r.winning_choice as u64,
            winner_tally,
            total,
        );
        match r.step.decision_commitment {
            Some(c) if c == expected => {}
            _ => return Err(CollectiveVerifyBreak::DecisionBindingBroken { round: i }),
        }
    }
    Ok(())
}
