//! # `governance` — officers elected by a real quorum-certified vote
//!
//! Guild governance is not an officer flag a host sets — it is the real
//! collective-choice engine (`dungeon-on-dregg/src/collective.rs`). An
//! [`OfficerElection`] opens a poll whose options are the candidate officers and whose
//! electorate is the guild's seats (each a real ed25519 custody key). A ballot is a
//! real cap-bounded signed turn; the winner is certified only at the quorum gate. The
//! teeth carry straight over from the collective:
//!
//! * **Below quorum, no officer is seated** — the quorum `AffineLe` gate refuses the
//!   decision-turn and [`OfficerElection::elect`] yields `None`.
//! * **A non-seated key is Ineligible** — a valid signature by a key that is not on the
//!   guild's electorate holds no ballot cap ([`CollectiveError::Vote`] /
//!   `VoteError::Ineligible`).
//! * **A forged / wrong-key / re-pointed ballot signature is refused**
//!   ([`CollectiveError::BadSignature`]) — a name is not a vote.
//!
//! The candidate proposals carry an inert placeholder [`Command`] coordinate: this
//! election only reads the certified winner (which officer the guild seated), it does
//! not resolve a command into a game world.

use dungeon_on_dregg::collective::{CollectiveRound, Proposal};
use dungeon_on_dregg::narrator::Command;

pub use collective_choice::{PollId, Tally, TurnReceipt};
pub use dungeon_on_dregg::collective::{
    CollectiveError, Custodian, Seat, SignedBallot, demo_custodians, demo_roster,
};

/// The officer the guild seated — the quorum-certified winner of an [`OfficerElection`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ElectedOfficer {
    /// The seated officer's name (the winning candidate label).
    pub name: String,
    /// The number of ballots that named this officer.
    pub votes: u64,
    /// The quorum-met total that certified the election.
    pub total: u64,
}

/// **A guild officer election** — a real quorum-certified collective vote over the
/// guild's seats. Wraps a [`CollectiveRound`] whose options are the candidate officers.
pub struct OfficerElection {
    round: CollectiveRound,
    candidates: Vec<String>,
}

impl OfficerElection {
    /// **Open an election** over `candidates`, an `electorate` of guild seats (custody
    /// public keys), a `quorum` threshold `M`, and a `federation` id. Each candidate is
    /// a poll option; a seat votes by casting a signed ballot for a candidate's index.
    pub fn open(
        question: impl Into<String>,
        candidates: Vec<String>,
        electorate: &[Seat],
        quorum: u64,
        federation: [u8; 32],
    ) -> Result<OfficerElection, CollectiveError> {
        let proposals: Vec<Proposal> = candidates
            .iter()
            .enumerate()
            // The command is an inert placeholder — the election only reads the
            // certified winner (which officer), never resolves a command into a world.
            .map(|(i, name)| Proposal::new(name.clone(), Command::at("guild-hall", i)))
            .collect();
        let round =
            CollectiveRound::open_with(question, proposals, electorate, quorum, federation)?;
        Ok(OfficerElection { round, candidates })
    }

    /// The open poll's id (a seat needs it to sign a ballot via
    /// [`Custodian::sign_ballot`](dungeon_on_dregg::collective::Custodian::sign_ballot)).
    pub fn poll(&self) -> PollId {
        self.round.poll()
    }

    /// The candidate officer labels (index-aligned with the ballot options).
    pub fn candidates(&self) -> &[String] {
        &self.candidates
    }

    /// **Cast a seat's signed ballot** for a candidate — a real cap-bounded ballot turn,
    /// admitted ONLY if the signature verifies against the seat's registered custody key
    /// and that key is on the guild's electorate. A forged / wrong-key / re-pointed
    /// signature is [`CollectiveError::BadSignature`]; a non-seated key is
    /// `VoteError::Ineligible`; a second ballot by a seat is `VoteError::DoubleVote`.
    pub fn cast(&mut self, ballot: &SignedBallot) -> Result<TurnReceipt, CollectiveError> {
        self.round.cast(ballot)
    }

    /// The current per-candidate tally (the monotone verified board).
    pub fn tally(&self) -> Result<Tally, CollectiveError> {
        self.round.tally()
    }

    /// **Certify the elected officer at the quorum gate.** Returns the seated
    /// [`ElectedOfficer`] once at least `M` ballots are cast; `None` below quorum (the
    /// gate refuses the decision-turn — no officer is seated).
    pub fn elect(&mut self) -> Result<Option<ElectedOfficer>, CollectiveError> {
        Ok(self.round.resolve()?.map(|w| ElectedOfficer {
            name: w.label,
            votes: w.decision.winner_tally,
            total: w.decision.total,
        }))
    }
}
