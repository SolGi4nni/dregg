//! # `collective` — the crowd decides, the real world resolves the decision
//!
//! Phase C of the collective-fiction rebuild (plan `ok-yeah-wanna-binary-tide.md`).
//! Phase A landed a dungeon move as a real cap-bounded [`TurnReceipt`] on the real
//! executor; Phase B landed the narrator on that same substrate (prose is not power).
//! This phase lands the **collective**: a crowd's quorum-certified vote fires the
//! winning [`Command`] as a REAL [`WorldCell`] turn — not a LARP toy.
//!
//! ## The two real substrates, welded at the resolve→apply seam
//!
//! * **The vote** runs on the REAL [`collective_choice::CollectiveChoice`] engine — its
//!   own [`EmbeddedExecutor`](dregg_app_framework::EmbeddedExecutor) hosting a poll cell,
//!   per-voter ballot cells, and a monotone tally as *verified turns*. A ballot is a real
//!   [`StateConstraint::WriteOnce`](dregg_app_framework::StateConstraint) cap-bounded
//!   turn; the tally is [`Monotonic`](dregg_app_framework::StateConstraint); a round
//!   RESOLVES only when the polis `AffineLe` quorum gate (`M·RESOLVED − Σ TALLY ≤ 0`)
//!   admits the decision-turn.
//! * **The world** runs on the REAL [`WorldCell`] game executor (Phase A/B) — the same
//!   cell/turn/`CellProgram` the Warden's Keep is built on.
//!
//! [`CollectiveRound::resolve_into_world`] is the seam: the engine's `resolve` yields the
//! certified winning `Command`, and that exact `Command` is applied to the game world via
//! [`WorldCell::apply_choice`] → a real [`TurnReceipt`] on the game executor. **The crowd
//! decides; the world resolves the decided Command.**
//!
//! ## The world-resolves teeth hold OVER the collective
//!
//! A vote is not power any more than prose is:
//!
//! * **Sub-quorum does not move the world.** Below `M` ballots the quorum `AffineLe`
//!   refuses the decision-turn, `resolve` yields nothing, and
//!   [`resolve_into_world`](CollectiveRound::resolve_into_world) fires NO world turn
//!   ([`CollectiveError::BelowQuorum`]) — the world is byte-for-byte unchanged.
//! * **A quorum-certified but ILLEGAL Command is a real executor refusal.** The crowd can
//!   vote — with full quorum — to descend an unlit stair or make an over-cap move; the
//!   game executor re-checks its installed `CellProgram` gate on the post-state and
//!   REFUSES it ([`CollectiveError::World`]). Nothing commits (anti-ghost). The crowd
//!   cannot vote past the executor's teeth.
//!
//! ## Honest scope
//!
//! The quorum, the WriteOnce ballots, the Monotonic tally, and the light-client
//! recomputation are all REAL verified turns. Identity is **demo-grade**: each seat's
//! electorate key is [`seat_pk`] = `blake3(name)`, a deterministic demo public key. A
//! production deployment binds each seat to a real CUSTODY signing key — that binding is
//! the named production gap; the quorum-certified tally itself is genuine.
//!
//! [`TurnReceipt`]: dregg_app_framework::TurnReceipt
//! [`Command`]: crate::narrator::Command
//! [`WorldCell`]: spween_dregg::WorldCell

use std::collections::BTreeMap;

use collective_choice::{
    BallotCap, CollectiveChoice, Decision, PollId, PollSpec, Tally, TurnReceipt, VoteEngine,
    VoteError,
};
use spween::Scene;
use spween_dregg::{WorldCell, WorldError};

use crate::choice_at;
use crate::narrator::Command;

/// The demo seated roster — the five voters who hold ballots in a round. A voter outside
/// this roster holds no ballot cap and is refused as [`VoteError::Ineligible`] by the real
/// engine (a real eligibility tooth). Matches the party page's five seats.
pub const ROSTER: &[&str] = &["Bramwen", "Corvin", "Della", "Ferro", "Wisp"];

/// The quorum threshold `M`: a round certifies (and its winner fires a world turn) only
/// once at least this many ballots are cast — the polis `AffineLe` gate
/// `M·RESOLVED − Σ TALLY ≤ 0`. A participation quorum: a majority of the five-seat roster.
/// Below it the executor refuses the decision-turn and the world does NOT move.
pub const QUORUM: u64 = 3;

/// The federation the backing collective-choice engine's ballot / tally / resolve turns
/// commit under (a fixed demo federation id).
pub const FEDERATION: [u8; 32] = [0xC0; 32];

/// A seat's deterministic electorate public key — `blake3(name)`, a stable demo identity.
/// **The custody-key binding is the named production gap** (see the module doc); this is a
/// demo key, not a custody-held signing key.
pub fn seat_pk(name: &str) -> [u8; 32] {
    *blake3::hash(name.as_bytes()).as_bytes()
}

/// One candidate the crowd may vote for: a human [`label`](Proposal::label) and the typed
/// [`Command`] the world resolves if it wins. The `Command` is a coordinate in the
/// compiled scene's CLOSED move set — the crowd names a legal move; it cannot free-text a
/// state mutation.
#[derive(Clone, Debug)]
pub struct Proposal {
    /// The ballot label shown to voters.
    pub label: String,
    /// The typed move the world resolves if this proposal wins.
    pub command: Command,
}

impl Proposal {
    /// A proposal pairing a `label` with the `command` the world resolves if it wins.
    pub fn new(label: impl Into<String>, command: Command) -> Proposal {
        Proposal {
            label: label.into(),
            command,
        }
    }
}

/// The quorum-certified winner of a round — the real [`Decision`] the engine's quorum gate
/// admitted, plus the winning [`Command`] (still to be resolved by the world).
#[derive(Clone, Debug)]
pub struct CertifiedWinner {
    /// The engine's certified decision (winner index, its tally, the quorum-met total).
    pub decision: Decision,
    /// The winning proposal's label.
    pub label: String,
    /// The winning proposal's typed command (the world resolves THIS).
    pub command: Command,
}

/// The payoff of the whole phase — a quorum-certified collective vote that fired a REAL
/// world turn. Carries BOTH the quorum certificate ([`decision`](Self::decision)) and the
/// real game-executor [`TurnReceipt`] the winning `Command` committed.
#[derive(Clone, Debug)]
pub struct CertifiedTurn {
    /// The quorum certificate: the engine's [`Decision`] the `AffineLe` gate admitted.
    pub decision: Decision,
    /// The winning command the world resolved.
    pub command: Command,
    /// The winning command's real [`TurnReceipt`] on the GAME executor (a genuine
    /// committed turn — its `turn_hash` is non-zero and it chains `pre == prev.post`).
    pub receipt: TurnReceipt,
}

/// Everything a collective round can refuse.
#[derive(Debug)]
pub enum CollectiveError {
    /// The backing vote engine refused (ineligible voter, double vote, bad spec, …) — a
    /// real [`VoteError`] from the [`collective_choice`] executor.
    Vote(VoteError),
    /// The round has not reached quorum: the `AffineLe` gate refused the decision-turn, so
    /// no winner is certified and NO world turn fires (the world is unchanged).
    BelowQuorum,
    /// The quorum-certified winning `Command` was REFUSED by the GAME executor (an
    /// ineligible gate on the post-state — e.g. an unlit descent, an over-cap move). The
    /// crowd cannot vote past the `CellProgram`; nothing committed on the world.
    World(WorldError),
}

impl std::fmt::Display for CollectiveError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CollectiveError::Vote(e) => write!(f, "the vote engine refused: {e}"),
            CollectiveError::BelowQuorum => {
                write!(
                    f,
                    "below quorum — no winner certified, the world does not move"
                )
            }
            CollectiveError::World(e) => {
                write!(f, "the game executor refused the certified command: {e}")
            }
        }
    }
}

impl std::error::Error for CollectiveError {}

impl From<VoteError> for CollectiveError {
    fn from(e: VoteError) -> Self {
        CollectiveError::Vote(e)
    }
}

/// **A collective round** — a crowd deciding the party's next move by a real
/// quorum-certified vote. Holds a live [`CollectiveChoice`] engine + its open [`PollId`]
/// whose options are the round's [`Proposal`]s (index-aligned). Every [`cast`](Self::cast)
/// is a real cap-bounded ballot turn; the tally is a monotone verified board; the round
/// [`resolve`](Self::resolve)s only at the quorum gate.
pub struct CollectiveRound {
    engine: CollectiveChoice,
    poll: PollId,
    question: String,
    /// Index-aligned with the poll's options.
    proposals: Vec<Proposal>,
    roster: Vec<String>,
    quorum: u64,
    /// Per-seat issued ballot caps (idempotent: a seat has exactly one ballot per round).
    ballots: BTreeMap<String, BallotCap>,
}

impl CollectiveRound {
    /// **Open a round** over the demo [`ROSTER`] with the demo [`QUORUM`] and [`FEDERATION`]
    /// — the standard collective-fiction round. See [`open_with`](Self::open_with) to vary
    /// the roster / quorum / federation.
    pub fn open(
        question: impl Into<String>,
        proposals: Vec<Proposal>,
    ) -> Result<CollectiveRound, CollectiveError> {
        Self::open_with(question, proposals, ROSTER, QUORUM, FEDERATION)
    }

    /// Open a round over an explicit `roster` (seat names), `quorum` `M`, and `federation`.
    /// Stands up a fresh [`CollectiveChoice`] engine and opens a real poll whose options are
    /// the `proposals` and whose electorate is the roster's [`seat_pk`]s.
    pub fn open_with(
        question: impl Into<String>,
        proposals: Vec<Proposal>,
        roster: &[&str],
        quorum: u64,
        federation: [u8; 32],
    ) -> Result<CollectiveRound, CollectiveError> {
        let question = question.into();
        let mut engine = CollectiveChoice::new(federation);
        let electorate: Vec<[u8; 32]> = roster.iter().map(|n| seat_pk(n)).collect();
        let spec = PollSpec {
            question: question.clone(),
            options: proposals.iter().map(|p| p.label.clone()).collect(),
            electorate,
            quorum_m: quorum,
        };
        let poll = engine.open_poll(spec)?;
        Ok(CollectiveRound {
            engine,
            poll,
            question,
            proposals,
            roster: roster.iter().map(|s| s.to_string()).collect(),
            quorum,
            ballots: BTreeMap::new(),
        })
    }

    /// The poll question.
    pub fn question(&self) -> &str {
        &self.question
    }

    /// The round's proposals (index-aligned with the poll options / the tally).
    pub fn proposals(&self) -> &[Proposal] {
        &self.proposals
    }

    /// The quorum threshold `M`.
    pub fn quorum(&self) -> u64 {
        self.quorum
    }

    /// **Cast one seat's ballot for `option`** — a REAL cap-bounded turn on the vote
    /// engine. Mints (idempotently) the seat's factory-born ballot cell and casts, so:
    /// a seat NOT on the roster holds no cap and is refused [`VoteError::Ineligible`]; a
    /// SECOND cast by the same seat is refused [`VoteError::DoubleVote`] (the ballot's
    /// `WriteOnce(VOTE)` + the engine nullifier). Returns the real ballot [`TurnReceipt`].
    pub fn cast(&mut self, seat: &str, option: usize) -> Result<TurnReceipt, CollectiveError> {
        // Eligibility is the real engine's gate: a non-roster seat holds no ballot cap.
        let cap = match self.ballots.get(seat) {
            Some(cap) => cap.clone(),
            None => {
                let cap = self.engine.issue_ballot(self.poll, seat_pk(seat))?;
                self.ballots.insert(seat.to_string(), cap.clone());
                cap
            }
        };
        let receipt = self.engine.cast(self.poll, &cap, option)?;
        Ok(receipt)
    }

    /// The authoritative per-option tally, read from the engine's monotone poll-cell slots.
    pub fn tally(&self) -> Result<Tally, CollectiveError> {
        Ok(self.engine.tally(self.poll)?)
    }

    /// The light-client tally — recomputed from the append-only cast log alone (no
    /// re-execution). When it agrees with [`tally`](Self::tally) the board is unforged.
    pub fn light_client_tally(&self) -> Result<Tally, CollectiveError> {
        Ok(self.engine.light_client_tally(self.poll)?)
    }

    /// **Attempt to quorum-certify a winner** — commits the engine's decision-turn IFF the
    /// `AffineLe` quorum gate admits it (`Σ TALLY ≥ M`). Returns the [`CertifiedWinner`]
    /// (decision + winning command) at quorum, or `None` below quorum (the gate refused the
    /// decision-turn; the world must not move).
    pub fn resolve(&mut self) -> Result<Option<CertifiedWinner>, CollectiveError> {
        let decision = match self.engine.resolve(self.poll)? {
            Some(d) => d,
            None => return Ok(None),
        };
        let proposal = self
            .proposals
            .get(decision.winner)
            .expect("the certified winner index is a poll option");
        Ok(Some(CertifiedWinner {
            decision,
            label: proposal.label.clone(),
            command: proposal.command.clone(),
        }))
    }

    /// **THE SEAM — the crowd decides, the real world resolves the decision.** Quorum-
    /// certifies the winner ([`resolve`](Self::resolve)), then applies the winning
    /// [`Command`] to the real game `world` via [`WorldCell::apply_choice`] → a real
    /// [`TurnReceipt`] on the GAME executor.
    ///
    /// The world-resolves teeth hold over the collective:
    /// * below quorum, no winner is certified → NO world turn fires
    ///   ([`CollectiveError::BelowQuorum`]); the world is unchanged.
    /// * a quorum-certified but ILLEGAL command is refused by the game executor
    ///   ([`CollectiveError::World`]); nothing commits (anti-ghost). The crowd cannot vote
    ///   past the `CellProgram` gate.
    pub fn resolve_into_world(
        &mut self,
        world: &WorldCell,
        scene: &Scene,
    ) -> Result<CertifiedTurn, CollectiveError> {
        // The crowd decides — only a quorum-certified winner reaches the world.
        let winner = self.resolve()?.ok_or(CollectiveError::BelowQuorum)?;

        // The world resolves the DECIDED command on the real game executor. An ineligible
        // gate on the post-state is a real refusal — the vote cannot override it.
        let cmd = winner.command;
        let choice = choice_at(scene, &cmd.room, cmd.choice);
        let receipt = world
            .apply_choice(&cmd.room, cmd.choice, &choice)
            .map_err(CollectiveError::World)?;

        Ok(CertifiedTurn {
            decision: winner.decision,
            command: cmd,
            receipt,
        })
    }

    /// The seated roster (seat names).
    pub fn roster(&self) -> &[String] {
        &self.roster
    }
}

#[cfg(test)]
mod collective_tests {
    //! The collective, DRIVEN on both real substrates: a quorum-certified vote fires a
    //! real `WorldCell` turn; a sub-quorum round does NOT move the world; a quorum-
    //! certified ILLEGAL command is a real game-executor refusal (the crowd cannot vote
    //! past the `CellProgram`); a duplicate / non-seated ballot is refused by the real
    //! vote engine.
    use super::*;
    use crate::narrator::Command;
    use crate::{
        CH_DESCEND, CH_LEAVE_LANTERN, KP_PRESS_ON, KP_TRADE_BLOWS, ROOM_ANTECHAMBER, ROOM_SHORE,
        deploy, deploy_keep, keep_scene, scene as salt_scene,
    };
    use spween_dregg::Value;

    /// The standard keep round: the crowd decides whether to trade blows with the
    /// gate-warden or press past. Option 0 = trade-blows, option 1 = press-on.
    fn keep_round() -> CollectiveRound {
        CollectiveRound::open(
            "The gate-warden bars the way — what does the party do?",
            vec![
                Proposal::new("Trade blows with the gate-warden", Command::trade_blows()),
                Proposal::new("Press past into the plundered hall", Command::press_on()),
            ],
        )
        .expect("the round opens")
    }

    /// **THE HARD GATE — a real quorum-certified collective vote fires a REAL WorldCell
    /// turn.** Three of five seats reach quorum for trade-blows; the certified winner is
    /// applied to the real game world → a genuine `TurnReceipt` (hp 50 → 30). Assert BOTH
    /// the quorum certificate AND the real world receipt.
    #[test]
    fn quorum_certified_vote_fires_a_real_world_turn() {
        let mut round = keep_round();
        let s = keep_scene();
        let mut world = deploy_keep(30);
        world.seed_var("hp", Value::Int(50)); // the gate-warden fight begins at 50 HP.

        // Three seats vote trade-blows (option 0), one votes press-on (option 1): quorum
        // (M=3) is met, and trade-blows is the argmax winner.
        round
            .cast("Bramwen", KP_TRADE_BLOWS)
            .expect("Bramwen votes");
        round.cast("Corvin", KP_TRADE_BLOWS).expect("Corvin votes");
        round.cast("Della", KP_PRESS_ON).expect("Della votes");
        round.cast("Ferro", KP_TRADE_BLOWS).expect("Ferro votes");

        // The tally is a monotone verified board; the light client recomputes it identically.
        let tally = round.tally().expect("tally");
        assert_eq!(tally.per_option, vec![3, 1], "3 trade-blows, 1 press-on");
        assert_eq!(
            round.light_client_tally().expect("lc tally"),
            tally,
            "the light client recomputes the same board (unforged)"
        );

        // THE SEAM: the crowd decides (quorum cert), the world resolves the decided command.
        let cert = round
            .resolve_into_world(&world, &s)
            .expect("the quorum-certified winner fires a real world turn");

        // The quorum certificate: trade-blows won with 3 votes at the quorum-met total.
        assert_eq!(
            cert.decision.winner, KP_TRADE_BLOWS,
            "trade-blows certified"
        );
        assert_eq!(cert.decision.winner_tally, 3);
        assert_eq!(cert.decision.total, 4);
        assert_eq!(cert.command, Command::trade_blows());

        // The REAL world receipt: a genuine committed game-executor turn, and the world
        // resolved trade-blows (hp fell 50 → 30 — a real state transition on the game cell).
        assert_ne!(
            cert.receipt.turn_hash, [0u8; 32],
            "the certified command committed a genuine world turn"
        );
        assert_eq!(world.read_var("hp"), 30, "the world resolved trade-blows");
    }

    /// **Sub-quorum does NOT move the world (anti-ghost).** Only two of five seats vote
    /// (below M=3): the quorum `AffineLe` refuses the decision-turn, `resolve` yields
    /// nothing, and `resolve_into_world` fires NO world turn — the world is unchanged.
    #[test]
    fn sub_quorum_round_does_not_move_the_world() {
        let mut round = keep_round();
        let s = keep_scene();
        let mut world = deploy_keep(31);
        world.seed_var("hp", Value::Int(50));

        // Two votes — below the M=3 quorum.
        round
            .cast("Bramwen", KP_TRADE_BLOWS)
            .expect("Bramwen votes");
        round.cast("Corvin", KP_TRADE_BLOWS).expect("Corvin votes");
        assert_eq!(round.tally().expect("tally").total, 2, "two ballots cast");

        // resolve is refused by the quorum gate (yields None).
        assert!(
            round.resolve().expect("resolve query").is_none(),
            "below quorum the decision-turn is refused — no winner certified"
        );

        // resolve_into_world fires NO world turn.
        match round.resolve_into_world(&world, &s) {
            Err(CollectiveError::BelowQuorum) => {}
            other => panic!("a sub-quorum round must not move the world, got {other:?}"),
        }

        // Anti-ghost: the world is byte-for-byte unchanged (hp untouched, no fight resolved).
        assert_eq!(
            world.read_var("hp"),
            50,
            "the world did not move (hp unchanged)"
        );
    }

    /// **A quorum-certified ILLEGAL command is a REAL game-executor refusal.** The crowd
    /// reaches full quorum to descend an unlit stair; the vote engine certifies the winner,
    /// but the GAME executor re-checks its `FieldGte(has_lantern, 1)` gate on the post-state
    /// and REFUSES it. The crowd cannot vote past the `CellProgram`; nothing commits.
    #[test]
    fn quorum_certified_illegal_command_is_a_real_executor_refusal() {
        // The salt-shore dungeon: walk to the gate room WITHOUT the lantern.
        let s = salt_scene();
        let world = deploy(32);
        let leave = choice_at(&s, ROOM_SHORE, CH_LEAVE_LANTERN);
        world
            .apply_choice(ROOM_SHORE, CH_LEAVE_LANTERN, &leave)
            .expect("stepping north empty-handed is ungated and commits");
        assert_eq!(world.read_passage(), Some(1), "in the antechamber, unlit");

        // The crowd votes — with full quorum — to descend the unlit stair.
        let mut round = CollectiveRound::open(
            "The dark stair drops away — do we descend, or retreat?",
            vec![
                Proposal::new(
                    "Descend the dark stair",
                    Command::at(ROOM_ANTECHAMBER, CH_DESCEND),
                ),
                Proposal::new("Retreat to the shore", Command::at(ROOM_ANTECHAMBER, 1)),
            ],
        )
        .expect("the round opens");
        for seat in ["Bramwen", "Corvin", "Della"] {
            round
                .cast(seat, 0)
                .unwrap_or_else(|e| panic!("{seat} votes: {e}"));
        }
        assert_eq!(round.tally().expect("tally").per_option, vec![3, 0]);

        // The crowd DID quorum-certify the descend command...
        let winner = round
            .resolve()
            .expect("resolve query")
            .expect("quorum reached — a winner is certified");
        assert_eq!(winner.command, Command::at(ROOM_ANTECHAMBER, CH_DESCEND));

        // ...but the GAME executor refuses the certified command — the crowd cannot vote
        // past the CellProgram gate (an unlit descent fails FieldGte(has_lantern, 1)).
        match round.resolve_into_world(&world, &s) {
            Err(CollectiveError::World(WorldError::Refused(_))) => {}
            other => panic!(
                "a quorum-certified illegal command must be a real executor refusal, got {other:?}"
            ),
        }

        // Anti-ghost: the refused turn committed NOTHING on the world.
        assert_eq!(world.read_passage(), Some(1), "still in the antechamber");
        assert_eq!(world.read_var("depth"), 0, "depth did not advance");
        assert_eq!(
            world.read_var("has_lantern"),
            0,
            "no lantern conjured by the vote"
        );
    }

    /// **A duplicate ballot is refused by the real engine.** A seat's SECOND cast is a real
    /// `VoteError::DoubleVote` (the ballot's `WriteOnce(VOTE)` + the engine nullifier); the
    /// board does not move.
    #[test]
    fn duplicate_ballot_is_refused_by_the_real_engine() {
        let mut round = keep_round();
        round
            .cast("Wisp", KP_TRADE_BLOWS)
            .expect("Wisp's first vote commits");
        match round.cast("Wisp", KP_PRESS_ON) {
            Err(CollectiveError::Vote(VoteError::DoubleVote)) => {}
            other => panic!("a second ballot by the same seat must be refused, got {other:?}"),
        }
        assert_eq!(
            round.tally().expect("tally").per_option,
            vec![1, 0],
            "the board did not move on the refused double vote"
        );
    }

    /// **A non-seated ballot is refused by the real engine.** A voter outside the roster
    /// holds no ballot cap — `issue_ballot` refuses `VoteError::Ineligible`.
    #[test]
    fn non_seated_ballot_is_refused_by_the_real_engine() {
        let mut round = keep_round();
        // "Mallory" is not on the ROSTER — she holds no eligibility cap.
        match round.cast("Mallory", KP_TRADE_BLOWS) {
            Err(CollectiveError::Vote(VoteError::Ineligible)) => {}
            other => panic!("a non-seated voter must be refused as ineligible, got {other:?}"),
        }
        assert_eq!(
            round.tally().expect("tally").total,
            0,
            "no ballot cast by the ineligible voter"
        );
    }
}
