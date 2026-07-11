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
//! ## Seat identity is a REAL custody signing key — a ballot is authenticated by a signature
//!
//! Each seat is bound to a real ed25519 CUSTODY keypair ([`Custodian`]) — the SAME
//! classical signature the executor authorizes turns with (`Authorization::Signature`,
//! [`dregg_types::sign`]/[`dregg_types::verify`]). The seat's PUBLIC key is its electorate
//! identity (registered on the round via [`Seat`]); the SECRET stays with the seat. A
//! ballot is a real ballot only if it carries a [`SignedBallot`] — the seat's signature
//! over the canonical ballot message (domain ‖ poll ‖ voter-pk ‖ option). [`cast`] verifies
//! that signature against the registered public key BEFORE any turn is issued:
//!
//! * a **missing / wrong-key / forged** signature is [`CollectiveError::BadSignature`] —
//!   nothing is issued or cast (the board does not move);
//! * a signature **re-pointed** at a different option/poll fails to verify (the message
//!   binds both) — likewise refused;
//! * a **valid signature by a non-seated key** still holds no ballot cap and is refused
//!   [`VoteError::Ineligible`] by the real engine (a valid signature is not a seat).
//!
//! [`cast`]: CollectiveRound::cast
//!
//! ## Honest scope
//!
//! The quorum, the WriteOnce ballots, the Monotonic tally, the light-client recomputation,
//! AND the seat identities are now all REAL: each ballot is authenticated by a genuine
//! ed25519 signature over the seat's registered custody public key. What remains for full
//! production identity is **key distribution / registration** (how a seat's real custody
//! public key is enrolled into the electorate out-of-band and attested) and **key
//! rotation / revocation** (retiring a compromised custody key). The demo keyring
//! ([`demo_custodians`]) derives each seat's real secret DETERMINISTICALLY from its name so
//! the example/tests reproduce stable identities; a production seat generates its secret in
//! its own custody ([`Custodian::generate`]) and never derives it from public data. The
//! signing-and-verification itself — the thing that makes a ballot authentic — is genuine.
//!
//! [`TurnReceipt`]: dregg_app_framework::TurnReceipt
//! [`Command`]: crate::narrator::Command
//! [`WorldCell`]: spween_dregg::WorldCell
//! [`VoteError::Ineligible`]: collective_choice::VoteError::Ineligible

use std::collections::BTreeMap;

use collective_choice::{
    BallotCap, CollectiveChoice, Decision, PollId, PollSpec, Tally, TurnReceipt, VoteEngine,
    VoteError,
};
use dregg_types::{PublicKey, Signature, SigningKey};
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

/// The domain tag prefixing every ballot signature — binds a signature to THIS scheme +
/// version so a signature minted in another context never verifies as a ballot here.
const BALLOT_DOMAIN: &[u8] = b"dungeon-on-dregg/collective/ballot-v1";

/// The `blake3::derive_key` context for the DEMO custody secret seeds (see
/// [`Custodian::demo`]) — a domain separator so a demo seat's derived secret is unique to
/// this keyring.
const CUSTODY_DERIVE_CONTEXT: &str = "dungeon-on-dregg collective custody seat v1";

/// The canonical ballot message a seat signs with its custody key: `domain ‖ poll-cell id
/// ‖ voter pk ‖ option`. Binding the poll id stops a cross-poll replay of a signature;
/// binding the option stops re-pointing a signature at a different choice.
fn ballot_message(poll: PollId, voter_pk: &PublicKey, option: usize) -> Vec<u8> {
    let mut m = Vec::with_capacity(BALLOT_DOMAIN.len() + 32 + 32 + 8);
    m.extend_from_slice(BALLOT_DOMAIN);
    m.extend_from_slice(poll.0.as_bytes());
    m.extend_from_slice(&voter_pk.0);
    m.extend_from_slice(&(option as u64).to_be_bytes());
    m
}

/// A seat's **custody keypair** — the real ed25519 signing key that authenticates its
/// ballots (the SAME classical scheme the executor authorizes turns with). Its PUBLIC key
/// is the seat's electorate identity (registered on the round as a [`Seat`]); the SECRET
/// stays with the seat. A ballot is a real ballot only if signed by this key: a
/// forged/wrong-key/tampered signature is refused ([`CollectiveError::BadSignature`]).
pub struct Custodian {
    name: String,
    key: SigningKey,
    pk: PublicKey,
}

impl Custodian {
    /// A **fresh random** custody keypair for `name` — the production path: the secret is
    /// generated in the seat's own custody and never derived from public data.
    pub fn generate(name: impl Into<String>) -> Custodian {
        let (key, pk) = dregg_types::generate_keypair();
        Custodian {
            name: name.into(),
            key,
            pk,
        }
    }

    /// A **deterministic demo** custody keypair for `name`: the ed25519 SECRET seed is
    /// `blake3::derive_key(CUSTODY_DERIVE_CONTEXT, name)`, a genuine keypair whose secret
    /// only this derivation reproduces (so the example/tests are stable). NOT a production
    /// custody key — a real seat generates its secret in its own device ([`generate`]).
    ///
    /// [`generate`]: Custodian::generate
    pub fn demo(name: impl Into<String>) -> Custodian {
        let name = name.into();
        let seed = blake3::derive_key(CUSTODY_DERIVE_CONTEXT, name.as_bytes());
        let key = SigningKey::from_bytes(&seed);
        let pk = key.public_key();
        Custodian { name, key, pk }
    }

    /// The seat's human name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// The seat's custody PUBLIC key — its electorate identity.
    pub fn public_key(&self) -> PublicKey {
        self.pk
    }

    /// The seat's registered public identity (name + public key), for enrolling into a
    /// round's electorate. The secret is NOT included.
    pub fn seat(&self) -> Seat {
        Seat {
            name: self.name.clone(),
            pk: self.pk,
        }
    }

    /// **Sign a ballot** for `option` in `poll` with this seat's custody key. The signature
    /// covers the canonical [`ballot_message`] (domain ‖ poll ‖ voter-pk ‖ option), so it
    /// authenticates WHO votes and WHAT for, and cannot be replayed into a different poll or
    /// re-pointed at another option. The returned [`SignedBallot`] is what [`cast`] admits.
    ///
    /// [`cast`]: CollectiveRound::cast
    pub fn sign_ballot(&self, poll: PollId, option: usize) -> SignedBallot {
        let msg = ballot_message(poll, &self.pk, option);
        let signature = dregg_types::sign(&self.key, &msg);
        SignedBallot {
            voter_pk: self.pk,
            option,
            signature,
        }
    }

    /// Sign an arbitrary `message` with this seat's custody secret (a raw ed25519 signature).
    /// Used to construct adversarial ballots in tests (e.g. an impostor signing a message
    /// stamped with another seat's public key) — the signature is genuine, but by the WRONG
    /// key, so it never verifies against the claimed seat.
    pub fn sign_raw(&self, message: &[u8]) -> Signature {
        dregg_types::sign(&self.key, message)
    }
}

/// A seat's **registered public identity** in a round: its human name + the ed25519 PUBLIC
/// key it signs ballots with. Only the public key is held by the round (the round never
/// sees a secret); it is the electorate entry the engine checks ballots against.
#[derive(Clone, Debug)]
pub struct Seat {
    /// The seat's human name (a display label).
    pub name: String,
    /// The seat's custody public key — its electorate identity.
    pub pk: PublicKey,
}

/// A **signature-authenticated ballot** — the payload [`CollectiveRound::cast`] admits: the
/// voter's public key, the chosen option, and the seat's ed25519 signature over the
/// canonical ballot message. The round admits it ONLY if the signature verifies against the
/// registered public key (and that key is seated).
#[derive(Clone, Debug)]
pub struct SignedBallot {
    /// The seat's custody public key (must be a registered electorate member).
    pub voter_pk: PublicKey,
    /// The option this ballot votes for.
    pub option: usize,
    /// The seat's ed25519 signature over the canonical ballot message.
    pub signature: Signature,
}

/// The demo seated roster's **custodians** — name + real ed25519 custody keypair, derived
/// deterministically ([`Custodian::demo`]) so the example/tests reproduce stable
/// identities. Their PUBLIC keys are the [`CollectiveRound::open`] electorate.
pub fn demo_custodians() -> Vec<Custodian> {
    ROSTER.iter().map(|n| Custodian::demo(*n)).collect()
}

/// The demo roster as registered public [`Seat`]s (public keys only) — the electorate
/// [`CollectiveRound::open`] enrolls.
pub fn demo_roster() -> Vec<Seat> {
    demo_custodians().iter().map(|c| c.seat()).collect()
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
    /// The ballot's signature did not verify against the claimed seat public key — a
    /// missing, wrong-key, forged, or tampered (option/poll re-pointed) signature. Nothing
    /// is issued or cast; the board does not move (checked BEFORE any turn).
    BadSignature,
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
            CollectiveError::BadSignature => write!(
                f,
                "the ballot signature did not verify against the seat's registered custody key"
            ),
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
    /// The registered electorate — each seat's name + custody PUBLIC key.
    electorate: Vec<Seat>,
    quorum: u64,
    /// Per-seat issued ballot caps keyed by custody public key (idempotent: a seat has
    /// exactly one ballot per round).
    ballots: BTreeMap<[u8; 32], BallotCap>,
}

impl CollectiveRound {
    /// **Open a round** over the demo [`ROSTER`] with the demo [`QUORUM`] and [`FEDERATION`]
    /// — the standard collective-fiction round. See [`open_with`](Self::open_with) to vary
    /// the roster / quorum / federation.
    pub fn open(
        question: impl Into<String>,
        proposals: Vec<Proposal>,
    ) -> Result<CollectiveRound, CollectiveError> {
        Self::open_with(question, proposals, &demo_roster(), QUORUM, FEDERATION)
    }

    /// Open a round over an explicit `electorate` (registered [`Seat`]s — name + custody
    /// public key), `quorum` `M`, and `federation`. Stands up a fresh [`CollectiveChoice`]
    /// engine and opens a real poll whose options are the `proposals` and whose electorate
    /// is the seats' custody PUBLIC keys — a ballot is admitted only if signed by the
    /// matching custody key (see [`cast`](Self::cast)).
    pub fn open_with(
        question: impl Into<String>,
        proposals: Vec<Proposal>,
        electorate: &[Seat],
        quorum: u64,
        federation: [u8; 32],
    ) -> Result<CollectiveRound, CollectiveError> {
        let question = question.into();
        let mut engine = CollectiveChoice::new(federation);
        let electorate_pks: Vec<[u8; 32]> = electorate.iter().map(|s| s.pk.0).collect();
        let spec = PollSpec {
            question: question.clone(),
            options: proposals.iter().map(|p| p.label.clone()).collect(),
            electorate: electorate_pks,
            quorum_m: quorum,
        };
        let poll = engine.open_poll(spec)?;
        Ok(CollectiveRound {
            engine,
            poll,
            question,
            proposals,
            electorate: electorate.to_vec(),
            quorum,
            ballots: BTreeMap::new(),
        })
    }

    /// The open poll's id (a seat needs it to sign a ballot — [`Custodian::sign_ballot`]).
    pub fn poll(&self) -> PollId {
        self.poll
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

    /// **Cast one seat's signature-authenticated ballot** — a REAL cap-bounded turn on the
    /// vote engine, admitted ONLY if the ballot carries a valid custody signature.
    ///
    /// The signature is checked FIRST, before any turn is issued or cast: a missing /
    /// wrong-key / forged / re-pointed signature is [`CollectiveError::BadSignature`] and
    /// nothing commits (the board does not move). A signature that verifies but whose key is
    /// NOT a seated electorate member holds no ballot cap and is refused
    /// [`VoteError::Ineligible`] by the real engine (a valid signature is not a seat). A
    /// SECOND cast by the same seat is refused [`VoteError::DoubleVote`] (the ballot's
    /// `WriteOnce(VOTE)` + the engine nullifier). Returns the real ballot [`TurnReceipt`].
    ///
    /// [`VoteError::Ineligible`]: collective_choice::VoteError::Ineligible
    /// [`VoteError::DoubleVote`]: collective_choice::VoteError::DoubleVote
    pub fn cast(&mut self, ballot: &SignedBallot) -> Result<TurnReceipt, CollectiveError> {
        // Depth (0): the CUSTODY signature. The seat authenticates its ballot with a real
        // ed25519 signature over (domain ‖ poll ‖ voter-pk ‖ option). A signature that does
        // not verify against the CLAIMED public key is refused before anything is issued or
        // cast — nothing commits. This is the identity tooth: a name is not a vote.
        let msg = ballot_message(self.poll, &ballot.voter_pk, ballot.option);
        if !dregg_types::verify(&ballot.voter_pk, &msg, &ballot.signature) {
            return Err(CollectiveError::BadSignature);
        }

        // Eligibility is the real engine's gate, keyed by the seat's custody PUBLIC key: a
        // key not in the registered electorate holds no ballot cap (Ineligible), even with a
        // perfectly valid signature over its own key.
        let voter = ballot.voter_pk.0;
        let cap = match self.ballots.get(&voter) {
            Some(cap) => cap.clone(),
            None => {
                let cap = self.engine.issue_ballot(self.poll, voter)?;
                self.ballots.insert(voter, cap.clone());
                cap
            }
        };
        let receipt = self.engine.cast(self.poll, &cap, ballot.option)?;
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

    /// The registered electorate — each seat's name + custody public key.
    pub fn electorate(&self) -> &[Seat] {
        &self.electorate
    }

    /// The seated roster's names (display labels).
    pub fn roster(&self) -> Vec<&str> {
        self.electorate.iter().map(|s| s.name.as_str()).collect()
    }
}

#[cfg(test)]
mod collective_tests {
    //! The collective, DRIVEN on both real substrates: a quorum-certified vote fires a
    //! real `WorldCell` turn; a sub-quorum round does NOT move the world; a quorum-
    //! certified ILLEGAL command is a real game-executor refusal (the crowd cannot vote
    //! past the `CellProgram`); a duplicate ballot is refused by the real vote engine. AND
    //! identity is a REAL custody signature: a correctly-signed ballot is admitted; a
    //! forged / wrong-key / tampered signature is refused (BadSignature, nothing commits); a
    //! valid signature by a NON-seated key is still Ineligible.
    use super::*;
    use crate::narrator::Command;
    use crate::{
        CH_DESCEND, CH_LEAVE_LANTERN, KP_PRESS_ON, KP_TRADE_BLOWS, ROOM_ANTECHAMBER, ROOM_SHORE,
        deploy, deploy_keep, keep_scene, scene as salt_scene,
    };
    use spween_dregg::Value;

    /// The seat's deterministic demo CUSTODY keypair — reproduces the same keypair the
    /// round registered (both go through [`Custodian::demo`]), so a seat can sign a ballot
    /// the round will admit.
    fn seat(name: &str) -> Custodian {
        Custodian::demo(name)
    }

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
        // (M=3) is met, and trade-blows is the argmax winner. Each ballot is a REAL custody
        // signature by the seat's registered key — admitted as a genuine ballot turn.
        let poll = round.poll();
        let r0 = round
            .cast(&seat("Bramwen").sign_ballot(poll, KP_TRADE_BLOWS))
            .expect("Bramwen's signed ballot is admitted");
        assert_ne!(
            r0.turn_hash, [0u8; 32],
            "a correctly-signed ballot commits a genuine turn"
        );
        round
            .cast(&seat("Corvin").sign_ballot(poll, KP_TRADE_BLOWS))
            .expect("Corvin's signed ballot is admitted");
        round
            .cast(&seat("Della").sign_ballot(poll, KP_PRESS_ON))
            .expect("Della's signed ballot is admitted");
        round
            .cast(&seat("Ferro").sign_ballot(poll, KP_TRADE_BLOWS))
            .expect("Ferro's signed ballot is admitted");

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

        // Two signed votes — below the M=3 quorum.
        let poll = round.poll();
        round
            .cast(&seat("Bramwen").sign_ballot(poll, KP_TRADE_BLOWS))
            .expect("Bramwen votes");
        round
            .cast(&seat("Corvin").sign_ballot(poll, KP_TRADE_BLOWS))
            .expect("Corvin votes");
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
        let poll = round.poll();
        for name in ["Bramwen", "Corvin", "Della"] {
            round
                .cast(&seat(name).sign_ballot(poll, 0))
                .unwrap_or_else(|e| panic!("{name} votes: {e}"));
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

    /// **A duplicate ballot is refused by the real engine.** A seat's SECOND (correctly
    /// signed) cast is a real `VoteError::DoubleVote` (the ballot's `WriteOnce(VOTE)` + the
    /// engine nullifier); the board does not move.
    #[test]
    fn duplicate_ballot_is_refused_by_the_real_engine() {
        let mut round = keep_round();
        let poll = round.poll();
        let wisp = seat("Wisp");
        round
            .cast(&wisp.sign_ballot(poll, KP_TRADE_BLOWS))
            .expect("Wisp's first vote commits");
        match round.cast(&wisp.sign_ballot(poll, KP_PRESS_ON)) {
            Err(CollectiveError::Vote(VoteError::DoubleVote)) => {}
            other => panic!("a second ballot by the same seat must be refused, got {other:?}"),
        }
        assert_eq!(
            round.tally().expect("tally").per_option,
            vec![1, 0],
            "the board did not move on the refused double vote"
        );
    }

    /// **A valid signature by a NON-seated key is still refused.** "Mallory" holds a real
    /// ed25519 custody key and signs a perfectly valid ballot for her OWN public key — the
    /// signature verifies, but her key is not in the registered electorate, so the engine
    /// refuses `VoteError::Ineligible`. A valid signature is not a seat.
    #[test]
    fn non_seated_valid_signature_is_refused_as_ineligible() {
        let mut round = keep_round();
        let poll = round.poll();
        // Mallory is NOT on the ROSTER — her key was never enrolled in the electorate.
        let mallory = Custodian::generate("Mallory");
        let ballot = mallory.sign_ballot(poll, KP_TRADE_BLOWS);
        // Her signature IS valid over her own key (the identity tooth passes)...
        assert!(
            dregg_types::verify(
                &ballot.voter_pk,
                &ballot_message(poll, &ballot.voter_pk, ballot.option),
                &ballot.signature
            ),
            "Mallory's signature is genuinely valid over her own key"
        );
        // ...but she holds no ballot cap: the engine refuses her as ineligible.
        match round.cast(&ballot) {
            Err(CollectiveError::Vote(VoteError::Ineligible)) => {}
            other => panic!("a non-seated voter must be refused as ineligible, got {other:?}"),
        }
        assert_eq!(
            round.tally().expect("tally").total,
            0,
            "no ballot cast by the ineligible voter"
        );
    }

    /// **A FORGED signature is rejected — non-vacuous.** A ballot claims a seated seat's
    /// public key but carries a garbage 64-byte signature. `cast` verifies the signature
    /// FIRST and refuses `BadSignature`; nothing is issued or cast (the board stays empty).
    #[test]
    fn forged_signature_is_rejected() {
        let mut round = keep_round();
        let poll = round.poll();
        let bramwen_pk = seat("Bramwen").public_key();
        // A forged ballot: Bramwen's real public key, but a signature nobody produced.
        let forged = SignedBallot {
            voter_pk: bramwen_pk,
            option: KP_TRADE_BLOWS,
            signature: Signature([0x7u8; 64]),
        };
        match round.cast(&forged) {
            Err(CollectiveError::BadSignature) => {}
            other => panic!("a forged signature must be rejected as BadSignature, got {other:?}"),
        }
        assert_eq!(
            round.tally().expect("tally").total,
            0,
            "anti-ghost: nothing committed on the forged ballot"
        );
    }

    /// **A WRONG-KEY signature is rejected — non-vacuous.** An attacker (Mallory) signs a
    /// ballot but stamps it with a SEATED seat's public key (Bramwen). The signature is a
    /// genuine ed25519 signature — by the WRONG key — so it does not verify against Bramwen's
    /// registered key: `BadSignature`, nothing commits. A signature is who signed it, not
    /// whose name is on it.
    #[test]
    fn wrong_key_signature_is_rejected() {
        let mut round = keep_round();
        let poll = round.poll();
        let bramwen_pk = seat("Bramwen").public_key();
        let mallory = Custodian::generate("Mallory");
        // Mallory signs the message FOR Bramwen's pk, then claims to be Bramwen.
        let msg = ballot_message(poll, &bramwen_pk, KP_TRADE_BLOWS);
        let impostor = SignedBallot {
            voter_pk: bramwen_pk,
            option: KP_TRADE_BLOWS,
            signature: mallory.sign_raw(&msg),
        };
        match round.cast(&impostor) {
            Err(CollectiveError::BadSignature) => {}
            other => panic!("a wrong-key signature must be rejected, got {other:?}"),
        }
        assert_eq!(round.tally().expect("tally").total, 0, "nothing committed");
    }

    /// **A TAMPERED (re-pointed) signature is rejected — non-vacuous, proving the option is
    /// bound.** Bramwen signs a ballot for option 0 (trade-blows), but the ballot is mutated
    /// to option 1 (press-on) before casting. The signature covers option 0's message, so it
    /// does not verify against option 1: `BadSignature`. A signed ballot cannot be
    /// re-pointed at a different choice.
    #[test]
    fn tampered_option_signature_is_rejected() {
        let mut round = keep_round();
        let poll = round.poll();
        let mut ballot = seat("Bramwen").sign_ballot(poll, KP_TRADE_BLOWS);
        // Re-point the ballot at a different option — the signature no longer matches.
        ballot.option = KP_PRESS_ON;
        match round.cast(&ballot) {
            Err(CollectiveError::BadSignature) => {}
            other => panic!("a re-pointed option must be rejected, got {other:?}"),
        }
        assert_eq!(round.tally().expect("tally").total, 0, "nothing committed");
    }
}
