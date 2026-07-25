//! # `crew_descent` — THE AWAY MISSION: a crew runs the Descent together
//!
//! The station is the party ([`crate::Party`]); the dungeon is the away mission a crew
//! leaves it to run. [`crate::crew`] got a crew as far as the airlock — four identities, a
//! charter, roles assigned by a proof over preferences nobody reveals, a quorum engine, an
//! on-ledger loot split. What it never had was a DUNGEON: [`AwayTeam`](crate::crew::AwayTeam)
//! acts on four abstract role-cells. This module takes the crew down the real
//! Lean-refereed [`Descent`](dungeon_on_dregg::descent::Descent).
//!
//! ⚑ **SUBSTRATE, said out loud: this module authors NO rules.** The Descent's rules — what
//! the executor ADMITS — are Lean-authored (`metatheory/Dregg2/Games/{Dungeon,
//! DungeonProgram}.lean`, emitted to `program/dungeon_program.json`) and unchanged by
//! anything here. Every move this module submits is one of the five admitted verbs, projected
//! by the Descent's own mover and refereed by the Lean-loaded teeth. What lives here is
//! strictly ABOVE the admitted turn: **which** admitted move gets submitted, and **who** was
//! entitled to submit it. That is the legitimate Rust half of the line. A crew's decision to
//! push deeper does not change what a delve IS; it changes whether one gets sent.
//!
//! ## The design question: what does a crew decide, and what does a seat own?
//!
//! Voting on every move is tedious — four people ratifying a sword swing is a committee, not
//! a game. Voting on nothing is single-player with spectators. The split follows the shape of
//! the Descent's own tension, which is a burning clock (26 breath) and a carry ceiling that
//! tightens every floor (`pack + depth ≤ CAP`):
//!
//! **The crew decides what cannot be taken back.** Two of the five verbs are irreversible in
//! the strong sense — there is no ascent verb in the game, so DELVE only ever tightens the
//! ceiling, and FLEE ends the run forever. Those are exactly the two choices with real stakes
//! and no take-backs, which is to say exactly the two people will argue about. They need a
//! quorum-certified [`Council`].
//!
//! **A seat owns what its role owns.** The other three verbs belong to one seat each, and a
//! seat firing another's move is refused BY NAME:
//!
//! | role (party / raid name) | owns | why it bites |
//! |---|---|---|
//! | Tank / **Bulwark** — *the Bearer* | [`SeatMove::Take`] (LOOT) | the pack is theirs, and every relic they take raises `pack`, which is subtracted from how deep the crew can still go |
//! | Mage / **Striker** | [`SeatMove::Strike`] (SMITE) | two breath a blow — the most expensive verb in the game, spent from the crew's common 26 |
//! | Scout / **Pathfinder** | [`SeatMove::OpenWay`] (UNLOCK), and the hand that takes a certified DELVE | the one who can open a way opens it, and leads the step the crew voted for |
//! | Healer / **Mender** | the hand that takes a certified FLEE | the one who brings the crew home — and only on the crew's word |
//!
//! Every role owns something; nobody owns everything; and the two collective verbs still need
//! a HAND, so a certified decision is executed by the role whose job it is. Role assignment
//! therefore MATTERS: the proof that gave you Bulwark gave you the pack, and the crew has to
//! live with it.
//!
//! **This is where the argument comes from.** The Bearer can take a treasure on floor one
//! that the crew will not discover was fatal until floor four, when the certified push comes
//! back as `too laden to squeeze deeper` — a real refusal from the Lean-authored capacity
//! law, not a scolding from this layer. The Striker's fourth blow is four breath the crew
//! needed to get out. "One more floor" stops being a button and becomes a conversation with
//! consequences, and the consequences are enforced by the dungeon rather than by the loudest
//! player.
//!
//! **The split is arithmetic, not seniority.** When the crew is home, the haul is what the
//! ledger says was banked, and the division is the LAST council: candidate splits are ballot
//! options, the quorum-certified winner is written into the party's `WriteOnce` loot slots
//! ([`crate::Party::split_loot`]), and a split whose shares do not sum to the committed haul
//! is refused before it is ever put to a vote.
//!
//! ## What is REAL here (and what is evidence rather than enforcement)
//!
//! * **The roles** are a real crew-bound hiding proof when the seating is
//!   [`RoleProvenance::Proven`] — the assignment is optimal over preferences nobody revealed
//!   and bound to THIS crew inside the proof's own public statement.
//! * **The council** is a real [`CollectiveRound`]: signed ballots as `WriteOnce` cap-bounded
//!   turns, a `Monotonic` tally, and the polis `AffineLe` quorum gate. Below quorum NOTHING
//!   is certified and the mission does not move. A non-crew ballot is `Ineligible`; a forged
//!   one is `BadSignature`.
//! * **The move** is a real cap-bounded turn on the real `WorldCell` against the Lean-loaded
//!   program. A quorum-certified move the rules refuse is still refused — the crew cannot
//!   vote past the teeth, and that is the good news, not the bad.
//! * **A seat's own move is AUTHENTICATED.** The Descent is one world-cell with one writer,
//!   so unlike the party world there are no per-seat capabilities for the executor to check.
//!   The replacement is the same standard the ballots already meet: a seat SIGNS its move
//!   with its custody key over (crew ‖ cell ‖ ordinal ‖ verb ‖ arg ‖ signer), the signature is
//!   verified before any turn is built, and the resulting warrant is emitted INTO the turn
//!   ([`dungeon_on_dregg::authorized_descent`]) where it is absorbed into `receipt_hash` and
//!   covered by the executor's signature. Forging a teammate's move fails at the signature;
//!   an unwarranted move is visible on replay.
//! * **The loot split** is a `WriteOnce` ledger fact on the party world.
//!
//! Named honestly: the role↔verb ownership is enforced by THIS layer plus the mover's
//! signature, not by an executor capability — the Descent's cell cannot express one. What the
//! receipt chain gives is evidence (every move names its warrant), not admission control. And
//! the council rounds and the descent turns are separately-verified records on two ledgers:
//! the writ is bound into the descent turn it authorizes, but no cross-world atomicity is
//! claimed (the same residual [`crate::crew`] names for the proof session).

use dregg_types::{PublicKey, Signature};
use dungeon_on_dregg::authorized_descent::{
    AuthorizedDescent, Verb, receipt_carries_authorization,
};
use dungeon_on_dregg::collective::{
    CollectiveError, CollectiveRound, Proposal, Seat as ElectorateSeat, SignedBallot,
};
use dungeon_on_dregg::descent::{BANKED, BREATH, CAP};
use dungeon_on_dregg::narrator::Command;

use crate::crew::{CREW_SEATS, CrewCharter, CrewError};
use crate::{ActOutcome, Party, PartyFormationError, Role, SeatCustody};

/// The federation the crew's council ballots commit under (distinct from the party fork's,
/// so a fork ballot can never be replayed as a council ballot).
const FEDERATION: [u8; 32] = [0xC5; 32];

/// The domain a seat signs its own descent move under.
const SEAT_MOVE_DOMAIN: &[u8] = b"dregg.party.crew.away-mission.seat-move.v1";
/// `blake3::derive_key` context for a seat-authored move's warrant.
const SEAT_WARRANT_CONTEXT: &str = "dregg.party.crew.away-mission.seat-warrant.v1";
/// `blake3::derive_key` context for a council-certified move's warrant.
const COUNCIL_WARRANT_CONTEXT: &str = "dregg.party.crew.away-mission.council-warrant.v1";

// ── The seating: who holds which job, and where that came from ───────────────────

/// **Where a crew's roles came from.** Carried in the type so nothing can quietly pass a
/// hand-dealt roster off as a proof-assigned one.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RoleProvenance {
    /// The roles are the verified output of the crew-bound hiding proof
    /// ([`crate::crew::CrewRoll::assign_roles`]): globally suitability-maximal over rows
    /// nobody revealed, and bound to this exact crew inside the proof's public statement.
    Proven {
        /// The verified statement session — the crew binding.
        session: u32,
        /// The verified hiding root over the private preference matrix.
        input_root: [u32; 8],
    },
    /// The roles were DECLARED by the caller. Legitimate for a fixed script, a replay, or a
    /// table that assigned jobs by agreement — but it is not a proof, and it does not claim
    /// to be one.
    Declared,
}

impl RoleProvenance {
    /// Whether these roles came from the verified proof.
    pub const fn is_proven(self) -> bool {
        matches!(self, RoleProvenance::Proven { .. })
    }
}

/// **A crew's seating for an away mission** — the charter, the role each charter seat holds,
/// and where that assignment came from.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CrewSeating {
    charter: CrewCharter,
    /// Indexed by CHARTER SEAT.
    roles: [Role; CREW_SEATS],
    provenance: RoleProvenance,
}

impl CrewSeating {
    /// A DECLARED seating — the caller names who holds which job. `roles` is indexed by
    /// charter seat and must be a permutation of the four roles (a crew with two Strikers and
    /// no Mender is not a crew).
    pub fn declared(
        charter: CrewCharter,
        roles: [Role; CREW_SEATS],
    ) -> Result<CrewSeating, CrewError> {
        let mut seen = [false; CREW_SEATS];
        for role in roles {
            if std::mem::replace(&mut seen[role.index()], true) {
                return Err(CrewError::Formation(PartyFormationError::DuplicateRole(
                    role,
                )));
            }
        }
        Ok(CrewSeating {
            charter,
            roles,
            provenance: RoleProvenance::Declared,
        })
    }

    /// The seating a VERIFIED crew-bound role assignment yields — the real path.
    #[cfg(feature = "private-role-assignment")]
    pub fn proven(assignment: &crate::crew::CrewRoles) -> CrewSeating {
        CrewSeating {
            charter: assignment.charter().clone(),
            roles: assignment.roles(),
            provenance: RoleProvenance::Proven {
                session: assignment.session(),
                input_root: assignment.input_root(),
            },
        }
    }

    /// The crew.
    pub fn charter(&self) -> &CrewCharter {
        &self.charter
    }

    /// The roles, in charter seat order.
    pub const fn roles(&self) -> [Role; CREW_SEATS] {
        self.roles
    }

    /// Where this assignment came from.
    pub const fn provenance(&self) -> RoleProvenance {
        self.provenance
    }

    /// The job this identity holds on the mission.
    pub fn role_of(&self, identity: &str) -> Option<Role> {
        self.charter.seat_of(identity).map(|seat| self.roles[seat])
    }

    /// The crew member holding `role`.
    pub fn identity_in(&self, role: Role) -> &str {
        let seat = self
            .roles
            .iter()
            .position(|&r| r == role)
            .expect("a seating is a permutation of the four roles");
        &self.charter.members()[seat]
    }

    /// The roster [`Party::muster_with_roster`] wants.
    pub fn roster(&self) -> [(Role, String); CREW_SEATS] {
        Role::ALL.map(|role| (role, self.identity_in(role).to_string()))
    }

    /// **Depart on the away mission**, hotseat custody: the party mints each seat's ballot
    /// and move-signing key from fresh OS entropy and holds it, so one machine can drive the
    /// whole crew. `day_seed` is the committed beacon seed the day's map is DRAWN from
    /// (every drawn map is Lean-checked completable).
    pub fn depart(&self, seed: u8, day_seed: [u8; 32]) -> Result<CrewDescent, CrewDescentError> {
        let party =
            Party::muster_with_roster(self.roster()).map_err(CrewDescentError::Formation)?;
        let run = AuthorizedDescent::deploy(seed, day_seed).map_err(world_error)?;
        Ok(CrewDescent::new(self.clone(), party, run))
    }

    /// Depart on an EXPLICIT map index (the reproducible entry for a fixed script or a
    /// replay); `day_seed` is still bound as the run's loot provenance root.
    pub fn depart_on_map(
        &self,
        seed: u8,
        day_seed: [u8; 32],
        day: usize,
    ) -> Result<CrewDescent, CrewDescentError> {
        let party =
            Party::muster_with_roster(self.roster()).map_err(CrewDescentError::Formation)?;
        let run = AuthorizedDescent::deploy_on_map(seed, day_seed, day).map_err(world_error)?;
        Ok(CrewDescent::new(self.clone(), party, run))
    }

    /// Depart with the crew holding their OWN secrets ([`Party::muster_with_custody`]): the
    /// party never sees a signing key, so ballots and move signatures arrive already made
    /// from each player's device. This is the deployment shape.
    pub fn depart_with_custody(
        &self,
        keys: &[(String, PublicKey)],
        seed: u8,
        day_seed: [u8; 32],
        day: usize,
    ) -> Result<CrewDescent, CrewDescentError> {
        let mut roster: Vec<(Role, String, PublicKey)> = Vec::with_capacity(CREW_SEATS);
        for role in Role::ALL {
            let identity = self.identity_in(role).to_string();
            let key = keys
                .iter()
                .find(|(name, _)| name == &identity)
                .map(|(_, pk)| *pk)
                .ok_or_else(|| CrewDescentError::NoCustodyKey(identity.clone()))?;
            roster.push((role, identity, key));
        }
        let roster: [(Role, String, PublicKey); CREW_SEATS] =
            roster.try_into().expect("length checked");
        let party = Party::muster_with_custody(roster).map_err(CrewDescentError::Formation)?;
        let run = AuthorizedDescent::deploy_on_map(seed, day_seed, day).map_err(world_error)?;
        Ok(CrewDescent::new(self.clone(), party, run))
    }
}

// ── What a seat owns alone ───────────────────────────────────────────────────────

/// **A move ONE seat owns outright.** The other two admitted verbs (delve, flee) are the
/// crew's — see [`Question`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SeatMove {
    /// **Pathfinder** (Scout): exercise the carried key-relic for `way`, opening it for good.
    OpenWay {
        /// The way to open.
        way: u64,
    },
    /// **Striker** (Mage): wound the standing floor's guardian. Two breath a blow — the
    /// crew's clock, spent by one seat.
    Strike,
    /// **Bulwark** (Tank), the Bearer: take `relic` from the standing floor's hoard into the
    /// pack. Every take raises `pack`, and `pack + depth ≤ CAP` is how deep the crew can
    /// still go — this is the seat power the whole mission argues about.
    Take {
        /// The relic slot to take.
        relic: usize,
    },
}

impl SeatMove {
    /// The ONE role that owns this move.
    pub const fn owner(self) -> Role {
        match self {
            SeatMove::OpenWay { .. } => Role::Scout,
            SeatMove::Strike => Role::Mage,
            SeatMove::Take { .. } => Role::Tank,
        }
    }

    /// The admitted descent verb this move submits.
    pub const fn verb(self) -> Verb {
        match self {
            SeatMove::OpenWay { way } => Verb::Unlock { way },
            SeatMove::Strike => Verb::Smite,
            SeatMove::Take { relic } => Verb::Loot { relic },
        }
    }
}

/// **A seat's own move, authenticated.** The payload [`CrewDescent::submit`] admits: who
/// moves, what they do, at which move ordinal, and their custody signature over exactly that.
/// The signature binds the crew, the descent cell, the ordinal, the verb and its argument, and
/// the signer — so it cannot be replayed at another ordinal, re-pointed at another verb, or
/// re-attributed to another seat.
#[derive(Clone, Debug)]
pub struct SignedSeatMove {
    /// The mover's custody public key (must be a crew seat).
    pub mover_pk: PublicKey,
    /// The move.
    pub mv: SeatMove,
    /// The move ordinal this signature is spendable at.
    pub step: u64,
    /// The mover's ed25519 signature over the canonical move message.
    pub signature: Signature,
}

/// The canonical message a seat signs to submit its own move.
fn seat_move_message(
    charter_root: &[u8; 32],
    descent_cell: &[u8; 32],
    step: u64,
    verb: Verb,
    mover_pk: &PublicKey,
) -> Vec<u8> {
    let mut m = Vec::with_capacity(SEAT_MOVE_DOMAIN.len() + 32 + 32 + 8 + 1 + 8 + 32);
    m.extend_from_slice(SEAT_MOVE_DOMAIN);
    m.extend_from_slice(charter_root);
    m.extend_from_slice(descent_cell);
    m.extend_from_slice(&step.to_be_bytes());
    m.push(verb.tag());
    m.extend_from_slice(&verb.arg().to_be_bytes());
    m.extend_from_slice(&mover_pk.0);
    m
}

// ── What the crew decides together ───────────────────────────────────────────────

/// **A question only the crew may answer** — the irreversible choices.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Question {
    /// One more floor. Burns breath, tightens the carry ceiling, and cannot be undone —
    /// there is no ascent verb. Certified, the **Pathfinder** takes the step.
    Push,
    /// Take what we have and go. Terminal: the pack banks and the tomb freezes. Certified,
    /// the **Mender** takes the crew home.
    ClimbOut,
    /// How the banked haul divides. Only askable once the crew is home, and only over splits
    /// that sum to what the ledger says was actually banked.
    Split {
        /// The candidate divisions, each indexed by CHARTER SEAT.
        candidates: Vec<(String, [u64; CREW_SEATS])>,
    },
}

/// What the crew certified.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Mandate {
    /// Go one floor deeper. The Pathfinder's hand.
    Descend,
    /// End the run and bank the pack. The Mender's hand.
    ClimbOut,
    /// Stay where we are — a real outcome, and the reason a council is not a rubber stamp.
    Hold,
    /// Write this division into the party's `WriteOnce` loot slots (indexed by charter seat).
    Split([u64; CREW_SEATS]),
}

impl Mandate {
    /// The role whose job it is to carry this out — `None` when the mandate needs no hand.
    pub const fn hand(&self) -> Option<Role> {
        match self {
            // The one who opens ways leads the step the crew voted for.
            Mandate::Descend => Some(Role::Scout),
            // The mender brings the crew home.
            Mandate::ClimbOut => Some(Role::Healer),
            // Arithmetic needs no authority beyond the certificate that produced it.
            Mandate::Split(_) | Mandate::Hold => None,
        }
    }

    /// The admitted verb this mandate submits, if any.
    const fn verb(&self) -> Option<Verb> {
        match self {
            Mandate::Descend => Some(Verb::Delve),
            Mandate::ClimbOut => Some(Verb::Flee),
            Mandate::Hold | Mandate::Split(_) => None,
        }
    }
}

/// **A quorum-certified writ** — what the crew decided, with the certificate that proves it.
/// Held by the mission until the hand that owns it carries it out, and consumed only by a
/// move that actually commits.
#[derive(Clone, Debug)]
pub struct Writ {
    /// The certified mandate.
    pub mandate: Mandate,
    /// The council poll this came out of. A writ is single-use: one poll id must appear at
    /// most once in a mission's warrants.
    pub poll: collective_choice::PollId,
    /// The certified winning option index.
    pub winner: usize,
    /// The winner's tally.
    pub winner_tally: u64,
    /// The quorum-met total.
    pub total: u64,
    /// The quorum threshold the round was opened under.
    pub quorum: u64,
    /// The winning option's label.
    pub label: String,
}

/// A council sitting — the live quorum round plus what each option means.
struct Council {
    round: CollectiveRound,
    question: Question,
    /// Index-aligned with the round's proposals.
    mandates: Vec<Mandate>,
}

// ── The mission journal ──────────────────────────────────────────────────────────

/// What entitled a committed move.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Authority {
    /// The seat that owns the verb signed for it.
    Seat {
        /// The mover.
        identity: String,
        /// The role they hold.
        role: Role,
    },
    /// The crew certified it, and the named hand carried it out.
    Council {
        /// The certified mandate.
        mandate: Mandate,
        /// The member who carried it out.
        hand: String,
        /// The winner's tally out of the quorum-met total.
        winner_tally: u64,
        /// The quorum-met total.
        total: u64,
    },
}

/// One committed move of the away mission — the ordinal, the verb, the warrant it carried,
/// and the real descent receipt.
#[derive(Clone, Debug)]
pub struct MissionStep {
    /// The move ordinal.
    pub step: u64,
    /// The admitted verb committed.
    pub verb: Verb,
    /// What entitled it.
    pub authority: Authority,
    /// The 32-byte warrant emitted into the descent turn (recomputable from public data).
    pub warrant: [u8; 32],
    /// The real committed descent turn hash.
    pub receipt: [u8; 32],
}

// ── The away mission ─────────────────────────────────────────────────────────────

/// **A crew descent.** The seating, the crew's party world (custody keys + the `WriteOnce`
/// loot split), and the real Lean-refereed run they are down in.
pub struct CrewDescent {
    seating: CrewSeating,
    party: Party,
    run: AuthorizedDescent,
    council: Option<Council>,
    writ: Option<Writ>,
    journal: Vec<MissionStep>,
}

impl CrewDescent {
    fn new(seating: CrewSeating, party: Party, run: AuthorizedDescent) -> CrewDescent {
        CrewDescent {
            seating,
            party,
            run,
            council: None,
            writ: None,
            journal: Vec::new(),
        }
    }

    // ── reading the mission ──────────────────────────────────────────────────────

    /// The seating (who holds which job, and where that came from).
    pub fn seating(&self) -> &CrewSeating {
        &self.seating
    }

    /// The crew's party world (custody, the loot split) — read-only.
    pub fn party(&self) -> &Party {
        &self.party
    }

    /// The live run: the mover's committed state, the day's map, the descent receipt chain.
    pub fn run(&self) -> &AuthorizedDescent {
        &self.run
    }

    /// Every committed move, in order.
    pub fn journal(&self) -> &[MissionStep] {
        &self.journal
    }

    /// The certified writ waiting for its hand, if any.
    pub fn writ(&self) -> Option<&Writ> {
        self.writ.as_ref()
    }

    /// The floor the crew is standing on.
    pub fn depth(&self) -> u64 {
        self.run.sim().depth
    }

    /// How much of the 26-breath light is left. THE clock: every verb any seat fires spends
    /// it, and a strike spends two.
    pub fn breath_left(&self) -> u64 {
        BREATH.saturating_sub(self.run.sim().spent)
    }

    /// How many relics the Bearer is carrying.
    pub fn pack(&self) -> u64 {
        self.run.sim().pack()
    }

    /// How many MORE relics the Bearer could take at this depth before the carry ceiling
    /// (`pack + depth ≤ CAP`) closes. The number the crew should be arguing about.
    pub fn carry_room(&self) -> u64 {
        CAP.saturating_sub(self.pack() + self.depth())
    }

    /// Whether the crew is still light enough to go one floor deeper. When this is `false`
    /// the certified push will come back as a real refusal from the capacity law — the
    /// Bearer's greed, priced by the dungeon.
    pub fn can_still_descend(&self) -> bool {
        self.pack() + self.depth() + 1 <= CAP
    }

    /// Whether the run has ended (the pack banked, the tomb frozen).
    pub fn is_home(&self) -> bool {
        self.run.sim().fate != 0
    }

    /// The haul the crew brought home — the number of relics the ledger says banked. `0`
    /// until the Mender takes them out.
    pub fn haul(&self) -> u64 {
        self.run
            .sim()
            .custody
            .iter()
            .filter(|&&custody| custody == BANKED)
            .count() as u64
    }

    /// Whether THE PRIZE (relic 0) is among the banked haul.
    pub fn crowned(&self) -> bool {
        self.run.sim().custody[0] == BANKED
    }

    /// A crew member's committed loot share, read off the party ledger (`0` before the split).
    pub fn share_of(&self, identity: &str) -> Option<u64> {
        let role = self.seating.role_of(identity)?;
        Some(self.party.loot_share(role.index()))
    }

    // ── a seat's own move ────────────────────────────────────────────────────────

    /// Sign `identity`'s own move with their custody key — only possible when the party
    /// holds that seat's secret (hotseat). A player holding their own secret signs off-box
    /// with [`CrewDescent::seat_move_message_for`] and submits via
    /// [`submit`](Self::submit).
    pub fn sign_seat_move(
        &self,
        identity: &str,
        mv: SeatMove,
    ) -> Result<SignedSeatMove, CrewDescentError> {
        let seat_index = self
            .party
            .seat_index_for(identity)
            .ok_or_else(|| CrewDescentError::NotOnTheCrew(identity.to_string()))?;
        let seat = self.party.seat(seat_index);
        let SeatCustody::Local(custodian) = seat.custody() else {
            return Err(CrewDescentError::RemoteCustody(identity.to_string()));
        };
        let step = self.run.step();
        let message = self.seat_move_message_for(&custodian.public_key(), step, mv.verb());
        Ok(SignedSeatMove {
            mover_pk: custodian.public_key(),
            mv,
            step,
            signature: custodian.sign_raw(&message),
        })
    }

    /// The exact bytes a seat must sign to submit `verb` at move ordinal `step` — what a
    /// player's own device needs, without the party ever holding their secret.
    pub fn seat_move_message_for(&self, mover_pk: &PublicKey, step: u64, verb: Verb) -> Vec<u8> {
        seat_move_message(
            &self.seating.charter.root(),
            &self.descent_cell(),
            step,
            verb,
            mover_pk,
        )
    }

    /// The descent world-cell this mission runs on — bound into every warrant so a warrant
    /// minted for one run never authorizes a move on another.
    fn descent_cell(&self) -> [u8; 32] {
        *self.run.descent().cell().as_bytes()
    }

    /// **Submit a seat's own authenticated move.** The order of refusals is the point:
    ///
    /// 1. the SIGNATURE is verified first, so a forgery builds no turn at all;
    /// 2. the signer must be a crew seat;
    /// 3. the signature must be for the CURRENT move ordinal (a warrant is single-use);
    /// 4. the mover's role must own the verb — otherwise [`OutOfRole`], naming whose job it
    ///    actually is;
    /// 5. and only then does the move reach the Lean-refereed executor, which is still free
    ///    to refuse it (no guardian to strike, the relic does not lie here, carrying rights
    ///    exhausted…).
    pub fn submit(&mut self, signed: &SignedSeatMove) -> Result<MissionStep, CrewDescentError> {
        let verb = signed.mv.verb();
        let message = self.seat_move_message_for(&signed.mover_pk, signed.step, verb);
        if !dregg_types::verify(&signed.mover_pk, &message, &signed.signature) {
            return Err(CrewDescentError::BadSignature);
        }
        let seat_index = self
            .party
            .seats()
            .iter()
            .position(|seat| seat.custody().public_key().0 == signed.mover_pk.0)
            .ok_or(CrewDescentError::NotOnTheCrew(
                "<a key that holds no crew seat>".to_string(),
            ))?;
        let identity = self.party.seat(seat_index).name().to_string();
        let step = self.run.step();
        if signed.step != step {
            return Err(CrewDescentError::StaleWarrant {
                signed_for: signed.step,
                current: step,
            });
        }
        let assigned = self
            .seating
            .role_of(&identity)
            .ok_or_else(|| CrewDescentError::NotOnTheCrew(identity.clone()))?;
        let owner = signed.mv.owner();
        if owner != assigned {
            return Err(CrewDescentError::OutOfRole(OutOfRole {
                identity,
                assigned,
                attempted: signed.mv,
                owner,
                owner_holder: self.seating.identity_in(owner).to_string(),
            }));
        }

        let warrant = self.seat_warrant(signed);
        let receipt = self.run.commit(verb, warrant).map_err(world_error)?;
        let record = MissionStep {
            step,
            verb,
            authority: Authority::Seat {
                identity,
                role: assigned,
            },
            warrant,
            receipt: receipt.turn_hash,
        };
        self.journal.push(record.clone());
        Ok(record)
    }

    /// Sign and submit `identity`'s own move in one call — the hotseat path.
    pub fn act(&mut self, identity: &str, mv: SeatMove) -> Result<MissionStep, CrewDescentError> {
        let signed = self.sign_seat_move(identity, mv)?;
        self.submit(&signed)
    }

    /// **The warrant a seat-authored move carries** — recomputable by anyone holding the
    /// public [`SignedSeatMove`] and the crew's charter, and checkable against the committed
    /// turn ([`receipt_carries_authorization`]).
    pub fn seat_warrant(&self, signed: &SignedSeatMove) -> [u8; 32] {
        let verb = signed.mv.verb();
        let mut material = Vec::new();
        material.extend_from_slice(&self.seating.charter.root());
        material.extend_from_slice(&self.descent_cell());
        material.extend_from_slice(&signed.step.to_be_bytes());
        material.push(verb.tag());
        material.extend_from_slice(&verb.arg().to_be_bytes());
        material.extend_from_slice(&signed.mover_pk.0);
        material.extend_from_slice(&signed.signature.0);
        blake3::derive_key(SEAT_WARRANT_CONTEXT, &material)
    }

    // ── the council ──────────────────────────────────────────────────────────────

    /// **Call the crew together.** Any crew member may put an irreversible question; nobody
    /// may put an ordinary one (a seat's job is a seat's job, not a committee's). Opens a
    /// REAL quorum round over the crew's custody public keys at the party's quorum.
    ///
    /// A [`Question::Split`] may be called only once the crew is home, and only over
    /// candidates that each sum to the haul the ledger says was banked — the argument about
    /// who gets what is bounded by arithmetic before it starts.
    pub fn call_council(
        &mut self,
        identity: &str,
        question: Question,
    ) -> Result<collective_choice::PollId, CrewDescentError> {
        if self.seating.role_of(identity).is_none() {
            return Err(CrewDescentError::NotOnTheCrew(identity.to_string()));
        }
        if self.council.is_some() {
            return Err(CrewDescentError::CouncilAlreadySitting);
        }

        let (prompt, options): (String, Vec<(String, Mandate)>) = match &question {
            Question::Push => (
                format!(
                    "Floor {}: one more, or hold? ({} breath left, {} carry room)",
                    self.depth(),
                    self.breath_left(),
                    self.carry_room()
                ),
                vec![
                    ("Push deeper".to_string(), Mandate::Descend),
                    ("Hold this floor".to_string(), Mandate::Hold),
                ],
            ),
            Question::ClimbOut => (
                format!(
                    "Take what we have and go? ({} in the pack, {} breath left)",
                    self.pack(),
                    self.breath_left()
                ),
                vec![
                    ("Climb out".to_string(), Mandate::ClimbOut),
                    ("Press on".to_string(), Mandate::Hold),
                ],
            ),
            Question::Split { candidates } => {
                if !self.is_home() {
                    return Err(CrewDescentError::NotHomeYet);
                }
                if candidates.len() < 2 {
                    return Err(CrewDescentError::MalformedQuestion(
                        "a split council needs at least two candidate divisions to be a decision"
                            .to_string(),
                    ));
                }
                let haul = self.haul();
                for (label, shares) in candidates {
                    let total: u64 = shares.iter().copied().sum();
                    if total != haul {
                        return Err(CrewDescentError::SplitDoesNotMatchHaul {
                            label: label.clone(),
                            proposed: total,
                            haul,
                        });
                    }
                }
                (
                    format!("The haul is {haul}. How does it divide?"),
                    candidates
                        .iter()
                        .map(|(label, shares)| (label.clone(), Mandate::Split(*shares)))
                        .collect(),
                )
            }
        };

        let electorate: Vec<ElectorateSeat> = self
            .party
            .seats()
            .iter()
            .map(|seat| seat.electorate_seat())
            .collect();
        let proposals: Vec<Proposal> = options
            .iter()
            .enumerate()
            .map(|(index, (label, _))| Proposal::new(label.clone(), Command::at("council", index)))
            .collect();
        let round = CollectiveRound::open_with(
            prompt,
            proposals,
            &electorate,
            self.party.quorum(),
            FEDERATION,
        )
        .map_err(|error| CrewDescentError::Vote(error.to_string()))?;
        let poll = round.poll();
        self.council = Some(Council {
            round,
            question,
            mandates: options.into_iter().map(|(_, mandate)| mandate).collect(),
        });
        Ok(poll)
    }

    /// The sitting council's poll id — what a member needs to sign a ballot off-box.
    pub fn council_poll(&self) -> Option<collective_choice::PollId> {
        self.council.as_ref().map(|council| council.round.poll())
    }

    /// The sitting council's question.
    pub fn council_question(&self) -> Option<&Question> {
        self.council.as_ref().map(|council| &council.question)
    }

    /// The sitting council's ballot options (index-aligned with the vote), for a surface to
    /// render.
    pub fn council_options(&self) -> Option<Vec<(&str, &Mandate)>> {
        let council = self.council.as_ref()?;
        Some(
            council
                .round
                .proposals()
                .iter()
                .map(|proposal| proposal.label.as_str())
                .zip(council.mandates.iter())
                .collect(),
        )
    }

    /// The sitting council's monotone tally.
    pub fn council_tally(&self) -> Result<collective_choice::Tally, CrewDescentError> {
        let council = self.council.as_ref().ok_or(CrewDescentError::NoCouncil)?;
        council
            .round
            .tally()
            .map_err(|error| CrewDescentError::Vote(error.to_string()))
    }

    /// Cast `identity`'s own custody-signed ballot in the sitting council (hotseat custody).
    pub fn vote(&mut self, identity: &str, option: usize) -> Result<(), CrewDescentError> {
        let seat_index = self
            .party
            .seat_index_for(identity)
            .ok_or_else(|| CrewDescentError::NotOnTheCrew(identity.to_string()))?;
        let SeatCustody::Local(custodian) = self.party.seat(seat_index).custody() else {
            return Err(CrewDescentError::RemoteCustody(identity.to_string()));
        };
        let council = self.council.as_mut().ok_or(CrewDescentError::NoCouncil)?;
        let ballot = custodian.sign_ballot(council.round.poll(), option);
        council.round.cast(&ballot).map(|_| ()).map_err(vote_error)
    }

    /// Cast an externally produced ballot (the deployment shape: the member's secret never
    /// leaves their device).
    pub fn cast(&mut self, ballot: &SignedBallot) -> Result<(), CrewDescentError> {
        let council = self.council.as_mut().ok_or(CrewDescentError::NoCouncil)?;
        council.round.cast(ballot).map(|_| ()).map_err(vote_error)
    }

    /// **Settle the council.** Quorum-certifies the winner and mints the [`Writ`] its hand
    /// will carry out. Below quorum the `AffineLe` gate refuses the decision-turn: NOTHING is
    /// certified, the mission does not move, and the council stays open for more ballots.
    ///
    /// A certified [`Mandate::Hold`] closes the council and mints no writ — the crew decided
    /// not to move, which is a real answer.
    ///
    /// A newly certified writ REPLACES one still in hand: a crew that voted to push, was
    /// refused by the capacity law, and then voted to climb out has changed its mind, and the
    /// stale mandate should not linger.
    pub fn settle(&mut self) -> Result<Writ, CrewDescentError> {
        let council = self.council.as_mut().ok_or(CrewDescentError::NoCouncil)?;
        let quorum = self.party.quorum();
        let winner = match council.round.resolve() {
            Ok(Some(winner)) => winner,
            Ok(None) => return Err(CrewDescentError::BelowQuorum),
            Err(error) => return Err(CrewDescentError::Vote(error.to_string())),
        };
        let mandate = council.mandates[winner.decision.winner].clone();
        let writ = Writ {
            mandate: mandate.clone(),
            poll: council.round.poll(),
            winner: winner.decision.winner,
            winner_tally: winner.decision.winner_tally,
            total: winner.decision.total,
            quorum,
            label: winner.label,
        };
        self.council = None;
        if !matches!(mandate, Mandate::Hold) {
            self.writ = Some(writ.clone());
        }
        Ok(writ)
    }

    /// **The warrant a council-certified move carries** — recomputable by anyone holding the
    /// crew's charter and the certified decision.
    pub fn council_warrant(&self, writ: &Writ, step: u64, verb: Verb) -> [u8; 32] {
        let mut material = Vec::new();
        material.extend_from_slice(&self.seating.charter.root());
        material.extend_from_slice(&self.descent_cell());
        material.extend_from_slice(&step.to_be_bytes());
        material.push(verb.tag());
        material.extend_from_slice(&verb.arg().to_be_bytes());
        material.extend_from_slice(writ.poll.0.as_bytes());
        material.extend_from_slice(&(writ.winner as u64).to_be_bytes());
        material.extend_from_slice(&writ.winner_tally.to_be_bytes());
        material.extend_from_slice(&writ.total.to_be_bytes());
        material.extend_from_slice(&writ.quorum.to_be_bytes());
        blake3::derive_key(COUNCIL_WARRANT_CONTEXT, &material)
    }

    /// **Carry out the crew's certified decision.** The hand must be the role whose job it is
    /// — the Pathfinder takes the certified step, the Mender takes the crew home — and any
    /// crew member may pay out a certified split (the certificate is the authority; the
    /// arithmetic needs no rank).
    ///
    /// The writ is consumed only by a move that actually COMMITS: a certified push the
    /// capacity law refuses leaves the writ in hand, so the crew can drop weight and try
    /// again rather than having to re-vote.
    pub fn carry_out(&mut self, identity: &str) -> Result<MissionStep, CrewDescentError> {
        let Some(assigned) = self.seating.role_of(identity) else {
            return Err(CrewDescentError::NotOnTheCrew(identity.to_string()));
        };
        let writ = self.writ.clone().ok_or(CrewDescentError::NoWrit)?;
        if let Some(hand) = writ.mandate.hand()
            && hand != assigned
        {
            return Err(CrewDescentError::WrongHand {
                mandate: writ.mandate.clone(),
                required: hand,
                holder: self.seating.identity_in(hand).to_string(),
                attempted: identity.to_string(),
                attempted_role: assigned,
            });
        }

        match writ.mandate {
            Mandate::Hold => Err(CrewDescentError::NothingToCarryOut),
            Mandate::Split(shares) => {
                // The party's loot slots are indexed by ROLE; the crew's shares by CHARTER
                // SEAT — translate so a share follows the MEMBER, not the job they drew.
                let mut by_role = [0u64; CREW_SEATS];
                for (seat, share) in shares.into_iter().enumerate() {
                    by_role[self.seating.roles[seat].index()] = share;
                }
                // The split is a party-world turn, not a descent verb; it is warranted
                // under the terminal verb that produced the haul, and the certificate rides
                // that turn exactly as a descent move's does.
                let step = self.run.step();
                let warrant = self.council_warrant(&writ, step, Verb::Flee);
                match self.party.split_loot_certified(&by_role, warrant) {
                    ActOutcome::Committed { receipt } => {
                        let record = MissionStep {
                            step,
                            verb: Verb::Flee,
                            authority: Authority::Council {
                                mandate: writ.mandate.clone(),
                                hand: identity.to_string(),
                                winner_tally: writ.winner_tally,
                                total: writ.total,
                            },
                            warrant,
                            receipt,
                        };
                        self.writ = None;
                        self.journal.push(record.clone());
                        Ok(record)
                    }
                    ActOutcome::Refused { reason } => Err(CrewDescentError::World(reason)),
                }
            }
            ref mandate => {
                let verb = mandate.verb().expect("descend and climb-out carry a verb");
                let step = self.run.step();
                let warrant = self.council_warrant(&writ, step, verb);
                let receipt = self.run.commit(verb, warrant).map_err(world_error)?;
                let record = MissionStep {
                    step,
                    verb,
                    authority: Authority::Council {
                        mandate: writ.mandate.clone(),
                        hand: identity.to_string(),
                        winner_tally: writ.winner_tally,
                        total: writ.total,
                    },
                    warrant,
                    receipt: receipt.turn_hash,
                };
                self.writ = None;
                self.journal.push(record.clone());
                Ok(record)
            }
        }
    }

    /// Check a journalled move against the ledger it landed on: the committed turn must
    /// carry exactly the warrant this mission recorded. The join between "the crew says this
    /// move was authorized" and "the receipt chain says so".
    ///
    /// Descent verbs land on the descent's world; a certified split lands on the party's.
    /// Both carry their warrant in-turn, so both are checkable — and a warrant no turn
    /// carries verifies against neither.
    pub fn verify_step(&self, record: &MissionStep) -> bool {
        let on_descent = self
            .run
            .descent()
            .world()
            .receipt_chain_snapshot()
            .iter()
            .any(|receipt| {
                receipt.turn_hash == record.receipt
                    && receipt_carries_authorization(receipt, &record.warrant)
            });
        on_descent
            || self.party.world().receipts().iter().any(|receipt| {
                receipt.turn_hash == record.receipt
                    && crate::receipt_carries_split_certificate(receipt, &record.warrant)
            })
    }

    /// **The replay tooth — is there a move on this run the crew never authorized?**
    ///
    /// Walks the descent's whole receipt chain and returns the turn hashes that no journalled
    /// warrant accounts for: a turn carrying a warrant the mission never minted, or a turn
    /// carrying no warrant at all once the mission has begun. (The deploy-time genesis mint
    /// precedes the crew and carries none; it is the untouched prefix, not a finding.)
    ///
    /// This is what the in-turn warrant is FOR. A host that drove the descent around the
    /// crew layer — no council, no signature — leaves turns that show up here, because the
    /// evidence lives on the ledger rather than in the host's log.
    pub fn unwarranted_turns(&self) -> Vec<[u8; 32]> {
        let journalled: std::collections::BTreeSet<[u8; 32]> =
            self.journal.iter().map(|record| record.warrant).collect();
        let chain = self.run.descent().world().receipt_chain_snapshot();
        let mut begun = false;
        let mut unwarranted = Vec::new();
        for receipt in &chain {
            match dungeon_on_dregg::authorized_descent::receipt_authorization(receipt) {
                Some(warrant) => {
                    begun = true;
                    if !journalled.contains(&warrant) {
                        unwarranted.push(receipt.turn_hash);
                    }
                }
                None if begun => unwarranted.push(receipt.turn_hash),
                None => {}
            }
        }
        unwarranted
    }
}

// ── The customary divisions ──────────────────────────────────────────────────────

/// An even division of `haul` across the crew, remainder to the earliest charter seats — the
/// default a crew argues FROM.
pub fn even_split(haul: u64) -> [u64; CREW_SEATS] {
    let base = haul / CREW_SEATS as u64;
    let remainder = haul % CREW_SEATS as u64;
    std::array::from_fn(|seat| base + u64::from((seat as u64) < remainder))
}

/// An even division with one seat cut an extra share off the top (the Bearer who carried it,
/// the Mender who got everyone home — whoever the crew thinks earned it). `seat` is a CHARTER
/// seat. Falls back to [`even_split`] when the haul is too small to cut.
pub fn weighted_split(haul: u64, seat: usize) -> [u64; CREW_SEATS] {
    if haul == 0 || seat >= CREW_SEATS {
        return even_split(haul);
    }
    let mut shares = even_split(haul - 1);
    shares[seat] += 1;
    shares
}

// ── Refusals ─────────────────────────────────────────────────────────────────────

/// **A move outside the mover's job, refused by name** — who tried it, the role the seating
/// gave them, and whose job it actually was.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OutOfRole {
    /// The member who tried it.
    pub identity: String,
    /// The role the seating gave them.
    pub assigned: Role,
    /// The move they attempted.
    pub attempted: SeatMove,
    /// The role that owns that move.
    pub owner: Role,
    /// The crew member holding that role.
    pub owner_holder: String,
}

impl std::fmt::Display for OutOfRole {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} holds the {} seat and attempted {:?}, which is {}'s job ({})",
            self.identity,
            self.assigned.name(),
            self.attempted,
            self.owner.name(),
            self.owner_holder
        )
    }
}

impl std::error::Error for OutOfRole {}

/// Why an away-mission step did not happen.
#[derive(Clone, Debug)]
pub enum CrewDescentError {
    /// The caller holds no seat on this crew.
    NotOnTheCrew(String),
    /// The move's signature did not verify against the claimed key — a missing, forged,
    /// wrong-key, or re-pointed signature. Nothing was built (the mission does not move).
    BadSignature,
    /// The signature was minted for a different move ordinal: a warrant is single-use, so a
    /// signature cannot be replayed once the mission has moved on.
    StaleWarrant {
        /// The ordinal the signature covers.
        signed_for: u64,
        /// The mission's current ordinal.
        current: u64,
    },
    /// The mover acted outside the job the seating gave them.
    OutOfRole(OutOfRole),
    /// This seat's secret lives with its player; the party cannot sign for them.
    RemoteCustody(String),
    /// No custody public key was supplied for a crew member.
    NoCustodyKey(String),
    /// A council is already sitting — one question at a time.
    CouncilAlreadySitting,
    /// No council is sitting.
    NoCouncil,
    /// The council has not reached quorum: nothing is certified and the mission does not
    /// move. The council stays open.
    BelowQuorum,
    /// No certified writ is waiting.
    NoWrit,
    /// The crew certified `Hold` — there is nothing to carry out.
    NothingToCarryOut,
    /// The certified decision is not this member's to execute.
    WrongHand {
        /// What the crew certified.
        mandate: Mandate,
        /// The role whose job it is.
        required: Role,
        /// The member holding that role.
        holder: String,
        /// The member who tried.
        attempted: String,
        /// The role they actually hold.
        attempted_role: Role,
    },
    /// A split council was called before the crew came home.
    NotHomeYet,
    /// A candidate division does not add up to the haul the ledger says was banked.
    SplitDoesNotMatchHaul {
        /// The candidate's label.
        label: String,
        /// What it proposes to hand out.
        proposed: u64,
        /// What was actually banked.
        haul: u64,
    },
    /// The question was malformed.
    MalformedQuestion(String),
    /// The vote engine refused (an ineligible voter, a forged ballot, a double vote).
    Vote(String),
    /// **The dungeon refused the move.** The Lean-refereed executor (or the mover it
    /// projects through) said no: the way is shut, the guardian still stands, the light is
    /// out, carrying rights are exhausted. A quorum cannot vote past this.
    World(String),
    /// The seating could not be lowered into a cap-seated party.
    Formation(PartyFormationError),
}

impl std::fmt::Display for CrewDescentError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CrewDescentError::NotOnTheCrew(identity) => {
                write!(f, "{identity:?} holds no seat on this crew")
            }
            CrewDescentError::BadSignature => write!(
                f,
                "the move's signature did not verify against the claimed custody key"
            ),
            CrewDescentError::StaleWarrant {
                signed_for,
                current,
            } => write!(
                f,
                "that move was signed for step {signed_for}; the mission is at step {current}"
            ),
            CrewDescentError::OutOfRole(out) => write!(f, "{out}"),
            CrewDescentError::RemoteCustody(identity) => write!(
                f,
                "{identity:?} holds their own secret; the party cannot sign for them"
            ),
            CrewDescentError::NoCustodyKey(identity) => {
                write!(f, "no custody public key was supplied for {identity:?}")
            }
            CrewDescentError::CouncilAlreadySitting => {
                write!(f, "a council is already sitting — settle it first")
            }
            CrewDescentError::NoCouncil => write!(f, "no council is sitting"),
            CrewDescentError::BelowQuorum => write!(
                f,
                "below quorum — nothing is certified and the crew does not move"
            ),
            CrewDescentError::NoWrit => write!(
                f,
                "the crew has certified nothing — this is the crew's call, not a seat's"
            ),
            CrewDescentError::NothingToCarryOut => {
                write!(f, "the crew voted to hold — there is nothing to carry out")
            }
            CrewDescentError::WrongHand {
                required,
                holder,
                attempted,
                attempted_role,
                ..
            } => write!(
                f,
                "{attempted} holds the {} seat; the crew's decision is the {} seat's to carry out ({holder})",
                attempted_role.name(),
                required.name()
            ),
            CrewDescentError::NotHomeYet => write!(
                f,
                "the haul is not banked yet — a split is decided once the crew is home"
            ),
            CrewDescentError::SplitDoesNotMatchHaul {
                label,
                proposed,
                haul,
            } => write!(
                f,
                "the division {label:?} hands out {proposed} of a {haul}-relic haul"
            ),
            CrewDescentError::MalformedQuestion(reason) => write!(f, "{reason}"),
            CrewDescentError::Vote(reason) => write!(f, "the vote engine refused: {reason}"),
            CrewDescentError::World(reason) => write!(f, "the dungeon refused: {reason}"),
            CrewDescentError::Formation(error) => {
                write!(f, "the crew could not be seated: {error}")
            }
        }
    }
}

impl std::error::Error for CrewDescentError {}

fn world_error(error: impl std::fmt::Display) -> CrewDescentError {
    CrewDescentError::World(error.to_string())
}

fn vote_error(error: CollectiveError) -> CrewDescentError {
    CrewDescentError::Vote(error.to_string())
}

#[cfg(test)]
mod tests;
