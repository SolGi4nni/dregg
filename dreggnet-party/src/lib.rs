//! # `dreggnet-party` — FIRST-CLASS PARTIES ("the crowd IS the party, each seat a job")
//!
//! The biggest play-together unlock of the game roadmap (`docs/GAME-INFRA-ROADMAP.md`
//! §SOCIAL #1), landed on the REAL multi-actor dregg substrate. A **party** is a fixed
//! roster of `N` seated identities that share ONE run, ONE objective, and an on-ledger
//! loot split — and each seat is a real player-cell whose held capabilities ARE its
//! **role**. This is the escape from TPP-mush: not `N` interchangeable voters, but a
//! DIVISION OF LABOR the executor enforces move-for-move.
//!
//! ## The five teeth (each executor-refereed, each DRIVEN + non-vacuous)
//!
//! 1. **A roster of N seated player-cells** ([`Party::muster`]). Each [`Seat`] is a real
//!    cell/identity in ONE shared [`World`](starbridge_v2::world::World) ledger, holding a
//!    custody keypair (its ballot identity) and a [`Role`] whose capability grants ARE its
//!    mandate.
//! 2. **SEATED CO-OP with distinct caps** ([`Party::act`]). The tank holds a cap only to
//!    the front-rank cell, the scout only to the trap/lock cell, the mage to the spell +
//!    focus cells, the healer to the rally + focus cells. A seat firing a move OUTSIDE its
//!    role writes a cell it holds no cap to — a real `CapabilityNotHeld` refusal
//!    ([`ActOutcome::Refused`]). Nobody plays your seat; forging a teammate's move is
//!    refused by the kernel, not a host `if`.
//! 3. **A COLLECTIVE decision at a fork** ([`Party::open_fork`] → [`PartyFork`]). A signed
//!    party ballot on the REAL [`collective_choice`] quorum engine: each seat SIGNS its
//!    ballot with its custody key; a non-member vote is `Ineligible`, a forged/wrong-key
//!    vote `BadSignature`, and only a quorum-certified winner
//!    ([`PartyFork::resolve_into`]) fires the shared move into the party world as a real
//!    turn. A sub-quorum round moves NOTHING.
//! 4. **A shared FOCUS pool** (the `focus` cell). A party-wide
//!    [`FieldLteField`](dregg_cell::StateConstraint::FieldLteField) budget the kernel
//!    re-checks on every spend: the mage AND the healer draw on the SAME pool, so it caps
//!    the PARTY, not one seat. An overspend is refused; an in-budget spend commits.
//! 5. **An on-ledger LOOT SPLIT** ([`Party::split_loot`]). Each seat's share is a
//!    committed cell field, [`WriteOnce`](dregg_cell::StateConstraint::WriteOnce)-frozen so
//!    it can NEVER be re-written — a ledger FACT, not a leader's promise. "We cleared it
//!    together" is a receipt.
//!
//! ## The verifiable edge
//!
//! Nobody plays your seat (distinct caps, executor-gated), nobody forges your vote (a real
//! ed25519 custody signature over the ballot), nobody fakes the loot split (a committed,
//! WriteOnce-frozen ledger fact). Every refusal is the real executor / vote-engine firing,
//! and every "yes" is a real committed [`TurnReceipt`](dregg_app_framework::TurnReceipt).
//!
//! ## Honest scope (named residuals, not holes)
//!
//! * **Role ABILITY KITS.** A role's move here writes a role-marked cell + (for casters)
//!    spends the shared focus — enough to prove the cap-gated division of labor. Wiring
//!    each role to a full ability kit (the built-but-idle `dungeon-on-dregg::spells`, the
//!    combat `Arena`) is the named follow-on.
//! * **Live party-formation UX.** [`Party::muster`] mints the roster at genesis; join /
//!    leave / invite (a seat minting its own cell + custody key and enrolling into the
//!    electorate) is the session layer above the world.
//! * **RAIDS.** A party acts turn-by-turn on ONE serial world here. The concurrent
//!    multi-cell battle (each seat its own cell acting SIMULTANEOUSLY, phases gating on
//!    prior-phase completion) is the raid frontier `combat.rs` / `mud.rs` name — staged
//!    after parties.

use dregg_app_framework::field_from_u64;
use dregg_cell::{AuthRequired, CellId, CellProgram, FieldElement, StateConstraint};
use dregg_turn::action::Effect;
use starbridge_v2::world::{CommitOutcome, World, make_open_cell, set_field};

use dungeon_on_dregg::collective::{
    CollectiveError, CollectiveRound, Custodian, Proposal, Seat as ElectorateSeat, SignedBallot,
};
use dungeon_on_dregg::narrator::Command;

// ── Party parameters (the balance numbers; the teeth guarantee the invariants) ───

/// The shared party FOCUS budget (a [`FieldLteField`](StateConstraint::FieldLteField)
/// cross-slot bound on the `focus` cell). Both caster seats draw on this ONE pool.
pub const FOCUS_BUDGET: u64 = 40;
/// The focus a single cast (mage ward / healer rally) spends from the shared pool.
/// With [`FOCUS_BUDGET`] = 40 the party affords TWO casts across the whole roster; a
/// third — from EITHER caster — overspends and is refused (the pool caps the party).
pub const FOCUS_COST: u64 = 15;

/// The `focus` cell slot holding the party's total focus SPENT (the accumulator a
/// spend advances; the `FieldLteField` left operand).
pub const FOCUS_SPENT_SLOT: usize = 0;
/// The `focus` cell slot holding the party BUDGET (seeded at genesis; the
/// `FieldLteField` right operand — a spend must keep `spent <= budget`).
pub const FOCUS_BUDGET_SLOT: usize = 1;

/// The state slot a role move stamps on its target cell (proof the move LANDED — a
/// non-zero reading a stranger reads off the ledger).
pub const ROLE_SLOT: usize = 0;
/// The marker a role move writes into [`ROLE_SLOT`] (a real, non-empty reading).
const ROLE_MARK: u64 = 1;
/// The `gate` cell slot the certified fork move writes the chosen path into.
pub const GATE_SLOT: usize = 0;

/// The federation the fork's backing [`collective_choice`] ballots commit under.
const FEDERATION: [u8; 32] = [0xB1; 32];

/// The executor signing seed the party world commits receipts under (a fixed demo key,
/// so every committed receipt carries a genuine executor signature under one authority).
const EXECUTOR_SEED: [u8; 32] = [0x9C; 32];

// ── Roles — a seat's capability set IS its mandate ───────────────────────────────

/// A seat's **role** — the division of labor. A role fixes WHICH cells a seat holds a
/// capability to (its mandate) and WHICH move it may fire. A seat cannot act outside its
/// role: the cells its role does not reach are cells it holds no cap to, so a move onto
/// them is a real executor refusal.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Role {
    /// The front line — acts on the front-rank cell (holds the enemy at the gate). No
    /// focus (a martial seat).
    Tank,
    /// The infiltrator — acts on the trap/lock cell (disarms what bars the way). No focus.
    Scout,
    /// The caster — acts on the spell (`ward`) cell AND draws on the shared focus pool.
    Mage,
    /// The mender — acts on the party-unit (`rally`) cell AND draws on the shared focus
    /// pool (so the pool is contested ACROSS two seats).
    Healer,
}

impl Role {
    /// The role's display name.
    pub fn name(self) -> &'static str {
        match self {
            Role::Tank => "Tank",
            Role::Scout => "Scout",
            Role::Mage => "Mage",
            Role::Healer => "Healer",
        }
    }

    /// The party move this role fires (its seat's ONLY sanctioned move).
    pub fn move_of(self) -> PartyMove {
        match self {
            Role::Tank => PartyMove::GuardFront,
            Role::Scout => PartyMove::DisarmLock,
            Role::Mage => PartyMove::CastWard,
            Role::Healer => PartyMove::Rally,
        }
    }
}

/// A move a seat can attempt — the union of every role's move. [`Party::act`] lowers it to
/// cell-write effects and lets the REAL executor referee: a move whose target cells the
/// acting seat holds no cap to is refused (forging / acting outside your seat), no host
/// role-check involved.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PartyMove {
    /// Tank: hold the front-rank cell.
    GuardFront,
    /// Scout: disarm the trap/lock cell.
    DisarmLock,
    /// Mage: cast on the spell cell AND spend from the shared focus pool.
    CastWard,
    /// Healer: rally the party-unit cell AND spend from the shared focus pool.
    Rally,
}

// ── The seated roster ────────────────────────────────────────────────────────────

/// A **seat** — one identity in the party. A real player-cell in the shared ledger
/// (`cell`, whose held capabilities ARE its [`role`](Seat::role) mandate) bound to a real
/// ed25519 CUSTODY keypair (`custodian`, its electorate identity for the fork ballot). The
/// secret stays with the seat; its public key is what the fork's electorate checks a ballot
/// against.
pub struct Seat {
    role: Role,
    name: String,
    cell: CellId,
    custodian: Custodian,
}

impl Seat {
    /// This seat's role.
    pub fn role(&self) -> Role {
        self.role
    }
    /// This seat's display name.
    pub fn name(&self) -> &str {
        &self.name
    }
    /// This seat's real player-cell id (its identity in the shared ledger).
    pub fn cell(&self) -> CellId {
        self.cell
    }
    /// This seat's registered electorate identity (name + custody public key) — enrolled
    /// into a fork's electorate. The secret is NOT included.
    pub fn electorate_seat(&self) -> ElectorateSeat {
        self.custodian.seat()
    }
}

/// The fixed cell [`Layout`] of a party's shared world — the role-target cells, the shared
/// focus pool, the fork gate, and the loot-split cell.
#[derive(Clone, Copy, Debug)]
pub struct Layout {
    /// The party ROOT cell — the agent party-level moves (fork resolution, loot split) are
    /// attributed to; holds caps to `gate` + `loot`.
    pub party: CellId,
    /// The front-rank cell — only the TANK seat holds a cap.
    pub front: CellId,
    /// The trap/lock cell — only the SCOUT seat holds a cap.
    pub lock: CellId,
    /// The spell cell — only the MAGE seat holds a cap.
    pub ward: CellId,
    /// The party-unit cell — only the HEALER seat holds a cap.
    pub rally: CellId,
    /// The shared FOCUS pool — a `FieldLteField(spent <= budget)` cell; MAGE + HEALER both
    /// hold a cap (the party-wide resource).
    pub focus: CellId,
    /// The fork GATE — the shared cell a quorum-certified fork move writes into.
    pub gate: CellId,
    /// The LOOT-SPLIT cell — each seat's share a `WriteOnce` slot (an on-ledger fact).
    pub loot: CellId,
}

// ── The party ────────────────────────────────────────────────────────────────────

/// **A first-class party** — a fixed roster of seated player-cells sharing ONE
/// [`World`](starbridge_v2::world::World) ledger, one focus pool, and one on-ledger loot
/// split. Built by [`Party::muster`].
pub struct Party {
    world: World,
    seats: Vec<Seat>,
    layout: Layout,
    quorum: u64,
}

impl Party {
    /// **Muster the canonical party** — a roster of four distinct-role seats (Tank,
    /// Scout, Mage, Healer) in one shared world, each a real player-cell whose held caps
    /// ARE its role. Sets up the shared cells with their real teeth (the focus pool's
    /// `FieldLteField` budget, the loot cell's per-seat `WriteOnce` shares) and grants each
    /// seat exactly its role's mandate:
    ///
    /// | seat   | role   | may act on         |
    /// |--------|--------|--------------------|
    /// | Bramwen| Tank   | `front`            |
    /// | Corvin | Scout  | `lock`             |
    /// | Della  | Mage   | `ward`, `focus`    |
    /// | Ferro  | Healer | `rally`, `focus`   |
    ///
    /// The quorum for a fork ballot is a majority of the roster (3 of 4).
    pub fn muster() -> Party {
        let mut world = World::new().with_executor_signing_key(EXECUTOR_SEED);

        // The role-target cells (open — reach is what the caps gate).
        let front = world.genesis_cell(0x51, 0);
        let lock = world.genesis_cell(0x52, 0);
        let ward = world.genesis_cell(0x53, 0);
        let rally = world.genesis_cell(0x54, 0);
        let gate = world.genesis_cell(0x56, 0);

        // THE SHARED FOCUS POOL: a cell seeded with the party budget and carrying the
        // real `FieldLteField(spent <= budget)` tooth. Built at genesis with the budget
        // slot pre-set (genesis bypasses the executor, so the predicate bites only on
        // turns) and the predicate installed.
        let mut focus_cell = make_open_cell(0x55, 0);
        focus_cell.state.fields[FOCUS_BUDGET_SLOT] = field_from_u64(FOCUS_BUDGET);
        focus_cell.program = CellProgram::Predicate(vec![StateConstraint::FieldLteField {
            left_index: FOCUS_SPENT_SLOT as u8,
            right_index: FOCUS_BUDGET_SLOT as u8,
        }]);
        let focus = world.genesis_install(focus_cell);

        // THE LOOT-SPLIT CELL: each of the four seat-share slots is WRITE-ONCE — the split
        // commits once (0 -> share) and can NEVER be re-written (a ledger fact).
        let loot = world.genesis_cell(0x57, 0);
        world.set_cell_program(
            &loot,
            CellProgram::Predicate(
                (0..4u8)
                    .map(|i| StateConstraint::WriteOnce { index: i })
                    .collect(),
            ),
        );

        // The four seats — each a real player-cell holding ONLY its role's caps, plus a
        // deterministic demo custody keypair (its ballot identity).
        let roster = [
            (Role::Tank, "Bramwen", 0x0A, vec![front]),
            (Role::Scout, "Corvin", 0x0B, vec![lock]),
            (Role::Mage, "Della", 0x0C, vec![ward, focus]),
            (Role::Healer, "Ferro", 0x0D, vec![rally, focus]),
        ];
        let seats: Vec<Seat> = roster
            .into_iter()
            .map(|(role, name, seed, caps)| {
                let cell = install_seat(&mut world, seed, &caps);
                Seat {
                    role,
                    name: name.to_string(),
                    cell,
                    custodian: Custodian::demo(name),
                }
            })
            .collect();

        // The party ROOT — the agent party-level moves are attributed to; reaches the
        // shared `gate` (fork resolution) + `loot` (the split).
        let party = install_seat(&mut world, 0x40, &[gate, loot]);

        Party {
            world,
            seats,
            layout: Layout {
                party,
                front,
                lock,
                ward,
                rally,
                focus,
                gate,
                loot,
            },
            quorum: 3,
        }
    }

    /// The party's shared cell [`Layout`].
    pub fn layout(&self) -> Layout {
        self.layout
    }

    /// The seated roster (index-aligned with [`Self::seat`]).
    pub fn seats(&self) -> &[Seat] {
        &self.seats
    }

    /// The number of seats in the roster.
    pub fn seat_count(&self) -> usize {
        self.seats.len()
    }

    /// The seat at `idx`.
    pub fn seat(&self, idx: usize) -> &Seat {
        &self.seats[idx]
    }

    /// The fork-ballot quorum threshold `M` (a majority of the roster).
    pub fn quorum(&self) -> u64 {
        self.quorum
    }

    /// The live world (read-only) — for reading a cell's committed state.
    pub fn world(&self) -> &World {
        &self.world
    }

    /// Read `slot` of `cell` as a `u64` (the canonical big-endian decode) — `0` if the
    /// cell is absent from the shared ledger.
    pub fn read_field(&self, cell: CellId, slot: usize) -> u64 {
        self.world
            .ledger()
            .get(&cell)
            .map(|c| field_to_u64(&c.state.fields[slot]))
            .unwrap_or(0)
    }

    /// The party's total focus SPENT so far (the shared pool's accumulator).
    pub fn focus_spent(&self) -> u64 {
        self.read_field(self.layout.focus, FOCUS_SPENT_SLOT)
    }

    /// Seat `seat_idx`'s committed loot share (a ledger fact; `0` before the split).
    pub fn loot_share(&self, seat_idx: usize) -> u64 {
        self.read_field(self.layout.loot, seat_idx)
    }

    /// **Fire a move AS a seat** — the seated-co-op path. Lowers `mv` to the cell-write
    /// effects it touches, builds a real turn attributed to the seat's player-cell, and
    /// commits it through the REAL executor. The executor is the sole referee:
    ///
    /// * a move within the seat's role touches cells the seat holds caps to → COMMITS;
    /// * a move OUTSIDE the seat's role (or forging a teammate's move) touches a cell the
    ///   seat holds no cap to → a real `CapabilityNotHeld` refusal ([`ActOutcome::Refused`],
    ///   never a silent apply);
    /// * a caster's spend that would exceed the shared focus budget fails the pool's
    ///   `FieldLteField` tooth → refused.
    pub fn act(&mut self, seat_idx: usize, mv: PartyMove) -> ActOutcome {
        let seat_cell = self.seats[seat_idx].cell;
        let effects = self.lower_move(mv);
        let turn = self.world.turn(seat_cell, effects);
        commit_to_outcome(self.world.commit_turn(turn))
    }

    /// Fire a seat's OWN role move (the sanctioned path — sugar for
    /// `act(seat_idx, seats[seat_idx].role().move_of())`).
    pub fn act_in_role(&mut self, seat_idx: usize) -> ActOutcome {
        self.act(seat_idx, self.seats[seat_idx].role.move_of())
    }

    /// Lower a [`PartyMove`] to the cell-write effects a turn carries. A caster's spend
    /// reads the CURRENT committed focus-spent and advances it by [`FOCUS_COST`] (the pool
    /// is shared, so this composes across seats' turns).
    fn lower_move(&self, mv: PartyMove) -> Vec<Effect> {
        let l = &self.layout;
        let mark = field_from_u64(ROLE_MARK);
        match mv {
            PartyMove::GuardFront => vec![set_field(l.front, ROLE_SLOT, mark)],
            PartyMove::DisarmLock => vec![set_field(l.lock, ROLE_SLOT, mark)],
            PartyMove::CastWard => {
                let next = self.focus_spent() + FOCUS_COST;
                vec![
                    set_field(l.ward, ROLE_SLOT, mark),
                    set_field(l.focus, FOCUS_SPENT_SLOT, field_from_u64(next)),
                ]
            }
            PartyMove::Rally => {
                let next = self.focus_spent() + FOCUS_COST;
                vec![
                    set_field(l.rally, ROLE_SLOT, mark),
                    set_field(l.focus, FOCUS_SPENT_SLOT, field_from_u64(next)),
                ]
            }
        }
    }

    /// **Commit the party's on-ledger LOOT SPLIT** — write each seat's `shares[i]` into the
    /// loot cell's `WriteOnce` slot `i`, as one real turn attributed to the party root.
    /// The split becomes a committed LEDGER FACT: readable by anyone
    /// ([`Self::loot_share`]) and un-alterable — a second split (a re-write to a different
    /// share) fails the `WriteOnce` tooth. Not a leader's promise: a receipt.
    ///
    /// `shares` must have one entry per seat.
    pub fn split_loot(&mut self, shares: &[u64]) -> ActOutcome {
        assert_eq!(
            shares.len(),
            self.seats.len(),
            "the loot split names one share per seat"
        );
        let loot = self.layout.loot;
        let effects: Vec<Effect> = shares
            .iter()
            .enumerate()
            .map(|(i, &s)| set_field(loot, i, field_from_u64(s)))
            .collect();
        let turn = self.world.turn(self.layout.party, effects);
        commit_to_outcome(self.world.commit_turn(turn))
    }

    /// **Open a fork ballot** over the party roster — a signed collective decision at a
    /// genuine fork. Each `(label, path)` is a candidate shared move: `path` is the value
    /// the certified winner writes into the fork `gate` cell. Stands up a REAL
    /// [`CollectiveRound`] whose electorate is the seats' custody public keys and whose
    /// quorum is the party's ([`Self::quorum`]). A seat casts a signed ballot
    /// ([`Party::sign_ballot`]); the quorum-certified winner resolves into this world via
    /// [`PartyFork::resolve_into`].
    pub fn open_fork(
        &self,
        question: impl Into<String>,
        options: Vec<(String, u64)>,
    ) -> Result<PartyFork, CollectiveError> {
        let electorate: Vec<ElectorateSeat> =
            self.seats.iter().map(|s| s.electorate_seat()).collect();
        let proposals: Vec<Proposal> = options
            .iter()
            .enumerate()
            .map(|(i, (label, _))| Proposal::new(label.clone(), Command::at("fork", i)))
            .collect();
        let round =
            CollectiveRound::open_with(question, proposals, &electorate, self.quorum, FEDERATION)?;
        let paths = options.into_iter().map(|(_, p)| p).collect();
        Ok(PartyFork { round, paths })
    }

    /// Sign seat `seat_idx`'s ballot for `option` in `fork` — with the seat's OWN custody
    /// key (the seated identity). The returned [`SignedBallot`] is what
    /// [`PartyFork::cast`] admits.
    pub fn sign_ballot(&self, fork: &PartyFork, seat_idx: usize, option: usize) -> SignedBallot {
        self.seats[seat_idx]
            .custodian
            .sign_ballot(fork.poll(), option)
    }
}

// ── The fork ballot ──────────────────────────────────────────────────────────────

/// A **party fork** — a live signed ballot over the roster ([`Party::open_fork`]). Wraps a
/// REAL [`CollectiveRound`] (WriteOnce ballots + a monotone tally + the polis `AffineLe`
/// quorum gate) plus the per-option `path` a certified winner writes into the fork gate.
pub struct PartyFork {
    round: CollectiveRound,
    /// Index-aligned with the round's proposals: the value the winner writes into `gate`.
    paths: Vec<u64>,
}

impl PartyFork {
    /// The open poll's id (a seat needs it to sign a ballot — [`Party::sign_ballot`]).
    pub fn poll(&self) -> collective_choice::PollId {
        self.round.poll()
    }

    /// **Cast a seat's signature-authenticated ballot** — a real cap-bounded turn on the
    /// vote engine, admitted ONLY under a valid custody signature. A missing / wrong-key /
    /// forged / re-pointed signature is [`CollectiveError::BadSignature`]; a valid signature
    /// by a NON-seated key is [`VoteError::Ineligible`](collective_choice::VoteError); a
    /// second ballot by the same seat is [`VoteError::DoubleVote`]. Nothing commits on a
    /// refusal (the board does not move).
    pub fn cast(&mut self, ballot: &SignedBallot) -> Result<(), CollectiveError> {
        self.round.cast(ballot).map(|_receipt| ())
    }

    /// The per-option tally (the monotone verified board).
    pub fn tally(&self) -> Result<collective_choice::Tally, CollectiveError> {
        self.round.tally()
    }

    /// **Resolve the fork into the party world** — quorum-certify the winner, then fire its
    /// shared move (writing the winning `path` into the party's fork `gate` cell) as a real
    /// turn attributed to the party root. Below quorum the `AffineLe` gate refuses the
    /// decision-turn: no winner, no world move ([`ForkError::BelowQuorum`]) — the world is
    /// unchanged.
    pub fn resolve_into(&mut self, party: &mut Party) -> Result<ForkResolution, ForkError> {
        let winner = match self.round.resolve() {
            Ok(Some(w)) => w,
            Ok(None) => return Err(ForkError::BelowQuorum),
            Err(e) => return Err(ForkError::Vote(e)),
        };
        let idx = winner.decision.winner;
        let path = self.paths[idx];
        let gate = party.layout.gate;
        let turn = party.world.turn(
            party.layout.party,
            vec![set_field(gate, GATE_SLOT, field_from_u64(path))],
        );
        match party.world.commit_turn(turn) {
            CommitOutcome::Committed { receipt, .. } => Ok(ForkResolution {
                winner: idx,
                label: winner.label,
                path,
                winner_tally: winner.decision.winner_tally,
                total: winner.decision.total,
                receipt: receipt.turn_hash,
            }),
            CommitOutcome::Rejected { reason, .. } => Err(ForkError::WorldRefused(reason)),
            CommitOutcome::Queued { .. } => {
                Err(ForkError::WorldRefused("the world is suspended".into()))
            }
        }
    }
}

/// The payoff of a resolved fork — the quorum certificate + the real party-world turn the
/// certified shared move committed.
#[derive(Clone, Debug)]
pub struct ForkResolution {
    /// The certified winning option index.
    pub winner: usize,
    /// The winning option's label.
    pub label: String,
    /// The path the winner wrote into the fork `gate` cell.
    pub path: u64,
    /// The winner's tally.
    pub winner_tally: u64,
    /// The quorum-met total ballots.
    pub total: u64,
    /// The real committed party-world turn hash (the shared move's receipt).
    pub receipt: [u8; 32],
}

/// Why a fork could not resolve into the party world.
#[derive(Debug)]
pub enum ForkError {
    /// The round has not reached quorum — no winner certified, NO world move (unchanged).
    BelowQuorum,
    /// The backing vote engine refused (e.g. a query error).
    Vote(CollectiveError),
    /// The party world refused the certified shared move (should not occur for a legal
    /// gate write; surfaced fail-closed).
    WorldRefused(String),
}

impl std::fmt::Display for ForkError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ForkError::BelowQuorum => {
                write!(
                    f,
                    "below quorum — no winner certified, the world does not move"
                )
            }
            ForkError::Vote(e) => write!(f, "the vote engine refused: {e}"),
            ForkError::WorldRefused(r) => write!(f, "the party world refused the move: {r}"),
        }
    }
}

impl std::error::Error for ForkError {}

// ── The outcome of a seated move ─────────────────────────────────────────────────

/// The outcome of firing a seat's move — a legible echo of the real
/// [`CommitOutcome`](starbridge_v2::world::CommitOutcome).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ActOutcome {
    /// The move committed — a real signed turn landed on the shared ledger; carries the
    /// receipt's `turn_hash`.
    Committed {
        /// The committed turn's hash (proof of a genuine receipted turn).
        receipt: [u8; 32],
    },
    /// The move was REFUSED by the real executor (a `CapabilityNotHeld` seat/forge refusal,
    /// or the shared focus pool's `FieldLteField` refusing an overspend). Carries the
    /// executor's reason.
    Refused {
        /// The executor's refusal reason.
        reason: String,
    },
}

impl ActOutcome {
    /// Did the move commit?
    pub fn committed(&self) -> bool {
        matches!(self, ActOutcome::Committed { .. })
    }
    /// Was the move refused?
    pub fn refused(&self) -> bool {
        matches!(self, ActOutcome::Refused { .. })
    }
    /// The committed receipt hash, if it committed.
    pub fn receipt(&self) -> Option<[u8; 32]> {
        match self {
            ActOutcome::Committed { receipt } => Some(*receipt),
            ActOutcome::Refused { .. } => None,
        }
    }
    /// The refusal reason, if it was refused.
    pub fn reason(&self) -> Option<&str> {
        match self {
            ActOutcome::Refused { reason } => Some(reason),
            ActOutcome::Committed { .. } => None,
        }
    }
}

// ── helpers ──────────────────────────────────────────────────────────────────────

/// Install a player/root cell holding caps (`AuthRequired::None`) reaching each cell in
/// `caps` — the cell's mandate. Returns its genesis cell id.
fn install_seat(world: &mut World, seed: u8, caps: &[CellId]) -> CellId {
    let mut cell = make_open_cell(seed, 0);
    for &target in caps {
        cell.capabilities
            .grant(target, AuthRequired::None)
            .expect("granting a genesis cap to a seat cell");
    }
    world.genesis_install(cell)
}

/// Decode a canonical big-endian [`field_from_u64`] slot back to a `u64` (the trailing 8
/// bytes are the value; matches the kernel's integer-constraint comparison).
fn field_to_u64(f: &FieldElement) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&f[24..32]);
    u64::from_be_bytes(b)
}

/// Fold a real [`CommitOutcome`] into the legible [`ActOutcome`].
fn commit_to_outcome(outcome: CommitOutcome) -> ActOutcome {
    match outcome {
        CommitOutcome::Committed { receipt, .. } => ActOutcome::Committed {
            receipt: receipt.turn_hash,
        },
        CommitOutcome::Rejected { reason, .. } => ActOutcome::Refused { reason },
        CommitOutcome::Queued { .. } => ActOutcome::Refused {
            reason: "the world is suspended — the move was staged, not committed".into(),
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use collective_choice::VoteError;
    use dregg_types::Signature;

    /// Seat indices in the mustered roster (Tank, Scout, Mage, Healer).
    const TANK: usize = 0;
    const SCOUT: usize = 1;
    const MAGE: usize = 2;
    const HEALER: usize = 3;

    /// THE ROSTER — a party of four DISTINCT-role seated identities forms in ONE shared
    /// ledger, each a real player-cell whose caps ARE its role.
    #[test]
    fn a_party_of_four_forms_a_roster_of_distinct_seated_identities() {
        let party = Party::muster();
        assert_eq!(party.seat_count(), 4, "a four-seat party");

        // Distinct roles, distinct identities.
        let roles: Vec<Role> = party.seats().iter().map(|s| s.role()).collect();
        assert_eq!(
            roles,
            vec![Role::Tank, Role::Scout, Role::Mage, Role::Healer]
        );
        for i in 0..4 {
            for j in (i + 1)..4 {
                assert_ne!(
                    party.seat(i).cell(),
                    party.seat(j).cell(),
                    "each seat is its own cell/identity"
                );
            }
        }

        // Every seat + shared cell is a real cell in the ONE shared ledger.
        let l = party.layout();
        for id in [
            l.party, l.front, l.lock, l.ward, l.rally, l.focus, l.gate, l.loot,
        ] {
            assert!(
                party.world().ledger().get(&id).is_some(),
                "the shared cell is a real cell in the one ledger"
            );
        }
        for s in party.seats() {
            assert!(party.world().ledger().get(&s.cell()).is_some());
        }

        // The shared focus pool is seeded with the party budget (the FieldLteField ceiling).
        assert_eq!(
            party.read_field(l.focus, FOCUS_BUDGET_SLOT),
            FOCUS_BUDGET,
            "the shared pool carries the party budget"
        );
        assert_eq!(party.focus_spent(), 0, "nothing spent yet");
    }

    /// SEATED CO-OP — each seat acts on its OWN role's cell (a real committed turn), and the
    /// ONE shared world reflects every seat's move at once.
    #[test]
    fn each_seat_acts_on_its_own_role_cell_in_one_world() {
        let mut party = Party::muster();
        let l = party.layout();

        let t = party.act_in_role(TANK);
        assert!(t.committed(), "the tank guards the front rank: {t:?}");
        assert_ne!(t.receipt().unwrap(), [0u8; 32], "a genuine receipted turn");

        let s = party.act_in_role(SCOUT);
        assert!(s.committed(), "the scout disarms the lock: {s:?}");

        // Distinct receipts prove two independent seats' turns landed.
        assert_ne!(t.receipt().unwrap(), s.receipt().unwrap());

        // The ONE shared world reflects BOTH seats' committed moves at once.
        assert_eq!(
            party.read_field(l.front, ROLE_SLOT),
            ROLE_MARK,
            "front held"
        );
        assert_eq!(
            party.read_field(l.lock, ROLE_SLOT),
            ROLE_MARK,
            "lock disarmed"
        );
    }

    /// NOBODY PLAYS YOUR SEAT — a seat firing a move OUTSIDE its role writes a cell it holds
    /// no cap to: a real `CapabilityNotHeld` refusal (non-vacuous — the same move by the
    /// RIGHT seat commits), and the cell is untouched (anti-ghost).
    #[test]
    fn a_move_outside_your_seat_is_refused_and_forging_a_teammates_move_is_refused() {
        let mut party = Party::muster();
        let l = party.layout();

        // The scout tries to fire the TANK's move (guard the front rank) — no cap to `front`.
        let forge = party.act(SCOUT, PartyMove::GuardFront);
        assert!(
            forge.refused(),
            "the scout cannot play the tank's seat: {forge:?}"
        );
        assert!(
            forge.reason().unwrap().to_lowercase().contains("cap"),
            "the refusal is a capability refusal, got: {}",
            forge.reason().unwrap()
        );
        assert_eq!(
            party.read_field(l.front, ROLE_SLOT),
            0,
            "anti-ghost: the forged move touched the front rank not at all"
        );

        // The tank tries to CAST (the mage's move) — no cap to `ward`/`focus` → refused.
        let miscast = party.act(TANK, PartyMove::CastWard);
        assert!(miscast.refused(), "the tank cannot cast: {miscast:?}");
        assert_eq!(
            party.focus_spent(),
            0,
            "anti-ghost: no focus spent by the forge"
        );

        // Non-vacuous: the SAME guard-front move by the TANK (its own seat) commits.
        assert!(
            party.act(TANK, PartyMove::GuardFront).committed(),
            "the tank's own move commits — the refusal above was real, not a broken move"
        );
        assert_eq!(party.read_field(l.front, ROLE_SLOT), ROLE_MARK);
    }

    /// THE SHARED FOCUS POOL caps the PARTY (not one seat). The mage AND the healer draw on
    /// the SAME budget: two casts fit (2 x 15 <= 40), a THIRD — from EITHER caster —
    /// overspends (45 > 40) and is a real `FieldLteField` refusal that spends nothing.
    #[test]
    fn the_shared_focus_pool_caps_the_party_across_seats() {
        let mut party = Party::muster();

        // Mage casts (spends 15) — within budget, commits.
        let c1 = party.act_in_role(MAGE);
        assert!(c1.committed(), "the mage's cast is within budget: {c1:?}");
        assert_eq!(party.focus_spent(), FOCUS_COST, "15 spent");

        // Healer rallies (spends another 15 from the SAME pool) — total 30 <= 40, commits.
        let c2 = party.act_in_role(HEALER);
        assert!(c2.committed(), "the healer draws the shared pool: {c2:?}");
        assert_eq!(
            party.focus_spent(),
            2 * FOCUS_COST,
            "30 spent across two seats"
        );

        // A THIRD cast (mage again) would push 30 -> 45 > 40: the pool refuses it.
        let over = party.act_in_role(MAGE);
        assert!(
            over.refused(),
            "an overspend of the shared pool is refused (FieldLteField): {over:?}"
        );
        assert_eq!(
            party.focus_spent(),
            2 * FOCUS_COST,
            "anti-ghost: the refused cast spent nothing"
        );

        // Non-vacuous: a cheaper (in-role, no-focus) move still commits after the overspend.
        assert!(
            party.act_in_role(TANK).committed(),
            "the tank (no focus) still acts — only the pool overspend was refused"
        );
    }

    /// THE FORK BALLOT — a quorum-certified party vote fires the shared move into the real
    /// world. Three of four seats reach quorum for the left stair; the certified winner
    /// writes the chosen path into the fork gate as a real committed turn.
    #[test]
    fn a_quorum_certified_fork_resolves_the_shared_move_into_the_world() {
        let mut party = Party::muster();
        let l = party.layout();
        let mut fork = party
            .open_fork(
                "The passage forks — which way does the party go?",
                vec![
                    ("Left, the sunken stair".into(), 1),
                    ("Right, the warded arch".into(), 2),
                ],
            )
            .expect("the fork opens");

        // Three seats vote LEFT (option 0), one votes RIGHT (option 1): quorum (M=3) is met.
        for seat in [TANK, SCOUT, MAGE] {
            let ballot = party.sign_ballot(&fork, seat, 0);
            fork.cast(&ballot)
                .expect("a seated signed ballot is admitted");
        }
        let ballot = party.sign_ballot(&fork, HEALER, 1);
        fork.cast(&ballot)
            .expect("the healer's signed ballot is admitted");

        assert_eq!(
            fork.tally().expect("tally").per_option,
            vec![3, 1],
            "3 left, 1 right"
        );

        // THE SEAM: the quorum-certified winner resolves into the party world.
        let res = fork
            .resolve_into(&mut party)
            .expect("the quorum-certified move fires");
        assert_eq!(res.winner, 0, "left won");
        assert_eq!(res.winner_tally, 3);
        assert_eq!(res.total, 4);
        assert_ne!(
            res.receipt, [0u8; 32],
            "a genuine committed shared-move turn"
        );

        // The world resolved the decided move: the gate holds the LEFT path (1).
        assert_eq!(
            party.read_field(l.gate, GATE_SLOT),
            1,
            "the shared world reflects the quorum-certified path"
        );
    }

    /// A SUB-QUORUM fork moves NOTHING (anti-ghost). Only two of four seats vote (below
    /// M=3): the quorum gate refuses the decision-turn and no shared move fires — the gate
    /// is untouched.
    #[test]
    fn a_sub_quorum_fork_does_not_move_the_world() {
        let mut party = Party::muster();
        let l = party.layout();
        let mut fork = party
            .open_fork("Fork?", vec![("Left".into(), 1), ("Right".into(), 2)])
            .expect("open");

        for seat in [TANK, SCOUT] {
            let b = party.sign_ballot(&fork, seat, 0);
            fork.cast(&b).expect("vote");
        }

        match fork.resolve_into(&mut party) {
            Err(ForkError::BelowQuorum) => {}
            other => panic!("a sub-quorum fork must not move the world, got {other:?}"),
        }
        assert_eq!(
            party.read_field(l.gate, GATE_SLOT),
            0,
            "anti-ghost: the gate did not move below quorum"
        );
    }

    /// NOBODY FORGES YOUR VOTE — a valid signature by a NON-MEMBER is Ineligible, and a
    /// FORGED signature (a seated seat's key, a garbage signature) is BadSignature. Neither
    /// moves the board.
    #[test]
    fn a_non_member_vote_is_ineligible_and_a_forged_vote_is_bad_signature() {
        let party = Party::muster();
        let mut fork = party
            .open_fork("Fork?", vec![("Left".into(), 1), ("Right".into(), 2)])
            .expect("open");
        let poll = fork.poll();

        // A NON-MEMBER (never enrolled in the party electorate) signs a perfectly valid
        // ballot for her OWN key — the signature verifies, but she holds no ballot cap.
        let outsider = Custodian::generate("Mallory");
        let outsider_ballot = outsider.sign_ballot(poll, 0);
        match fork.cast(&outsider_ballot) {
            Err(CollectiveError::Vote(VoteError::Ineligible)) => {}
            other => panic!("a non-member vote must be Ineligible, got {other:?}"),
        }

        // A FORGED ballot: claims a seated seat's public key, but carries a signature
        // nobody produced → BadSignature (verified BEFORE any turn; the board stays empty).
        let tank_pk = party.seat(TANK).electorate_seat().pk;
        let forged = SignedBallot {
            voter_pk: tank_pk,
            option: 0,
            signature: Signature([0x7u8; 64]),
        };
        match fork.cast(&forged) {
            Err(CollectiveError::BadSignature) => {}
            other => panic!("a forged vote must be BadSignature, got {other:?}"),
        }

        assert_eq!(
            fork.tally().expect("tally").total,
            0,
            "anti-ghost: neither the non-member nor the forge moved the board"
        );
    }

    /// THE ON-LEDGER LOOT SPLIT — each seat's share is a committed cell fact, and a
    /// re-split (an attempt to alter it) is refused by the WriteOnce tooth. Not a leader's
    /// promise: a receipt nobody can fake or rewrite.
    #[test]
    fn the_loot_split_is_a_committed_writeonce_ledger_fact() {
        let mut party = Party::muster();

        // The party agrees a split and COMMITS it as one real turn.
        let shares = [40u64, 30, 20, 10];
        let out = party.split_loot(&shares);
        assert!(out.committed(), "the loot split commits: {out:?}");
        assert_ne!(out.receipt().unwrap(), [0u8; 32]);

        // It is now a LEDGER FACT — each seat's share readable off the shared ledger.
        for (i, &s) in shares.iter().enumerate() {
            assert_eq!(
                party.loot_share(i),
                s,
                "seat {i}'s share is a committed ledger fact"
            );
        }

        // NOBODY FAKES THE SPLIT: a re-split (rewriting a share to a different value) is a
        // real WriteOnce refusal — the split cannot be altered after the fact.
        let re = party.split_loot(&[10u64, 10, 10, 10]);
        assert!(
            re.refused(),
            "a re-split of the frozen loot is refused (WriteOnce): {re:?}"
        );
        // Anti-ghost: the committed split is unchanged.
        assert_eq!(party.loot_share(0), 40, "the original split stands");
        assert_eq!(party.loot_share(3), 10);
    }

    /// A DUPLICATE ballot by the same seat is refused by the real vote engine (WriteOnce
    /// ballot + nullifier) — one seat, one vote.
    #[test]
    fn a_seat_cannot_vote_twice() {
        let party = Party::muster();
        let mut fork = party
            .open_fork("Fork?", vec![("Left".into(), 1), ("Right".into(), 2)])
            .expect("open");

        let first = party.sign_ballot(&fork, MAGE, 0);
        fork.cast(&first).expect("the mage's first vote commits");
        let second = party.sign_ballot(&fork, MAGE, 1);
        match fork.cast(&second) {
            Err(CollectiveError::Vote(VoteError::DoubleVote)) => {}
            other => panic!("a second ballot by the same seat must be refused, got {other:?}"),
        }
        assert_eq!(
            fork.tally().expect("tally").per_option,
            vec![1, 0],
            "the board did not move on the refused double vote"
        );
    }
}
