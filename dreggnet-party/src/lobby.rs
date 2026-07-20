//! Live formation for a real [`crate::Party`].
//!
//! The party substrate already enforces roles with capabilities, signed fork
//! ballots, a shared focus budget, and an immutable loot split. Its missing
//! player-facing joint was formation: deciding which authenticated identity
//! occupies which role and refusing gameplay until the whole roster is ready.
//! This module closes that joint as a small deterministic state machine.
//!
//! Successful commands append to a bounded, domain-separated hash chain.
//! Refusals are anti-ghost: they change neither roster, revision, nor root. A
//! launch is leader-authorized, requires all four distinct roles to be ready,
//! locks the lobby, and returns the actual cap-seated [`crate::Party`]. The
//! exported journal is replay-verified rather than trusted as a state blob.

use crate::{Party, PartyFormationError, Role};

/// A lobby cannot churn forever and pin an unbounded journal in a live host.
pub const MAX_LOBBY_EVENTS: usize = 256;
/// Maximum byte length of an opaque authenticated player identity.
pub const MAX_LOBBY_IDENTITY_BYTES: usize = 256;
/// Maximum byte length of a frontend session/table id.
pub const MAX_LOBBY_SESSION_BYTES: usize = 128;

const GENESIS_DOMAIN: &[u8] = b"dregg.party-lobby.genesis.v1";
const EVENT_DOMAIN: &[u8] = b"dregg.party-lobby.event.v1";

/// One occupied role in the lobby.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LobbySeat {
    identity: String,
    ready: bool,
}

impl LobbySeat {
    /// The frontend-authenticated identity holding this role.
    pub fn identity(&self) -> &str {
        &self.identity
    }

    /// Whether this player has explicitly readied.
    pub fn ready(&self) -> bool {
        self.ready
    }
}

/// One semantic lobby command. These are the only mutations covered by the
/// journal and are intentionally small enough for every frontend transport.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LobbyCommand {
    /// Claim one currently-open role.
    Claim(Role),
    /// Set this player's readiness flag.
    SetReady(bool),
    /// Vacate this player's role before launch.
    Leave,
    /// Lock the complete ready roster and launch the game (leader only).
    Launch,
}

/// One admitted journal event. The fields are public because a restored record
/// is untrusted input; [`PartyLobby::verify_record`] replays and checks all of them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LobbyEvent {
    /// Monotone one-based event number.
    pub revision: u64,
    /// Authenticated actor attributed by the hosting surface.
    pub actor: String,
    /// The semantic command that landed.
    pub command: LobbyCommand,
    /// Hash-chain root after this event.
    pub root: [u8; 32],
}

/// Replayable public record of a party lobby. It contains identities, role
/// claims, and readiness only—no custody secret, private game state, or move.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LobbyRecord {
    /// Stable frontend session/table id.
    pub session_id: String,
    /// Identity authorized to launch the ready roster.
    pub leader: String,
    /// Ordered admitted events.
    pub events: Vec<LobbyEvent>,
}

/// Public receipt of one successfully admitted lobby mutation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LobbyReceipt {
    /// Monotone revision after the mutation.
    pub revision: u64,
    /// Hash-chain root after the mutation.
    pub root: [u8; 32],
    /// Number of occupied roles.
    pub occupied: usize,
    /// Number of occupied roles explicitly ready.
    pub ready: usize,
    /// Whether the roster is now locked and launched.
    pub launched: bool,
}

/// A completed launch: the lobby receipt binds the roster that produced the
/// actual executor-backed party returned beside it.
pub struct PartyLaunch {
    /// The real cap-seated shared world, ready for role moves and ballots.
    pub party: Party,
    /// Receipt for the roster-lock event.
    pub receipt: LobbyReceipt,
}

/// Why a lobby command was refused. Every refusal is anti-ghost.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LobbyRefusal {
    /// Session ids must be non-empty and bounded.
    InvalidSessionId,
    /// Player identities must be non-empty and bounded.
    InvalidIdentity,
    /// The bounded journal is full.
    EventLimit,
    /// The roster has already launched and is immutable.
    AlreadyLaunched,
    /// This role is held by another identity.
    RoleTaken(Role),
    /// This identity already occupies a role.
    AlreadySeated(Role),
    /// This identity does not occupy any role.
    NotSeated,
    /// A repeated readiness write would not change state.
    ReadinessUnchanged(bool),
    /// Only the lobby leader can launch.
    LeaderOnly,
    /// Launch requires all four roles to be occupied.
    IncompleteRoster { occupied: usize },
    /// Launch requires every occupied player to be explicitly ready.
    PlayersNotReady { ready: usize },
    /// The roster could not be lowered into a party (fail closed).
    Formation(PartyFormationError),
}

impl std::fmt::Display for LobbyRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidSessionId => write!(f, "session id is empty or exceeds 128 bytes"),
            Self::InvalidIdentity => write!(f, "identity is empty or exceeds 256 bytes"),
            Self::EventLimit => write!(f, "party lobby journal reached its 256-event limit"),
            Self::AlreadyLaunched => write!(f, "party already launched; its roster is locked"),
            Self::RoleTaken(role) => write!(f, "the {} role is already occupied", role.name()),
            Self::AlreadySeated(role) => {
                write!(f, "identity already occupies the {} role", role.name())
            }
            Self::NotSeated => write!(f, "identity does not occupy a role"),
            Self::ReadinessUnchanged(ready) => {
                write!(f, "readiness is already {ready}")
            }
            Self::LeaderOnly => write!(f, "only the party leader can launch"),
            Self::IncompleteRoster { occupied } => {
                write!(f, "all four roles are required; {occupied} are occupied")
            }
            Self::PlayersNotReady { ready } => {
                write!(f, "all four players must ready; {ready} are ready")
            }
            Self::Formation(e) => write!(f, "roster formation refused: {e}"),
        }
    }
}

impl std::error::Error for LobbyRefusal {}

/// Result of replay-checking an untrusted lobby record.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LobbyVerifyReport {
    /// Whether every event replayed with its exact revision and root.
    pub verified: bool,
    /// Number of events checked before success or first break.
    pub events: usize,
    /// Human-readable verification account.
    pub detail: String,
}

impl LobbyVerifyReport {
    fn ok(events: usize) -> Self {
        Self {
            verified: true,
            events,
            detail: "party lobby re-verified by semantic replay".to_string(),
        }
    }

    fn broken(events: usize, detail: impl Into<String>) -> Self {
        Self {
            verified: false,
            events,
            detail: detail.into(),
        }
    }
}

/// A live four-role party lobby.
#[derive(Clone)]
pub struct PartyLobby {
    session_id: String,
    leader: String,
    seats: [Option<LobbySeat>; 4],
    events: Vec<LobbyEvent>,
    root: [u8; 32],
    launched: bool,
}

impl PartyLobby {
    /// Open a fresh lobby. The leader is launch authority, but need not occupy a
    /// role (a tournament organizer may launch a roster they do not play in).
    pub fn new(
        session_id: impl Into<String>,
        leader: impl Into<String>,
    ) -> Result<Self, LobbyRefusal> {
        let session_id = session_id.into();
        let leader = leader.into();
        if !valid_bounded(&session_id, MAX_LOBBY_SESSION_BYTES) {
            return Err(LobbyRefusal::InvalidSessionId);
        }
        if !valid_identity(&leader) {
            return Err(LobbyRefusal::InvalidIdentity);
        }
        let root = genesis_root(&session_id, &leader);
        Ok(Self {
            session_id,
            leader,
            seats: std::array::from_fn(|_| None),
            events: Vec::new(),
            root,
            launched: false,
        })
    }

    /// Stable lobby id.
    pub fn session_id(&self) -> &str {
        &self.session_id
    }

    /// Launch-authorized identity.
    pub fn leader(&self) -> &str {
        &self.leader
    }

    /// Current role occupant, if any.
    pub fn seat(&self, role: Role) -> Option<&LobbySeat> {
        self.seats[role.index()].as_ref()
    }

    /// Number of occupied roles.
    pub fn occupied_count(&self) -> usize {
        self.seats.iter().flatten().count()
    }

    /// Number of explicitly ready players.
    pub fn ready_count(&self) -> usize {
        self.seats
            .iter()
            .flatten()
            .filter(|seat| seat.ready)
            .count()
    }

    /// Whether all four roles are occupied and ready.
    pub fn ready_to_launch(&self) -> bool {
        !self.launched && self.occupied_count() == 4 && self.ready_count() == 4
    }

    /// Whether the roster has been locked by a successful launch.
    pub fn launched(&self) -> bool {
        self.launched
    }

    /// Current journal revision.
    pub fn revision(&self) -> u64 {
        self.events.len() as u64
    }

    /// Current domain-separated journal root.
    pub fn root(&self) -> [u8; 32] {
        self.root
    }

    /// Claim an unoccupied role as `actor`.
    pub fn claim(
        &mut self,
        actor: impl Into<String>,
        role: Role,
    ) -> Result<LobbyReceipt, LobbyRefusal> {
        self.commit(actor.into(), LobbyCommand::Claim(role))
    }

    /// Explicitly ready or unready this actor's occupied role.
    pub fn set_ready(
        &mut self,
        actor: impl Into<String>,
        ready: bool,
    ) -> Result<LobbyReceipt, LobbyRefusal> {
        self.commit(actor.into(), LobbyCommand::SetReady(ready))
    }

    /// Vacate this actor's role before launch.
    pub fn leave(&mut self, actor: impl Into<String>) -> Result<LobbyReceipt, LobbyRefusal> {
        self.commit(actor.into(), LobbyCommand::Leave)
    }

    /// Leader-authorized launch into the actual executor-backed party.
    pub fn launch(&mut self, actor: impl Into<String>) -> Result<PartyLaunch, LobbyRefusal> {
        let actor = actor.into();
        self.validate(&actor, &LobbyCommand::Launch)?;

        // Build before committing the lock. A formation error therefore leaves
        // revision/root/roster untouched (the same anti-ghost law as any refusal).
        let mut roster = Vec::with_capacity(4);
        for role in Role::ALL {
            let Some(seat) = self.seat(role) else {
                return Err(LobbyRefusal::IncompleteRoster {
                    occupied: self.occupied_count(),
                });
            };
            roster.push((role, seat.identity.clone()));
        }
        let roster: [(Role, String); 4] =
            roster
                .try_into()
                .map_err(|_| LobbyRefusal::IncompleteRoster {
                    occupied: self.occupied_count(),
                })?;
        let party = Party::muster_with_roster(roster).map_err(LobbyRefusal::Formation)?;
        let receipt = self.commit(actor, LobbyCommand::Launch)?;
        Ok(PartyLaunch { party, receipt })
    }

    /// Export the semantic event log; restored state must be replayed from it.
    pub fn export_record(&self) -> LobbyRecord {
        LobbyRecord {
            session_id: self.session_id.clone(),
            leader: self.leader.clone(),
            events: self.events.clone(),
        }
    }

    /// Verify an untrusted record by replaying every semantic transition and
    /// requiring its claimed revision/root to match. No state blob is trusted.
    ///
    /// This establishes that the record is a valid history (including a valid
    /// prefix). A durable deployment that has an independently anchored latest
    /// root should use [`Self::verify_record_at`] to also refuse truncation.
    pub fn verify_record(record: &LobbyRecord) -> LobbyVerifyReport {
        let mut replay = match Self::new(record.session_id.clone(), record.leader.clone()) {
            Ok(replay) => replay,
            Err(e) => return LobbyVerifyReport::broken(0, format!("invalid genesis: {e}")),
        };
        if record.events.len() > MAX_LOBBY_EVENTS {
            return LobbyVerifyReport::broken(
                0,
                format!(
                    "journal has {} events; maximum is {MAX_LOBBY_EVENTS}",
                    record.events.len()
                ),
            );
        }
        for (idx, event) in record.events.iter().enumerate() {
            let receipt = match replay.commit(event.actor.clone(), event.command.clone()) {
                Ok(receipt) => receipt,
                Err(e) => {
                    return LobbyVerifyReport::broken(
                        idx,
                        format!("event {} refused on replay: {e}", idx + 1),
                    );
                }
            };
            if event.revision != receipt.revision || event.root != receipt.root {
                return LobbyVerifyReport::broken(
                    idx + 1,
                    format!("event {} revision/root mismatch", idx + 1),
                );
            }
        }
        LobbyVerifyReport::ok(record.events.len())
    }

    /// Replay-verify a record against an independently anchored latest
    /// `(revision, root)`. This is the rollback-resistant durable-store check: a
    /// valid but truncated prefix is refused even though its own events replay.
    pub fn verify_record_at(
        record: &LobbyRecord,
        expected_revision: u64,
        expected_root: [u8; 32],
    ) -> LobbyVerifyReport {
        let report = Self::verify_record(record);
        if !report.verified {
            return report;
        }
        let revision = record.events.len() as u64;
        let root = record
            .events
            .last()
            .map(|event| event.root)
            .unwrap_or_else(|| genesis_root(&record.session_id, &record.leader));
        if revision != expected_revision || root != expected_root {
            return LobbyVerifyReport::broken(
                record.events.len(),
                "record is a valid prefix but does not match the anchored latest revision/root",
            );
        }
        report
    }

    /// Re-verify this live lobby's own record.
    pub fn verify(&self) -> LobbyVerifyReport {
        Self::verify_record_at(&self.export_record(), self.revision(), self.root())
    }

    fn commit(
        &mut self,
        actor: String,
        command: LobbyCommand,
    ) -> Result<LobbyReceipt, LobbyRefusal> {
        if self.events.len() >= MAX_LOBBY_EVENTS {
            return Err(LobbyRefusal::EventLimit);
        }
        self.validate(&actor, &command)?;
        self.apply(&actor, &command);
        let revision = self.revision() + 1;
        self.root = next_root(self.root, revision, &actor, &command);
        self.events.push(LobbyEvent {
            revision,
            actor,
            command,
            root: self.root,
        });
        Ok(self.receipt())
    }

    fn validate(&self, actor: &str, command: &LobbyCommand) -> Result<(), LobbyRefusal> {
        if !valid_identity(actor) {
            return Err(LobbyRefusal::InvalidIdentity);
        }
        if self.launched {
            return Err(LobbyRefusal::AlreadyLaunched);
        }
        let actor_role = Role::ALL
            .into_iter()
            .find(|role| self.seat(*role).is_some_and(|seat| seat.identity == actor));
        match command {
            LobbyCommand::Claim(role) => {
                if let Some(role) = actor_role {
                    return Err(LobbyRefusal::AlreadySeated(role));
                }
                if self.seat(*role).is_some() {
                    return Err(LobbyRefusal::RoleTaken(*role));
                }
            }
            LobbyCommand::SetReady(ready) => {
                let role = actor_role.ok_or(LobbyRefusal::NotSeated)?;
                if self.seat(role).is_some_and(|seat| seat.ready == *ready) {
                    return Err(LobbyRefusal::ReadinessUnchanged(*ready));
                }
            }
            LobbyCommand::Leave => {
                actor_role.ok_or(LobbyRefusal::NotSeated)?;
            }
            LobbyCommand::Launch => {
                if actor != self.leader {
                    return Err(LobbyRefusal::LeaderOnly);
                }
                let occupied = self.occupied_count();
                if occupied != 4 {
                    return Err(LobbyRefusal::IncompleteRoster { occupied });
                }
                let ready = self.ready_count();
                if ready != 4 {
                    return Err(LobbyRefusal::PlayersNotReady { ready });
                }
            }
        }
        Ok(())
    }

    fn apply(&mut self, actor: &str, command: &LobbyCommand) {
        match command {
            LobbyCommand::Claim(role) => {
                self.seats[role.index()] = Some(LobbySeat {
                    identity: actor.to_string(),
                    ready: false,
                });
            }
            LobbyCommand::SetReady(ready) => {
                let seat = self
                    .seats
                    .iter_mut()
                    .flatten()
                    .find(|seat| seat.identity == actor)
                    .expect("validation established an occupied role");
                seat.ready = *ready;
            }
            LobbyCommand::Leave => {
                let idx = self
                    .seats
                    .iter()
                    .position(|seat| seat.as_ref().is_some_and(|seat| seat.identity == actor))
                    .expect("validation established an occupied role");
                self.seats[idx] = None;
            }
            LobbyCommand::Launch => self.launched = true,
        }
    }

    fn receipt(&self) -> LobbyReceipt {
        LobbyReceipt {
            revision: self.revision(),
            root: self.root,
            occupied: self.occupied_count(),
            ready: self.ready_count(),
            launched: self.launched,
        }
    }
}

fn valid_bounded(value: &str, max: usize) -> bool {
    !value.is_empty() && value.len() <= max
}

fn valid_identity(identity: &str) -> bool {
    valid_bounded(identity, MAX_LOBBY_IDENTITY_BYTES)
}

fn genesis_root(session_id: &str, leader: &str) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(GENESIS_DOMAIN);
    hash_string(&mut h, session_id);
    hash_string(&mut h, leader);
    *h.finalize().as_bytes()
}

fn next_root(previous: [u8; 32], revision: u64, actor: &str, command: &LobbyCommand) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(EVENT_DOMAIN);
    h.update(&previous);
    h.update(&revision.to_le_bytes());
    hash_string(&mut h, actor);
    match command {
        LobbyCommand::Claim(role) => {
            h.update(&[0, role.index() as u8]);
        }
        LobbyCommand::SetReady(ready) => {
            h.update(&[1, u8::from(*ready)]);
        }
        LobbyCommand::Leave => {
            h.update(&[2]);
        }
        LobbyCommand::Launch => {
            h.update(&[3]);
        }
    }
    *h.finalize().as_bytes()
}

fn hash_string(h: &mut blake3::Hasher, value: &str) {
    h.update(&(value.len() as u64).to_le_bytes());
    h.update(value.as_bytes());
}
