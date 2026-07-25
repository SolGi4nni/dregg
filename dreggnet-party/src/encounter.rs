//! A live party enters the tactical Arena.
//!
//! This is the first mechanical bridge between the multi-actor party and
//! [`dungeon_on_dregg::combat::Arena`]. The party first custody-signs a quorum
//! fork selecting the enemy to concentrate on. Each later player contribution
//! must then pass two independent real executors:
//!
//! 1. the authenticated identity fires the requested role move in [`Party`], so
//!    the role's capability and shared-focus teeth authorize it; and
//! 2. the corresponding tactic advances the real Arena cell (guard, strike,
//!    heavy strike, or rally/guard).
//!
//! An [`EncounterEvent`] retains the exact custody-signed ballot and every
//! complete turn receipt, then folds them, the exact post-states, and the
//! previous event root into one domain-separated encounter root.
//! [`PartyArenaEncounter::resume`] rebuilds both worlds and the vote engine from
//! semantic commands, refusing a forged receipt, actor, target, state, or root.
//!
//! ## Atomic publication boundary
//!
//! Party and Arena still use two independently-owned embedded executors, so this
//! module does not pretend their receipts are one kernel forest receipt. Instead a
//! contribution is executed against an isolated encounter rebuilt from the last
//! admitted record. Only after BOTH real executor turns land, the complete event
//! is hash-chained, and an optional commit hook accepts it is that candidate image
//! swapped into the live encounter. A party-only prefix is therefore never visible
//! through the authoritative [`PartyArenaEncounter`]. A crash merely loses the
//! detached candidate and leaves the last admitted record authoritative.
//!
//! [`PreparedContribution`] adds a bounded checksummed intent anchored to the exact
//! pre-revision/root. It can be persisted before execution and recovered
//! idempotently: an exact base completes the contribution; a record already
//! carrying that command verifies as committed; a stale or conflicting record is
//! refused. This is a crash-safe application transaction over two local engines,
//! not a distributed atomic hyperedge across independently publishing federations.

use std::collections::BTreeMap;
use std::fs::{File, OpenOptions};
use std::io::{Read, Write};
use std::path::{Path, PathBuf};

use collective_choice::PollId;
use dregg_app_framework::TurnReceipt;
use dungeon_on_dregg::collective::SignedBallot;
use dungeon_on_dregg::combat::{
    ATTACK_DIE, Arena, CLERIC, FINISH_THRESHOLD, HEAVY_DIE, HOUND, Outcome as ArenaOutcome, RANGER,
    WARDEN, is_hero,
};

use crate::{
    ActOutcome, FOCUS_BUDGET_SLOT, FOCUS_SPENT_SLOT, ForkError, GATE_SLOT, Party, PartyFork,
    ROLE_SLOT, Role,
};

/// The parameter relation that makes a Scout basic attack unable to cross the Arena HP
/// floor, and therefore makes a Scout `UnsafeStrike` preflight arm unnecessary.
///
/// `contribute` routes a Scout to `finish` when `hp <= FINISH_THRESHOLD` and to `attack`
/// (a `d ATTACK_DIE`, damage `<= ATTACK_DIE`) otherwise. The attack branch is therefore
/// only reachable with `hp > FINISH_THRESHOLD`, and it can floor the target only if
/// `hp <= ATTACK_DIE`. While `FINISH_THRESHOLD >= ATTACK_DIE` that window is empty.
///
/// This is a COMPILE-TIME check on purpose. The runtime guard that used to stand here was
/// `hp > FINISH_THRESHOLD && hp <= ATTACK_DIE` with both constants equal to `8` — an
/// unsatisfiable condition, i.e. a guard that could never refuse anything. Separating the
/// two constants reds this assertion at build time and sends the reader to
/// `preflight_player`, where the arm must be restored.
const SCOUT_ATTACK_CANNOT_FLOOR: () = assert!(
    FINISH_THRESHOLD >= ATTACK_DIE,
    "FINISH_THRESHOLD < ATTACK_DIE: a Scout basic attack can now floor the target, so \
     preflight_player needs its Scout UnsafeStrike arm back (see the comment there)"
);
const _: () = SCOUT_ATTACK_CANNOT_FLOOR;

const GENESIS_DOMAIN: &[u8] = b"dregg.party-arena.genesis.v1";
const EVENT_DOMAIN: &[u8] = b"dregg.party-arena.event.v1";
const CONTRIBUTION_INTENT_DOMAIN: &str = "dregg.party-arena.contribution-intent.v1";
const PREPARED_MAGIC: &[u8; 8] = b"DPAINT01";
const PREPARED_VERSION: u8 = 1;
const PREPARED_CHECKSUM_DOMAIN: &str = "dregg.party-arena.prepared-wire.v1";
const JOURNAL_FILE: &str = "party-arena-contribution.bin";
const JOURNAL_TEMP: &str = "party-arena-contribution.tmp";
const JOURNAL_LOCK: &str = "party-arena-contribution.lock";
const MAX_ACTOR_BYTES: usize = 256;
pub const MAX_PREPARED_CONTRIBUTION_BYTES: usize =
    8 + 1 + 8 + 32 + 1 + 2 + MAX_ACTOR_BYTES + 32 + 32;

/// Bounded encounter history. A gate assault is deliberately finite: four
/// once-per-encounter role contributions plus votes, resolution, and enemy turns.
pub const MAX_ENCOUNTER_EVENTS: usize = 128;

/// One semantic command in the replayable encounter journal.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EncounterCommand {
    /// Cast the authenticated party seat's custody-signed target ballot.
    Vote { actor: String, option: usize },
    /// Leader-authorized quorum resolution into the party gate.
    Resolve { actor: String },
    /// Attempt `role`'s real capability move and, if it lands, its Arena tactic.
    Contribute { actor: String, role: Role },
    /// Advance the currently-active enemy under the deterministic encounter AI.
    AdvanceEnemy { actor: String },
}

/// One admitted event. Complete executor receipts are retained rather than
/// replacing a real turn with an application-level synthetic hash.
#[derive(Clone, Debug)]
pub struct EncounterEvent {
    /// Monotone one-based event number.
    pub revision: u64,
    /// Semantic command re-driven by restart/replay.
    pub command: EncounterCommand,
    /// Exact custody-signed ballot admitted by the vote engine.
    pub ballot: Option<SignedBallot>,
    /// Original poll id covered by the custody signature. The collective-choice
    /// operator is freshly generated on restart, so semantic replay uses a fresh
    /// poll while independently re-verifying this original evidence.
    pub ballot_poll: Option<PollId>,
    /// Receipt for a signed ballot turn on the collective-choice world.
    pub vote_receipt: Option<TurnReceipt>,
    /// Receipt for the party-world role or fork-resolution turn.
    pub party_receipt: Option<TurnReceipt>,
    /// Receipt for the mechanically corresponding tactical-Arena turn.
    pub arena_receipt: Option<TurnReceipt>,
    /// Quorum-selected enemy after this event, if resolved.
    pub target: Option<u8>,
    /// Arena active pointer after this event.
    pub arena_active: u8,
    /// Arena outcome after this event.
    pub arena_outcome: ArenaOutcome,
    /// Exact committed tactical state after this event.
    pub arena_state: Vec<u64>,
    /// Whole-image root of the party world after this event.
    pub party_root: [u8; 32],
    /// Stable semantic party state (gate; four role marks; focus pair; loot).
    /// Unlike `party_root`, this intentionally excludes process-local receipt ids
    /// and is compared across a fresh restart.
    pub party_state: Vec<u64>,
    /// Domain-separated hash-chain root binding this event.
    pub root: [u8; 32],
}

/// Restart input. Roster order is canonical `Tank, Scout, Mage, Healer`.
#[derive(Clone, Debug)]
pub struct EncounterRecord {
    /// Canonical role-aligned authenticated identities.
    pub roster: [String; 4],
    /// Identity authorized to resolve the fork and advance enemy turns.
    pub leader: String,
    /// Deterministic tactical Arena seed.
    pub arena_seed: u8,
    /// Ordered admitted events.
    pub events: Vec<EncounterEvent>,
}

/// A bounded, persistable compare-and-swap intent for one paired contribution.
///
/// The anchor prevents a command prepared at one encounter head from being
/// replayed onto another. `intent` binds every field and is independently
/// recomputed when decoding or committing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PreparedContribution {
    pub base_revision: u64,
    pub base_root: [u8; 32],
    pub actor: String,
    pub role: Role,
    pub intent: [u8; 32],
}

impl PreparedContribution {
    fn new(base_revision: u64, base_root: [u8; 32], actor: String, role: Role) -> Self {
        let intent = contribution_intent(base_revision, base_root, &actor, role);
        Self {
            base_revision,
            base_root,
            actor,
            role,
            intent,
        }
    }

    fn validate(&self) -> Result<(), EncounterError> {
        if self.actor.is_empty() || self.actor.len() > MAX_ACTOR_BYTES {
            return Err(EncounterError::MalformedPrepared(
                "actor is empty or exceeds 256 bytes".to_string(),
            ));
        }
        let expected =
            contribution_intent(self.base_revision, self.base_root, &self.actor, self.role);
        if self.intent != expected {
            return Err(EncounterError::MalformedPrepared(
                "intent digest does not bind the prepared fields".to_string(),
            ));
        }
        Ok(())
    }

    /// Canonical bounded wire image suitable for durable host storage.
    pub fn to_wire_bytes(&self) -> Result<Vec<u8>, EncounterError> {
        self.validate()?;
        let mut out = Vec::with_capacity(MAX_PREPARED_CONTRIBUTION_BYTES);
        out.extend_from_slice(PREPARED_MAGIC);
        out.push(PREPARED_VERSION);
        out.extend_from_slice(&self.base_revision.to_be_bytes());
        out.extend_from_slice(&self.base_root);
        out.push(role_tag(self.role));
        out.extend_from_slice(&(self.actor.len() as u16).to_be_bytes());
        out.extend_from_slice(self.actor.as_bytes());
        out.extend_from_slice(&self.intent);
        let checksum = blake3::derive_key(PREPARED_CHECKSUM_DOMAIN, &out);
        out.extend_from_slice(&checksum);
        debug_assert!(out.len() <= MAX_PREPARED_CONTRIBUTION_BYTES);
        Ok(out)
    }

    /// Decode and integrity-check the canonical prepared-intent wire image.
    pub fn from_wire_bytes(bytes: &[u8]) -> Result<Self, EncounterError> {
        const MIN: usize = 8 + 1 + 8 + 32 + 1 + 2 + 1 + 32 + 32;
        if bytes.len() < MIN || bytes.len() > MAX_PREPARED_CONTRIBUTION_BYTES {
            return Err(EncounterError::MalformedPrepared(
                "prepared wire length is outside its fixed bound".to_string(),
            ));
        }
        let (body, encoded_checksum) = bytes.split_at(bytes.len() - 32);
        if blake3::derive_key(PREPARED_CHECKSUM_DOMAIN, body).as_slice() != encoded_checksum {
            return Err(EncounterError::MalformedPrepared(
                "prepared wire checksum mismatch".to_string(),
            ));
        }
        let mut cursor = PreparedCursor::new(body);
        if cursor.take::<8>()? != *PREPARED_MAGIC || cursor.byte()? != PREPARED_VERSION {
            return Err(EncounterError::MalformedPrepared(
                "unsupported prepared wire format".to_string(),
            ));
        }
        let base_revision = u64::from_be_bytes(cursor.take()?);
        let base_root = cursor.take()?;
        let role = role_from_tag(cursor.byte()?)?;
        let actor_len = u16::from_be_bytes(cursor.take()?) as usize;
        if actor_len == 0 || actor_len > MAX_ACTOR_BYTES {
            return Err(EncounterError::MalformedPrepared(
                "prepared actor length is invalid".to_string(),
            ));
        }
        let actor = cursor.string(actor_len)?;
        let intent = cursor.take()?;
        if !cursor.finished() {
            return Err(EncounterError::MalformedPrepared(
                "prepared wire has trailing bytes".to_string(),
            ));
        }
        let prepared = Self {
            base_revision,
            base_root,
            actor,
            role,
            intent,
        };
        prepared.validate()?;
        Ok(prepared)
    }
}

/// Publication checkpoints for deterministic crash/failure injection.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ContributionCheckpoint {
    /// The role-capability turn landed in the detached party image.
    AfterParty,
    /// The tactical turn landed in the detached Arena image.
    AfterArena,
    /// Both receipts and the complete event exist, immediately before live swap.
    BeforePublish,
}

/// Optional durable-host/fault-injection hook. An error drops the detached image;
/// the live encounter is byte-for-byte at its prior semantic head.
pub trait ContributionCommitHook {
    fn checkpoint(&mut self, point: ContributionCheckpoint) -> Result<(), String>;
}

#[derive(Default)]
pub struct NoContributionCommitHook;

impl ContributionCommitHook for NoContributionCommitHook {
    fn checkpoint(&mut self, _point: ContributionCheckpoint) -> Result<(), String> {
        Ok(())
    }
}

/// What recovery learned about a durable prepared contribution.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ContributionRecovery {
    /// The record was at the exact prepared base; recovery executed and published it.
    Applied,
    /// The durable record already contained the exact prepared command.
    AlreadyCommitted,
}

/// Single-intent file journal for a durable encounter host.
///
/// Reservation is write+fsync+atomic-rename+directory-fsync under an advisory
/// lock. The host persists the resulting [`EncounterRecord`] before calling
/// [`Self::clear`]. A crash before that persistence replays from the old exact
/// anchor; a crash after it is classified as [`ContributionRecovery::AlreadyCommitted`].
#[derive(Clone, Debug)]
pub struct FileContributionJournal {
    root: PathBuf,
}

impl FileContributionJournal {
    pub fn open(root: impl AsRef<Path>) -> Result<Self, EncounterError> {
        std::fs::create_dir_all(root.as_ref())
            .map_err(|error| EncounterError::Journal(error.to_string()))?;
        let root = std::fs::canonicalize(root.as_ref())
            .map_err(|error| EncounterError::Journal(error.to_string()))?;
        File::open(&root)
            .and_then(|directory| directory.sync_all())
            .map_err(|error| EncounterError::Journal(error.to_string()))?;
        Ok(Self { root })
    }

    pub fn root(&self) -> &Path {
        &self.root
    }

    /// Reserve exactly one contribution intent. Repeating the same reservation
    /// is idempotent; a different outstanding intent is refused.
    pub fn reserve(&self, prepared: &PreparedContribution) -> Result<(), EncounterError> {
        let replacement = prepared.to_wire_bytes()?;
        self.with_lock(|journal| {
            if let Some(current) = journal.read_unlocked()? {
                if current == replacement {
                    return Ok(());
                }
                return Err(EncounterError::Journal(
                    "another contribution intent is already reserved".to_string(),
                ));
            }
            journal.write_unlocked(&replacement)
        })
    }

    pub fn load(&self) -> Result<Option<PreparedContribution>, EncounterError> {
        self.with_lock(|journal| {
            journal
                .read_unlocked()?
                .map(|wire| PreparedContribution::from_wire_bytes(&wire))
                .transpose()
        })
    }

    /// Clear only the exact intent the host has durably incorporated into its
    /// encounter record. A stale clearer cannot erase a newer reservation.
    pub fn clear(&self, expected: &PreparedContribution) -> Result<(), EncounterError> {
        let expected = expected.to_wire_bytes()?;
        self.with_lock(|journal| {
            let Some(current) = journal.read_unlocked()? else {
                return Ok(());
            };
            if current != expected {
                return Err(EncounterError::Journal(
                    "prepared journal changed before clear".to_string(),
                ));
            }
            std::fs::remove_file(journal.state_path())
                .map_err(|error| EncounterError::Journal(error.to_string()))?;
            File::open(&journal.root)
                .and_then(|directory| directory.sync_all())
                .map_err(|error| EncounterError::Journal(error.to_string()))
        })
    }

    fn state_path(&self) -> PathBuf {
        self.root.join(JOURNAL_FILE)
    }

    fn temp_path(&self) -> PathBuf {
        self.root.join(JOURNAL_TEMP)
    }

    fn lock_path(&self) -> PathBuf {
        self.root.join(JOURNAL_LOCK)
    }

    fn with_lock<T>(
        &self,
        operation: impl FnOnce(&Self) -> Result<T, EncounterError>,
    ) -> Result<T, EncounterError> {
        let lock = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .truncate(false)
            .open(self.lock_path())
            .map_err(|error| EncounterError::Journal(error.to_string()))?;
        lock.lock()
            .map_err(|error| EncounterError::Journal(error.to_string()))?;
        let result = operation(self);
        let unlock = lock
            .unlock()
            .map_err(|error| EncounterError::Journal(error.to_string()));
        match (result, unlock) {
            (Ok(value), Ok(())) => Ok(value),
            (Err(error), _) => Err(error),
            (Ok(_), Err(error)) => Err(error),
        }
    }

    fn read_unlocked(&self) -> Result<Option<Vec<u8>>, EncounterError> {
        let mut file = match File::open(self.state_path()) {
            Ok(file) => file,
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(None),
            Err(error) => return Err(EncounterError::Journal(error.to_string())),
        };
        let length = usize::try_from(
            file.metadata()
                .map_err(|error| EncounterError::Journal(error.to_string()))?
                .len(),
        )
        .map_err(|_| EncounterError::Journal("journal length exceeds usize".to_string()))?;
        if length == 0 || length > MAX_PREPARED_CONTRIBUTION_BYTES {
            return Err(EncounterError::Journal(
                "journal length is outside its fixed bound".to_string(),
            ));
        }
        let mut wire = Vec::with_capacity(length);
        Read::by_ref(&mut file)
            .take((MAX_PREPARED_CONTRIBUTION_BYTES + 1) as u64)
            .read_to_end(&mut wire)
            .map_err(|error| EncounterError::Journal(error.to_string()))?;
        if wire.len() != length {
            return Err(EncounterError::Journal(
                "journal changed while locked".to_string(),
            ));
        }
        Ok(Some(wire))
    }

    fn write_unlocked(&self, wire: &[u8]) -> Result<(), EncounterError> {
        let temp = self.temp_path();
        match std::fs::remove_file(&temp) {
            Ok(()) => {}
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
            Err(error) => return Err(EncounterError::Journal(error.to_string())),
        }
        let mut file = OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&temp)
            .map_err(|error| EncounterError::Journal(error.to_string()))?;
        file.write_all(wire)
            .and_then(|_| file.sync_all())
            .map_err(|error| EncounterError::Journal(error.to_string()))?;
        std::fs::rename(temp, self.state_path())
            .map_err(|error| EncounterError::Journal(error.to_string()))?;
        File::open(&self.root)
            .and_then(|directory| directory.sync_all())
            .map_err(|error| EncounterError::Journal(error.to_string()))
    }
}

/// Why an encounter command or replay was refused. Every ordinary command
/// refusal happens before an event is appended and leaves the encounter root
/// unchanged.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EncounterError {
    /// Leader is not one of the four role-seated identities.
    LeaderNotSeated,
    /// The bounded journal is full.
    EventLimit,
    /// Actor has no party seat.
    Unseated(String),
    /// Only the encounter leader may perform this command.
    LeaderOnly,
    /// Ballot option is outside the two-enemy target set.
    InvalidOption,
    /// This seat has already cast its target ballot.
    AlreadyVoted,
    /// The target fork has already resolved.
    ForkResolved,
    /// No quorum-selected target exists yet.
    TargetNotResolved,
    /// A player contribution was attempted during an enemy's active turn.
    EnemyIsActive(u8),
    /// Enemy advance was attempted during a hero's active turn.
    HeroIsActive(u8),
    /// The selected target has already been defeated.
    TargetDown(u8),
    /// A dice strike is conservatively refused before the paired party commit
    /// when it could hit the Arena's HP floor.
    UnsafeStrike { target: u8, hp: u64, die: u64 },
    /// The role capability/shared resource executor refused.
    PartyRefused(String),
    /// The custody-signed vote engine refused.
    VoteRefused(String),
    /// The quorum/fork world refused.
    ForkRefused(String),
    /// The tactical Arena executor refused.
    ArenaRefused(String),
    /// A detached candidate was deliberately interrupted at a commit checkpoint.
    CommitInterrupted {
        point: ContributionCheckpoint,
        reason: String,
    },
    /// The prepared compare-and-swap anchor no longer names this encounter head.
    StalePrepared,
    /// A prepared intent was malformed, corrupt, or non-canonical.
    MalformedPrepared(String),
    /// Durable journal I/O or compare-and-swap failed.
    Journal(String),
    /// A re-driven event differs from its recorded complete receipts or state.
    ReplayDiverged { event: usize, detail: String },
    /// Record genesis was malformed.
    InvalidRecord(String),
}

impl std::fmt::Display for EncounterError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::LeaderNotSeated => write!(f, "encounter leader does not hold a party seat"),
            Self::EventLimit => write!(f, "encounter journal reached its 128-event limit"),
            Self::Unseated(actor) => write!(f, "identity {actor:?} holds no party seat"),
            Self::LeaderOnly => write!(f, "only the encounter leader may do that"),
            Self::InvalidOption => write!(f, "the target ballot has only two options"),
            Self::AlreadyVoted => write!(f, "this party seat already voted"),
            Self::ForkResolved => write!(f, "the target fork already resolved"),
            Self::TargetNotResolved => write!(f, "resolve the target fork before fighting"),
            Self::EnemyIsActive(enemy) => write!(f, "enemy combatant {enemy} is active"),
            Self::HeroIsActive(hero) => write!(f, "hero combatant {hero} is active"),
            Self::TargetDown(target) => write!(f, "selected target {target} is already down"),
            Self::UnsafeStrike { target, hp, die } => write!(
                f,
                "target {target} has {hp} HP; a d{die} strike could cross the Arena floor"
            ),
            Self::PartyRefused(reason) => write!(f, "party executor refused: {reason}"),
            Self::VoteRefused(reason) => write!(f, "vote engine refused: {reason}"),
            Self::ForkRefused(reason) => write!(f, "fork refused: {reason}"),
            Self::ArenaRefused(reason) => write!(f, "Arena executor refused: {reason}"),
            Self::CommitInterrupted { point, reason } => {
                write!(f, "contribution interrupted at {point:?}: {reason}")
            }
            Self::StalePrepared => write!(f, "prepared contribution anchor is stale"),
            Self::MalformedPrepared(reason) => {
                write!(f, "malformed prepared contribution: {reason}")
            }
            Self::Journal(reason) => write!(f, "contribution journal failed: {reason}"),
            Self::ReplayDiverged { event, detail } => {
                write!(f, "encounter replay diverged at event {event}: {detail}")
            }
            Self::InvalidRecord(reason) => write!(f, "invalid encounter record: {reason}"),
        }
    }
}

impl std::error::Error for EncounterError {}

/// The live bridge across the real party, vote, and tactical-Arena engines.
pub struct PartyArenaEncounter {
    roster: [String; 4],
    leader: String,
    arena_seed: u8,
    party: Party,
    arena: Arena,
    fork: Option<PartyFork>,
    votes: BTreeMap<String, usize>,
    target: Option<u8>,
    events: Vec<EncounterEvent>,
    root: [u8; 32],
    /// The host-private custody root the party's local seat secrets derive from (see
    /// [`PartyArenaEncounter::custody_root`]). Never enters [`EncounterRecord`].
    custody_root: Option<[u8; 32]>,
}

impl PartyArenaEncounter {
    /// Start a gate assault from a canonical role-aligned roster. The seats' ballot
    /// secrets are drawn from OS entropy; keep [`custody_root`](Self::custody_root) if you
    /// intend to [`resume`](Self::resume) this encounter after a restart.
    pub fn new(
        roster: [String; 4],
        leader: impl Into<String>,
        arena_seed: u8,
    ) -> Result<Self, EncounterError> {
        let party = Party::muster_with_roster([
            (Role::Tank, roster[0].clone()),
            (Role::Scout, roster[1].clone()),
            (Role::Mage, roster[2].clone()),
            (Role::Healer, roster[3].clone()),
        ])
        .map_err(|error| EncounterError::InvalidRecord(error.to_string()))?;
        Self::from_party(party, leader, arena_seed)
    }

    /// Rebuild the SAME seats a previous encounter had, from the host-held secret
    /// `custody_root` ([`Self::custody_root`]). The replay path — a resumed record's
    /// recorded ballots only re-verify against seats derived from the same root.
    fn new_under_root(
        roster: [String; 4],
        leader: impl Into<String>,
        arena_seed: u8,
        custody_root: [u8; 32],
    ) -> Result<Self, EncounterError> {
        let party = Party::muster_under_custody_root(
            custody_root,
            [
                (Role::Tank, roster[0].clone()),
                (Role::Scout, roster[1].clone()),
                (Role::Mage, roster[2].clone()),
                (Role::Healer, roster[3].clone()),
            ],
        )
        .map_err(|error| EncounterError::InvalidRecord(error.to_string()))?;
        Self::from_party(party, leader, arena_seed)
    }

    /// **The host-private custody root** this encounter's seat ballot keys derive from.
    ///
    /// ⚠ Key material. A host that persists an [`EncounterRecord`] to resume later must
    /// store this ALONGSIDE it, in its own private storage — never inside the record, which
    /// is the publishable object. `None` when the players hold their own secrets
    /// ([`Party::muster_with_custody`]); such an encounter cannot mint seat ballots and so
    /// cannot be resumed by re-signing either.
    pub fn custody_root(&self) -> Option<[u8; 32]> {
        self.custody_root
    }

    /// The custody root the isolated candidate image must be rebuilt under. A party whose
    /// seats are remote-custody holds no secret, so it cannot mint the ballots a replay
    /// re-drives — that is a refusal, not a silently weaker replay.
    fn replay_custody_root(&self) -> Result<[u8; 32], EncounterError> {
        self.custody_root.ok_or_else(|| {
            EncounterError::InvalidRecord(
                "this encounter's seats hold their own ballot secrets, so the party cannot \
                 rebuild a replay image that re-signs for them"
                    .to_string(),
            )
        })
    }

    /// Enter the Arena with the actual party returned by a live
    /// [`crate::lobby::PartyLobby`] launch. This consumes that cap-seated world;
    /// it does not rebuild a parallel synthetic roster. The canonical roster is
    /// read back out only for restart replay.
    pub fn from_party(
        party: Party,
        leader: impl Into<String>,
        arena_seed: u8,
    ) -> Result<Self, EncounterError> {
        let roster: [String; 4] = Role::ALL.map(|role| {
            party
                .seats()
                .iter()
                .find(|seat| seat.role() == role)
                .expect("Party construction guarantees every canonical role")
                .name()
                .to_string()
        });
        let leader = leader.into();
        if !roster.iter().any(|identity| identity == &leader) {
            return Err(EncounterError::LeaderNotSeated);
        }
        let fork = party
            .open_fork(
                "Which enemy does the party concentrate on?",
                vec![
                    ("Break the Warden".to_string(), WARDEN as u64),
                    ("Silence the Hound".to_string(), HOUND as u64),
                ],
            )
            .map_err(|error| EncounterError::VoteRefused(error.to_string()))?;
        let arena = Arena::deploy(arena_seed);
        let root = genesis_root(&roster, &leader, arena_seed, &party, &arena);
        let custody_root = party.custody_root();
        Ok(Self {
            roster,
            leader,
            arena_seed,
            party,
            arena,
            fork: Some(fork),
            votes: BTreeMap::new(),
            target: None,
            events: Vec::new(),
            root,
            custody_root,
        })
    }

    /// Live party world.
    pub fn party(&self) -> &Party {
        &self.party
    }

    /// Live tactical Arena.
    pub fn arena(&self) -> &Arena {
        &self.arena
    }

    /// Quorum-selected target, once resolved.
    pub fn target(&self) -> Option<u8> {
        self.target
    }

    /// Current domain-separated encounter root.
    pub fn root(&self) -> [u8; 32] {
        self.root
    }

    /// Number of admitted encounter events.
    pub fn revision(&self) -> u64 {
        self.events.len() as u64
    }

    /// Immutable admitted events.
    pub fn events(&self) -> &[EncounterEvent] {
        &self.events
    }

    /// Export the semantic history and complete observed receipts for restart.
    pub fn export_record(&self) -> EncounterRecord {
        EncounterRecord {
            roster: self.roster.clone(),
            leader: self.leader.clone(),
            arena_seed: self.arena_seed,
            events: self.events.clone(),
        }
    }

    /// Cast the actor's own custody-signed target ballot.
    pub fn vote(&mut self, actor: &str, option: usize) -> Result<&EncounterEvent, EncounterError> {
        self.check_event_capacity()?;
        if self.target.is_some() {
            return Err(EncounterError::ForkResolved);
        }
        if option > 1 {
            return Err(EncounterError::InvalidOption);
        }
        if self.party.seat_index_for(actor).is_none() {
            return Err(EncounterError::Unseated(actor.to_string()));
        }
        if self.votes.contains_key(actor) {
            return Err(EncounterError::AlreadyVoted);
        }
        let fork = self.fork.as_mut().ok_or(EncounterError::ForkResolved)?;
        let ballot_poll = fork.poll();
        // `try_sign_ballot_as`, not `sign_ballot_as`: a party mustered by
        // `Party::muster_with_custody` holds no secret for its seats (the players do), and
        // that is a refusal to report, not a panic. Such a deployment submits an
        // already-signed ballot rather than asking the host to mint one.
        let ballot =
            self.party
                .try_sign_ballot_as(fork, actor, option)
                .map_err(|error| match error {
                    crate::BallotCustodyError::Unseated(who) => EncounterError::Unseated(who.0),
                    remote => EncounterError::VoteRefused(remote.to_string()),
                })?;
        let receipt = fork
            .cast_receipted(&ballot)
            .map_err(|error| EncounterError::VoteRefused(error.to_string()))?;
        self.votes.insert(actor.to_string(), option);
        Ok(self.append(
            EncounterCommand::Vote {
                actor: actor.to_string(),
                option,
            },
            Some(ballot),
            Some(ballot_poll),
            Some(receipt),
            None,
            None,
        ))
    }

    /// Resolve the quorum target and commit it to the party gate. Only the
    /// designated leader may turn the collective certificate into world state.
    pub fn resolve(&mut self, actor: &str) -> Result<&EncounterEvent, EncounterError> {
        self.check_event_capacity()?;
        if actor != self.leader {
            return Err(EncounterError::LeaderOnly);
        }
        if self.target.is_some() {
            return Err(EncounterError::ForkResolved);
        }
        let fork = self.fork.as_mut().ok_or(EncounterError::ForkResolved)?;
        let resolution = fork
            .resolve_into(&mut self.party)
            .map_err(|error| match error {
                ForkError::BelowQuorum => EncounterError::ForkRefused("below quorum".to_string()),
                other => EncounterError::ForkRefused(other.to_string()),
            })?;
        let receipt = self
            .party
            .world()
            .receipts()
            .last()
            .filter(|receipt| receipt.turn_hash == resolution.receipt)
            .cloned()
            .ok_or_else(|| {
                EncounterError::ForkRefused(
                    "party fork committed without its complete receipt".to_string(),
                )
            })?;
        self.target = Some(resolution.path as u8);
        self.fork = None;
        Ok(self.append(
            EncounterCommand::Resolve {
                actor: actor.to_string(),
            },
            None,
            None,
            None,
            Some(receipt),
            None,
        ))
    }

    /// Fire the requested role contribution as `actor` and mechanically apply
    /// its corresponding tactic to the current hero's Arena turn.
    pub fn contribute(
        &mut self,
        actor: &str,
        requested: Role,
    ) -> Result<&EncounterEvent, EncounterError> {
        self.contribute_with_hook(actor, requested, &mut NoContributionCommitHook)
    }

    /// Execute a paired contribution on an isolated replayed image and publish
    /// it only after both real executor turns and every hook checkpoint succeed.
    pub fn contribute_with_hook<H: ContributionCommitHook>(
        &mut self,
        actor: &str,
        requested: Role,
        hook: &mut H,
    ) -> Result<&EncounterEvent, EncounterError> {
        let prepared =
            PreparedContribution::new(self.revision(), self.root(), actor.to_string(), requested);
        self.commit_prepared_with_hook(&prepared, hook)
    }

    /// Validate and return a durable contribution intent without mutating the
    /// live encounter. Validation executes both legs against a disposable
    /// candidate, so a returned prepare is known to be admissible at its anchor.
    pub fn prepare_contribution(
        &self,
        actor: &str,
        requested: Role,
    ) -> Result<PreparedContribution, EncounterError> {
        let prepared =
            PreparedContribution::new(self.revision(), self.root(), actor.to_string(), requested);
        prepared.validate()?;
        let mut candidate = Self::resume_at(
            &self.export_record(),
            self.replay_custody_root()?,
            prepared.base_revision,
            prepared.base_root,
        )?;
        candidate.contribute_in_place_with_hook(
            &prepared.actor,
            prepared.role,
            &mut NoContributionCommitHook,
        )?;
        Ok(prepared)
    }

    /// Validate a contribution and fsync its exact intent before any live
    /// mutation. Repeating the same call is idempotent at the journal boundary.
    pub fn prepare_contribution_durable(
        &self,
        actor: &str,
        requested: Role,
        journal: &FileContributionJournal,
    ) -> Result<PreparedContribution, EncounterError> {
        let prepared = self.prepare_contribution(actor, requested)?;
        journal.reserve(&prepared)?;
        Ok(prepared)
    }

    /// Compare-and-swap a prepared intent onto the exact encounter head.
    pub fn commit_prepared(
        &mut self,
        prepared: &PreparedContribution,
    ) -> Result<&EncounterEvent, EncounterError> {
        self.commit_prepared_with_hook(prepared, &mut NoContributionCommitHook)
    }

    pub fn commit_prepared_with_hook<H: ContributionCommitHook>(
        &mut self,
        prepared: &PreparedContribution,
        hook: &mut H,
    ) -> Result<&EncounterEvent, EncounterError> {
        prepared.validate()?;
        if self.revision() != prepared.base_revision || self.root() != prepared.base_root {
            return Err(EncounterError::StalePrepared);
        }

        // The candidate owns both temporary engines. A refusal or process death
        // before the final assignment cannot expose either prefix through `self`.
        let mut candidate = Self::resume_at(
            &self.export_record(),
            self.replay_custody_root()?,
            prepared.base_revision,
            prepared.base_root,
        )?;
        candidate.contribute_in_place_with_hook(&prepared.actor, prepared.role, hook)?;
        hook.checkpoint(ContributionCheckpoint::BeforePublish)
            .map_err(|reason| EncounterError::CommitInterrupted {
                point: ContributionCheckpoint::BeforePublish,
                reason,
            })?;
        *self = candidate;
        Ok(self
            .events
            .last()
            .expect("a committed prepared contribution appended one event"))
    }

    /// Recover one checksummed prepared intent against an untrusted durable
    /// encounter record. This is idempotent across every crash interval.
    pub fn recover_prepared(
        record: &EncounterRecord,
        custody_root: [u8; 32],
        prepared: &PreparedContribution,
    ) -> Result<(Self, ContributionRecovery), EncounterError> {
        prepared.validate()?;
        let mut encounter = Self::resume(record, custody_root)?;
        let record_revision = encounter.revision();

        if record_revision == prepared.base_revision {
            if encounter.root() != prepared.base_root {
                return Err(EncounterError::StalePrepared);
            }
            encounter.commit_prepared(prepared)?;
            return Ok((encounter, ContributionRecovery::Applied));
        }

        if record_revision > prepared.base_revision {
            let base_matches = root_at_revision(record, prepared.base_revision)
                .is_some_and(|root| root == prepared.base_root);
            let command_matches = usize::try_from(prepared.base_revision)
                .ok()
                .and_then(|index| record.events.get(index))
                .is_some_and(|event| {
                    event.command
                        == (EncounterCommand::Contribute {
                            actor: prepared.actor.clone(),
                            role: prepared.role,
                        })
                });
            if base_matches && command_matches {
                return Ok((encounter, ContributionRecovery::AlreadyCommitted));
            }
        }
        Err(EncounterError::StalePrepared)
    }

    /// Load and recover the journal's outstanding command. The returned intent
    /// remains reserved: the host first durably replaces its [`EncounterRecord`]
    /// with `encounter.export_record()`, then calls
    /// [`FileContributionJournal::clear`] with that exact intent.
    pub fn recover_journaled(
        record: &EncounterRecord,
        custody_root: [u8; 32],
        journal: &FileContributionJournal,
    ) -> Result<Option<(Self, PreparedContribution, ContributionRecovery)>, EncounterError> {
        let Some(prepared) = journal.load()? else {
            return Ok(None);
        };
        let (encounter, recovery) = Self::recover_prepared(record, custody_root, &prepared)?;
        Ok(Some((encounter, prepared, recovery)))
    }

    /// The serial work performed only inside a detached candidate or during
    /// replay. Callers must use the transactional wrappers above.
    fn contribute_in_place_with_hook<H: ContributionCommitHook>(
        &mut self,
        actor: &str,
        requested: Role,
        hook: &mut H,
    ) -> Result<&EncounterEvent, EncounterError> {
        self.check_event_capacity()?;
        let target = self.target.ok_or(EncounterError::TargetNotResolved)?;
        self.party
            .seat_index_for(actor)
            .ok_or_else(|| EncounterError::Unseated(actor.to_string()))?;
        // Deliberately do not host-check `held == requested`: the requested role
        // move is sent through the actor's real capability-bearing seat below.
        // A forged teammate move therefore reaches, and is refused by, the party
        // executor's capability tooth. The lookup above only establishes membership.
        if role_used(&self.party, requested) {
            // Reach the actual WriteOnce tooth even when the corresponding Arena
            // tactic would now be ineligible because the first use changed combat.
            return match self.party.act_as(actor, requested.move_of()) {
                ActOutcome::Refused { reason } => Err(EncounterError::PartyRefused(reason)),
                ActOutcome::Committed { .. } => Err(EncounterError::PartyRefused(
                    "a previously used role unexpectedly committed twice".to_string(),
                )),
            };
        }
        let active = self.arena.active();
        if !is_hero(active) {
            return Err(EncounterError::EnemyIsActive(active));
        }
        self.preflight_player(active, target, requested)?;

        let party_outcome = self.party.act_as(actor, requested.move_of());
        let party_hash = match party_outcome {
            ActOutcome::Committed { receipt } => receipt,
            ActOutcome::Refused { reason } => return Err(EncounterError::PartyRefused(reason)),
        };
        let party_receipt = self
            .party
            .world()
            .receipts()
            .last()
            .filter(|receipt| receipt.turn_hash == party_hash)
            .cloned()
            .ok_or_else(|| {
                EncounterError::PartyRefused(
                    "party role committed without its complete receipt".to_string(),
                )
            })?;

        hook.checkpoint(ContributionCheckpoint::AfterParty)
            .map_err(|reason| EncounterError::CommitInterrupted {
                point: ContributionCheckpoint::AfterParty,
                reason,
            })?;

        let arena_receipt = match requested {
            Role::Tank | Role::Healer => self.arena.guard(active),
            Role::Scout if self.arena.hp(target) <= FINISH_THRESHOLD => {
                self.arena.finish(active, target)
            }
            Role::Scout => self.arena.attack(active, target).map(|hit| hit.receipt),
            Role::Mage => self.arena.heavy(active, target).map(|hit| hit.receipt),
        }
        .map_err(|error| EncounterError::ArenaRefused(error.to_string()))?;

        hook.checkpoint(ContributionCheckpoint::AfterArena)
            .map_err(|reason| EncounterError::CommitInterrupted {
                point: ContributionCheckpoint::AfterArena,
                reason,
            })?;

        Ok(self.append(
            EncounterCommand::Contribute {
                actor: actor.to_string(),
                role: requested,
            },
            None,
            None,
            None,
            Some(party_receipt),
            Some(arena_receipt),
        ))
    }

    /// Advance a non-player combatant. This is an explicit leader-authorized
    /// system step, so enemy movement is neither hidden in a player's receipt nor
    /// silently performed by rendering code.
    pub fn advance_enemy(&mut self, actor: &str) -> Result<&EncounterEvent, EncounterError> {
        self.check_event_capacity()?;
        if actor != self.leader {
            return Err(EncounterError::LeaderOnly);
        }
        self.target.ok_or(EncounterError::TargetNotResolved)?;
        let active = self.arena.active();
        if is_hero(active) {
            return Err(EncounterError::HeroIsActive(active));
        }
        let receipt = if self.arena.is_stunned(active) {
            self.arena.pass(active)
        } else {
            let target = [RANGER, CLERIC]
                .into_iter()
                .filter(|hero| !self.arena.is_down(*hero))
                .min_by_key(|hero| (self.arena.is_guarding(*hero), self.arena.hp(*hero)))
                .ok_or_else(|| EncounterError::ArenaRefused("all heroes are down".to_string()))?;
            let hp = self.arena.hp(target);
            if hp <= FINISH_THRESHOLD && !self.arena.is_guarding(target) {
                self.arena.finish(active, target)
            } else if hp > ATTACK_DIE {
                self.arena.attack(active, target).map(|hit| hit.receipt)
            } else {
                self.arena.guard(active)
            }
        }
        .map_err(|error| EncounterError::ArenaRefused(error.to_string()))?;
        Ok(self.append(
            EncounterCommand::AdvanceEnemy {
                actor: actor.to_string(),
            },
            None,
            None,
            None,
            None,
            Some(receipt),
        ))
    }

    /// Re-drive an untrusted record through fresh party, vote, and Arena engines.
    /// The returned live encounter can continue play after restart.
    pub fn resume(
        record: &EncounterRecord,
        custody_root: [u8; 32],
    ) -> Result<Self, EncounterError> {
        if record.events.len() > MAX_ENCOUNTER_EVENTS {
            return Err(EncounterError::InvalidRecord(format!(
                "{} events exceeds the {MAX_ENCOUNTER_EVENTS}-event bound",
                record.events.len()
            )));
        }
        let mut replay = Self::new_under_root(
            record.roster.clone(),
            record.leader.clone(),
            record.arena_seed,
            custody_root,
        )?;
        validate_record_chain(record, replay.root)?;
        for (idx, expected) in record.events.iter().enumerate() {
            let actual = match &expected.command {
                EncounterCommand::Vote { actor, option } => replay.vote(actor, *option),
                EncounterCommand::Resolve { actor } => replay.resolve(actor),
                EncounterCommand::Contribute { actor, role } => replay
                    .contribute_in_place_with_hook(actor, *role, &mut NoContributionCommitHook),
                EncounterCommand::AdvanceEnemy { actor } => replay.advance_enemy(actor),
            }
            .map_err(|error| EncounterError::ReplayDiverged {
                event: idx + 1,
                detail: format!("semantic command refused: {error}"),
            })?;
            if let Err(detail) = event_matches(actual, expected) {
                return Err(EncounterError::ReplayDiverged {
                    event: idx + 1,
                    detail,
                });
            }
        }
        // The fresh collective engine has a fresh process-local operator/poll,
        // so its replay ballot bytes and application roots intentionally differ.
        // The original chain was self-verified above and its custody signatures
        // independently checked by `event_matches`; retain that anchored record
        // while installing the freshly replayed live worlds underneath it.
        replay.events = record.events.clone();
        replay.root = record
            .events
            .last()
            .map(|event| event.root)
            .unwrap_or(replay.root);
        Ok(replay)
    }

    /// Resume and additionally require an independently anchored latest
    /// revision/root, refusing a valid but truncated prefix or a rewritten
    /// self-consistent chain.
    pub fn resume_at(
        record: &EncounterRecord,
        custody_root: [u8; 32],
        expected_revision: u64,
        expected_root: [u8; 32],
    ) -> Result<Self, EncounterError> {
        let replay = Self::resume(record, custody_root)?;
        if replay.revision() != expected_revision || replay.root() != expected_root {
            return Err(EncounterError::InvalidRecord(
                "record does not match the independently anchored latest revision/root".to_string(),
            ));
        }
        Ok(replay)
    }

    fn preflight_player(
        &self,
        active: u8,
        target: u8,
        requested: Role,
    ) -> Result<(), EncounterError> {
        if self.arena.is_down(target) {
            return Err(EncounterError::TargetDown(target));
        }
        if self.arena.is_down(active) || self.arena.is_stunned(active) {
            return Err(EncounterError::ArenaRefused(
                "the active hero cannot use this role tactic".to_string(),
            ));
        }
        let hp = self.arena.hp(target);
        match requested {
            // NOTE: there is NO Scout `UnsafeStrike` arm, and that is a THEOREM about the
            // shipped parameters, not an omission. A Scout with `hp <= FINISH_THRESHOLD`
            // takes the `finish` branch (see `contribute`); otherwise it attacks for at most
            // `ATTACK_DIE`. So the only unsafe Scout strike is `FINISH_THRESHOLD < hp <=
            // ATTACK_DIE` — an EMPTY interval while `FINISH_THRESHOLD >= ATTACK_DIE`, which
            // `SCOUT_ATTACK_CANNOT_FLOOR` below proves at compile time. This file used to
            // carry that arm as live code; it was unsatisfiable (clippy
            // `impossible_comparisons`) and therefore refused nothing. If the balance
            // constants ever separate, the const assertion fails to compile and points here.
            Role::Scout if hp <= FINISH_THRESHOLD && self.arena.is_guarding(target) => Err(
                EncounterError::ArenaRefused("a guarding target cannot be finished".to_string()),
            ),
            Role::Mage if hp <= HEAVY_DIE => Err(EncounterError::UnsafeStrike {
                target,
                hp,
                die: HEAVY_DIE,
            }),
            _ => Ok(()),
        }
    }

    fn check_event_capacity(&self) -> Result<(), EncounterError> {
        if self.events.len() >= MAX_ENCOUNTER_EVENTS {
            Err(EncounterError::EventLimit)
        } else {
            Ok(())
        }
    }

    fn append(
        &mut self,
        command: EncounterCommand,
        ballot: Option<SignedBallot>,
        ballot_poll: Option<PollId>,
        vote_receipt: Option<TurnReceipt>,
        party_receipt: Option<TurnReceipt>,
        arena_receipt: Option<TurnReceipt>,
    ) -> &EncounterEvent {
        let revision = self.revision() + 1;
        let arena_state = self.arena.world.snapshot();
        let party_root = self.party.world().state_root();
        let party_state = party_state(&self.party);
        let arena_active = self.arena.active();
        let arena_outcome = self.arena.outcome();
        let root = next_root(
            self.root,
            revision,
            &command,
            ballot.as_ref(),
            ballot_poll,
            vote_receipt.as_ref(),
            party_receipt.as_ref(),
            arena_receipt.as_ref(),
            self.target,
            arena_active,
            arena_outcome,
            &arena_state,
            party_root,
            &party_state,
        );
        self.root = root;
        self.events.push(EncounterEvent {
            revision,
            command,
            ballot,
            ballot_poll,
            vote_receipt,
            party_receipt,
            arena_receipt,
            target: self.target,
            arena_active,
            arena_outcome,
            arena_state,
            party_root,
            party_state,
            root,
        });
        self.events.last().expect("the event was just appended")
    }
}

fn genesis_root(
    roster: &[String; 4],
    leader: &str,
    arena_seed: u8,
    party: &Party,
    arena: &Arena,
) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(GENESIS_DOMAIN);
    for identity in roster {
        hash_string(&mut h, identity);
    }
    hash_string(&mut h, leader);
    h.update(&[arena_seed]);
    h.update(&party.world().state_root());
    h.update(&arena.genesis.receipt_hash());
    hash_u64s(&mut h, &arena.world.snapshot());
    *h.finalize().as_bytes()
}

#[allow(clippy::too_many_arguments)]
fn next_root(
    previous: [u8; 32],
    revision: u64,
    command: &EncounterCommand,
    ballot: Option<&SignedBallot>,
    ballot_poll: Option<PollId>,
    vote_receipt: Option<&TurnReceipt>,
    party_receipt: Option<&TurnReceipt>,
    arena_receipt: Option<&TurnReceipt>,
    target: Option<u8>,
    active: u8,
    outcome: ArenaOutcome,
    arena_state: &[u64],
    party_root: [u8; 32],
    party_state: &[u64],
) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(EVENT_DOMAIN);
    h.update(&previous);
    h.update(&revision.to_le_bytes());
    hash_command(&mut h, command);
    hash_ballot(&mut h, ballot, ballot_poll);
    hash_receipt(&mut h, vote_receipt);
    hash_receipt(&mut h, party_receipt);
    hash_receipt(&mut h, arena_receipt);
    h.update(&[target.unwrap_or(u8::MAX), active, outcome_tag(outcome)]);
    hash_u64s(&mut h, arena_state);
    h.update(&party_root);
    hash_u64s(&mut h, party_state);
    *h.finalize().as_bytes()
}

fn hash_command(h: &mut blake3::Hasher, command: &EncounterCommand) {
    match command {
        EncounterCommand::Vote { actor, option } => {
            h.update(&[0]);
            hash_string(h, actor);
            h.update(&(*option as u64).to_le_bytes());
        }
        EncounterCommand::Resolve { actor } => {
            h.update(&[1]);
            hash_string(h, actor);
        }
        EncounterCommand::Contribute { actor, role } => {
            h.update(&[2, role.index() as u8]);
            hash_string(h, actor);
        }
        EncounterCommand::AdvanceEnemy { actor } => {
            h.update(&[3]);
            hash_string(h, actor);
        }
    }
}

fn hash_receipt(h: &mut blake3::Hasher, receipt: Option<&TurnReceipt>) {
    match receipt {
        Some(receipt) => {
            h.update(&[1]);
            h.update(&receipt.receipt_hash());
            match &receipt.executor_signature {
                Some(signature) => {
                    h.update(&(signature.len() as u64).to_le_bytes());
                    h.update(signature);
                }
                None => {
                    h.update(&0u64.to_le_bytes());
                }
            }
        }
        None => {
            h.update(&[0]);
        }
    }
}

fn hash_ballot(h: &mut blake3::Hasher, ballot: Option<&SignedBallot>, poll: Option<PollId>) {
    match (ballot, poll) {
        (Some(ballot), Some(poll)) => {
            h.update(&[1]);
            h.update(poll.0.as_bytes());
            h.update(ballot.voter_pk.as_bytes());
            h.update(&(ballot.option as u64).to_le_bytes());
            h.update(&ballot.signature.0);
        }
        (None, None) => {
            h.update(&[0]);
        }
        _ => {
            h.update(&[0xff]);
        }
    }
}

fn hash_string(h: &mut blake3::Hasher, value: &str) {
    h.update(&(value.len() as u64).to_le_bytes());
    h.update(value.as_bytes());
}

fn hash_u64s(h: &mut blake3::Hasher, values: &[u64]) {
    h.update(&(values.len() as u64).to_le_bytes());
    for value in values {
        h.update(&value.to_le_bytes());
    }
}

fn outcome_tag(outcome: ArenaOutcome) -> u8 {
    match outcome {
        ArenaOutcome::Ongoing => 0,
        ArenaOutcome::Victory => 1,
        ArenaOutcome::Defeat => 2,
    }
}

fn event_matches(actual: &EncounterEvent, expected: &EncounterEvent) -> Result<(), String> {
    if actual.revision != expected.revision || actual.command != expected.command {
        return Err("revision or semantic command changed".to_string());
    }
    verify_recorded_ballot(actual, expected)?;
    // The current collective-choice engine issues a complete but unsigned
    // process-local receipt whose cell ids are freshly generated on restart.
    // Its authority is therefore the custody signature + successful semantic
    // replay, not byte equality of that receipt. Preserve it for audit, require
    // the same presence and a nonzero committed turn, but do not pretend it is
    // a portable executor-signed certificate.
    match (&actual.vote_receipt, &expected.vote_receipt) {
        (None, None) => {}
        (Some(actual), Some(expected))
            if actual.turn_hash != [0u8; 32] && expected.turn_hash != [0u8; 32] => {}
        _ => return Err("ballot-engine receipt presence/commitment changed".to_string()),
    }
    if !same_receipt_presence(&actual.party_receipt, &expected.party_receipt) {
        return Err("party authorization receipt presence changed".to_string());
    }
    if !same_receipt_presence(&actual.arena_receipt, &expected.arena_receipt) {
        return Err("Arena transition receipt presence changed".to_string());
    }
    if actual.target != expected.target
        || actual.arena_active != expected.arena_active
        || actual.arena_outcome != expected.arena_outcome
        || actual.arena_state != expected.arena_state
        || actual.party_state != expected.party_state
    {
        return Err("committed target/state changed".to_string());
    }
    Ok(())
}

fn verify_recorded_ballot(
    actual: &EncounterEvent,
    expected: &EncounterEvent,
) -> Result<(), String> {
    match (
        &actual.command,
        &actual.ballot,
        &expected.ballot,
        expected.ballot_poll,
    ) {
        (
            EncounterCommand::Vote { option, .. },
            Some(actual),
            Some(expected),
            Some(expected_poll),
        ) if actual.voter_pk == expected.voter_pk
            && actual.option == expected.option
            && expected.option == *option
            && dregg_types::verify(
                &expected.voter_pk,
                &ballot_message(expected_poll, &expected.voter_pk, expected.option),
                &expected.signature,
            ) =>
        {
            Ok(())
        }
        (EncounterCommand::Vote { .. }, _, _, _) => {
            Err("recorded custody ballot/poll/signature is invalid".to_string())
        }
        (_, None, None, None) => Ok(()),
        _ => Err("a non-vote event carried ballot evidence".to_string()),
    }
}

fn ballot_message(poll: PollId, voter_pk: &dregg_types::PublicKey, option: usize) -> Vec<u8> {
    const DOMAIN: &[u8] = b"dungeon-on-dregg/collective/ballot-v1";
    let mut message = Vec::with_capacity(DOMAIN.len() + 32 + 32 + 8);
    message.extend_from_slice(DOMAIN);
    message.extend_from_slice(poll.0.as_bytes());
    message.extend_from_slice(voter_pk.as_bytes());
    message.extend_from_slice(&(option as u64).to_be_bytes());
    message
}

fn validate_record_chain(
    record: &EncounterRecord,
    genesis_root: [u8; 32],
) -> Result<(), EncounterError> {
    let mut previous = genesis_root;
    for (idx, event) in record.events.iter().enumerate() {
        let revision = (idx + 1) as u64;
        if event.revision != revision {
            return Err(EncounterError::ReplayDiverged {
                event: idx + 1,
                detail: "non-monotone event revision".to_string(),
            });
        }
        let recomputed = next_root(
            previous,
            revision,
            &event.command,
            event.ballot.as_ref(),
            event.ballot_poll,
            event.vote_receipt.as_ref(),
            event.party_receipt.as_ref(),
            event.arena_receipt.as_ref(),
            event.target,
            event.arena_active,
            event.arena_outcome,
            &event.arena_state,
            event.party_root,
            &event.party_state,
        );
        if recomputed != event.root {
            return Err(EncounterError::ReplayDiverged {
                event: idx + 1,
                detail: "recorded receipt/state root does not recompute".to_string(),
            });
        }
        previous = event.root;
    }
    Ok(())
}

fn same_receipt_presence(left: &Option<TurnReceipt>, right: &Option<TurnReceipt>) -> bool {
    match (left, right) {
        (None, None) => true,
        (Some(left), Some(right)) => left.turn_hash != [0u8; 32] && right.turn_hash != [0u8; 32],
        _ => false,
    }
}

fn role_used(party: &Party, role: Role) -> bool {
    let layout = party.layout();
    let cell = match role {
        Role::Tank => layout.front,
        Role::Scout => layout.lock,
        Role::Mage => layout.ward,
        Role::Healer => layout.rally,
    };
    party.read_field(cell, ROLE_SLOT) != 0
}

fn party_state(party: &Party) -> Vec<u64> {
    let layout = party.layout();
    let mut state = vec![
        party.read_field(layout.gate, GATE_SLOT),
        party.read_field(layout.front, ROLE_SLOT),
        party.read_field(layout.lock, ROLE_SLOT),
        party.read_field(layout.ward, ROLE_SLOT),
        party.read_field(layout.rally, ROLE_SLOT),
        party.read_field(layout.focus, FOCUS_SPENT_SLOT),
        party.read_field(layout.focus, FOCUS_BUDGET_SLOT),
    ];
    state.extend((0..party.seat_count()).map(|idx| party.loot_share(idx)));
    state
}

fn contribution_intent(
    base_revision: u64,
    base_root: [u8; 32],
    actor: &str,
    role: Role,
) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(CONTRIBUTION_INTENT_DOMAIN);
    hasher.update(&base_revision.to_be_bytes());
    hasher.update(&base_root);
    hasher.update(&[role_tag(role)]);
    hasher.update(&(actor.len() as u16).to_be_bytes());
    hasher.update(actor.as_bytes());
    *hasher.finalize().as_bytes()
}

fn role_tag(role: Role) -> u8 {
    role.index() as u8
}

fn role_from_tag(tag: u8) -> Result<Role, EncounterError> {
    Role::ALL
        .get(tag as usize)
        .copied()
        .ok_or_else(|| EncounterError::MalformedPrepared("unknown role tag".to_string()))
}

fn root_at_revision(record: &EncounterRecord, revision: u64) -> Option<[u8; 32]> {
    if revision == 0 {
        return PartyArenaEncounter::new(
            record.roster.clone(),
            record.leader.clone(),
            record.arena_seed,
        )
        .ok()
        .map(|encounter| encounter.root());
    }
    usize::try_from(revision)
        .ok()
        .and_then(|revision| revision.checked_sub(1))
        .and_then(|index| record.events.get(index))
        .map(|event| event.root)
}

struct PreparedCursor<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl<'a> PreparedCursor<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, offset: 0 }
    }

    fn take<const N: usize>(&mut self) -> Result<[u8; N], EncounterError> {
        let end = self.offset.checked_add(N).ok_or_else(|| {
            EncounterError::MalformedPrepared("prepared wire offset overflow".to_string())
        })?;
        let value = self.bytes.get(self.offset..end).ok_or_else(|| {
            EncounterError::MalformedPrepared("prepared wire is truncated".to_string())
        })?;
        self.offset = end;
        value.try_into().map_err(|_| {
            EncounterError::MalformedPrepared("prepared wire field has wrong width".to_string())
        })
    }

    fn byte(&mut self) -> Result<u8, EncounterError> {
        Ok(self.take::<1>()?[0])
    }

    fn string(&mut self, length: usize) -> Result<String, EncounterError> {
        let end = self.offset.checked_add(length).ok_or_else(|| {
            EncounterError::MalformedPrepared("prepared actor offset overflow".to_string())
        })?;
        let value = self.bytes.get(self.offset..end).ok_or_else(|| {
            EncounterError::MalformedPrepared("prepared actor is truncated".to_string())
        })?;
        self.offset = end;
        std::str::from_utf8(value)
            .map(str::to_string)
            .map_err(|_| EncounterError::MalformedPrepared("actor is not UTF-8".to_string()))
    }

    fn finished(&self) -> bool {
        self.offset == self.bytes.len()
    }
}
