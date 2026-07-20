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
//! ## Boundary
//!
//! The two world commits are serial in one process and the encounter root binds
//! their receipts after both land. This is strong replay-verifiable application
//! authorization, but it is not yet one atomic multi-cell/hyperedge commit: a
//! process crash in the narrow interval between the party and Arena commits needs
//! the durable host to discard the unjournaled prefix and resume from the last
//! encounter root.

use std::collections::BTreeMap;

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

const GENESIS_DOMAIN: &[u8] = b"dregg.party-arena.genesis.v1";
const EVENT_DOMAIN: &[u8] = b"dregg.party-arena.event.v1";

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
}

impl PartyArenaEncounter {
    /// Start a gate assault from a canonical role-aligned roster.
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
        let ballot = self
            .party
            .sign_ballot_as(fork, actor, option)
            .map_err(|error| EncounterError::Unseated(error.0))?;
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

        let arena_receipt = match requested {
            Role::Tank | Role::Healer => self.arena.guard(active),
            Role::Scout if self.arena.hp(target) <= FINISH_THRESHOLD => {
                self.arena.finish(active, target)
            }
            Role::Scout => self.arena.attack(active, target).map(|hit| hit.receipt),
            Role::Mage => self.arena.heavy(active, target).map(|hit| hit.receipt),
        }
        .map_err(|error| EncounterError::ArenaRefused(error.to_string()))?;

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
    pub fn resume(record: &EncounterRecord) -> Result<Self, EncounterError> {
        if record.events.len() > MAX_ENCOUNTER_EVENTS {
            return Err(EncounterError::InvalidRecord(format!(
                "{} events exceeds the {MAX_ENCOUNTER_EVENTS}-event bound",
                record.events.len()
            )));
        }
        let mut replay = Self::new(
            record.roster.clone(),
            record.leader.clone(),
            record.arena_seed,
        )?;
        validate_record_chain(record, replay.root)?;
        for (idx, expected) in record.events.iter().enumerate() {
            let actual = match &expected.command {
                EncounterCommand::Vote { actor, option } => replay.vote(actor, *option),
                EncounterCommand::Resolve { actor } => replay.resolve(actor),
                EncounterCommand::Contribute { actor, role } => replay.contribute(actor, *role),
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
        expected_revision: u64,
        expected_root: [u8; 32],
    ) -> Result<Self, EncounterError> {
        let replay = Self::resume(record)?;
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
            Role::Scout if hp > FINISH_THRESHOLD && hp <= ATTACK_DIE => {
                Err(EncounterError::UnsafeStrike {
                    target,
                    hp,
                    die: ATTACK_DIE,
                })
            }
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
