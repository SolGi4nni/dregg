//! # `PartyOffering` — live formation into a capability-seated co-op game.
//!
//! A shared table now begins as an actual lobby instead of four server-named
//! demo seats. Authenticated frontend identities claim Tank/Scout/Mage/Healer,
//! explicitly ready, and the first claimant (the leader) launches only when the
//! full roster is ready. Launch consumes that actual capability-seated party into
//! [`dreggnet_party::encounter::PartyArenaEncounter`]. There is no parallel
//! "demo party": target ballots, role contributions, and enemy turns all advance
//! the real party, collective-choice, and tactical-Arena executors.
//!
//! Formation is not off-ledger UI state. Every admitted lobby mutation advances
//! a dedicated audit cell whose `FieldDelta(+1)` revision and full 256-bit lobby
//! root are committed by the real executor. Refusals mutate neither lobby nor
//! audit world. After launch, each role action returns the tactical executor's
//! complete receipt while the encounter journal binds it together with the
//! party authorization receipt. Repeated role actions hit the party cell's
//! executor-enforced `WriteOnce` predicate.
//!
//! Target selection is individual hosted play too: each seated identity casts
//! its own custody-signed Warden/Hound ballot, then the leader resolves the real
//! quorum result before the fight begins. Enemy turns are explicit leader moves,
//! not side effects of render. This matters operationally: the shared
//! [`dreggnet_offerings::OfferingHost`] move log records and resumes each claim,
//! ready, ballot, resolve, and role move without needing a synthetic crowd blob.

use deos_view::ViewNode;
use dregg_app_framework::{CellProgram, StateConstraint, TurnReceipt, field_from_u64};
use dreggnet_offerings::{
    Action, CollectiveDecision, DreggIdentity, Offering, OfferingError, Outcome, RunCost,
    SessionConfig, Surface, VerifyReport,
};
use dreggnet_party::encounter::{EncounterCommand, PartyArenaEncounter};
use dreggnet_party::lobby::{LobbyRefusal, PartyLobby};
use dreggnet_party::{FOCUS_BUDGET, ROLE_SLOT, Role};
use dungeon_on_dregg::combat::{
    CLERIC, HOUND, N, Outcome as ArenaOutcome, RANGER, WARDEN, is_hero, name as combatant_name,
};
use starbridge_v2::world::{CommitOutcome, World, set_field};

use crate::{action_menu, menu, pill, row, section, text};

/// Claim one role (`arg = Role::index()`).
pub const TURN_CLAIM: &str = "claim-role";
/// Mark the caller's occupied role ready.
pub const TURN_READY: &str = "ready";
/// Withdraw the caller's readiness without leaving their role.
pub const TURN_UNREADY: &str = "unready";
/// Vacate the caller's role before launch.
pub const TURN_LEAVE: &str = "leave-party";
/// Leader-only lock of a full ready roster into the real party world.
pub const TURN_LAUNCH: &str = "launch-party";
/// Contribute the authenticated caller's own role tactic. `arg` is ignored for authority.
pub const TURN_ACT: &str = "act";
/// Adversarial probe: attempt a move outside the caller's claimed role.
pub const TURN_MISPLAY: &str = "misplay";
/// Cast the caller's own custody-signed target ballot (`arg = 0` Warden, `1` Hound).
pub const TURN_FORK: &str = "fork";
/// Leader-only resolution once the real ballot engine reaches quorum.
pub const TURN_RESOLVE_FORK: &str = "resolve-fork";
/// Leader-only explicit tactical turn for the currently active enemy.
pub const TURN_ADVANCE_ENEMY: &str = "advance-enemy";

const LOBBY_REVISION_SLOT: usize = 0;
const LOBBY_ROOT_BASE: usize = 1;

fn fork_options() -> Vec<(String, u64)> {
    vec![
        ("Break the Warden".to_string(), WARDEN as u64),
        ("Silence the Hound".to_string(), HOUND as u64),
    ]
}

#[derive(Clone)]
struct HostedStep {
    input: Action,
    actor: DreggIdentity,
}

/// One live shared party table: formation lobby + its executor audit cell,
/// followed by the launched party's real collective tactical encounter.
pub struct PartySession {
    seed: u64,
    lobby_session_id: String,
    lobby: Option<PartyLobby>,
    lobby_world: World,
    lobby_agent: dregg_app_framework::CellId,
    lobby_cell: dregg_app_framework::CellId,
    encounter: Option<PartyArenaEncounter>,
    turns: usize,
    history: Vec<HostedStep>,
}

impl PartySession {
    /// Occupied roles (during formation) or fixed seat count (after launch).
    pub fn seat_count(&self) -> usize {
        self.encounter
            .as_ref()
            .map(|encounter| encounter.party().seat_count())
            .or_else(|| self.lobby.as_ref().map(PartyLobby::occupied_count))
            .unwrap_or(0)
    }

    /// Fork quorum (three of four for this role kit).
    pub fn quorum(&self) -> u64 {
        self.encounter
            .as_ref()
            .map(|encounter| encounter.party().quorum())
            .unwrap_or(3)
    }

    /// Total shared focus spent after launch.
    pub fn focus_spent(&self) -> u64 {
        self.encounter
            .as_ref()
            .map(|encounter| encounter.party().focus_spent())
            .unwrap_or(0)
    }

    /// Number of committed formation, ballot, resolution, and role turns.
    pub fn turns(&self) -> usize {
        self.turns
    }

    /// Whether the lobby has locked into the real party world.
    pub fn launched(&self) -> bool {
        self.encounter.is_some()
    }

    /// First claimant and launch authority, if formation has begun.
    pub fn leader(&self) -> Option<&str> {
        self.lobby.as_ref().map(PartyLobby::leader)
    }

    /// Lobby journal revision (also the committed audit-cell revision).
    pub fn lobby_revision(&self) -> u64 {
        self.lobby.as_ref().map(PartyLobby::revision).unwrap_or(0)
    }

    /// Role held by an identity, if any.
    pub fn role_of(&self, identity: &str) -> Option<Role> {
        Role::ALL.into_iter().find(|role| {
            self.lobby
                .as_ref()
                .and_then(|lobby| lobby.seat(*role))
                .is_some_and(|seat| seat.identity() == identity)
        })
    }

    /// Quorum-selected enemy label.
    pub fn last_fork(&self) -> Option<&str> {
        match self.encounter.as_ref()?.target()? {
            WARDEN => Some("Warden"),
            HOUND => Some("Hound"),
            _ => None,
        }
    }

    /// Quorum-selected enemy id.
    pub fn target(&self) -> Option<u8> {
        self.encounter
            .as_ref()
            .and_then(PartyArenaEncounter::target)
    }

    /// Number of replay-bound tactical events after launch.
    pub fn encounter_revision(&self) -> u64 {
        self.encounter
            .as_ref()
            .map(PartyArenaEncounter::revision)
            .unwrap_or(0)
    }

    /// Current tactical combatant id.
    pub fn arena_active(&self) -> Option<u8> {
        self.encounter
            .as_ref()
            .map(|encounter| encounter.arena().active())
    }

    /// Current HP for one of the four tactical combatants.
    pub fn arena_hp(&self, combatant: u8) -> Option<u64> {
        if combatant >= N {
            return None;
        }
        Some(self.encounter.as_ref()?.arena().hp(combatant))
    }

    /// Current mechanically derived Arena result.
    pub fn arena_outcome(&self) -> Option<ArenaOutcome> {
        self.encounter
            .as_ref()
            .map(|encounter| encounter.arena().outcome())
    }

    fn seat_acted(&self, idx: usize) -> bool {
        let Some(party) = self.encounter.as_ref().map(PartyArenaEncounter::party) else {
            return false;
        };
        if idx >= party.seat_count() {
            return false;
        }
        let layout = party.layout();
        let cell = match party.seat(idx).role() {
            Role::Tank => layout.front,
            Role::Scout => layout.lock,
            Role::Mage => layout.ward,
            Role::Healer => layout.rally,
        };
        party.read_field(cell, ROLE_SLOT) != 0
    }

    fn actor_acted(&self, actor: &DreggIdentity) -> bool {
        self.encounter
            .as_ref()
            .and_then(|encounter| encounter.party().seat_index_for(actor.as_str()))
            .is_some_and(|idx| self.seat_acted(idx))
    }

    fn fork_tally(&self) -> Option<Vec<u64>> {
        let encounter = self.encounter.as_ref()?;
        if encounter.target().is_some() {
            return None;
        }
        let mut counts = vec![0, 0];
        for event in encounter.events() {
            if let EncounterCommand::Vote { option, .. } = &event.command {
                if let Some(count) = counts.get_mut(*option) {
                    *count += 1;
                }
            }
        }
        Some(counts)
    }

    fn fork_total(&self) -> u64 {
        self.fork_tally()
            .map(|counts| counts.into_iter().sum())
            .unwrap_or(0)
    }

    fn has_voted(&self, actor: &str) -> bool {
        self.encounter.as_ref().is_some_and(|encounter| {
            encounter.events().iter().any(|event| {
                matches!(&event.command, EncounterCommand::Vote { actor: voter, .. } if voter == actor)
            })
        })
    }
}

/// Frontend-neutral factory for the hosted party table.
pub struct PartyOffering;

impl PartyOffering {
    /// A fresh hosted party offering.
    pub fn new() -> Self {
        Self
    }

    fn open_seed(seed: u64) -> Result<PartySession, OfferingError> {
        let mut lobby_world = World::new();
        let lobby_cell = lobby_world.genesis_cell(0xE1, 0);
        let installed = lobby_world.set_cell_program(
            &lobby_cell,
            CellProgram::Predicate(vec![StateConstraint::FieldDelta {
                index: LOBBY_REVISION_SLOT as u8,
                delta: field_from_u64(1),
            }]),
        );
        if !installed {
            return Err(OfferingError::Deploy(
                "could not install the party-lobby audit program".to_string(),
            ));
        }
        let (lobby_agent, _) = lobby_world.genesis_cell_with_cap(0xE2, 0, lobby_cell);
        Ok(PartySession {
            seed,
            lobby_session_id: format!("party:{seed:016x}"),
            lobby: None,
            lobby_world,
            lobby_agent,
            lobby_cell,
            encounter: None,
            turns: 0,
            history: Vec::new(),
        })
    }

    fn commit_lobby_checkpoint(
        session: &mut PartySession,
        next: &PartyLobby,
    ) -> Result<TurnReceipt, String> {
        let mut effects = vec![set_field(
            session.lobby_cell,
            LOBBY_REVISION_SLOT,
            field_from_u64(next.revision()),
        )];
        for (i, chunk) in next.root().chunks_exact(8).enumerate() {
            let limb = u64::from_le_bytes(chunk.try_into().expect("eight-byte root limb"));
            effects.push(set_field(
                session.lobby_cell,
                LOBBY_ROOT_BASE + i,
                field_from_u64(limb),
            ));
        }
        let turn = session.lobby_world.turn(session.lobby_agent, effects);
        match session.lobby_world.commit_turn(turn) {
            CommitOutcome::Committed { receipt, .. } => Ok(*receipt),
            CommitOutcome::Rejected { reason, .. } => {
                Err(format!("party-lobby audit cell refused: {reason}"))
            }
            CommitOutcome::Queued { .. } => Err("party-lobby audit world is suspended".to_string()),
        }
    }

    fn land_lobby(session: &mut PartySession, next: PartyLobby) -> Result<TurnReceipt, String> {
        // The next lobby is a clone/shadow. Only install it after the real audit
        // turn commits, so an executor refusal leaves the live lobby untouched.
        let receipt = Self::commit_lobby_checkpoint(session, &next)?;
        session.lobby = Some(next);
        Ok(receipt)
    }

    fn lobby_refusal(error: LobbyRefusal) -> Outcome {
        Outcome::Refused(error.to_string())
    }

    fn do_claim(session: &mut PartySession, actor: &DreggIdentity, arg: i64) -> Outcome {
        let Some(role) = role_from_arg(arg) else {
            return Outcome::Refused("no such party role".to_string());
        };
        let mut next = match session.lobby.as_ref() {
            Some(lobby) => lobby.clone(),
            None => match PartyLobby::new(&session.lobby_session_id, actor.as_str()) {
                Ok(lobby) => lobby,
                Err(error) => return Self::lobby_refusal(error),
            },
        };
        if let Err(error) = next.claim(actor.as_str(), role) {
            return Self::lobby_refusal(error);
        }
        match Self::land_lobby(session, next) {
            Ok(receipt) => landed(session, receipt),
            Err(reason) => Outcome::Refused(reason),
        }
    }

    fn do_ready(session: &mut PartySession, actor: &DreggIdentity, ready: bool) -> Outcome {
        let Some(mut next) = session.lobby.clone() else {
            return Outcome::Refused("claim a role before readying".to_string());
        };
        if let Err(error) = next.set_ready(actor.as_str(), ready) {
            return Self::lobby_refusal(error);
        }
        match Self::land_lobby(session, next) {
            Ok(receipt) => landed(session, receipt),
            Err(reason) => Outcome::Refused(reason),
        }
    }

    fn do_leave(session: &mut PartySession, actor: &DreggIdentity) -> Outcome {
        let Some(mut next) = session.lobby.clone() else {
            return Outcome::Refused("identity does not occupy a role".to_string());
        };
        if let Err(error) = next.leave(actor.as_str()) {
            return Self::lobby_refusal(error);
        }
        match Self::land_lobby(session, next) {
            Ok(receipt) => landed(session, receipt),
            Err(reason) => Outcome::Refused(reason),
        }
    }

    fn do_launch(session: &mut PartySession, actor: &DreggIdentity) -> Outcome {
        if session.encounter.is_some() {
            return Outcome::Refused("party already launched".to_string());
        }
        let Some(mut next) = session.lobby.clone() else {
            return Outcome::Refused("the party roster is empty".to_string());
        };
        let launch = match next.launch(actor.as_str()) {
            Ok(launch) => launch,
            Err(error) => return Self::lobby_refusal(error),
        };
        // Consume the exact Party produced by the live lobby. Construct the
        // tactical bridge before locking either hosted state so a malformed
        // launch cannot strand the lobby in a half-launched phase.
        let encounter = match PartyArenaEncounter::from_party(
            launch.party,
            actor.as_str(),
            arena_seed(session.seed),
        ) {
            Ok(encounter) => encounter,
            Err(error) => {
                return Outcome::Refused(format!("the party could not enter the Arena: {error}"));
            }
        };
        let receipt = match Self::commit_lobby_checkpoint(session, &next) {
            Ok(receipt) => receipt,
            Err(reason) => return Outcome::Refused(reason),
        };
        session.lobby = Some(next);
        session.encounter = Some(encounter);
        landed(session, receipt)
    }

    fn land_encounter_event(
        session: &mut PartySession,
        receipt: Option<TurnReceipt>,
        kind: &str,
    ) -> Outcome {
        match receipt {
            Some(receipt) if receipt.turn_hash != [0u8; 32] => landed(session, receipt),
            _ => Outcome::Refused(format!(
                "{kind} committed but its complete executor receipt was unavailable"
            )),
        }
    }

    fn do_act(session: &mut PartySession, actor: &DreggIdentity) -> Outcome {
        if session.actor_acted(actor) {
            return Outcome::Refused("this role already contributed to the encounter".to_string());
        }
        let Some(role) = session.role_of(actor.as_str()) else {
            return Outcome::Refused("identity holds no party seat".to_string());
        };
        let Some(encounter) = session.encounter.as_mut() else {
            return Outcome::Refused("the roster has not launched".to_string());
        };
        let receipt = match encounter.contribute(actor.as_str(), role) {
            Ok(event) => event.arena_receipt.clone(),
            Err(error) => return Outcome::Refused(error.to_string()),
        };
        Self::land_encounter_event(session, receipt, "role contribution")
    }

    fn do_misplay(session: &mut PartySession, actor: &DreggIdentity) -> Outcome {
        let Some(held) = session.role_of(actor.as_str()) else {
            return Outcome::Refused("identity holds no party seat".to_string());
        };
        let wrong = if held == Role::Tank {
            Role::Scout
        } else {
            Role::Tank
        };
        let Some(encounter) = session.encounter.as_mut() else {
            return Outcome::Refused("the roster has not launched".to_string());
        };
        match encounter.contribute(actor.as_str(), wrong) {
            Ok(_) => Outcome::Refused(
                "cross-role contribution unexpectedly passed the party capability".to_string(),
            ),
            Err(error) => Outcome::Refused(error.to_string()),
        }
    }

    fn do_fork_vote(session: &mut PartySession, actor: &DreggIdentity, arg: i64) -> Outcome {
        if arg < 0 || arg as usize >= fork_options().len() {
            return Outcome::Refused("no such enemy target".to_string());
        }
        let option = arg as usize;
        let Some(encounter) = session.encounter.as_mut() else {
            return Outcome::Refused("the roster has not launched".to_string());
        };
        let receipt = match encounter.vote(actor.as_str(), option) {
            Ok(event) => event.vote_receipt.clone(),
            Err(error) => return Outcome::Refused(error.to_string()),
        };
        match receipt {
            Some(receipt) => landed(session, receipt),
            None => Outcome::Refused(
                "target ballot committed without its vote-engine receipt".to_string(),
            ),
        }
    }

    fn do_resolve_fork(session: &mut PartySession, actor: &DreggIdentity) -> Outcome {
        if session.leader() != Some(actor.as_str()) {
            return Outcome::Refused("only the party leader can resolve the fork".to_string());
        }
        let Some(encounter) = session.encounter.as_mut() else {
            return Outcome::Refused("the roster has not launched".to_string());
        };
        let receipt = match encounter.resolve(actor.as_str()) {
            Ok(event) => event.party_receipt.clone(),
            Err(error) => return Outcome::Refused(error.to_string()),
        };
        match receipt {
            Some(receipt) => landed(session, receipt),
            None => {
                Outcome::Refused("target resolved without its complete party receipt".to_string())
            }
        }
    }

    fn do_advance_enemy(session: &mut PartySession, actor: &DreggIdentity) -> Outcome {
        let Some(encounter) = session.encounter.as_mut() else {
            return Outcome::Refused("the roster has not launched".to_string());
        };
        let receipt = match encounter.advance_enemy(actor.as_str()) {
            Ok(event) => event.arena_receipt.clone(),
            Err(error) => return Outcome::Refused(error.to_string()),
        };
        match receipt {
            Some(receipt) => landed(session, receipt),
            None => Outcome::Refused("enemy advanced without its Arena receipt".to_string()),
        }
    }

    fn apply_solo(
        &self,
        session: &mut PartySession,
        input: Action,
        actor: DreggIdentity,
    ) -> Outcome {
        match input.turn.as_str() {
            TURN_CLAIM => Self::do_claim(session, &actor, input.arg),
            TURN_READY => Self::do_ready(session, &actor, true),
            TURN_UNREADY => Self::do_ready(session, &actor, false),
            TURN_LEAVE => Self::do_leave(session, &actor),
            TURN_LAUNCH => Self::do_launch(session, &actor),
            TURN_ACT => Self::do_act(session, &actor),
            TURN_MISPLAY => Self::do_misplay(session, &actor),
            TURN_FORK => Self::do_fork_vote(session, &actor, input.arg),
            TURN_RESOLVE_FORK => Self::do_resolve_fork(session, &actor),
            TURN_ADVANCE_ENEMY => Self::do_advance_enemy(session, &actor),
            other => Outcome::Refused(format!("unknown party affordance: {other}")),
        }
    }

    fn public_actions(&self, session: &PartySession) -> Vec<Action> {
        if !session.launched() {
            let mut out = open_role_actions(session);
            if session.lobby.is_some() {
                out.push(Action::new("Ready my role", TURN_READY, 0, true));
                out.push(Action::new("Unready my role", TURN_UNREADY, 0, true));
                out.push(Action::new("Leave my role", TURN_LEAVE, 0, true));
                out.push(Action::new(
                    "Launch the ready party",
                    TURN_LAUNCH,
                    0,
                    session
                        .lobby
                        .as_ref()
                        .is_some_and(PartyLobby::ready_to_launch),
                ));
            }
            return out;
        }

        if session.target().is_none() {
            let mut out = Vec::new();
            for (i, (label, _)) in fork_options().into_iter().enumerate() {
                out.push(Action::new(
                    format!("Target: {label}"),
                    TURN_FORK,
                    i as i64,
                    true,
                ));
            }
            out.push(Action::new(
                "Leader resolves the target",
                TURN_RESOLVE_FORK,
                0,
                session.fork_total() >= session.quorum(),
            ));
            return out;
        }
        let active = session.arena_active();
        vec![
            Action::new(
                "Contribute my role tactic",
                TURN_ACT,
                0,
                active.is_some_and(is_hero),
            ),
            Action::new(
                "Leader advances the enemy",
                TURN_ADVANCE_ENEMY,
                0,
                active.is_some_and(|combatant| !is_hero(combatant)),
            ),
        ]
    }

    fn viewer_actions(&self, session: &PartySession, viewer: &DreggIdentity) -> Vec<Action> {
        if !session.launched() {
            let Some(lobby) = session.lobby.as_ref() else {
                return open_role_actions(session);
            };
            let Some(role) = session.role_of(viewer.as_str()) else {
                return open_role_actions(session);
            };
            let ready = lobby.seat(role).is_some_and(|seat| seat.ready());
            let mut out = vec![if ready {
                Action::new("Unready my role", TURN_UNREADY, 0, true)
            } else {
                Action::new("Ready my role", TURN_READY, 0, true)
            }];
            out.push(Action::new("Leave my role", TURN_LEAVE, 0, true));
            if lobby.leader() == viewer.as_str() {
                out.push(Action::new(
                    "Launch the ready party",
                    TURN_LAUNCH,
                    0,
                    lobby.ready_to_launch(),
                ));
            }
            return out;
        }

        let Some(party) = session.encounter.as_ref().map(PartyArenaEncounter::party) else {
            return Vec::new();
        };
        let Some(seat_idx) = party.seat_index_for(viewer.as_str()) else {
            return Vec::new();
        };
        if session.target().is_none() {
            let mut out = Vec::new();
            if !session.has_voted(viewer.as_str()) {
                for (i, (label, _)) in fork_options().into_iter().enumerate() {
                    out.push(Action::new(
                        format!("Target: {label}"),
                        TURN_FORK,
                        i as i64,
                        true,
                    ));
                }
            }
            if session.leader() == Some(viewer.as_str()) {
                out.push(Action::new(
                    "Resolve the target",
                    TURN_RESOLVE_FORK,
                    0,
                    session.fork_total() >= session.quorum(),
                ));
            }
            return out;
        }

        let active = session.arena_active();
        let mut out = Vec::new();
        if active.is_some_and(is_hero) {
            out.push(Action::new(
                format!("Contribute {} tactic", party.seat(seat_idx).role().name()),
                TURN_ACT,
                seat_idx as i64,
                !session.seat_acted(seat_idx),
            ));
        }
        if session.leader() == Some(viewer.as_str())
            && active.is_some_and(|combatant| !is_hero(combatant))
        {
            out.push(Action::new(
                format!("Advance {}", active.map(combatant_name).unwrap_or("enemy")),
                TURN_ADVANCE_ENEMY,
                0,
                true,
            ));
        }
        out
    }

    fn render_with_actions(&self, session: &PartySession, actions: Vec<Action>) -> Surface {
        let phase = if session.launched() {
            "LAUNCHED"
        } else {
            "FORMING"
        };
        // THE DIRECTIVE, first — one sentence saying what this table is waiting on. Without it the
        // page opened on `FORMING 0 / 4 roles · quorum 3`, which states the position and asks for
        // nothing.
        let seats = session.seat_count();
        let quorum = session.quorum();
        let mut children = vec![section(
            "Your next move",
            "accent",
            vec![text(if session.launched() {
                "The party is LAUNCHED — the roles are locked and the fight is live. Each seat \
                     contributes ONE committed action; the roster below says who has and who has \
                     not."
                    .to_string()
            } else if seats == 0 {
                format!(
                    "Nobody has taken a seat yet — claim one of the four roles below. The \
                         table launches at a quorum of {quorum} ready seats, and every claim is a \
                         committed turn, so a seat cannot be taken twice."
                )
            } else {
                format!(
                    "{seats} of 4 roles are held and this table launches at {quorum} READY \
                         seats — claim an open role, or mark your own seat ready. A launch below \
                         quorum is refused by the lobby, not hidden by this page."
                )
            })],
        )];
        children.push(section(
            "Party table",
            "muted",
            vec![
                pill(phase, if session.launched() { "good" } else { "warn" }),
                text(format!(
                    "{} / 4 roles · quorum {} · committed turns {} · lobby revision {}",
                    session.seat_count(),
                    session.quorum(),
                    session.turns(),
                    session.lobby_revision(),
                )),
            ],
        ));

        let mut rows = vec![row(vec![text("Role"), text("Holder"), text("Status")])];
        for role in Role::ALL {
            let seat = session.lobby.as_ref().and_then(|lobby| lobby.seat(role));
            rows.push(row(vec![
                pill(role.name(), "accent"),
                text(
                    seat.map(|seat| short_identity(seat.identity()))
                        .unwrap_or_else(|| "open".to_string()),
                ),
                pill(
                    if session.launched() {
                        if session.seat_acted(role.index()) {
                            "contributed"
                        } else {
                            "ready to fight"
                        }
                    } else if seat.is_some_and(|seat| seat.ready()) {
                        "ready"
                    } else if seat.is_some() {
                        "not ready"
                    } else {
                        "open"
                    },
                    if session.launched() || seat.is_some_and(|seat| seat.ready()) {
                        "good"
                    } else {
                        "muted"
                    },
                ),
            ]));
        }
        children.push(section("Roster", "accent", vec![ViewNode::Table(rows)]));

        if session.launched() {
            if let Some(encounter) = session.encounter.as_ref() {
                let arena = encounter.arena();
                let active = arena.active();
                let (resolution, resolution_tag) = arena_resolution(arena.outcome());
                let mut tactical = vec![
                    pill(resolution, resolution_tag),
                    // "active {name}" is the wording the cross-surface web pins read
                    // (`party_cross_surface.rs`); keep it while the resolution moves to a pill
                    // and the focus pool moves to a gauge.
                    text(format!(
                        "event {} · active {}",
                        encounter.revision(),
                        combatant_name(active),
                    )),
                    // The shared focus pool is a budget, so it paints as the gauge every
                    // backend already renders rather than as "3/8" buried in a sentence.
                    ViewNode::Progress {
                        value: session.focus_spent(),
                        max: FOCUS_BUDGET,
                        label: "shared focus spent".to_string(),
                    },
                ];
                let mut combat = vec![row(vec![text("Combatant"), text("HP"), text("Condition")])];
                for combatant in [RANGER, CLERIC, WARDEN, HOUND] {
                    let condition = if arena.is_down(combatant) {
                        "down"
                    } else if arena.is_stunned(combatant) {
                        "stunned"
                    } else if arena.is_guarding(combatant) {
                        "guarding"
                    } else {
                        "standing"
                    };
                    combat.push(row(vec![
                        pill(
                            combatant_name(combatant),
                            if Some(combatant) == session.target() {
                                "warn"
                            } else {
                                "accent"
                            },
                        ),
                        text(arena.hp(combatant).to_string()),
                        pill(
                            condition,
                            if condition == "down" { "muted" } else { "good" },
                        ),
                    ]));
                }
                tactical.push(ViewNode::Table(combat));
                children.push(section("Tactical Arena", "accent", tactical));
            }
        }

        if let Some(tally) = session.fork_tally() {
            let labels = fork_options();
            let counts = tally
                .iter()
                .enumerate()
                .map(|(i, count)| {
                    text(format!(
                        "{} — {} vote(s)",
                        labels.get(i).map(|x| x.0.as_str()).unwrap_or("unknown"),
                        count
                    ))
                })
                .collect();
            children.push(section("Enemy target ballot", "warn", counts));
        }
        if let Some(fork) = session.last_fork() {
            children.push(section(
                "Resolved target",
                "genuine",
                vec![text(format!("the party concentrates on the {fork}"))],
            ));
        }

        let actions = action_menu(actions);
        if !actions.is_empty() {
            children.push(section("Actions", "accent", vec![menu(actions)]));
        }

        Surface(section(
            "DreggNet Party — muster, choose, fight",
            "accent",
            children,
        ))
    }

    fn audit_matches(session: &PartySession) -> bool {
        let Some(cell) = session.lobby_world.ledger().get(&session.lobby_cell) else {
            return false;
        };
        let expected_revision = session.lobby_revision();
        if field_to_u64(&cell.state.fields[LOBBY_REVISION_SLOT]) != expected_revision {
            return false;
        }
        let expected_root = session
            .lobby
            .as_ref()
            .map(PartyLobby::root)
            .unwrap_or([0u8; 32]);
        for (i, chunk) in expected_root.chunks_exact(8).enumerate() {
            let expected = u64::from_le_bytes(chunk.try_into().expect("eight-byte root limb"));
            if field_to_u64(&cell.state.fields[LOBBY_ROOT_BASE + i]) != expected {
                return false;
            }
        }
        true
    }

    fn encounter_semantics_match(left: &PartySession, right: &PartySession) -> bool {
        match (&left.encounter, &right.encounter) {
            (None, None) => true,
            (Some(left), Some(right)) => {
                left.target() == right.target()
                    && left.revision() == right.revision()
                    && left
                        .events()
                        .iter()
                        .map(|event| &event.command)
                        .eq(right.events().iter().map(|event| &event.command))
                    && left.arena().active() == right.arena().active()
                    && left.arena().outcome() == right.arena().outcome()
                    && left.arena().world.snapshot() == right.arena().world.snapshot()
                    && left.party().focus_spent() == right.party().focus_spent()
                    && (0..left.party().seat_count()).all(|idx| {
                        left.party().seat(idx).name() == right.party().seat(idx).name()
                            && left.party().seat(idx).role() == right.party().seat(idx).role()
                            && left.party().loot_share(idx) == right.party().loot_share(idx)
                    })
                    && Role::ALL.into_iter().all(|role| {
                        let left_layout = left.party().layout();
                        let right_layout = right.party().layout();
                        let (left_cell, right_cell) = match role {
                            Role::Tank => (left_layout.front, right_layout.front),
                            Role::Scout => (left_layout.lock, right_layout.lock),
                            Role::Mage => (left_layout.ward, right_layout.ward),
                            Role::Healer => (left_layout.rally, right_layout.rally),
                        };
                        left.party().read_field(left_cell, ROLE_SLOT)
                            == right.party().read_field(right_cell, ROLE_SLOT)
                    })
            }
            _ => false,
        }
    }
}

impl Default for PartyOffering {
    fn default() -> Self {
        Self::new()
    }
}

impl Offering for PartyOffering {
    type Session = PartySession;

    fn open(&self, cfg: SessionConfig) -> Result<PartySession, OfferingError> {
        Self::open_seed(cfg.seed.unwrap_or(1))
    }

    fn actions(&self, session: &PartySession) -> Vec<Action> {
        self.public_actions(session)
    }

    fn actions_for(&self, session: &PartySession, viewer: &DreggIdentity) -> Vec<Action> {
        self.viewer_actions(session, viewer)
    }

    fn advance(&self, session: &mut PartySession, input: Action, actor: DreggIdentity) -> Outcome {
        let step = HostedStep {
            input: input.clone(),
            actor: actor.clone(),
        };
        let outcome = self.apply_solo(session, input, actor);
        if outcome.landed() {
            session.history.push(step);
        }
        outcome
    }

    fn advance_collective(
        &self,
        session: &mut PartySession,
        input: Action,
        decision: CollectiveDecision,
    ) -> Outcome {
        if input.turn == TURN_FORK {
            return Outcome::Refused(
                "forks use one custody-signed, resumable ballot turn per seated identity"
                    .to_string(),
            );
        }
        self.advance(session, input, decision.carrier)
    }

    fn verify(&self, session: &PartySession) -> VerifyReport {
        if let Some(lobby) = session.lobby.as_ref() {
            let report = lobby.verify();
            if !report.verified {
                return VerifyReport::broken(session.turns, report.detail);
            }
        }
        if !Self::audit_matches(session) {
            return VerifyReport::broken(
                session.turns,
                "lobby journal diverges from its committed audit cell",
            );
        }
        if session.lobby.as_ref().is_some_and(PartyLobby::launched) != session.encounter.is_some() {
            return VerifyReport::broken(
                session.turns,
                "lobby launch state diverges from the party-Arena encounter",
            );
        }
        if let Some(encounter) = session.encounter.as_ref() {
            let party = encounter.party();
            for seat in party.seats() {
                if party.world().ledger().get(&seat.cell()).is_none() {
                    return VerifyReport::broken(
                        session.turns,
                        format!("seat `{}` has no cell in the shared world", seat.name()),
                    );
                }
            }
            let record = encounter.export_record();
            // The record carries no secret, so replaying it needs the encounter's own private
            // custody root (the seats are re-derived under it and the ballots re-signed). A
            // remote-custody party holds none and cannot be replayed this way — say so rather
            // than silently skipping the check.
            let Some(custody_root) = encounter.custody_root() else {
                return VerifyReport::broken(
                    session.turns,
                    "party-Arena encounter holds no custody root, so its record cannot be replayed",
                );
            };
            if let Err(error) = PartyArenaEncounter::resume_at(
                &record,
                custody_root,
                encounter.revision(),
                encounter.root(),
            ) {
                return VerifyReport::broken(
                    session.turns,
                    format!("party-Arena encounter record did not replay: {error}"),
                );
            }
        }

        // Re-drive only successful frontend actions from the deterministic seed.
        // Each live commit already re-executes inside its World; this second layer
        // proves the hosted state is exactly the semantic move-log's result.
        let mut replay = match Self::open_seed(session.seed) {
            Ok(replay) => replay,
            Err(error) => return VerifyReport::broken(0, error.to_string()),
        };
        for (idx, step) in session.history.iter().enumerate() {
            let outcome = self.apply_solo(&mut replay, step.input.clone(), step.actor.clone());
            if !outcome.landed() {
                // `VerifyReport::detail` is painted into the page, so give the executor's own
                // refusal reason rather than a `Debug` dump of the whole `Outcome`.
                let why = match &outcome {
                    Outcome::Refused(reason) => reason.as_str(),
                    Outcome::Landed { .. } => "the replay landed after all",
                };
                return VerifyReport::broken(
                    idx,
                    format!(
                        "hosted party replay refused at step {idx} ({}): {why}",
                        step.input.turn
                    ),
                );
            }
        }
        let replay_lobby = replay
            .lobby
            .as_ref()
            .map(|lobby| (lobby.revision(), lobby.root(), lobby.launched()));
        let live_lobby = session
            .lobby
            .as_ref()
            .map(|lobby| (lobby.revision(), lobby.root(), lobby.launched()));
        // Compare the committed audit cell through `audit_matches` plus the
        // semantic lobby record above. The whole World root includes
        // process-local cell identities, so it is deliberately not a portable
        // restart commitment once the party and Arena allocate other worlds.
        let divergence = if replay_lobby != live_lobby {
            Some("lobby semantic state")
        } else if replay.turns != session.turns {
            Some("hosted turn count")
        } else if !Self::encounter_semantics_match(&replay, session) {
            Some("party-Arena semantic state")
        } else {
            None
        };
        if let Some(divergence) = divergence {
            return VerifyReport::broken(
                session.turns,
                format!("hosted party replay changed {divergence}"),
            );
        }
        VerifyReport::ok(session.turns)
    }

    fn render(&self, session: &PartySession) -> Surface {
        self.render_with_actions(session, self.actions(session))
    }

    fn render_for(&self, session: &PartySession, viewer: &DreggIdentity) -> Surface {
        self.render_with_actions(session, self.actions_for(session, viewer))
    }

    fn price(&self, _input: &Action) -> RunCost {
        RunCost::free()
    }
}

fn role_from_arg(arg: i64) -> Option<Role> {
    usize::try_from(arg)
        .ok()
        .and_then(|idx| Role::ALL.get(idx).copied())
}

fn arena_seed(seed: u64) -> u8 {
    seed.to_le_bytes().into_iter().fold(0u8, u8::wrapping_add)
}

/// The fight's resolution as a player-readable pill instead of a `Debug` variant name.
///
/// `{:?}` on [`ArenaOutcome`] painted the bare Rust identifier (`Ongoing`) into the page,
/// which reads as a debug view and says nothing a player recognises.
fn arena_resolution(outcome: ArenaOutcome) -> (&'static str, &'static str) {
    match outcome {
        ArenaOutcome::Ongoing => ("THE FIGHT IS LIVE", "warn"),
        ArenaOutcome::Victory => ("VICTORY — EVERY ENEMY IS DOWN", "good"),
        ArenaOutcome::Defeat => ("DEFEAT — EVERY HERO IS DOWN", "bad"),
    }
}

fn open_role_actions(session: &PartySession) -> Vec<Action> {
    Role::ALL
        .into_iter()
        .filter(|role| {
            session
                .lobby
                .as_ref()
                .and_then(|lobby| lobby.seat(*role))
                .is_none()
        })
        .map(|role| {
            Action::new(
                format!("Claim {}", role.name()),
                TURN_CLAIM,
                role.index() as i64,
                true,
            )
        })
        .collect()
}

fn landed(session: &mut PartySession, receipt: TurnReceipt) -> Outcome {
    session.turns += 1;
    Outcome::Landed {
        receipt,
        ended: false,
    }
}

fn short_identity(identity: &str) -> String {
    if identity.chars().count() <= 16 {
        return identity.to_string();
    }
    format!("{}…", identity.chars().take(15).collect::<String>())
}

fn field_to_u64(field: &dregg_app_framework::FieldElement) -> u64 {
    let mut bytes = [0u8; 8];
    bytes.copy_from_slice(&field[24..32]);
    u64::from_be_bytes(bytes)
}
