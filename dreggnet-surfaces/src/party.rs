//! # `PartyOffering` — live formation into a capability-seated co-op game.
//!
//! A shared table now begins as an actual lobby instead of four server-named
//! demo seats. Authenticated frontend identities claim Tank/Scout/Mage/Healer,
//! explicitly ready, and the first claimant (the leader) launches only when the
//! full roster is ready. Launch lowers that roster into [`dreggnet_party::Party`]:
//! each identity reaches only its own capability-bearing player cell.
//!
//! Formation is not off-ledger UI state. Every admitted lobby mutation advances
//! a dedicated audit cell whose `FieldDelta(+1)` revision and full 256-bit lobby
//! root are committed by the real executor. Refusals mutate neither lobby nor
//! audit world. After launch, role actions return the complete real party-world
//! receipt; repeated role actions hit the role cell's executor-enforced
//! `WriteOnce` predicate.
//!
//! Forks are individual hosted turns too: each seated identity casts its own
//! custody-signed ballot as an ordinary `fork` action, then the leader resolves
//! the real quorum result. This matters operationally: the shared
//! [`dreggnet_offerings::OfferingHost`] move log records and resumes each claim,
//! ready, ballot, resolve, and role move without needing a synthetic crowd blob.

use std::collections::BTreeMap;

use deos_view::ViewNode;
use dregg_app_framework::{CellProgram, StateConstraint, TurnReceipt, field_from_u64};
use dreggnet_offerings::{
    Action, CollectiveDecision, DreggIdentity, Offering, OfferingError, Outcome, RunCost,
    SessionConfig, Surface, VerifyReport,
};
use dreggnet_party::lobby::{LobbyRefusal, PartyLobby};
use dreggnet_party::{ActOutcome, FOCUS_BUDGET, Party, PartyFork, PartyMove, ROLE_SLOT, Role};
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
/// Act in the authenticated caller's own role. `arg` is ignored for authority.
pub const TURN_ACT: &str = "act";
/// Adversarial probe: attempt a move outside the caller's claimed role.
pub const TURN_MISPLAY: &str = "misplay";
/// Cast the caller's own custody-signed fork ballot (`arg = option`).
pub const TURN_FORK: &str = "fork";
/// Leader-only resolution once the real ballot engine reaches quorum.
pub const TURN_RESOLVE_FORK: &str = "resolve-fork";

const LOBBY_REVISION_SLOT: usize = 0;
const LOBBY_ROOT_BASE: usize = 1;

fn fork_options() -> Vec<(String, u64)> {
    vec![
        ("Left, the sunken stair".to_string(), 1),
        ("Right, the warded arch".to_string(), 2),
    ]
}

#[derive(Clone)]
struct HostedStep {
    input: Action,
    actor: DreggIdentity,
}

/// One live shared party table: formation lobby + its executor audit cell,
/// followed by the launched party and (optionally) an open signed fork ballot.
pub struct PartySession {
    seed: u64,
    lobby_session_id: String,
    lobby: Option<PartyLobby>,
    lobby_world: World,
    lobby_agent: dregg_app_framework::CellId,
    lobby_cell: dregg_app_framework::CellId,
    party: Option<Party>,
    current_fork: Option<PartyFork>,
    fork_votes: BTreeMap<String, usize>,
    turns: usize,
    last_fork: Option<String>,
    history: Vec<HostedStep>,
}

impl PartySession {
    /// Occupied roles (during formation) or fixed seat count (after launch).
    pub fn seat_count(&self) -> usize {
        self.party
            .as_ref()
            .map(Party::seat_count)
            .or_else(|| self.lobby.as_ref().map(PartyLobby::occupied_count))
            .unwrap_or(0)
    }

    /// Fork quorum (three of four for this role kit).
    pub fn quorum(&self) -> u64 {
        self.party.as_ref().map(Party::quorum).unwrap_or(3)
    }

    /// Total shared focus spent after launch.
    pub fn focus_spent(&self) -> u64 {
        self.party.as_ref().map(Party::focus_spent).unwrap_or(0)
    }

    /// Number of committed formation, ballot, resolution, and role turns.
    pub fn turns(&self) -> usize {
        self.turns
    }

    /// Whether the lobby has locked into the real party world.
    pub fn launched(&self) -> bool {
        self.party.is_some()
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

    /// Last resolved fork label.
    pub fn last_fork(&self) -> Option<&str> {
        self.last_fork.as_deref()
    }

    fn seat_acted(&self, idx: usize) -> bool {
        let Some(party) = self.party.as_ref() else {
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
        self.party
            .as_ref()
            .and_then(|party| party.seat_index_for(actor.as_str()))
            .is_some_and(|idx| self.seat_acted(idx))
    }

    fn fork_tally(&self) -> Option<Vec<u64>> {
        self.current_fork
            .as_ref()?
            .tally()
            .ok()
            .map(|tally| tally.per_option)
    }

    fn fork_total(&self) -> u64 {
        self.fork_tally()
            .map(|counts| counts.into_iter().sum())
            .unwrap_or(0)
    }

    fn party_root(&self) -> Option<[u8; 32]> {
        self.party.as_ref().map(|party| party.world().state_root())
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
            party: None,
            current_fork: None,
            fork_votes: BTreeMap::new(),
            turns: 0,
            last_fork: None,
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
        if session.party.is_some() {
            return Outcome::Refused("party already launched".to_string());
        }
        let Some(mut next) = session.lobby.clone() else {
            return Outcome::Refused("the party roster is empty".to_string());
        };
        let launch = match next.launch(actor.as_str()) {
            Ok(launch) => launch,
            Err(error) => return Self::lobby_refusal(error),
        };
        let receipt = match Self::commit_lobby_checkpoint(session, &next) {
            Ok(receipt) => receipt,
            Err(reason) => return Outcome::Refused(reason),
        };
        session.lobby = Some(next);
        session.party = Some(launch.party);
        landed(session, receipt)
    }

    fn fold_party_act(session: &mut PartySession, outcome: ActOutcome) -> Outcome {
        match outcome {
            ActOutcome::Refused { reason } => Outcome::Refused(reason),
            ActOutcome::Committed { receipt: expected } => {
                let receipt = session
                    .party
                    .as_ref()
                    .and_then(|party| party.world().receipts().last())
                    .cloned();
                match receipt {
                    Some(receipt) if receipt.turn_hash == expected => landed(session, receipt),
                    _ => Outcome::Refused(
                        "party committed but its complete receipt was unavailable".to_string(),
                    ),
                }
            }
        }
    }

    fn do_act(session: &mut PartySession, actor: &DreggIdentity) -> Outcome {
        if session.actor_acted(actor) {
            return Outcome::Refused("this role already contributed to the encounter".to_string());
        }
        let Some(party) = session.party.as_mut() else {
            return Outcome::Refused("the roster has not launched".to_string());
        };
        let outcome = party.act_in_role_as(actor.as_str());
        Self::fold_party_act(session, outcome)
    }

    fn do_misplay(session: &mut PartySession, actor: &DreggIdentity) -> Outcome {
        let Some(party) = session.party.as_mut() else {
            return Outcome::Refused("the roster has not launched".to_string());
        };
        let Some(idx) = party.seat_index_for(actor.as_str()) else {
            return Outcome::Refused("identity holds no party seat".to_string());
        };
        let wrong = if party.seat(idx).role() == Role::Tank {
            PartyMove::DisarmLock
        } else {
            PartyMove::GuardFront
        };
        let outcome = party.act_as(actor.as_str(), wrong);
        Self::fold_party_act(session, outcome)
    }

    fn do_fork_vote(session: &mut PartySession, actor: &DreggIdentity, arg: i64) -> Outcome {
        let options = fork_options();
        if arg < 0 || arg as usize >= options.len() {
            return Outcome::Refused("no such fork path".to_string());
        }
        let option = arg as usize;
        let Some(party) = session.party.as_ref() else {
            return Outcome::Refused("the roster has not launched".to_string());
        };
        if party.seat_index_for(actor.as_str()).is_none() {
            return Outcome::Refused("identity holds no party seat".to_string());
        }
        if session.fork_votes.contains_key(actor.as_str()) {
            return Outcome::Refused("this seat already voted at the fork".to_string());
        }

        if session.current_fork.is_none() {
            let mut fork = match party.open_fork("The passage forks", options) {
                Ok(fork) => fork,
                Err(error) => {
                    return Outcome::Refused(format!("the fork could not open: {error}"));
                }
            };
            let ballot = match party.sign_ballot_as(&fork, actor.as_str(), option) {
                Ok(ballot) => ballot,
                Err(error) => return Outcome::Refused(error.to_string()),
            };
            let receipt = match fork.cast_receipted(&ballot) {
                Ok(receipt) => receipt,
                Err(error) => {
                    return Outcome::Refused(format!("the party ballot was refused: {error}"));
                }
            };
            session.current_fork = Some(fork);
            session.fork_votes.insert(actor.0.clone(), option);
            return landed(session, receipt);
        }

        let ballot = {
            let fork = session.current_fork.as_ref().expect("checked above");
            match party.sign_ballot_as(fork, actor.as_str(), option) {
                Ok(ballot) => ballot,
                Err(error) => return Outcome::Refused(error.to_string()),
            }
        };
        let receipt = match session
            .current_fork
            .as_mut()
            .expect("checked above")
            .cast_receipted(&ballot)
        {
            Ok(receipt) => receipt,
            Err(error) => {
                return Outcome::Refused(format!("the party ballot was refused: {error}"));
            }
        };
        session.fork_votes.insert(actor.0.clone(), option);
        landed(session, receipt)
    }

    fn do_resolve_fork(session: &mut PartySession, actor: &DreggIdentity) -> Outcome {
        if session.leader() != Some(actor.as_str()) {
            return Outcome::Refused("only the party leader can resolve the fork".to_string());
        }
        let Some(fork) = session.current_fork.as_mut() else {
            return Outcome::Refused("no fork ballot is open".to_string());
        };
        let Some(party) = session.party.as_mut() else {
            return Outcome::Refused("the roster has not launched".to_string());
        };
        let resolution = match fork.resolve_into(party) {
            Ok(resolution) => resolution,
            Err(error) => return Outcome::Refused(format!("the fork did not resolve: {error}")),
        };
        let receipt = match party.world().receipts().last().cloned() {
            Some(receipt) if receipt.turn_hash == resolution.receipt => receipt,
            _ => {
                return Outcome::Refused(
                    "fork resolved but its complete receipt was unavailable".to_string(),
                );
            }
        };
        session.current_fork = None;
        session.fork_votes.clear();
        session.last_fork = Some(resolution.label);
        landed(session, receipt)
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

        let mut out = vec![Action::new("Act in my role", TURN_ACT, 0, true)];
        for (i, (label, _)) in fork_options().into_iter().enumerate() {
            out.push(Action::new(
                format!("Vote: {label}"),
                TURN_FORK,
                i as i64,
                true,
            ));
        }
        out.push(Action::new(
            "Resolve the fork",
            TURN_RESOLVE_FORK,
            0,
            session.fork_total() >= session.quorum(),
        ));
        out
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

        let Some(party) = session.party.as_ref() else {
            return Vec::new();
        };
        let Some(seat_idx) = party.seat_index_for(viewer.as_str()) else {
            return Vec::new();
        };
        let mut out = vec![Action::new(
            format!("Act as {}", party.seat(seat_idx).role().name()),
            TURN_ACT,
            seat_idx as i64,
            !session.seat_acted(seat_idx),
        )];
        if !session.fork_votes.contains_key(viewer.as_str()) {
            for (i, (label, _)) in fork_options().into_iter().enumerate() {
                out.push(Action::new(
                    format!("Vote: {label}"),
                    TURN_FORK,
                    i as i64,
                    true,
                ));
            }
        }
        if session.leader() == Some(viewer.as_str()) {
            out.push(Action::new(
                "Resolve the fork",
                TURN_RESOLVE_FORK,
                0,
                session.fork_total() >= session.quorum(),
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
        let mut children = vec![section(
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
        )];

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
                        "playing"
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
            children.push(section(
                "Encounter",
                "accent",
                vec![text(format!(
                    "shared focus {}/{} · each role contributes once",
                    session.focus_spent(),
                    FOCUS_BUDGET,
                ))],
            ));
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
            children.push(section("Open fork ballot", "warn", counts));
        }
        if let Some(fork) = session.last_fork() {
            children.push(section(
                "Resolved fork",
                "genuine",
                vec![text(format!("the party took: {fork}"))],
            ));
        }

        let actions = action_menu(actions);
        if !actions.is_empty() {
            children.push(section("Actions", "accent", vec![menu(actions)]));
        }

        Surface(section(
            "DreggNet Party — form, ready, act, decide",
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
        if session.lobby.as_ref().is_some_and(PartyLobby::launched) != session.party.is_some() {
            return VerifyReport::broken(
                session.turns,
                "lobby launch state diverges from the party world",
            );
        }
        if let Some(party) = session.party.as_ref() {
            for seat in party.seats() {
                if party.world().ledger().get(&seat.cell()).is_none() {
                    return VerifyReport::broken(
                        session.turns,
                        format!("seat `{}` has no cell in the shared world", seat.name()),
                    );
                }
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
                return VerifyReport::broken(
                    idx,
                    format!("hosted party replay refused at step {idx}: {outcome:?}"),
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
        if replay_lobby != live_lobby
            || replay.turns != session.turns
            || replay.lobby_world.state_root() != session.lobby_world.state_root()
            || replay.party_root() != session.party_root()
            || replay.fork_votes != session.fork_votes
            || replay.fork_tally() != session.fork_tally()
            || replay.last_fork != session.last_fork
        {
            return VerifyReport::broken(
                session.turns,
                "hosted party replay reached a different committed state",
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
