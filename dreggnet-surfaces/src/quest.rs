//! A playable faction-to-quest composition on the shared Offering surface.
//!
//! The underlying crates already had the difficult pieces: `dreggnet-faction` commits
//! monotone standing and one-way betrayal on a real `WorldCell`, while `dreggnet-quest`
//! commits an ordered three-step errand and verifies its completion by fresh replay. This
//! module makes them one hosted game. A player must earn and exercise the Embers' trial
//! before any errand move is admitted; the completed quest is the existing replay-verified
//! `reward == 1` win, never a host-authored completion flag.
//!
//! Every landed choice also writes a full 32-byte, domain-separated commitment to the
//! owning [`DreggIdentity`] into the same world turn. Verification replays both cells,
//! recomputes every actor commitment, checks exact pre/post state roots, and checks the
//! cross-feature unlock before accepting any quest history. The generic `OfferingHost`
//! move log therefore restarts the whole composition by replay rather than restoring a
//! trusted state blob. Replay compares the timestamp-independent committed state and
//! the full actor-binding field; receipt hashes are checked as a chain, but are not
//! expected to reproduce after a refused attempt has consumed a local signing nonce.
//!
//! Honest boundary: faction and quest are currently separate `WorldCell` ledgers. The
//! transition between them is a fail-closed host read through faction's canonical
//! `FactionStanding`; it is not yet one in-executor `ObservedFieldEquals` across the two
//! cells. The committed faction history and the gate are rechecked here, but a production
//! cross-node version still wants the project's finalized-root witness channel.

use deos_view::ViewNode;
use dregg_app_framework::{FieldElement, TurnReceipt, field_from_bytes};
use dreggnet_faction::standing::{FactionStanding, read_standing};
use dreggnet_faction::{ROOM_HALL as FACTION_HALL, Roster};
use dreggnet_offerings::{
    Action, DreggIdentity, Offering, OfferingError, Outcome, RunCost, SessionConfig, Surface,
    VerifyReport,
};
use dreggnet_quest::{
    HALL_ACCEPT, LN_LIGHT_1, LN_LIGHT_2, LN_LIGHT_3, LN_TURN_IN, ROOM_BOARD,
    ROOM_HALL as QUEST_HALL, deploy_quest, errand_compiled, errand_scene, reached_quest_win,
};
use spween::{Choice, PassageContent, Scene};
use spween_dregg::{Driver, Playthrough, StepReceipt, WorldCell, WorldError};

use crate::{action_menu, menu, pill, row, section, text};

/// Shared catalog key. This is an identity-owned RPG surface, not a shared table.
pub const KEY: &str = "quest";
/// Shared catalog copy for the generic web/Discord/Telegram/WeChat host.
pub const DESCRIPTION: &str =
    "Ashenmoor Errand — earn committed faction standing, unlock, and complete an ordered quest";

pub const TURN_PLEDGE_EMBERS: &str = "pledge-embers";
pub const TURN_UNDERTAKE_TRIAL: &str = "undertake-ember-trial";
pub const TURN_BETRAY_EMBERS: &str = "betray-embers";
pub const TURN_QUEST_CHOICE: &str = "quest-choice";

const EMBERS: &str = "embers";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Lane {
    Faction,
    Quest,
}

impl Lane {
    fn tag(self) -> u8 {
        match self {
            Lane::Faction => 0,
            Lane::Quest => 1,
        }
    }
}

#[derive(Clone, Debug)]
struct JournalStep {
    lane: Lane,
    lane_step: usize,
    passage: String,
    choice: usize,
    actor: DreggIdentity,
    actor_commitment: FieldElement,
}

/// One live Ashenmoor errand: two genuine executor worlds plus their replay records.
pub struct AshenmoorErrandSession {
    seed: u64,
    cell_seed: u8,
    owner: Option<DreggIdentity>,
    roster: Roster,
    faction_scene: Scene,
    faction_world: WorldCell,
    faction_genesis: TurnReceipt,
    faction_genesis_state: Vec<u64>,
    faction_steps: Vec<StepReceipt>,
    quest_scene: Scene,
    quest_world: WorldCell,
    quest_genesis: TurnReceipt,
    quest_genesis_state: Vec<u64>,
    quest_steps: Vec<StepReceipt>,
    journal: Vec<JournalStep>,
}

impl AshenmoorErrandSession {
    pub fn owner(&self) -> Option<&DreggIdentity> {
        self.owner.as_ref()
    }

    pub fn turns(&self) -> usize {
        self.journal.len()
    }

    pub fn standing(&self) -> FactionStanding {
        read_standing(
            &self.faction_world,
            self.roster
                .faction(EMBERS)
                .expect("the Ashenmoor roster contains the Embers"),
        )
    }

    pub fn quest_opened(&self) -> bool {
        let standing = self.standing();
        standing.unlocked && standing.content_available()
    }

    pub fn quest_completed(&self) -> bool {
        self.quest_opened()
            && self.quest_world.read_passage().is_none()
            && self.quest_world.read_var("reward") == 1
    }

    pub fn ended(&self) -> bool {
        let standing = self.standing();
        self.quest_completed() || (standing.betrayed && !standing.unlocked)
    }

    pub fn quest_steps_done(&self) -> u64 {
        self.quest_world.read_var("steps_done")
    }

    fn faction_playthrough(&self) -> Playthrough {
        Playthrough {
            genesis: self.faction_genesis.clone(),
            genesis_state: self.faction_genesis_state.clone(),
            steps: self.faction_steps.clone(),
        }
    }

    fn quest_playthrough(&self) -> Playthrough {
        Playthrough {
            genesis: self.quest_genesis.clone(),
            genesis_state: self.quest_genesis_state.clone(),
            steps: self.quest_steps.clone(),
        }
    }

    fn current_quest_passage(&self) -> Option<String> {
        let idx = self.quest_world.read_passage()?;
        self.quest_scene
            .passages
            .get(idx)
            .map(|passage| passage.name.to_string())
    }
}

/// The frontend-neutral Ashenmoor errand factory.
#[derive(Debug, Clone, Copy, Default)]
pub struct AshenmoorErrandOffering;

impl AshenmoorErrandOffering {
    pub const fn new() -> Self {
        AshenmoorErrandOffering
    }

    fn actor_commitment(
        seed: u64,
        actor: &DreggIdentity,
        lane: Lane,
        ordinal: usize,
        passage: &str,
        choice: usize,
    ) -> FieldElement {
        let mut material = b"dreggnet-ashenmoor-errand-actor-v1".to_vec();
        material.extend_from_slice(&seed.to_le_bytes());
        material.push(lane.tag());
        material.extend_from_slice(&(ordinal as u64).to_le_bytes());
        material.extend_from_slice(&(passage.len() as u64).to_le_bytes());
        material.extend_from_slice(passage.as_bytes());
        material.extend_from_slice(&(choice as u64).to_le_bytes());
        material.extend_from_slice(&(actor.0.len() as u64).to_le_bytes());
        material.extend_from_slice(actor.0.as_bytes());
        field_from_bytes(&material)
    }

    fn choice(scene: &Scene, passage: &str, index: usize) -> Option<Choice> {
        scene
            .passages
            .iter()
            .find(|p| p.name.as_str() == passage)?
            .content
            .iter()
            .filter_map(|content| match content {
                PassageContent::Choice(choice) => Some(choice),
                _ => None,
            })
            .nth(index)
            .cloned()
    }

    fn check_actor(session: &AshenmoorErrandSession, actor: &DreggIdentity) -> Result<(), String> {
        if let Some(owner) = &session.owner
            && owner != actor
        {
            return Err(format!(
                "this errand belongs to {}; {} cannot advance it",
                owner.0, actor.0
            ));
        }
        Ok(())
    }

    fn land(
        session: &mut AshenmoorErrandSession,
        lane: Lane,
        passage: String,
        choice_index: usize,
        choice: Choice,
        actor: DreggIdentity,
    ) -> Outcome {
        if let Err(reason) = Self::check_actor(session, &actor) {
            return Outcome::Refused(reason);
        }
        let lane_step = match lane {
            Lane::Faction => session.faction_steps.len(),
            Lane::Quest => session.quest_steps.len(),
        };
        let commitment = Self::actor_commitment(
            session.seed,
            &actor,
            lane,
            session.journal.len(),
            &passage,
            choice_index,
        );
        let applied = match lane {
            Lane::Faction => session.faction_world.apply_choice_certified(
                &passage,
                choice_index,
                &choice,
                commitment,
            ),
            Lane::Quest => session.quest_world.apply_choice_certified(
                &passage,
                choice_index,
                &choice,
                commitment,
            ),
        };
        match applied {
            Ok(receipt) => {
                let state = match lane {
                    Lane::Faction => session.faction_world.snapshot(),
                    Lane::Quest => session.quest_world.snapshot(),
                };
                let step = StepReceipt {
                    passage: passage.clone(),
                    choice_index,
                    receipt: receipt.clone(),
                    state,
                    decision_commitment: Some(commitment),
                };
                match lane {
                    Lane::Faction => session.faction_steps.push(step),
                    Lane::Quest => session.quest_steps.push(step),
                }
                if session.owner.is_none() {
                    session.owner = Some(actor.clone());
                }
                session.journal.push(JournalStep {
                    lane,
                    lane_step,
                    passage,
                    choice: choice_index,
                    actor,
                    actor_commitment: commitment,
                });
                Outcome::Landed {
                    receipt,
                    ended: session.ended(),
                }
            }
            Err(WorldError::Refused(reason)) => Outcome::Refused(reason),
            Err(error) => Outcome::Refused(error.to_string()),
        }
    }

    fn faction_action(
        session: &mut AshenmoorErrandSession,
        actor: DreggIdentity,
        index: usize,
    ) -> Outcome {
        if session.quest_opened() {
            return Outcome::Refused("the trial is complete; continue the errand".to_string());
        }
        let Some(choice) = Self::choice(&session.faction_scene, FACTION_HALL, index) else {
            return Outcome::Refused("that faction move does not exist".to_string());
        };
        Self::land(
            session,
            Lane::Faction,
            FACTION_HALL.to_string(),
            index,
            choice,
            actor,
        )
    }

    fn quest_action(
        session: &mut AshenmoorErrandSession,
        actor: DreggIdentity,
        index: usize,
    ) -> Outcome {
        if !session.quest_opened() {
            return Outcome::Refused(
                "the Loremaster's errand is sealed until the Ember trial is genuinely unlocked"
                    .to_string(),
            );
        }
        let Some(passage) = session.current_quest_passage() else {
            return Outcome::Refused("the errand has already ended".to_string());
        };
        let Some(choice) = Self::choice(&session.quest_scene, &passage, index) else {
            return Outcome::Refused("that move is not in the current quest passage".to_string());
        };
        Self::land(session, Lane::Quest, passage, index, choice, actor)
    }

    fn faction_actions(&self, session: &AshenmoorErrandSession) -> Vec<Action> {
        let standing = session.standing();
        if standing.betrayed || standing.unlocked {
            return Vec::new();
        }
        let lines = session.roster.lines(EMBERS);
        vec![
            Action::new(
                "Tend the Ember beacon",
                TURN_PLEDGE_EMBERS,
                0,
                standing.rep < standing.ceiling,
            ),
            Action::new(
                "Undertake the Ember trial",
                TURN_UNDERTAKE_TRIAL,
                0,
                standing.meets_threshold(),
            ),
            Action::new(
                "Betray the Ember wardens (final)",
                TURN_BETRAY_EMBERS,
                0,
                true,
            ),
        ]
        .into_iter()
        .map(|mut action| {
            action.arg = match action.turn.as_str() {
                TURN_PLEDGE_EMBERS => lines.pledge as i64,
                TURN_UNDERTAKE_TRIAL => lines.trial as i64,
                TURN_BETRAY_EMBERS => lines.betray as i64,
                _ => 0,
            };
            action
        })
        .collect()
    }

    fn quest_actions(&self, session: &AshenmoorErrandSession) -> Vec<Action> {
        let Some(passage) = session.current_quest_passage() else {
            return Vec::new();
        };
        if passage == ROOM_BOARD {
            let done = session.quest_steps_done();
            [LN_LIGHT_1, LN_LIGHT_2, LN_LIGHT_3, LN_TURN_IN]
                .into_iter()
                .filter_map(|index| {
                    let choice = Self::choice(&session.quest_scene, ROOM_BOARD, index)?;
                    let enabled = match index {
                        LN_LIGHT_1 => done == 0,
                        LN_LIGHT_2 => done == 1,
                        LN_LIGHT_3 => done == 2,
                        LN_TURN_IN => done >= 3 && session.quest_world.read_var("reward") == 0,
                        _ => false,
                    };
                    Some(Action::new(
                        choice.text.to_string(),
                        TURN_QUEST_CHOICE,
                        index as i64,
                        enabled,
                    ))
                })
                .collect()
        } else if passage == QUEST_HALL {
            Self::choice(&session.quest_scene, QUEST_HALL, HALL_ACCEPT)
                .map(|choice| {
                    vec![Action::new(
                        choice.text.to_string(),
                        TURN_QUEST_CHOICE,
                        HALL_ACCEPT as i64,
                        session.quest_world.read_var("reward") == 1,
                    )]
                })
                .unwrap_or_default()
        } else {
            Vec::new()
        }
    }

    fn replay_committed_state(
        fresh: WorldCell,
        scene: &Scene,
        play: &Playthrough,
    ) -> Result<(), String> {
        let driver = Driver::start(fresh, scene).map_err(|error| error.to_string())?;
        let genesis = driver
            .genesis()
            .ok_or_else(|| "replay produced no genesis receipt".to_string())?;
        if genesis.pre_state_hash != play.genesis.pre_state_hash
            || genesis.post_state_hash != play.genesis.post_state_hash
            || genesis.effects_hash != play.genesis.effects_hash
        {
            return Err("genesis receipt roots differ on fresh replay".to_string());
        }
        let (world, _) = driver.finish();
        for (index, recorded) in play.steps.iter().enumerate() {
            let current = world
                .read_passage()
                .and_then(|passage| scene.passages.get(passage))
                .map(|passage| passage.name.to_string())
                .ok_or_else(|| format!("world ended before replay step {index}"))?;
            if current != recorded.passage {
                return Err(format!(
                    "step {index} recorded in `{}` but replay is in `{current}`",
                    recorded.passage
                ));
            }
            let choice = Self::choice(scene, &current, recorded.choice_index)
                .ok_or_else(|| format!("step {index} names no authored choice"))?;
            let replayed_receipt = match recorded.decision_commitment {
                Some(commitment) => world.apply_choice_certified(
                    &current,
                    recorded.choice_index,
                    &choice,
                    commitment,
                ),
                None => world.apply_choice(&current, recorded.choice_index, &choice),
            }
            .map_err(|error| format!("step {index} refused on exact replay: {error}"))?;
            // The effect tape is independent of the executor's burned agent nonce: it is
            // the canonical fold of the authored Set/Modify/navigation effects plus this
            // step's exact actor commitment. Bind it to replay even though pre/post roots
            // cannot be equal after an earlier refused turn (see the verifier comment).
            if replayed_receipt.effects_hash != recorded.receipt.effects_hash {
                return Err(format!("step {index} effects differ on fresh replay"));
            }
            if world.snapshot() != recorded.state {
                return Err(format!("step {index} state differs on fresh replay"));
            }
            let expected_decision = recorded.decision_commitment.unwrap_or([0u8; 32]);
            if world.read_decision() != expected_decision {
                return Err(format!(
                    "step {index} actor-binding field differs on fresh replay"
                ));
            }
        }
        Ok(())
    }

    fn verify_journal(&self, session: &AshenmoorErrandSession) -> Result<(), String> {
        if session.owner.is_none() != session.journal.is_empty() {
            return Err("owner claim and landed journal disagree".to_string());
        }
        let mut faction_cursor = 0usize;
        let mut quest_cursor = 0usize;
        let mut quest_seen = false;
        for (ordinal, journal) in session.journal.iter().enumerate() {
            let Some(owner) = &session.owner else {
                return Err("a landed move has no owning identity".to_string());
            };
            if &journal.actor != owner {
                return Err(format!(
                    "journal step {ordinal} belongs to a different actor"
                ));
            }
            let expected = Self::actor_commitment(
                session.seed,
                &journal.actor,
                journal.lane,
                ordinal,
                &journal.passage,
                journal.choice,
            );
            if journal.actor_commitment != expected {
                return Err(format!(
                    "journal step {ordinal} has a forged actor commitment"
                ));
            }
            let step = match journal.lane {
                Lane::Faction => {
                    if quest_seen {
                        return Err("faction history appears after the quest opened".to_string());
                    }
                    if journal.lane_step != faction_cursor {
                        return Err(
                            "faction journal order diverges from its receipt lane".to_string()
                        );
                    }
                    let step = session
                        .faction_steps
                        .get(faction_cursor)
                        .ok_or_else(|| "faction journal names a missing receipt".to_string())?;
                    faction_cursor += 1;
                    step
                }
                Lane::Quest => {
                    quest_seen = true;
                    if journal.lane_step != quest_cursor {
                        return Err(
                            "quest journal order diverges from its receipt lane".to_string()
                        );
                    }
                    let step = session
                        .quest_steps
                        .get(quest_cursor)
                        .ok_or_else(|| "quest journal names a missing receipt".to_string())?;
                    quest_cursor += 1;
                    step
                }
            };
            if step.passage != journal.passage
                || step.choice_index != journal.choice
                || step.decision_commitment != Some(expected)
            {
                return Err(format!(
                    "journal step {ordinal} diverges from its committed step"
                ));
            }
        }
        if faction_cursor != session.faction_steps.len()
            || quest_cursor != session.quest_steps.len()
        {
            return Err("a committed lane step is absent from the actor journal".to_string());
        }
        if !session.quest_steps.is_empty() && !session.quest_opened() {
            return Err(
                "quest receipts exist without a replay-verified faction unlock".to_string(),
            );
        }
        let mut hashes = std::collections::HashSet::new();
        for (lane, play) in [
            ("faction", session.faction_playthrough()),
            ("quest", session.quest_playthrough()),
        ] {
            for (index, receipt) in play.receipts().into_iter().enumerate() {
                if receipt.turn_hash == [0u8; 32] {
                    return Err(format!("{lane} receipt {index} has no genuine turn hash"));
                }
                if !hashes.insert(receipt.turn_hash) {
                    return Err(format!("{lane} receipt {index} duplicates a prior turn"));
                }
            }
            // Chain the receipts by their explicit causal head. This remains exact across
            // refusals: Phase 1 burns an agent nonce/fee even when the target-world turn is
            // rejected, so adjacent successful receipts need not have equal post/pre state
            // anchors, but a refusal produces no receipt and cannot advance this hash head.
            // `replay_committed_state` separately reproduces genesis and every committed
            // state snapshot, the full actor field, and each effects hash. Receipt turn hashes
            // and pre/post roots are intentionally not expected to reproduce: an executor
            // refusal commits no target-world mutation, but it burns the submitting agent's
            // on-ledger nonce. That nonce is included in the consensus-state anchor and signed
            // turn, so the resulting later receipt is still genuine and chained while those
            // fields differ from a success-only replay. The target world remains exactly
            // replayable through `snapshot`, and the choice tape through `effects_hash`.
            let receipts = play.receipts();
            for (index, pair) in receipts.windows(2).enumerate() {
                if pair[1].previous_receipt_hash != Some(pair[0].receipt_hash()) {
                    return Err(format!(
                        "{lane} causal receipt chain breaks between receipt {index} and {}",
                        index + 1
                    ));
                }
            }
        }
        let faction_state = session
            .faction_steps
            .last()
            .map(|step| step.state.as_slice())
            .unwrap_or(session.faction_genesis_state.as_slice());
        if session.faction_world.snapshot() != faction_state {
            return Err("live faction state diverges from its last committed step".to_string());
        }
        let faction_decision = session
            .faction_steps
            .last()
            .and_then(|step| step.decision_commitment)
            .unwrap_or([0u8; 32]);
        if session.faction_world.read_decision() != faction_decision {
            return Err(
                "live faction actor-binding field diverges from its last committed step"
                    .to_string(),
            );
        }
        let quest_state = session
            .quest_steps
            .last()
            .map(|step| step.state.as_slice())
            .unwrap_or(session.quest_genesis_state.as_slice());
        if session.quest_world.snapshot() != quest_state {
            return Err("live quest state diverges from its last committed step".to_string());
        }
        let quest_decision = session
            .quest_steps
            .last()
            .and_then(|step| step.decision_commitment)
            .unwrap_or([0u8; 32]);
        if session.quest_world.read_decision() != quest_decision {
            return Err(
                "live quest actor-binding field diverges from its last committed step".to_string(),
            );
        }
        Ok(())
    }
}

impl Offering for AshenmoorErrandOffering {
    type Session = AshenmoorErrandSession;

    fn open(&self, cfg: SessionConfig) -> Result<Self::Session, OfferingError> {
        let seed = cfg.seed.unwrap_or(0xA57E);
        let cell_seed = ((seed % 251) + 1) as u8;

        let roster = Roster::ashenmoor();
        let faction_scene = roster.scene();
        let faction_driver = Driver::start(roster.deploy(cell_seed), &faction_scene)
            .map_err(|error| OfferingError::Deploy(format!("faction genesis: {error}")))?;
        let faction_genesis = faction_driver.genesis().cloned().unwrap_or_default();
        let faction_genesis_state = faction_driver.playthrough().genesis_state;
        let (faction_world, _) = faction_driver.finish();

        let quest_scene = errand_scene();
        let quest_driver = Driver::start(deploy_quest(cell_seed.wrapping_add(1)), &quest_scene)
            .map_err(|error| OfferingError::Deploy(format!("quest genesis: {error}")))?;
        let quest_genesis = quest_driver.genesis().cloned().unwrap_or_default();
        let quest_genesis_state = quest_driver.playthrough().genesis_state;
        let (quest_world, _) = quest_driver.finish();

        Ok(AshenmoorErrandSession {
            seed,
            cell_seed,
            owner: None,
            roster,
            faction_scene,
            faction_world,
            faction_genesis,
            faction_genesis_state,
            faction_steps: Vec::new(),
            quest_scene,
            quest_world,
            quest_genesis,
            quest_genesis_state,
            quest_steps: Vec::new(),
            journal: Vec::new(),
        })
    }

    fn actions(&self, session: &Self::Session) -> Vec<Action> {
        if session.ended() {
            Vec::new()
        } else if session.quest_opened() {
            self.quest_actions(session)
        } else {
            self.faction_actions(session)
        }
    }

    fn actions_for(&self, session: &Self::Session, viewer: &DreggIdentity) -> Vec<Action> {
        let mut actions = self.actions(session);
        if session.owner.as_ref().is_some_and(|owner| owner != viewer) {
            for action in &mut actions {
                action.enabled = false;
            }
        }
        actions
    }

    fn advance(&self, session: &mut Self::Session, input: Action, actor: DreggIdentity) -> Outcome {
        if let Err(reason) = Self::check_actor(session, &actor) {
            return Outcome::Refused(reason);
        }
        if session.ended() {
            return Outcome::Refused("this Ashenmoor errand is final".to_string());
        }
        match input.turn.as_str() {
            TURN_PLEDGE_EMBERS => {
                let index = session.roster.lines(EMBERS).pledge;
                if input.arg != index as i64 {
                    Outcome::Refused(
                        "pledge coordinate does not match the authored roster".to_string(),
                    )
                } else {
                    Self::faction_action(session, actor, index)
                }
            }
            TURN_UNDERTAKE_TRIAL => {
                let index = session.roster.lines(EMBERS).trial;
                if input.arg != index as i64 {
                    Outcome::Refused(
                        "trial coordinate does not match the authored roster".to_string(),
                    )
                } else {
                    Self::faction_action(session, actor, index)
                }
            }
            TURN_BETRAY_EMBERS => {
                let index = session.roster.lines(EMBERS).betray;
                if input.arg != index as i64 {
                    Outcome::Refused(
                        "betrayal coordinate does not match the authored roster".to_string(),
                    )
                } else {
                    Self::faction_action(session, actor, index)
                }
            }
            TURN_QUEST_CHOICE if input.arg >= 0 => {
                Self::quest_action(session, actor, input.arg as usize)
            }
            TURN_QUEST_CHOICE => Outcome::Refused("negative quest choice".to_string()),
            _ => Outcome::Refused(format!("unknown Ashenmoor affordance `{}`", input.turn)),
        }
    }

    fn verify(&self, session: &Self::Session) -> VerifyReport {
        let turns = 2 + session.turns();
        let checked = (|| -> Result<(), String> {
            self.verify_journal(session)?;
            let faction_play = session.faction_playthrough();
            Self::replay_committed_state(
                session.roster.deploy(session.cell_seed),
                &session.faction_scene,
                &faction_play,
            )
            .map_err(|error| format!("faction roots: {error}"))?;

            let quest_play = session.quest_playthrough();
            let quest_seed = session.cell_seed.wrapping_add(1);
            Self::replay_committed_state(
                deploy_quest(quest_seed),
                &session.quest_scene,
                &quest_play,
            )
            .map_err(|error| format!("quest roots: {error}"))?;

            if session.quest_completed() {
                let final_state = quest_play
                    .steps
                    .last()
                    .map(|step| step.state.as_slice())
                    .ok_or_else(|| "a completed quest has no committed step".to_string())?;
                if !reached_quest_win(&errand_compiled(), final_state) {
                    return Err("quest ended without the authored reward win".to_string());
                }
            }
            Ok(())
        })();
        match checked {
            Ok(()) => VerifyReport::ok(turns),
            Err(error) => VerifyReport::broken(turns, error),
        }
    }

    fn render(&self, session: &Self::Session) -> Surface {
        let standing = session.standing();
        let owner = session
            .owner
            .as_ref()
            .map(|owner| owner.0.as_str())
            .unwrap_or("unclaimed — first landed move keeps it");
        let state = if session.quest_completed() {
            "writ accepted · completion replay-verifiable"
        } else if standing.betrayed && !standing.unlocked {
            "the Ember route is permanently closed"
        } else if session.quest_opened() {
            "Ember trial cleared · the ordered errand is live"
        } else {
            "earn standing, then undertake the real trial"
        };
        let progress = ViewNode::Table(vec![
            row(vec![text("Owner"), text(owner)]),
            row(vec![
                text("Committed moves"),
                text(session.turns().to_string()),
            ]),
            row(vec![
                text("Quest wards"),
                text(format!("{}/3", session.quest_steps_done())),
            ]),
            row(vec![
                text("Reward"),
                text(session.quest_world.read_var("reward").to_string()),
            ]),
        ]);
        let mut children = vec![
            section(
                "One identity · two executor worlds",
                "muted",
                vec![text(
                    "Standing is committed first; only its canonical unlocked state opens the quest.",
                )],
            ),
            dreggnet_faction::surface::standing_bars(&session.faction_world, &session.roster),
            section(
                "Errand",
                "accent",
                vec![
                    pill(
                        state,
                        if session.quest_completed() {
                            "good"
                        } else {
                            "accent"
                        },
                    ),
                    progress,
                ],
            ),
        ];
        let actions = self.actions(session);
        if !actions.is_empty() {
            children.push(section(
                "What do you do?",
                "genuine",
                vec![menu(action_menu(actions))],
            ));
        }
        Surface(section("The Ashenmoor Errand", "accent", children))
    }

    fn price(&self, _input: &Action) -> RunCost {
        RunCost::free()
    }
}
