//! Incremental Offering adapter for the Lean-native Descent.
//!
//! The game beneath this adapter is [`dungeon_on_dregg::descent::Descent`]: its
//! deployed `CellProgram` is loaded from the Lean-emitted
//! `dungeon_program.json`. This module supplies only the frontend-neutral
//! session machinery: real verb affordances, first-successful-action player
//! binding, an actor-bound hash-chained journal, exact re-execution, restart,
//! and a deos surface. It does not mirror the game rules; affordance `enabled`
//! decorations ask the native [`Sim`] mover and every submitted action goes
//! through the real executor-backed [`Descent`] verb.

use deos_view::{MenuItem, ViewNode};
use dregg_app_framework::TurnReceipt;
use dungeon_on_dregg::descent::{
    BANKED, BREATH, CAP, CARRIED, DELVE, Descent, FLEE, FLOORS, LOOT, PROGRAM_JSON, RELICS, SMITE,
    Sim, UNLOCK, guard_hp,
};
use spween_dregg::WorldError;

use crate::{
    Action, DreggIdentity, Offering, OfferingError, Outcome, RecordVerify, RunCost, SessionConfig,
    Surface, VerifyReport,
};

/// Hard bound for one hosted run journal. The perfect crowned run is 18 moves.
pub const MAX_NATIVE_DESCENT_EVENTS: usize = 128;
const MAX_ACTOR_BYTES: usize = 512;

const GENESIS_ROOT_DOMAIN: &str = "dregg.native-descent.genesis.v1";
const EVENT_ROOT_DOMAIN: &str = "dregg.native-descent.event.v1";

/// One exact native Descent verb.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NativeDescentMove {
    Delve,
    Unlock { way: u64 },
    Smite,
    Loot { relic: usize },
    Flee,
}

impl NativeDescentMove {
    fn from_action(action: &Action) -> Result<Self, String> {
        if action.text.is_some() || action.wants_text {
            return Err("native Descent verbs do not carry text".to_string());
        }
        match (action.turn.as_str(), action.arg) {
            (DELVE, 0) => Ok(Self::Delve),
            (UNLOCK, 2..=4) => Ok(Self::Unlock {
                way: action.arg as u64,
            }),
            (SMITE, 0) => Ok(Self::Smite),
            (LOOT, 0..=7) => Ok(Self::Loot {
                relic: action.arg as usize,
            }),
            (FLEE, 0) => Ok(Self::Flee),
            (verb, _) if matches!(verb, DELVE | UNLOCK | SMITE | LOOT | FLEE) => {
                Err(format!("invalid argument for native Descent verb {verb:?}"))
            }
            (verb, _) => Err(format!("unknown native Descent affordance {verb:?}")),
        }
    }

    fn execute(self, game: &mut Descent) -> Result<TurnReceipt, WorldError> {
        match self {
            Self::Delve => game.delve(),
            Self::Unlock { way } => game.unlock(way),
            Self::Smite => game.smite(),
            Self::Loot { relic } => game.loot(relic),
            Self::Flee => game.flee(),
        }
    }

    fn hash_into(self, hasher: &mut blake3::Hasher) {
        match self {
            Self::Delve => {
                hasher.update(&[0]);
            }
            Self::Unlock { way } => {
                hasher.update(&[1]);
                hasher.update(&way.to_be_bytes());
            }
            Self::Smite => {
                hasher.update(&[2]);
            }
            Self::Loot { relic } => {
                hasher.update(&[3]);
                hasher.update(&(relic as u64).to_be_bytes());
            }
            Self::Flee => {
                hasher.update(&[4]);
            }
        }
    }
}

/// One admitted, actor-bound native Descent event.
#[derive(Clone, Debug)]
pub struct NativeDescentEvent {
    pub revision: u64,
    pub actor: DreggIdentity,
    pub command: NativeDescentMove,
    pub receipt: TurnReceipt,
    pub post: Sim,
    pub root: [u8; 32],
}

/// Restart/verification checkpoint of the complete player and game image.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativeDescentCheckpoint {
    pub actor: DreggIdentity,
    pub revision: u64,
    pub root: [u8; 32],
    pub state: Sim,
}

/// A terminal bank settlement. `settlement_receipt_hash` is the real `flee`
/// executor receipt; banking is the native game's settlement rather than a
/// second application-level promise.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativeDescentCompletion {
    pub actor: DreggIdentity,
    pub revision: u64,
    pub root: [u8; 32],
    pub settlement_receipt_hash: [u8; 32],
    pub banked_relics: Vec<usize>,
    pub crowned: bool,
}

/// Public restart record. Every field is re-derived from commands through a
/// fresh Lean-program-backed executor; none is trusted as a state blob.
#[derive(Clone, Debug)]
pub struct NativeDescentRecord {
    pub seed: u8,
    pub actor: Option<DreggIdentity>,
    pub events: Vec<NativeDescentEvent>,
    pub root: [u8; 32],
    pub checkpoint: Option<NativeDescentCheckpoint>,
    pub completion: Option<NativeDescentCompletion>,
}

/// One live frontend-neutral session.
pub struct NativeDescentSession {
    seed: u8,
    game: Descent,
    actor: Option<DreggIdentity>,
    events: Vec<NativeDescentEvent>,
    root: [u8; 32],
    checkpoint: Option<NativeDescentCheckpoint>,
    completion: Option<NativeDescentCompletion>,
}

impl NativeDescentSession {
    pub fn actor(&self) -> Option<&DreggIdentity> {
        self.actor.as_ref()
    }

    pub fn game(&self) -> &Descent {
        &self.game
    }

    pub fn revision(&self) -> u64 {
        self.events.len() as u64
    }

    pub fn root(&self) -> [u8; 32] {
        self.root
    }

    pub fn events(&self) -> &[NativeDescentEvent] {
        &self.events
    }

    pub fn checkpoint(&self) -> Option<&NativeDescentCheckpoint> {
        self.checkpoint.as_ref()
    }

    pub fn completion(&self) -> Option<&NativeDescentCompletion> {
        self.completion.as_ref()
    }

    pub fn export_record(&self) -> NativeDescentRecord {
        NativeDescentRecord {
            seed: self.seed,
            actor: self.actor.clone(),
            events: self.events.clone(),
            root: self.root,
            checkpoint: self.checkpoint.clone(),
            completion: self.completion.clone(),
        }
    }
}

/// The generic Offering adapter for the Lean-native Descent.
#[derive(Clone, Copy, Debug, Default)]
pub struct NativeDescentOffering;

impl NativeDescentOffering {
    pub fn new() -> Self {
        Self
    }

    /// Resume an untrusted record only after exact native re-execution.
    pub fn resume_record(
        &self,
        record: &NativeDescentRecord,
    ) -> Result<NativeDescentSession, OfferingError> {
        replay_record(record).map_err(OfferingError::Deploy)
    }

    fn actions_for_sim(sim: &Sim) -> Vec<Action> {
        if sim.fate != 0 {
            return Vec::new();
        }
        let mut actions = vec![
            Action::new(
                format!("Descend to floor {}", sim.depth + 1),
                DELVE,
                0,
                sim.delve().is_ok(),
            ),
            Action::new("Strike the guardian", SMITE, 0, sim.smite().is_ok()),
            Action::new(
                "Bank the carried relics and leave",
                FLEE,
                0,
                sim.flee().is_ok(),
            ),
        ];
        actions.extend((2..=FLOORS).map(|way| {
            Action::new(
                format!("Exercise the key to way {way}"),
                UNLOCK,
                way as i64,
                sim.unlock(way).is_ok(),
            )
        }));
        actions.extend((0..RELICS).map(|relic| {
            Action::new(
                relic_label(relic),
                LOOT,
                relic as i64,
                sim.loot(relic).is_ok(),
            )
        }));
        actions
    }

    fn verify_exact_record(
        &self,
        session: &NativeDescentSession,
        record: &NativeDescentRecord,
    ) -> VerifyReport {
        let turns = record.events.len() + 1;
        if record.seed != session.seed
            || record.actor != session.actor
            || record.root != session.root
            || record.checkpoint != session.checkpoint
            || record.completion != session.completion
            || record.events.len() != session.events.len()
        {
            return VerifyReport::broken(turns, "record does not name the exact live session head");
        }
        match replay_record(record) {
            Ok(_) => VerifyReport::ok(turns),
            Err(reason) => VerifyReport::broken(turns, reason),
        }
    }
}

impl Offering for NativeDescentOffering {
    type Session = NativeDescentSession;

    fn open(&self, cfg: SessionConfig) -> Result<Self::Session, OfferingError> {
        let seed = ((cfg.seed.unwrap_or(1) % 251) + 1) as u8;
        let game =
            Descent::deploy(seed).map_err(|error| OfferingError::Deploy(error.to_string()))?;
        let root = genesis_root(seed, game.sim());
        Ok(NativeDescentSession {
            seed,
            game,
            actor: None,
            events: Vec::new(),
            root,
            checkpoint: None,
            completion: None,
        })
    }

    fn actions(&self, session: &Self::Session) -> Vec<Action> {
        Self::actions_for_sim(session.game.sim())
    }

    fn actions_for(&self, session: &Self::Session, viewer: &DreggIdentity) -> Vec<Action> {
        let mut actions = self.actions(session);
        if session.actor.as_ref().is_some_and(|actor| actor != viewer) {
            for action in &mut actions {
                action.enabled = false;
            }
        }
        actions
    }

    fn advance(&self, session: &mut Self::Session, input: Action, actor: DreggIdentity) -> Outcome {
        if session.events.len() >= MAX_NATIVE_DESCENT_EVENTS {
            return Outcome::Refused("native Descent journal reached its fixed bound".to_string());
        }
        if !valid_actor(&actor) {
            return Outcome::Refused("the actor identity is empty or overlong".to_string());
        }
        if let Some(bound) = &session.actor {
            if bound != &actor {
                return Outcome::Refused(format!(
                    "this Descent is bound to {}; {} cannot move it",
                    bound.as_str(),
                    actor.as_str()
                ));
            }
        }
        let command = match NativeDescentMove::from_action(&input) {
            Ok(command) => command,
            Err(reason) => return Outcome::Refused(reason),
        };
        let receipt = match command.execute(&mut session.game) {
            Ok(receipt) => receipt,
            Err(WorldError::Refused(reason)) => return Outcome::Refused(reason),
            Err(error) => return Outcome::Refused(error.to_string()),
        };

        // A refused first click cannot seize the session: identity binds only
        // after the real executor has admitted the first native game turn.
        if session.actor.is_none() {
            session.actor = Some(actor.clone());
        }
        let revision = session.revision() + 1;
        let post = session.game.sim().clone();
        let root = event_root(session.root, revision, &actor, command, &receipt, &post);
        let event = NativeDescentEvent {
            revision,
            actor: actor.clone(),
            command,
            receipt: receipt.clone(),
            post: post.clone(),
            root,
        };
        session.root = root;
        session.events.push(event);
        session.checkpoint = Some(NativeDescentCheckpoint {
            actor: actor.clone(),
            revision,
            root,
            state: post.clone(),
        });
        if post.fate != 0 {
            session.completion = Some(completion(&actor, revision, root, &post, &receipt));
        }
        Outcome::Landed {
            receipt,
            ended: post.fate != 0,
        }
    }

    fn verify(&self, session: &Self::Session) -> VerifyReport {
        self.verify_exact_record(session, &session.export_record())
    }

    fn render(&self, session: &Self::Session) -> Surface {
        let sim = session.game.sim();
        let actor = session
            .actor
            .as_ref()
            .map(|actor| actor.as_str())
            .unwrap_or("unclaimed — the first landed move binds the player");
        let guardian = if sim.depth == 0 {
            "surface — no guardian".to_string()
        } else {
            format!(
                "floor {} guardian: {}/{} wounds",
                sim.depth,
                sim.wounds,
                guard_hp(sim.depth)
            )
        };
        let carried = relics_with_custody(sim, CARRIED);
        let banked = relics_with_custody(sim, BANKED);
        let state = vec![
            ViewNode::Text(format!("player: {actor}")),
            ViewNode::Text(format!(
                "depth {} · light {} / {} · carrying {} / {}",
                sim.depth,
                BREATH.saturating_sub(sim.spent),
                BREATH,
                sim.pack(),
                CAP.saturating_sub(sim.depth)
            )),
            ViewNode::Text(guardian),
            ViewNode::Text(format!("carried: {carried}")),
            ViewNode::Text(format!("banked: {banked}")),
            ViewNode::Text(format!(
                "revision {} · root {}",
                session.revision(),
                short_digest(session.root)
            )),
        ];
        let mut children = vec![ViewNode::Section {
            title: if sim.fate == 0 {
                "The living descent".to_string()
            } else {
                "The banked tomb".to_string()
            },
            tag: if sim.fate == 0 { "accent" } else { "genuine" }.to_string(),
            children: state,
        }];
        let actions = self.actions(session);
        if !actions.is_empty() {
            children.push(ViewNode::Menu {
                items: actions
                    .iter()
                    .map(|action| MenuItem {
                        label: action.label.clone(),
                        turn: action.turn.clone(),
                        arg: action.arg,
                        enabled: action.enabled,
                    })
                    .collect(),
            });
        }
        if let Some(completion) = &session.completion {
            children.push(ViewNode::Section {
                title: if completion.crowned {
                    "Crowned settlement"
                } else {
                    "Bank settlement"
                }
                .to_string(),
                tag: "genuine".to_string(),
                children: vec![
                    ViewNode::Text(format!(
                        "{} relics banked in the terminal flee receipt",
                        completion.banked_relics.len()
                    )),
                    ViewNode::Text(format!(
                        "receipt {}",
                        short_digest(completion.settlement_receipt_hash)
                    )),
                ],
            });
        }
        Surface(ViewNode::Section {
            title: "The Descent — Lean-authored".to_string(),
            tag: "accent".to_string(),
            children,
        })
    }

    fn price(&self, _input: &Action) -> RunCost {
        RunCost::free()
    }
}

impl RecordVerify for NativeDescentOffering {
    type Session = NativeDescentSession;
    type Record = NativeDescentRecord;

    fn export_record(&self, session: &Self::Session) -> Self::Record {
        session.export_record()
    }

    fn verify_record(&self, session: &Self::Session, record: &Self::Record) -> VerifyReport {
        self.verify_exact_record(session, record)
    }
}

fn replay_record(record: &NativeDescentRecord) -> Result<NativeDescentSession, String> {
    if record.events.len() > MAX_NATIVE_DESCENT_EVENTS {
        return Err(format!(
            "{} events exceeds the native Descent bound",
            record.events.len()
        ));
    }
    let mut game = Descent::deploy(record.seed).map_err(|error| error.to_string())?;
    let mut root = genesis_root(record.seed, game.sim());
    let mut actor: Option<DreggIdentity> = None;
    let mut checkpoint = None;
    let mut derived_completion = None;

    for (index, expected) in record.events.iter().enumerate() {
        let revision = (index + 1) as u64;
        if expected.revision != revision {
            return Err(format!("event {revision} has a non-canonical revision"));
        }
        if !valid_actor(&expected.actor) {
            return Err(format!("event {revision} has an invalid actor identity"));
        }
        match &actor {
            None => actor = Some(expected.actor.clone()),
            Some(bound) if bound != &expected.actor => {
                return Err(format!("event {revision} substituted the bound player"));
            }
            Some(_) => {}
        }
        let actual = expected
            .command
            .execute(&mut game)
            .map_err(|error| format!("event {revision} refused on replay: {error}"))?;
        if actual.turn_hash != expected.receipt.turn_hash
            || actual.receipt_hash() != expected.receipt.receipt_hash()
            || actual.executor_signature != expected.receipt.executor_signature
        {
            return Err(format!("event {revision} receipt did not replay exactly"));
        }
        if game.sim() != &expected.post {
            return Err(format!(
                "event {revision} post-state differs from native replay"
            ));
        }
        let derived = event_root(
            root,
            revision,
            &expected.actor,
            expected.command,
            &expected.receipt,
            &expected.post,
        );
        if derived != expected.root {
            return Err(format!("event {revision} journal root does not recompute"));
        }
        root = derived;
        checkpoint = Some(NativeDescentCheckpoint {
            actor: expected.actor.clone(),
            revision,
            root,
            state: expected.post.clone(),
        });
        if expected.post.fate != 0 {
            if index + 1 != record.events.len() {
                return Err("the banked tomb carried later events".to_string());
            }
            derived_completion = Some(completion(
                &expected.actor,
                revision,
                root,
                &expected.post,
                &expected.receipt,
            ));
        }
    }
    if actor != record.actor
        || root != record.root
        || checkpoint != record.checkpoint
        || derived_completion != record.completion
    {
        return Err("record summary/checkpoint/completion differs from replay".to_string());
    }
    Ok(NativeDescentSession {
        seed: record.seed,
        game,
        actor,
        events: record.events.clone(),
        root,
        checkpoint,
        completion: derived_completion,
    })
}

fn valid_actor(actor: &DreggIdentity) -> bool {
    !actor.as_str().is_empty() && actor.as_str().len() <= MAX_ACTOR_BYTES
}

fn genesis_root(seed: u8, sim: &Sim) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(GENESIS_ROOT_DOMAIN);
    hasher.update(&[seed]);
    hasher.update(blake3::hash(PROGRAM_JSON.as_bytes()).as_bytes());
    hash_sim(&mut hasher, sim);
    *hasher.finalize().as_bytes()
}

fn event_root(
    previous: [u8; 32],
    revision: u64,
    actor: &DreggIdentity,
    command: NativeDescentMove,
    receipt: &TurnReceipt,
    post: &Sim,
) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(EVENT_ROOT_DOMAIN);
    hasher.update(&previous);
    hasher.update(&revision.to_be_bytes());
    hasher.update(&(actor.as_str().len() as u64).to_be_bytes());
    hasher.update(actor.as_str().as_bytes());
    command.hash_into(&mut hasher);
    hasher.update(&receipt.receipt_hash());
    match &receipt.executor_signature {
        Some(signature) => {
            hasher.update(&(signature.len() as u64).to_be_bytes());
            hasher.update(signature);
        }
        None => {
            hasher.update(&0u64.to_be_bytes());
        }
    }
    hash_sim(&mut hasher, post);
    *hasher.finalize().as_bytes()
}

fn hash_sim(hasher: &mut blake3::Hasher, sim: &Sim) {
    for value in [sim.depth, sim.spent, sim.wounds, sim.fate] {
        hasher.update(&value.to_be_bytes());
    }
    for value in sim.ways {
        hasher.update(&value.to_be_bytes());
    }
    for value in sim.custody {
        hasher.update(&value.to_be_bytes());
    }
}

fn completion(
    actor: &DreggIdentity,
    revision: u64,
    root: [u8; 32],
    sim: &Sim,
    receipt: &TurnReceipt,
) -> NativeDescentCompletion {
    let banked_relics: Vec<usize> = sim
        .custody
        .iter()
        .enumerate()
        .filter_map(|(relic, custody)| (*custody == BANKED).then_some(relic))
        .collect();
    NativeDescentCompletion {
        actor: actor.clone(),
        revision,
        root,
        settlement_receipt_hash: receipt.receipt_hash(),
        crowned: banked_relics.contains(&0),
        banked_relics,
    }
}

fn relic_label(relic: usize) -> String {
    match relic {
        0 => "Take the Crown of the Deep".to_string(),
        1..=3 => format!("Take the key-relic for way {}", relic + 1),
        _ => format!("Take treasure relic {relic}"),
    }
}

fn relics_with_custody(sim: &Sim, wanted: u64) -> String {
    let names: Vec<String> = sim
        .custody
        .iter()
        .enumerate()
        .filter_map(|(relic, custody)| (*custody == wanted).then(|| relic_label(relic)))
        .collect();
    if names.is_empty() {
        "none".to_string()
    } else {
        names.join(" · ")
    }
}

fn short_digest(digest: [u8; 32]) -> String {
    digest[..6]
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}
