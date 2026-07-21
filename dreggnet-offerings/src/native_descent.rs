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
#[cfg(feature = "private-preference-operation")]
use dungeon_on_dregg::private_preference::{
    PrivatePartyDecision, PrivatePreferenceReceipt, PrivatePreferenceSession,
};
#[cfg(feature = "private-raid-operation")]
use dungeon_on_dregg::private_raid::{
    RaidAssignmentReceipt, RaidAssignmentSession, RaidPartyAssignment,
};
use spween_dregg::WorldError;

use crate::{
    Action, DreggIdentity, Offering, OfferingError, Outcome, RecordVerify, RunCost, SessionConfig,
    Surface, VerifyReport,
};
#[cfg(any(
    feature = "private-preference-operation",
    feature = "private-raid-operation"
))]
use crate::{
    BinaryOperationDescriptor, BinaryOperationError, BinaryOperationReceipt,
    BinaryOperationReplayMaterial,
};

/// Hard bound for one hosted run journal. The perfect crowned run is 18 moves.
pub const MAX_NATIVE_DESCENT_EVENTS: usize = 128;
const MAX_ACTOR_BYTES: usize = 512;

const GENESIS_ROOT_DOMAIN: &str = "dregg.native-descent.genesis.v1";
const EVENT_ROOT_DOMAIN: &str = "dregg.native-descent.event.v1";

#[cfg(any(
    feature = "private-preference-operation",
    feature = "private-raid-operation"
))]
const PRIVATE_OPERATION_WIRE_MAGIC: [u8; 8] = *b"DREGGNDO";
#[cfg(any(
    feature = "private-preference-operation",
    feature = "private-raid-operation"
))]
const PRIVATE_OPERATION_WIRE_VERSION: u8 = 1;
#[cfg(any(
    feature = "private-preference-operation",
    feature = "private-raid-operation"
))]
const MAX_NATIVE_DESCENT_PRIVATE_OPERATION_BYTES: usize = 8 * 1024 * 1024;
#[cfg(any(
    feature = "private-preference-operation",
    feature = "private-raid-operation"
))]
const BABYBEAR_P: u64 = 2_013_265_921;

#[cfg(feature = "private-preference-operation")]
pub const NATIVE_DESCENT_PRIVATE_PREFERENCE_OPERATION: &str = "descent.private-party-preference.v1";
#[cfg(feature = "private-preference-operation")]
pub const NATIVE_DESCENT_PRIVATE_PREFERENCE_MEDIA_TYPE: &str =
    "application/vnd.dregg.native-descent.private-party-preference.v1+binary";
#[cfg(feature = "private-preference-operation")]
pub const NATIVE_DESCENT_PRIVATE_PREFERENCE_DISCLOSURE: &str = "A Lean-authored HidingFri proof aggregates four producer-private score ballots and reveals only the faithful ballot root and winning party plan. The canonical request binds that proof to this native Descent's authenticated player, exact revision, and exact journal root; stale, cross-player, and cross-root reuse refuses. The Tier-1 producer sees all ballots, while the durable journal retains only the public binding and opaque hiding proof.";

#[cfg(feature = "private-raid-operation")]
pub const NATIVE_DESCENT_PRIVATE_RAID_OPERATION: &str = "descent.private-raid-assignment.v1";
#[cfg(feature = "private-raid-operation")]
pub const NATIVE_DESCENT_PRIVATE_RAID_MEDIA_TYPE: &str =
    "application/vnd.dregg.native-descent.private-raid-assignment.v1+binary";
#[cfg(feature = "private-raid-operation")]
pub const NATIVE_DESCENT_PRIVATE_RAID_DISCLOSURE: &str = "A Lean-authored HidingFri proof publishes the globally optimal admissible four-seat raid-role permutation while keeping the producer's suitability scores and admissibility matrix private. The canonical request binds that proof to this native Descent's authenticated player, exact revision, and exact journal root; stale, cross-player, and cross-root reuse refuses. This is Tier-1 proof production, not distributed private-input assembly.";

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

/// Public identity of one exact private-party decision point in a native
/// Descent. The proof's field-sized `session` is derived from all three fields,
/// while the canonical operation envelope carries them losslessly. The hash
/// derivation is therefore domain separation for the underlying proof; this
/// exact context equality is the cross-session/revision replay gate.
#[cfg(any(
    feature = "private-preference-operation",
    feature = "private-raid-operation"
))]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativeDescentPrivateContext {
    pub actor: DreggIdentity,
    pub revision: u64,
    pub root: [u8; 32],
}

/// One accepted shielded party preference, bound to the native session head
/// at which it landed. The retained request contains only public context,
/// public result fields, the pinned verifier identity, and opaque proof bytes.
#[cfg(feature = "private-preference-operation")]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativeDescentPrivatePreference {
    context: NativeDescentPrivateContext,
    decision: PrivatePartyDecision,
    receipt_id: [u8; 32],
    canonical_request: Vec<u8>,
}

#[cfg(feature = "private-preference-operation")]
impl NativeDescentPrivatePreference {
    pub fn context(&self) -> &NativeDescentPrivateContext {
        &self.context
    }

    pub const fn decision(&self) -> PrivatePartyDecision {
        self.decision
    }

    pub const fn receipt_id(&self) -> [u8; 32] {
        self.receipt_id
    }
}

/// One accepted shielded raid assignment, bound to the native session head at
/// which it landed. Scores and the admissibility matrix are absent.
#[cfg(feature = "private-raid-operation")]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativeDescentPrivateRaid {
    context: NativeDescentPrivateContext,
    assignment: RaidPartyAssignment,
    receipt_id: [u8; 32],
    canonical_request: Vec<u8>,
}

#[cfg(feature = "private-raid-operation")]
impl NativeDescentPrivateRaid {
    pub fn context(&self) -> &NativeDescentPrivateContext {
        &self.context
    }

    pub const fn assignment(&self) -> RaidPartyAssignment {
        self.assignment
    }

    pub const fn receipt_id(&self) -> [u8; 32] {
        self.receipt_id
    }
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
    #[cfg(feature = "private-preference-operation")]
    pub private_preference: Option<NativeDescentPrivatePreference>,
    #[cfg(feature = "private-raid-operation")]
    pub private_raid: Option<NativeDescentPrivateRaid>,
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
    #[cfg(feature = "private-preference-operation")]
    private_preference: Option<NativeDescentPrivatePreference>,
    #[cfg(feature = "private-raid-operation")]
    private_raid: Option<NativeDescentPrivateRaid>,
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

    /// Exact proof-production context for the current committed native head.
    /// An unclaimed session has no authenticated party and therefore exposes
    /// no private-party operation.
    #[cfg(any(
        feature = "private-preference-operation",
        feature = "private-raid-operation"
    ))]
    pub fn private_operation_context(&self) -> Option<NativeDescentPrivateContext> {
        Some(NativeDescentPrivateContext {
            actor: self.actor.clone()?,
            revision: self.revision(),
            root: self.root,
        })
    }

    #[cfg(feature = "private-preference-operation")]
    pub fn private_preference(&self) -> Option<&NativeDescentPrivatePreference> {
        self.private_preference.as_ref()
    }

    #[cfg(feature = "private-raid-operation")]
    pub fn private_raid(&self) -> Option<&NativeDescentPrivateRaid> {
        self.private_raid.as_ref()
    }

    pub fn export_record(&self) -> NativeDescentRecord {
        NativeDescentRecord {
            seed: self.seed,
            actor: self.actor.clone(),
            events: self.events.clone(),
            root: self.root,
            checkpoint: self.checkpoint.clone(),
            completion: self.completion.clone(),
            #[cfg(feature = "private-preference-operation")]
            private_preference: self.private_preference.clone(),
            #[cfg(feature = "private-raid-operation")]
            private_raid: self.private_raid.clone(),
        }
    }
}

/// Canonical BabyBear proof-session id for a private preference at this exact
/// native Descent head. The lossless actor/revision/root tuple remains in the
/// operation envelope and is compared byte-for-byte on admission.
#[cfg(feature = "private-preference-operation")]
pub fn native_descent_private_preference_proof_session(
    context: &NativeDescentPrivateContext,
) -> u32 {
    private_proof_session(
        "dregg.native-descent.private-preference.proof-session.v1",
        context,
    )
}

/// Wrap one already-produced hiding preference receipt in the canonical,
/// exact native-session context expected by the binary operation.
#[cfg(feature = "private-preference-operation")]
pub fn encode_native_descent_private_preference(
    context: &NativeDescentPrivateContext,
    receipt: &PrivatePreferenceReceipt,
) -> Result<Vec<u8>, BinaryOperationError> {
    if receipt.statement().session != native_descent_private_preference_proof_session(context) {
        return Err(BinaryOperationError::Refused(
            "private preference proof session is not derived from the supplied native Descent context"
                .to_string(),
        ));
    }
    let proof = receipt
        .to_postcard()
        .map_err(|error| BinaryOperationError::Malformed(error.to_string()))?;
    encode_private_operation(PrivateOperationKind::Preference, context, &proof)
}

/// Canonical BabyBear proof-session id for a private raid assignment at this
/// exact native Descent head.
#[cfg(feature = "private-raid-operation")]
pub fn native_descent_private_raid_proof_session(context: &NativeDescentPrivateContext) -> u32 {
    private_proof_session(
        "dregg.native-descent.private-raid.proof-session.v1",
        context,
    )
}

/// Wrap one already-produced hiding raid receipt in the canonical, exact
/// native-session context expected by the binary operation.
#[cfg(feature = "private-raid-operation")]
pub fn encode_native_descent_private_raid(
    context: &NativeDescentPrivateContext,
    receipt: &RaidAssignmentReceipt,
) -> Result<Vec<u8>, BinaryOperationError> {
    if receipt.statement().session != native_descent_private_raid_proof_session(context) {
        return Err(BinaryOperationError::Refused(
            "private raid proof session is not derived from the supplied native Descent context"
                .to_string(),
        ));
    }
    let proof = receipt
        .to_postcard()
        .map_err(|error| BinaryOperationError::Malformed(error.to_string()))?;
    encode_private_operation(PrivateOperationKind::Raid, context, &proof)
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
            || {
                #[cfg(feature = "private-preference-operation")]
                {
                    record.private_preference != session.private_preference
                }
                #[cfg(not(feature = "private-preference-operation"))]
                {
                    false
                }
            }
            || {
                #[cfg(feature = "private-raid-operation")]
                {
                    record.private_raid != session.private_raid
                }
                #[cfg(not(feature = "private-raid-operation"))]
                {
                    false
                }
            }
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
            #[cfg(feature = "private-preference-operation")]
            private_preference: None,
            #[cfg(feature = "private-raid-operation")]
            private_raid: None,
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
        #[cfg(feature = "private-preference-operation")]
        if let Some(preference) = &session.private_preference {
            children.push(ViewNode::Section {
                title: "Shielded party preference".to_string(),
                tag: "genuine".to_string(),
                children: vec![
                    ViewNode::Text(format!(
                        "plan {} won at revision {} · root {}",
                        preference.decision.winner(),
                        preference.context.revision,
                        short_digest(preference.context.root)
                    )),
                    ViewNode::Text(
                        "ballots and aggregate scores remain hidden behind the verified receipt"
                            .to_string(),
                    ),
                ],
            });
        }
        #[cfg(feature = "private-raid-operation")]
        if let Some(raid) = &session.private_raid {
            children.push(ViewNode::Section {
                title: "Shielded raid assignment".to_string(),
                tag: "genuine".to_string(),
                children: vec![
                    ViewNode::Text(format!(
                        "roles {:?} at revision {} · root {}",
                        raid.assignment.roles(),
                        raid.context.revision,
                        short_digest(raid.context.root)
                    )),
                    ViewNode::Text(
                        "private suitability scores and admissibility remain hidden".to_string(),
                    ),
                ],
            });
        }
        Surface(ViewNode::Section {
            title: "The Descent — Lean-authored".to_string(),
            tag: "accent".to_string(),
            children,
        })
    }

    #[cfg(any(
        feature = "private-preference-operation",
        feature = "private-raid-operation"
    ))]
    fn binary_operations(&self, session: &Self::Session) -> Vec<BinaryOperationDescriptor> {
        let Some(context) = session.private_operation_context() else {
            return Vec::new();
        };
        let head = format!(
            "revision {} · root {} · actor {}",
            context.revision,
            short_digest(context.root),
            context.actor.as_str()
        );
        let mut operations = Vec::new();
        #[cfg(feature = "private-preference-operation")]
        if session.private_preference.is_none() {
            operations.push(BinaryOperationDescriptor {
                name: NATIVE_DESCENT_PRIVATE_PREFERENCE_OPERATION.to_string(),
                title: format!("Prove a shielded party preference for {head}"),
                input_media_type: NATIVE_DESCENT_PRIVATE_PREFERENCE_MEDIA_TYPE.to_string(),
                max_input_bytes: MAX_NATIVE_DESCENT_PRIVATE_OPERATION_BYTES,
                disclosure: NATIVE_DESCENT_PRIVATE_PREFERENCE_DISCLOSURE.to_string(),
            });
        }
        #[cfg(feature = "private-raid-operation")]
        if session.private_raid.is_none() {
            operations.push(BinaryOperationDescriptor {
                name: NATIVE_DESCENT_PRIVATE_RAID_OPERATION.to_string(),
                title: format!("Prove a shielded raid assignment for {head}"),
                input_media_type: NATIVE_DESCENT_PRIVATE_RAID_MEDIA_TYPE.to_string(),
                max_input_bytes: MAX_NATIVE_DESCENT_PRIVATE_OPERATION_BYTES,
                disclosure: NATIVE_DESCENT_PRIVATE_RAID_DISCLOSURE.to_string(),
            });
        }
        operations
    }

    #[cfg(any(
        feature = "private-preference-operation",
        feature = "private-raid-operation"
    ))]
    fn binary_operation_replay_material(
        &self,
        session: &Self::Session,
        name: &str,
        payload: &[u8],
    ) -> Result<Option<BinaryOperationReplayMaterial>, BinaryOperationError> {
        #[cfg(feature = "private-preference-operation")]
        if name == NATIVE_DESCENT_PRIVATE_PREFERENCE_OPERATION {
            let (_, _, canonical) = validate_private_preference_request(session, payload)?;
            return Ok(Some(BinaryOperationReplayMaterial::new(
                canonical,
                NATIVE_DESCENT_PRIVATE_PREFERENCE_DISCLOSURE,
            )));
        }
        #[cfg(feature = "private-raid-operation")]
        if name == NATIVE_DESCENT_PRIVATE_RAID_OPERATION {
            let (_, _, canonical) = validate_private_raid_request(session, payload)?;
            return Ok(Some(BinaryOperationReplayMaterial::new(
                canonical,
                NATIVE_DESCENT_PRIVATE_RAID_DISCLOSURE,
            )));
        }
        Err(BinaryOperationError::UnknownOperation(name.to_string()))
    }

    #[cfg(any(
        feature = "private-preference-operation",
        feature = "private-raid-operation"
    ))]
    fn invoke_binary_operation(
        &self,
        session: &mut Self::Session,
        name: &str,
        payload: &[u8],
        actor: DreggIdentity,
    ) -> Result<BinaryOperationReceipt, BinaryOperationError> {
        #[cfg(feature = "private-preference-operation")]
        if name == NATIVE_DESCENT_PRIVATE_PREFERENCE_OPERATION {
            return apply_private_preference(session, payload, actor);
        }
        #[cfg(feature = "private-raid-operation")]
        if name == NATIVE_DESCENT_PRIVATE_RAID_OPERATION {
            return apply_private_raid(session, payload, actor);
        }
        Err(BinaryOperationError::UnknownOperation(name.to_string()))
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
    #[cfg(any(
        feature = "private-preference-operation",
        feature = "private-raid-operation"
    ))]
    let genesis = root;
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
    #[cfg(feature = "private-preference-operation")]
    let private_preference = match &record.private_preference {
        Some(expected) => Some(replay_private_preference(record, genesis, expected)?),
        None => None,
    };
    #[cfg(feature = "private-raid-operation")]
    let private_raid = match &record.private_raid {
        Some(expected) => Some(replay_private_raid(record, genesis, expected)?),
        None => None,
    };
    Ok(NativeDescentSession {
        seed: record.seed,
        game,
        actor,
        events: record.events.clone(),
        root,
        checkpoint,
        completion: derived_completion,
        #[cfg(feature = "private-preference-operation")]
        private_preference,
        #[cfg(feature = "private-raid-operation")]
        private_raid,
    })
}

#[cfg(any(
    feature = "private-preference-operation",
    feature = "private-raid-operation"
))]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum PrivateOperationKind {
    Preference = 1,
    Raid = 2,
}

#[cfg(any(
    feature = "private-preference-operation",
    feature = "private-raid-operation"
))]
impl PrivateOperationKind {
    fn from_byte(byte: u8) -> Result<Self, BinaryOperationError> {
        match byte {
            1 => Ok(Self::Preference),
            2 => Ok(Self::Raid),
            other => Err(BinaryOperationError::Malformed(format!(
                "unknown native Descent private-operation kind {other}"
            ))),
        }
    }
}

#[cfg(any(
    feature = "private-preference-operation",
    feature = "private-raid-operation"
))]
struct PrivateOperationEnvelope {
    context: NativeDescentPrivateContext,
    proof: Vec<u8>,
}

#[cfg(any(
    feature = "private-preference-operation",
    feature = "private-raid-operation"
))]
fn private_proof_session(domain: &str, context: &NativeDescentPrivateContext) -> u32 {
    let mut hasher = blake3::Hasher::new_derive_key(domain);
    hasher.update(&(context.actor.as_str().len() as u64).to_be_bytes());
    hasher.update(context.actor.as_str().as_bytes());
    hasher.update(&context.revision.to_be_bytes());
    hasher.update(&context.root);
    let mut low = [0u8; 8];
    low.copy_from_slice(&hasher.finalize().as_bytes()[..8]);
    (u64::from_le_bytes(low) % BABYBEAR_P) as u32
}

#[cfg(any(
    feature = "private-preference-operation",
    feature = "private-raid-operation"
))]
fn encode_private_operation(
    kind: PrivateOperationKind,
    context: &NativeDescentPrivateContext,
    proof: &[u8],
) -> Result<Vec<u8>, BinaryOperationError> {
    if !valid_actor(&context.actor) {
        return Err(BinaryOperationError::Malformed(
            "native Descent private-operation actor is empty or overlong".to_string(),
        ));
    }
    if context.revision == 0 {
        return Err(BinaryOperationError::Refused(
            "native Descent private operations require an actor-bound landed move".to_string(),
        ));
    }
    if proof.is_empty() {
        return Err(BinaryOperationError::Malformed(
            "native Descent private-operation proof receipt is empty".to_string(),
        ));
    }
    let actor_len = u16::try_from(context.actor.as_str().len()).map_err(|_| {
        BinaryOperationError::Malformed(
            "native Descent private-operation actor length does not fit the wire".to_string(),
        )
    })?;
    let proof_len = u64::try_from(proof.len()).map_err(|_| {
        BinaryOperationError::Malformed(
            "native Descent private-operation proof length does not fit the wire".to_string(),
        )
    })?;
    let mut out = Vec::with_capacity(
        PRIVATE_OPERATION_WIRE_MAGIC.len()
            + 1
            + 1
            + 8
            + 32
            + 2
            + usize::from(actor_len)
            + 8
            + proof.len(),
    );
    out.extend_from_slice(&PRIVATE_OPERATION_WIRE_MAGIC);
    out.push(PRIVATE_OPERATION_WIRE_VERSION);
    out.push(kind as u8);
    out.extend_from_slice(&context.revision.to_be_bytes());
    out.extend_from_slice(&context.root);
    out.extend_from_slice(&actor_len.to_be_bytes());
    out.extend_from_slice(context.actor.as_str().as_bytes());
    out.extend_from_slice(&proof_len.to_be_bytes());
    out.extend_from_slice(proof);
    if out.len() > MAX_NATIVE_DESCENT_PRIVATE_OPERATION_BYTES {
        return Err(BinaryOperationError::Malformed(format!(
            "native Descent private-operation request is {} bytes; maximum is {MAX_NATIVE_DESCENT_PRIVATE_OPERATION_BYTES}",
            out.len()
        )));
    }
    Ok(out)
}

#[cfg(any(
    feature = "private-preference-operation",
    feature = "private-raid-operation"
))]
fn decode_private_operation(
    expected_kind: PrivateOperationKind,
    bytes: &[u8],
) -> Result<PrivateOperationEnvelope, BinaryOperationError> {
    if bytes.len() > MAX_NATIVE_DESCENT_PRIVATE_OPERATION_BYTES {
        return Err(BinaryOperationError::Malformed(format!(
            "native Descent private-operation request is {} bytes; maximum is {MAX_NATIVE_DESCENT_PRIVATE_OPERATION_BYTES}",
            bytes.len()
        )));
    }
    let mut reader = PrivateOperationReader::new(bytes);
    if reader.array::<8>()? != PRIVATE_OPERATION_WIRE_MAGIC {
        return Err(BinaryOperationError::Malformed(
            "native Descent private-operation wire magic mismatch".to_string(),
        ));
    }
    let version = reader.byte()?;
    if version != PRIVATE_OPERATION_WIRE_VERSION {
        return Err(BinaryOperationError::Malformed(format!(
            "unsupported native Descent private-operation wire version {version}"
        )));
    }
    let actual_kind = PrivateOperationKind::from_byte(reader.byte()?)?;
    if actual_kind != expected_kind {
        return Err(BinaryOperationError::Malformed(
            "private-operation payload kind does not match the addressed operation".to_string(),
        ));
    }
    let revision = reader.u64()?;
    let root = reader.array::<32>()?;
    let actor_len = usize::from(reader.u16()?);
    if actor_len == 0 || actor_len > MAX_ACTOR_BYTES {
        return Err(BinaryOperationError::Malformed(format!(
            "native Descent private-operation actor length {actor_len} is invalid"
        )));
    }
    let actor_bytes = reader.bytes(actor_len)?;
    let actor = std::str::from_utf8(actor_bytes)
        .map_err(|_| {
            BinaryOperationError::Malformed(
                "native Descent private-operation actor is not UTF-8".to_string(),
            )
        })?
        .to_string();
    let proof_len = usize::try_from(reader.u64()?).map_err(|_| {
        BinaryOperationError::Malformed(
            "native Descent private-operation proof length does not fit usize".to_string(),
        )
    })?;
    if proof_len == 0 || proof_len > MAX_NATIVE_DESCENT_PRIVATE_OPERATION_BYTES {
        return Err(BinaryOperationError::Malformed(format!(
            "native Descent private-operation proof length {proof_len} is invalid"
        )));
    }
    let proof = reader.bytes(proof_len)?.to_vec();
    reader.finish()?;
    let envelope = PrivateOperationEnvelope {
        context: NativeDescentPrivateContext {
            actor: DreggIdentity(actor),
            revision,
            root,
        },
        proof,
    };
    let canonical = encode_private_operation(expected_kind, &envelope.context, &envelope.proof)?;
    if canonical != bytes {
        return Err(BinaryOperationError::Malformed(
            "native Descent private-operation request is not canonically encoded".to_string(),
        ));
    }
    Ok(envelope)
}

#[cfg(any(
    feature = "private-preference-operation",
    feature = "private-raid-operation"
))]
fn validate_live_private_context(
    session: &NativeDescentSession,
    claimed: &NativeDescentPrivateContext,
) -> Result<(), BinaryOperationError> {
    let expected = session.private_operation_context().ok_or_else(|| {
        BinaryOperationError::Refused(
            "native Descent private operations require the first real move to bind a player"
                .to_string(),
        )
    })?;
    if claimed.actor != expected.actor {
        return Err(BinaryOperationError::Refused(format!(
            "private operation names actor {}, but this Descent is bound to {}",
            claimed.actor.as_str(),
            expected.actor.as_str()
        )));
    }
    if claimed.revision != expected.revision {
        return Err(BinaryOperationError::Refused(format!(
            "stale native Descent private-operation revision: expected {}, claimed {}",
            expected.revision, claimed.revision
        )));
    }
    if claimed.root != expected.root {
        return Err(BinaryOperationError::Refused(format!(
            "wrong native Descent private-operation root: expected {}, claimed {}",
            hex_digest(expected.root),
            hex_digest(claimed.root)
        )));
    }
    Ok(())
}

#[cfg(feature = "private-preference-operation")]
fn validate_private_preference_request(
    session: &NativeDescentSession,
    payload: &[u8],
) -> Result<
    (
        NativeDescentPrivateContext,
        PrivatePreferenceReceipt,
        Vec<u8>,
    ),
    BinaryOperationError,
> {
    let envelope = decode_private_operation(PrivateOperationKind::Preference, payload)?;
    validate_live_private_context(session, &envelope.context)?;
    if session.private_preference.is_some() {
        return Err(BinaryOperationError::Refused(
            "this native Descent already has a private party preference".to_string(),
        ));
    }
    let receipt = PrivatePreferenceReceipt::from_postcard(&envelope.proof)
        .map_err(|error| BinaryOperationError::Malformed(error.to_string()))?;
    let canonical_receipt = receipt
        .to_postcard()
        .map_err(|error| BinaryOperationError::Malformed(error.to_string()))?;
    if canonical_receipt != envelope.proof {
        return Err(BinaryOperationError::Malformed(
            "private preference receipt is not canonically encoded".to_string(),
        ));
    }
    let expected_session = native_descent_private_preference_proof_session(&envelope.context);
    if receipt.statement().session != expected_session {
        return Err(BinaryOperationError::Refused(format!(
            "private preference proof session mismatch: expected {expected_session}, claimed {}",
            receipt.statement().session
        )));
    }
    Ok((envelope.context, receipt, payload.to_vec()))
}

#[cfg(feature = "private-preference-operation")]
fn apply_private_preference(
    session: &mut NativeDescentSession,
    payload: &[u8],
    actor: DreggIdentity,
) -> Result<BinaryOperationReceipt, BinaryOperationError> {
    let (context, proof_receipt, canonical_request) =
        validate_private_preference_request(session, payload)?;
    if actor != context.actor {
        return Err(BinaryOperationError::Refused(format!(
            "private preference was bound to actor {}; {} submitted it",
            context.actor.as_str(),
            actor.as_str()
        )));
    }
    let mut verifier =
        PrivatePreferenceSession::new(native_descent_private_preference_proof_session(&context))
            .map_err(|error| BinaryOperationError::Refused(error.to_string()))?;
    let decision = verifier
        .accept(&proof_receipt)
        .map_err(|error| BinaryOperationError::Refused(error.to_string()))?;
    let receipt_id = private_operation_receipt_id(
        "dregg.native-descent.private-preference.receipt.v1",
        &canonical_request,
    );
    session.private_preference = Some(NativeDescentPrivatePreference {
        context: context.clone(),
        decision,
        receipt_id,
        canonical_request,
    });
    Ok(BinaryOperationReceipt {
        operation: NATIVE_DESCENT_PRIVATE_PREFERENCE_OPERATION.to_string(),
        receipt_id,
        public_fields: vec![
            ("actor".to_string(), context.actor.as_str().to_string()),
            ("revision".to_string(), context.revision.to_string()),
            ("root".to_string(), hex_digest(context.root)),
            ("proofSession".to_string(), decision.session().to_string()),
            (
                "ballotRoot".to_string(),
                format!("{:?}", decision.ballot_root()),
            ),
            ("winner".to_string(), decision.winner().to_string()),
        ],
    })
}

#[cfg(feature = "private-raid-operation")]
fn validate_private_raid_request(
    session: &NativeDescentSession,
    payload: &[u8],
) -> Result<(NativeDescentPrivateContext, RaidAssignmentReceipt, Vec<u8>), BinaryOperationError> {
    let envelope = decode_private_operation(PrivateOperationKind::Raid, payload)?;
    validate_live_private_context(session, &envelope.context)?;
    if session.private_raid.is_some() {
        return Err(BinaryOperationError::Refused(
            "this native Descent already has a private raid assignment".to_string(),
        ));
    }
    let receipt = RaidAssignmentReceipt::from_postcard(&envelope.proof)
        .map_err(|error| BinaryOperationError::Malformed(error.to_string()))?;
    let canonical_receipt = receipt
        .to_postcard()
        .map_err(|error| BinaryOperationError::Malformed(error.to_string()))?;
    if canonical_receipt != envelope.proof {
        return Err(BinaryOperationError::Malformed(
            "private raid receipt is not canonically encoded".to_string(),
        ));
    }
    let expected_session = native_descent_private_raid_proof_session(&envelope.context);
    if receipt.statement().session != expected_session {
        return Err(BinaryOperationError::Refused(format!(
            "private raid proof session mismatch: expected {expected_session}, claimed {}",
            receipt.statement().session
        )));
    }
    Ok((envelope.context, receipt, payload.to_vec()))
}

#[cfg(feature = "private-raid-operation")]
fn apply_private_raid(
    session: &mut NativeDescentSession,
    payload: &[u8],
    actor: DreggIdentity,
) -> Result<BinaryOperationReceipt, BinaryOperationError> {
    let (context, proof_receipt, canonical_request) =
        validate_private_raid_request(session, payload)?;
    if actor != context.actor {
        return Err(BinaryOperationError::Refused(format!(
            "private raid assignment was bound to actor {}; {} submitted it",
            context.actor.as_str(),
            actor.as_str()
        )));
    }
    let mut verifier =
        RaidAssignmentSession::new(native_descent_private_raid_proof_session(&context))
            .map_err(|error| BinaryOperationError::Refused(error.to_string()))?;
    let assignment = verifier
        .accept(&proof_receipt)
        .map_err(|error| BinaryOperationError::Refused(error.to_string()))?;
    let receipt_id = private_operation_receipt_id(
        "dregg.native-descent.private-raid.receipt.v1",
        &canonical_request,
    );
    session.private_raid = Some(NativeDescentPrivateRaid {
        context: context.clone(),
        assignment,
        receipt_id,
        canonical_request,
    });
    Ok(BinaryOperationReceipt {
        operation: NATIVE_DESCENT_PRIVATE_RAID_OPERATION.to_string(),
        receipt_id,
        public_fields: vec![
            ("actor".to_string(), context.actor.as_str().to_string()),
            ("revision".to_string(), context.revision.to_string()),
            ("root".to_string(), hex_digest(context.root)),
            ("proofSession".to_string(), assignment.session().to_string()),
            (
                "inputRoot".to_string(),
                format!("{:?}", assignment.input_root()),
            ),
            ("roles".to_string(), format!("{:?}", assignment.roles())),
        ],
    })
}

#[cfg(feature = "private-preference-operation")]
fn replay_private_preference(
    record: &NativeDescentRecord,
    genesis: [u8; 32],
    expected: &NativeDescentPrivatePreference,
) -> Result<NativeDescentPrivatePreference, String> {
    validate_recorded_private_context(record, genesis, &expected.context)?;
    let envelope = decode_private_operation(
        PrivateOperationKind::Preference,
        &expected.canonical_request,
    )
    .map_err(|error| error.to_string())?;
    if envelope.context != expected.context {
        return Err("private preference envelope substituted its native context".to_string());
    }
    let receipt = PrivatePreferenceReceipt::from_postcard(&envelope.proof)
        .map_err(|error| error.to_string())?;
    if receipt.to_postcard().map_err(|error| error.to_string())? != envelope.proof {
        return Err("private preference replay receipt is not canonical".to_string());
    }
    let mut verifier = PrivatePreferenceSession::new(
        native_descent_private_preference_proof_session(&expected.context),
    )
    .map_err(|error| error.to_string())?;
    let decision = verifier
        .accept(&receipt)
        .map_err(|error| error.to_string())?;
    let actual = NativeDescentPrivatePreference {
        context: expected.context.clone(),
        decision,
        receipt_id: private_operation_receipt_id(
            "dregg.native-descent.private-preference.receipt.v1",
            &expected.canonical_request,
        ),
        canonical_request: expected.canonical_request.clone(),
    };
    if &actual != expected {
        return Err("private preference record differs from exact proof replay".to_string());
    }
    Ok(actual)
}

#[cfg(feature = "private-raid-operation")]
fn replay_private_raid(
    record: &NativeDescentRecord,
    genesis: [u8; 32],
    expected: &NativeDescentPrivateRaid,
) -> Result<NativeDescentPrivateRaid, String> {
    validate_recorded_private_context(record, genesis, &expected.context)?;
    let envelope =
        decode_private_operation(PrivateOperationKind::Raid, &expected.canonical_request)
            .map_err(|error| error.to_string())?;
    if envelope.context != expected.context {
        return Err("private raid envelope substituted its native context".to_string());
    }
    let receipt =
        RaidAssignmentReceipt::from_postcard(&envelope.proof).map_err(|error| error.to_string())?;
    if receipt.to_postcard().map_err(|error| error.to_string())? != envelope.proof {
        return Err("private raid replay receipt is not canonical".to_string());
    }
    let mut verifier =
        RaidAssignmentSession::new(native_descent_private_raid_proof_session(&expected.context))
            .map_err(|error| error.to_string())?;
    let assignment = verifier
        .accept(&receipt)
        .map_err(|error| error.to_string())?;
    let actual = NativeDescentPrivateRaid {
        context: expected.context.clone(),
        assignment,
        receipt_id: private_operation_receipt_id(
            "dregg.native-descent.private-raid.receipt.v1",
            &expected.canonical_request,
        ),
        canonical_request: expected.canonical_request.clone(),
    };
    if &actual != expected {
        return Err("private raid record differs from exact proof replay".to_string());
    }
    Ok(actual)
}

#[cfg(any(
    feature = "private-preference-operation",
    feature = "private-raid-operation"
))]
fn validate_recorded_private_context(
    record: &NativeDescentRecord,
    genesis: [u8; 32],
    context: &NativeDescentPrivateContext,
) -> Result<(), String> {
    if record.actor.as_ref() != Some(&context.actor) {
        return Err("private operation substituted the native Descent actor".to_string());
    }
    let expected_root = if context.revision == 0 {
        genesis
    } else {
        let index = usize::try_from(context.revision - 1)
            .map_err(|_| "private operation revision does not fit usize".to_string())?;
        record
            .events
            .get(index)
            .map(|event| event.root)
            .ok_or_else(|| "private operation names an absent native revision".to_string())?
    };
    if context.revision == 0 || context.root != expected_root {
        return Err("private operation is not bound to its exact recorded native root".to_string());
    }
    Ok(())
}

#[cfg(any(
    feature = "private-preference-operation",
    feature = "private-raid-operation"
))]
fn private_operation_receipt_id(domain: &str, canonical_request: &[u8]) -> [u8; 32] {
    *blake3::Hasher::new_derive_key(domain)
        .update(canonical_request)
        .finalize()
        .as_bytes()
}

#[cfg(any(
    feature = "private-preference-operation",
    feature = "private-raid-operation"
))]
struct PrivateOperationReader<'a> {
    bytes: &'a [u8],
    position: usize,
}

#[cfg(any(
    feature = "private-preference-operation",
    feature = "private-raid-operation"
))]
impl<'a> PrivateOperationReader<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, position: 0 }
    }

    fn array<const N: usize>(&mut self) -> Result<[u8; N], BinaryOperationError> {
        let end = self.position.checked_add(N).ok_or_else(|| {
            BinaryOperationError::Malformed(
                "native Descent private-operation wire position overflow".to_string(),
            )
        })?;
        let bytes = self.bytes.get(self.position..end).ok_or_else(|| {
            BinaryOperationError::Malformed(
                "truncated native Descent private-operation field".to_string(),
            )
        })?;
        self.position = end;
        Ok(bytes
            .try_into()
            .expect("private-operation field length checked"))
    }

    fn byte(&mut self) -> Result<u8, BinaryOperationError> {
        Ok(self.array::<1>()?[0])
    }

    fn u16(&mut self) -> Result<u16, BinaryOperationError> {
        Ok(u16::from_be_bytes(self.array()?))
    }

    fn u64(&mut self) -> Result<u64, BinaryOperationError> {
        Ok(u64::from_be_bytes(self.array()?))
    }

    fn bytes(&mut self, len: usize) -> Result<&'a [u8], BinaryOperationError> {
        let end = self.position.checked_add(len).ok_or_else(|| {
            BinaryOperationError::Malformed(
                "native Descent private-operation wire position overflow".to_string(),
            )
        })?;
        let bytes = self.bytes.get(self.position..end).ok_or_else(|| {
            BinaryOperationError::Malformed(
                "truncated native Descent private-operation bytes".to_string(),
            )
        })?;
        self.position = end;
        Ok(bytes)
    }

    fn finish(self) -> Result<(), BinaryOperationError> {
        if self.position == self.bytes.len() {
            Ok(())
        } else {
            Err(BinaryOperationError::Malformed(
                "trailing bytes after native Descent private-operation object".to_string(),
            ))
        }
    }
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

#[cfg(any(
    feature = "private-preference-operation",
    feature = "private-raid-operation"
))]
fn hex_digest(digest: [u8; 32]) -> String {
    digest.iter().map(|byte| format!("{byte:02x}")).collect()
}
