//! **Offering #0 — the dungeon.** The `discord-bot/fiction.rs` `RealSession` logic, factored
//! out of the Discord frontend into a [`DungeonOffering`] that implements the frontend-agnostic
//! [`Offering`] trait over `dungeon_on_dregg`'s real `WorldCell`.
//!
//! What was Discord-coupled in `fiction.rs` (serenity embeds, ballot buttons, the round/tally,
//! the narrator gate) splits cleanly:
//! - the **substrate seam** — deploy the Keep, run genesis, apply a choice as ONE real
//!   cap-bounded turn, record the [`Playthrough`], re-verify by replay — is THIS module (the
//!   [`DungeonSession`] is the old `RealSession`, verbatim in substance).
//! - the **ballot / tally / plurality** is the *orchestrator's* job (collective-choice); the
//!   core resolves the single typed [`Action`] the crowd picked.
//! - the **embed / buttons** is the *frontend's* job; the core renders a deos [`Surface`].
//! - the **narrator credit gate** is the *frontend's* job; the core names the [`RunCost`].
//!
//! The executor is the SOURCE OF TRUTH: a legal move lands a real `TurnReceipt`; an illegal one
//! (a killing blow past the HP floor, a second grab of a `WriteOnce` relic, climbing a one-way
//! stair, an over-budget ward) is a real `WorldError::Refused` that commits nothing — the
//! anti-ghost tooth. `verify` re-drives a fresh identically-seeded world-cell through the
//! recorded choices ([`verify_by_replay`]) and rechecks any private-result enactment against
//! its accepted session/result/actor; a forged, substituted, or reordered record fails.

use deos_view::{MenuItem, ViewNode};
use dregg_app_framework::{FieldElement, TurnReceipt, field_from_bytes};
use spween::{CompareOp, ConditionClause, ConditionExpr, PassageContent, Scene};
use spween_dregg::{StepReceipt, WorldCell, WorldError, value_to_u64, verify, verify_by_replay};

#[cfg(feature = "private-preference-operation")]
use dungeon_on_dregg::KP_PRIVATE_COUNSEL_DESCEND;
#[cfg(any(
    feature = "private-preference-operation",
    feature = "private-fair-shuffle-operation"
))]
use dungeon_on_dregg::ROOM_HALL;
#[cfg(feature = "private-fair-shuffle-operation")]
use dungeon_on_dregg::private_fair_shuffle::{
    DIGEST_WIDTH as SHUFFLE_DIGEST_WIDTH, FairCardOpening, FairShuffleAttemptOutcome,
    FairShuffleReceipt, FairShuffleTable, PARTICIPANTS as SHUFFLE_PARTICIPANTS,
};
#[cfg(feature = "private-preference-operation")]
use dungeon_on_dregg::private_preference::{
    PrivatePartyDecision, PrivatePreferenceReceipt, PrivatePreferenceSession,
};
#[cfg(feature = "private-quest-operation")]
use dungeon_on_dregg::private_quest::{
    PRIVATE_QUEST_DOMAIN, PRIVATE_QUEST_STEPS, PrivateQuestPublicHistory,
    decode_private_quest_receipt, encode_private_quest_receipt,
};
#[cfg(feature = "private-raid-operation")]
use dungeon_on_dregg::private_raid::{
    RaidAssignmentReceipt, RaidAssignmentSession, RaidPartyAssignment,
};
#[cfg(feature = "private-fair-shuffle-operation")]
use dungeon_on_dregg::{KP_PRIVATE_SHUFFLE_EVEN_INITIATIVE, KP_PRIVATE_SHUFFLE_ODD_INITIATIVE};
use dungeon_on_dregg::{deploy_keep, keep_scene};

use crate::{
    Action, CollectiveDecision, DreggIdentity, Offering, OfferingError, Outcome, RecordVerify,
    RunCost, SessionConfig, Surface, VerifyReport,
};
#[cfg(any(
    feature = "private-raid-operation",
    feature = "private-preference-operation",
    feature = "private-fair-shuffle-operation",
    feature = "private-quest-operation"
))]
use crate::{
    BinaryOperationDescriptor, BinaryOperationError, BinaryOperationReceipt,
    BinaryOperationReplayMaterial,
};

/// Re-export of the substrate **playthrough** — the public, transmissible session record the
/// [`RecordVerify`] tamper-verify seam exports and re-checks. Re-exported here so a frontend can
/// name the record type (and forge a copy in a tamper test) without depending on `spween-dregg`
/// directly.
pub use spween_dregg::{Playthrough, VerifyBreak};

/// The affordance verb every dungeon move fires — a choice on the current room's ballot. The
/// action's `arg` is the scene choice index within the current passage.
pub const TURN_CHOOSE: &str = "choose";

/// The hosted universe's display name.
pub const KEEP_NAME: &str = "The Warden's Keep";

/// The Keep's objective, stated for the party.
pub const KEEP_OBJECTIVE: &str = "trade past the gate-warden, claim the crown, descend the collapsing stair, and seize the hoard";

#[cfg(feature = "private-raid-operation")]
pub const PRIVATE_RAID_OPERATION: &str = "dungeon.private-raid-assignment.v1";
#[cfg(feature = "private-raid-operation")]
pub const PRIVATE_RAID_MEDIA_TYPE: &str =
    "application/vnd.dregg.private-raid-assignment.v1+postcard";
#[cfg(feature = "private-raid-operation")]
pub const MAX_PRIVATE_RAID_BYTES: usize = 8 * 1024 * 1024;
#[cfg(feature = "private-raid-operation")]
pub const PRIVATE_RAID_DISCLOSURE: &str = "HidingFri proves the published four-seat role permutation is admissible and globally optimal for one producer-private 4x4 score matrix. The producer sees every score and admissibility bit; this is not distributed private-input assembly or an Effect::Custom cell transition.";

#[cfg(feature = "private-preference-operation")]
pub const PRIVATE_PREFERENCE_OPERATION: &str = "dungeon.private-party-preference.v1";
#[cfg(feature = "private-preference-operation")]
pub const PRIVATE_PREFERENCE_MEDIA_TYPE: &str =
    "application/vnd.dregg.private-party-preference.v1+postcard";
#[cfg(feature = "private-preference-operation")]
pub const MAX_PRIVATE_PREFERENCE_BYTES: usize = 8 * 1024 * 1024;
#[cfg(feature = "private-preference-operation")]
pub const PRIVATE_PREFERENCE_DISCLOSURE: &str = "A Lean-authored HidingFri proof aggregates four producer-private, two-bit score ballots over four public party plans and reveals only the lowest-index winning plan plus a faithful ballot root. When the drowned-stair plan wins, its authenticated submitter may enact a one-shot two-depth route whose real world receipt commits the public result and actor. Ballots, option totals, and the winning total stay hidden; the current Tier-1 producer sees all ballots, and the hiding proof itself is reverified from the durable operation journal rather than recursively folded into the world turn.";
#[cfg(feature = "private-preference-operation")]
pub const PRIVATE_PREFERENCE_OPTIONS: [&str; 4] = [
    "assault the ash gate",
    "descend the drowned stair",
    "barter in the Dark Bazaar",
    "muster for the moon raid",
];
/// The shielded plan with an enacted Keep mechanic: a verified winner of the
/// drowned-stair plan authorizes its submitting identity to take the two-depth
/// counsel route from the hall. The ordinary stair advances only one depth.
#[cfg(feature = "private-preference-operation")]
pub const PRIVATE_PREFERENCE_DROWNED_STAIR_PLAN: usize = 1;

#[cfg(feature = "private-fair-shuffle-operation")]
pub const PRIVATE_SHUFFLE_COMMIT_OPERATION: &str = "dungeon.private-fair-shuffle.commit.v1";
#[cfg(feature = "private-fair-shuffle-operation")]
pub const PRIVATE_SHUFFLE_PROVE_OPERATION: &str = "dungeon.private-fair-shuffle.prove.v1";
#[cfg(feature = "private-fair-shuffle-operation")]
pub const PRIVATE_SHUFFLE_REVEAL_OPERATION: &str = "dungeon.private-fair-shuffle.reveal.v1";
#[cfg(feature = "private-fair-shuffle-operation")]
pub const PRIVATE_SHUFFLE_COMMIT_MEDIA_TYPE: &str =
    "application/vnd.dregg.private-fair-shuffle-commit.v1";
#[cfg(feature = "private-fair-shuffle-operation")]
pub const PRIVATE_SHUFFLE_PROOF_MEDIA_TYPE: &str =
    "application/vnd.dregg.private-fair-shuffle-proof.v1+postcard";
#[cfg(feature = "private-fair-shuffle-operation")]
pub const PRIVATE_SHUFFLE_REVEAL_MEDIA_TYPE: &str =
    "application/vnd.dregg.private-fair-shuffle-opening.v1+postcard";
#[cfg(feature = "private-fair-shuffle-operation")]
pub const PRIVATE_SHUFFLE_DISCLOSURE: &str = "Eight actor-bound commitments must land before a HidingFri proof can admit a bias-free deal; rejected ranks are recorded and retried, and each accepted seat may reveal only its own Merkle-opened card. In the Keep, that seat owner may spend the revealed card as fair initiative: parity chooses the banner in one atomic crown-and-descent turn, bound to the accepted deal, seat, card, actor, and reveal order. The current producer sees all contributions and the host sees submitted openings; this is Tier-1, not distributed MPC input assembly, and the hiding proof remains in the durable operation journal rather than recursively folded into the world turn.";
#[cfg(feature = "private-fair-shuffle-operation")]
const MAX_PRIVATE_SHUFFLE_PROOF_BYTES: usize = 8 * 1024 * 1024;
#[cfg(feature = "private-fair-shuffle-operation")]
const MAX_PRIVATE_SHUFFLE_OPENING_BYTES: usize = 64 * 1024;
#[cfg(feature = "private-fair-shuffle-operation")]
const PRIVATE_SHUFFLE_COMMIT_BYTES: usize = 1 + 4 * SHUFFLE_DIGEST_WIDTH;

#[cfg(feature = "private-quest-operation")]
pub const PRIVATE_QUEST_OPERATION: &str = "dungeon.private-quest-reduction.v1";
#[cfg(feature = "private-quest-operation")]
pub const PRIVATE_QUEST_MEDIA_TYPE: &str =
    "application/vnd.dregg.private-quest-reduction.v1+postcard";
#[cfg(feature = "private-quest-operation")]
pub const MAX_PRIVATE_QUEST_BYTES: usize = 8 * 1024 * 1024;
#[cfg(feature = "private-quest-operation")]
pub const PRIVATE_QUEST_DISCLOSURE: &str = "Each opaque HidingFri receipt proves one of two ordered, Lean-authored Warden graph reductions over a hidden four-edge quest state. The host retains only the fixed domain/session/index, blinded ruleset and state roots, and proof; graph edges, match, selected rule, and blindings stay with the producer. This standalone history is not yet the Effect::Custom cell carrier.";

/// Stable public proof-session id derived from the hosted session seed.
#[cfg(feature = "private-fair-shuffle-operation")]
pub fn private_fair_shuffle_session_for_seed(seed: u64) -> u32 {
    const BABYBEAR_P: u64 = 2_013_265_921;
    let mut hasher =
        blake3::Hasher::new_derive_key("dregg-dungeon-private-fair-shuffle-session-v1");
    hasher.update(&seed.to_le_bytes());
    let mut low = [0u8; 8];
    low.copy_from_slice(&hasher.finalize().as_bytes()[..8]);
    (u64::from_le_bytes(low) % BABYBEAR_P) as u32
}

/// Stable canonical BabyBear session id for the private party preference.
#[cfg(feature = "private-preference-operation")]
pub fn private_preference_session_for_seed(seed: u64) -> u32 {
    const BABYBEAR_P: u64 = 2_013_265_921;
    let mut hasher =
        blake3::Hasher::new_derive_key("dregg-dungeon-private-party-preference-session-v1");
    hasher.update(&seed.to_le_bytes());
    let mut low = [0u8; 8];
    low.copy_from_slice(&hasher.finalize().as_bytes()[..8]);
    (u64::from_le_bytes(low) % BABYBEAR_P) as u32
}

/// Stable canonical BabyBear session id for the private semantic quest.
#[cfg(feature = "private-quest-operation")]
pub fn private_quest_session_for_seed(seed: u64) -> u32 {
    const BABYBEAR_P: u64 = 2_013_265_921;
    let mut hasher = blake3::Hasher::new_derive_key("dregg-dungeon-private-quest-session-v1");
    hasher.update(&seed.to_le_bytes());
    let mut low = [0u8; 8];
    low.copy_from_slice(&hasher.finalize().as_bytes()[..8]);
    (u64::from_le_bytes(low) % BABYBEAR_P) as u32
}

/// Exact fixed-width commitment submission used by every frontend adapter.
#[cfg(feature = "private-fair-shuffle-operation")]
pub fn encode_private_shuffle_commitment(
    participant: u8,
    commitment: [u32; SHUFFLE_DIGEST_WIDTH],
) -> Vec<u8> {
    let mut out = Vec::with_capacity(PRIVATE_SHUFFLE_COMMIT_BYTES);
    out.push(participant);
    for lane in commitment {
        out.extend_from_slice(&lane.to_be_bytes());
    }
    out
}

#[cfg(feature = "private-fair-shuffle-operation")]
fn decode_private_shuffle_commitment(
    payload: &[u8],
) -> Result<(usize, [u32; SHUFFLE_DIGEST_WIDTH]), BinaryOperationError> {
    if payload.len() != PRIVATE_SHUFFLE_COMMIT_BYTES {
        return Err(BinaryOperationError::Malformed(format!(
            "private shuffle commitment is {} bytes; canonical width is {PRIVATE_SHUFFLE_COMMIT_BYTES}",
            payload.len()
        )));
    }
    let participant = payload[0] as usize;
    let mut commitment = [0u32; SHUFFLE_DIGEST_WIDTH];
    for (lane, slot) in commitment.iter_mut().enumerate() {
        let base = 1 + lane * 4;
        *slot = u32::from_be_bytes(
            payload[base..base + 4]
                .try_into()
                .expect("fixed payload width checked"),
        );
    }
    Ok((participant, commitment))
}

/// **A dungeon play session over the REAL substrate** — the factored `fiction.rs` `RealSession`.
/// Owns the live [`WorldCell`] (the committed dungeon-on-dregg Keep), the owned scene (the
/// choices/conditions actions are built from), the deterministic seed, and the accumulated
/// [`Playthrough`] (genesis + committed steps) that [`DungeonOffering::verify`] re-verifies by
/// replay. Also keeps a per-step **actor log** (who drove each move) — session metadata beside
/// the world-signed substrate turn, so a frontend can attribute moves without the executor
/// (which signs with the world's cap) having to.
pub struct DungeonSession {
    /// The live world-cell — genesis committed, subsequent moves committed on it.
    world: WorldCell,
    /// The owned Keep scene (deterministic; a re-deploy under `seed` reproduces it).
    scene: Scene,
    /// The deterministic deploy seed — `verify` re-deploys a fresh identically-seeded cell.
    seed: u8,
    /// The genesis receipt (intro entry effects + initial passage bind).
    genesis: TurnReceipt,
    /// The committed slot vector right after genesis (the replay verifier reproduces it).
    genesis_state: Vec<u64>,
    /// The committed choice-steps, in order — each a real landed turn.
    steps: Vec<StepReceipt>,
    /// Who drove each committed step (parallel to `steps`) — session-level attribution. For a
    /// collective turn this is the decision's *carrier* (the mover of record).
    actors: Vec<DreggIdentity>,
    /// The collective decision behind each committed step (parallel to `steps`): `None` for a
    /// single-actor [`Offering::advance`], `Some` for an [`Offering::advance_collective`] crowd
    /// turn — the recorded electorate + carrier + tally, the crowd decision made first-class.
    collectives: Vec<Option<CollectiveDecision>>,
    /// Opt-in proof-gated public role assignment. The HidingFri receipt is
    /// accepted at most once for the session-derived field identifier.
    #[cfg(feature = "private-raid-operation")]
    private_raid: RaidAssignmentSession,
    #[cfg(feature = "private-raid-operation")]
    private_raid_actor: Option<DreggIdentity>,
    /// One proof-gated aggregate party decision. The public session retains
    /// only the ballot root, winner, and submitter.
    #[cfg(feature = "private-preference-operation")]
    private_preference: PrivatePreferenceSession,
    #[cfg(feature = "private-preference-operation")]
    private_preference_actor: Option<DreggIdentity>,
    /// Number of already-landed world steps when the verified preference was
    /// accepted. This is the operation/move ordering pin used by verification:
    /// counsel cannot authorize an earlier world step after the fact.
    #[cfg(feature = "private-preference-operation")]
    private_preference_accepted_after_steps: Option<usize>,
    /// Public commit/proof/opening state for the opt-in private fair deal.
    #[cfg(feature = "private-fair-shuffle-operation")]
    private_shuffle: FairShuffleTable,
    #[cfg(feature = "private-fair-shuffle-operation")]
    private_shuffle_actors: [Option<DreggIdentity>; SHUFFLE_PARTICIPANTS],
    /// World-step cursor at which each selective opening landed. An opened
    /// card cannot be retconned into authorization for an earlier initiative.
    #[cfg(feature = "private-fair-shuffle-operation")]
    private_shuffle_revealed_after_steps: [Option<usize>; SHUFFLE_PARTICIPANTS],
    /// Consumer-side root/proof history. The hidden graph is intentionally not
    /// present in the host session; an external quest producer owns it.
    #[cfg(feature = "private-quest-operation")]
    private_quest: Option<PrivateQuestPublicHistory>,
    #[cfg(feature = "private-quest-operation")]
    private_quest_actors: Vec<DreggIdentity>,
    #[cfg(feature = "private-quest-operation")]
    private_quest_session: u32,
}

impl DungeonSession {
    /// The current passage name (the "room"), if the dungeon is still running.
    pub fn current_passage_name(&self) -> Option<String> {
        let idx = self.world.read_passage()?;
        self.scene.passages.get(idx).map(|p| p.name.to_string())
    }

    /// The current room's prose (the scene's authored description of the passage).
    pub fn current_prose(&self) -> String {
        let Some(idx) = self.world.read_passage() else {
            return String::new();
        };
        let Some(passage) = self.scene.passages.get(idx) else {
            return String::new();
        };
        let mut out = String::new();
        for c in &passage.content {
            if let PassageContent::Prose(p) = c {
                if !out.is_empty() {
                    out.push(' ');
                }
                out.push_str(p.text.trim());
            }
        }
        out
    }

    /// Whether the dungeon has ended.
    pub fn is_ended(&self) -> bool {
        self.world.read_passage().is_none()
    }

    /// The number of real verified turns so far (genesis + committed steps).
    pub fn receipts_len(&self) -> usize {
        1 + self.steps.len()
    }

    /// Read a narrative var off the committed cell state.
    pub fn read_var(&self, name: &str) -> u64 {
        self.world.read_var(name)
    }

    #[cfg(feature = "private-raid-operation")]
    pub const fn private_raid_session_id(&self) -> u32 {
        self.private_raid.session()
    }

    #[cfg(feature = "private-raid-operation")]
    pub fn private_raid_assignment(&self) -> Option<RaidPartyAssignment> {
        self.private_raid.assignment().copied()
    }

    #[cfg(feature = "private-raid-operation")]
    pub fn private_raid_actor(&self) -> Option<&DreggIdentity> {
        self.private_raid_actor.as_ref()
    }

    #[cfg(feature = "private-preference-operation")]
    pub const fn private_preference_session_id(&self) -> u32 {
        self.private_preference.session()
    }

    #[cfg(feature = "private-preference-operation")]
    pub fn private_preference_decision(&self) -> Option<PrivatePartyDecision> {
        self.private_preference.decision().copied()
    }

    #[cfg(feature = "private-preference-operation")]
    pub fn private_preference_actor(&self) -> Option<&DreggIdentity> {
        self.private_preference_actor.as_ref()
    }

    #[cfg(feature = "private-fair-shuffle-operation")]
    pub const fn private_fair_shuffle_session_id(&self) -> u32 {
        self.private_shuffle.session()
    }

    #[cfg(feature = "private-fair-shuffle-operation")]
    pub fn private_fair_shuffle_table(&self) -> &FairShuffleTable {
        &self.private_shuffle
    }

    #[cfg(feature = "private-quest-operation")]
    pub const fn private_quest_session_id(&self) -> u32 {
        self.private_quest_session
    }

    #[cfg(feature = "private-quest-operation")]
    pub fn private_quest_history(&self) -> Option<&PrivateQuestPublicHistory> {
        self.private_quest.as_ref()
    }

    #[cfg(feature = "private-quest-operation")]
    pub fn private_quest_actors(&self) -> &[DreggIdentity] {
        &self.private_quest_actors
    }

    /// The recorded playthrough (genesis + committed steps) — the input to replay-verify.
    pub fn playthrough(&self) -> Playthrough {
        Playthrough {
            genesis: self.genesis.clone(),
            genesis_state: self.genesis_state.clone(),
            steps: self.steps.clone(),
        }
    }

    /// The actor who drove step `n` (0-based over committed steps), if recorded. For a collective
    /// step this is the decision's carrier (the mover of record).
    pub fn actor_of_step(&self, n: usize) -> Option<&DreggIdentity> {
        self.actors.get(n)
    }

    /// The [`CollectiveDecision`] behind step `n` (0-based over committed steps), if the step was
    /// a crowd turn ([`Offering::advance_collective`]). `None` for a single-actor step or an
    /// absent index — the recorded electorate + carrier + tally, the crowd decision first-class.
    pub fn collective_of_step(&self, n: usize) -> Option<&CollectiveDecision> {
        self.collectives.get(n).and_then(|c| c.as_ref())
    }

    /// A compact one-line projection of the party's committed state (for the surface).
    pub fn state_line(&self) -> String {
        let owner = match self.read_var("relic_owner") {
            1 => "Red Hand",
            2 => "Blue Hand",
            _ => "unclaimed",
        };
        format!(
            "HP {} · depth {} · gold {} · crown {} · will spent {}",
            self.read_var("hp"),
            self.read_var("depth"),
            self.read_var("gold"),
            owner,
            self.read_var("mana_spent"),
        )
    }
}

/// Bind the public result of the hiding proof and its authenticated carrier to
/// the exact world turn that enacts it. `apply_choice_certified` commits this
/// field under the world's decision ext-key in the same receipt as the route.
#[cfg(feature = "private-preference-operation")]
fn private_preference_enactment_commitment(
    decision: PrivatePartyDecision,
    actor: &DreggIdentity,
) -> FieldElement {
    let mut bytes = Vec::with_capacity(64 + actor.as_str().len());
    bytes.extend_from_slice(b"dregg-dungeon/private-preference-enactment-v1");
    bytes.extend_from_slice(&decision.session().to_be_bytes());
    for lane in decision.ballot_root() {
        bytes.extend_from_slice(&lane.to_be_bytes());
    }
    bytes.extend_from_slice(&(decision.winner() as u64).to_be_bytes());
    bytes.extend_from_slice(&(actor.as_str().len() as u64).to_be_bytes());
    bytes.extend_from_slice(actor.as_str().as_bytes());
    field_from_bytes(&bytes)
}

/// Locate the one selectively revealed card owned by `actor`. Commit-time
/// admission already prevents one identity from occupying two live seats.
#[cfg(feature = "private-fair-shuffle-operation")]
fn private_shuffle_card_for_actor(
    session: &DungeonSession,
    actor: &DreggIdentity,
) -> Option<(usize, u8)> {
    session
        .private_shuffle_actors
        .iter()
        .zip(session.private_shuffle.revealed_cards())
        .enumerate()
        .find_map(|(seat, (bound, card))| {
            if bound.as_ref() == Some(actor) {
                card.map(|card| (seat, card))
            } else {
                None
            }
        })
}

/// Bind the accepted fair-deal statement, the selectively opened result, and
/// its seat owner to the exact crown-and-descent transition it authorizes.
#[cfg(feature = "private-fair-shuffle-operation")]
fn private_shuffle_enactment_commitment(
    session: &DungeonSession,
    seat: usize,
    card: u8,
    revealed_after: usize,
    actor: &DreggIdentity,
) -> Option<FieldElement> {
    let receipt = session.private_shuffle.accepted_receipt()?;
    let statement = receipt.statement();
    let mut bytes = Vec::with_capacity(160 + actor.as_str().len());
    bytes.extend_from_slice(b"dregg-dungeon/private-fair-shuffle-enactment-v1");
    bytes.extend_from_slice(&statement.session.to_be_bytes());
    bytes.extend_from_slice(&statement.attempt.to_be_bytes());
    for lane in statement.commitment_root {
        bytes.extend_from_slice(&lane.to_be_bytes());
    }
    for lane in statement.deal_root {
        bytes.extend_from_slice(&lane.to_be_bytes());
    }
    bytes.extend_from_slice(&receipt.verifier_key());
    bytes.extend_from_slice(&(seat as u64).to_be_bytes());
    bytes.push(card);
    bytes.extend_from_slice(&(revealed_after as u64).to_be_bytes());
    bytes.extend_from_slice(&(actor.as_str().len() as u64).to_be_bytes());
    bytes.extend_from_slice(actor.as_str().as_bytes());
    Some(field_from_bytes(&bytes))
}

/// **The dungeon offering** — offering #0. A stateless factory over the hosted Keep universe;
/// each [`open`](Offering::open) deploys a fresh [`DungeonSession`]. Carries the per-move
/// [`RunCost`] (the free tier by default; a paid tier prices the confined narrator — which the
/// frontend, not the core, actually debits and runs).
pub struct DungeonOffering {
    /// Run-credits a move's paid narration costs (`0` → free tier). The substrate turn is
    /// always free + verifiable; this prices the confined intelligence overlay.
    narration_credits: u64,
}

impl DungeonOffering {
    /// The free-tier dungeon (no credit debited per move; scripted/local narration).
    pub fn new() -> Self {
        DungeonOffering {
            narration_credits: 0,
        }
    }

    /// A paid-tier dungeon: each move's hosted narration costs `credits` run-credits (the
    /// frontend debits them against the actor's `dregg_pay` balance before serving the render).
    pub fn paid(credits: u64) -> Self {
        DungeonOffering {
            narration_credits: credits,
        }
    }

    /// The current room's choices as cap-gated [`Action`]s (the ballot options / affordances),
    /// in the SAME order the compiler indexed them (so `arg` is exactly the choice index
    /// [`WorldCell::apply_choice`] checks the gate case against). A choice whose scene condition
    /// currently fails is `enabled: false` — the cap tooth shown, not hidden (a decoration; the
    /// executor is the sole referee — a gated illegal move still refuses on `advance`).
    fn room_actions(&self, session: &DungeonSession) -> Vec<Action> {
        let Some(idx) = session.world.read_passage() else {
            return Vec::new();
        };
        let Some(passage) = session.scene.passages.get(idx) else {
            return Vec::new();
        };
        passage
            .content
            .iter()
            .filter_map(|c| match c {
                PassageContent::Choice(ch) => Some(ch),
                _ => None,
            })
            .enumerate()
            .map(|(choice_index, choice)| {
                let available = choice
                    .condition
                    .as_ref()
                    .map(|c| eval_condition(&c.expr, &session.world))
                    .unwrap_or(true);
                #[cfg(feature = "private-preference-operation")]
                let available = if passage.name.as_str() == ROOM_HALL
                    && choice_index == KP_PRIVATE_COUNSEL_DESCEND
                {
                    session
                        .private_preference_decision()
                        .is_some_and(|decision| {
                            decision.winner() == PRIVATE_PREFERENCE_DROWNED_STAIR_PLAN
                        })
                } else {
                    available
                };
                #[cfg(feature = "private-fair-shuffle-operation")]
                let available = if passage.name.as_str() == ROOM_HALL
                    && matches!(
                        choice_index,
                        KP_PRIVATE_SHUFFLE_EVEN_INITIATIVE | KP_PRIVATE_SHUFFLE_ODD_INITIATIVE
                    ) {
                    let wanted_parity = (choice_index == KP_PRIVATE_SHUFFLE_ODD_INITIATIVE) as u8;
                    session.read_var("relic_owner") == 0
                        && session
                            .private_shuffle
                            .revealed_cards()
                            .iter()
                            .flatten()
                            .any(|card| card % 2 == wanted_parity)
                } else {
                    available
                };
                Action::new(
                    choice.text.to_string(),
                    TURN_CHOOSE,
                    choice_index as i64,
                    available,
                )
            })
            .collect()
    }
}

impl Default for DungeonOffering {
    fn default() -> Self {
        DungeonOffering::new()
    }
}

impl Offering for DungeonOffering {
    type Session = DungeonSession;

    /// Deploy a fresh session hosting the Keep: deploy a real world-cell under the config seed,
    /// run the intro's entry effects as the genesis turn (via the stock [`Driver`], finished to
    /// hold the post-genesis cell), and record the genesis snapshot. (The factored
    /// `RealSession::open`.)
    fn open(&self, cfg: SessionConfig) -> Result<DungeonSession, OfferingError> {
        // A deterministic deploy seed in 1..=251 (stable per session → replay-verifiable
        // identity), derived from the config seed (default 1).
        let seed = ((cfg.seed.unwrap_or(1) % 251) + 1) as u8;
        #[cfg(feature = "private-raid-operation")]
        let private_raid_session = {
            let source = cfg.seed.unwrap_or(1);
            // Canonical nonzero BabyBear value, stable for the hosted session.
            ((source % 2_013_265_920) + 1) as u32
        };
        #[cfg(feature = "private-preference-operation")]
        let private_preference_session = private_preference_session_for_seed(cfg.seed.unwrap_or(1));
        #[cfg(feature = "private-fair-shuffle-operation")]
        let private_shuffle_session = private_fair_shuffle_session_for_seed(cfg.seed.unwrap_or(1));
        #[cfg(feature = "private-quest-operation")]
        let private_quest_session = private_quest_session_for_seed(cfg.seed.unwrap_or(1));
        let scene = keep_scene();
        let world = deploy_keep(seed);
        // Drive genesis with the stock runtime (intro entry effects: hp=50, mana_budget=50),
        // then finish to hold the post-genesis world-cell for direct `apply_choice` play.
        let driver = spween_dregg::Driver::start(world, &scene)
            .map_err(|e| OfferingError::Deploy(e.to_string()))?;
        let genesis = driver.genesis().cloned().unwrap_or_default();
        let genesis_state = driver.playthrough().genesis_state;
        let (world, _no_steps) = driver.finish();
        Ok(DungeonSession {
            world,
            scene,
            seed,
            genesis,
            genesis_state,
            steps: Vec::new(),
            actors: Vec::new(),
            collectives: Vec::new(),
            #[cfg(feature = "private-raid-operation")]
            private_raid: RaidAssignmentSession::new(private_raid_session)
                .map_err(|error| OfferingError::Deploy(error.to_string()))?,
            #[cfg(feature = "private-raid-operation")]
            private_raid_actor: None,
            #[cfg(feature = "private-preference-operation")]
            private_preference: PrivatePreferenceSession::new(private_preference_session)
                .map_err(|error| OfferingError::Deploy(error.to_string()))?,
            #[cfg(feature = "private-preference-operation")]
            private_preference_actor: None,
            #[cfg(feature = "private-preference-operation")]
            private_preference_accepted_after_steps: None,
            #[cfg(feature = "private-fair-shuffle-operation")]
            private_shuffle: FairShuffleTable::new(private_shuffle_session)
                .map_err(|error| OfferingError::Deploy(error.to_string()))?,
            #[cfg(feature = "private-fair-shuffle-operation")]
            private_shuffle_actors: core::array::from_fn(|_| None),
            #[cfg(feature = "private-fair-shuffle-operation")]
            private_shuffle_revealed_after_steps: [None; SHUFFLE_PARTICIPANTS],
            #[cfg(feature = "private-quest-operation")]
            private_quest: None,
            #[cfg(feature = "private-quest-operation")]
            private_quest_actors: Vec::new(),
            #[cfg(feature = "private-quest-operation")]
            private_quest_session,
        })
    }

    fn actions(&self, session: &DungeonSession) -> Vec<Action> {
        self.room_actions(session)
    }

    /// **Apply a choice as ONE real cap-bounded turn** (the factored `RealSession::apply_winner`
    /// + the anti-ghost tooth). `input.arg` is the scene choice index. A legal move commits a
    /// real [`TurnReceipt`] (recorded onto the playthrough + the actor log); an illegal / stale
    /// / forged one is a real [`WorldError::Refused`] — nothing commits, no step recorded.
    fn advance(
        &self,
        session: &mut DungeonSession,
        input: Action,
        actor: DreggIdentity,
    ) -> Outcome {
        if input.turn != TURN_CHOOSE {
            return Outcome::Refused(format!("unknown affordance: {}", input.turn));
        }
        if input.arg < 0 {
            return Outcome::Refused("that move is not on the current ballot".to_string());
        }
        let choice_index = input.arg as usize;

        let Some(idx) = session.world.read_passage() else {
            return Outcome::Refused("the dungeon has already ended".to_string());
        };
        let passage_name = match session.scene.passages.get(idx) {
            Some(p) => p.name.to_string(),
            None => return Outcome::Refused("no current passage".to_string()),
        };
        let Some(choice) = nth_choice(&session.scene, &passage_name, choice_index) else {
            return Outcome::Refused("that move is not on the current ballot".to_string());
        };

        #[cfg(feature = "private-preference-operation")]
        let private_preference_binding = if passage_name == ROOM_HALL
            && choice_index == KP_PRIVATE_COUNSEL_DESCEND
        {
            let Some(decision) = session.private_preference_decision() else {
                return Outcome::Refused(
                    "the shielded counsel route requires a verified private preference".to_string(),
                );
            };
            if decision.winner() != PRIVATE_PREFERENCE_DROWNED_STAIR_PLAN {
                return Outcome::Refused(format!(
                    "private plan #{} does not authorize the drowned-stair route",
                    decision.winner()
                ));
            }
            let Some(counsel_actor) = session.private_preference_actor() else {
                return Outcome::Refused(
                    "the verified private preference has no authenticated submitter".to_string(),
                );
            };
            if counsel_actor != &actor {
                return Outcome::Refused(
                    "only the authenticated private-counsel submitter may enact its route"
                        .to_string(),
                );
            }
            let Some(accepted_after) = session.private_preference_accepted_after_steps else {
                return Outcome::Refused(
                    "the private preference is missing its replay-order binding".to_string(),
                );
            };
            if accepted_after > session.steps.len() {
                return Outcome::Refused(
                    "the private preference cannot authorize an earlier world step".to_string(),
                );
            }
            Some(private_preference_enactment_commitment(
                decision,
                counsel_actor,
            ))
        } else {
            None
        };
        #[cfg(not(feature = "private-preference-operation"))]
        let private_preference_binding: Option<FieldElement> = None;

        #[cfg(feature = "private-fair-shuffle-operation")]
        let private_shuffle_binding = if passage_name == ROOM_HALL
            && matches!(
                choice_index,
                KP_PRIVATE_SHUFFLE_EVEN_INITIATIVE | KP_PRIVATE_SHUFFLE_ODD_INITIATIVE
            ) {
            if session.read_var("relic_owner") != 0 {
                return Outcome::Refused(
                    "fair-dealt initiative cannot retake an already claimed crown".to_string(),
                );
            }
            let Some((seat, card)) = private_shuffle_card_for_actor(session, &actor) else {
                return Outcome::Refused(
                    "fair-dealt initiative requires this actor's selectively opened card"
                        .to_string(),
                );
            };
            let expected_choice = if card % 2 == 0 {
                KP_PRIVATE_SHUFFLE_EVEN_INITIATIVE
            } else {
                KP_PRIVATE_SHUFFLE_ODD_INITIATIVE
            };
            if choice_index != expected_choice {
                return Outcome::Refused(format!(
                    "revealed card {card} authorizes the other initiative route"
                ));
            }
            let Some(revealed_after) = session.private_shuffle_revealed_after_steps[seat] else {
                return Outcome::Refused(
                    "the fair-dealt card is missing its replay-order binding".to_string(),
                );
            };
            if revealed_after > session.steps.len() {
                return Outcome::Refused(
                    "the fair-dealt card cannot authorize an earlier world step".to_string(),
                );
            }
            let Some(commitment) =
                private_shuffle_enactment_commitment(session, seat, card, revealed_after, &actor)
            else {
                return Outcome::Refused(
                    "fair-dealt initiative has no accepted shuffle receipt".to_string(),
                );
            };
            Some(commitment)
        } else {
            None
        };
        #[cfg(not(feature = "private-fair-shuffle-operation"))]
        let private_shuffle_binding: Option<FieldElement> = None;

        let private_result_binding = private_preference_binding.or(private_shuffle_binding);

        let applied = match private_result_binding {
            Some(commitment) => session.world.apply_choice_certified(
                &passage_name,
                choice_index,
                &choice,
                commitment,
            ),
            None => session
                .world
                .apply_choice(&passage_name, choice_index, &choice),
        };
        match applied {
            Ok(receipt) => {
                let step = StepReceipt {
                    passage: passage_name,
                    choice_index,
                    receipt: receipt.clone(),
                    state: session.world.snapshot(),
                    decision_commitment: private_result_binding,
                };
                session.steps.push(step);
                session.actors.push(actor);
                // Keep the collective log parallel to `steps`; `advance` is single-actor, so no
                // crowd decision by default. `advance_collective` fills this slot after us.
                session.collectives.push(None);
                let ended = session.world.read_passage().is_none();
                Outcome::Landed { receipt, ended }
            }
            Err(WorldError::Refused(why)) => Outcome::Refused(why),
            Err(e) => Outcome::Refused(e.to_string()),
        }
    }

    /// **Record a first-class crowd turn** (the collective analogue of `advance`). Resolves the
    /// winning [`Action`] as ONE real cap-bounded turn attributed to the decision's `carrier`
    /// (via [`advance`](Self::advance) — the substrate still admits exactly one typed move), then,
    /// *iff it landed*, persists the whole [`CollectiveDecision`] (electorate + tally + carrier)
    /// beside the committed step. So the receipt says "the PARTY (these voters) decided X, carried
    /// by Y" with the real electorate — closing the gap where the /dungeon frontend attributed the
    /// crowd turn to a nameless `party_actor()` constant. A refused move records nothing (the
    /// anti-ghost tooth: no step, no decision).
    fn advance_collective(
        &self,
        session: &mut DungeonSession,
        input: Action,
        decision: CollectiveDecision,
    ) -> Outcome {
        let carrier = decision.carrier.clone();
        let out = self.advance(session, input, carrier);
        if out.landed() {
            // `advance` just pushed a `None` collective slot for this landed step; fill it with
            // the crowd decision (electorate + tally), making the crowd turn first-class.
            if let Some(slot) = session.collectives.last_mut() {
                *slot = Some(decision);
            }
        }
        out
    }

    /// **Re-verify the whole receipt chain by REPLAY** — re-drives a fresh identically-seeded
    /// world-cell through the recorded choices and confirms it reproduces exactly the committed
    /// state chain in passage order ([`verify_by_replay`]). Private-counsel steps additionally
    /// rebind their certified value to the accepted hiding-proof result, operation order, and
    /// submitting actor. A forged/reordered/substituted record fails.
    fn verify(&self, session: &DungeonSession) -> VerifyReport {
        let turns = session.receipts_len();
        match verify_by_replay(
            deploy_keep(session.seed),
            &session.scene,
            &session.playthrough(),
        ) {
            Ok(()) => match verify_private_result_enactments(session, &session.playthrough()) {
                Ok(()) => VerifyReport::ok(turns),
                Err(reason) => VerifyReport::broken(turns, reason),
            },
            Err(b) => VerifyReport::broken(turns, b.to_string()),
        }
    }

    /// Render the current room as a **deos affordance [`Surface`]**: the room prose + the party
    /// state + verified-turn count, and the choices as a cap-gated affordance [`Menu`] (each row
    /// a `{turn: "choose", arg: choice_index}` affordance; an ineligible choice is a dimmed
    /// `!enabled` row — the cap tooth shown, not hidden).
    fn render(&self, session: &DungeonSession) -> Surface {
        let room_name = session
            .current_passage_name()
            .unwrap_or_else(|| "the dark".to_string());
        let actions = self.room_actions(session);

        let mut children = vec![
            ViewNode::Text(session.current_prose()),
            ViewNode::Section {
                title: "Party".to_string(),
                tag: "muted".to_string(),
                children: vec![ViewNode::Text(session.state_line())],
            },
            ViewNode::Section {
                title: "Objective".to_string(),
                tag: "muted".to_string(),
                children: vec![ViewNode::Text(KEEP_OBJECTIVE.to_string())],
            },
            ViewNode::Section {
                title: "Verified turns".to_string(),
                tag: "genuine".to_string(),
                children: vec![ViewNode::Text(session.receipts_len().to_string())],
            },
        ];

        #[cfg(feature = "private-raid-operation")]
        {
            let state = match session.private_raid_assignment() {
                Some(assignment) => format!(
                    "verified roles: {:?} · submitted by {}",
                    assignment.roles(),
                    session
                        .private_raid_actor()
                        .map(|actor| actor.0.as_str())
                        .unwrap_or("unknown")
                ),
                None => format!(
                    "awaiting {PRIVATE_RAID_OPERATION} receipt for proof session {}",
                    session.private_raid_session_id()
                ),
            };
            children.push(ViewNode::Section {
                title: "Private raid muster".to_string(),
                tag: "genuine".to_string(),
                children: vec![
                    ViewNode::Text(state),
                    ViewNode::Text(PRIVATE_RAID_DISCLOSURE.to_string()),
                ],
            });
        }

        #[cfg(feature = "private-preference-operation")]
        {
            let state = match session.private_preference_decision() {
                Some(decision) => format!(
                    "the party privately chose #{}: {} · submitted by {}",
                    decision.winner(),
                    PRIVATE_PREFERENCE_OPTIONS[decision.winner()],
                    session
                        .private_preference_actor()
                        .map(|actor| actor.0.as_str())
                        .unwrap_or("unknown")
                ),
                None => format!(
                    "awaiting {PRIVATE_PREFERENCE_OPERATION} receipt for proof session {} · plans: {}",
                    session.private_preference_session_id(),
                    PRIVATE_PREFERENCE_OPTIONS.join(" · ")
                ),
            };
            children.push(ViewNode::Section {
                title: "Shielded party counsel".to_string(),
                tag: "genuine".to_string(),
                children: vec![
                    ViewNode::Text(state),
                    ViewNode::Text(PRIVATE_PREFERENCE_DISCLOSURE.to_string()),
                ],
            });
        }

        #[cfg(feature = "private-fair-shuffle-operation")]
        {
            let table = session.private_fair_shuffle_table();
            let committed = table
                .commitments()
                .iter()
                .filter(|entry| entry.is_some())
                .count();
            let state = if let Some(receipt) = table.accepted_receipt() {
                format!(
                    "accepted attempt {} · {} private card opening(s) landed",
                    receipt.statement().attempt,
                    table
                        .revealed_cards()
                        .iter()
                        .filter(|card| card.is_some())
                        .count()
                )
            } else {
                format!(
                    "attempt {} · {committed}/{SHUFFLE_PARTICIPANTS} actor-bound commitments",
                    table.next_attempt().unwrap_or_default()
                )
            };
            children.push(ViewNode::Section {
                title: "Private fair deal".to_string(),
                tag: "genuine".to_string(),
                children: vec![
                    ViewNode::Text(state),
                    ViewNode::Text(format!(
                        "proof session {} · {} rejected unbiased-retry receipt(s)",
                        session.private_fair_shuffle_session_id(),
                        table.rejected_receipts().len()
                    )),
                    ViewNode::Text(PRIVATE_SHUFFLE_DISCLOSURE.to_string()),
                ],
            });
        }

        #[cfg(feature = "private-quest-operation")]
        {
            let (steps, root) = session
                .private_quest_history()
                .map(|history| {
                    (
                        history.receipt_count(),
                        format!("{:?}", history.head().current_root),
                    )
                })
                .unwrap_or_else(|| (0, "not established".to_string()));
            children.push(ViewNode::Section {
                title: "Private semantic quest".to_string(),
                tag: "genuine".to_string(),
                children: vec![
                    ViewNode::Text(format!(
                        "{steps}/{PRIVATE_QUEST_STEPS} opaque reductions verified · current root {root}"
                    )),
                    ViewNode::Text(format!(
                        "proof session {} · domain {PRIVATE_QUEST_DOMAIN} · {} authenticated submitter(s)",
                        session.private_quest_session_id(),
                        session.private_quest_actors().len()
                    )),
                    ViewNode::Text(PRIVATE_QUEST_DISCLOSURE.to_string()),
                ],
            });
        }

        if session.is_ended() {
            children.push(ViewNode::Section {
                title: "The Keep is cleared".to_string(),
                tag: "genuine".to_string(),
                children: vec![ViewNode::Text(
                    "The objective is met — one real turn at a time.".to_string(),
                )],
            });
        } else {
            let items = actions
                .iter()
                .map(|a| MenuItem {
                    label: a.label.clone(),
                    turn: a.turn.clone(),
                    arg: a.arg,
                    enabled: a.enabled,
                })
                .collect();
            children.push(ViewNode::Section {
                title: "The party's move".to_string(),
                tag: "accent".to_string(),
                children: vec![ViewNode::Menu { items }],
            });
        }

        Surface(ViewNode::Section {
            title: format!("{KEEP_NAME} — {room_name}"),
            tag: "accent".to_string(),
            children,
        })
    }

    #[cfg(any(
        feature = "private-raid-operation",
        feature = "private-preference-operation",
        feature = "private-fair-shuffle-operation",
        feature = "private-quest-operation"
    ))]
    fn binary_operations(&self, _session: &Self::Session) -> Vec<BinaryOperationDescriptor> {
        let mut operations = Vec::new();
        #[cfg(feature = "private-raid-operation")]
        operations.push(BinaryOperationDescriptor {
            name: PRIVATE_RAID_OPERATION.to_string(),
            title: "Prove private raid-role assignment".to_string(),
            input_media_type: PRIVATE_RAID_MEDIA_TYPE.to_string(),
            max_input_bytes: MAX_PRIVATE_RAID_BYTES,
            disclosure: PRIVATE_RAID_DISCLOSURE.to_string(),
        });
        #[cfg(feature = "private-preference-operation")]
        operations.push(BinaryOperationDescriptor {
            name: PRIVATE_PREFERENCE_OPERATION.to_string(),
            title: "Prove a shielded party preference".to_string(),
            input_media_type: PRIVATE_PREFERENCE_MEDIA_TYPE.to_string(),
            max_input_bytes: MAX_PRIVATE_PREFERENCE_BYTES,
            disclosure: PRIVATE_PREFERENCE_DISCLOSURE.to_string(),
        });
        #[cfg(feature = "private-fair-shuffle-operation")]
        operations.extend([
            BinaryOperationDescriptor {
                name: PRIVATE_SHUFFLE_COMMIT_OPERATION.to_string(),
                title: "Commit one private fair-shuffle contribution".to_string(),
                input_media_type: PRIVATE_SHUFFLE_COMMIT_MEDIA_TYPE.to_string(),
                max_input_bytes: PRIVATE_SHUFFLE_COMMIT_BYTES,
                disclosure: PRIVATE_SHUFFLE_DISCLOSURE.to_string(),
            },
            BinaryOperationDescriptor {
                name: PRIVATE_SHUFFLE_PROVE_OPERATION.to_string(),
                title: "Prove a bias-free private fair deal".to_string(),
                input_media_type: PRIVATE_SHUFFLE_PROOF_MEDIA_TYPE.to_string(),
                max_input_bytes: MAX_PRIVATE_SHUFFLE_PROOF_BYTES,
                disclosure: PRIVATE_SHUFFLE_DISCLOSURE.to_string(),
            },
            BinaryOperationDescriptor {
                name: PRIVATE_SHUFFLE_REVEAL_OPERATION.to_string(),
                title: "Reveal one actor-owned card".to_string(),
                input_media_type: PRIVATE_SHUFFLE_REVEAL_MEDIA_TYPE.to_string(),
                max_input_bytes: MAX_PRIVATE_SHUFFLE_OPENING_BYTES,
                disclosure: PRIVATE_SHUFFLE_DISCLOSURE.to_string(),
            },
        ]);
        #[cfg(feature = "private-quest-operation")]
        operations.push(BinaryOperationDescriptor {
            name: PRIVATE_QUEST_OPERATION.to_string(),
            title: "Prove one hidden semantic quest reduction".to_string(),
            input_media_type: PRIVATE_QUEST_MEDIA_TYPE.to_string(),
            max_input_bytes: MAX_PRIVATE_QUEST_BYTES,
            disclosure: PRIVATE_QUEST_DISCLOSURE.to_string(),
        });
        operations
    }

    #[cfg(any(
        feature = "private-raid-operation",
        feature = "private-preference-operation",
        feature = "private-fair-shuffle-operation",
        feature = "private-quest-operation"
    ))]
    fn binary_operation_replay_material(
        &self,
        _session: &Self::Session,
        name: &str,
        payload: &[u8],
    ) -> Result<Option<BinaryOperationReplayMaterial>, BinaryOperationError> {
        #[cfg(feature = "private-raid-operation")]
        if name == PRIVATE_RAID_OPERATION {
            let receipt = RaidAssignmentReceipt::from_postcard(payload)
                .map_err(|error| BinaryOperationError::Malformed(error.to_string()))?;
            let canonical = receipt
                .to_postcard()
                .map_err(|error| BinaryOperationError::Malformed(error.to_string()))?;
            if canonical != payload {
                return Err(BinaryOperationError::Malformed(
                    "private raid receipt is not canonically encoded".to_string(),
                ));
            }
            return Ok(Some(BinaryOperationReplayMaterial::new(
                canonical,
                "Retains the public raid statement, pinned verifier identity, and opaque hiding proof; no scores, admissibility matrix, or proof witness.",
            )));
        }

        #[cfg(feature = "private-preference-operation")]
        if name == PRIVATE_PREFERENCE_OPERATION {
            let receipt = PrivatePreferenceReceipt::from_postcard(payload)
                .map_err(|error| BinaryOperationError::Malformed(error.to_string()))?;
            let canonical = receipt
                .to_postcard()
                .map_err(|error| BinaryOperationError::Malformed(error.to_string()))?;
            if canonical != payload {
                return Err(BinaryOperationError::Malformed(
                    "private preference receipt is not canonically encoded".to_string(),
                ));
            }
            return Ok(Some(BinaryOperationReplayMaterial::new(
                canonical,
                "Retains the public preference session, faithful ballot root, winner, pinned verifier identity, and opaque HidingFri proof; no ballot, option total, winning total, or commitment blinding.",
            )));
        }

        #[cfg(feature = "private-fair-shuffle-operation")]
        if name == PRIVATE_SHUFFLE_COMMIT_OPERATION {
            let _ = decode_private_shuffle_commitment(payload)?;
            return Ok(Some(BinaryOperationReplayMaterial::new(
                payload.to_vec(),
                "Retains one public participant commitment and participant index; no contribution or commitment blinding.",
            )));
        }

        #[cfg(feature = "private-fair-shuffle-operation")]
        if name == PRIVATE_SHUFFLE_PROVE_OPERATION {
            let receipt = FairShuffleReceipt::from_postcard(payload)
                .map_err(|error| BinaryOperationError::Malformed(error.to_string()))?;
            let canonical = receipt
                .to_postcard()
                .map_err(|error| BinaryOperationError::Malformed(error.to_string()))?;
            if canonical != payload {
                return Err(BinaryOperationError::Malformed(
                    "private fair-shuffle receipt is not canonically encoded".to_string(),
                ));
            }
            return Ok(Some(BinaryOperationReplayMaterial::new(
                canonical,
                "Retains the public shuffle statement, pinned verifier identity, and opaque hiding proof; no participant contributions, cards, rank, or proof witness.",
            )));
        }

        #[cfg(feature = "private-fair-shuffle-operation")]
        if name == PRIVATE_SHUFFLE_REVEAL_OPERATION {
            let opening = FairCardOpening::from_postcard(payload)
                .map_err(|error| BinaryOperationError::Malformed(error.to_string()))?;
            let canonical = opening
                .to_postcard()
                .map_err(|error| BinaryOperationError::Malformed(error.to_string()))?;
            if canonical != payload {
                return Err(BinaryOperationError::Malformed(
                    "private fair-shuffle opening is not canonically encoded".to_string(),
                ));
            }
            return Ok(Some(BinaryOperationReplayMaterial::new(
                canonical,
                "Retains exactly one intentionally revealed seat/card plus its commitment blinding and Merkle authentication path; no other card or contribution.",
            )));
        }

        #[cfg(feature = "private-quest-operation")]
        if name == PRIVATE_QUEST_OPERATION {
            let receipt = decode_private_quest_receipt(payload)
                .map_err(|error| BinaryOperationError::Malformed(error.to_string()))?;
            let canonical = encode_private_quest_receipt(&receipt)
                .map_err(|error| BinaryOperationError::Malformed(error.to_string()))?;
            return Ok(Some(BinaryOperationReplayMaterial::new(
                canonical,
                "Retains the fixed quest domain/session/index, blinded old/new/ruleset roots, and opaque HidingFri proof; no graph edges, match, selected rule, or commitment blindings.",
            )));
        }

        Err(BinaryOperationError::UnknownOperation(name.to_string()))
    }

    #[cfg(any(
        feature = "private-raid-operation",
        feature = "private-preference-operation",
        feature = "private-fair-shuffle-operation",
        feature = "private-quest-operation"
    ))]
    fn invoke_binary_operation(
        &self,
        session: &mut Self::Session,
        name: &str,
        payload: &[u8],
        actor: DreggIdentity,
    ) -> Result<BinaryOperationReceipt, BinaryOperationError> {
        #[cfg(feature = "private-raid-operation")]
        if name == PRIVATE_RAID_OPERATION {
            if payload.len() > MAX_PRIVATE_RAID_BYTES {
                return Err(BinaryOperationError::Malformed(format!(
                    "private raid receipt is {} bytes; maximum is {MAX_PRIVATE_RAID_BYTES}",
                    payload.len()
                )));
            }
            let receipt = RaidAssignmentReceipt::from_postcard(payload)
                .map_err(|error| BinaryOperationError::Malformed(error.to_string()))?;
            let canonical = receipt
                .to_postcard()
                .map_err(|error| BinaryOperationError::Malformed(error.to_string()))?;
            if canonical != payload {
                return Err(BinaryOperationError::Malformed(
                    "private raid receipt is not canonically encoded".to_string(),
                ));
            }
            let receipt_id = {
                let mut hash = blake3::Hasher::new();
                hash.update(b"dregg-dungeon-private-raid-operation-receipt-v1");
                hash.update(&canonical);
                *hash.finalize().as_bytes()
            };
            let assignment = session
                .private_raid
                .accept(&receipt)
                .map_err(|error| BinaryOperationError::Refused(error.to_string()))?;
            session.private_raid_actor = Some(actor);
            return Ok(BinaryOperationReceipt {
                operation: PRIVATE_RAID_OPERATION.to_string(),
                receipt_id,
                public_fields: vec![
                    ("session".to_string(), assignment.session().to_string()),
                    (
                        "inputRoot".to_string(),
                        format!("{:?}", assignment.input_root()),
                    ),
                    ("roles".to_string(), format!("{:?}", assignment.roles())),
                ],
            });
        }

        #[cfg(feature = "private-preference-operation")]
        if name == PRIVATE_PREFERENCE_OPERATION {
            if payload.len() > MAX_PRIVATE_PREFERENCE_BYTES {
                return Err(BinaryOperationError::Malformed(format!(
                    "private preference receipt is {} bytes; maximum is {MAX_PRIVATE_PREFERENCE_BYTES}",
                    payload.len()
                )));
            }
            let receipt = PrivatePreferenceReceipt::from_postcard(payload)
                .map_err(|error| BinaryOperationError::Malformed(error.to_string()))?;
            let canonical = receipt
                .to_postcard()
                .map_err(|error| BinaryOperationError::Malformed(error.to_string()))?;
            if canonical != payload {
                return Err(BinaryOperationError::Malformed(
                    "private preference receipt is not canonically encoded".to_string(),
                ));
            }
            let receipt_id = {
                let mut hash = blake3::Hasher::new();
                hash.update(b"dregg-dungeon-private-preference-operation-receipt-v1");
                hash.update(&canonical);
                *hash.finalize().as_bytes()
            };
            let decision = session
                .private_preference
                .accept(&receipt)
                .map_err(|error| BinaryOperationError::Refused(error.to_string()))?;
            session.private_preference_actor = Some(actor);
            session.private_preference_accepted_after_steps = Some(session.steps.len());
            return Ok(BinaryOperationReceipt {
                operation: PRIVATE_PREFERENCE_OPERATION.to_string(),
                receipt_id,
                public_fields: vec![
                    ("session".to_string(), decision.session().to_string()),
                    (
                        "ballotRoot".to_string(),
                        format!("{:?}", decision.ballot_root()),
                    ),
                    ("winner".to_string(), decision.winner().to_string()),
                    (
                        "plan".to_string(),
                        PRIVATE_PREFERENCE_OPTIONS[decision.winner()].to_string(),
                    ),
                ],
            });
        }

        #[cfg(feature = "private-fair-shuffle-operation")]
        if name == PRIVATE_SHUFFLE_COMMIT_OPERATION {
            let (participant, commitment) = decode_private_shuffle_commitment(payload)?;
            if participant >= SHUFFLE_PARTICIPANTS {
                return Err(BinaryOperationError::Refused(format!(
                    "participant {participant} is outside fixed range 0..{}",
                    SHUFFLE_PARTICIPANTS - 1
                )));
            }
            if session
                .private_shuffle_actors
                .iter()
                .enumerate()
                .any(|(seat, bound)| seat != participant && bound.as_ref() == Some(&actor))
            {
                return Err(BinaryOperationError::Refused(
                    "one authenticated actor cannot occupy two shuffle participants".to_string(),
                ));
            }
            session
                .private_shuffle
                .commit(participant, commitment)
                .map_err(|error| BinaryOperationError::Refused(error.to_string()))?;
            session.private_shuffle_actors[participant] = Some(actor);
            let receipt_id =
                *blake3::Hasher::new_derive_key("dregg-dungeon-private-shuffle-commit-receipt-v1")
                    .update(payload)
                    .finalize()
                    .as_bytes();
            return Ok(BinaryOperationReceipt {
                operation: name.to_string(),
                receipt_id,
                public_fields: vec![
                    ("participant".to_string(), participant.to_string()),
                    (
                        "attempt".to_string(),
                        session
                            .private_shuffle
                            .next_attempt()
                            .unwrap_or_default()
                            .to_string(),
                    ),
                ],
            });
        }

        #[cfg(feature = "private-fair-shuffle-operation")]
        if name == PRIVATE_SHUFFLE_PROVE_OPERATION {
            if payload.len() > MAX_PRIVATE_SHUFFLE_PROOF_BYTES {
                return Err(BinaryOperationError::Malformed(format!(
                    "private fair-shuffle receipt is {} bytes; maximum is {MAX_PRIVATE_SHUFFLE_PROOF_BYTES}",
                    payload.len()
                )));
            }
            let receipt = FairShuffleReceipt::from_postcard(payload)
                .map_err(|error| BinaryOperationError::Malformed(error.to_string()))?;
            let canonical = receipt
                .to_postcard()
                .map_err(|error| BinaryOperationError::Malformed(error.to_string()))?;
            if canonical != payload {
                return Err(BinaryOperationError::Malformed(
                    "private fair-shuffle receipt is not canonically encoded".to_string(),
                ));
            }
            let outcome = session
                .private_shuffle
                .accept_attempt(&receipt)
                .map_err(|error| BinaryOperationError::Refused(error.to_string()))?;
            if outcome == FairShuffleAttemptOutcome::Rejected {
                session.private_shuffle_actors = core::array::from_fn(|_| None);
            }
            let receipt_id =
                *blake3::Hasher::new_derive_key("dregg-dungeon-private-shuffle-proof-receipt-v1")
                    .update(&canonical)
                    .finalize()
                    .as_bytes();
            return Ok(BinaryOperationReceipt {
                operation: name.to_string(),
                receipt_id,
                public_fields: vec![
                    (
                        "session".to_string(),
                        receipt.statement().session.to_string(),
                    ),
                    (
                        "attempt".to_string(),
                        receipt.statement().attempt.to_string(),
                    ),
                    (
                        "outcome".to_string(),
                        match outcome {
                            FairShuffleAttemptOutcome::Accepted => "accepted",
                            FairShuffleAttemptOutcome::Rejected => "rejected",
                        }
                        .to_string(),
                    ),
                    (
                        "dealRoot".to_string(),
                        format!("{:?}", receipt.statement().deal_root),
                    ),
                ],
            });
        }

        #[cfg(feature = "private-fair-shuffle-operation")]
        if name == PRIVATE_SHUFFLE_REVEAL_OPERATION {
            if payload.len() > MAX_PRIVATE_SHUFFLE_OPENING_BYTES {
                return Err(BinaryOperationError::Malformed(format!(
                    "private fair-shuffle opening is {} bytes; maximum is {MAX_PRIVATE_SHUFFLE_OPENING_BYTES}",
                    payload.len()
                )));
            }
            let opening = FairCardOpening::from_postcard(payload)
                .map_err(|error| BinaryOperationError::Malformed(error.to_string()))?;
            let canonical = opening
                .to_postcard()
                .map_err(|error| BinaryOperationError::Malformed(error.to_string()))?;
            if canonical != payload {
                return Err(BinaryOperationError::Malformed(
                    "private fair-shuffle opening is not canonically encoded".to_string(),
                ));
            }
            let seat = opening.seat as usize;
            if session
                .private_shuffle_actors
                .get(seat)
                .and_then(Option::as_ref)
                != Some(&actor)
            {
                return Err(BinaryOperationError::Refused(
                    "only the actor bound to this shuffle seat may reveal its card".to_string(),
                ));
            }
            let card = session
                .private_shuffle
                .reveal_card(opening)
                .map_err(|error| BinaryOperationError::Refused(error.to_string()))?;
            session.private_shuffle_revealed_after_steps[seat] = Some(session.steps.len());
            let receipt_id =
                *blake3::Hasher::new_derive_key("dregg-dungeon-private-shuffle-opening-receipt-v1")
                    .update(&canonical)
                    .finalize()
                    .as_bytes();
            return Ok(BinaryOperationReceipt {
                operation: name.to_string(),
                receipt_id,
                public_fields: vec![
                    ("seat".to_string(), seat.to_string()),
                    ("card".to_string(), card.to_string()),
                ],
            });
        }

        #[cfg(feature = "private-quest-operation")]
        if name == PRIVATE_QUEST_OPERATION {
            if payload.len() > MAX_PRIVATE_QUEST_BYTES {
                return Err(BinaryOperationError::Malformed(format!(
                    "private quest receipt is {} bytes; maximum is {MAX_PRIVATE_QUEST_BYTES}",
                    payload.len()
                )));
            }
            let receipt = decode_private_quest_receipt(payload)
                .map_err(|error| BinaryOperationError::Malformed(error.to_string()))?;
            if receipt.statement.session != session.private_quest_session {
                return Err(BinaryOperationError::Refused(format!(
                    "private quest session mismatch: expected {}, claimed {}",
                    session.private_quest_session, receipt.statement.session
                )));
            }
            let canonical = encode_private_quest_receipt(&receipt)
                .map_err(|error| BinaryOperationError::Malformed(error.to_string()))?;
            let statement = receipt.statement;

            if let Some(history) = session.private_quest.as_mut() {
                history
                    .append_verified(receipt)
                    .map_err(|error| BinaryOperationError::Refused(error.to_string()))?;
            } else {
                session.private_quest = Some(
                    PrivateQuestPublicHistory::begin_verified(receipt)
                        .map_err(|error| BinaryOperationError::Refused(error.to_string()))?,
                );
            }
            session.private_quest_actors.push(actor);

            let receipt_id =
                *blake3::Hasher::new_derive_key("dregg-dungeon-private-quest-operation-receipt-v1")
                    .update(&canonical)
                    .finalize()
                    .as_bytes();
            return Ok(BinaryOperationReceipt {
                operation: name.to_string(),
                receipt_id,
                public_fields: vec![
                    ("domain".to_string(), statement.domain.to_string()),
                    ("session".to_string(), statement.session.to_string()),
                    ("index".to_string(), statement.index.to_string()),
                    ("oldRoot".to_string(), format!("{:?}", statement.old_root)),
                    ("newRoot".to_string(), format!("{:?}", statement.new_root)),
                    (
                        "rulesetRoot".to_string(),
                        format!("{:?}", statement.ruleset_root),
                    ),
                ],
            });
        }

        Err(BinaryOperationError::UnknownOperation(name.to_string()))
    }

    /// The move's [`RunCost`] — the free tier by default; the paid tier prices the confined
    /// narrator (which the frontend debits + runs). The substrate turn itself is always free.
    fn price(&self, _input: &Action) -> RunCost {
        RunCost::credits(self.narration_credits)
    }
}

/// **The frontend-facing tamper-verify seam for the dungeon.** A frontend holds a session
/// (opaquely) and its exported [`Playthrough`]; it can serialize/transmit the record and might
/// receive a **forged** copy back. [`verify_record`](RecordVerify::verify_record) re-checks any
/// such record against the session's authentic world identity (the private `seed`/`scene`) using
/// the FULL substrate verifier ([`verify`] — both teeth: chain-linkage + replay), so a frontend
/// can express "a forged record fails" without reaching substrate internals. Strictly stronger
/// than [`Offering::verify`] (which runs replay only): a spliced/relinked receipt that replay
/// alone might miss is still caught by the linkage tooth.
impl RecordVerify for DungeonOffering {
    type Session = DungeonSession;
    type Record = Playthrough;

    /// Export the session's authentic playthrough (genesis + committed steps) — the public record
    /// a frontend transmits / persists / re-checks. No private world identity leaves the offering.
    fn export_record(&self, session: &DungeonSession) -> Playthrough {
        session.playthrough()
    }

    /// Re-verify a (possibly forged) `record` against the session's authentic world identity —
    /// re-deploy a fresh identically-seeded Keep and run BOTH verification teeth over the record.
    /// A legal record re-verifies; a forged / reordered / ineligible / spliced one fails.
    fn verify_record(&self, session: &DungeonSession, record: &Playthrough) -> VerifyReport {
        let turns = record.receipts().len();
        match verify(deploy_keep(session.seed), &session.scene, record) {
            Ok(()) => match verify_private_result_enactments(session, record) {
                Ok(()) => VerifyReport::ok(turns),
                Err(reason) => VerifyReport::broken(turns, reason),
            },
            Err(b) => VerifyReport::broken(turns, b.to_string()),
        }
    }
}

/// Verify the application-level half of the private-result carrier. The generic
/// spween verifier replays the certified commitment byte-for-byte in the real
/// world transition; this check proves that commitment is exactly the accepted
/// HidingFri result, session ordering, and authenticated actor—not an unrelated
/// collective value placed under the same ext-key.
fn verify_private_result_enactments(
    session: &DungeonSession,
    record: &Playthrough,
) -> Result<(), String> {
    #[cfg(feature = "private-preference-operation")]
    {
        for (index, step) in record.steps.iter().enumerate() {
            let is_counsel =
                step.passage == ROOM_HALL && step.choice_index == KP_PRIVATE_COUNSEL_DESCEND;
            if !is_counsel {
                continue;
            }
            let decision = session.private_preference_decision().ok_or_else(|| {
                "private-counsel world step has no verified private preference".to_string()
            })?;
            if decision.winner() != PRIVATE_PREFERENCE_DROWNED_STAIR_PLAN {
                return Err(format!(
                    "private-counsel world step is not authorized by winner #{}",
                    decision.winner()
                ));
            }
            let accepted_after =
                session
                    .private_preference_accepted_after_steps
                    .ok_or_else(|| {
                        "private-counsel world step has no operation-order binding".to_string()
                    })?;
            if accepted_after > index {
                return Err(
                    "private-counsel proof was accepted after the world step it claims to authorize"
                        .to_string(),
                );
            }
            let actor = session.actors.get(index).ok_or_else(|| {
                "private-counsel world step has no authenticated actor attribution".to_string()
            })?;
            if session.private_preference_actor() != Some(actor) {
                return Err(
                    "private-counsel world step actor differs from the proof submitter".to_string(),
                );
            }
            let expected = private_preference_enactment_commitment(decision, actor);
            if step.decision_commitment != Some(expected) {
                return Err(
                    "private-counsel world step carries a substituted result commitment"
                        .to_string(),
                );
            }
        }
    }
    #[cfg(feature = "private-fair-shuffle-operation")]
    {
        for (index, step) in record.steps.iter().enumerate() {
            let is_initiative = step.passage == ROOM_HALL
                && matches!(
                    step.choice_index,
                    KP_PRIVATE_SHUFFLE_EVEN_INITIATIVE | KP_PRIVATE_SHUFFLE_ODD_INITIATIVE
                );
            if !is_initiative {
                continue;
            }
            let actor = session.actors.get(index).ok_or_else(|| {
                "fair-dealt initiative has no authenticated actor attribution".to_string()
            })?;
            let (seat, card) = private_shuffle_card_for_actor(session, actor).ok_or_else(|| {
                "fair-dealt initiative actor has no selectively verified card".to_string()
            })?;
            let revealed_after = session.private_shuffle_revealed_after_steps[seat]
                .ok_or_else(|| "fair-dealt initiative has no reveal-order binding".to_string())?;
            if revealed_after > index {
                return Err(
                    "fair-dealt card was revealed after the world step it claims to authorize"
                        .to_string(),
                );
            }
            let expected_choice = if card % 2 == 0 {
                KP_PRIVATE_SHUFFLE_EVEN_INITIATIVE
            } else {
                KP_PRIVATE_SHUFFLE_ODD_INITIATIVE
            };
            if step.choice_index != expected_choice {
                return Err(format!(
                    "fair-dealt card {card} does not authorize this initiative route"
                ));
            }
            let expected =
                private_shuffle_enactment_commitment(session, seat, card, revealed_after, actor)
                    .ok_or_else(|| {
                        "fair-dealt initiative has no accepted shuffle statement".to_string()
                    })?;
            if step.decision_commitment != Some(expected) {
                return Err(
                    "fair-dealt initiative carries a substituted result commitment".to_string(),
                );
            }
        }
    }
    let _ = (session, record);
    Ok(())
}

/// Pull the `n`-th `Choice` out of `passage` in the scene (the same ordering the compiler
/// indexes with `choice_method(passage, n)`). `None` if the passage or index is absent — a
/// non-panicking lookup used when applying a possibly-stale ballot winner. (Factored verbatim
/// from `fiction.rs`.)
fn nth_choice(scene: &Scene, passage_name: &str, n: usize) -> Option<spween::Choice> {
    let passage = scene
        .passages
        .iter()
        .find(|p| p.name.as_str() == passage_name)?;
    passage
        .content
        .iter()
        .filter_map(|c| match c {
            PassageContent::Choice(ch) => Some(ch),
            _ => None,
        })
        .nth(n)
        .cloned()
}

/// Evaluate a scene condition against the committed cell state (mirrors the runtime's own
/// evaluation via the public world reads). Used only to decide an affordance's `enabled`
/// decoration; the installed `CellProgram` gate is the sole authority over whether a move lands.
fn eval_condition(expr: &ConditionExpr, world: &WorldCell) -> bool {
    match expr {
        ConditionExpr::Atom(clause) => eval_clause(clause, world),
        ConditionExpr::And(a, b) => eval_condition(a, world) && eval_condition(b, world),
        ConditionExpr::Or(a, b) => eval_condition(a, world) || eval_condition(b, world),
    }
}

fn eval_clause(clause: &ConditionClause, world: &WorldCell) -> bool {
    match clause {
        ConditionClause::Has(h) => world.read_membership(&h.category, &h.key),
        ConditionClause::Compare(c) => {
            let lhs = world.read_var(&c.var);
            let rhs = value_to_u64(&c.value);
            match c.op {
                CompareOp::Ge => lhs >= rhs,
                CompareOp::Le => lhs <= rhs,
                CompareOp::Gt => lhs > rhs,
                CompareOp::Lt => lhs < rhs,
                CompareOp::Eq => lhs == rhs,
                CompareOp::Ne => lhs != rhs,
            }
        }
        ConditionClause::Not(inner) => !eval_clause(inner, world),
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The replay-tamper tooth — an in-crate test (it reaches the session's private
// `scene`/`seed` to forge the committed record, exactly as `fiction.rs`'s own
// forged-choice test does). The end-to-end driven flow (open → advance → verify →
// render → frontend) lives in `tests/driven.rs`.
// ─────────────────────────────────────────────────────────────────────────────
#[cfg(test)]
mod forge_tests {
    use super::*;
    use crate::SessionConfig;
    use dungeon_on_dregg::{KP_CLAIM_RED, KP_PRESS_ON};

    /// A legal line re-verifies by replay; then a FORGED committed record (the first step's
    /// choice swapped) fails replay — the executor refuses on re-drive, or the reproduced state
    /// diverges. The real receipt-chain tooth end to end, through the [`Offering`] API.
    #[test]
    fn a_forged_choice_fails_replay() {
        let off = DungeonOffering::new();
        let mut s = off
            .open(SessionConfig::with_seed(9))
            .expect("the Keep opens");
        let actor = DreggIdentity("party".to_string());

        assert!(
            off.advance(
                &mut s,
                Action::new("press on", TURN_CHOOSE, KP_PRESS_ON as i64, true),
                actor.clone(),
            )
            .landed()
        );
        assert!(
            off.advance(
                &mut s,
                Action::new("claim red", TURN_CHOOSE, KP_CLAIM_RED as i64, true),
                actor,
            )
            .landed()
        );
        assert!(off.verify(&s).verified, "the legal line re-verifies");

        // Forge the recorded record: gatehall had choices 0 (trade-blows) and 1 (press-on);
        // swap the first step's 1 → 0 and confirm replay rejects it.
        let mut play = s.playthrough();
        if let Some(first) = play.steps.first_mut() {
            first.choice_index = 0;
        }
        let out = verify_by_replay(deploy_keep(s.seed), &s.scene, &play);
        assert!(
            out.is_err(),
            "a forged choice must fail replay, got {out:?}"
        );
    }
}
