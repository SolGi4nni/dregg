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
//! anti-ghost tooth. [`verify_dungeon_record`] runs every tooth over a record — chain linkage,
//! the receipt-hash chain, replay against a fresh identically-seeded world-cell, the executor
//! anchor, the narration binding, and the private-result enactments — and BOTH the session
//! verify and the record verify go through it; a forged, substituted, reordered, or retconned
//! record fails.
//!
//! ## The narration binding is checked here, not merely committed
//!
//! A narrated turn's prose rides a receipt-only `Effect::EmitEvent`. That binds it into
//! `effects_hash` and `receipt_hash` — but `EmitEvent` mutates no cap-gated field, so it moves
//! NEITHER state hash, and replay re-drives *choices* without ever re-emitting the event. A
//! served verify that ran replay alone therefore could not see a narration swap at all, which
//! is what this module used to do. The session now keeps the prose beside each receipt
//! (`DungeonSession::narrations`) and verification RE-DERIVES the expected narration event from
//! it, so the text a reader is shown is the text that was committed.

pub mod narrated;

use narrated::{
    CHUTES_NARRATED_DISCLOSURE, CHUTES_NARRATED_MEDIA_TYPE, CHUTES_NARRATED_OPERATION,
    ChutesNarratedRequest, MAX_CHUTES_NARRATED_REQUEST_BYTES,
};

use deos_view::{MenuItem, ViewNode};
use dregg_app_framework::{
    CellProgram, FieldElement, StateConstraint, TransitionGuard, TurnReceipt, field_from_bytes,
    symbol,
};
use dungeon_on_dregg::narrator::{RecordedNarration, verify_narration_binding};
use dungeon_on_dregg::{KP_CAST_WARD, KP_CLIMB_BACK, KP_DESCEND, KP_TRADE_BLOWS};
use spween::{CompareOp, ConditionClause, ConditionExpr, PassageContent, Scene};
use spween_dregg::{
    CompiledStory, StepReceipt, WorldCell, field_to_u64, value_to_u64, verify, verify_by_replay,
    verify_receipts_anchored,
};

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
    RaidAssignmentReceipt, RaidAssignmentSession, RaidPartyAssignment, RaidRole, roles_line,
};
#[cfg(feature = "private-raid-operation")]
use dungeon_on_dregg::{KP_PRIVATE_RAID_MENDER_CHOICES, ROOM_SANCTUM};
#[cfg(feature = "private-fair-shuffle-operation")]
use dungeon_on_dregg::{KP_PRIVATE_SHUFFLE_EVEN_INITIATIVE, KP_PRIVATE_SHUFFLE_ODD_INITIATIVE};
use dungeon_on_dregg::{deploy_keep, keep_scene};

use crate::{
    Action, BinaryOperationDescriptor, BinaryOperationError, BinaryOperationReceipt,
    BinaryOperationReplayMaterial, CollectiveDecision, DreggIdentity, Offering, OfferingError,
    Outcome, RecordVerify, RunCost, SessionConfig, Surface, VerifyReport,
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
pub const PRIVATE_RAID_DISCLOSURE: &str = "HidingFri proves the published four-seat role permutation is admissible and globally optimal for one producer-private 4x4 score matrix. In the Keep, the accepted assignment gives the party one shared +20 HP sanctum recovery at the unique Mender seat; the enacting world turn is bound to the assignment, its actual actor attribution, and operation order. The producer sees every score and admissibility bit, while every assigned role is public. The proof statement does not bind seat numbers or proof bytes to player identities, so uploading the receipt records provenance only and never awards an uploader-exclusive role. This is not distributed private-input assembly, and the standalone proof remains in the durable operation journal rather than recursively folded into the world turn.";

#[cfg(feature = "private-preference-operation")]
pub const PRIVATE_PREFERENCE_OPERATION: &str = "dungeon.private-party-preference.v1";
#[cfg(feature = "private-preference-operation")]
pub const PRIVATE_PREFERENCE_MEDIA_TYPE: &str =
    "application/vnd.dregg.private-party-preference.v1+postcard";
#[cfg(feature = "private-preference-operation")]
pub const MAX_PRIVATE_PREFERENCE_BYTES: usize = 8 * 1024 * 1024;
#[cfg(feature = "private-preference-operation")]
pub const PRIVATE_PREFERENCE_DISCLOSURE: &str = "A Lean-authored HidingFri proof aggregates four producer-private, two-bit score ballots over four public party plans and reveals only the lowest-index winning plan plus a faithful ballot root. When the drowned-stair plan wins, it unlocks a shared one-shot two-depth party route whose real world receipt commits the public result and actual enacting actor. Ballots, option totals, and the winning total stay hidden; the current Tier-1 producer sees all ballots. The proof statement does not bind its bytes to a player identity, so uploading it records provenance only and never awards an uploader-exclusive route. The hiding proof itself is reverified from the durable operation journal rather than recursively folded into the world turn.";
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
pub const PRIVATE_SHUFFLE_DISCLOSURE: &str = "Eight seat-indexed commitments must land before a HidingFri proof can admit a bias-free deal; rejected ranks are recorded and retried, and a Merkle opening intentionally publishes one accepted seat's card. In the Keep, an opened card gives the party one shared fair initiative: parity chooses the banner in one atomic crown-and-descent turn, bound to the accepted deal, seat, card, actual enacting actor, and reveal order. The current producer sees all contributions and the host sees submitted openings. Commitments and openings do not prove uploader or seat-owner identity, so uploader attribution is provenance only; this is Tier-1, not distributed MPC input assembly, and the hiding proof remains in the durable operation journal rather than recursively folded into the world turn.";
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
    let participant = usize::from(payload[0]);
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
    /// The narration bound into each committed step (parallel to `steps`): `None` for an
    /// ordinary player/collective move, `Some` for a narrated turn
    /// ([`DungeonSession::advance_narrated_receipt_in_enclave`]).
    ///
    /// **This log is what makes the narration commitment checkable at all.** The receipt binds
    /// a *digest* of the prose; without the prose beside it there is nothing to re-derive that
    /// digest from, and the "narration is bound into the receipt" property can only ever be
    /// checked against itself. [`DungeonOffering::verify`] re-derives each entry's expected
    /// narration event ([`verify_narration_binding`]) and requires the receipt to bind exactly
    /// it, so a retconned narration — which moves NEITHER state hash, `EmitEvent` being
    /// state-passthrough, and is therefore invisible to replay — is caught.
    ///
    /// Kept parallel to `steps` by every push site; a length divergence is treated as a
    /// verification break rather than papered over (see [`DungeonSession::narration_log`]).
    narrations: Vec<Option<RecordedNarration>>,
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
    /// Number of already-landed world steps when the private raid assignment
    /// was accepted. The assignment cannot authorize an earlier recovery.
    #[cfg(feature = "private-raid-operation")]
    private_raid_accepted_after_steps: Option<usize>,
    /// One proof-gated aggregate party decision. The public session retains
    /// only the ballot root, winner, and uploader attribution. Upload does not
    /// confer an exclusive capability because the statement has no claimant.
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
    /// Attribution supplied by the accepted receipt's uploader. The proof has
    /// no claimant field, so this is provenance, not role ownership.
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
    /// Attribution supplied by the accepted receipt's uploader. The proof has
    /// no claimant field, so this is provenance, not route authority.
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

    /// The narration bound into step `n` (0-based over committed steps), if it was a narrated
    /// turn. This is the prose whose commitment [`DungeonOffering::verify`] re-derives.
    pub fn narration_of_step(&self, n: usize) -> Option<&RecordedNarration> {
        self.narrations.get(n).and_then(|n| n.as_ref())
    }

    /// The whole per-step narration log, or `None` when it has fallen out of step with
    /// `steps` — a push site that recorded a turn without recording (or explicitly
    /// disclaiming) its narration.
    ///
    /// Fail-closed on purpose. If the logs diverge, index `i` of one no longer describes
    /// index `i` of the other, and pairing them anyway would check turn `i`'s receipt
    /// against turn `j`'s prose — a check that reports on the wrong turn. Verification
    /// treats `None` as a break rather than skipping the tooth, so a future push site that
    /// forgets the log is loud instead of silently disarming it.
    fn narration_log(&self) -> Option<&[Option<RecordedNarration>]> {
        (self.narrations.len() == self.steps.len()).then_some(self.narrations.as_slice())
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

    /// Read var `name` out of a committed step SNAPSHOT.
    ///
    /// A snapshot is [`WorldCell::snapshot`]'s layout — the 16 register slots, then every compiled
    /// EXT var in ascending key order — so the index is derived from the same compiled story the
    /// world was deployed with, never from a guessed position.
    fn var_in(&self, snapshot: &[u64], name: &str) -> Option<u64> {
        let story = self.world.story();
        let key = story.var_key(name)?;
        let index = if (key as usize) < spween_dregg::STATE_SLOTS {
            key as usize
        } else {
            spween_dregg::STATE_SLOTS + story.ext_keys().iter().position(|k| *k == key)?
        };
        snapshot.get(index).copied()
    }

    /// The passage a committed step SNAPSHOT stands in (`None` once the scene has ended).
    fn passage_in(&self, snapshot: &[u64]) -> Option<String> {
        let raw = snapshot.get(spween_dregg::PASSAGE_SLOT).copied()?;
        if raw == spween_dregg::PASSAGE_ENDED {
            return None;
        }
        self.scene
            .passages
            .get(raw as usize)
            .map(|passage| passage.name.to_string())
    }

    /// **WHAT THE LAST COMMITTED TURN DID** — the surface's answer to "what just happened",
    /// DERIVED from the session's own committed record rather than kept beside it.
    ///
    /// ⚑ This is the hole it closes. The dungeon surface was STATIC: authored room prose, a
    /// counter line, a turn count. A player who lost 20 HP to the gate-warden — a move that
    /// returns to the SAME passage, so the prose does not change — had to diff two renders in
    /// their head to learn that anything happened at all, and on a chat frontend where the
    /// previous message has scrolled away they could not. The move's consequence was
    /// structurally unrecoverable from the surface.
    ///
    /// Every field here comes out of the committed chain: the room and choice index off the
    /// [`StepReceipt`], the prose off the same scene the executor was driven with, the deltas by
    /// differencing this step's committed snapshot against the previous one (the post-genesis
    /// snapshot for the first step), the driver off the actor log, and the binding off the real
    /// receipt hash. So it cannot claim a consequence the executor did not commit, and a
    /// tamper-verified record re-derives exactly the same sentence.
    pub fn last_outcome(&self) -> Option<DungeonTurnOutcome> {
        let steps = self.steps.len();
        let last = self.steps.last()?;
        let before: &[u64] = if steps >= 2 {
            &self.steps[steps - 2].state
        } else {
            &self.genesis_state
        };
        let after = &last.state;
        let changes = KEEP_PARTY_VARS
            .iter()
            .filter_map(|(var, label)| {
                let before = self.var_in(before, var)?;
                let after = self.var_in(after, var)?;
                (before != after).then_some(DungeonSlotChange {
                    var: (*var).to_string(),
                    label: (*label).to_string(),
                    before,
                    after,
                })
            })
            .collect();
        Some(DungeonTurnOutcome {
            turn: steps,
            room: last.passage.clone(),
            choice: nth_choice(&self.scene, &last.passage, last.choice_index)
                .map(|choice| choice.text.to_string())
                .unwrap_or_else(|| format!("choice #{}", last.choice_index)),
            actor: self.actors.get(steps - 1).cloned(),
            arrived: self.passage_in(after),
            changes,
            voters: self
                .collectives
                .get(steps - 1)
                .and_then(|slot| slot.as_ref())
                .map(|decision| decision.electorate.len()),
            narrated: self
                .narrations
                .get(steps - 1)
                .is_some_and(|slot| slot.is_some()),
            receipt: last.receipt.receipt_hash(),
        })
    }
}

/// The party vars a turn can move, with the words a player reads them by. The surface diffs
/// exactly these across a committed turn; a var the Keep never writes simply never appears.
const KEEP_PARTY_VARS: [(&str, &str); 6] = [
    ("hp", "HP"),
    ("depth", "depth"),
    ("gold", "gold"),
    ("mana_spent", "will spent"),
    ("relic_owner", "crown"),
    ("raid_mending_used", "Mender recovery"),
];

/// One committed slot movement — a party var the last turn actually moved, `before → after`, both
/// values read out of committed snapshots.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DungeonSlotChange {
    /// The compiled var name (`hp`, `depth`, …).
    pub var: String,
    /// The word a player reads it by (`HP`, `will spent`, …).
    pub label: String,
    /// The committed value before this turn.
    pub before: u64,
    /// The committed value after it.
    pub after: u64,
}

impl DungeonSlotChange {
    /// The signed movement (`after − before`), for a `+20` / `−20` reading.
    pub fn delta(&self) -> i64 {
        self.after as i64 - self.before as i64
    }
}

/// **The last committed turn, as a consequence** — [`DungeonSession::last_outcome`]'s answer.
/// Everything here is derived from the committed chain, so it is exactly as trustworthy as the
/// receipt it names.
#[derive(Clone, Debug)]
pub struct DungeonTurnOutcome {
    /// Which committed turn this was (1-based over choice steps; genesis is turn 0).
    pub turn: usize,
    /// The room the move was taken IN.
    pub room: String,
    /// The authored text of the choice that was pressed.
    pub choice: String,
    /// Who drove it (for a crowd turn, the decision's carrier).
    pub actor: Option<DreggIdentity>,
    /// The room the turn LEFT the party in (`None` once the Keep has ended).
    pub arrived: Option<String>,
    /// The party vars it moved, `before → after`.
    pub changes: Vec<DungeonSlotChange>,
    /// The size of the electorate, when the turn was a crowd decision.
    pub voters: Option<usize>,
    /// Whether a narration was bound into the turn's receipt.
    pub narrated: bool,
    /// The receipt hash the whole consequence is bound into.
    pub receipt: [u8; 32],
}

/// Bind the public result of the hiding proof and the actual enacting actor to
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
    bytes.extend_from_slice(
        &u64::try_from(decision.winner())
            .expect("the fixed private preference option set fits u64")
            .to_be_bytes(),
    );
    bytes.extend_from_slice(
        &u64::try_from(actor.as_str().len())
            .expect("the bounded actor identity fits u64")
            .to_be_bytes(),
    );
    bytes.extend_from_slice(actor.as_str().as_bytes());
    field_from_bytes(&bytes)
}

/// Return the seat encoded by one of the four role-indexed sanctum choices.
#[cfg(feature = "private-raid-operation")]
fn private_raid_mender_seat(choice_index: usize) -> Option<usize> {
    KP_PRIVATE_RAID_MENDER_CHOICES
        .iter()
        .position(|choice| *choice == choice_index)
}

/// Bind the exact public assignment, its accepting timeline cursor, and the
/// actual enacting actor to the one shared role-specific world transition.
#[cfg(feature = "private-raid-operation")]
fn private_raid_enactment_commitment(
    assignment: RaidPartyAssignment,
    accepted_after: usize,
    actor: &DreggIdentity,
) -> FieldElement {
    let mut bytes = Vec::with_capacity(128 + actor.as_str().len());
    bytes.extend_from_slice(b"dregg-dungeon/private-raid-mender-enactment-v1");
    bytes.extend_from_slice(&assignment.session().to_be_bytes());
    for lane in assignment.input_root() {
        bytes.extend_from_slice(&lane.to_be_bytes());
    }
    for role in assignment.roles() {
        bytes.push(role as u8);
    }
    bytes.extend_from_slice(
        &u64::try_from(accepted_after)
            .expect("the bounded dungeon step cursor fits u64")
            .to_be_bytes(),
    );
    bytes.extend_from_slice(
        &u64::try_from(actor.as_str().len())
            .expect("the bounded actor identity fits u64")
            .to_be_bytes(),
    );
    bytes.extend_from_slice(actor.as_str().as_bytes());
    field_from_bytes(&bytes)
}

/// Deterministically locate one selectively revealed card whose parity admits
/// the requested shared initiative route. Seat order breaks ties, so replay
/// derives the same public carrier without pretending an uploader owns a seat.
#[cfg(feature = "private-fair-shuffle-operation")]
fn private_shuffle_card_for_choice(
    session: &DungeonSession,
    choice_index: usize,
) -> Option<(usize, u8)> {
    let wanted_parity = match choice_index {
        KP_PRIVATE_SHUFFLE_EVEN_INITIATIVE => 0,
        KP_PRIVATE_SHUFFLE_ODD_INITIATIVE => 1,
        _ => return None,
    };
    session
        .private_shuffle
        .revealed_cards()
        .iter()
        .enumerate()
        .find_map(|(seat, card)| match *card {
            Some(card) if card % 2 == wanted_parity => Some((seat, card)),
            _ => None,
        })
}

/// Bind the accepted fair-deal statement, the selectively opened result, and
/// the actual enacting actor to the exact crown-and-descent transition it authorizes.
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
    bytes.extend_from_slice(
        &u64::try_from(seat)
            .expect("the fixed private shuffle seat set fits u64")
            .to_be_bytes(),
    );
    bytes.push(card);
    bytes.extend_from_slice(
        &u64::try_from(revealed_after)
            .expect("the bounded dungeon step cursor fits u64")
            .to_be_bytes(),
    );
    bytes.extend_from_slice(
        &u64::try_from(actor.as_str().len())
            .expect("the bounded actor identity fits u64")
            .to_be_bytes(),
    );
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
                #[cfg(feature = "private-raid-operation")]
                let available = if passage.name.as_str() == ROOM_SANCTUM {
                    if let Some(seat) = private_raid_mender_seat(choice_index) {
                        session.read_var("raid_mending_used") == 0
                            && session.read_var("hp") <= 30
                            && session.private_raid_assignment().is_some_and(|assignment| {
                                assignment.role_for_seat(seat) == Some(RaidRole::Mender)
                            })
                    } else {
                        available
                    }
                } else {
                    available
                };
                Action::new(
                    choice.text.to_string(),
                    TURN_CHOOSE,
                    i64::try_from(choice_index)
                        .expect("the bounded scene choice list fits the stable action wire"),
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
            narrations: Vec::new(),
            collectives: Vec::new(),
            #[cfg(feature = "private-raid-operation")]
            private_raid: RaidAssignmentSession::new(private_raid_session)
                .map_err(|error| OfferingError::Deploy(error.to_string()))?,
            #[cfg(feature = "private-raid-operation")]
            private_raid_actor: None,
            #[cfg(feature = "private-raid-operation")]
            private_raid_accepted_after_steps: None,
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
    /// / forged one is a real [`spween_dregg::WorldError::Refused`] — nothing commits, no step
    /// recorded, and the player is shown the refusal's own text
    /// ([`crate::refusal::refuse_world_error`]).
    fn advance(
        &self,
        session: &mut DungeonSession,
        input: Action,
        actor: DreggIdentity,
    ) -> Outcome {
        if input.turn != TURN_CHOOSE {
            return Outcome::Refused(format!("unknown affordance: {}", input.turn));
        }
        let choice_index = match usize::try_from(input.arg) {
            Ok(index) => index,
            Err(_) => {
                return Outcome::Refused("that move is not on the current ballot".to_string());
            }
        };

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
            Some(private_preference_enactment_commitment(decision, &actor))
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
            let Some((seat, card)) = private_shuffle_card_for_choice(session, choice_index) else {
                return Outcome::Refused(
                    "fair-dealt initiative requires a selectively opened card of this parity"
                        .to_string(),
                );
            };
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

        #[cfg(feature = "private-raid-operation")]
        let private_raid_binding = if passage_name == ROOM_SANCTUM {
            if let Some(seat) = private_raid_mender_seat(choice_index) {
                let Some(assignment) = session.private_raid_assignment() else {
                    return Outcome::Refused(
                        "raid Mender recovery requires a verified private assignment".to_string(),
                    );
                };
                if assignment.role_for_seat(seat) != Some(RaidRole::Mender) {
                    return Outcome::Refused(format!(
                        "raid seat {seat} is not the assignment's Mender"
                    ));
                }
                let Some(accepted_after) = session.private_raid_accepted_after_steps else {
                    return Outcome::Refused(
                        "the raid assignment is missing its replay-order binding".to_string(),
                    );
                };
                if accepted_after > session.steps.len() {
                    return Outcome::Refused(
                        "the raid assignment cannot authorize an earlier world step".to_string(),
                    );
                }
                if session.read_var("raid_mending_used") != 0 {
                    return Outcome::Refused(
                        "the assigned Mender recovery has already been spent".to_string(),
                    );
                }
                if session.read_var("hp") > 30 {
                    return Outcome::Refused(
                        "the Mender cannot raise the party above its 50 HP limit".to_string(),
                    );
                }
                Some(private_raid_enactment_commitment(
                    assignment,
                    accepted_after,
                    &actor,
                ))
            } else {
                None
            }
        } else {
            None
        };
        #[cfg(not(feature = "private-raid-operation"))]
        let private_raid_binding: Option<FieldElement> = None;

        let private_result_binding = private_preference_binding
            .or(private_shuffle_binding)
            .or(private_raid_binding);

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
                // A plain choice-turn binds no narration event. Recording that explicitly (rather
                // than leaving the log short) is what lets `verify_narration_binding` REFUSE a
                // narration event stapled onto an ordinary move, instead of only checking turns
                // that claim one.
                session.narrations.push(None);
                // Keep the collective log parallel to `steps`; `advance` is single-actor, so no
                // crowd decision by default. `advance_collective` fills this slot after us.
                session.collectives.push(None);
                let ended = session.world.read_passage().is_none();
                Outcome::Landed { receipt, ended }
            }
            // ONE arm, two audiences. A rules refusal (`WorldError::Refused`) is the keep's own text
            // and comes back verbatim; every other variant is a fault on this server, so the player
            // gets the shared commit-failure sentence and an operator gets the cause in a log line.
            // This used to be `Err(e) => Outcome::Refused(e.to_string())` — the generic fallback that
            // put "under-gated choice refused: method `select` did not lower fully to executor teeth"
            // on a player's screen.
            Err(e) => Outcome::Refused(crate::refusal::refuse_world_error(&e)),
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

    /// **Re-verify the whole session** — every tooth the dungeon has, over its own recorded
    /// chain ([`verify_dungeon_record`]): chain linkage, the receipt-hash chain, replay
    /// against a fresh identically-seeded world, the executor anchor, the narration binding,
    /// and the private-result enactments. A forged/reordered/substituted/retconned record
    /// fails.
    ///
    /// This is what the frontends' "re-verify chain" button drives. It used to run replay
    /// ALONE, which made the narration binding unchecked in practice: replay re-drives
    /// *choices*, never re-emitting the narration event, and `EmitEvent` moves neither state
    /// hash, so a swapped narration was invisible on the served path even though it does
    /// change `receipt_hash`.
    fn verify(&self, session: &DungeonSession) -> VerifyReport {
        let turns = session.receipts_len();
        match verify_dungeon_record(session, &session.playthrough()) {
            Ok(()) => VerifyReport::ok(turns),
            Err(reason) => VerifyReport::broken(turns, reason),
        }
    }

    /// Render the current room as a **deos affordance [`Surface`]** — the authored room prose, the
    /// two plaques, WHAT THE LAST TURN DID, and the choices as a cap-gated affordance [`Menu`]
    /// (each row a `{turn: "choose", arg: choice_index}` affordance; an ineligible choice is a
    /// dimmed `!enabled` row — the cap tooth shown, not hidden).
    ///
    /// ⚑ The composition is the plaque convention (`dregg-automatafl`'s `standing` /
    /// `automaton_plaque`): where the party stands *with the one sentence saying what to do right
    /// now*, then the DOMAIN plaque for what a player cannot read off the prose — the executor teeth
    /// that decide which of these choices can land, READ OUT OF THE DEPLOYED PROGRAM.
    ///
    /// ⚑ And the thing this surface could not do at all: SAY WHAT HAPPENED. The authored prose
    /// reads well and is STATIC — trading blows with the gate-warden returns to the same passage, so
    /// a 20-HP loss re-rendered with the same prose, the same objective, the same sections, and the
    /// consequence was recoverable only by diffing two renders in your head.
    /// [`DungeonSession::last_outcome`] derives it from the committed chain instead, and the plaque
    /// below names the room, the choice, the driver, every party var the turn moved and the receipt
    /// it is bound into.
    fn render(&self, session: &DungeonSession) -> Surface {
        let room_name = session
            .current_passage_name()
            .unwrap_or_else(|| "the dark".to_string());
        let actions = self.room_actions(session);

        let mut children = vec![
            ViewNode::Text(session.current_prose()),
            keep_standing(session, &room_name, &actions),
            last_turn_plaque(session),
            keep_teeth_plaque(session),
        ];

        #[cfg(feature = "private-raid-operation")]
        {
            let state = match session.private_raid_assignment() {
                Some(assignment) => format!(
                    "verified shared roles: {} · receipt uploaded by {} (provenance only)",
                    roles_line(assignment.roles()),
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
                    "the party privately chose #{}: {} · receipt uploaded by {} (provenance only)",
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
                    "attempt {} · {committed}/{SHUFFLE_PARTICIPANTS} seat-indexed commitments",
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
                        hex_felts(history.head().current_root),
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
                        "proof session {} · domain {PRIVATE_QUEST_DOMAIN} · {} attributed uploader(s)",
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
                    wants_text: a.wants_text,
                })
                .collect();
            children.push(ViewNode::Section {
                title: "The party's move".to_string(),
                tag: "accent".to_string(),
                children: vec![ViewNode::Menu { items }],
            });
        }

        // The bookkeeping nobody needs to read to PLAY, below the moves.
        children.push(ViewNode::Section {
            title: "The record".to_string(),
            tag: "muted".to_string(),
            children: vec![
                ViewNode::Text(format!(
                    "{} verified turn{} — genesis plus {} committed choice{}.",
                    session.receipts_len(),
                    if session.receipts_len() == 1 { "" } else { "s" },
                    session.steps.len(),
                    if session.steps.len() == 1 { "" } else { "s" }
                )),
                ViewNode::Text(format!("committed state — {}", session.state_line())),
            ],
        });

        Surface(ViewNode::Section {
            title: format!("{KEEP_NAME} — {room_name}"),
            tag: "accent".to_string(),
            children,
        })
    }

    fn binary_operations(&self, _session: &Self::Session) -> Vec<BinaryOperationDescriptor> {
        let mut operations = vec![BinaryOperationDescriptor {
            name: CHUTES_NARRATED_OPERATION.to_string(),
            title: "Narrate one closed-command Dungeon turn with Chutes".to_string(),
            input_media_type: CHUTES_NARRATED_MEDIA_TYPE.to_string(),
            max_input_bytes: MAX_CHUTES_NARRATED_REQUEST_BYTES,
            disclosure: CHUTES_NARRATED_DISCLOSURE.to_string(),
        }];
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
                title: "Reveal one accepted deal card".to_string(),
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

    fn binary_operation_replay_material(
        &self,
        _session: &Self::Session,
        name: &str,
        payload: &[u8],
    ) -> Result<Option<BinaryOperationReplayMaterial>, BinaryOperationError> {
        if name == CHUTES_NARRATED_OPERATION {
            let request = ChutesNarratedRequest::decode(payload)?;
            return Ok(Some(BinaryOperationReplayMaterial::new(
                request.encode()?,
                CHUTES_NARRATED_DISCLOSURE,
            )));
        }

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

    fn invoke_binary_operation(
        &self,
        session: &mut Self::Session,
        name: &str,
        payload: &[u8],
        actor: DreggIdentity,
    ) -> Result<BinaryOperationReceipt, BinaryOperationError> {
        if name == CHUTES_NARRATED_OPERATION {
            let request = ChutesNarratedRequest::decode(payload)?;
            let view = session.narrated_view();
            let narrated = request.narrated_for(&view)?;
            let command = narrated.command.clone();
            let keyword = dungeon_on_dregg::narrator::legal_commands(&view)
                .into_iter()
                .find_map(|(keyword, candidate)| (candidate == command).then_some(keyword))
                .ok_or_else(|| {
                    BinaryOperationError::Refused(
                        "the admitted narrated command left the live room's closed vocabulary"
                            .to_string(),
                    )
                })?
                .to_string();
            let landed = session
                .advance_narrated_receipt(&narrated, actor)
                .map_err(BinaryOperationError::Refused)?;
            if landed.narrated.command != command {
                return Err(BinaryOperationError::Refused(
                    "the landed narrated receipt substituted the admitted command".to_string(),
                ));
            }
            return Ok(BinaryOperationReceipt {
                operation: CHUTES_NARRATED_OPERATION.to_string(),
                receipt_id: landed.narrated.receipt.receipt_hash(),
                public_fields: vec![
                    ("model".to_string(), request.model().to_string()),
                    ("command".to_string(), keyword),
                    (
                        "operatorSpendMicroUsd".to_string(),
                        request.operator_spend_micro_usd().to_string(),
                    ),
                    (
                        "narrationCommit".to_string(),
                        hex_bytes(&landed.narrated.narration_commit),
                    ),
                    ("ended".to_string(), landed.ended.to_string()),
                ],
            });
        }

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
            session.private_raid_accepted_after_steps = Some(session.steps.len());
            return Ok(BinaryOperationReceipt {
                operation: PRIVATE_RAID_OPERATION.to_string(),
                receipt_id,
                public_fields: vec![
                    ("session".to_string(), assignment.session().to_string()),
                    ("inputRoot".to_string(), hex_felts(assignment.input_root())),
                    ("roles".to_string(), roles_line(assignment.roles())),
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
                    ("ballotRoot".to_string(), hex_felts(decision.ballot_root())),
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
            session
                .private_shuffle
                .commit(participant, commitment)
                .map_err(|error| BinaryOperationError::Refused(error.to_string()))?;
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
                        hex_felts(receipt.statement().deal_root),
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
            let seat = usize::from(opening.seat);
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
                    ("oldRoot".to_string(), hex_felts(statement.old_root)),
                    ("newRoot".to_string(), hex_felts(statement.new_root)),
                    ("rulesetRoot".to_string(), hex_felts(statement.ruleset_root)),
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
/// such record against the session's authentic world identity (the private `seed`/`scene`) with
/// [`verify_dungeon_record`] — every tooth — so a frontend can express "a forged record fails"
/// without reaching substrate internals.
///
/// [`Offering::verify`] now runs the same teeth over the session's own playthrough; the
/// difference is only WHICH record is checked (a caller-supplied one here, the session's own
/// there).
impl RecordVerify for DungeonOffering {
    type Session = DungeonSession;
    type Record = Playthrough;

    /// Export the session's authentic playthrough (genesis + committed steps) — the public record
    /// a frontend transmits / persists / re-checks. No private world identity leaves the offering.
    ///
    /// Note the exported record carries RECEIPTS, not narration text: the prose stays in the
    /// session's narration log, which is what [`verify_record`](Self::verify_record) re-derives
    /// each receipt's narration event from. A frontend that wants to publish the prose must
    /// publish it alongside, and a reader re-checks it with
    /// [`verify_narration_binding`](dungeon_on_dregg::narrator::verify_narration_binding).
    fn export_record(&self, session: &DungeonSession) -> Playthrough {
        session.playthrough()
    }

    /// Re-verify a (possibly forged) `record` against the session's authentic world identity —
    /// re-deploy a fresh identically-seeded Keep and run every tooth over the record. A legal
    /// record re-verifies; a forged / reordered / ineligible / spliced / retconned one fails.
    fn verify_record(&self, session: &DungeonSession, record: &Playthrough) -> VerifyReport {
        let turns = record.receipts().len();
        match verify_dungeon_record(session, record) {
            Ok(()) => VerifyReport::ok(turns),
            Err(reason) => VerifyReport::broken(turns, reason),
        }
    }
}

/// **Every tooth the dungeon has**, run over `record` against `session`'s authentic world
/// identity. The one place the served verification path is defined, so
/// [`Offering::verify`] and [`RecordVerify::verify_record`] cannot drift apart — the drift
/// that left the deployed "re-verify chain" button running replay alone while the record
/// verifier ran two teeth.
///
/// In order:
///
/// 1. **Chain linkage, receipt-hash chain, replay** (`spween_dregg::verify`) — the record
///    links, each receipt's *whole body* is the one the next receipt committed to, and a
///    fresh identically-seeded world reproduces the committed state at every step.
/// 2. **Executor anchor** (`verify_receipts_anchored`, against the session's LIVE world) —
///    every receipt is one this executor actually issued, under its recomputed
///    `receipt_hash`. This is the only tooth covering the HEAD receipt's body, since
///    `previous_receipt_hash` links backwards and nothing follows the head.
/// 3. **Narration binding** (`verify_narration_binding`) — each recorded narration is
///    re-hashed and must equal what its receipt bound, with the same requirement in the
///    negative: a turn the log says had no narration must bind no narration event.
/// 4. **Private-result enactments** — a certified private result is bound to the accepted
///    session/result/actor and operation order.
///
/// The narration log is paired POSITIONALLY with `record.steps` (`record.receipts()` puts
/// genesis first, which never carries a narration). A record whose step count differs from
/// the session's log is refused rather than checked on a prefix: index `i` of one would no
/// longer describe index `i` of the other.
///
/// ## What a passing report means — and what it does NOT
///
/// It means the RECORDED CHAIN has not been tampered with: these receipts are the ones this
/// executor issued, they link, they reproduce on replay against a fresh identically-seeded
/// world, and the narration shown beside each turn is the narration that turn committed to.
/// A retcon — of a choice, a state, a receipt body, or the prose — fails.
///
/// It does NOT mean the narration was produced by any particular model, or by a model at
/// all. Nothing in this function looks at where bytes came from; a host that invents prose
/// and then honestly commits to the invention passes every tooth here. What it cannot do is
/// change its story afterwards. Model provenance rides the ATTESTATION —
/// [`TeeProvenance`](dungeon_on_dregg::narrator::TeeProvenance) for the enclave path — and
/// even a matching provenance slot only says a DCAP verification accepted an enclave with
/// that measurement at narration time. That claim's trust root is Intel's attestation key
/// and the backend that checked the quote, not this check; all this check adds is that the
/// summary in the record is the summary the turn bound.
fn verify_dungeon_record(session: &DungeonSession, record: &Playthrough) -> Result<(), String> {
    verify(deploy_keep(session.seed), &session.scene, record).map_err(|b| b.to_string())?;
    verify_receipts_anchored(&session.world, record).map_err(|b| b.to_string())?;

    let log = session.narration_log().ok_or_else(|| {
        "the session's narration log has fallen out of step with its committed steps".to_string()
    })?;
    if record.steps.len() != log.len() {
        return Err(format!(
            "the record carries {} steps but this session recorded {}: its narrations cannot be paired",
            record.steps.len(),
            log.len()
        ));
    }
    // Genesis binds no narration; the log runs parallel to the choice-steps that follow it.
    let narrations = std::iter::once(None).chain(log.iter().map(Option::as_ref));
    verify_narration_binding(record.receipts().into_iter().zip(narrations))
        .map_err(|b| b.to_string())?;

    verify_private_result_enactments(session, record)
}

fn hex_bytes(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        out.push(HEX[(byte >> 4) as usize] as char);
        out.push(HEX[(byte & 0x0f) as usize] as char);
    }
    out
}

/// Render a felt-limb public digest as canonical lowercase hex.
///
/// The AIR's public roots are `[u32; 8]`; a `Debug` dump of that array reads as an
/// internals spill, and these values are painted into a browser page and a chat message.
#[cfg(any(
    feature = "private-raid-operation",
    feature = "private-preference-operation",
    feature = "private-fair-shuffle-operation",
    feature = "private-quest-operation",
))]
fn hex_felts(felts: [u32; 8]) -> String {
    felts
        .into_iter()
        .map(|felt| format!("{felt:08x}"))
        .collect()
}

/// Verify the application-level half of the private-result carrier. The generic
/// spween verifier replays the certified commitment byte-for-byte in the real
/// world transition; this check proves that commitment is exactly the accepted
/// HidingFri result, session ordering, and actual enacting actor—not an unrelated
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
            let actor = session
                .actors
                .get(index)
                .ok_or_else(|| "private-counsel world step has no actor attribution".to_string())?;
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
            let actor = session
                .actors
                .get(index)
                .ok_or_else(|| "fair-dealt initiative has no actor attribution".to_string())?;
            let wanted_parity = (step.choice_index == KP_PRIVATE_SHUFFLE_ODD_INITIATIVE) as u8;
            let bound_to_timely_opening = session
                .private_shuffle
                .revealed_cards()
                .iter()
                .enumerate()
                .filter_map(|(seat, card)| {
                    let card = (*card)?;
                    let revealed_after = session.private_shuffle_revealed_after_steps[seat]?;
                    (card % 2 == wanted_parity && revealed_after <= index).then_some((
                        seat,
                        card,
                        revealed_after,
                    ))
                })
                .any(|(seat, card, revealed_after)| {
                    private_shuffle_enactment_commitment(session, seat, card, revealed_after, actor)
                        == step.decision_commitment
                });
            if !bound_to_timely_opening {
                return Err(
                    "fair-dealt initiative carries a substituted result commitment, wrong-parity card, or postdated opening"
                        .to_string(),
                );
            }
        }
    }
    #[cfg(feature = "private-raid-operation")]
    {
        for (index, step) in record.steps.iter().enumerate() {
            if step.passage != ROOM_SANCTUM {
                continue;
            }
            let Some(seat) = private_raid_mender_seat(step.choice_index) else {
                continue;
            };
            let assignment = session.private_raid_assignment().ok_or_else(|| {
                "raid Mender world step has no verified private assignment".to_string()
            })?;
            if assignment.role_for_seat(seat) != Some(RaidRole::Mender) {
                return Err(format!("raid seat {seat} is not the assignment's Mender"));
            }
            let accepted_after = session.private_raid_accepted_after_steps.ok_or_else(|| {
                "raid Mender world step has no operation-order binding".to_string()
            })?;
            if accepted_after > index {
                return Err(
                    "raid assignment was accepted after the recovery it claims to authorize"
                        .to_string(),
                );
            }
            let actor = session
                .actors
                .get(index)
                .ok_or_else(|| "raid Mender world step has no actor attribution".to_string())?;
            let expected = private_raid_enactment_commitment(assignment, accepted_after, actor);
            if step.decision_commitment != Some(expected) {
                return Err(
                    "raid Mender world step carries a substituted result commitment".to_string(),
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
// ═══════════════════════════════════════════════════════════════════════════════════════════
// THE SURFACE — the two plaques and the last-outcome node.
//
// PRESENTATION ONLY. Every number below is either a committed read (`read_var`, a step
// snapshot) or a constraint lifted out of the DEPLOYED `CellProgram`; nothing here restates a
// rule, and the executor stays the sole referee for every move.
// ═══════════════════════════════════════════════════════════════════════════════════════════

/// The register slot holding var `name` in the deployed story, when it lives on the register
/// plane (which is where a `StateConstraint`'s `u8` index can name it at all).
fn keep_slot_of(story: &CompiledStory, name: &str) -> Option<u8> {
    let key = story.var_key(name)?;
    (key < spween_dregg::STATE_SLOTS as u64).then_some(key as u8)
}

/// The constraints the DEPLOYED program carries on the case guarded by `method`.
fn method_case<'a>(story: &'a CompiledStory, method: &str) -> Option<&'a [StateConstraint]> {
    let wanted = symbol(method);
    let CellProgram::Cases(cases) = &story.program else {
        return None;
    };
    cases
        .iter()
        .find(
            |case| matches!(&case.guard, TransitionGuard::MethodIs { method } if *method == wanted),
        )
        .map(|case| case.constraints.as_slice())
}

/// The constraints the DEPLOYED program carries on the non-dispatching case that fires whenever
/// slot `index` MOVES — the write-bound teeth (`bind_slot_write`), which are the ones that hold
/// against a staple onto some other method's turn.
fn slot_case(story: &CompiledStory, index: u8) -> Option<&[StateConstraint]> {
    let CellProgram::Cases(cases) = &story.program else {
        return None;
    };
    cases
        .iter()
        .find(
            |case| matches!(&case.guard, TransitionGuard::SlotChanged { index: i } if *i == index),
        )
        .map(|case| case.constraints.as_slice())
}

/// The `FieldGte` threshold the deployed case demands on `slot`.
fn gte_on(constraints: &[StateConstraint], slot: u8) -> Option<u64> {
    constraints.iter().find_map(|c| match c {
        StateConstraint::FieldGte { index, value } if *index == slot => Some(field_to_u64(value)),
        _ => None,
    })
}

/// The `FieldLte` ceiling the deployed case demands on `slot`.
fn lte_on(constraints: &[StateConstraint], slot: u8) -> Option<u64> {
    constraints.iter().find_map(|c| match c {
        StateConstraint::FieldLte { index, value } if *index == slot => Some(field_to_u64(value)),
        _ => None,
    })
}

/// The exact `FieldDelta` the deployed case pins on `slot`, read back as a signed movement (a
/// decrement is encoded as the additive inverse, so the `u64` lane reinterpreted as `i64` is the
/// number a player sees).
fn delta_on(constraints: &[StateConstraint], slot: u8) -> Option<i64> {
    constraints.iter().find_map(|c| match c {
        StateConstraint::FieldDelta { index, delta } if *index == slot => {
            Some(field_to_u64(delta) as i64)
        }
        _ => None,
    })
}

/// Whether the deployed case carries `WriteOnce` on `slot`.
fn write_once_on(constraints: &[StateConstraint], slot: u8) -> bool {
    constraints
        .iter()
        .any(|c| matches!(c, StateConstraint::WriteOnce { index } if *index == slot))
}

/// Whether the deployed case carries `Monotonic` on `slot`.
fn monotonic_on(constraints: &[StateConstraint], slot: u8) -> bool {
    constraints
        .iter()
        .any(|c| matches!(c, StateConstraint::Monotonic { index } if *index == slot))
}

/// The Keep's method for the gate-warden trade — the case carrying the HP floor and the exact blow.
fn trade_blows_method() -> String {
    spween_dregg::choice_method(dungeon_on_dregg::ROOM_GATEHALL, KP_TRADE_BLOWS)
}

/// The exact HP a gate-warden trade costs, and the post-state floor the executor holds it to —
/// **read off the deployed case**, so the price a player is quoted is the price the tooth enforces.
fn deployed_blow(story: &CompiledStory) -> Option<(i64, u64)> {
    let hp = keep_slot_of(story, "hp")?;
    let case = method_case(story, &trade_blows_method())?;
    Some((delta_on(case, hp)?, gte_on(case, hp)?))
}

/// The party's HP CEILING as the deployed program spells it — the `FieldLte` the certified Mender
/// recovery is held to, which is the only place the 50-HP limit exists as a tooth.
fn deployed_hp_ceiling(story: &CompiledStory) -> Option<u64> {
    let hp = keep_slot_of(story, "hp")?;
    let CellProgram::Cases(cases) = &story.program else {
        return None;
    };
    cases.iter().find_map(|case| lte_on(&case.constraints, hp))
}

/// The whole hoard, as the deployed write-bound `gold` tooth pins it: gained ONCE, by exactly this
/// delta. `None` when the tooth is not installed — reported, never guessed.
fn deployed_hoard(story: &CompiledStory) -> Option<i64> {
    let gold = keep_slot_of(story, "gold")?;
    delta_on(slot_case(story, gold)?, gold)
}

/// How many more gate-warden trades the party can take at `hp` — the largest `n` with
/// `hp + n·cost ≥ floor`, where `cost` is the deployed (negative) blow and `floor` the deployed
/// post-state bound. Both operands come off the installed program, so this is arithmetic over the
/// executor's own numbers rather than a second rule.
fn blows_left(hp: u64, cost: i64, floor: u64) -> i64 {
    if cost >= 0 {
        return 0;
    }
    let headroom = hp as i64 - floor as i64;
    if headroom < 0 { 0 } else { headroom / -cost }
}

/// The crown's owner, by banner.
fn crown_holder(owner: u64) -> &'static str {
    match owner {
        1 => "the Red Hand",
        2 => "the Blue Hand",
        _ => "nobody",
    }
}

/// **WHERE THE PARTY STANDS** — the phase pills, the ONE SENTENCE saying what to do right now, the
/// party meters, and the ⚠ pressure lines.
///
/// The directive is the FIRST paragraph on purpose: a `tag: "accent"` plaque paints its first
/// paragraph as the serif lead, so the sentence a player must act on reads first. Every number is a
/// committed read; the blow's price comes off the deployed tooth.
fn keep_standing(session: &DungeonSession, room_name: &str, actions: &[Action]) -> ViewNode {
    let story = session.world.story();
    let hp = session.read_var("hp");
    let depth = session.read_var("depth");
    let gold = session.read_var("gold");
    let spent = session.read_var("mana_spent");
    let budget = session.read_var("mana_budget");
    let owner = session.read_var("relic_owner");
    let live = actions.iter().filter(|action| action.enabled).count();
    let blow = deployed_blow(story);

    // THE DIRECTIVE — the next unmet leg of the objective, read off the committed state, plus how
    // many of the room's choices can actually land.
    let directive = if session.is_ended() {
        format!(
            "The Keep is closed: {gold} gold came out of the hoard, and every turn that took it \
             re-verifies."
        )
    } else if live == 0 {
        format!(
            "Every choice in {room_name} is barred right now — the executor would refuse each one, \
             so this run has no legal move left."
        )
    } else {
        let leg = if room_name == dungeon_on_dregg::ROOM_GATEHALL {
            "Get past the gate-warden into the plundered hall".to_string()
        } else if depth == 0 && owner == 0 {
            "Claim the crown, then descend the collapsing stair".to_string()
        } else if depth == 0 {
            format!(
                "Descend the collapsing stair — the crown is already {}'s",
                crown_holder(owner)
            )
        } else {
            "Seize the hoard".to_string()
        };
        format!(
            "{leg}: {live} of {} choices here can land right now, and the dimmed ones are moves \
             the executor would refuse.",
            actions.len()
        )
    };

    let phase = if session.is_ended() {
        "KEEP CLEARED".to_string()
    } else {
        room_name.to_uppercase()
    };
    let mut children = vec![
        ViewNode::Text(directive),
        // ⚑ THE PROSE MIRROR of the pill row — the phase, the turn and the crown's holder, in a
        // sentence.
        //
        // ⚠ ITS ORIGINAL REASON EXPIRED ON 2026-07-26 (see the same note in `campaign.rs`): the
        // shared prose walk no longer drops `Pill`, so a chat reader now gets this sentence AND
        // the badges. Redundant, not contradictory; left for a deliberate copy pass.
        ViewNode::Text(format!(
            "{phase} — turn {}, depth {depth}, the crown held by {}.",
            session.steps.len(),
            crown_holder(owner)
        )),
        ViewNode::Row(vec![
            ViewNode::Pill {
                text: phase.clone(),
                tag: if session.is_ended() { "good" } else { "accent" }.to_string(),
                slot: None,
                cases: Vec::new(),
            },
            ViewNode::Pill {
                text: format!("turn {}", session.steps.len()),
                tag: "muted".to_string(),
                slot: None,
                cases: Vec::new(),
            },
            ViewNode::Pill {
                text: format!("depth {depth}"),
                tag: if depth == 0 { "muted" } else { "warn" }.to_string(),
                slot: None,
                cases: Vec::new(),
            },
            ViewNode::Pill {
                text: if owner == 0 {
                    "crown unclaimed".to_string()
                } else {
                    format!("crown: {}", crown_holder(owner))
                },
                tag: if owner == 0 { "muted" } else { "good" }.to_string(),
                slot: None,
                cases: Vec::new(),
            },
        ]),
    ];

    // ── THE METERS. These were bare integers in a `HP 50 · depth 0 · gold 0 · …` counter line; a
    //    `Progress` paints as a brass gauge on every renderer that carries the Night Record skin,
    //    and a gauge answers "how much is left" without arithmetic. Labels padded to a common
    //    width so they stack into an aligned column on the prose channels too.
    children.push(ViewNode::Progress {
        value: hp,
        // The ceiling is the DEPLOYED `FieldLte` the Mender recovery is held to. With no such
        // tooth the meter falls back to the live value, which reads full rather than lying.
        max: deployed_hp_ceiling(story).unwrap_or(hp.max(1)),
        label: "party HP".to_string(),
    });
    children.push(ViewNode::Progress {
        value: spent,
        // The budget is a COMMITTED slot, and it is the very slot the executor's
        // `FieldLteField{mana_spent, mana_budget}` tooth compares against.
        max: budget.max(1),
        label: "will    ".to_string(),
    });
    if let Some(hoard) = deployed_hoard(story) {
        children.push(ViewNode::Progress {
            value: gold,
            max: u64::try_from(hoard).unwrap_or(1).max(1),
            label: "hoard   ".to_string(),
        });
    }

    // ── THE PRESSURES — what the party is about to lose to, said out loud. Each is derived from a
    //    committed read plus a deployed tooth, so none can disagree with the referee.
    if !session.is_ended() {
        // The warden's toll is a pressure only where the trade is actually on the ballot. Quoting
        // "two blows left" in the sanctum would be true of the party's HP and false about anything
        // it can DO — a pressure line is what you are about to lose to now, not a rulebook entry
        // (that is the teeth plaque's job).
        if let Some((cost, floor)) = blow.filter(|_| room_name == dungeon_on_dregg::ROOM_GATEHALL) {
            let next = hp as i64 + cost;
            if next < floor as i64 {
                children.push(ViewNode::Text(format!(
                    "⚠ the gate-warden trade is spent — at {hp} HP the next blow lands on {next}, \
                     under the floor of {floor} the executor holds the case to, so it commits \
                     nothing"
                )));
            } else if cost < 0 {
                let left = blows_left(hp, cost, floor);
                children.push(ViewNode::Text(format!(
                    "⚠ {left} blow{} left in the party at {hp} HP — each costs exactly {} and the \
                     one that would break the floor of {floor} is refused",
                    if left == 1 { "" } else { "s" },
                    -cost
                )));
            }
        }
        if spent >= budget {
            children.push(ViewNode::Text(format!(
                "⚠ the will reserve is spent — {spent} of {budget}, and a ward whose post-state \
                 would pass the budget is refused"
            )));
        }
        if depth >= 1 {
            children.push(ViewNode::Text(
                "⚠ the stair collapsed behind you — `depth` may only rise, so climbing back is \
                 refused"
                    .to_string(),
            ));
        }
        if owner != 0 {
            children.push(ViewNode::Text(format!(
                "⚠ the crown is {}'s and cannot change hands — the rival claim is refused for good",
                crown_holder(owner)
            )));
        }
    }

    children.push(ViewNode::Text(format!("The objective: {KEEP_OBJECTIVE}.")));

    ViewNode::Section {
        title: format!("Where the party stands — {room_name}"),
        tag: "accent".to_string(),
        children,
    }
}

/// **WHAT THE LAST TURN DID** — the node that makes "what just happened" recoverable at all.
///
/// One sentence naming the room, the choice and the driver, then one pill per party var the turn
/// actually moved (`HP −20 · 50 → 30`), then the receipt the whole consequence is bound into. With
/// no committed turn yet it says so, which is itself the distinction a static surface could not
/// make: turn 0 no longer looks like turn 1.
fn last_turn_plaque(session: &DungeonSession) -> ViewNode {
    let Some(outcome) = session.last_outcome() else {
        return ViewNode::Section {
            title: "What the last turn did".to_string(),
            tag: "muted".to_string(),
            children: vec![ViewNode::Text(
                "Nothing yet — this is the Keep exactly as its genesis turn committed it. The next \
                 press will be turn 1, and this plaque will say what it moved."
                    .to_string(),
            )],
        };
    };
    let driver = match (&outcome.actor, outcome.voters) {
        (Some(actor), Some(voters)) => format!(
            "carried by {} for an electorate of {voters}",
            actor.as_str()
        ),
        (Some(actor), None) => format!("driven by {}", actor.as_str()),
        (None, _) => "driven by an unrecorded actor".to_string(),
    };
    let went = match &outcome.arrived {
        Some(room) if *room == outcome.room => format!("and left the party in {room}"),
        Some(room) => format!("and moved the party from {} to {room}", outcome.room),
        None => "and ended the Keep".to_string(),
    };
    let moved = if outcome.changes.is_empty() {
        "It moved no party var at all.".to_string()
    } else {
        format!(
            "It moved {}.",
            outcome
                .changes
                .iter()
                .map(|change| format!("{} {} → {}", change.label, change.before, change.after))
                .collect::<Vec<String>>()
                .join(", ")
        )
    };
    let mut children = vec![ViewNode::Text(format!(
        "Turn {} pressed “{}” in {}, {went} — {driver}. {moved}",
        outcome.turn, outcome.choice, outcome.room
    ))];
    if !outcome.changes.is_empty() {
        children.push(ViewNode::Row(
            outcome
                .changes
                .iter()
                .map(|change| {
                    let delta = change.delta();
                    ViewNode::Pill {
                        text: format!(
                            "{} {}{} · {} → {}",
                            change.label,
                            if delta > 0 { "+" } else { "" },
                            delta,
                            change.before,
                            change.after
                        ),
                        // Down is loss, up is gain — except `will spent`, where rising IS the
                        // cost, so it reads as the warning it is.
                        tag: match (change.var.as_str(), delta) {
                            ("mana_spent", _) => "warn",
                            (_, d) if d < 0 => "bad",
                            _ => "good",
                        }
                        .to_string(),
                        slot: None,
                        cases: Vec::new(),
                    }
                })
                .collect(),
        ));
    }
    if outcome.narrated {
        children.push(ViewNode::Text(
            "A narration was bound into this turn's receipt, and this surface's verify re-derives \
             it from the prose beside it."
                .to_string(),
        ));
    }
    children.push(ViewNode::Text(format!(
        "Every word of that is derived from the committed step, bound into receipt {}.",
        short_receipt(outcome.receipt)
    )));
    ViewNode::Section {
        title: "What the last turn did".to_string(),
        tag: "genuine".to_string(),
        children,
    }
}

/// **"What the executor will not let you do"** — the Keep's domain plaque: the teeth that decide
/// which of the room's choices can land, and none of them is visible in the authored prose.
///
/// ⚑ Every clause is LIFTED OUT OF THE DEPLOYED `CellProgram` — the exact cases
/// [`dungeon_on_dregg::keep_compiled`] installed and the executor admits turns under — rather than
/// retyped here. So a blow re-priced, a ceiling moved or a tooth removed in the substrate moves
/// this plaque, and a tooth that is NOT there is reported as missing instead of promised.
fn keep_teeth_plaque(session: &DungeonSession) -> ViewNode {
    let story = session.world.story();
    let hp = session.read_var("hp");
    let mut children = vec![ViewNode::Text(
        "The prose does not say which of these presses can land — the installed cell program does, \
         and every rule below is read back out of it rather than restated here."
            .to_string(),
    )];
    let mut found = 0usize;

    match deployed_blow(story) {
        Some((cost, floor)) => {
            found += 1;
            let left = blows_left(hp, cost, floor);
            children.push(ViewNode::Text(format!(
                "THE WARDEN'S TOLL — the trade moves HP by exactly {cost}, and the case is \
                 admitted only while the post-state keeps HP ≥ {floor}. At {hp} HP that is {left} \
                 more blow{}; the next one after that is a real refusal that commits nothing, not \
                 a death.",
                if left == 1 { "" } else { "s" }
            )));
        }
        None => children.push(ViewNode::Text(
            "⚠ THE WARDEN'S TOLL could not be read out of the deployed program, so it is not \
             stated here rather than guessed."
                .to_string(),
        )),
    }

    if let Some(owner) = keep_slot_of(story, "relic_owner") {
        if slot_case(story, owner).is_some_and(|case| write_once_on(case, owner)) {
            found += 1;
            children.push(ViewNode::Text(
                "THE CROWN IS WRITE-ONCE, AND BOUND TO THE WRITE — the first hand to close on it \
                 holds it, and a rival claim is refused on ANY method, including one stapled onto \
                 someone else's turn."
                    .to_string(),
            ));
        }
    }

    if let Some(depth) = keep_slot_of(story, "depth") {
        let ratchet = [
            spween_dregg::choice_method(dungeon_on_dregg::ROOM_HALL, KP_DESCEND),
            spween_dregg::choice_method(dungeon_on_dregg::ROOM_SANCTUM, KP_CLIMB_BACK),
        ]
        .iter()
        .any(|method| method_case(story, method).is_some_and(|case| monotonic_on(case, depth)));
        if ratchet {
            found += 1;
            children.push(ViewNode::Text(
                "THE STAIR IS ONE-WAY — `depth` is monotonic, so the descent commits and the \
                 climb back is refused: the stair really has collapsed behind you."
                    .to_string(),
            ));
        }
    }

    if let (Some(spent), Some(budget)) = (
        keep_slot_of(story, "mana_spent"),
        keep_slot_of(story, "mana_budget"),
    ) {
        let cross = method_case(
            story,
            &spween_dregg::choice_method(dungeon_on_dregg::ROOM_SANCTUM, KP_CAST_WARD),
        )
        .is_some_and(|case| {
            case.iter().any(|c| {
                matches!(c, StateConstraint::FieldLteField { left_index, right_index }
                if *left_index == spent && *right_index == budget)
            })
        });
        if cross {
            found += 1;
            children.push(ViewNode::Text(format!(
                "THE WILL IS FINITE — a ward is admitted only while the post-state keeps \
                 `mana_spent ≤ mana_budget`, a live comparison of two committed slots ({} of {}). \
                 The overspending ward commits nothing.",
                session.read_var("mana_spent"),
                session.read_var("mana_budget")
            )));
        }
    }

    if let (Some(gold), Some(hoard)) = (keep_slot_of(story, "gold"), deployed_hoard(story)) {
        if slot_case(story, gold).is_some_and(|case| write_once_on(case, gold)) {
            found += 1;
            children.push(ViewNode::Text(format!(
                "THE HOARD IS ONE PAYOUT — gold is write-once and pinned to exactly {hoard} on \
                 ANY method, so the total that can ever leave this Keep is provably that, gained \
                 once."
            )));
        }
    }

    if found == 0 {
        children.push(ViewNode::Text(
            "⚠ NONE of the Keep's teeth could be read out of the deployed program. That is a \
             report, not a reassurance: this plaque can say nothing about what will land until the \
             installed cases can be read."
                .to_string(),
        ));
    }

    ViewNode::Section {
        title: "What the executor will not let you do".to_string(),
        tag: "accent".to_string(),
        children,
    }
}

/// The first six bytes of a receipt hash as hex — a handle a player can match against a verify
/// report without a 64-character wall.
fn short_receipt(digest: [u8; 32]) -> String {
    digest[..6]
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

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

    #[test]
    fn target_wide_choice_indices_are_anti_ghost_refusals() {
        let off = DungeonOffering::new();
        let mut session = off
            .open(SessionConfig::with_seed(9))
            .expect("the Keep opens");
        let before = session.world.snapshot();

        for arg in [-1, i64::MAX] {
            assert!(matches!(
                off.advance(
                    &mut session,
                    Action::new("hostile choice", TURN_CHOOSE, arg, true),
                    DreggIdentity("party".to_string()),
                ),
                Outcome::Refused(_)
            ));
            assert_eq!(session.world.snapshot(), before);
            assert!(session.steps.is_empty());
            assert!(session.actors.is_empty());
            assert!(session.collectives.is_empty());
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The narration-binding tooth on the SERVED path — in-crate tests, so they can
// reach the session's private `seed`/`scene`/`world`/`narrations` to forge a
// record and to show which tooth actually fires (same precedent as `forge_tests`).
// ─────────────────────────────────────────────────────────────────────────────
#[cfg(test)]
mod narration_tooth_tests {
    use super::*;
    use crate::SessionConfig;
    use dregg_app_framework::symbol;
    use dungeon_on_dregg::KP_PRESS_ON;
    use dungeon_on_dregg::narrator::{
        Command, NARRATION_TOPIC, Narrated, SLOT_NARRATION_COMMIT, TeeProvenance,
        narration_commitment,
    };
    use spween_dregg::{verify_chain_linkage, verify_receipt_hash_chain};

    fn party() -> DreggIdentity {
        DreggIdentity("party".to_string())
    }

    fn provenance() -> TeeProvenance {
        TeeProvenance::new([0x5a; 32], "tdx-keep-01", "UpToDate", [0xc3; 32])
    }

    /// A session whose committed chain is: genesis, one narrated trade-blows (with enclave
    /// provenance), one narrated trade-blows, then one PLAIN press-on.
    fn played(seed: u64) -> (DungeonOffering, DungeonSession) {
        let offering = DungeonOffering::new();
        let mut session = offering
            .open(SessionConfig::with_seed(seed))
            .expect("the Keep opens");

        let prov = provenance();
        session
            .advance_narrated_receipt_in_enclave(
                &Narrated::new(
                    Command::trade_blows(),
                    "Sparks leap from the warden's guard.",
                ),
                party(),
                Some(&prov),
            )
            .expect("the first narrated blow lands");
        session
            .advance_narrated_receipt(
                &Narrated::new(
                    Command::trade_blows(),
                    "He reels; your second blow bites deep.",
                ),
                party(),
            )
            .expect("the second narrated blow lands");
        assert!(
            offering
                .advance(
                    &mut session,
                    Action::new("press on", TURN_CHOOSE, KP_PRESS_ON as i64, true),
                    party(),
                )
                .landed(),
            "the plain move lands"
        );
        (offering, session)
    }

    /// Rewrite the narration commitment inside `receipt`'s narration event.
    fn retcon_event(receipt: &mut TurnReceipt, prose: &str) {
        let topic = symbol(NARRATION_TOPIC);
        let event = receipt
            .emitted_events
            .iter_mut()
            .find(|e| e.topic == topic)
            .expect("this receipt bound a narration event");
        event.data[SLOT_NARRATION_COMMIT] = narration_commitment(prose);
    }

    /// The honest served session verifies under every tooth, narrated turns included.
    #[test]
    fn the_honest_session_verifies() {
        let (offering, session) = played(55);
        let report = offering.verify(&session);
        assert!(report.verified, "honest session: {}", report.detail);
        assert_eq!(report.turns, 4, "genesis + two narrated + one plain");

        let record = offering.export_record(&session);
        assert!(offering.verify_record(&session, &record).verified);
    }

    /// **CANARY — a retconned narration is CAUGHT by the served `verify`, and the tooth the
    /// served path USED TO RUN is blind to it.**
    ///
    /// The prose in the session's narration log is rewritten and NOTHING else is touched:
    /// no receipt, no state. That is the whole point — the narration rides a receipt-only
    /// `EmitEvent`, so a swap moves neither state hash and the replay tooth (which was the
    /// entire body of `Offering::verify`) cannot express the difference.
    #[test]
    fn a_retconned_narration_is_caught_where_replay_alone_was_blind() {
        let (offering, mut session) = played(56);
        assert!(offering.verify(&session).verified);

        session.narrations[0]
            .as_mut()
            .expect("step 0 is narrated")
            .narration = "The warden yields the Keep's whole treasury without a fight.".to_string();

        // BEFORE — the previous served verify was exactly this call, and it still passes.
        assert_eq!(
            verify_by_replay(
                deploy_keep(session.seed),
                &session.scene,
                &session.playthrough()
            ),
            Ok(()),
            "replay is blind to the retcon: it re-drives choices and never re-emits the event"
        );
        // …as are the other purely receipt-shaped teeth, since no receipt changed.
        assert_eq!(verify_chain_linkage(&session.playthrough()), Ok(()));
        assert_eq!(verify_receipt_hash_chain(&session.playthrough()), Ok(()));

        // AFTER — the served verify now refuses.
        let report = offering.verify(&session);
        assert!(!report.verified, "the retconned narration must be refused");
        assert!(
            report.detail.contains("narration commitment"),
            "the break should name the narration commitment, got: {}",
            report.detail
        );
    }

    /// **CANARY — a swapped enclave attestation is CAUGHT.** Only the recorded
    /// [`TeeProvenance`] moves (its TCB verdict), which is exactly the fact a host would
    /// want to launder. Replay and the whole receipt chain are again blind; the tooth is not.
    #[test]
    fn a_swapped_tee_provenance_is_caught_where_replay_alone_was_blind() {
        let (offering, mut session) = played(57);
        assert!(offering.verify(&session).verified);

        session.narrations[0]
            .as_mut()
            .expect("step 0 is narrated")
            .tee_provenance = Some(TeeProvenance::new(
            [0x5a; 32],
            "tdx-keep-01",
            "SWHardeningNeeded",
            [0xc3; 32],
        ));

        assert_eq!(
            verify_by_replay(
                deploy_keep(session.seed),
                &session.scene,
                &session.playthrough()
            ),
            Ok(()),
            "replay is blind to a swapped attestation summary"
        );
        let report = offering.verify(&session);
        assert!(!report.verified, "a swapped TCB verdict must be refused");
        assert!(
            report.detail.contains("TEE-provenance"),
            "the break should name the TEE slot, got: {}",
            report.detail
        );
    }

    /// **CANARY — a transmitted record whose narration EVENT was edited is CAUGHT.** The
    /// forger rewrites the prose *and* recomputes its commitment into the receipt, so the
    /// record is internally self-consistent. Replay and chain-linkage still pass (the edit
    /// moved no state); the receipt-hash tooth fires, because the next receipt committed to
    /// the old body.
    #[test]
    fn an_edited_narration_event_in_a_transmitted_record_is_caught() {
        let (offering, session) = played(58);
        let mut forged = offering.export_record(&session);
        retcon_event(
            &mut forged.steps[0].receipt,
            "A wholly different opening beat.",
        );

        // BEFORE — both of the pre-existing teeth accept the forgery.
        assert_eq!(
            verify_by_replay(deploy_keep(session.seed), &session.scene, &forged),
            Ok(()),
            "replay accepts an edited emitted event: it moves no state"
        );
        assert_eq!(
            verify_chain_linkage(&forged),
            Ok(()),
            "linkage accepts it too: pre/post are untouched"
        );

        // AFTER — the receipt-hash tooth sees the changed body. The edited step is
        // `steps[0]`, i.e. receipt 1 (genesis is receipt 0), so the break surfaces on its
        // SUCCESSOR — receipt 2 is the one that committed to the old body.
        assert_eq!(
            verify_receipt_hash_chain(&forged),
            Err(VerifyBreak::ReceiptHashMismatch { index: 2 }),
        );
        assert!(!offering.verify_record(&session, &forged).verified);
    }

    /// **CANARY — the HEAD receipt, and why the executor anchor exists.** The forger edits
    /// the LAST receipt's narration event and retcons the session's log to match. Every
    /// record-only tooth now passes: replay and linkage move no state, the narration
    /// binding is self-consistent again, and `previous_receipt_hash` links BACKWARD so
    /// nothing commits to the head's body. Only the anchor — the executor's own chain —
    /// refuses.
    #[test]
    fn a_head_receipt_edit_is_caught_only_by_the_executor_anchor() {
        let offering = DungeonOffering::new();
        let mut session = offering
            .open(SessionConfig::with_seed(59))
            .expect("the Keep opens");
        session
            .advance_narrated_receipt(
                &Narrated::new(Command::trade_blows(), "Sparks leap from the guard."),
                party(),
            )
            .expect("the first narrated blow lands");
        session
            .advance_narrated_receipt(
                &Narrated::new(Command::trade_blows(), "He reels under the second."),
                party(),
            )
            .expect("the head narrated blow lands");

        let retconned = "He kneels and swears you the Keep.";
        let mut forged = offering.export_record(&session);
        retcon_event(
            &mut forged.steps.last_mut().expect("a head step").receipt,
            retconned,
        );
        session
            .narrations
            .last_mut()
            .expect("a head narration")
            .as_mut()
            .expect("the head step is narrated")
            .narration = retconned.to_string();

        // BEFORE — every record-only tooth passes on the forged head.
        assert_eq!(
            verify(deploy_keep(session.seed), &session.scene, &forged),
            Ok(()),
            "linkage + receipt-hash chain + replay all accept a head-only edit"
        );
        // AFTER — the executor never issued a receipt with that body.
        assert_eq!(
            verify_receipts_anchored(&session.world, &forged),
            Err(VerifyBreak::ReceiptUnanchored { index: 2 }),
        );
        assert!(!offering.verify_record(&session, &forged).verified);
    }

    /// A narration event stapled onto a PLAIN move is caught: the log records `None` for an
    /// ordinary choice-turn, and `None` is checked, not skipped.
    #[test]
    fn a_narration_stapled_onto_a_plain_move_is_caught() {
        let (offering, session) = played(60);
        let mut forged = offering.export_record(&session);
        let narrated_event = forged.steps[0]
            .receipt
            .emitted_events
            .iter()
            .find(|e| e.topic == symbol(NARRATION_TOPIC))
            .expect("step 0 bound a narration event")
            .clone();
        // Step 2 is the plain press-on; give it prose it never had.
        forged.steps[2].receipt.emitted_events.push(narrated_event);

        // The narration tooth names the staple directly (the executor anchor also refuses
        // the altered body; both are teeth this record has to get past, and it gets past
        // neither).
        let log = session
            .narration_log()
            .expect("the log runs parallel to the steps");
        let narrations = std::iter::once(None).chain(log.iter().map(Option::as_ref));
        assert_eq!(
            verify_narration_binding(forged.receipts().into_iter().zip(narrations)),
            Err(dungeon_on_dregg::narrator::NarrationBreak::EventStapled { index: 3 }),
        );
        let report = offering.verify_record(&session, &forged);
        assert!(!report.verified, "a stapled narration must be refused");
    }
}
