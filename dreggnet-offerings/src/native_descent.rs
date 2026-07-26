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
//!
//! ## Banking a relic MINTS a real owned note
//!
//! A session is deployed on a committed **run day-seed** (its provenance root) and owns a
//! [`LootVault`]. When the terminal `flee` lands, the run's BANKED custody relics are minted
//! through [`Descent::mint_banked_relics`] into that vault, and
//! [`NativeDescentCompletion::banked_notes`] carries the resulting real
//! [`dreggnet_asset`] notes — not merely the computed
//! [`banked_relics`](NativeDescentCompletion::banked_relics) index list. Each note's
//! [`AssetId`] is content-addressed to `(run day-seed, custody slot, player key)`, so it
//! **replays to this run**: re-deriving
//! [`banked_relic_drop`](dungeon_on_dregg::loot::banked_relic_drop) from the record's day-seed
//! and the banked slot re-mints the byte-identical id — which is exactly what the exact-replay
//! verifier does on every [`verify`](Offering::verify) (the completion, notes included, must
//! recompute). A run that banks nothing mints nothing.
//!
//! The run day-seed is the offering's day binding: [`NativeDescentOffering::new`] derives a
//! reproducible one from the normalized deploy seed, while
//! [`NativeDescentOffering::on_beacon`] / [`on_day`](NativeDescentOffering::on_day) bind the
//! day's REAL verified beacon seed, making the provenance root
//! unpredictable-until-revealed and distinct per day. Either way the run day-seed is folded
//! into the journal's genesis root, so a record cannot be re-pointed at another day's
//! provenance without breaking its hash chain.
//!
//! Because the root is in the genesis, a verifier that rebuilds a run by RE-OPENING and
//! re-driving its commands must deploy on the same root:
//! [`NativeDescentOffering::on_run_day_seed`] pins the exact one a record carries.
//! [`resume_record`](NativeDescentOffering::resume_record) needs no pinning — it reads
//! [`NativeDescentRecord::day_seed`] itself, so every resume path is day-agnostic already.

use deos_view::{CoordCell, MenuItem, ViewNode};
use dregg_app_framework::TurnReceipt;
/// A minted note's content-addressed id, re-exported so a surface or leaderboard can name a
/// settled run's owned notes without its own dependency on the asset layer.
pub use dreggnet_asset::AssetId;
use dungeon_on_dregg::descent::{
    ASCEND, BANKED, BREATH, BankedRelicMint, CAP, CARRIED, DELVE, Descent, FLEE, FLOORS, HARMCAP,
    LOOT, LUNGE, PROGRAM_JSON, RELICS, SMITE, Sim, UNLOCK, day_index, day_seed_from_deploy_seed,
    day_world,
};
/// **The world's presentation constants**, re-exported so a FRONTEND can size a light bar or a
/// carry meter against the same Lean-sourced numbers this surface does, without its own dependency
/// on the game crate — and so a browser-side mirror of them can be PINNED by a test against these
/// rather than drifting silently. They decide nothing; the executor is still the only referee.
///
/// These are the numbers that are the SAME every day. The guardian vitalities and the relic mint
/// homes are NOT among them — they are drawn from the committed day-seed, so a frontend sizing a
/// guardian meter asks the run for [`DayWorld`] ([`NativeDescentSession::day_world`], or
/// [`NativeDescentOffering::day_world_for_seed`] before a session exists) instead of reading a
/// constant. There deliberately is no `guardian_hp` re-export any more: the free
/// `descent::guard_hp` is day 0's table and is therefore right on one day in
/// [`DAYS`](dungeon_on_dregg::descent::DAYS).
pub use dungeon_on_dregg::descent::{
    BANKED as CUSTODY_BANKED, BREATH as LIGHT_BREATH, CAP as CARRY_CAP, CARRIED as CUSTODY_CARRIED,
    DAYS as DUNGEON_DAYS, DayWorld, FLOORS as DUNGEON_FLOORS, RELICS as DUNGEON_RELICS,
};
use dungeon_on_dregg::loot::LootError;
/// The settled run's owned-note world and the shape of what it recorded — re-exported so a
/// consumer can read a banked note's provenance / rarity, and hand the live vault on to a
/// market organ, without its own dependency on the loot layer.
pub use dungeon_on_dregg::loot::{LootProvenance, LootVault, Rarity};
#[cfg(feature = "private-fair-shuffle-operation")]
use dungeon_on_dregg::private_fair_shuffle::{
    DIGEST_WIDTH as SHUFFLE_DIGEST_WIDTH, FairCardOpening, FairShuffleAttemptOutcome,
    FairShuffleReceipt, FairShuffleTable, PARTICIPANTS as SHUFFLE_PARTICIPANTS,
};
#[cfg(feature = "private-preference-operation")]
use dungeon_on_dregg::private_preference::{
    PrivatePartyDecision, PrivatePreferenceReceipt, PrivatePreferenceSession,
};
#[cfg(feature = "private-raid-operation")]
use dungeon_on_dregg::private_raid::{
    RaidAssignmentReceipt, RaidAssignmentSession, RaidPartyAssignment, roles_line,
};
/// A run day-seed / beacon day, re-exported so a consumer can name (and re-derive under) a
/// record's provenance root without its own dependency on the procgen layer.
pub use procgen_dregg::CommittedSeed;
use procgen_dregg::beacon::DailyBeacon;
use spween_dregg::WorldError;

use crate::refusal::{belongs_to_another_player, refuse_world_error, stale_control_refresh};
use crate::{
    Action, DreggIdentity, Offering, OfferingError, Outcome, RecordVerify, RunCost, SessionConfig,
    Surface, VerifyReport,
};
#[cfg(any(
    feature = "private-preference-operation",
    feature = "private-raid-operation",
    feature = "private-fair-shuffle-operation"
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
/// Domain tag binding a day's committed beacon seed to one normalized native deploy seed.
const RUN_DAY_SEED_DOMAIN: &str = "dregg.native-descent.run-day-seed.v1";

#[cfg(any(
    feature = "private-preference-operation",
    feature = "private-raid-operation",
    feature = "private-fair-shuffle-operation"
))]
const PRIVATE_OPERATION_WIRE_MAGIC: [u8; 8] = *b"DREGGNDO";
#[cfg(any(
    feature = "private-preference-operation",
    feature = "private-raid-operation",
    feature = "private-fair-shuffle-operation"
))]
const PRIVATE_OPERATION_WIRE_VERSION: u8 = 1;
#[cfg(any(
    feature = "private-preference-operation",
    feature = "private-raid-operation",
    feature = "private-fair-shuffle-operation"
))]
const MAX_NATIVE_DESCENT_PRIVATE_OPERATION_BYTES: usize = 8 * 1024 * 1024;
#[cfg(any(
    feature = "private-preference-operation",
    feature = "private-raid-operation",
    feature = "private-fair-shuffle-operation"
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

#[cfg(feature = "private-fair-shuffle-operation")]
pub const NATIVE_DESCENT_PRIVATE_DEAL_OPERATION: &str = "descent.private-initiative-deal.v1";
#[cfg(feature = "private-fair-shuffle-operation")]
pub const NATIVE_DESCENT_PRIVATE_DEAL_MEDIA_TYPE: &str =
    "application/vnd.dregg.native-descent.private-initiative-deal.v1+binary";
#[cfg(feature = "private-fair-shuffle-operation")]
pub const NATIVE_DESCENT_PRIVATE_DEAL_DISCLOSURE: &str = "A Lean-authored HidingFri proof certifies a bias-free eight-seat deal from eight committed private contributions. The full deal, rank, contributions, and seven unselected cards remain hidden; only the deal root and the fixed seat-zero initiative card are selectively opened. The canonical request binds the proof, all public commitments, and opening to this native Descent's authenticated player, exact revision, and exact journal root; stale, cross-player, cross-root, and duplicate submissions to the same run refuse. The retained request contains public commitments, the seat-zero opening (including its blinding and Merkle path), and the opaque proof. This is a Tier-1 local producer that sees every contribution, not distributed private-input assembly or MPC; its one-shot envelope does not establish the dungeon protocol's temporal multi-party commit-before-reveal, and unbiasedness assumes at least one contribution was uniform conditional on the others. Distinct hosted sessions with identical actor, seed, and move history have the same native proof context because the host SessionId is not part of the native journal.";

/// One exact native Descent verb.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NativeDescentMove {
    Delve,
    /// **The climb** — rise one floor toward the surface for one light. `Flee` is illegal
    /// below the surface, so this is the only way home and it is priced per floor.
    Ascend,
    Unlock {
        way: u64,
    },
    Smite,
    /// **The lunge** — the same wound for one light instead of two, paid with `+1 harm`
    /// (one carry slot, forfeited for the rest of the run).
    Lunge,
    /// Stable relic identifier carried by records and surface adapters.
    /// Conversion to the executor's target-sized collection index happens
    /// only inside [`NativeDescentMove::execute`] and is checked.
    Loot {
        relic: u64,
    },
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
                way: u64::try_from(action.arg)
                    .expect("the matched native unlock argument is non-negative"),
            }),
            (ASCEND, 0) => Ok(Self::Ascend),
            (SMITE, 0) => Ok(Self::Smite),
            (LUNGE, 0) => Ok(Self::Lunge),
            (LOOT, 0..=7) => Ok(Self::Loot {
                relic: u64::try_from(action.arg)
                    .expect("the matched native relic argument is non-negative"),
            }),
            (FLEE, 0) => Ok(Self::Flee),
            // ⚑ BOTH ARMS ARE THE STALE-CONTROL CONDITION, and both used to `{verb:?}` a raw wire
            // string at the reader (a `Debug` dump, quotes and escapes included, of a value that was
            // never theirs to see). A verb this build knows carrying an argument the run does not
            // offer, and a verb this build does not know at all, are the same thing from the reader's
            // side: the control they used is not one the live Descent offers. One shared sentence,
            // from `crate::refusal` — the same one tug, the web, Telegram and Discord say.
            (verb, _) if matches!(verb, DELVE | ASCEND | UNLOCK | SMITE | LUNGE | LOOT | FLEE) => {
                Err(stale_control_refresh())
            }
            _ => Err(stale_control_refresh()),
        }
    }

    fn execute(self, game: &mut Descent) -> Result<TurnReceipt, WorldError> {
        match self {
            Self::Delve => game.delve(),
            Self::Ascend => game.ascend(),
            Self::Unlock { way } => game.unlock(way),
            Self::Smite => game.smite(),
            Self::Lunge => game.lunge(),
            Self::Loot { relic } => {
                let relic = usize::try_from(relic).map_err(|_| {
                    WorldError::Refused(
                        "relic index exceeds the native executor address space".to_string(),
                    )
                })?;
                game.loot(relic)
            }
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
                hasher.update(&relic.to_be_bytes());
            }
            Self::Flee => {
                hasher.update(&[4]);
            }
            // ⚑ A NEW TAG, never a renumber: every tag 0–4 keeps its byte, so an existing
            // run's move-tape hash is unchanged by the arrival of the lunge.
            Self::Lunge => {
                hasher.update(&[5]);
            }
            // …and the same discipline for the climb: tag 6, nothing below it moves.
            Self::Ascend => {
                hasher.update(&[6]);
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

/// One banked relic that became a **real owned asset note** at settlement.
///
/// The [`AssetId`] is `blake3_derive_key(player_pubkey ‖ drop_commitment(run day-seed, banked
/// slot, fair roll, rarity, chest))`, so it content-addresses this run's provenance root, this
/// custody slot, and this player. Re-deriving
/// [`banked_relic_drop`](dungeon_on_dregg::loot::banked_relic_drop) from the run's day-seed and
/// `relic`, then claiming it for the same player, re-mints the byte-identical id — the note
/// **replays to the banked run** rather than to a manufactured draw.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct NativeDescentBankedNote {
    /// The stable relic identifier (the custody slot the relic banked in); never a
    /// target-sized collection offset.
    pub relic: u64,
    /// The minted note's content-addressed asset id — the handle a market names it by.
    pub asset_id: AssetId,
    /// The fair-draw tier of the banked relic's drop (a legendary is a provable ~3% tail).
    pub rarity: Rarity,
    /// The owning player's pubkey at mint (the settling actor's vault identity).
    pub owner: [u8; 32],
}

/// A terminal bank settlement. `settlement_receipt_hash` is the real `flee`
/// executor receipt; banking is the native game's settlement rather than a
/// second application-level promise.
///
/// [`banked_relics`](Self::banked_relics) is the custody read; [`banked_notes`](Self::banked_notes)
/// is what those relics BECAME — real owned [`dreggnet_asset`] notes minted into the session's
/// [`LootVault`] under this run's day-seed. Both are re-derived by exact replay, so a record
/// whose notes do not re-mint is refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativeDescentCompletion {
    pub actor: DreggIdentity,
    pub revision: u64,
    pub root: [u8; 32],
    pub settlement_receipt_hash: [u8; 32],
    /// Stable relic identifiers; never target-sized collection offsets.
    pub banked_relics: Vec<u64>,
    /// The owned asset notes the banked relics minted, in the same slot order as
    /// [`banked_relics`](Self::banked_relics). Empty exactly when the run banked nothing.
    pub banked_notes: Vec<NativeDescentBankedNote>,
    pub crowned: bool,
}

/// Public identity of one exact private-party decision point in a native
/// Descent. The proof's field-sized `session` is derived from all three fields,
/// while the canonical operation envelope carries them losslessly. The hash
/// derivation is therefore domain separation for the underlying proof; this
/// exact context equality is the cross-session/revision replay gate.
#[cfg(any(
    feature = "private-preference-operation",
    feature = "private-raid-operation",
    feature = "private-fair-shuffle-operation"
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

/// One accepted bias-free private initiative deal at an exact native Descent
/// head. The complete permutation and seven cards are absent; only the fixed
/// seat-zero card deliberately opened for public initiative is retained.
#[cfg(feature = "private-fair-shuffle-operation")]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativeDescentPrivateDeal {
    context: NativeDescentPrivateContext,
    deal_root: [u32; SHUFFLE_DIGEST_WIDTH],
    initiative_card: u8,
    receipt_id: [u8; 32],
    canonical_request: Vec<u8>,
}

#[cfg(feature = "private-fair-shuffle-operation")]
impl NativeDescentPrivateDeal {
    pub fn context(&self) -> &NativeDescentPrivateContext {
        &self.context
    }

    pub const fn deal_root(&self) -> [u32; SHUFFLE_DIGEST_WIDTH] {
        self.deal_root
    }

    /// The selectively opened card at fixed seat zero. No other card crosses
    /// the producer boundary.
    pub const fn initiative_card(&self) -> u8 {
        self.initiative_card
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
    /// The run's committed day-seed — the provenance root the banked relics minted under.
    /// Replay redeploys on exactly this seed, and it is folded into the genesis root, so a
    /// record re-pointed at another day's provenance no longer recomputes its own hash chain.
    pub day_seed: CommittedSeed,
    pub actor: Option<DreggIdentity>,
    pub events: Vec<NativeDescentEvent>,
    pub root: [u8; 32],
    pub checkpoint: Option<NativeDescentCheckpoint>,
    pub completion: Option<NativeDescentCompletion>,
    #[cfg(feature = "private-preference-operation")]
    pub private_preference: Option<NativeDescentPrivatePreference>,
    #[cfg(feature = "private-raid-operation")]
    pub private_raid: Option<NativeDescentPrivateRaid>,
    #[cfg(feature = "private-fair-shuffle-operation")]
    pub private_deal: Option<NativeDescentPrivateDeal>,
}

/// One live frontend-neutral session.
pub struct NativeDescentSession {
    seed: u8,
    game: Descent,
    /// The player-owned loot vault this session's BANKED relics mint into at settlement.
    vault: LootVault,
    actor: Option<DreggIdentity>,
    events: Vec<NativeDescentEvent>,
    root: [u8; 32],
    checkpoint: Option<NativeDescentCheckpoint>,
    completion: Option<NativeDescentCompletion>,
    #[cfg(feature = "private-preference-operation")]
    private_preference: Option<NativeDescentPrivatePreference>,
    #[cfg(feature = "private-raid-operation")]
    private_raid: Option<NativeDescentPrivateRaid>,
    #[cfg(feature = "private-fair-shuffle-operation")]
    private_deal: Option<NativeDescentPrivateDeal>,
}

impl NativeDescentSession {
    pub fn actor(&self) -> Option<&DreggIdentity> {
        self.actor.as_ref()
    }

    pub fn game(&self) -> &Descent {
        &self.game
    }

    /// **THIS run's drawn map** — where each relic was minted and how much vitality each floor's
    /// guardian has TODAY.
    ///
    /// Every guardian-shaped number a surface renders (the vitality meter's denominator, whether
    /// the glyph reads slain, how many strikes and how much light are still owed) comes from here,
    /// never from the free `descent::guard_hp`, which is DAY 0's table and is therefore wrong on
    /// fifteen of the sixteen drawn maps.
    pub fn day_world(&self) -> DayWorld {
        self.game.day_world()
    }

    /// The run's committed day-seed — the provenance root this session's banked relics mint
    /// under. Reproducible from the deploy seed unless the offering bound a day
    /// ([`NativeDescentOffering::on_day`] / [`on_beacon`](NativeDescentOffering::on_beacon)).
    pub fn day_seed(&self) -> &CommittedSeed {
        self.game.day_seed()
    }

    /// The session's loot vault — the real owned-note world the settled run's banked relics
    /// were minted into. Provenance, ownership, and rarity of every
    /// [`NativeDescentBankedNote`] read back off this vault.
    pub fn loot_vault(&self) -> &LootVault {
        &self.vault
    }

    /// Take the session's loot vault, to hand the LIVE note world on to a market/inventory
    /// organ (`vault.into_assets()` → `dreggnet_trade::TradeWorld::with_assets`). The minted
    /// notes keep their existing lineage and owner; a consumer must never re-mint them from
    /// display metadata.
    pub fn into_loot_vault(self) -> LootVault {
        self.vault
    }

    /// The full provenance of one settled banked note — the run day-seed + chest (the banked
    /// custody slot) it was drawn from, its fair roll/rarity, and the asset layer's own lineage
    /// re-verification. `None` if the note was not minted by this session's vault.
    pub fn banked_note_provenance(&self, note: &NativeDescentBankedNote) -> Option<LootProvenance> {
        self.vault.provenance(note.asset_id)
    }

    pub fn revision(&self) -> u64 {
        u64::try_from(self.events.len()).expect("the fixed native journal bound fits u64")
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
        feature = "private-raid-operation",
        feature = "private-fair-shuffle-operation"
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

    #[cfg(feature = "private-fair-shuffle-operation")]
    pub fn private_deal(&self) -> Option<&NativeDescentPrivateDeal> {
        self.private_deal.as_ref()
    }

    pub fn export_record(&self) -> NativeDescentRecord {
        NativeDescentRecord {
            seed: self.seed,
            day_seed: *self.game.day_seed(),
            actor: self.actor.clone(),
            events: self.events.clone(),
            root: self.root,
            checkpoint: self.checkpoint.clone(),
            completion: self.completion.clone(),
            #[cfg(feature = "private-preference-operation")]
            private_preference: self.private_preference.clone(),
            #[cfg(feature = "private-raid-operation")]
            private_raid: self.private_raid.clone(),
            #[cfg(feature = "private-fair-shuffle-operation")]
            private_deal: self.private_deal.clone(),
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

/// Canonical BabyBear proof-session id for a private fair initiative deal at
/// this exact native Descent head.
#[cfg(feature = "private-fair-shuffle-operation")]
pub fn native_descent_private_deal_proof_session(context: &NativeDescentPrivateContext) -> u32 {
    private_proof_session(
        "dregg.native-descent.private-initiative-deal.proof-session.v1",
        context,
    )
}

/// Wrap a proved eight-seat fair deal, its public commitment leaves, and the
/// fixed seat-zero selective opening in the exact native-session envelope.
/// Private contributions, rank, the full permutation, and the other cards do
/// not enter this request.
#[cfg(feature = "private-fair-shuffle-operation")]
pub fn encode_native_descent_private_deal(
    context: &NativeDescentPrivateContext,
    commitments: [[u32; SHUFFLE_DIGEST_WIDTH]; SHUFFLE_PARTICIPANTS],
    receipt: &FairShuffleReceipt,
    initiative_opening: FairCardOpening,
) -> Result<Vec<u8>, BinaryOperationError> {
    if receipt.statement().session != native_descent_private_deal_proof_session(context) {
        return Err(BinaryOperationError::Refused(
            "private deal proof session is not derived from the supplied native Descent context"
                .to_string(),
        ));
    }
    let deal = encode_private_deal_payload(commitments, receipt, initiative_opening)?;
    encode_private_operation(PrivateOperationKind::Deal, context, &deal)
}

/// **The run day-seed a bound day mints its banked relics under** — a domain-separated hash of
/// the day's committed beacon seed and the normalized native deploy seed. Distinct days give
/// distinct provenance roots (a banked note cannot be pre-computed before the day's beacon
/// round matures), and distinct worlds within one day keep distinct roots; both are
/// re-derivable by anyone holding the day's seed.
/// **The one deploy-seed normalization.** A [`SessionConfig`] seed is folded into `1..=251` here
/// and nowhere else, so the map a surface PUBLISHES for a seed and the map the session OPENED on
/// that seed cannot come from two different normalizations.
fn normalize_seed(seed: u64) -> u8 {
    ((seed % 251) + 1) as u8
}

pub fn native_descent_run_day_seed(day: &CommittedSeed, seed: u8) -> CommittedSeed {
    let mut hasher = blake3::Hasher::new_derive_key(RUN_DAY_SEED_DOMAIN);
    hasher.update(day.as_bytes());
    hasher.update(&[seed]);
    CommittedSeed::from_bytes(*hasher.finalize().as_bytes())
}

/// **What an offering binds its sessions' provenance roots to.**
///
/// Every session deploys on a *run day-seed* — the provenance root its banked relics mint
/// under. This says where that root comes from, and it is the whole difference between a
/// pre-computable relic id and one that could not exist before a drand round was revealed.
#[derive(Clone, Copy, Debug, Default)]
enum DayBinding {
    /// **No day.** The run day-seed is [`day_seed_from_deploy_seed`] of the normalized deploy
    /// seed: reproducible per seed, and therefore *pre-computable* — fine for a fixture or a
    /// deterministic replay, NOT the live daily posture.
    #[default]
    SeedDerived,
    /// **A verified beacon day.** The run day-seed is
    /// [`native_descent_run_day_seed`]`(day, seed)`, so it is unpredictable until that day's
    /// round was revealed and distinct for every day and every world within a day.
    Day(CommittedSeed),
    /// **An exact already-derived run day-seed** — what a [`NativeDescentRecord`] carries.
    /// The reconstruct path: a verifier that rebuilds a run by re-opening and re-driving its
    /// commands (rather than [`resume_record`](NativeDescentOffering::resume_record), which
    /// reads the record's own day-seed) must deploy on the SAME root or nothing re-derives.
    RunDaySeed(CommittedSeed),
    /// **A live day source, resolved at EVERY open** — the deployed daily posture. A host is
    /// registered once and then serves for weeks, so a day frozen into the offering at
    /// registration would keep minting yesterday's provenance; this asks at open time instead.
    /// `None` from the source REFUSES the open (fail-closed: no verified day, no run), it
    /// never falls back to the pre-computable seed-derived root.
    Live(fn() -> Option<CommittedSeed>),
}

/// The generic Offering adapter for the Lean-native Descent.
///
/// The offering's [`DayBinding`] decides the provenance root every session it opens deploys on:
/// [`new`](Self::new) is the reproducible seed-derived root, [`on_beacon`](Self::on_beacon) /
/// [`on_day`](Self::on_day) bind a real verified beacon day, and
/// [`on_run_day_seed`](Self::on_run_day_seed) pins one exact run's root for re-derivation.
#[derive(Clone, Copy, Debug, Default)]
pub struct NativeDescentOffering {
    day: DayBinding,
}

impl NativeDescentOffering {
    pub fn new() -> Self {
        Self {
            day: DayBinding::SeedDerived,
        }
    }

    /// **Bind this offering to a day's committed seed.** Every session it opens deploys on the
    /// run day-seed [`native_descent_run_day_seed`] derives from it, so the banked relics of
    /// that day's runs mint under that day's provenance root. Pass the seed of a VERIFIED
    /// beacon (or use [`on_beacon`](Self::on_beacon), which verifies for you).
    pub fn on_day(day: CommittedSeed) -> Self {
        Self {
            day: DayBinding::Day(day),
        }
    }

    /// **Bind this offering to today's verified drand beacon** — the live daily path. The
    /// beacon is verified HERE and a beacon that does not verify yields no offering
    /// (fail-closed: you cannot open a forged day), so a banked relic's minted note is
    /// unpredictable-until-revealed and distinct per day.
    pub fn on_beacon(beacon: &DailyBeacon) -> Result<Self, OfferingError> {
        let day = beacon
            .seed()
            .map_err(|error| OfferingError::Deploy(format!("beacon did not verify: {error:?}")))?;
        Ok(Self::on_day(day))
    }

    /// **Pin one exact run day-seed** — the root a [`NativeDescentRecord`] already carries
    /// ([`NativeDescentRecord::day_seed`]). This is the constructor a verifier that re-opens and
    /// re-drives a run's commands needs: without it such a verifier deploys on the
    /// seed-derived root and NOTHING about a beacon-bound run re-derives (its genesis root, and
    /// therefore its whole hash chain and its banked notes, are day-bound). Note that
    /// [`resume_record`](Self::resume_record) needs no such pinning — it reads the record's
    /// day-seed directly, which is why every resume path is already day-agnostic.
    pub fn on_run_day_seed(run_day_seed: CommittedSeed) -> Self {
        Self {
            day: DayBinding::RunDaySeed(run_day_seed),
        }
    }

    /// **The deployed daily binding: ask `source` for today's verified day at EVERY open.**
    ///
    /// A long-lived host registers its offerings once and then serves for weeks. An offering
    /// built with [`on_day`](Self::on_day) would keep minting the day it was registered on, so
    /// a live surface hands this a source that returns the CURRENT day's committed seed —
    /// derived from a beacon its frontend already verified (`DailyBeacon::seed` pairs before it
    /// derives, so a forged reveal never becomes a seed).
    ///
    /// FAIL-CLOSED: when the source has no verified day for right now (never resolved, or the
    /// cached day has rolled and today's round has not been fetched yet), the source returns
    /// `None` and [`open`](Offering::open) REFUSES. It does not quietly fall back to the
    /// pre-computable seed-derived root — a day nobody has revealed is not a day to play.
    pub fn on_day_source(source: fn() -> Option<CommittedSeed>) -> Self {
        Self {
            day: DayBinding::Live(source),
        }
    }

    /// The verified beacon day this offering binds its sessions' provenance roots to right now
    /// — the fixed day of [`on_day`](Self::on_day), or whatever a live source currently
    /// resolves. A seed-derived or run-day-seed-pinned offering names no day.
    pub fn day(&self) -> Option<CommittedSeed> {
        match &self.day {
            DayBinding::Day(day) => Some(*day),
            DayBinding::Live(source) => source(),
            DayBinding::SeedDerived | DayBinding::RunDaySeed(_) => None,
        }
    }

    /// Whether this offering's provenance roots come from a real revealed beacon day rather
    /// than from the (pre-computable) deploy seed. A live daily surface must answer `true`.
    /// A live-source offering answers `true` because that is its posture — whether it can
    /// resolve a day *right now* is [`day`](Self::day), and an unresolvable day refuses the
    /// open rather than degrading.
    pub fn is_day_bound(&self) -> bool {
        matches!(self.day, DayBinding::Day(_) | DayBinding::Live(_))
    }

    /// The run day-seed a session opened at `seed` deploys on. A live binding with no
    /// currently-verified day yields no run day-seed, and therefore no session.
    fn run_day_seed(&self, seed: u8) -> Result<CommittedSeed, OfferingError> {
        match &self.day {
            DayBinding::Day(day) => Ok(native_descent_run_day_seed(day, seed)),
            DayBinding::RunDaySeed(run_day_seed) => Ok(*run_day_seed),
            DayBinding::SeedDerived => Ok(day_seed_from_deploy_seed(seed)),
            DayBinding::Live(source) => source()
                .map(|day| native_descent_run_day_seed(&day, seed))
                .ok_or_else(|| {
                    OfferingError::Deploy(
                        "this Descent is bound to the live daily beacon and no verified day is \
                         resolved right now: refusing to open on a pre-computable provenance \
                         root (fetch today's drand round, then retry)"
                            .to_string(),
                    )
                }),
        }
    }

    /// **The drawn map a session opened at `seed` would play**, without opening one.
    ///
    /// A surface that must publish the day's guardian vitalities *before* (or beside) a session —
    /// the browser play page mirrors them to size its meter — asks HERE. It resolves through this
    /// offering's own [`DayBinding`], the same [`normalize_seed`] the [`open`](Offering::open)
    /// path applies, and the game crate's own `day_index` / `day_world`, so it cannot describe a
    /// different dungeon than the session will. `native_descent::the_published_day_world_is_the_one_a_session_plays`
    /// pins that agreement over every seed on every drawn day.
    ///
    /// A live binding with no currently-verified day resolves no map, exactly as it opens no
    /// session.
    pub fn day_world_for_seed(&self, seed: u64) -> Result<DayWorld, OfferingError> {
        let run_day_seed = self.run_day_seed(normalize_seed(seed))?;
        Ok(day_world(day_index(&run_day_seed)))
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
        let pack = sim.pack();
        // Every label carries WHAT IT COSTS. The light is the whole clock, so a move whose price is
        // invisible is a move a newcomer cannot weigh; naming it turns each button into a verb with
        // a consequence. Presentation only — the mover prices the turn and the executor admits it.
        let mut actions = vec![
            Action::new(
                format!(
                    "↓ Descend to floor {}{}",
                    sim.depth + 1,
                    light_cost(LIGHT_DELVE)
                ),
                DELVE,
                0,
                sim.delve().is_ok(),
            ),
            Action::new(
                format!("⚔ Press the guardian{}", light_cost(LIGHT_SMITE)),
                SMITE,
                0,
                sim.smite().is_ok(),
            ),
            // The same wound for half the light. The label names BOTH prices, because the
            // second one is the whole decision: a forfeited carry slot is invisible until
            // the bottom, where capacity is `CAP - FLOORS` and the prize needs all of it.
            Action::new(
                format!(
                    "⚡ Lunge · one light, one carry slot forfeit ({}/{} grip broken){}",
                    sim.harm,
                    HARMCAP,
                    light_cost(LIGHT_LUNGE)
                ),
                LUNGE,
                0,
                sim.lunge().is_ok(),
            ),
            // ⚑ THE CLIMB. One floor, one light — and it is the ONLY way out, so its price
            // is part of every plan made below the surface, not an afterthought at the end.
            Action::new(
                format!(
                    "↑ Climb to {}{}",
                    if sim.depth <= 1 {
                        "the surface".to_string()
                    } else {
                        format!("floor {}", sim.depth - 1)
                    },
                    light_cost(LIGHT_ASCEND)
                ),
                ASCEND,
                0,
                sim.ascend().is_ok(),
            ),
            Action::new(
                if pack == 0 {
                    format!("⌂ Bank nothing and end the run{}", light_cost(LIGHT_FLEE))
                } else {
                    format!(
                        "⌂ Bank {} carried relic{} and end the run{}",
                        pack,
                        if pack == 1 { "" } else { "s" },
                        light_cost(LIGHT_FLEE)
                    )
                },
                FLEE,
                0,
                sim.flee().is_ok(),
            ),
        ];
        actions.extend((2..=FLOORS).map(|way| {
            Action::new(
                format!(
                    "{GLYPH_KEY} Exercise the key to way {way}{}",
                    light_cost(LIGHT_UNLOCK)
                ),
                UNLOCK,
                i64::try_from(way).expect("the fixed native way set fits the action wire"),
                sim.unlock(way).is_ok(),
            )
        }));
        actions.extend((0..RELICS).map(|relic| {
            Action::new(
                // The VERB is built here; [`relic_label`] is the relic's NAME, because the pack, the
                // vault line, and the minted-note list all read it as one.
                format!(
                    "{} Take the {}{}",
                    relic_glyph(relic),
                    relic_label(relic),
                    light_cost(LIGHT_LOOT)
                ),
                LOOT,
                i64::try_from(relic).expect("the fixed native relic set fits the action wire"),
                sim.loot(relic).is_ok(),
            )
        }));
        // Every frontend consumes this one list directly. Keep the complete action vocabulary —
        // including disabled actions, whose real executor refusals are useful and intentional —
        // but put the moves a player can take NOW before the locked catalogue. FLEE is a legal
        // terminal move almost everywhere; ordering it after other enabled moves keeps newly won
        // loot and newly exercisable keys above the irreversible exit on web, Discord, and the
        // especially tall one-button-per-row Telegram keyboard.
        //
        // `sort_by_key` is stable, so actions within each band retain the authored verb/relic
        // order. This is presentation only: action identities and executor admission are unchanged.
        actions.sort_by_key(|action| match (action.enabled, action.turn.as_str()) {
            (true, FLEE) => 1,
            (true, _) => 0,
            (false, _) => 2,
        });
        actions
    }

    fn verify_exact_record(
        &self,
        session: &NativeDescentSession,
        record: &NativeDescentRecord,
    ) -> VerifyReport {
        let turns = record.events.len() + 1;
        if record.seed != session.seed
            || record.day_seed != *session.game.day_seed()
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
            || {
                #[cfg(feature = "private-fair-shuffle-operation")]
                {
                    record.private_deal != session.private_deal
                }
                #[cfg(not(feature = "private-fair-shuffle-operation"))]
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
        let seed = normalize_seed(cfg.seed.unwrap_or(1));
        let game = Descent::deploy_on_day(seed, self.run_day_seed(seed)?)
            .map_err(|error| OfferingError::Deploy(error.to_string()))?;
        let root = genesis_root(seed, game.day_seed(), game.sim());
        Ok(NativeDescentSession {
            seed,
            game,
            vault: LootVault::new(),
            actor: None,
            events: Vec::new(),
            root,
            checkpoint: None,
            completion: None,
            #[cfg(feature = "private-preference-operation")]
            private_preference: None,
            #[cfg(feature = "private-raid-operation")]
            private_raid: None,
            #[cfg(feature = "private-fair-shuffle-operation")]
            private_deal: None,
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
                // ⚑ NEITHER KEY IS PRINTED. This branch only fires when `bound != actor`, so the
                // reader never needed to tell the two 64-char hex strings apart — and could not read
                // either. What they need is the ACCOUNT diagnosis, which the shared sentence gives.
                return Outcome::Refused(belongs_to_another_player("Descent"));
            }
        }
        let command = match NativeDescentMove::from_action(&input) {
            Ok(command) => command,
            Err(reason) => return Outcome::Refused(reason),
        };
        let receipt = match command.execute(&mut session.game) {
            Ok(receipt) => receipt,
            // ONE arm: `refuse_world_error` hands a rules refusal back verbatim and answers every
            // machinery fault with the shared commit-failure sentence + an operator log line.
            Err(error) => return Outcome::Refused(refuse_world_error(&error)),
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
            // The terminal bank is where a BANKED custody relic becomes a real owned note:
            // mint the run's banked relics into this session's vault under the run day-seed.
            // The mint is driven from the committed custody, so a run that banked nothing
            // mints nothing. It cannot fail here — the draws are the fair `(day_seed, slot)`
            // drops the vault re-verifies, each slot is claimed once, and `fate` latches so
            // this settlement runs exactly once per session.
            let banked_notes = mint_banked_notes(&session.game, &mut session.vault, &actor)
                .expect("a settled run's own banked-relic drops are the vault's fair draws");
            session.completion = Some(completion(
                &actor,
                revision,
                root,
                &post,
                &receipt,
                banked_notes,
            ));
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
            .unwrap_or("unclaimed · the first landed move binds the player");
        let mut children = vec![descent_vitals_section(sim), descent_shaft_section(sim)];
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
                        wants_text: action.wants_text,
                    })
                    .collect(),
            });
        }
        // The bookkeeping a player does not need to read to PLAY — carried/banked by name, who
        // holds the run, the journal head. Below the moves, on purpose.
        children.push(ViewNode::Section {
            title: "The record".to_string(),
            tag: "muted".to_string(),
            children: vec![
                ViewNode::Text(format!("player: {actor}")),
                ViewNode::Text(format!("carried: {}", relics_with_custody(sim, CARRIED))),
                ViewNode::Text(format!("banked: {}", relics_with_custody(sim, BANKED))),
                ViewNode::Text(format!(
                    "revision {} · root {}",
                    session.revision(),
                    short_digest(session.root)
                )),
            ],
        });
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
                    ViewNode::Text(if completion.banked_notes.is_empty() {
                        "no relics banked · nothing was minted".to_string()
                    } else {
                        format!(
                            "minted as owned notes on run day-seed {}: {}",
                            short_digest(*session.day_seed().as_bytes()),
                            completion
                                .banked_notes
                                .iter()
                                .map(|note| format!(
                                    "{} ({}) {}",
                                    relic_label(note.relic as usize),
                                    note.rarity.label(),
                                    short_digest(note.asset_id.bytes())
                                ))
                                .collect::<Vec<String>>()
                                .join(" · ")
                        )
                    }),
                    ViewNode::Text(format!(
                        "proof/share record: actor {} · root {} · receipt {}",
                        completion.actor.as_str(),
                        hex_digest(completion.root),
                        hex_digest(completion.settlement_receipt_hash)
                    )),
                    ViewNode::Text(
                        "re-verify this exact record with this surface's verify control before forwarding it"
                            .to_string(),
                    ),
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
                        "roles {} at revision {} · root {}",
                        roles_line(raid.assignment.roles()),
                        raid.context.revision,
                        short_digest(raid.context.root)
                    )),
                    ViewNode::Text(
                        "private suitability scores and admissibility remain hidden".to_string(),
                    ),
                ],
            });
        }
        #[cfg(feature = "private-fair-shuffle-operation")]
        if let Some(deal) = &session.private_deal {
            children.push(ViewNode::Section {
                title: "Shielded initiative deal".to_string(),
                tag: "genuine".to_string(),
                children: vec![
                    ViewNode::Text(format!(
                        "seat 0 drew initiative card {} at revision {} · root {}",
                        deal.initiative_card,
                        deal.context.revision,
                        short_digest(deal.context.root)
                    )),
                    ViewNode::Text(format!(
                        "commitment to the hidden deal: {}",
                        hex_felts(deal.deal_root)
                    )),
                    ViewNode::Text(
                        "the full permutation, seven cards, rank, and contributions remain hidden"
                            .to_string(),
                    ),
                ],
            });
        }
        Surface(ViewNode::Section {
            title: "The Descent · Lean-authored".to_string(),
            tag: "accent".to_string(),
            children,
        })
    }

    #[cfg(any(
        feature = "private-preference-operation",
        feature = "private-raid-operation",
        feature = "private-fair-shuffle-operation"
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
        #[cfg(feature = "private-fair-shuffle-operation")]
        if session.private_deal.is_none() {
            operations.push(BinaryOperationDescriptor {
                name: NATIVE_DESCENT_PRIVATE_DEAL_OPERATION.to_string(),
                title: format!("Prove a shielded initiative deal for {head}"),
                input_media_type: NATIVE_DESCENT_PRIVATE_DEAL_MEDIA_TYPE.to_string(),
                max_input_bytes: MAX_NATIVE_DESCENT_PRIVATE_OPERATION_BYTES,
                disclosure: NATIVE_DESCENT_PRIVATE_DEAL_DISCLOSURE.to_string(),
            });
        }
        operations
    }

    #[cfg(any(
        feature = "private-preference-operation",
        feature = "private-raid-operation",
        feature = "private-fair-shuffle-operation"
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
        #[cfg(feature = "private-fair-shuffle-operation")]
        if name == NATIVE_DESCENT_PRIVATE_DEAL_OPERATION {
            let (_, _, canonical) = parse_private_deal_request(session, payload)?;
            return Ok(Some(BinaryOperationReplayMaterial::new(
                canonical,
                NATIVE_DESCENT_PRIVATE_DEAL_DISCLOSURE,
            )));
        }
        Err(BinaryOperationError::UnknownOperation(name.to_string()))
    }

    #[cfg(any(
        feature = "private-preference-operation",
        feature = "private-raid-operation",
        feature = "private-fair-shuffle-operation"
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
        #[cfg(feature = "private-fair-shuffle-operation")]
        if name == NATIVE_DESCENT_PRIVATE_DEAL_OPERATION {
            return apply_private_deal(session, payload, actor);
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
    let mut game =
        Descent::deploy_on_day(record.seed, record.day_seed).map_err(|error| error.to_string())?;
    let mut vault = LootVault::new();
    let mut root = genesis_root(record.seed, game.day_seed(), game.sim());
    #[cfg(any(
        feature = "private-preference-operation",
        feature = "private-raid-operation",
        feature = "private-fair-shuffle-operation"
    ))]
    let genesis = root;
    let mut actor: Option<DreggIdentity> = None;
    let mut checkpoint = None;
    let mut derived_completion = None;

    for (index, expected) in record.events.iter().enumerate() {
        let revision = u64::try_from(index + 1)
            .expect("the fixed native journal bound fits the revision wire");
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
            // Re-mint the run's banked relics into a FRESH vault. This is the provenance
            // replay: the notes must re-derive byte-identically from the record's day-seed
            // and the committed banked slots, or the completion below no longer matches.
            let banked_notes =
                mint_banked_notes(&game, &mut vault, &expected.actor).map_err(|error| {
                    format!("event {revision} banked relics did not re-mint: {error}")
                })?;
            derived_completion = Some(completion(
                &expected.actor,
                revision,
                root,
                &expected.post,
                &expected.receipt,
                banked_notes,
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
    #[cfg(feature = "private-fair-shuffle-operation")]
    let private_deal = match &record.private_deal {
        Some(expected) => Some(replay_private_deal(record, genesis, expected)?),
        None => None,
    };
    Ok(NativeDescentSession {
        seed: record.seed,
        game,
        vault,
        actor,
        events: record.events.clone(),
        root,
        checkpoint,
        completion: derived_completion,
        #[cfg(feature = "private-preference-operation")]
        private_preference,
        #[cfg(feature = "private-raid-operation")]
        private_raid,
        #[cfg(feature = "private-fair-shuffle-operation")]
        private_deal,
    })
}

#[cfg(any(
    feature = "private-preference-operation",
    feature = "private-raid-operation",
    feature = "private-fair-shuffle-operation"
))]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum PrivateOperationKind {
    Preference = 1,
    Raid = 2,
    Deal = 3,
}

#[cfg(any(
    feature = "private-preference-operation",
    feature = "private-raid-operation",
    feature = "private-fair-shuffle-operation"
))]
impl PrivateOperationKind {
    fn from_byte(byte: u8) -> Result<Self, BinaryOperationError> {
        match byte {
            1 => Ok(Self::Preference),
            2 => Ok(Self::Raid),
            3 => Ok(Self::Deal),
            other => Err(BinaryOperationError::Malformed(format!(
                "unknown native Descent private-operation kind {other}"
            ))),
        }
    }
}

#[cfg(any(
    feature = "private-preference-operation",
    feature = "private-raid-operation",
    feature = "private-fair-shuffle-operation"
))]
struct PrivateOperationEnvelope {
    context: NativeDescentPrivateContext,
    proof: Vec<u8>,
}

#[cfg(any(
    feature = "private-preference-operation",
    feature = "private-raid-operation",
    feature = "private-fair-shuffle-operation"
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
    feature = "private-raid-operation",
    feature = "private-fair-shuffle-operation"
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
    feature = "private-raid-operation",
    feature = "private-fair-shuffle-operation"
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
    feature = "private-raid-operation",
    feature = "private-fair-shuffle-operation"
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
        // ⚑ NEITHER KEY IS PRINTED — same condition, same shared sentence as `advance`'s binding
        // check. The two 64-char hex strings this used to print were unreadable and, since the branch
        // only fires when they differ, unnecessary.
        return Err(BinaryOperationError::Refused(belongs_to_another_player(
            "Descent",
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
            ("ballotRoot".to_string(), hex_felts(decision.ballot_root())),
            ("winner".to_string(), decision.winner().to_string()),
            (
                "plan".to_string(),
                crate::dungeon::PRIVATE_PREFERENCE_OPTIONS[decision.winner()].to_string(),
            ),
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
            ("inputRoot".to_string(), hex_felts(assignment.input_root())),
            ("roles".to_string(), roles_line(assignment.roles())),
        ],
    })
}

#[cfg(feature = "private-fair-shuffle-operation")]
struct PrivateDealPayload {
    commitments: [[u32; SHUFFLE_DIGEST_WIDTH]; SHUFFLE_PARTICIPANTS],
    receipt: FairShuffleReceipt,
    opening: FairCardOpening,
}

#[cfg(feature = "private-fair-shuffle-operation")]
fn encode_private_deal_payload(
    commitments: [[u32; SHUFFLE_DIGEST_WIDTH]; SHUFFLE_PARTICIPANTS],
    receipt: &FairShuffleReceipt,
    opening: FairCardOpening,
) -> Result<Vec<u8>, BinaryOperationError> {
    let receipt_bytes = receipt
        .to_postcard()
        .map_err(|error| BinaryOperationError::Malformed(error.to_string()))?;
    let opening_bytes = opening
        .to_postcard()
        .map_err(|error| BinaryOperationError::Malformed(error.to_string()))?;
    let receipt_len = u64::try_from(receipt_bytes.len()).map_err(|_| {
        BinaryOperationError::Malformed("private deal receipt length does not fit wire".to_string())
    })?;
    let opening_len = u64::try_from(opening_bytes.len()).map_err(|_| {
        BinaryOperationError::Malformed("private deal opening length does not fit wire".to_string())
    })?;
    let mut bytes = Vec::with_capacity(
        1 + SHUFFLE_PARTICIPANTS * SHUFFLE_DIGEST_WIDTH * 4
            + 8
            + receipt_bytes.len()
            + 8
            + opening_bytes.len(),
    );
    bytes.push(1);
    for commitment in commitments {
        for lane in commitment {
            bytes.extend_from_slice(&lane.to_be_bytes());
        }
    }
    bytes.extend_from_slice(&receipt_len.to_be_bytes());
    bytes.extend_from_slice(&receipt_bytes);
    bytes.extend_from_slice(&opening_len.to_be_bytes());
    bytes.extend_from_slice(&opening_bytes);
    if bytes.len() > MAX_NATIVE_DESCENT_PRIVATE_OPERATION_BYTES {
        return Err(BinaryOperationError::Malformed(format!(
            "private deal payload is {} bytes; maximum is {MAX_NATIVE_DESCENT_PRIVATE_OPERATION_BYTES}",
            bytes.len()
        )));
    }
    Ok(bytes)
}

#[cfg(feature = "private-fair-shuffle-operation")]
fn decode_private_deal_payload(bytes: &[u8]) -> Result<PrivateDealPayload, BinaryOperationError> {
    let mut reader = PrivateOperationReader::new(bytes);
    let version = reader.byte()?;
    if version != 1 {
        return Err(BinaryOperationError::Malformed(format!(
            "unsupported native Descent private-deal payload version {version}"
        )));
    }
    let mut commitments = [[0u32; SHUFFLE_DIGEST_WIDTH]; SHUFFLE_PARTICIPANTS];
    for commitment in &mut commitments {
        for lane in commitment {
            *lane = reader.u32()?;
        }
    }
    let receipt_len = usize::try_from(reader.u64()?).map_err(|_| {
        BinaryOperationError::Malformed(
            "private deal receipt length does not fit usize".to_string(),
        )
    })?;
    let receipt_bytes = reader.bytes(receipt_len)?;
    let receipt = FairShuffleReceipt::from_postcard(receipt_bytes)
        .map_err(|error| BinaryOperationError::Malformed(error.to_string()))?;
    if receipt
        .to_postcard()
        .map_err(|error| BinaryOperationError::Malformed(error.to_string()))?
        != receipt_bytes
    {
        return Err(BinaryOperationError::Malformed(
            "private deal receipt is not canonically encoded".to_string(),
        ));
    }
    let opening_len = usize::try_from(reader.u64()?).map_err(|_| {
        BinaryOperationError::Malformed(
            "private deal opening length does not fit usize".to_string(),
        )
    })?;
    let opening_bytes = reader.bytes(opening_len)?;
    let opening = FairCardOpening::from_postcard(opening_bytes)
        .map_err(|error| BinaryOperationError::Malformed(error.to_string()))?;
    if opening
        .to_postcard()
        .map_err(|error| BinaryOperationError::Malformed(error.to_string()))?
        != opening_bytes
    {
        return Err(BinaryOperationError::Malformed(
            "private deal opening is not canonically encoded".to_string(),
        ));
    }
    reader.finish()?;
    let payload = PrivateDealPayload {
        commitments,
        receipt,
        opening,
    };
    if encode_private_deal_payload(payload.commitments, &payload.receipt, payload.opening)? != bytes
    {
        return Err(BinaryOperationError::Malformed(
            "private deal payload is not canonically encoded".to_string(),
        ));
    }
    Ok(payload)
}

#[cfg(feature = "private-fair-shuffle-operation")]
fn verify_private_deal_payload(
    context: &NativeDescentPrivateContext,
    payload: &[u8],
) -> Result<([u32; SHUFFLE_DIGEST_WIDTH], u8), BinaryOperationError> {
    let deal = decode_private_deal_payload(payload)?;
    let expected_session = native_descent_private_deal_proof_session(context);
    let statement = deal.receipt.statement();
    if statement.session != expected_session {
        return Err(BinaryOperationError::Refused(format!(
            "private deal proof session mismatch: expected {expected_session}, claimed {}",
            statement.session
        )));
    }
    if statement.attempt != 0 {
        return Err(BinaryOperationError::Refused(format!(
            "native Descent initiative deal requires attempt 0, claimed {}",
            statement.attempt
        )));
    }
    if deal.opening.seat != 0 {
        return Err(BinaryOperationError::Refused(format!(
            "native Descent initiative reveals fixed seat 0, claimed seat {}",
            deal.opening.seat
        )));
    }
    let mut table = FairShuffleTable::new(expected_session)
        .map_err(|error| BinaryOperationError::Refused(error.to_string()))?;
    for (participant, commitment) in deal.commitments.into_iter().enumerate() {
        table
            .commit(participant, commitment)
            .map_err(|error| BinaryOperationError::Refused(error.to_string()))?;
    }
    let outcome = table
        .accept_attempt(&deal.receipt)
        .map_err(|error| BinaryOperationError::Refused(error.to_string()))?;
    if outcome != FairShuffleAttemptOutcome::Accepted {
        return Err(BinaryOperationError::Refused(
            "native Descent initiative requires an accepted bias-free deal; rejected attempt is not a deal"
                .to_string(),
        ));
    }
    let card = table
        .reveal_card(deal.opening)
        .map_err(|error| BinaryOperationError::Refused(error.to_string()))?;
    Ok((statement.deal_root, card))
}

#[cfg(feature = "private-fair-shuffle-operation")]
fn parse_private_deal_request(
    session: &NativeDescentSession,
    payload: &[u8],
) -> Result<(NativeDescentPrivateContext, Vec<u8>, Vec<u8>), BinaryOperationError> {
    let envelope = decode_private_operation(PrivateOperationKind::Deal, payload)?;
    validate_live_private_context(session, &envelope.context)?;
    if session.private_deal.is_some() {
        return Err(BinaryOperationError::Refused(
            "this native Descent already has a private initiative deal".to_string(),
        ));
    }
    let deal = decode_private_deal_payload(&envelope.proof)?;
    let statement = deal.receipt.statement();
    let expected_session = native_descent_private_deal_proof_session(&envelope.context);
    if statement.session != expected_session {
        return Err(BinaryOperationError::Refused(format!(
            "private deal proof session mismatch: expected {expected_session}, claimed {}",
            statement.session
        )));
    }
    if statement.attempt != 0 {
        return Err(BinaryOperationError::Refused(format!(
            "native Descent initiative deal requires attempt 0, claimed {}",
            statement.attempt
        )));
    }
    if deal.opening.seat != 0 {
        return Err(BinaryOperationError::Refused(format!(
            "native Descent initiative reveals fixed seat 0, claimed seat {}",
            deal.opening.seat
        )));
    }
    Ok((envelope.context, envelope.proof, payload.to_vec()))
}

#[cfg(feature = "private-fair-shuffle-operation")]
fn apply_private_deal(
    session: &mut NativeDescentSession,
    payload: &[u8],
    actor: DreggIdentity,
) -> Result<BinaryOperationReceipt, BinaryOperationError> {
    let (context, proof_payload, canonical_request) = parse_private_deal_request(session, payload)?;
    if actor != context.actor {
        return Err(BinaryOperationError::Refused(format!(
            "private initiative deal was bound to actor {}; {} submitted it",
            context.actor.as_str(),
            actor.as_str()
        )));
    }
    let (deal_root, initiative_card) = verify_private_deal_payload(&context, &proof_payload)?;
    let receipt_id = private_operation_receipt_id(
        "dregg.native-descent.private-initiative-deal.receipt.v1",
        &canonical_request,
    );
    session.private_deal = Some(NativeDescentPrivateDeal {
        context: context.clone(),
        deal_root,
        initiative_card,
        receipt_id,
        canonical_request,
    });
    Ok(BinaryOperationReceipt {
        operation: NATIVE_DESCENT_PRIVATE_DEAL_OPERATION.to_string(),
        receipt_id,
        public_fields: vec![
            ("actor".to_string(), context.actor.as_str().to_string()),
            ("revision".to_string(), context.revision.to_string()),
            ("root".to_string(), hex_digest(context.root)),
            (
                "proofSession".to_string(),
                native_descent_private_deal_proof_session(&context).to_string(),
            ),
            ("dealRoot".to_string(), hex_felts(deal_root)),
            ("initiativeSeat".to_string(), "0".to_string()),
            ("initiativeCard".to_string(), initiative_card.to_string()),
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

#[cfg(feature = "private-fair-shuffle-operation")]
fn replay_private_deal(
    record: &NativeDescentRecord,
    genesis: [u8; 32],
    expected: &NativeDescentPrivateDeal,
) -> Result<NativeDescentPrivateDeal, String> {
    validate_recorded_private_context(record, genesis, &expected.context)?;
    let envelope =
        decode_private_operation(PrivateOperationKind::Deal, &expected.canonical_request)
            .map_err(|error| error.to_string())?;
    if envelope.context != expected.context {
        return Err("private deal envelope substituted its native context".to_string());
    }
    let (deal_root, initiative_card) =
        verify_private_deal_payload(&expected.context, &envelope.proof)
            .map_err(|error| error.to_string())?;
    let actual = NativeDescentPrivateDeal {
        context: expected.context.clone(),
        deal_root,
        initiative_card,
        receipt_id: private_operation_receipt_id(
            "dregg.native-descent.private-initiative-deal.receipt.v1",
            &expected.canonical_request,
        ),
        canonical_request: expected.canonical_request.clone(),
    };
    if &actual != expected {
        return Err("private initiative deal record differs from exact proof replay".to_string());
    }
    Ok(actual)
}

#[cfg(any(
    feature = "private-preference-operation",
    feature = "private-raid-operation",
    feature = "private-fair-shuffle-operation"
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
    feature = "private-raid-operation",
    feature = "private-fair-shuffle-operation"
))]
fn private_operation_receipt_id(domain: &str, canonical_request: &[u8]) -> [u8; 32] {
    *blake3::Hasher::new_derive_key(domain)
        .update(canonical_request)
        .finalize()
        .as_bytes()
}

#[cfg(any(
    feature = "private-preference-operation",
    feature = "private-raid-operation",
    feature = "private-fair-shuffle-operation"
))]
struct PrivateOperationReader<'a> {
    bytes: &'a [u8],
    position: usize,
}

#[cfg(any(
    feature = "private-preference-operation",
    feature = "private-raid-operation",
    feature = "private-fair-shuffle-operation"
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

    #[cfg(feature = "private-fair-shuffle-operation")]
    fn u32(&mut self) -> Result<u32, BinaryOperationError> {
        Ok(u32::from_be_bytes(self.array()?))
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

/// The journal's genesis root. It commits to the deploy seed, the run's day-seed (the
/// provenance root the banked relics will mint under), the exact Lean-emitted program, and the
/// genesis state — so a record cannot be re-pointed at another day's provenance without
/// breaking its whole hash chain.
fn genesis_root(seed: u8, day_seed: &CommittedSeed, sim: &Sim) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(GENESIS_ROOT_DOMAIN);
    hasher.update(&[seed]);
    hasher.update(day_seed.as_bytes());
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

/// **Mint the settled run's BANKED relics into `vault` as real owned notes.** Delegates to
/// [`Descent::mint_banked_relics`], which iterates the run's COMMITTED custody and feeds each
/// BANKED slot plus the run's day-seed through the loot vault's forged-claim gate — so the
/// notes are the banked relics' own fair `(day_seed, slot)` drops, in slot order, and a run
/// that banked nothing mints nothing.
fn mint_banked_notes(
    game: &Descent,
    vault: &mut LootVault,
    actor: &DreggIdentity,
) -> Result<Vec<NativeDescentBankedNote>, LootError> {
    Ok(game
        .mint_banked_relics(vault, actor.as_str())?
        .into_iter()
        .map(|BankedRelicMint { slot, item }| NativeDescentBankedNote {
            relic: u64::try_from(slot).expect("the fixed native relic set fits the stable wire"),
            asset_id: item.asset_id,
            rarity: item.rarity,
            owner: item.owner,
        })
        .collect())
}

fn completion(
    actor: &DreggIdentity,
    revision: u64,
    root: [u8; 32],
    sim: &Sim,
    receipt: &TurnReceipt,
    banked_notes: Vec<NativeDescentBankedNote>,
) -> NativeDescentCompletion {
    let banked_relics: Vec<u64> = sim
        .custody
        .iter()
        .enumerate()
        .filter_map(|(relic, custody)| {
            (*custody == BANKED).then(|| {
                u64::try_from(relic).expect("the fixed native relic set fits the stable wire")
            })
        })
        .collect();
    debug_assert_eq!(
        banked_relics,
        banked_notes
            .iter()
            .map(|note| note.relic)
            .collect::<Vec<u64>>(),
        "the minted notes are exactly the committed banked custody, in slot order"
    );
    NativeDescentCompletion {
        actor: actor.clone(),
        revision,
        root,
        settlement_receipt_hash: receipt.receipt_hash(),
        crowned: banked_relics.contains(&0),
        banked_relics,
        banked_notes,
    }
}

/// **A RELIC'S NAME — a noun, and the same noun everywhere.**
///
/// This used to return `"Take the key-relic for way 2"`, an imperative built for the LOOT button,
/// and three other readers used it as a name: the pack and vault lines read `carried: Take the
/// key-relic for way 2 · Take the Crown of the Deep` and the minted-note list read
/// `Take treasure relic 4 (rare) 3f9c…`. A player cannot tell the story of a run whose relics are
/// verbs and whose treasures are indices, so the noun lives here and the verb is built at the
/// button ([`Self::actions_for_sim`] wraps it in "Take the …").
///
/// The names are per-SLOT identity — relic 0 is the prize on every drawn map and 1–3 are the way
/// keys by construction (`homes (keyFor w) < w`) — so they are not a day fact and cannot go stale
/// with the draw. Where a relic LIES is read from the day-world; only what it is called is fixed.
fn relic_label(relic: usize) -> String {
    match relic {
        0 => "Crown of the Deep".to_string(),
        1..=3 => format!("Ward-key of the {} way", ordinal_word(relic + 1)),
        4 => "Ashen Chalice".to_string(),
        5 => "Verdigris Coil".to_string(),
        6 => "Bone Astrolabe".to_string(),
        _ => "Salt-Wept Idol".to_string(),
    }
}

/// The ordinal a way is spoken by. Only ways `2..=FLOORS` are ever named (way 1 is the mouth and
/// always open), so the fallback is the bare number rather than a wrong word.
fn ordinal_word(way: usize) -> String {
    match way {
        2 => "second".to_string(),
        3 => "third".to_string(),
        4 => "fourth".to_string(),
        other => format!("{other}th"),
    }
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// THE DUNGEON, PAINTED — the map, the light, the pack, the guardian.
//
// PRESENTATION ONLY. Everything below reads the mover's own public projections (`Sim::pack`,
// `hoard_at`, `way_open`, the `delve/smite/loot/unlock/flee` legality probes) and the Lean-sourced
// constants; it derives no rule of its own, and the executor stays the referee for every move.
// ═══════════════════════════════════════════════════════════════════════════════════════════

/// The map's glyph vocabulary — ONE character per cell, so the shared
/// [`coordgrid_text`](deos_view::coordgrid_text) projection stays column-aligned on every text
/// channel (a Discord embed, a Telegram message, a WeChat reply block) as well as in pixels.
const GLYPH_EMPTY: &str = "·";
/// The floor you stand on. It is a GLYPH, not a highlight: `highlight` means "you may act on this
/// NOW" (the text projection brackets it `[x]`), and standing somewhere is not an action.
const GLYPH_YOU: &str = ">";
const GLYPH_WAY_OPEN: &str = "/";
const GLYPH_WAY_SHUT: &str = "#";
/// A guardian still standing paints the BLOWS IT OWES (a digit), not a letter — see the guardian
/// column in [`descent_map`]. This is the fallen one.
const GLYPH_GUARDIAN_SLAIN: &str = "x";
const GLYPH_CROWN: &str = "C";
const GLYPH_KEY: &str = "k";
const GLYPH_TREASURE: &str = "*";
/// The pack row's marker — what is ON YOU right now, and still losable.
const GLYPH_PACK: &str = "@";
/// The vault row's marker — what a proved exit already made yours.
const GLYPH_VAULT: &str = "$";

/// The map is `marker + way + guardian + one column PER RELIC` wide. A relic's column is FIXED, so
/// you watch it travel: from the row of the floor it lies on, up into the pack row when you take
/// it, and into the vault row when a proved exit banks it. Relic 0 is the crown, 1–3 the keys to
/// ways 2–4, 4–7 the treasures — the column order is the relic index, so the legend needs one line.
const MAP_COLS: usize = 3 + RELICS;

/// The light each verb spends. These label the affordances so a move reads as a verb WITH A
/// CONSEQUENCE ("Descend to floor 2 · 1 light") instead of a bare noun — the single most useful
/// thing a stranger can be told, because the light IS the game. The mover still prices every turn;
/// a label can only describe.
///
/// `pub` because the browser play page mirrors them to word the same sentences, and
/// `dreggnet-web/tests/descent_play_map.rs` pins that mirror against THESE — a price that moves
/// here must move there or the pin goes red.
const LIGHT_DELVE: u64 = 1;
pub const LIGHT_ASCEND: u64 = 1;
const LIGHT_UNLOCK: u64 = 1;
const LIGHT_SMITE: u64 = 2;
const LIGHT_LUNGE: u64 = 1;
const LIGHT_LOOT: u64 = 1;
pub const LIGHT_FLEE: u64 = 1;

/// `"… · 2 light"` — the cost tail every affordance label carries.
fn light_cost(cost: u64) -> String {
    format!(" · {cost} light")
}

/// The glyph a relic paints in its map column (its KIND: the crown, a way key, a treasure).
fn relic_glyph(relic: usize) -> &'static str {
    match relic {
        0 => GLYPH_CROWN,
        1..=3 => GLYPH_KEY,
        _ => GLYPH_TREASURE,
    }
}

/// The semantic palette tag a relic's cell paints in (the renderer's `tag-*` class / icon tint).
fn relic_tag(relic: usize) -> &'static str {
    match relic {
        0 => "accent",
        1..=3 => "warn",
        _ => "good",
    }
}

fn map_cell(glyph: &str, tag: &str, highlight: bool) -> CoordCell {
    CoordCell {
        glyph: glyph.to_string(),
        tag: tag.to_string(),
        // INERT BY CONSTRUCTION. The `Menu` below is the surface's SINGLE affordance carrier, so a
        // 66-square board never doubles every move: Discord's component budget is 25 buttons and
        // WeChat's numbered reply list would otherwise offer each move twice. The board's job is to
        // SHOW what is actionable (`highlight`); pressing it is the menu's job.
        turn: String::new(),
        arg: 0,
        highlight,
    }
}

/// **The shaft, as a coordinate board.** Four floor rows, then the pack row, then the vault row.
///
/// A cell is HIGHLIGHTED exactly when it is actionable *right now* — the way you may descend or
/// unlock, the guardian you may strike, the relic you may take — so the board answers "what can I
/// do?" before you read a single button. Legality comes from the mover's own probes, never from a
/// re-derived rule here.
fn descent_map(sim: &Sim) -> ViewNode {
    let mut cells: Vec<CoordCell> = Vec::with_capacity(MAP_COLS * (FLOORS as usize + 2));

    for floor in 1..=FLOORS {
        let standing_here = sim.depth == floor;
        // The row marker — the floor's depth, or `>` on the floor you stand on. NOT highlighted:
        // the highlight means "actionable now", and where you are standing is not a move.
        let marker = if standing_here {
            GLYPH_YOU.to_string()
        } else {
            floor.to_string()
        };
        cells.push(map_cell(
            &marker,
            if standing_here { "accent" } else { "muted" },
            false,
        ));

        // The way INTO this floor. Floor 1 is the mouth (always open); a deeper way opens only once
        // its key-relic has been EXERCISED. Highlighted when you may step through it now, or when
        // you carry the key that opens it.
        let open = sim.way_open(floor);
        let passable_now = floor == sim.depth + 1 && sim.delve().is_ok();
        let openable_now = floor >= 2 && sim.unlock(floor).is_ok();
        cells.push(map_cell(
            if open { GLYPH_WAY_OPEN } else { GLYPH_WAY_SHUT },
            if open { "good" } else { "bad" },
            passable_now || openable_now,
        ));

        // ⚑ THE FLOOR'S PRICE, NOT JUST ITS OCCUPANT. This cell used to be a flat `G` on every
        // floor, so the board told you WHERE the relics were and never what reaching them costs —
        // and guardian vitality is drawn from the committed day-seed, so it IS the difference
        // between today's dungeon and yesterday's. A player who cannot read it cannot budget the
        // light until they are already standing in the fight.
        //
        // The glyph is the BLOWS THE GUARDIAN STILL OWES: on the floor you stand on, what is left
        // of this fight (wounds are per-standing-floor); on a floor below, what that fight opens at.
        // Read off `sim.guard_hp` — the run's own drawn map — so it is a DAY fact, never a literal.
        // One character, so the grid stays column-aligned on every text channel.
        let vitality = sim.guard_hp(floor);
        let owed = vitality.saturating_sub(if standing_here { sim.wounds } else { 0 });
        let slain_here = standing_here && vitality > 0 && owed == 0;
        let guardian_glyph = if vitality == 0 {
            // No guardian was minted on this floor at all. Say nothing stands here rather than
            // calling an absence a corpse — no drawn day does this, and the surface still must not
            // invent one.
            GLYPH_EMPTY.to_string()
        } else if owed == 0 {
            GLYPH_GUARDIAN_SLAIN.to_string()
        } else {
            owed.to_string()
        };
        cells.push(map_cell(
            &guardian_glyph,
            match (standing_here, slain_here) {
                (true, true) => "good",
                (true, false) => "bad",
                _ => "muted",
            },
            standing_here && (sim.smite().is_ok() || sim.lunge().is_ok()),
        ));

        // One column per relic: the relics LYING on this floor.
        for relic in 0..RELICS {
            if sim.custody[relic] == floor {
                cells.push(map_cell(
                    relic_glyph(relic),
                    relic_tag(relic),
                    sim.loot(relic).is_ok(),
                ));
            } else {
                cells.push(map_cell(GLYPH_EMPTY, "muted", false));
            }
        }
    }

    // The pack row — carried, and still losable: the light dying with these on you banks nothing.
    cells.push(map_cell(GLYPH_PACK, "accent", false));
    cells.push(map_cell(GLYPH_EMPTY, "muted", false));
    cells.push(map_cell(GLYPH_EMPTY, "muted", false));
    for relic in 0..RELICS {
        if sim.custody[relic] == CARRIED {
            cells.push(map_cell(relic_glyph(relic), relic_tag(relic), true));
        } else {
            cells.push(map_cell(GLYPH_EMPTY, "muted", false));
        }
    }

    // The vault row — what a proved exit already made yours.
    cells.push(map_cell(GLYPH_VAULT, "good", false));
    cells.push(map_cell(GLYPH_EMPTY, "muted", false));
    cells.push(map_cell(GLYPH_EMPTY, "muted", false));
    for relic in 0..RELICS {
        if sim.custody[relic] == BANKED {
            cells.push(map_cell(relic_glyph(relic), "good", false));
        } else {
            cells.push(map_cell(GLYPH_EMPTY, "muted", false));
        }
    }

    ViewNode::CoordGrid {
        cols: MAP_COLS,
        cells,
    }
}

/// **THE VITALS PLAQUE — the Descent's own reading of a [`Sim`].** One status badge, the prose
/// standing, the light/pack/guardian/banked meters, then the ⚠ pressure lines.
///
/// `pub(crate)` because the CAMPAIGN wraps this exact `Sim` ([`crate::campaign`] opens a native
/// expedition per region location) and must speak this exact vocabulary. It used to render a flat
/// `depth 2 · light spent 9 · wounds 1` counter dump beside a menu while the whole reading sat one
/// module away — two descriptions of one state, and only one of them was legible. There is now one
/// painter and both surfaces call it, so a meter added here reaches both.
pub(crate) fn descent_vitals_section(sim: &Sim) -> ViewNode {
    let (status, status_tag) = descent_status(sim);
    let light = BREATH.saturating_sub(sim.spent);
    // Carrying rights ATTENUATE with depth AND with harm: the capacity law the mover enforces is
    // `pack + depth + harm ≤ CAP` (`Sim::delve` / `Sim::lunge` / `Sim::loot` in
    // `dungeon_on_dregg::descent`), so the pack meter's ceiling MOVES as you descend and MOVES
    // AGAIN every time a lunge breaks your grip.
    //
    // ⚑ `harm` was missing from this denominator, and it was the one term a player could not infer.
    // After a lunge the meter read `2/5` while `loot` would refuse at 2 — the bar showed room the
    // run did not have, in the exact moment (a guardian just felled, a hoard just lit) where the
    // decision it was supposed to inform is taken. `depth` at least announces itself in the floor
    // title; a forfeited carry slot is invisible everywhere else.
    let carry_rights = CAP.saturating_sub(sim.depth + sim.harm);

    // ── THE VITALS: one badge, three meters. The light is the clock; the pack is the ceiling;
    //    the guardian is the toll. Labels are padded to a common width so the bars stack into
    //    an aligned column on the prose channels too. ──
    let mut vitals = vec![
        ViewNode::Pill {
            text: status.to_string(),
            tag: status_tag.to_string(),
            slot: None,
            cases: Vec::new(),
        },
        ViewNode::Text(descent_standing(sim)),
        ViewNode::Progress {
            value: light,
            max: BREATH,
            label: "light   ".to_string(),
        },
        ViewNode::Progress {
            value: sim.pack(),
            max: carry_rights,
            label: "pack    ".to_string(),
        },
    ];
    if sim.depth >= 1 {
        vitals.push(ViewNode::Progress {
            value: sim.wounds,
            // THIS DAY's guardian, off the run's own drawn map — never the day-0 table. A
            // meter reading `0/1` where today's guardian has two points of vitality tells a
            // player one blow will open the hoard, and it will not.
            max: sim.guard_hp(sim.depth),
            label: "guardian".to_string(),
        });
    }
    vitals.push(ViewNode::Progress {
        value: sim.bank(),
        max: RELICS as u64,
        label: "banked  ".to_string(),
    });
    vitals.extend(descent_pressures(sim));
    ViewNode::Section {
        title: descent_floor_title(sim),
        tag: if sim.fate == 0 { "accent" } else { "genuine" }.to_string(),
        children: vitals,
    }
}

/// Where the run STANDS, as a section title — the mouth, a numbered floor, or the frozen tomb.
pub(crate) fn descent_floor_title(sim: &Sim) -> String {
    match (sim.fate, sim.depth) {
        (0, 0) => "The living descent · at the mouth".to_string(),
        (0, depth) => format!("The living descent · floor {depth} of {FLOORS}"),
        _ => "The banked tomb".to_string(),
    }
}

/// **THE SHAFT — the board plus the two lines that read it.** The other half of the Descent's
/// vocabulary the campaign reuses; a `CoordGrid` lands in the shared night well on every renderer.
pub(crate) fn descent_shaft_section(sim: &Sim) -> ViewNode {
    let mut shaft = vec![descent_map(sim)];
    shaft.extend(map_legend());
    ViewNode::Section {
        title: "The shaft".to_string(),
        tag: "accent".to_string(),
        children: shaft,
    }
}

/// The lines that make the board readable without a manual.
///
/// ⚑ The BRACKET half is [`deos_view::coordgrid_legend`], not words of ours. It used to be a
/// hand-written `[ ] you may act on it now` clause, which was the whole vocabulary while the shared
/// projection painted the bracket from `highlight` alone. That projection now paints the CELL'S ROLE
/// too (a `warn` cell you may act on — here, a way-key — reads `(k)`), and a legend that names one
/// mark while the board paints five is worse than no legend. Reading it from the projection means it
/// cannot drift again.
fn map_legend() -> Vec<ViewNode> {
    vec![
        ViewNode::Text(format!(
            "rows: floors 1–{FLOORS} · {GLYPH_PACK} your pack (still losable) · {GLYPH_VAULT} banked (yours). \
             columns: floor · way · guardian · then one per relic (1 crown, 2–4 way-keys, 5–8 treasures)"
        )),
        ViewNode::Text(format!(
            "{GLYPH_YOU} you are here · {GLYPH_WAY_OPEN} open way · {GLYPH_WAY_SHUT} shut way · \
             a DIGIT in the guardian column is the blows that floor's guardian still owes \
             ({LIGHT_SMITE} light each to press, {LIGHT_LUNGE} to lunge) · {GLYPH_GUARDIAN_SLAIN} \
             fallen · {GLYPH_CROWN} crown · {GLYPH_KEY} way-key · {GLYPH_TREASURE} treasure"
        )),
        ViewNode::Text(deos_view::coordgrid_legend()),
    ]
}

/// **THE WAY HOME, WALKED BY THE MOVER — never priced here.**
///
/// `flee` demands the SURFACE and [`Sim::ascend`] buys one floor at a time, so a run standing below
/// ground owes the climb before it owes anything else. That is the clock the descent really plays
/// against (the Lean `Dungeon.toll`, a ratchet no verb rewinds), and it was the one number the
/// surface never showed: the guttering line said "climbing out costs 1" — the price of the exit
/// ALONE — and so told a player on floor 3 holding 4 light that they had three to spare when they
/// had none, which is exactly the position that strands a run for good.
///
/// ⚑ Every step here is [`Sim::ascend`] / [`Sim::flee`] — a verb the mover itself declared legal at
/// its own posted price — so this can never disagree with the referee and re-pricing the climb in
/// Lean re-words this sentence with it. `Ok(cost)` is the light the way home will take; `Err(floors)`
/// is the Lean `Dungeon.doomed_never_banks` case reached CONSTRUCTIVELY (the light buys `floors` of
/// climb and then dies), so the surface can say the run is over while it can still move.
fn climb_home(sim: &Sim) -> Result<u64, u64> {
    let mut climbing = sim.clone();
    let mut floors = 0;
    while climbing.depth > 0 {
        match climbing.ascend() {
            Ok(next) => {
                climbing = next;
                floors += 1;
            }
            Err(_) => return Err(floors),
        }
    }
    match climbing.flee() {
        Ok(banked) => Ok(banked.spent - sim.spent),
        Err(_) => Err(floors),
    }
}

/// The run's ONE-WORD state, with its semantic palette tag: still delving, settled and banked,
/// stranded below with the climb unpayable, or out of light altogether.
fn descent_status(sim: &Sim) -> (&'static str, &'static str) {
    if sim.fate != 0 {
        ("BANKED", "good")
    } else if sim.spent + 1 > BREATH {
        // Every verb costs at least one light, so a run that cannot pay one can never move again.
        ("THE LIGHT IS DEAD", "bad")
    } else if climb_home(sim).is_err() {
        // ⚑ ALIVE, STILL ABLE TO MOVE, AND ALREADY OVER. Lean proves a run whose light cannot pay
        // the climb can never bank from ANY continuation whatsoever (`Dungeon.doomed_never_banks`),
        // and the status word used to read DELVING right through that window — the most dramatic
        // thing the game can tell you, told by nobody.
        ("STRANDED", "bad")
    } else {
        ("DELVING", "warn")
    }
}

/// The prose mirror of the status pill. A pill is a badge layer with no plain-text form, so a chat
/// channel would otherwise learn the run's fate from nothing at all.
fn descent_standing(sim: &Sim) -> String {
    let (word, _) = descent_status(sim);
    match word {
        "BANKED" => format!(
            "{word}: the tomb is frozen. {} relic{} came out with you.",
            sim.bank(),
            if sim.bank() == 1 { "" } else { "s" }
        ),
        "THE LIGHT IS DEAD" => format!(
            "{word}: {} relic{} still in the pack never became yours.",
            sim.pack(),
            if sim.pack() == 1 { "" } else { "s" }
        ),
        "STRANDED" => format!(
            "{word}: floor {} is as high as the light reaches. {} relic{} in the pack will never \
             be banked, and no move from here changes that.",
            sim.depth,
            sim.pack(),
            if sim.pack() == 1 { "" } else { "s" }
        ),
        _ if sim.depth == 0 => {
            format!("{word}: you stand at the mouth; {FLOORS} floors lie below.")
        }
        _ => format!(
            "{word}: {} relic{} lying on this floor.",
            sim.hoard_at(sim.depth),
            if sim.hoard_at(sim.depth) == 1 {
                ""
            } else {
                "s"
            }
        ),
    }
}

/// The pressure lines — the things a player is about to lose to, said out loud. Each is derived
/// from a projection the mover already exposes, so none of them can disagree with the referee.
fn descent_pressures(sim: &Sim) -> Vec<ViewNode> {
    let mut out = Vec::new();
    if sim.fate != 0 {
        return out;
    }
    let light = BREATH.saturating_sub(sim.spent);
    // ⚑ THE CLIMB IS THE CLOCK, AND IT GOES FIRST. Below the surface the light a run may actually
    // SPEND is what is left minus the way home, and that is the number every decision down here is
    // weighed against — so it is stated every turn rather than only once the band is nearly out.
    // See [`climb_home`]: the cost is walked with the mover's own verbs, never priced here.
    if sim.depth >= 1 {
        match climb_home(sim) {
            Ok(cost) => out.push(ViewNode::Text(format!(
                "⚠ the way home costs {cost} light: {} floor{} of climb and the exit itself. {} \
                 light left to spend down here.",
                sim.depth,
                if sim.depth == 1 { "" } else { "s" },
                light.saturating_sub(cost)
            ))),
            Err(floors) => out.push(ViewNode::Text(format!(
                "⚠ STRANDED. {light} light cannot buy the way out of floor {}: it pays for {floors} \
                 floor{} of climb and then dies. Nothing in the pack will ever be banked.",
                sim.depth,
                if floors == 1 { "" } else { "s" }
            ))),
        }
    } else if light <= 4 {
        // At the mouth the way home IS the exit, so the old wording is true here and only here.
        out.push(ViewNode::Text(format!(
            "⚠ the light is guttering: {light} left, and the exit itself costs {LIGHT_FLEE}"
        )));
    }
    // The toll is THIS DAY's: the drawn map decides how much vitality this floor's guardian has,
    // so the strikes-remaining count is read off the run's own world. Quoting day 0's table here
    // priced the guardian wrong — and it is a PRICE, in the one resource the run cannot refill.
    let owed = sim.guard_hp(sim.depth).saturating_sub(sim.wounds);
    if sim.depth >= 1 && owed > 0 {
        out.push(ViewNode::Text(format!(
            "⚠ the guardian stands: the floor's hoard stays shut until it falls ({owed} more strike{}, {} light)",
            if owed == 1 { "" } else { "s" },
            owed * LIGHT_SMITE
        )));
    }
    // ⚑ THE SAME LAW THE MOVER ENFORCES, `pack + depth + harm ≤ CAP` (`Sim::loot`). `harm` was
    // omitted here too, so a run that had lunged was told nothing at all in the one state where the
    // warning matters most — it had LESS room than the meter beside it already overstated.
    if sim.pack() + 1 + sim.depth + sim.harm > CAP {
        let broken = match sim.harm {
            0 => String::new(),
            1 => " and one carry slot broken by a lunge".to_string(),
            n => format!(" and {n} carry slots broken by lunges"),
        };
        out.push(ViewNode::Text(format!(
            "⚠ carrying rights are spent: the next relic would not fit ({} carried, standing on \
             floor {}{}, against the cap of {CAP})",
            sim.pack(),
            sim.depth,
            broken
        )));
    }
    if sim.pack() > 0 {
        out.push(ViewNode::Text(format!(
            "⚠ {} relic{} ride{} in the pack: nothing is yours until a proved exit banks it",
            sim.pack(),
            if sim.pack() == 1 { "" } else { "s" },
            if sim.pack() == 1 { "s" } else { "" }
        )));
    }
    // ⚑ NEVER LET AN ABSENCE SPEAK FOR ITSELF. A live run with nothing pressing on it emitted no
    // line at all and the whole block disappeared — and a missing panel is indistinguishable from a
    // broken one. That is exactly the state a first-time reader meets: turn 0, at the mouth, with
    // everything still ahead of them. This is the only combination that reaches here (below ground
    // the climb always has a price, and a pack is always losable), so it can name itself precisely.
    if out.is_empty() {
        out.push(ViewNode::Text(
            "nothing presses on you yet: you stand at the mouth, the light is long and the pack is \
             empty. Every floor you take costs a breath to leave again."
                .to_string(),
        ));
    }
    out
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

fn hex_digest(digest: [u8; 32]) -> String {
    digest.iter().map(|byte| format!("{byte:02x}")).collect()
}

/// Render a felt-limb public digest as canonical lowercase hex.
///
/// The AIR's public roots are `[u32; 8]`; a `Debug` dump of that array reads as an
/// internals spill, and these values are painted into a browser page and a chat message.
#[cfg(any(
    feature = "private-raid-operation",
    feature = "private-preference-operation",
    feature = "private-fair-shuffle-operation",
))]
fn hex_felts(felts: [u32; 8]) -> String {
    felts
        .into_iter()
        .map(|felt| format!("{felt:08x}"))
        .collect()
}
