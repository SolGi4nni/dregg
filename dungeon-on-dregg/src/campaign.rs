//! One coherent game core for the Dungeon, the Descent, and their world — and the
//! **settlement the crew comes back to** between away missions.
//!
//! This is the game-engine seam below web/chat adapters. A [`CampaignSession`]
//! owns five real executor-backed objects: a Lean-native [`Descent`], the
//! persistent progression hero, the persistent overworld region, a persistent
//! relic reliquary, and the persistent [`chronicle`](chronicle_story) of every
//! expedition the campaign has ever run. Clients submit a closed
//! [`CampaignAction`]; prose is bound into the primary real turn as an event but
//! cannot choose effects.
//!
//! ## SUBSTRATE LAW — which half of this file is which
//!
//! The Descent's rules are **Lean-authored** (`metatheory/Dregg2/Games/Dungeon.lean`,
//! re-emitted to `program/dungeon_program.json`). Nothing in this module authors,
//! edits, or softens a constraint the executor admits an expedition move under; the
//! only thing it does to an expedition is pick which of the sixteen Lean-checked maps
//! to deploy and then hand the mover's projections to the Lean-loaded referee.
//!
//! Everything else here — the run boundary, the chronicle, the reliquary, the XP
//! schedule, the settlement/expedition phase — lives strictly **above the turn**, keyed
//! off a COMPLETED expedition's committed state, and is legitimately Rust.
//!
//! ## The two phases (this is the loop)
//!
//! A campaign alternates between [`Phase::Expedition`] and [`Phase::Settlement`]:
//!
//! * **Expedition** — only [`CampaignAction::Descent`] moves are open. The burning
//!   clock and the carry ceiling are the Lean rules; the campaign layer adds nothing.
//! * **Settlement** — reached by [`CampaignAction::Return`] once the expedition is over
//!   (banked, or the light dead). Return SEALS the run: it writes the chronicle, mints
//!   every banked relic into the reliquary, clears the location on a first crown, and
//!   pays the XP. Travel, level-ups, relic vows, and the next
//!   [`CampaignAction::Embark`] are settlement business.
//!
//! You cannot cash in without coming home, and you cannot walk to the next place with an
//! expedition still underway.
//!
//! ## WHAT PERSISTS, AND WHAT RESETS
//!
//! **Resets, every single time, and the campaign layer has no API to do otherwise.**
//! [`CampaignAction::Embark`] deploys a *fresh* [`Descent`] through
//! [`Descent::deploy_on_day`], whose genesis is the Lean `genesisState` committed under
//! the Lean `genesis` case. Depth, breath, wounds, ways and custody all return to the
//! minted world. [`crate::descent::BREATH`] (26 light) and [`crate::descent::CAP`] (the
//! `pack + depth <= CAP` carry ceiling) are Lean constants; no amount of persistence
//! moves them. **Run ten is exactly as hard as run one.**
//!
//! And the map itself resets — to a *different* one. Expedition `n` at location `l`
//! draws its day-seed from `(campaign seed, player, l, n)`, so consecutive runs at one
//! place are different members of the [`crate::descent::DAYS`]-strong drawn family, each
//! Lean-checked legal and Lean-driven completable. A memorised line does not survive the
//! walk home; the grammar you learned does.
//!
//! **Persists:** the cleared roads (region cell, WriteOnce), the reliquary's eight relic
//! slots, the hero's XP/level/class, and the chronicle's per-location `runs` / `deepest`
//! / `crowns` marks. None of it touches what the executor admits. What it buys is
//! *reasons and options*: a collection with holes in it, a map that opens, and a
//! settlement that can tell you where tomorrow's treasure is minted.
//!
//! ## XP IS PAID FOR NEW FACTS, NEVER FOR REPETITION
//!
//! [`CROWN_XP`] for the **first** crown at a location (a re-crown of a cleared place pays
//! nothing), [`RELIC_XP`] per relic that enters the reliquary for the first time,
//! [`DEPTH_XP`] per floor of a **new** deepest reach. Grinding the same run pays zero.
//! The campaign's whole XP supply is therefore finite and computable
//! ([`max_campaign_xp`]) — the ceiling is reachable only by a player who crowned every
//! location, bottomed out every location, and brought all eight relics home.
//!
//! ## The durable object
//!
//! [`CampaignRecord`] stores typed inputs and exact receipts, not trusted summary
//! counters. [`CampaignSession::resume`] deploys fresh deterministic objects and
//! re-executes every input, comparing the full receipt bytes, derived projection, and
//! hash-chain head. A copied, reordered, or substituted event therefore cannot mint XP,
//! an overworld clear, a chronicle mark, or a relic binding.
//!
//! ## Honest scope on the chronicle's binding
//!
//! The chronicle cell's own teeth are real and load-bearing: a mark can never fall
//! ([`StateConstraint::Monotonic`] under a `SlotChanged` guard), one seal advances
//! `runs` by exactly one ([`StateConstraint::FieldDelta`]), `crowns <= runs` is an
//! [`StateConstraint::AffineLe`], a seal at one location cannot move another location's
//! marks ([`StateConstraint::Immutable`]), and an unsanctioned method is a default-deny
//! refusal. What those teeth do NOT do is read the descent cell — the two live on
//! separate executor ledgers, the same ceiling [`crate::overworld`] names for its
//! `clear` gate. The binding to the actual run is (a) the seal turn's event, which
//! commits to [`ExpeditionOutcome::commitment`] — a hash over the descent cell's
//! COMMITTED registers and relic custody, read from the executor, never from the Rust
//! mover — and (b) replay: `resume` re-runs the expedition, so a chronicle mark that
//! was not earned diverges. [`verify_expedition_seal`] is the standalone check.

use std::collections::BTreeMap;
use std::sync::Arc;

use dregg_app_framework::{
    CellProgram, Effect, Event, FieldElement, StateConstraint, TransitionCase, TransitionGuard,
    TurnReceipt, field_from_u64, symbol,
};
use procgen_dregg::CommittedSeed;
use serde::{Deserialize, Serialize};
use spween_dregg::{CompiledStory, WorldCell, WorldError};

use crate::descent::{
    BANKED, BREATH, CAP, CARRIED, DELVE, DayWorld, Descent, FLEE, FLOORS, LOOT, REGISTERS, RELICS,
    SMITE, Sim, UNLOCK, crowned_line, day_world,
};
use crate::meta;
use crate::overworld::{RegionCell, RegionMap, deepening_ways};
use crate::progression;

/// Event topic used by every campaign action's primary real turn.
pub const CAMPAIGN_NARRATION_TOPIC: &str = "dungeon-on-dregg/campaign-narration-v1";
/// XP awarded by the **first** crown at a location. A crowned run at a place already
/// cleared pays nothing — see the module header's "new facts, never repetition" rule.
pub const CROWN_XP: u64 = 100;
/// XP awarded per relic entering the reliquary for the first time. The reliquary has one
/// slot per relic id campaign-wide, so this is paid at most [`RELICS`] times ever.
pub const RELIC_XP: u64 = 25;
/// XP awarded per floor of a NEW deepest reach at a location.
pub const DEPTH_XP: u64 = 10;
/// A bounded durable journal. An expedition is roughly twenty moves plus its `Return`
/// and the next `Embark`, so this holds something like forty complete expeditions.
pub const MAX_CAMPAIGN_EVENTS: usize = 1024;
/// Narration is flavor carried by receipts, not an unbounded storage channel.
pub const MAX_NARRATION_BYTES: usize = 8 * 1024;
/// The chronicle spends three of the cell's sixteen register slots per location, so a
/// chronicled region holds at most five places. [`deepening_ways`] has four.
pub const MAX_CHRONICLED_LOCATIONS: usize = 5;

const CAMPAIGN_ROOT_DOMAIN: &str = "dungeon-on-dregg/campaign-root-v1";
const RELIC_GRANT_DOMAIN: &str = "dungeon-on-dregg/relic-grant-v1";
const RELIC_BINDING_DOMAIN: &str = "dungeon-on-dregg/relic-binding-v1";
const LOCATION_SEED_DOMAIN: &str = "dungeon-on-dregg/location-seed-v1";
const EXPEDITION_SEED_DOMAIN: &str = "dungeon-on-dregg/expedition-seed-v1";
const EXPEDITION_DOMAIN: &str = "dungeon-on-dregg/expedition-outcome-v1";
const EMBARK_DOMAIN: &str = "dungeon-on-dregg/expedition-embark-v1";
const RELIQUARY_SCENE: &str = "dungeon-on-dregg/reliquary/v1";
const RELIQUARY_MINT: &str = "reliquary/mint";
const RELIQUARY_RAID: &str = "reliquary/vow/raid";
const RELIQUARY_BAZAAR: &str = "reliquary/vow/bazaar";
const RELIC_BANKED: u64 = 1;
const RELIC_RAID_BOUND: u64 = 2;
const RELIC_BAZAAR_BOUND: u64 = 3;
const CHRONICLE_SCENE: &str = "dungeon-on-dregg/chronicle/v1";
const CHRONICLE_SEAL: &str = "chronicle/seal";
const CHRONICLE_EMBARK: &str = "chronicle/embark";
/// `runs`, `deepest`, `crowns` — the three marks the chronicle keeps per location.
const CHRONICLE_MARKS: usize = 3;

/// Deterministic campaign identity and character genesis.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CampaignConfig {
    pub seed: u8,
    pub player: String,
    pub class_id: u64,
}

impl CampaignConfig {
    pub fn new(seed: u8, player: impl Into<String>, class_id: u64) -> Self {
        Self {
            seed,
            player: player.into(),
            class_id,
        }
    }
}

/// The closed command vocabulary for one Lean-native Descent expedition.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum DescentAction {
    Delve,
    Unlock { way: u64 },
    Smite,
    Loot { relic: u8 },
    Flee,
}

/// A one-time purpose for a banked relic. The external context is committed in
/// the executor receipt, so a grant for one raid/order cannot be relabeled.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum RelicUse {
    RaidSeat { session: [u8; 32], seat: u8 },
    BazaarOrder { market: [u8; 32], order: [u8; 32] },
}

/// Every player input accepted by the coherent engine.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum CampaignAction {
    /// One move of the live expedition. Open only in [`Phase::Expedition`].
    Descent(DescentAction),
    /// **Come home.** Seal the finished expedition: write the chronicle, mint every
    /// banked relic, clear the location on a first crown, pay the XP. Open only when the
    /// expedition is genuinely over (`fate != 0`, or the light is spent).
    Return,
    /// **Go out again.** Deploy a fresh Lean-native expedition at the current location on
    /// a freshly drawn map. Open only in [`Phase::Settlement`].
    Embark,
    /// Walk a cleared road. Settlement business.
    Travel { destination: String },
    /// Spend earned XP on the next level. Settlement business.
    LevelUp,
    /// Bind a banked relic to exactly one outside purpose. Settlement business.
    BindRelic { relic: u8, use_: RelicUse },
}

/// Which half of the loop the campaign stands in. Derived, not asserted: the campaign is
/// in [`Phase::Settlement`] exactly when the chronicle has already sealed as many
/// expeditions as the held [`Descent`]'s ordinal.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Phase {
    /// An expedition is deployed and unsealed; only descent moves are open.
    Expedition,
    /// The last expedition is sealed and the traveller stands in the settlement.
    Settlement,
}

/// Persistent state of one relic after it has left an expedition.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum RelicState {
    Unbanked,
    Banked,
    RaidBound,
    BazaarBound,
}

impl RelicState {
    fn from_u64(value: u64) -> Result<Self, CampaignError> {
        match value {
            0 => Ok(Self::Unbanked),
            RELIC_BANKED => Ok(Self::Banked),
            RELIC_RAID_BOUND => Ok(Self::RaidBound),
            RELIC_BAZAAR_BOUND => Ok(Self::BazaarBound),
            other => Err(CampaignError::Corrupt(format!(
                "reliquary contains unknown state {other}"
            ))),
        }
    }
}

/// **What one expedition actually was**, read off the descent CELL's committed state
/// (`Descent::read_reg` / `read_relic`), never off the Rust mover. This is the object the
/// chronicle seal commits to and the tombstone the settlement shows you.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExpeditionOutcome {
    /// Where it was run.
    pub location: String,
    /// Which expedition of the whole campaign this was (1-based).
    pub ordinal: u64,
    /// Which of the [`crate::descent::DAYS`] drawn maps it was played on.
    pub day: usize,
    /// The floor standing at the end.
    pub depth: u64,
    /// Light burned, of [`BREATH`].
    pub spent: u64,
    /// Wounds on the standing guardian at the end.
    pub wounds: u64,
    /// The Lean `fate` register: non-zero once the pack has been banked.
    pub fate: u64,
    /// Committed per-relic custody at the end. `BANKED` came home; `CARRIED` was in the
    /// pack when the light died and is gone.
    pub custody: [u64; RELICS],
    /// A hash over the location, ordinal, day, and every committed descent register and
    /// relic custody key — the value the chronicle seal turn emits.
    pub commitment: [u8; 32],
}

impl ExpeditionOutcome {
    /// Did the prize (relic 0) come home?
    pub fn crowned(&self) -> bool {
        self.custody[0] == BANKED
    }
    /// The relic slots that came home.
    pub fn banked(&self) -> Vec<usize> {
        (0..RELICS).filter(|&r| self.custody[r] == BANKED).collect()
    }
    /// The relic slots that were in the pack when the light died. These never bank; the
    /// chronicle is the only place they are remembered.
    pub fn lost(&self) -> Vec<usize> {
        (0..RELICS)
            .filter(|&r| self.custody[r] == CARRIED)
            .collect()
    }
    /// The run ended because the light ran out, not because the traveller banked.
    pub fn light_died(&self) -> bool {
        self.fate == 0 && self.spent >= BREATH
    }
    /// The expedition is finished: banked, or out of light. The precondition of
    /// [`CampaignAction::Return`].
    pub fn over(&self) -> bool {
        self.fate != 0 || self.spent >= BREATH
    }
}

/// The chronicle's three persistent marks for one place, plus whether its road is open.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LocationRecord {
    pub id: String,
    pub name: String,
    /// The region cell's WriteOnce cleared flag — the road out of here.
    pub cleared: bool,
    /// Expeditions sealed here. Never falls (`Monotonic`).
    pub runs: u64,
    /// Deepest floor ever stood on here. Never falls.
    pub deepest: u64,
    /// Crowned expeditions here. Never falls, and `crowns <= runs` is an executor tooth.
    pub crowns: u64,
}

/// The complete frontend-neutral view derived from the five real objects.
///
/// The `descent_*` fields describe the **held** expedition: the live one in
/// [`Phase::Expedition`], or the one that just ended in [`Phase::Settlement`]. Its place
/// is [`Self::expedition_location`], which is not the same as [`Self::location`] after a
/// travel.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CampaignProjection {
    pub phase: Phase,
    pub location: String,
    pub cleared_locations: Vec<String>,
    pub hero_xp: u64,
    pub hero_level: u64,
    pub hero_class: u64,
    /// The ordinal of the held expedition (1-based over the whole campaign).
    pub expedition_ordinal: u64,
    /// Where the held expedition is/was run.
    pub expedition_location: String,
    /// Which drawn map the held expedition is/was played on.
    pub expedition_day: usize,
    pub descent_depth: u64,
    pub descent_spent: u64,
    pub descent_wounds: u64,
    pub descent_terminal: bool,
    pub expedition_custody: [u64; RELICS],
    pub relics: [RelicState; RELICS],
    /// The chronicle, in map order.
    pub records: Vec<LocationRecord>,
}

/// Portable consequence of a one-time relic vow. It is accepted by another
/// subsystem only together with a campaign record that replays to this event.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RelicGrant {
    pub id: [u8; 32],
    pub player: String,
    pub relic: u8,
    pub use_: RelicUse,
    pub campaign_revision: u64,
    pub previous_campaign_root: [u8; 32],
    pub reliquary_receipt_hash: [u8; 32],
}

/// One narrated operation and every real receipt it caused. `receipts[0]` is
/// the primary action receipt carrying [`CAMPAIGN_NARRATION_TOPIC`]; later
/// receipts are deterministic consequences such as XP, clear, or relic mints.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CampaignEvent {
    pub revision: u64,
    pub action: CampaignAction,
    pub narration: String,
    pub narration_commitment: [u8; 32],
    pub receipts: Vec<TurnReceipt>,
    pub projection: CampaignProjection,
    pub grant: Option<RelicGrant>,
    pub root: [u8; 32],
}

impl CampaignEvent {
    pub fn receipt_hashes(&self) -> Vec<[u8; 32]> {
        self.receipts
            .iter()
            .map(TurnReceipt::receipt_hash)
            .collect()
    }
}

/// Serializable restart material. Every field is checked against fresh replay.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CampaignRecord {
    pub config: CampaignConfig,
    pub events: Vec<CampaignEvent>,
    pub root: [u8; 32],
    pub projection: CampaignProjection,
}

impl CampaignRecord {
    pub fn to_json(&self) -> Result<Vec<u8>, CampaignError> {
        serde_json::to_vec(self)
            .map_err(|error| CampaignError::Corrupt(format!("record encode failed: {error}")))
    }

    pub fn from_json(bytes: &[u8]) -> Result<Self, CampaignError> {
        serde_json::from_slice(bytes)
            .map_err(|error| CampaignError::Corrupt(format!("record decode failed: {error}")))
    }
}

/// Live coherent game state. All summary state is derived from the executor
/// objects; the journal is only the durable/replayable command history.
pub struct CampaignSession {
    config: CampaignConfig,
    hero: WorldCell,
    region: RegionCell,
    descent: Descent,
    reliquary: WorldCell,
    chronicle: WorldCell,
    /// The ordinal of the HELD expedition. Deterministic under replay: it starts at 1 and
    /// advances only on a landed [`CampaignAction::Embark`].
    expedition_ordinal: u64,
    /// Where the HELD expedition was deployed — not necessarily where the traveller now
    /// stands, since a settlement travel does not touch the expedition.
    expedition_location: String,
    events: Vec<CampaignEvent>,
    root: [u8; 32],
}

impl CampaignSession {
    pub fn open(config: CampaignConfig) -> Result<Self, CampaignError> {
        validate_config(&config)?;
        let map = deepening_ways();
        if map.locations.len() > MAX_CHRONICLED_LOCATIONS {
            return Err(CampaignError::Refused(format!(
                "a chronicled region holds at most {MAX_CHRONICLED_LOCATIONS} locations"
            )));
        }
        let hero = meta::deploy_meta_hero(derive_seed(config.seed, "hero"));
        let class_receipt =
            progression::choose_class(&hero, config.class_id).map_err(CampaignError::world)?;
        let level_receipt = progression::level_up(&hero).map_err(CampaignError::world)?;
        let region = RegionCell::deploy(&map, derive_seed(config.seed, "region"));
        // Expedition one is drawn exactly like every later one: from the campaign's own
        // seed, the player, the place, and the ordinal. No compile-time map is pinned.
        let day_seed = expedition_day_seed(&config, &map.start, 1);
        let descent = Descent::deploy_on_day(expedition_cell_seed(&day_seed), day_seed)
            .map_err(CampaignError::world)?;
        let reliquary = WorldCell::deploy_compiled(
            Arc::new(reliquary_story()),
            derive_seed(config.seed, "reliquary"),
        )
        .map_err(CampaignError::world)?;
        let chronicle = WorldCell::deploy_compiled(
            Arc::new(chronicle_story(&map)),
            derive_seed(config.seed, "chronicle"),
        )
        .map_err(CampaignError::world)?;

        let expedition_location = map.start.clone();
        let mut session = Self {
            config,
            hero,
            region,
            descent,
            reliquary,
            chronicle,
            expedition_ordinal: 1,
            expedition_location,
            events: Vec::new(),
            root: [0; 32],
        };
        let projection = session.projection()?;
        session.root = genesis_root(
            &session.config,
            &[class_receipt, level_receipt],
            &projection,
        )?;
        Ok(session)
    }

    pub fn config(&self) -> &CampaignConfig {
        &self.config
    }

    pub fn revision(&self) -> u64 {
        u64::try_from(self.events.len()).expect("the bounded journal fits u64")
    }

    pub fn root(&self) -> [u8; 32] {
        self.root
    }

    pub fn events(&self) -> &[CampaignEvent] {
        &self.events
    }

    pub fn descent(&self) -> &Descent {
        &self.descent
    }

    /// Expeditions sealed into the chronicle across the whole region. Read from committed
    /// cell state, so it cannot drift from the marks the teeth guard.
    pub fn sealed_expeditions(&self) -> u64 {
        (0..self.region.map().locations.len())
            .map(|index| self.chronicle.read_var(&runs_var(index)))
            .sum()
    }

    /// Which half of the loop the campaign stands in — derived, never asserted: the held
    /// expedition is sealed exactly when the chronicle has caught up to its ordinal.
    pub fn phase(&self) -> Phase {
        if self.sealed_expeditions() >= self.expedition_ordinal {
            Phase::Settlement
        } else {
            Phase::Expedition
        }
    }

    /// The held expedition as the descent CELL has committed it. Every field is read back
    /// out of the executor, so the settlement can never be paid off a mover the referee
    /// did not admit.
    pub fn expedition(&self) -> ExpeditionOutcome {
        let mut custody = [0u64; RELICS];
        for (slot, value) in custody.iter_mut().enumerate() {
            *value = self.descent.read_relic(slot);
        }
        let mut outcome = ExpeditionOutcome {
            location: self.expedition_location.clone(),
            ordinal: self.expedition_ordinal,
            day: self.descent.day(),
            depth: self.descent.read_reg("depth"),
            spent: self.descent.read_reg("spent"),
            wounds: self.descent.read_reg("wounds"),
            fate: self.descent.read_reg("fate"),
            custody,
            commitment: [0; 32],
        };
        outcome.commitment = expedition_commitment(&outcome, &self.descent);
        outcome
    }

    /// The chronicle + region marks for every place, in map order.
    pub fn records(&self) -> Vec<LocationRecord> {
        self.region
            .map()
            .locations
            .iter()
            .enumerate()
            .map(|(index, location)| LocationRecord {
                id: location.id.clone(),
                name: location.name.clone(),
                cleared: self.region.is_cleared(&location.id),
                runs: self.chronicle.read_var(&runs_var(index)),
                deepest: self.chronicle.read_var(&deepest_var(index)),
                crowns: self.chronicle.read_var(&crowns_var(index)),
            })
            .collect()
    }

    pub fn projection(&self) -> Result<CampaignProjection, CampaignError> {
        let map = self.region.map();
        let mut cleared_locations = map
            .locations
            .iter()
            .filter(|location| self.region.is_cleared(&location.id))
            .map(|location| location.id.clone())
            .collect::<Vec<_>>();
        cleared_locations.sort();
        let mut relics = [RelicState::Unbanked; RELICS];
        for (index, state) in relics.iter_mut().enumerate() {
            *state = RelicState::from_u64(self.reliquary.read_var(&relic_var(index)))?;
        }
        let sim = self.descent.sim();
        Ok(CampaignProjection {
            phase: self.phase(),
            location: self.region.current_location(),
            cleared_locations,
            hero_xp: self.hero.read_var("xp"),
            hero_level: self.hero.read_var("level"),
            hero_class: self.hero.read_var("class"),
            expedition_ordinal: self.expedition_ordinal,
            expedition_location: self.expedition_location.clone(),
            expedition_day: self.descent.day(),
            descent_depth: sim.depth,
            descent_spent: sim.spent,
            descent_wounds: sim.wounds,
            descent_terminal: sim.fate != 0,
            expedition_custody: sim.custody,
            relics,
            records: self.records(),
        })
    }

    pub fn export_record(&self) -> Result<CampaignRecord, CampaignError> {
        Ok(CampaignRecord {
            config: self.config.clone(),
            events: self.events.clone(),
            root: self.root,
            projection: self.projection()?,
        })
    }

    /// Submit one typed action. Every refusal is anti-ghost: no event/root is
    /// appended. The underlying executor may record its own rejected nonce, but
    /// no player progress can be derived from a refusal.
    pub fn advance(
        &mut self,
        action: CampaignAction,
        narration: impl Into<String>,
    ) -> Result<CampaignEvent, CampaignError> {
        if self.events.len() >= MAX_CAMPAIGN_EVENTS {
            return Err(CampaignError::Refused(
                "campaign journal is full".to_string(),
            ));
        }
        let narration = narration.into();
        validate_narration(&narration)?;
        let narration_commitment = narration_hash(&narration);
        let event = Event::new(symbol(CAMPAIGN_NARRATION_TOPIC), vec![narration_commitment]);
        let previous_root = self.root;
        let mut receipts = Vec::new();
        let mut grant = None;

        match &action {
            CampaignAction::Descent(command) => {
                self.require_phase(Phase::Expedition, "an expedition move")?;
                let (method, next) = descent_projection(self.descent.sim(), *command);
                let primary = self
                    .descent
                    .commit_projected_with_event(method, next, event)
                    .map_err(CampaignError::world)?;
                receipts.push(primary);
            }
            CampaignAction::Return => {
                self.require_phase(Phase::Expedition, "coming home")?;
                let outcome = self.expedition();
                if !outcome.over() {
                    return Err(CampaignError::Refused(format!(
                        "the expedition is still underway on floor {} with {} of {BREATH} light \
                         burned — flee to bank the pack, or spend the rest of it",
                        outcome.depth, outcome.spent
                    )));
                }
                receipts.extend(self.settle(&outcome, narration_commitment)?);
            }
            CampaignAction::Embark => {
                self.require_phase(Phase::Settlement, "a fresh expedition")?;
                let here = self.region.current_location();
                let ordinal = self.sealed_expeditions() + 1;
                let day_seed = expedition_day_seed(&self.config, &here, ordinal);
                let day = crate::descent::day_index(&day_seed);
                // Witness the draw BEFORE the run: the embark turn commits the place, the
                // ordinal, the day-seed and the drawn map to the ledger, so nobody can
                // afterwards claim a different dungeon was descended. It is barred from
                // moving any chronicle mark (`Immutable` on all of them).
                receipts.push(self.witness_embark(
                    &here,
                    ordinal,
                    &day_seed,
                    day,
                    narration_commitment,
                )?);
                self.descent = Descent::deploy_on_day(expedition_cell_seed(&day_seed), day_seed)
                    .map_err(CampaignError::world)?;
                self.expedition_ordinal = ordinal;
                self.expedition_location = here;
            }
            CampaignAction::Travel { destination } => {
                self.require_phase(Phase::Settlement, "travel")?;
                let here = self.region.current_location();
                if !self.region.is_cleared(&here) {
                    return Err(CampaignError::Refused(
                        "the current location has no crowned settlement".to_string(),
                    ));
                }
                if !self
                    .region
                    .map()
                    .edges_from(&here)
                    .iter()
                    .any(|edge| edge.to == *destination)
                {
                    return Err(CampaignError::Refused(format!(
                        "no road leads from `{here}` to `{destination}`"
                    )));
                }
                receipts.push(
                    self.region
                        .travel_with_event(destination, event)
                        .map_err(CampaignError::Refused)?,
                );
            }
            CampaignAction::LevelUp => {
                self.require_phase(Phase::Settlement, "a level-up")?;
                let target = self.hero.read_var("level") + 1;
                let xp = self.hero.read_var("xp");
                let threshold = progression::xp_threshold(target);
                if target > progression::MAX_LEVEL || xp < threshold {
                    return Err(CampaignError::Refused(format!(
                        "level {target} requires {threshold} XP; the hero has {xp}"
                    )));
                }
                let cell = self.hero.cell_id();
                receipts.push(
                    self.hero
                        .apply_raw(
                            &progression::level_up_method(target),
                            vec![
                                Effect::SetField {
                                    cell,
                                    index: progression::LEVEL_SLOT as u64,
                                    value: field_from_u64(target),
                                },
                                Effect::EmitEvent { cell, event },
                            ],
                        )
                        .map_err(CampaignError::world)?,
                );
            }
            CampaignAction::BindRelic { relic, use_ } => {
                self.require_phase(Phase::Settlement, "a relic vow")?;
                let index = usize::from(*relic);
                if index >= RELICS {
                    return Err(CampaignError::Refused(format!(
                        "relic {relic} is outside the persistent reliquary"
                    )));
                }
                let state = self.reliquary.read_var(&relic_var(index));
                if state != RELIC_BANKED {
                    return Err(CampaignError::Refused(format!(
                        "relic {relic} is not an unbound banked relic"
                    )));
                }
                let binding = relic_binding_hash(use_);
                let receipt = self.bind_relic(index, use_, narration_commitment, binding)?;
                let receipt_hash = receipt.receipt_hash();
                receipts.push(receipt);
                let revision = self.revision() + 1;
                grant = Some(RelicGrant {
                    id: relic_grant_id(
                        previous_root,
                        revision,
                        &self.config.player,
                        *relic,
                        use_,
                        receipt_hash,
                    ),
                    player: self.config.player.clone(),
                    relic: *relic,
                    use_: use_.clone(),
                    campaign_revision: revision,
                    previous_campaign_root: previous_root,
                    reliquary_receipt_hash: receipt_hash,
                });
            }
        }

        let projection = self.projection()?;
        let revision = self.revision() + 1;
        let root = event_root(
            previous_root,
            revision,
            &action,
            &narration,
            narration_commitment,
            &receipts,
            &projection,
            grant.as_ref(),
        )?;
        let event = CampaignEvent {
            revision,
            action,
            narration,
            narration_commitment,
            receipts,
            projection,
            grant,
            root,
        };
        self.root = root;
        self.events.push(event.clone());
        Ok(event)
    }

    /// Freshly re-execute every action and require exact event equality.
    pub fn resume(record: &CampaignRecord) -> Result<Self, CampaignError> {
        if record.events.len() > MAX_CAMPAIGN_EVENTS {
            return Err(CampaignError::Corrupt(
                "campaign record is overlong".to_string(),
            ));
        }
        let mut replayed = Self::open(record.config.clone())?;
        for (index, expected) in record.events.iter().enumerate() {
            let revision = u64::try_from(index + 1).expect("the bounded journal fits u64");
            if expected.revision != revision {
                return Err(CampaignError::Corrupt(format!(
                    "event {revision} has a non-canonical revision"
                )));
            }
            let actual = replayed
                .advance(expected.action.clone(), expected.narration.clone())
                .map_err(|error| {
                    CampaignError::Corrupt(format!("event {revision} refused on replay: {error}"))
                })?;
            if !same_event(&actual, expected)? {
                return Err(CampaignError::Corrupt(format!(
                    "event {revision} differs from fresh replay"
                )));
            }
        }
        if replayed.root != record.root || replayed.projection()? != record.projection {
            return Err(CampaignError::Corrupt(
                "record summary does not name the replayed head".to_string(),
            ));
        }
        Ok(replayed)
    }

    pub fn verify(record: &CampaignRecord) -> Result<(), CampaignError> {
        Self::resume(record).map(|_| ())
    }

    fn require_phase(&self, wanted: Phase, what: &str) -> Result<(), CampaignError> {
        let phase = self.phase();
        if phase == wanted {
            return Ok(());
        }
        Err(CampaignError::Refused(match wanted {
            Phase::Expedition => format!(
                "{what} needs an expedition underway; the traveller is in the settlement \
                 at `{}` — embark first",
                self.region.current_location()
            ),
            Phase::Settlement => format!(
                "{what} is settlement business; expedition {} is still deployed at `{}`",
                self.expedition_ordinal, self.expedition_location
            ),
        }))
    }

    /// **Seal one finished expedition.** Everything here is computed from `outcome`, which
    /// is read off the descent cell's COMMITTED state, and every consequence is a real
    /// turn. The order is fixed so a replay reproduces the receipt forest exactly:
    /// chronicle seal, first-crown clear, relic mints in slot order, then one XP turn.
    fn settle(
        &mut self,
        outcome: &ExpeditionOutcome,
        narration: [u8; 32],
    ) -> Result<Vec<TurnReceipt>, CampaignError> {
        let index = self
            .region
            .map()
            .index_of(&outcome.location)
            .ok_or_else(|| {
                CampaignError::Corrupt(format!(
                    "expedition location `{}` left the region map",
                    outcome.location
                ))
            })?;
        let previous_deepest = self.chronicle.read_var(&deepest_var(index));
        let first_crown = outcome.crowned() && !self.region.is_cleared(&outcome.location);

        let mut receipts = vec![self.seal_expedition(index, outcome, narration)?];

        // The road opens only on the FIRST crown of a place. A later crown here is a
        // perfectly good run; it just does not re-open an already-open road, and it does
        // not re-pay the crown.
        if first_crown {
            receipts.push(
                self.region
                    .clear(&outcome.location)
                    .map_err(CampaignError::Refused)?,
            );
        }

        // EVERY banked relic enters the reliquary, not only a crowned run's. This is the
        // whole reason a treasure run is worth walking: relics 4..7 are minted where the
        // crowned line cannot afford to stop for them, so the collection is filled by
        // expeditions that deliberately give up the Crown.
        let mut minted = 0u64;
        for relic in outcome.banked() {
            if self.reliquary.read_var(&relic_var(relic)) == 0 {
                receipts.push(self.mint_relic(relic)?);
                minted += 1;
            }
        }

        let depth_gain = outcome.depth.saturating_sub(previous_deepest);
        let xp = u64::from(first_crown) * CROWN_XP + minted * RELIC_XP + depth_gain * DEPTH_XP;
        if xp > 0 {
            receipts.push(progression::gain_xp(&self.hero, xp).map_err(CampaignError::world)?);
        }
        Ok(receipts)
    }

    /// The chronicle seal — one real turn advancing exactly this location's three marks.
    fn seal_expedition(
        &self,
        index: usize,
        outcome: &ExpeditionOutcome,
        narration: [u8; 32],
    ) -> Result<TurnReceipt, CampaignError> {
        let cell = self.chronicle.cell_id();
        let runs = self.chronicle.read_var(&runs_var(index));
        let deepest = self.chronicle.read_var(&deepest_var(index));
        let crowns = self.chronicle.read_var(&crowns_var(index));
        self.chronicle
            .apply_raw(
                &chronicle_method(CHRONICLE_SEAL, index),
                vec![
                    Effect::SetField {
                        cell,
                        index: runs_slot(index) as u64,
                        value: field_from_u64(runs + 1),
                    },
                    Effect::SetField {
                        cell,
                        index: deepest_slot(index) as u64,
                        value: field_from_u64(deepest.max(outcome.depth)),
                    },
                    Effect::SetField {
                        cell,
                        index: crowns_slot(index) as u64,
                        value: field_from_u64(crowns + u64::from(outcome.crowned())),
                    },
                    Effect::EmitEvent {
                        cell,
                        event: Event::new(
                            symbol(CAMPAIGN_NARRATION_TOPIC),
                            vec![narration, outcome.commitment],
                        ),
                    },
                ],
            )
            .map_err(CampaignError::world)
    }

    /// The embark witness — a real turn that commits the draw and moves no mark.
    fn witness_embark(
        &self,
        location: &str,
        ordinal: u64,
        day_seed: &CommittedSeed,
        day: usize,
        narration: [u8; 32],
    ) -> Result<TurnReceipt, CampaignError> {
        let index = self.region.map().index_of(location).ok_or_else(|| {
            CampaignError::Corrupt(format!("`{location}` is not a place in this region"))
        })?;
        let cell = self.chronicle.cell_id();
        self.chronicle
            .apply_raw(
                &chronicle_method(CHRONICLE_EMBARK, index),
                vec![Effect::EmitEvent {
                    cell,
                    event: Event::new(
                        symbol(CAMPAIGN_NARRATION_TOPIC),
                        vec![
                            narration,
                            embark_commitment(location, ordinal, day_seed, day),
                        ],
                    ),
                }],
            )
            .map_err(CampaignError::world)
    }

    fn mint_relic(&self, relic: usize) -> Result<TurnReceipt, CampaignError> {
        let cell = self.reliquary.cell_id();
        self.reliquary
            .apply_raw(
                &relic_method(RELIQUARY_MINT, relic),
                vec![Effect::SetField {
                    cell,
                    index: relic as u64,
                    value: field_from_u64(RELIC_BANKED),
                }],
            )
            .map_err(CampaignError::world)
    }

    fn bind_relic(
        &self,
        relic: usize,
        use_: &RelicUse,
        narration: [u8; 32],
        binding: [u8; 32],
    ) -> Result<TurnReceipt, CampaignError> {
        let (method, state) = match use_ {
            RelicUse::RaidSeat { seat, .. } => {
                if usize::from(*seat) >= 4 {
                    return Err(CampaignError::Refused(format!(
                        "raid seat {seat} is outside the four-seat party"
                    )));
                }
                (RELIQUARY_RAID, RELIC_RAID_BOUND)
            }
            RelicUse::BazaarOrder { market, order } => {
                if *market == [0; 32] || *order == [0; 32] {
                    return Err(CampaignError::Refused(
                        "Bazaar vow requires nonzero market and order identities".to_string(),
                    ));
                }
                (RELIQUARY_BAZAAR, RELIC_BAZAAR_BOUND)
            }
        };
        let cell = self.reliquary.cell_id();
        self.reliquary
            .apply_raw(
                &relic_method(method, relic),
                vec![
                    Effect::SetField {
                        cell,
                        index: relic as u64,
                        value: field_from_u64(state),
                    },
                    Effect::EmitEvent {
                        cell,
                        event: Event::new(
                            symbol(CAMPAIGN_NARRATION_TOPIC),
                            vec![narration, binding],
                        ),
                    },
                ],
            )
            .map_err(CampaignError::world)
    }
}

// ── The settlement board — persistent state a player can actually SEE ────────────

/// One road out of the current place, and whether it is walkable yet.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RoadStanding {
    pub to: String,
    pub name: String,
    pub open: bool,
    /// The location whose crown unbars this road, when it is still barred.
    pub needs: Option<String>,
}

/// **Where today's dungeon keeps its things.** Fully determined by the campaign config
/// and the expedition ordinal, so the settlement can show you the NEXT map before you
/// commit to it. This is planning material, not an advantage: the map was always drawn
/// deterministically, and knowing where a treasure is minted is exactly what makes the
/// Crown-or-treasure choice a decision instead of a surprise.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MapBriefing {
    /// Which of the [`crate::descent::DAYS`] Lean-checked maps.
    pub day: usize,
    /// The floor each relic is minted on (the Lean `World.homes`).
    pub homes: [u64; RELICS],
    /// Guardian vitality per floor, index 0 the surface (the Lean `World.ghp`).
    pub guardians: Vec<u64>,
    /// What the day's perfect crowned line costs, of [`BREATH`]. Every drawn map is
    /// Lean-proven to cost 20–26, so this is the tension made legible.
    pub perfect_line_cost: u64,
}

impl MapBriefing {
    fn of(day: usize) -> Self {
        let world: DayWorld = day_world(day);
        let mut sim = Sim::genesis_on_day(day);
        for (verb, argument) in crowned_line(day) {
            let next = match verb {
                DELVE => sim.delve(),
                SMITE => sim.smite(),
                LOOT => sim.loot(argument as usize),
                UNLOCK => sim.unlock(argument as u64),
                FLEE => sim.flee(),
                other => panic!("the day's crowned line emitted unknown verb `{other}`"),
            };
            sim = next.expect("every drawn map's crowned line replays (Dungeon.winsAt_true)");
        }
        MapBriefing {
            day,
            homes: world.homes,
            guardians: world.ghp.to_vec(),
            perfect_line_cost: sim.spent,
        }
    }
}

/// **The settlement board.** Everything persistent, rendered as the thing a frontend
/// shows between runs: the record, the collection with its holes, the roads, and the
/// concrete reasons to go out again.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Standing {
    pub player: String,
    pub phase: Phase,
    pub here: String,
    pub here_name: String,
    pub hero_level: u64,
    pub hero_xp: u64,
    /// The XP floor for the next level, or `None` at the installed ceiling.
    pub next_level_at: Option<u64>,
    /// Expeditions sealed into the chronicle across the whole region.
    pub sealed_expeditions: u64,
    pub locations: Vec<LocationRecord>,
    pub reliquary: [RelicState; RELICS],
    pub roads: Vec<RoadStanding>,
    /// The held expedition — live in [`Phase::Expedition`], the tombstone of the last one
    /// in [`Phase::Settlement`].
    pub expedition: ExpeditionOutcome,
    /// The map the held expedition runs on, or (in the settlement) the map the NEXT
    /// expedition here will be drawn on.
    pub map: MapBriefing,
    /// The concrete, checkable reasons to descend again.
    pub asks: Vec<String>,
}

impl CampaignSession {
    /// Build the settlement board off committed state.
    pub fn standing(&self) -> Result<Standing, CampaignError> {
        let projection = self.projection()?;
        let map = self.region.map();
        let here = self.region.current_location();
        let here_name = map
            .location(&here)
            .map(|location| location.name.clone())
            .unwrap_or_else(|| here.clone());
        let phase = projection.phase;
        let expedition = self.expedition();
        let briefing = match phase {
            Phase::Expedition => MapBriefing::of(expedition.day),
            Phase::Settlement => {
                let ordinal = self.sealed_expeditions() + 1;
                let seed = expedition_day_seed(&self.config, &here, ordinal);
                MapBriefing::of(crate::descent::day_index(&seed))
            }
        };
        let roads = map
            .edges_from(&here)
            .iter()
            .map(|edge| RoadStanding {
                to: edge.to.clone(),
                name: map
                    .location(&edge.to)
                    .map(|location| location.name.clone())
                    .unwrap_or_else(|| edge.to.clone()),
                open: edge
                    .gate
                    .as_ref()
                    .is_none_or(|prereq| self.region.is_cleared(prereq)),
                needs: edge
                    .gate
                    .clone()
                    .filter(|prereq| !self.region.is_cleared(prereq)),
            })
            .collect::<Vec<_>>();
        let level = projection.hero_level;
        let mut standing = Standing {
            player: self.config.player.clone(),
            phase,
            here_name,
            hero_level: level,
            hero_xp: projection.hero_xp,
            next_level_at: (level < progression::MAX_LEVEL)
                .then(|| progression::xp_threshold(level + 1)),
            sealed_expeditions: self.sealed_expeditions(),
            locations: projection.records.clone(),
            reliquary: projection.relics,
            roads,
            expedition,
            map: briefing,
            asks: Vec::new(),
            here,
        };
        standing.asks = standing.derive_asks();
        Ok(standing)
    }
}

impl Standing {
    /// The record for the place the traveller stands in.
    pub fn here_record(&self) -> Option<&LocationRecord> {
        self.locations.iter().find(|record| record.id == self.here)
    }

    /// Relic slots that have never reached the reliquary.
    pub fn missing_relics(&self) -> Vec<usize> {
        (0..RELICS)
            .filter(|&relic| self.reliquary[relic] == RelicState::Unbanked)
            .collect()
    }

    /// **The reasons to go again**, derived from committed state only. Each one names a
    /// fact that has not happened yet and where today's map puts it.
    fn derive_asks(&self) -> Vec<String> {
        let mut asks = Vec::new();
        if self.phase == Phase::Expedition {
            asks.push(format!(
                "Expedition {} is underway on floor {} of {} — {} of {BREATH} light burned. \
                 The settlement is closed until you come home.",
                self.expedition.ordinal,
                self.expedition.depth,
                self.here_name,
                self.expedition.spent
            ));
            return asks;
        }

        let cleared = self.here_record().is_some_and(|record| record.cleared);
        if !cleared {
            let barred = self
                .roads
                .iter()
                .filter(|road| !road.open)
                .map(|road| road.name.as_str())
                .collect::<Vec<_>>();
            let opens = if barred.is_empty() {
                String::new()
            } else {
                format!(" Bank it and the road to {} opens.", barred.join(" and "))
            };
            asks.push(format!(
                "{} has never been crowned. Today's draw mints the Crown (relic 0) on floor {}.{}",
                self.here_name, self.map.homes[0], opens
            ));
        }

        let missing = self.missing_relics();
        let treasures = missing
            .iter()
            .copied()
            .filter(|&relic| relic >= FLOORS as usize)
            .collect::<Vec<_>>();
        for relic in &missing {
            asks.push(format!(
                "Relic {relic} has never reached the reliquary; today's draw mints it on floor {}.",
                self.map.homes[*relic]
            ));
        }
        if !cleared && !treasures.is_empty() {
            asks.push(format!(
                "You will not bring both home on one run: at floor {FLOORS} the pack is already \
                 the three keys and the Crown, which is exactly the {CAP}-deep carry ceiling. \
                 The Crown or a treasure — choose before you delve.",
            ));
        }

        if let Some(record) = self.here_record()
            && record.deepest < FLOORS
        {
            asks.push(format!(
                "You have never stood deeper than floor {} of {} in {} expedition(s).",
                record.deepest, self.here_name, record.runs
            ));
        }
        if asks.is_empty() {
            asks.push(format!(
                "{} is crowned and the reliquary is full. Nothing here is owed to you.",
                self.here_name
            ));
        }
        asks
    }

    /// The board as the text a chat or web adapter prints between runs.
    pub fn briefing(&self) -> String {
        let mut out = String::new();
        out.push_str(&format!(
            "{} — {} (level {}, {} XP",
            self.player, self.here_name, self.hero_level, self.hero_xp
        ));
        match self.next_level_at {
            Some(next) => out.push_str(&format!("/{next})\n")),
            None => out.push_str(", at the ceiling)\n"),
        }
        out.push_str(&format!(
            "{} expedition(s) sealed. The last one: {}\n",
            self.sealed_expeditions,
            describe_outcome(&self.expedition)
        ));
        out.push_str("\nTHE RECORD\n");
        for record in &self.locations {
            out.push_str(&format!(
                "  {:<24} {:>3} run(s), deepest floor {}, {} crown(s){}\n",
                record.name,
                record.runs,
                record.deepest,
                record.crowns,
                if record.cleared { ", road open" } else { "" },
            ));
        }
        out.push_str("\nTHE RELIQUARY\n  ");
        for (relic, state) in self.reliquary.iter().enumerate() {
            out.push_str(&match state {
                RelicState::Unbanked => format!("{relic}:— "),
                RelicState::Banked => format!("{relic}:held "),
                RelicState::RaidBound => format!("{relic}:vowed(raid) "),
                RelicState::BazaarBound => format!("{relic}:vowed(bazaar) "),
            });
        }
        out.push_str(&format!(
            "\n\nTHE NEXT MAP (draw {}, perfect line costs {} of {BREATH} light)\n",
            self.map.day, self.map.perfect_line_cost
        ));
        for (relic, floor) in self.map.homes.iter().enumerate() {
            out.push_str(&format!("  relic {relic} lies on floor {floor}\n"));
        }
        out.push_str("\nWHY GO BACK\n");
        for ask in &self.asks {
            out.push_str(&format!("  - {ask}\n"));
        }
        out
    }
}

fn describe_outcome(outcome: &ExpeditionOutcome) -> String {
    let lost = outcome.lost();
    let banked = outcome.banked();
    let fate = if outcome.light_died() {
        format!(
            "the light died on floor {} with {} relic(s) still in the pack",
            outcome.depth,
            lost.len()
        )
    } else if outcome.crowned() {
        format!("crowned, out of floor {}", outcome.depth)
    } else if outcome.over() {
        format!("banked {} relic(s) and walked out", banked.len())
    } else {
        format!("still on floor {}", outcome.depth)
    };
    format!(
        "expedition {} at {} on draw {} — {fate} ({} of {BREATH} light).",
        outcome.ordinal, outcome.location, outcome.day, outcome.spent
    )
}

/// Read the narration commitment bound into a primary campaign receipt.
pub fn bound_campaign_narration(receipt: &TurnReceipt) -> Option<FieldElement> {
    let topic = symbol(CAMPAIGN_NARRATION_TOPIC);
    receipt
        .emitted_events
        .iter()
        .find(|event| event.topic == topic)
        .and_then(|event| event.data.first().copied())
}

/// Read the optional raid/Bazaar context commitment from a relic-vow receipt.
pub fn bound_relic_context(receipt: &TurnReceipt) -> Option<FieldElement> {
    let topic = symbol(CAMPAIGN_NARRATION_TOPIC);
    receipt
        .emitted_events
        .iter()
        .find(|event| event.topic == topic)
        .and_then(|event| event.data.get(1).copied())
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CampaignError {
    Refused(String),
    Corrupt(String),
}

impl CampaignError {
    fn world(error: WorldError) -> Self {
        Self::Refused(error.to_string())
    }
}

impl std::fmt::Display for CampaignError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Refused(reason) => write!(formatter, "campaign action refused: {reason}"),
            Self::Corrupt(reason) => write!(formatter, "campaign record refused: {reason}"),
        }
    }
}

impl std::error::Error for CampaignError {}

fn validate_config(config: &CampaignConfig) -> Result<(), CampaignError> {
    if config.player.is_empty() || config.player.len() > 512 || config.player.contains('\0') {
        return Err(CampaignError::Refused(
            "player identity must be 1..=512 non-NUL bytes".to_string(),
        ));
    }
    if !matches!(
        config.class_id,
        progression::WARRIOR | progression::MAGE | progression::ROGUE
    ) {
        return Err(CampaignError::Refused("unknown hero class".to_string()));
    }
    Ok(())
}

fn validate_narration(narration: &str) -> Result<(), CampaignError> {
    if narration.len() > MAX_NARRATION_BYTES {
        return Err(CampaignError::Refused("narration is overlong".to_string()));
    }
    if narration.contains('\0') {
        return Err(CampaignError::Refused("narration contains NUL".to_string()));
    }
    Ok(())
}

fn descent_projection(
    sim: &Sim,
    command: DescentAction,
) -> (&'static str, Result<Sim, &'static str>) {
    match command {
        DescentAction::Delve => (DELVE, sim.delve()),
        DescentAction::Unlock { way } => (UNLOCK, sim.unlock(way)),
        DescentAction::Smite => (SMITE, sim.smite()),
        DescentAction::Loot { relic } => (LOOT, sim.loot(usize::from(relic))),
        DescentAction::Flee => (FLEE, sim.flee()),
    }
}

fn reliquary_story() -> CompiledStory {
    let mut cases = Vec::new();
    let mut var_slots = BTreeMap::new();
    for relic in 0..RELICS {
        var_slots.insert(relic_var(relic), relic as u64);
        for (method, target) in [
            (RELIQUARY_MINT, RELIC_BANKED),
            (RELIQUARY_RAID, RELIC_RAID_BOUND),
            (RELIQUARY_BAZAAR, RELIC_BAZAAR_BOUND),
        ] {
            cases.push(TransitionCase {
                guard: TransitionGuard::MethodIs {
                    method: symbol(&relic_method(method, relic)),
                },
                constraints: vec![StateConstraint::FieldEquals {
                    index: relic as u8,
                    value: field_from_u64(target),
                }],
            });
        }
        cases.push(TransitionCase {
            guard: TransitionGuard::SlotChanged { index: relic as u8 },
            constraints: vec![StateConstraint::AllowedTransitions {
                slot_index: relic as u8,
                allowed: vec![
                    (field_from_u64(0), field_from_u64(RELIC_BANKED)),
                    (
                        field_from_u64(RELIC_BANKED),
                        field_from_u64(RELIC_RAID_BOUND),
                    ),
                    (
                        field_from_u64(RELIC_BANKED),
                        field_from_u64(RELIC_BAZAAR_BOUND),
                    ),
                ],
            }],
        });
    }
    CompiledStory {
        scene_id: RELIQUARY_SCENE.to_string(),
        var_slots,
        has_slots: BTreeMap::new(),
        passage_index: BTreeMap::new(),
        program: CellProgram::Cases(cases),
        fully_gated: BTreeMap::new(),
    }
}

/// **The chronicle's teeth.** Three marks per location, and four real constraints that a
/// forged history has to get past:
///
/// * an unsanctioned method is a default-deny refusal (the program has dispatch cases, so
///   `NoTransitionCaseMatched` bites anything that is not a seal or an embark);
/// * ANY turn that moves a mark must move it UP — a `SlotChanged` guard carrying
///   [`StateConstraint::Monotonic`] on every one of the twelve slots. A run cannot be
///   un-run and a deepest reach cannot be walked back;
/// * a seal advances `runs` by EXACTLY one ([`StateConstraint::FieldDelta`]), keeps
///   `deepest` inside the dungeon ([`StateConstraint::FieldLte`] at [`FLOORS`]), and
///   holds `crowns <= runs` as an [`StateConstraint::AffineLe`] — so a crown cannot be
///   minted without an expedition to hang it on, and one seal cannot mint two;
/// * a seal at one location leaves every OTHER location's marks
///   [`StateConstraint::Immutable`], and an embark leaves ALL of them immutable — going
///   out is witnessed, but it books nothing.
fn chronicle_story(map: &RegionMap) -> CompiledStory {
    let count = map.locations.len();
    let mut var_slots = BTreeMap::new();
    for index in 0..count {
        var_slots.insert(runs_var(index), runs_slot(index) as u64);
        var_slots.insert(deepest_var(index), deepest_slot(index) as u64);
        var_slots.insert(crowns_var(index), crowns_slot(index) as u64);
    }

    let mut cases = Vec::new();
    for index in 0..count {
        let mut sealed = vec![
            StateConstraint::FieldDelta {
                index: runs_slot(index),
                delta: field_from_u64(1),
            },
            StateConstraint::Monotonic {
                index: deepest_slot(index),
            },
            StateConstraint::Monotonic {
                index: crowns_slot(index),
            },
            StateConstraint::FieldLte {
                index: deepest_slot(index),
                value: field_from_u64(FLOORS),
            },
            // crowns - runs <= 0.
            StateConstraint::AffineLe {
                terms: vec![(1, crowns_slot(index)), (-1, runs_slot(index))],
                c: 0,
            },
        ];
        let mut embarked = Vec::new();
        for other in 0..count {
            for slot in marks_of(other) {
                if other != index {
                    sealed.push(StateConstraint::Immutable { index: slot });
                }
                embarked.push(StateConstraint::Immutable { index: slot });
            }
        }
        cases.push(TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: symbol(&chronicle_method(CHRONICLE_SEAL, index)),
            },
            constraints: sealed,
        });
        cases.push(TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: symbol(&chronicle_method(CHRONICLE_EMBARK, index)),
            },
            constraints: embarked,
        });
    }
    // The global no-erasure invariant: whichever method moved a mark, it moved it up.
    for index in 0..count {
        for slot in marks_of(index) {
            cases.push(TransitionCase {
                guard: TransitionGuard::SlotChanged { index: slot },
                constraints: vec![StateConstraint::Monotonic { index: slot }],
            });
        }
    }

    CompiledStory {
        scene_id: CHRONICLE_SCENE.to_string(),
        var_slots,
        has_slots: BTreeMap::new(),
        passage_index: BTreeMap::new(),
        program: CellProgram::Cases(cases),
        fully_gated: BTreeMap::new(),
    }
}

fn runs_slot(index: usize) -> u8 {
    (index * CHRONICLE_MARKS) as u8
}
fn deepest_slot(index: usize) -> u8 {
    runs_slot(index) + 1
}
fn crowns_slot(index: usize) -> u8 {
    runs_slot(index) + 2
}
fn marks_of(index: usize) -> [u8; CHRONICLE_MARKS] {
    [runs_slot(index), deepest_slot(index), crowns_slot(index)]
}
fn runs_var(index: usize) -> String {
    format!("runs_{index}")
}
fn deepest_var(index: usize) -> String {
    format!("deepest_{index}")
}
fn crowns_var(index: usize) -> String {
    format!("crowns_{index}")
}
fn chronicle_method(prefix: &str, index: usize) -> String {
    format!("{prefix}/{index}")
}

fn relic_var(relic: usize) -> String {
    format!("relic_{relic}")
}

fn relic_method(prefix: &str, relic: usize) -> String {
    format!("{prefix}/{relic}")
}

fn narration_hash(narration: &str) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(CAMPAIGN_NARRATION_TOPIC);
    hash_bytes(&mut hasher, narration.as_bytes());
    *hasher.finalize().as_bytes()
}

fn relic_binding_hash(use_: &RelicUse) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(RELIC_BINDING_DOMAIN);
    hash_relic_use(&mut hasher, use_);
    *hasher.finalize().as_bytes()
}

fn relic_grant_id(
    previous: [u8; 32],
    revision: u64,
    player: &str,
    relic: u8,
    use_: &RelicUse,
    receipt: [u8; 32],
) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(RELIC_GRANT_DOMAIN);
    hasher.update(&previous);
    hasher.update(&revision.to_be_bytes());
    hash_bytes(&mut hasher, player.as_bytes());
    hasher.update(&[relic]);
    hash_relic_use(&mut hasher, use_);
    hasher.update(&receipt);
    *hasher.finalize().as_bytes()
}

fn hash_relic_use(hasher: &mut blake3::Hasher, use_: &RelicUse) {
    match use_ {
        RelicUse::RaidSeat { session, seat } => {
            hasher.update(&[0]);
            hasher.update(session);
            hasher.update(&[*seat]);
        }
        RelicUse::BazaarOrder { market, order } => {
            hasher.update(&[1]);
            hasher.update(market);
            hasher.update(order);
        }
    }
}

fn derive_seed(seed: u8, label: &str) -> u8 {
    let mut hasher = blake3::Hasher::new_derive_key(LOCATION_SEED_DOMAIN);
    hasher.update(&[seed]);
    hash_bytes(&mut hasher, label.as_bytes());
    hasher.finalize().as_bytes()[0]
}

/// **The day-seed expedition `ordinal` at `location` is drawn under.** This is the one
/// place a map is chosen, and it depends on the ordinal — so the second expedition at a
/// place is a DIFFERENT member of the Lean-checked drawn family than the first. Fully
/// determined by the campaign config, so a replay redraws the identical dungeon and the
/// settlement can brief the next map before it is committed to.
pub fn expedition_day_seed(config: &CampaignConfig, location: &str, ordinal: u64) -> CommittedSeed {
    let mut hasher = blake3::Hasher::new_derive_key(EXPEDITION_SEED_DOMAIN);
    hasher.update(&[config.seed]);
    hash_bytes(&mut hasher, config.player.as_bytes());
    hash_bytes(&mut hasher, location.as_bytes());
    hasher.update(&ordinal.to_be_bytes());
    CommittedSeed::from_bytes(*hasher.finalize().as_bytes())
}

/// The world-cell deploy seed for the expedition drawn under `day_seed`.
fn expedition_cell_seed(day_seed: &CommittedSeed) -> u8 {
    day_seed.as_bytes()[31]
}

/// **The whole committed descent state, hashed.** Every one of the thirteen Lean
/// registers and all eight relic custody keys are read back OUT of the executor, so this
/// commits to what the referee admitted rather than to what the Rust mover believed.
fn expedition_commitment(outcome: &ExpeditionOutcome, descent: &Descent) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(EXPEDITION_DOMAIN);
    hash_bytes(&mut hasher, outcome.location.as_bytes());
    hasher.update(&outcome.ordinal.to_be_bytes());
    hasher.update(&(outcome.day as u64).to_be_bytes());
    for name in REGISTERS {
        hash_bytes(&mut hasher, name.as_bytes());
        hasher.update(&descent.read_reg(name).to_be_bytes());
    }
    for relic in 0..RELICS {
        hasher.update(&descent.read_relic(relic).to_be_bytes());
    }
    *hasher.finalize().as_bytes()
}

/// The value an [`CampaignAction::Embark`] turn commits: which place, which ordinal, and
/// which map was drawn — witnessed before the first move is made.
pub fn embark_commitment(
    location: &str,
    ordinal: u64,
    day_seed: &CommittedSeed,
    day: usize,
) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(EMBARK_DOMAIN);
    hash_bytes(&mut hasher, location.as_bytes());
    hasher.update(&ordinal.to_be_bytes());
    hasher.update(day_seed.as_bytes());
    hasher.update(&(day as u64).to_be_bytes());
    *hasher.finalize().as_bytes()
}

/// **Check that a sealed expedition's chronicle turn names the run it claims.** The seal
/// receipt's second event word must be exactly [`ExpeditionOutcome::commitment`], which
/// hashes the descent cell's committed registers and custody. A record that relabels a
/// shallow run as a deep one fails this without also forging the descent receipts the
/// same event carries — and those are re-executed by [`CampaignSession::resume`].
pub fn verify_expedition_seal(receipt: &TurnReceipt, outcome: &ExpeditionOutcome) -> bool {
    bound_relic_context(receipt) == Some(outcome.commitment)
}

/// **The campaign's entire XP supply**, at the given region size. XP is paid only for
/// facts that have never happened before, so this is a finite number rather than a
/// grinding rate: every location crowned once, every location bottomed out, and all
/// [`RELICS`] relics brought home.
pub fn max_campaign_xp(locations: u64) -> u64 {
    locations * CROWN_XP + locations * FLOORS * DEPTH_XP + RELICS as u64 * RELIC_XP
}

fn genesis_root(
    config: &CampaignConfig,
    receipts: &[TurnReceipt],
    projection: &CampaignProjection,
) -> Result<[u8; 32], CampaignError> {
    let mut hasher = blake3::Hasher::new_derive_key(CAMPAIGN_ROOT_DOMAIN);
    hasher.update(&[config.seed]);
    hash_bytes(&mut hasher, config.player.as_bytes());
    hasher.update(&config.class_id.to_be_bytes());
    hash_receipts(&mut hasher, receipts)?;
    hash_projection(&mut hasher, projection);
    Ok(*hasher.finalize().as_bytes())
}

#[allow(clippy::too_many_arguments)]
fn event_root(
    previous: [u8; 32],
    revision: u64,
    action: &CampaignAction,
    narration: &str,
    narration_commitment: [u8; 32],
    receipts: &[TurnReceipt],
    projection: &CampaignProjection,
    grant: Option<&RelicGrant>,
) -> Result<[u8; 32], CampaignError> {
    let mut hasher = blake3::Hasher::new_derive_key(CAMPAIGN_ROOT_DOMAIN);
    hasher.update(&previous);
    hasher.update(&revision.to_be_bytes());
    hash_action(&mut hasher, action);
    hash_bytes(&mut hasher, narration.as_bytes());
    hasher.update(&narration_commitment);
    hash_receipts(&mut hasher, receipts)?;
    hash_projection(&mut hasher, projection);
    match grant {
        Some(grant) => {
            hasher.update(&[1]);
            hasher.update(&grant.id);
        }
        None => {
            hasher.update(&[0]);
        }
    };
    Ok(*hasher.finalize().as_bytes())
}

fn hash_action(hasher: &mut blake3::Hasher, action: &CampaignAction) {
    match action {
        CampaignAction::Descent(command) => {
            hasher.update(&[0]);
            match command {
                DescentAction::Delve => hasher.update(&[0]),
                DescentAction::Unlock { way } => {
                    hasher.update(&[1]);
                    hasher.update(&way.to_be_bytes())
                }
                DescentAction::Smite => hasher.update(&[2]),
                DescentAction::Loot { relic } => {
                    hasher.update(&[3]);
                    hasher.update(&[*relic])
                }
                DescentAction::Flee => hasher.update(&[4]),
            };
        }
        CampaignAction::Travel { destination } => {
            hasher.update(&[1]);
            hash_bytes(hasher, destination.as_bytes());
        }
        CampaignAction::LevelUp => {
            hasher.update(&[2]);
        }
        CampaignAction::BindRelic { relic, use_ } => {
            hasher.update(&[3, *relic]);
            hash_relic_use(hasher, use_);
        }
        CampaignAction::Return => {
            hasher.update(&[4]);
        }
        CampaignAction::Embark => {
            hasher.update(&[5]);
        }
    }
}

fn hash_receipts(
    hasher: &mut blake3::Hasher,
    receipts: &[TurnReceipt],
) -> Result<(), CampaignError> {
    hasher.update(
        &u64::try_from(receipts.len())
            .expect("a bounded receipt forest fits u64")
            .to_be_bytes(),
    );
    for receipt in receipts {
        let bytes = serde_json::to_vec(receipt).map_err(|error| {
            CampaignError::Corrupt(format!("receipt serialization failed: {error}"))
        })?;
        hash_bytes(hasher, &bytes);
    }
    Ok(())
}

fn hash_projection(hasher: &mut blake3::Hasher, projection: &CampaignProjection) {
    hash_bytes(hasher, projection.location.as_bytes());
    hasher.update(
        &u64::try_from(projection.cleared_locations.len())
            .expect("a bounded region fits u64")
            .to_be_bytes(),
    );
    for location in &projection.cleared_locations {
        hash_bytes(hasher, location.as_bytes());
    }
    for value in [
        projection.hero_xp,
        projection.hero_level,
        projection.hero_class,
        projection.descent_depth,
        projection.descent_spent,
        projection.descent_wounds,
    ] {
        hasher.update(&value.to_be_bytes());
    }
    hasher.update(&[u8::from(projection.descent_terminal)]);
    for state in projection.expedition_custody {
        hasher.update(&state.to_be_bytes());
    }
    for state in projection.relics {
        hasher.update(&[match state {
            RelicState::Unbanked => 0,
            RelicState::Banked => 1,
            RelicState::RaidBound => 2,
            RelicState::BazaarBound => 3,
        }]);
    }
    // The persistent campaign layer. Every one of these is a claim about what carried
    // across runs, so all of them ride the same hash chain the receipts do — a record
    // cannot quietly inflate a run count, a deepest reach, or the phase it stands in.
    hasher.update(&[match projection.phase {
        Phase::Expedition => 0,
        Phase::Settlement => 1,
    }]);
    hasher.update(&projection.expedition_ordinal.to_be_bytes());
    hash_bytes(hasher, projection.expedition_location.as_bytes());
    hasher.update(&(projection.expedition_day as u64).to_be_bytes());
    hasher.update(
        &u64::try_from(projection.records.len())
            .expect("a bounded region fits u64")
            .to_be_bytes(),
    );
    for record in &projection.records {
        hash_bytes(hasher, record.id.as_bytes());
        hasher.update(&[u8::from(record.cleared)]);
        for value in [record.runs, record.deepest, record.crowns] {
            hasher.update(&value.to_be_bytes());
        }
    }
}

fn hash_bytes(hasher: &mut blake3::Hasher, bytes: &[u8]) {
    hasher.update(
        &u64::try_from(bytes.len())
            .expect("bounded campaign material fits u64")
            .to_be_bytes(),
    );
    hasher.update(bytes);
}

#[cfg(test)]
mod chronicle_teeth {
    //! The chronicle's constraints, driven at the CELL. The record-level falsifiers in
    //! `tests/campaign_engine.rs` go through `resume`, which compares projections — they
    //! would catch a forged field whether or not it had a tooth behind it. These drive
    //! raw turns straight at the deployed program, so what is being observed is the
    //! executor refusing, not a comparison failing.

    use super::*;

    fn deploy() -> (RegionMap, WorldCell) {
        let map = deepening_ways();
        let cell = WorldCell::deploy_compiled(Arc::new(chronicle_story(&map)), 11)
            .expect("the chronicle deploys");
        (map, cell)
    }

    fn write(cell: &WorldCell, method: &str, marks: &[(u8, u64)]) -> Result<(), String> {
        let id = cell.cell_id();
        cell.apply_raw(
            method,
            marks
                .iter()
                .map(|(slot, value)| Effect::SetField {
                    cell: id,
                    index: *slot as u64,
                    value: field_from_u64(*value),
                })
                .collect(),
        )
        .map(|_| ())
        .map_err(|error| error.to_string())
    }

    fn seal(index: usize) -> String {
        chronicle_method(CHRONICLE_SEAL, index)
    }

    #[test]
    fn an_honest_seal_commits_and_every_forgery_is_an_executor_refusal() {
        let (_map, chronicle) = deploy();

        // NON-VACUITY: the honest seal lands. Everything below is the same shape of turn
        // with one thing wrong.
        write(
            &chronicle,
            &seal(0),
            &[(runs_slot(0), 1), (deepest_slot(0), 3), (crowns_slot(0), 1)],
        )
        .expect("the sanctioned seal commits");
        assert_eq!(chronicle.read_var(&deepest_var(0)), 3);

        // Default-deny: a mark written under a method the program never installed.
        assert!(
            write(&chronicle, "chronicle/forge/0", &[(deepest_slot(0), 4)]).is_err(),
            "a forged method must fail closed"
        );

        // A deepest reach cannot be walked back, even on an otherwise-lawful seal.
        assert!(
            write(
                &chronicle,
                &seal(0),
                &[(runs_slot(0), 2), (deepest_slot(0), 1)],
            )
            .is_err(),
            "Monotonic(deepest) must refuse an erased reach"
        );

        // Nor can a run count.
        assert!(
            write(&chronicle, &seal(0), &[(runs_slot(0), 0)]).is_err(),
            "FieldDelta(runs, +1) must refuse an un-run expedition"
        );
        assert!(
            write(&chronicle, &seal(0), &[(runs_slot(0), 9)]).is_err(),
            "one seal is one run, never nine"
        );

        // A crown needs an expedition under it.
        assert!(
            write(
                &chronicle,
                &seal(0),
                &[(runs_slot(0), 2), (crowns_slot(0), 3)],
            )
            .is_err(),
            "AffineLe(crowns - runs <= 0) must refuse more crowns than runs"
        );

        // A reach deeper than the dungeon.
        assert!(
            write(
                &chronicle,
                &seal(0),
                &[(runs_slot(0), 2), (deepest_slot(0), FLOORS + 1)],
            )
            .is_err(),
            "FieldLte(deepest, FLOORS) must refuse a floor that does not exist"
        );

        // A seal at one place cannot book progress at another.
        assert!(
            write(
                &chronicle,
                &seal(0),
                &[(runs_slot(0), 2), (crowns_slot(1), 1)],
            )
            .is_err(),
            "Immutable on the other places' marks must refuse a cross-location credit"
        );

        // Going out is witnessed, but it books nothing.
        assert!(
            write(
                &chronicle,
                &chronicle_method(CHRONICLE_EMBARK, 0),
                &[(crowns_slot(0), 2)],
            )
            .is_err(),
            "an embark must not be able to move a mark"
        );

        // Anti-ghost: after all of that, the chronicle still says what it said.
        assert_eq!(chronicle.read_var(&runs_var(0)), 1);
        assert_eq!(chronicle.read_var(&deepest_var(0)), 3);
        assert_eq!(chronicle.read_var(&crowns_var(0)), 1);
        assert_eq!(chronicle.read_var(&crowns_var(1)), 0);

        // And a second honest seal still lands (the refusals did not wedge the cell).
        write(
            &chronicle,
            &seal(0),
            &[(runs_slot(0), 2), (deepest_slot(0), FLOORS)],
        )
        .expect("the next sanctioned seal commits");
        assert_eq!(chronicle.read_var(&deepest_var(0)), FLOORS);
    }

    /// The XP supply is a fixed, finite number rather than a rate — and it is tuned so
    /// the installed level ceiling is reachable only at the end of a completed campaign.
    #[test]
    fn the_xp_supply_is_finite_and_just_clears_the_level_ceiling() {
        let supply = max_campaign_xp(4);
        assert_eq!(supply, 4 * CROWN_XP + 4 * FLOORS * DEPTH_XP + 8 * RELIC_XP);
        let ceiling = progression::xp_threshold(progression::MAX_LEVEL);
        assert!(
            supply >= ceiling,
            "a completionist can reach level {}: {supply} of {ceiling}",
            progression::MAX_LEVEL
        );
        assert!(
            supply < ceiling + CROWN_XP,
            "but only just — the ceiling is not handed out early: {supply} vs {ceiling}"
        );
    }
}

fn same_event(left: &CampaignEvent, right: &CampaignEvent) -> Result<bool, CampaignError> {
    if left.revision != right.revision
        || left.action != right.action
        || left.narration != right.narration
        || left.narration_commitment != right.narration_commitment
        || left.projection != right.projection
        || left.grant != right.grant
        || left.root != right.root
        || left.receipts.len() != right.receipts.len()
    {
        return Ok(false);
    }
    for (left, right) in left.receipts.iter().zip(&right.receipts) {
        let left = serde_json::to_vec(left).map_err(|error| {
            CampaignError::Corrupt(format!("receipt serialization failed: {error}"))
        })?;
        let right = serde_json::to_vec(right).map_err(|error| {
            CampaignError::Corrupt(format!("receipt serialization failed: {error}"))
        })?;
        if left != right {
            return Ok(false);
        }
    }
    Ok(true)
}
