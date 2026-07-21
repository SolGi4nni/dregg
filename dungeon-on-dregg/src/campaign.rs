//! One coherent game core for the Dungeon, the Descent, and their world.
//!
//! This is the game-engine seam below web/chat adapters. A [`CampaignSession`]
//! owns four real executor-backed objects: a Lean-native [`Descent`], the
//! persistent progression hero, the persistent overworld region, and a
//! persistent relic reliquary. Clients submit a closed [`CampaignAction`]; prose
//! is bound into the primary real turn as an event but cannot choose effects.
//!
//! The durable object is [`CampaignRecord`]. It stores typed inputs and exact
//! receipts, not trusted summary counters. [`CampaignSession::resume`] deploys
//! fresh deterministic objects and re-executes every input, comparing the full
//! receipt bytes, derived projection, and hash-chain head. A copied, reordered,
//! or substituted event therefore cannot mint XP, an overworld clear, or a
//! relic binding.
//!
//! The small new mechanic is a **relic vow**. A relic banked by a crowned run
//! persists in the reliquary, then may be bound exactly once to either a raid
//! seat or a Bazaar order. The context commitment rides the same real executor
//! receipt as the vow. [`RelicGrant`] is the frontend/protocol affordance: a
//! consumer verifies it by replaying the campaign record before honoring it.

use std::collections::BTreeMap;
use std::sync::Arc;

use dregg_app_framework::{
    CellProgram, Effect, Event, FieldElement, StateConstraint, TransitionCase, TransitionGuard,
    TurnReceipt, field_from_u64, symbol,
};
use serde::{Deserialize, Serialize};
use spween_dregg::{CompiledStory, WorldCell, WorldError};

use crate::descent::{BANKED, DELVE, Descent, FLEE, LOOT, RELICS, SMITE, Sim, UNLOCK};
use crate::meta;
use crate::overworld::{RegionCell, deepening_ways};
use crate::progression;

/// Event topic used by every campaign action's primary real turn.
pub const CAMPAIGN_NARRATION_TOPIC: &str = "dungeon-on-dregg/campaign-narration-v1";
/// XP awarded by one crowned, replay-verifiable expedition.
pub const CROWN_XP: u64 = 100;
/// A bounded durable journal; this is well above four complete regions.
pub const MAX_CAMPAIGN_EVENTS: usize = 1024;
/// Narration is flavor carried by receipts, not an unbounded storage channel.
pub const MAX_NARRATION_BYTES: usize = 8 * 1024;

const CAMPAIGN_ROOT_DOMAIN: &str = "dungeon-on-dregg/campaign-root-v1";
const RELIC_GRANT_DOMAIN: &str = "dungeon-on-dregg/relic-grant-v1";
const RELIC_BINDING_DOMAIN: &str = "dungeon-on-dregg/relic-binding-v1";
const LOCATION_SEED_DOMAIN: &str = "dungeon-on-dregg/location-seed-v1";
const RELIQUARY_SCENE: &str = "dungeon-on-dregg/reliquary/v1";
const RELIQUARY_MINT: &str = "reliquary/mint";
const RELIQUARY_RAID: &str = "reliquary/vow/raid";
const RELIQUARY_BAZAAR: &str = "reliquary/vow/bazaar";
const RELIC_BANKED: u64 = 1;
const RELIC_RAID_BOUND: u64 = 2;
const RELIC_BAZAAR_BOUND: u64 = 3;

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
    Descent(DescentAction),
    Travel { destination: String },
    LevelUp,
    BindRelic { relic: u8, use_: RelicUse },
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

/// The complete frontend-neutral view derived from the four real objects.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CampaignProjection {
    pub location: String,
    pub cleared_locations: Vec<String>,
    pub hero_xp: u64,
    pub hero_level: u64,
    pub hero_class: u64,
    pub descent_depth: u64,
    pub descent_spent: u64,
    pub descent_wounds: u64,
    pub descent_terminal: bool,
    pub expedition_custody: [u64; RELICS],
    pub relics: [RelicState; RELICS],
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
    events: Vec<CampaignEvent>,
    root: [u8; 32],
}

impl CampaignSession {
    pub fn open(config: CampaignConfig) -> Result<Self, CampaignError> {
        validate_config(&config)?;
        let map = deepening_ways();
        let hero = meta::deploy_meta_hero(derive_seed(config.seed, "hero"));
        let class_receipt =
            progression::choose_class(&hero, config.class_id).map_err(CampaignError::world)?;
        let level_receipt = progression::level_up(&hero).map_err(CampaignError::world)?;
        let region = RegionCell::deploy(&map, derive_seed(config.seed, "region"));
        let descent = Descent::deploy(location_seed(config.seed, &map.start))
            .map_err(CampaignError::world)?;
        let reliquary = WorldCell::deploy_compiled(
            Arc::new(reliquary_story()),
            derive_seed(config.seed, "reliquary"),
        )
        .map_err(CampaignError::world)?;

        let mut session = Self {
            config,
            hero,
            region,
            descent,
            reliquary,
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
            location: self.region.current_location(),
            cleared_locations,
            hero_xp: self.hero.read_var("xp"),
            hero_level: self.hero.read_var("level"),
            hero_class: self.hero.read_var("class"),
            descent_depth: sim.depth,
            descent_spent: sim.spent,
            descent_wounds: sim.wounds,
            descent_terminal: sim.fate != 0,
            expedition_custody: sim.custody,
            relics,
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
                let (method, next) = descent_projection(self.descent.sim(), *command);
                let primary = self
                    .descent
                    .commit_projected_with_event(method, next, event)
                    .map_err(CampaignError::world)?;
                receipts.push(primary);

                if matches!(command, DescentAction::Flee) && self.descent.sim().fate != 0 {
                    let banked = self
                        .descent
                        .sim()
                        .custody
                        .iter()
                        .enumerate()
                        .filter_map(|(index, &state)| (state == BANKED).then_some(index))
                        .collect::<Vec<_>>();
                    if banked.contains(&0) {
                        let location = self.region.current_location();
                        receipts.push(
                            self.region
                                .clear(&location)
                                .map_err(CampaignError::Refused)?,
                        );
                        receipts.push(
                            progression::gain_xp(&self.hero, CROWN_XP)
                                .map_err(CampaignError::world)?,
                        );
                        for relic in banked {
                            if self.reliquary.read_var(&relic_var(relic)) == 0 {
                                receipts.push(self.mint_relic(relic)?);
                            }
                        }
                    }
                }
            }
            CampaignAction::Travel { destination } => {
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
                self.descent = Descent::deploy(location_seed(self.config.seed, destination))
                    .map_err(CampaignError::world)?;
            }
            CampaignAction::LevelUp => {
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

fn location_seed(seed: u8, location: &str) -> u8 {
    derive_seed(seed, location)
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
}

fn hash_bytes(hasher: &mut blake3::Hasher, bytes: &[u8]) {
    hasher.update(
        &u64::try_from(bytes.len())
            .expect("bounded campaign material fits u64")
            .to_be_bytes(),
    );
    hasher.update(bytes);
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
