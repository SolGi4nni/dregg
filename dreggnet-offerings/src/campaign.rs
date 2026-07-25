//! A player-driven campaign joining the real overworld region cell to the Lean-native Descent.
//!
//! Every map location opens a fresh [`NativeDescentOffering`]. The player submits every native
//! move through the ordinary [`Offering`] surface; there is no winning script and no autoplay in
//! this adapter. Only a terminal settlement that (1) carries the Crown of the Deep and (2)
//! re-verifies by fresh native replay is allowed to fire that location's real
//! [`RegionCell::clear`] WriteOnce turn. The resulting region-cell predicate, not a Rust boolean,
//! gates travel into the deeper map.
//!
//! ## Assurance boundary
//!
//! The native move and region clear are separate real executor commits coordinated by this
//! Offering. Exact public replay binds both receipts, the actor, the native root, and the region
//! trajectory, but this is not yet one atomic cross-cell hyperedge or a succinct proof. A host
//! must durably store [`DescentCampaignRecord`] and protect it against rollback; its public hash
//! chain detects substitution but is not an external anchor.
//!
//! ## The day binding
//!
//! A campaign carries whatever day binding its native offering carries
//! ([`DescentCampaignOffering::on_beacon`] is the live path;
//! [`over`](DescentCampaignOffering::over) is the reproducible seed-derived one). ⚠ NAMED SEAM:
//! [`Offering::verify`]'s campaign replay re-opens each location's native world through THIS
//! campaign's offering, so a campaign record only re-verifies under a campaign bound to the same
//! day. A beacon-bound campaign is therefore a *day's* campaign: an expedition record from
//! another day must be verified against that day's campaign (`over_on_day(map, day)`), not
//! today's. The native Descent itself has no such seam — its
//! [`resume_record`](NativeDescentOffering::resume_record) reads the record's own day-seed.

use deos_view::{MenuItem, ViewNode};
use dregg_app_framework::TurnReceipt;
use dungeon_on_dregg::descent::{ASCEND, DELVE, FLEE, LOOT, LUNGE, SMITE, UNLOCK};
use dungeon_on_dregg::overworld::{RegionCell, RegionMap, deepening_ways};
use procgen_dregg::CommittedSeed;
use procgen_dregg::beacon::DailyBeacon;

use crate::native_descent::{
    NativeDescentMove, NativeDescentOffering, NativeDescentRecord, NativeDescentSession,
};
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

/// The campaign-level travel verb. Its argument is the stable index in the region map.
pub const CAMPAIGN_TRAVEL: &str = "campaign-travel";
/// A bounded public journal; four perfect expeditions plus travel fit comfortably within it.
pub const MAX_CAMPAIGN_EVENTS: usize = 1024;

const MAX_ACTOR_BYTES: usize = 512;
const GENESIS_ROOT_DOMAIN: &str = "dregg.native-descent-campaign.genesis.v1";
const EVENT_ROOT_DOMAIN: &str = "dregg.native-descent-campaign.event.v1";
const LOCATION_SEED_DOMAIN: &str = "dregg.native-descent-campaign.location-seed.v1";

/// One exact player command in the campaign journal.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DescentCampaignMove {
    /// A move submitted to the current location's Lean-native Descent.
    Native(NativeDescentMove),
    /// A real region-cell travel turn.
    Travel(String),
}

/// One actor-bound campaign event. A crowned terminal native move carries two receipts: the
/// Descent settlement and the region clear it authorized. Ordinary native moves carry only the
/// first; travel carries only the second.
#[derive(Clone, Debug)]
pub struct DescentCampaignEvent {
    pub revision: u64,
    pub actor: DreggIdentity,
    /// Location before this command executes.
    pub location: String,
    pub command: DescentCampaignMove,
    pub native_receipt: Option<TurnReceipt>,
    pub region_receipt: Option<TurnReceipt>,
    pub post_native_root: [u8; 32],
    pub post_native_revision: u64,
    /// Whether this event cleared its location with a replay-verified crown.
    pub crowned: bool,
    pub root: [u8; 32],
}

/// Fully derived checkpoint at a campaign event boundary.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DescentCampaignCheckpoint {
    pub actor: DreggIdentity,
    pub revision: u64,
    pub root: [u8; 32],
    pub current_location: String,
    pub cleared_locations: Vec<String>,
    pub active_native_root: [u8; 32],
    pub active_native_revision: u64,
    pub active_crowned: bool,
}

/// Untrusted, public restart material. Acceptance always rebuilds both executors and replays every
/// command. The record intentionally stores no separately trusted campaign counters.
#[derive(Clone, Debug)]
pub struct DescentCampaignRecord {
    pub seed: u8,
    pub actor: Option<DreggIdentity>,
    pub events: Vec<DescentCampaignEvent>,
    pub root: [u8; 32],
    pub checkpoint: Option<DescentCampaignCheckpoint>,
    /// Exact current-location native record, including accepted shielded operations.
    pub active: NativeDescentRecord,
}

/// A live traversal: one real region cell and the current location's native game.
pub struct DescentCampaignSession {
    seed: u8,
    actor: Option<DreggIdentity>,
    region: RegionCell,
    active: NativeDescentSession,
    events: Vec<DescentCampaignEvent>,
    root: [u8; 32],
    checkpoint: Option<DescentCampaignCheckpoint>,
}

impl DescentCampaignSession {
    pub fn actor(&self) -> Option<&DreggIdentity> {
        self.actor.as_ref()
    }

    pub fn revision(&self) -> u64 {
        u64::try_from(self.events.len()).expect("the fixed campaign journal bound fits u64")
    }

    pub fn root(&self) -> [u8; 32] {
        self.root
    }

    pub fn current_location(&self) -> String {
        self.region.current_location()
    }

    pub fn is_cleared(&self, location: &str) -> bool {
        self.region.is_cleared(location)
    }

    pub fn cleared_count(&self) -> usize {
        self.region.cleared_count()
    }

    pub fn active_descent(&self) -> &NativeDescentSession {
        &self.active
    }

    pub fn events(&self) -> &[DescentCampaignEvent] {
        &self.events
    }

    pub fn checkpoint(&self) -> Option<&DescentCampaignCheckpoint> {
        self.checkpoint.as_ref()
    }

    pub fn export_record(&self) -> DescentCampaignRecord {
        DescentCampaignRecord {
            seed: self.seed,
            actor: self.actor.clone(),
            events: self.events.clone(),
            root: self.root,
            checkpoint: self.checkpoint.clone(),
            active: self.active.export_record(),
        }
    }
}

/// An additive campaign over a region topology. The default is the existing Deepening Ways.
#[derive(Clone, Debug)]
pub struct DescentCampaignOffering {
    map: RegionMap,
    native: NativeDescentOffering,
}

impl DescentCampaignOffering {
    /// The stable cross-frontend catalog key for this campaign composition.
    pub const KEY: &'static str = "descent-campaign";

    pub fn new() -> Self {
        Self::over(deepening_ways())
    }

    pub fn over(map: RegionMap) -> Self {
        Self::over_with(map, NativeDescentOffering::new())
    }

    /// **The live daily campaign** — every expedition this campaign opens deploys on the day's
    /// verified beacon, so an expedition's banked relics mint under a provenance root that was
    /// unpredictable until that round was revealed. Fail-closed: a beacon that does not verify
    /// yields no campaign ([`NativeDescentOffering::on_beacon`] verifies before binding).
    pub fn on_beacon(beacon: &DailyBeacon) -> Result<Self, OfferingError> {
        Ok(Self::over_with(
            deepening_ways(),
            NativeDescentOffering::on_beacon(beacon)?,
        ))
    }

    /// A campaign over `map` whose expeditions run on the day `day` names — the
    /// [`on_beacon`](Self::on_beacon) path with the beacon already verified by the caller.
    pub fn over_on_day(map: RegionMap, day: CommittedSeed) -> Self {
        Self::over_with(map, NativeDescentOffering::on_day(day))
    }

    /// A campaign over `map` whose expeditions ride the supplied native offering — the one
    /// place the campaign's day binding is chosen.
    pub fn over_with(map: RegionMap, native: NativeDescentOffering) -> Self {
        Self { map, native }
    }

    /// The default Deepening Ways campaign riding the supplied native offering — the
    /// registration seam a catalog uses to hand the campaign its day binding without naming
    /// the map (or depending on the overworld layer) itself.
    pub fn with_native(native: NativeDescentOffering) -> Self {
        Self::over_with(deepening_ways(), native)
    }

    /// The verified beacon day this campaign's expeditions currently mint their relics under,
    /// if it binds one.
    pub fn day(&self) -> Option<CommittedSeed> {
        self.native.day()
    }

    pub fn map(&self) -> &RegionMap {
        &self.map
    }

    /// Resume only after exact fresh replay of every native and region command.
    pub fn resume_record(
        &self,
        record: &DescentCampaignRecord,
    ) -> Result<DescentCampaignSession, OfferingError> {
        self.replay_record(record).map_err(OfferingError::Deploy)
    }

    fn deploy(&self, seed: u8) -> Result<DescentCampaignSession, String> {
        if self.map.locations.is_empty() || !self.map.has_location(&self.map.start) {
            return Err("campaign map has no valid start location".to_string());
        }
        let region = RegionCell::deploy(&self.map, seed);
        let active = self.open_native(seed, &self.map.start)?;
        let root = genesis_root(&self.map, seed, active.root());
        Ok(DescentCampaignSession {
            seed,
            actor: None,
            region,
            active,
            events: Vec::new(),
            root,
            checkpoint: None,
        })
    }

    fn open_native(&self, seed: u8, location: &str) -> Result<NativeDescentSession, String> {
        self.native
            .open(SessionConfig::with_seed(location_seed(seed, location)))
            .map_err(|error| error.to_string())
    }

    fn actions_for_session(&self, session: &DescentCampaignSession) -> Vec<Action> {
        let here = session.current_location();
        if !session.region.is_cleared(&here) {
            return self
                .native
                .actions(&session.active)
                .into_iter()
                .map(|mut action| {
                    action.label =
                        format!("{} · {}", location_name(&self.map, &here), action.label);
                    action
                })
                .collect();
        }
        self.map
            .locations
            .iter()
            .enumerate()
            .filter_map(|(index, location)| {
                let edge = self
                    .map
                    .edges_from(&here)
                    .into_iter()
                    .find(|edge| edge.to == location.id)?;
                let enabled = edge
                    .gate
                    .as_ref()
                    .is_none_or(|gate| session.region.is_cleared(gate));
                Some(Action::new(
                    format!("Travel to {}", location.name),
                    CAMPAIGN_TRAVEL,
                    i64::try_from(index)
                        .expect("the bounded campaign location list fits the action wire"),
                    enabled,
                ))
            })
            .collect()
    }

    fn parse_action(
        &self,
        session: &DescentCampaignSession,
        action: &Action,
    ) -> Result<DescentCampaignMove, String> {
        if action.text.is_some() || action.wants_text {
            return Err("campaign actions do not carry text".to_string());
        }
        if action.turn == CAMPAIGN_TRAVEL {
            let index = usize::try_from(action.arg)
                .map_err(|_| format!("no campaign location #{}", action.arg))?;
            let destination = self
                .map
                .locations
                .get(index)
                .ok_or_else(|| format!("no campaign location #{}", action.arg))?;
            let here = session.current_location();
            if !self
                .map
                .edges_from(&here)
                .iter()
                .any(|edge| edge.to == destination.id)
            {
                return Err(format!(
                    "no campaign road leads from `{here}` to `{}`",
                    destination.id
                ));
            }
            return Ok(DescentCampaignMove::Travel(destination.id.clone()));
        }
        Ok(DescentCampaignMove::Native(parse_native_move(action)?))
    }

    fn record_event(
        &self,
        session: &mut DescentCampaignSession,
        actor: DreggIdentity,
        location: String,
        command: DescentCampaignMove,
        native_receipt: Option<TurnReceipt>,
        region_receipt: Option<TurnReceipt>,
        crowned: bool,
    ) {
        if session.actor.is_none() {
            session.actor = Some(actor.clone());
        }
        let revision = session.revision() + 1;
        let root = event_root(
            session.root,
            revision,
            &actor,
            &location,
            &command,
            native_receipt.as_ref(),
            region_receipt.as_ref(),
            session.active.root(),
            session.active.revision(),
            crowned,
            &session.region,
            &self.map,
        );
        session.root = root;
        session.events.push(DescentCampaignEvent {
            revision,
            actor: actor.clone(),
            location,
            command,
            native_receipt,
            region_receipt,
            post_native_root: session.active.root(),
            post_native_revision: session.active.revision(),
            crowned,
            root,
        });
        session.checkpoint = Some(checkpoint(session, actor));
    }

    fn replay_record(
        &self,
        record: &DescentCampaignRecord,
    ) -> Result<DescentCampaignSession, String> {
        if record.events.len() > MAX_CAMPAIGN_EVENTS {
            return Err(format!(
                "{} events exceeds the campaign journal bound",
                record.events.len()
            ));
        }
        let mut replayed = self.deploy(record.seed)?;
        for (index, expected) in record.events.iter().enumerate() {
            let revision = u64::try_from(index + 1)
                .expect("the fixed campaign journal bound fits the revision wire");
            if expected.revision != revision {
                return Err(format!(
                    "campaign event {revision} has a non-canonical revision"
                ));
            }
            if !valid_actor(&expected.actor) {
                return Err(format!("campaign event {revision} has an invalid actor"));
            }
            if replayed
                .actor
                .as_ref()
                .is_some_and(|actor| actor != &expected.actor)
            {
                return Err(format!(
                    "campaign event {revision} substituted the bound actor"
                ));
            }
            if expected.location != replayed.current_location() {
                return Err(format!(
                    "campaign event {revision} substituted its location"
                ));
            }
            let outcome = self.advance_move(
                &mut replayed,
                expected.command.clone(),
                expected.actor.clone(),
            );
            if let Outcome::Refused(reason) = outcome {
                return Err(format!(
                    "campaign event {revision} refused on replay: {reason}"
                ));
            }
            let actual = replayed
                .events
                .last()
                .expect("a landed replay command records an event");
            if !same_event(actual, expected) {
                return Err(format!(
                    "campaign event {revision} differs from fresh replay: {}",
                    event_difference(actual, expected)
                ));
            }
        }
        // Ordinary campaign events reconstruct the exact native public head. Enrich that head
        // with the record's independently replay-verified shielded operations, then require the
        // ordinary actor/revision/root/state image to remain identical. A private proof can add a
        // consequence; it cannot replace the Descent trajectory it names.
        let enriched_active = self
            .native
            .resume_record(&record.active)
            .map_err(|error| format!("campaign active Descent record refused: {error}"))?;
        if enriched_active.actor() != replayed.active.actor()
            || enriched_active.revision() != replayed.active.revision()
            || enriched_active.root() != replayed.active.root()
            || enriched_active.game().sim() != replayed.active.game().sim()
        {
            return Err(
                "campaign active Descent record does not match its replayed location head"
                    .to_string(),
            );
        }
        replayed.active = enriched_active;
        if replayed.actor != record.actor
            || replayed.root != record.root
            || replayed.checkpoint != record.checkpoint
        {
            return Err("campaign record does not name the exact replayed head".to_string());
        }
        Ok(replayed)
    }

    fn advance_move(
        &self,
        session: &mut DescentCampaignSession,
        command: DescentCampaignMove,
        actor: DreggIdentity,
    ) -> Outcome {
        if session.events.len() >= MAX_CAMPAIGN_EVENTS {
            return Outcome::Refused("campaign journal reached its fixed bound".to_string());
        }
        if !valid_actor(&actor) {
            return Outcome::Refused("the actor identity is empty or overlong".to_string());
        }
        if session.actor.as_ref().is_some_and(|bound| bound != &actor) {
            return Outcome::Refused("this campaign belongs to a different actor".to_string());
        }
        let location = session.current_location();
        match command.clone() {
            DescentCampaignMove::Native(native_move) => {
                if session.region.is_cleared(&location) {
                    return Outcome::Refused(
                        "this location is cleared; choose a real region road".to_string(),
                    );
                }
                let native_action = match action_for_native_move(native_move) {
                    Ok(action) => action,
                    Err(reason) => return Outcome::Refused(reason),
                };
                let (native_receipt, ended) =
                    match self
                        .native
                        .advance(&mut session.active, native_action, actor.clone())
                    {
                        Outcome::Landed { receipt, ended } => (receipt, ended),
                        Outcome::Refused(reason) => return Outcome::Refused(reason),
                    };

                let crowned = ended
                    && session.active.completion().is_some_and(|completion| {
                        completion.actor == actor
                            && completion.crowned
                            && completion.banked_relics.contains(&0)
                    });
                let region_receipt =
                    if crowned {
                        let report = self.native.verify(&session.active);
                        if !report.verified {
                            panic!(
                                "a just-landed native run failed its own exact replay: {}",
                                report.detail
                            );
                        }
                        Some(session.region.clear(&location).unwrap_or_else(|error| {
                            panic!("known campaign location clears: {error}")
                        }))
                    } else {
                        None
                    };
                let returned = region_receipt.as_ref().unwrap_or(&native_receipt).clone();
                self.record_event(
                    session,
                    actor,
                    location,
                    command,
                    Some(native_receipt),
                    region_receipt,
                    crowned,
                );
                Outcome::Landed {
                    receipt: returned,
                    ended: session.cleared_count() == self.map.locations.len(),
                }
            }
            DescentCampaignMove::Travel(destination) => {
                if session.actor.is_none() {
                    return Outcome::Refused(
                        "an unclaimed campaign cannot travel before a crown".to_string(),
                    );
                }
                // Fail before constructing a region turn. RegionCell's driver
                // sequence is part of its executor image, so even a rejected
                // signed turn would make a landed-only restart log incomplete.
                // The real FieldGte predicate still independently re-checks
                // every travel that reaches RegionCell::travel.
                if !session.region.is_cleared(&location) {
                    return Outcome::Refused(
                        "the current location has no replay-verified crown".to_string(),
                    );
                }
                if !self
                    .map
                    .edges_from(&location)
                    .iter()
                    .any(|edge| edge.to == destination)
                {
                    return Outcome::Refused(format!(
                        "no campaign road leads from `{location}` to `{destination}`"
                    ));
                }
                let receipt = match session.region.travel(&destination) {
                    Ok(receipt) => receipt,
                    Err(reason) => return Outcome::Refused(reason),
                };
                session.active = self
                    .open_native(session.seed, &destination)
                    .unwrap_or_else(|error| panic!("known campaign location opens: {error}"));
                self.record_event(
                    session,
                    actor,
                    location,
                    command,
                    None,
                    Some(receipt.clone()),
                    false,
                );
                Outcome::Landed {
                    receipt,
                    ended: false,
                }
            }
        }
    }

    fn verify_exact_record(
        &self,
        session: &DescentCampaignSession,
        record: &DescentCampaignRecord,
    ) -> VerifyReport {
        let turns = record.events.len() + 1;
        if record.seed != session.seed
            || record.actor != session.actor
            || record.root != session.root
            || record.checkpoint != session.checkpoint
            || record.events.len() != session.events.len()
            || !record
                .events
                .iter()
                .zip(&session.events)
                .all(|(left, right)| same_event(left, right))
        {
            return VerifyReport::broken(
                turns,
                "record does not name the exact live campaign head",
            );
        }
        match self.replay_record(record) {
            Ok(_) => {
                let native = self.native.verify_record(&session.active, &record.active);
                if native.verified {
                    VerifyReport::ok(turns)
                } else {
                    VerifyReport::broken(
                        turns,
                        format!("active native Descent record failed: {}", native.detail),
                    )
                }
            }
            Err(reason) => VerifyReport::broken(turns, reason),
        }
    }
}

impl Default for DescentCampaignOffering {
    fn default() -> Self {
        Self::new()
    }
}

impl Offering for DescentCampaignOffering {
    type Session = DescentCampaignSession;

    fn open(&self, cfg: SessionConfig) -> Result<Self::Session, OfferingError> {
        let seed = ((cfg.seed.unwrap_or(1) % 251) + 1) as u8;
        self.deploy(seed).map_err(OfferingError::Deploy)
    }

    fn actions(&self, session: &Self::Session) -> Vec<Action> {
        self.actions_for_session(session)
    }

    fn actions_for(&self, session: &Self::Session, viewer: &DreggIdentity) -> Vec<Action> {
        let mut actions = self.actions_for_session(session);
        if session.actor.as_ref().is_some_and(|actor| actor != viewer) {
            for action in &mut actions {
                action.enabled = false;
            }
        }
        actions
    }

    fn advance(&self, session: &mut Self::Session, input: Action, actor: DreggIdentity) -> Outcome {
        let command = match self.parse_action(session, &input) {
            Ok(command) => command,
            Err(reason) => return Outcome::Refused(reason),
        };
        self.advance_move(session, command, actor)
    }

    fn verify(&self, session: &Self::Session) -> VerifyReport {
        self.verify_exact_record(session, &session.export_record())
    }

    fn render(&self, session: &Self::Session) -> Surface {
        let here = session.current_location();
        let sim = session.active.game().sim();
        let actor = session
            .actor
            .as_ref()
            .map(DreggIdentity::as_str)
            .unwrap_or("unclaimed — the first landed Descent move binds the traveller");
        let mut children = vec![
            ViewNode::Text(format!("traveller: {actor}")),
            ViewNode::Text(format!(
                "{} · {} / {} locations crowned",
                location_name(&self.map, &here),
                session.cleared_count(),
                self.map.locations.len()
            )),
            ViewNode::Text(format!(
                "depth {} · light spent {} · wounds {} · native turn {}",
                sim.depth,
                sim.spent,
                sim.wounds,
                session.active.revision()
            )),
            ViewNode::Text(format!(
                "campaign revision {} · root {}",
                session.revision(),
                short_digest(session.root)
            )),
        ];
        if session.region.is_cleared(&here) {
            children.push(ViewNode::Text(
                "The replay-verified Crown has opened this location's region roads.".to_string(),
            ));
        } else if session.active.completion().is_some() {
            children.push(ViewNode::Text(
                "This expedition settled without the Crown; it did not clear the location."
                    .to_string(),
            ));
        } else {
            children.push(ViewNode::Text(
                "Player-driven Lean-native expedition; no scripted completion is available."
                    .to_string(),
            ));
        }
        #[cfg(feature = "private-preference-operation")]
        if let Some(preference) = session.active.private_preference() {
            children.push(ViewNode::Text(format!(
                "Shielded party choice: {} · receipt {}",
                crate::dungeon::PRIVATE_PREFERENCE_OPTIONS[preference.decision().winner()],
                short_digest(preference.receipt_id()),
            )));
        }
        #[cfg(feature = "private-raid-operation")]
        if let Some(raid) = session.active.private_raid() {
            children.push(ViewNode::Text(format!(
                "Shielded raid assignment accepted · receipt {}",
                short_digest(raid.receipt_id()),
            )));
        }
        #[cfg(feature = "private-fair-shuffle-operation")]
        if let Some(deal) = session.active.private_deal() {
            children.push(ViewNode::Text(format!(
                "Shielded initiative: card {} · receipt {}",
                deal.initiative_card(),
                short_digest(deal.receipt_id()),
            )));
        }
        children.push(ViewNode::Menu {
            items: self
                .actions_for_session(session)
                .into_iter()
                .map(|action| MenuItem {
                    label: action.label,
                    turn: action.turn,
                    arg: action.arg,
                    enabled: action.enabled,
                })
                .collect(),
        });
        Surface(ViewNode::Section {
            title: format!("{} — native Descent campaign", self.map.name),
            tag: "accent".to_string(),
            children,
        })
    }

    fn price(&self, _input: &Action) -> RunCost {
        RunCost::free()
    }

    #[cfg(any(
        feature = "private-preference-operation",
        feature = "private-raid-operation",
        feature = "private-fair-shuffle-operation"
    ))]
    fn binary_operations(&self, session: &Self::Session) -> Vec<BinaryOperationDescriptor> {
        if session.region.is_cleared(&session.current_location()) {
            Vec::new()
        } else {
            self.native.binary_operations(&session.active)
        }
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
        if session.region.is_cleared(&session.current_location()) {
            return Err(BinaryOperationError::Refused(
                "a cleared campaign location accepts no further private operation".to_string(),
            ));
        }
        self.native
            .binary_operation_replay_material(&session.active, name, payload)
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
        if !valid_actor(&actor) {
            return Err(BinaryOperationError::Refused(
                "the campaign operation actor is empty or overlong".to_string(),
            ));
        }
        if session.actor.as_ref().is_some_and(|bound| bound != &actor) {
            return Err(BinaryOperationError::Refused(
                "this campaign belongs to a different actor".to_string(),
            ));
        }
        if session.region.is_cleared(&session.current_location()) {
            return Err(BinaryOperationError::Refused(
                "a cleared campaign location accepts no further private operation".to_string(),
            ));
        }
        self.native
            .invoke_binary_operation(&mut session.active, name, payload, actor)
    }
}

impl RecordVerify for DescentCampaignOffering {
    type Session = DescentCampaignSession;
    type Record = DescentCampaignRecord;

    fn export_record(&self, session: &Self::Session) -> Self::Record {
        session.export_record()
    }

    fn verify_record(&self, session: &Self::Session, record: &Self::Record) -> VerifyReport {
        self.verify_exact_record(session, record)
    }
}

fn parse_native_move(action: &Action) -> Result<NativeDescentMove, String> {
    match (action.turn.as_str(), action.arg) {
        (DELVE, 0) => Ok(NativeDescentMove::Delve),
        (ASCEND, 0) => Ok(NativeDescentMove::Ascend),
        (UNLOCK, way @ 2..=4) => Ok(NativeDescentMove::Unlock {
            way: u64::try_from(way).expect("the matched campaign unlock argument is non-negative"),
        }),
        (SMITE, 0) => Ok(NativeDescentMove::Smite),
        (LUNGE, 0) => Ok(NativeDescentMove::Lunge),
        (LOOT, relic @ 0..=7) => Ok(NativeDescentMove::Loot {
            relic: u64::try_from(relic)
                .expect("the matched campaign relic argument is non-negative"),
        }),
        (FLEE, 0) => Ok(NativeDescentMove::Flee),
        (turn, arg) => Err(format!("`{turn}({arg})` is not a native campaign move")),
    }
}

fn action_for_native_move(command: NativeDescentMove) -> Result<Action, String> {
    let action = match command {
        NativeDescentMove::Delve => Action::new("replay delve", DELVE, 0, true),
        NativeDescentMove::Ascend => Action::new("replay ascend", ASCEND, 0, true),
        NativeDescentMove::Unlock { way } => Action::new(
            "replay unlock",
            UNLOCK,
            i64::try_from(way).map_err(|_| "unlock index exceeds the action wire")?,
            true,
        ),
        NativeDescentMove::Smite => Action::new("replay smite", SMITE, 0, true),
        NativeDescentMove::Lunge => Action::new("replay lunge", LUNGE, 0, true),
        NativeDescentMove::Loot { relic } => Action::new(
            "replay loot",
            LOOT,
            i64::try_from(relic).map_err(|_| "relic index exceeds the action wire")?,
            true,
        ),
        NativeDescentMove::Flee => Action::new("replay flee", FLEE, 0, true),
    };
    Ok(action)
}

fn valid_actor(actor: &DreggIdentity) -> bool {
    !actor.0.is_empty() && actor.0.len() <= MAX_ACTOR_BYTES
}

fn location_seed(seed: u8, location: &str) -> u64 {
    let mut hasher = blake3::Hasher::new_derive_key(LOCATION_SEED_DOMAIN);
    hasher.update(&[seed]);
    hash_string(&mut hasher, location);
    let mut raw = [0u8; 8];
    raw.copy_from_slice(&hasher.finalize().as_bytes()[..8]);
    u64::from_le_bytes(raw)
}

fn genesis_root(map: &RegionMap, seed: u8, native_root: [u8; 32]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(GENESIS_ROOT_DOMAIN);
    hasher.update(&[seed]);
    hash_string(&mut hasher, &map.id);
    hash_string(&mut hasher, &map.start);
    hasher.update(
        &u64::try_from(map.locations.len())
            .expect("the bounded campaign location list fits u64")
            .to_be_bytes(),
    );
    for location in &map.locations {
        hash_string(&mut hasher, &location.id);
        hash_string(&mut hasher, &location.name);
    }
    hasher.update(
        &u64::try_from(map.edges.len())
            .expect("the bounded campaign edge list fits u64")
            .to_be_bytes(),
    );
    for edge in &map.edges {
        hash_string(&mut hasher, &edge.from);
        hash_string(&mut hasher, &edge.to);
        match &edge.gate {
            Some(gate) => {
                hasher.update(&[1]);
                hash_string(&mut hasher, gate);
            }
            None => {
                hasher.update(&[0]);
            }
        }
    }
    hasher.update(&native_root);
    *hasher.finalize().as_bytes()
}

#[allow(clippy::too_many_arguments)]
fn event_root(
    previous: [u8; 32],
    revision: u64,
    actor: &DreggIdentity,
    location: &str,
    command: &DescentCampaignMove,
    native_receipt: Option<&TurnReceipt>,
    region_receipt: Option<&TurnReceipt>,
    native_root: [u8; 32],
    native_revision: u64,
    crowned: bool,
    region: &RegionCell,
    map: &RegionMap,
) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(EVENT_ROOT_DOMAIN);
    hasher.update(&previous);
    hasher.update(&revision.to_be_bytes());
    hash_string(&mut hasher, actor.as_str());
    hash_string(&mut hasher, location);
    hash_command(&mut hasher, command);
    hash_receipt(&mut hasher, native_receipt);
    hash_receipt(&mut hasher, region_receipt);
    hasher.update(&native_root);
    hasher.update(&native_revision.to_be_bytes());
    hasher.update(&[u8::from(crowned)]);
    hash_string(&mut hasher, &region.current_location());
    for location in &map.locations {
        hasher.update(&[u8::from(region.is_cleared(&location.id))]);
    }
    *hasher.finalize().as_bytes()
}

fn hash_command(hasher: &mut blake3::Hasher, command: &DescentCampaignMove) {
    match command {
        DescentCampaignMove::Native(native) => {
            hasher.update(&[0]);
            match native {
                NativeDescentMove::Delve => {
                    hasher.update(&[0]);
                }
                NativeDescentMove::Unlock { way } => {
                    hasher.update(&[1]);
                    hasher.update(&way.to_be_bytes());
                }
                NativeDescentMove::Smite => {
                    hasher.update(&[2]);
                }
                NativeDescentMove::Loot { relic } => {
                    hasher.update(&[3]);
                    hasher.update(&relic.to_be_bytes());
                }
                NativeDescentMove::Flee => {
                    hasher.update(&[4]);
                }
                // A NEW tag, never a renumber: tags 0–4 keep their bytes, so an existing
                // campaign's command hash is unchanged by the arrival of the lunge.
                NativeDescentMove::Lunge => {
                    hasher.update(&[5]);
                }
                // …and tag 6 for the climb, on the same discipline.
                NativeDescentMove::Ascend => {
                    hasher.update(&[6]);
                }
            }
        }
        DescentCampaignMove::Travel(destination) => {
            hasher.update(&[1]);
            hash_string(hasher, destination);
        }
    }
}

fn hash_receipt(hasher: &mut blake3::Hasher, receipt: Option<&TurnReceipt>) {
    match receipt {
        Some(receipt) => {
            hasher.update(&[1]);
            hasher.update(&receipt.receipt_hash());
        }
        None => {
            hasher.update(&[0]);
        }
    }
}

fn checkpoint(session: &DescentCampaignSession, actor: DreggIdentity) -> DescentCampaignCheckpoint {
    DescentCampaignCheckpoint {
        actor,
        revision: session.revision(),
        root: session.root,
        current_location: session.current_location(),
        cleared_locations: session
            .region
            .map()
            .locations
            .iter()
            .filter(|location| session.region.is_cleared(&location.id))
            .map(|location| location.id.clone())
            .collect(),
        active_native_root: session.active.root(),
        active_native_revision: session.active.revision(),
        active_crowned: session
            .active
            .completion()
            .is_some_and(|completion| completion.crowned),
    }
}

fn same_event(left: &DescentCampaignEvent, right: &DescentCampaignEvent) -> bool {
    left.revision == right.revision
        && left.actor == right.actor
        && left.location == right.location
        && left.command == right.command
        && same_receipt(left.native_receipt.as_ref(), right.native_receipt.as_ref())
        && same_receipt(left.region_receipt.as_ref(), right.region_receipt.as_ref())
        && left.post_native_root == right.post_native_root
        && left.post_native_revision == right.post_native_revision
        && left.crowned == right.crowned
        && left.root == right.root
}

fn event_difference(left: &DescentCampaignEvent, right: &DescentCampaignEvent) -> String {
    let mut fields = Vec::new();
    if left.revision != right.revision {
        fields.push("revision");
    }
    if left.actor != right.actor {
        fields.push("actor");
    }
    if left.location != right.location {
        fields.push("location");
    }
    if left.command != right.command {
        fields.push("command");
    }
    if !same_receipt(left.native_receipt.as_ref(), right.native_receipt.as_ref()) {
        fields.push("native receipt");
    }
    if !same_receipt(left.region_receipt.as_ref(), right.region_receipt.as_ref()) {
        fields.push("region receipt");
        if let (Some(left), Some(right)) =
            (left.region_receipt.as_ref(), right.region_receipt.as_ref())
        {
            if left.turn_hash != right.turn_hash {
                fields.push("region.turn_hash");
            }
            if left.forest_hash != right.forest_hash {
                fields.push("region.forest_hash");
            }
            if left.pre_state_hash != right.pre_state_hash {
                fields.push("region.pre_state_hash");
            }
            if left.post_state_hash != right.post_state_hash {
                fields.push("region.post_state_hash");
            }
            if left.timestamp != right.timestamp {
                fields.push("region.timestamp");
            }
            if left.effects_hash != right.effects_hash {
                fields.push("region.effects_hash");
            }
            if left.previous_receipt_hash != right.previous_receipt_hash {
                fields.push("region.previous_receipt_hash");
            }
        }
    }
    if left.post_native_root != right.post_native_root {
        fields.push("native root");
    }
    if left.post_native_revision != right.post_native_revision {
        fields.push("native revision");
    }
    if left.crowned != right.crowned {
        fields.push("crown flag");
    }
    if left.root != right.root {
        fields.push("campaign root");
    }
    fields.join(", ")
}

fn same_receipt(left: Option<&TurnReceipt>, right: Option<&TurnReceipt>) -> bool {
    match (left, right) {
        (Some(left), Some(right)) => left.receipt_hash() == right.receipt_hash(),
        (None, None) => true,
        _ => false,
    }
}

fn hash_string(hasher: &mut blake3::Hasher, value: &str) {
    hasher.update(
        &u64::try_from(value.len())
            .expect("the bounded campaign string fits u64")
            .to_be_bytes(),
    );
    hasher.update(value.as_bytes());
}

fn location_name(map: &RegionMap, location: &str) -> String {
    map.location(location)
        .map(|location| location.name.clone())
        .unwrap_or_else(|| location.to_string())
}

fn short_digest(digest: [u8; 32]) -> String {
    digest[..6]
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}
