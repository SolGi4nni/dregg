//! **The overworld offering** — a player traverses a REGION of universes, the map opening as they
//! honestly clear each dungeon.
//!
//! Where [`crate::dungeon::DungeonOffering`] hosts ONE universe (the Keep) and
//! [`crate::character::AdventurerOffering`] binds a persistent character across runs, this offering
//! is the layer ABOVE both: a [`RegionMap`] of universes joined by travel edges, played on a real
//! dregg [`RegionCell`]. It re-homes `attested-dm`'s PROVEN overworld design (a region of dungeons,
//! travel gated on VERIFIED COMPLETION) off the toy blake3 ledger onto the real spween-dregg
//! executor.
//!
//! ## The teeth are REAL executor teeth (not app bookkeeping)
//!
//! - **Travel is gated on verified completion.** [`OverworldOffering::travel`] fires a real
//!   region-cell turn the executor REFUSES unless the destination's prerequisite is cleared (a
//!   `FieldGte` on a WriteOnce cleared flag — see [`dungeon_on_dregg::overworld`]). The map opens
//!   as you clear it.
//! - **Completion → unlock is a real committed turn.** [`OverworldOffering::play_and_clear`] drives
//!   a location's universe START → WIN on the real substrate, re-verifies the whole playthrough by
//!   replay, and ONLY THEN fires the sanctioned `clear` turn that sets the cleared flag — the
//!   session-level binding of a real, replay-verified WIN to a real committed unlock (the same
//!   `Won + verify + replay` gate attested-dm's `record_completion` used, and the same shape
//!   [`crate::character`] uses to bind a real dungeon outcome to a real character-cell XP turn).
//! - **A forged clear is refused.** A cleared flag written outside the sanctioned method is a real
//!   default-deny executor refusal ([`RegionCell::forge_cleared`]); an UNFINISHED run credits
//!   nothing (the completion gate refuses to clear it).
//!
//! ## Honest scope
//!
//! - "Verified completion" is bound to the unlock at the SESSION level (drive to WIN + replay-verify
//!   → fire the real clear turn). The purist alternative — the region cell gating `clear` on the
//!   dungeon cell's finalized WIN root via a cross-cell `ObservedFieldEquals` (the `multicell`
//!   pattern) — needs region + dungeon cells co-hosted on one executor ledger, a named follow-up.
//! - Region progress is restart-safe through [`OverworldRecord`]: a host may persist the public
//!   record and [`OverworldOffering::resume_record`] only accepts it after exact re-execution.
//!   A durable database implementing that storage policy remains a host concern.
//! - The generic [`crate::Offering`] clear action never auto-plays a dungeon. A caller separately
//!   obtains a [`WinRun`], stages it with [`OverworldOffering::stage_completion`], and the exact
//!   clear action consumes that replay-verified proof. [`OverworldOffering::play_and_clear`] remains
//!   as an explicit legacy/demo convenience, not the common-surface authority path.
//! - A fuller overworld adds branching/converging regions, world events, and shared public regions;
//!   the default generic session is deliberately a per-player traversal.

use deos_view::{MenuItem, ViewNode};
use dregg_app_framework::TurnReceipt;
use dungeon_on_dregg::overworld::{
    RegionCell, RegionMap, WinRun, deepening_ways, play_to_win, reverify_win, universe,
};
use spween_dregg::Driver;

use crate::refusal::belongs_to_another_player;
use crate::{
    Action, DreggIdentity, Offering, OfferingError, Outcome, RecordVerify, RunCost, SessionConfig,
    Surface, VerifyReport,
};

/// Generic-surface travel verb. Its `arg` is the stable index in [`RegionMap::locations`].
pub const OVERWORLD_TRAVEL: &str = "travel";
/// Generic-surface clear verb. It consumes a separately staged verified completion.
pub const OVERWORLD_CLEAR: &str = "clear";
/// Hard bound on one traversal's public replay journal.
pub const MAX_OVERWORLD_EVENTS: usize = 512;

const MAX_ACTOR_BYTES: usize = 512;
const GENESIS_ROOT_DOMAIN: &str = "dregg.overworld.genesis.v1";
const EVENT_ROOT_DOMAIN: &str = "dregg.overworld.event.v1";

/// **A player's live traversal of a region.** Owns the real region cell (the map + its committed
/// cleared flags), the player's identity, the log of region turns (travel + clear receipts, for
/// re-verify), and the cleared dungeons' recorded playthroughs (each re-verified by replay).
pub struct OverworldSession {
    /// `Some` for the compatibility `open(who, cfg)` path; `None` for the generic
    /// Offering path until its first executor-landed region turn.
    opened_for: Option<DreggIdentity>,
    actor: Option<DreggIdentity>,
    region: RegionCell,
    /// The deploy seed of the region cell — [`OverworldOffering::verify`] re-deploys an identical
    /// region cell from it and replays the recorded ops.
    seed: u8,
    events: Vec<OverworldEvent>,
    root: [u8; 32],
    checkpoint: Option<OverworldCheckpoint>,
    staged: Option<StagedCompletion>,
}

/// One exact public overworld command.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OverworldMove {
    /// A sanctioned clear of a location (unlocking the roads gated on it).
    Clear(String),
    /// A gated travel to a destination.
    Travel(String),
}

impl OverworldMove {
    fn hash_into(&self, hasher: &mut blake3::Hasher) {
        match self {
            Self::Clear(location) => {
                hasher.update(&[0]);
                hash_string(hasher, location);
            }
            Self::Travel(destination) => {
                hasher.update(&[1]);
                hash_string(hasher, destination);
            }
        }
    }
}

/// One actor-bound committed region event. A clear carries the exact winning
/// run whose replay authorized it; travel carries no completion.
#[derive(Clone)]
pub struct OverworldEvent {
    pub revision: u64,
    pub actor: DreggIdentity,
    pub command: OverworldMove,
    pub receipt: TurnReceipt,
    pub completion: Option<WinRun>,
    pub root: [u8; 32],
}

impl std::fmt::Debug for OverworldEvent {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("OverworldEvent")
            .field("revision", &self.revision)
            .field("actor", &self.actor)
            .field("command", &self.command)
            .field("receipt_hash", &self.receipt.receipt_hash())
            .field("has_completion", &self.completion.is_some())
            .field("root", &self.root)
            .finish()
    }
}

/// Fully derived restart checkpoint at a committed event boundary.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OverworldCheckpoint {
    pub actor: DreggIdentity,
    pub revision: u64,
    pub root: [u8; 32],
    pub current_location: String,
    pub cleared_locations: Vec<String>,
}

/// A verified but not-yet-consumed dungeon completion. Staging never binds a
/// player and never mutates the region; only the later clear turn does.
#[derive(Clone)]
pub struct StagedCompletion {
    pub actor: DreggIdentity,
    pub location: String,
    pub run: WinRun,
}

impl std::fmt::Debug for StagedCompletion {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("StagedCompletion")
            .field("actor", &self.actor)
            .field("location", &self.location)
            .field("run_id", &self.run.id)
            .field("run_seed", &self.run.seed)
            .finish()
    }
}

/// Public restart record. State, receipts, actor attribution, and completion
/// proofs are re-derived on a fresh region/dungeon executor before acceptance.
#[derive(Clone, Debug)]
pub struct OverworldRecord {
    pub seed: u8,
    pub opened_for: Option<DreggIdentity>,
    pub actor: Option<DreggIdentity>,
    pub events: Vec<OverworldEvent>,
    pub root: [u8; 32],
    pub checkpoint: Option<OverworldCheckpoint>,
    pub staged: Option<StagedCompletion>,
}

impl OverworldSession {
    /// The player traversing this region. Generic sessions have no player until
    /// the first region turn lands; call [`Self::actor`] when unbound is possible.
    pub fn who(&self) -> &DreggIdentity {
        self.actor
            .as_ref()
            .expect("generic overworld session has not landed its first turn")
    }
    /// The bound player, or `None` before the first landed generic action.
    pub fn actor(&self) -> Option<&DreggIdentity> {
        self.actor.as_ref()
    }
    /// The live region cell (for the driven forged-flag leg + introspection).
    pub fn region(&self) -> &RegionCell {
        &self.region
    }
    /// The region topology.
    pub fn map(&self) -> &RegionMap {
        self.region.map()
    }
    /// The location the traveller currently stands in.
    pub fn current_location(&self) -> String {
        self.region.current_location()
    }
    /// Whether location `loc` is cleared.
    pub fn is_cleared(&self, loc: &str) -> bool {
        self.region.is_cleared(loc)
    }
    /// How many dungeons are cleared.
    pub fn cleared_count(&self) -> usize {
        self.region.cleared_count()
    }
    /// Number of committed actor-bound region events.
    pub fn revision(&self) -> u64 {
        self.events.len() as u64
    }
    /// Hash-chain head binding the topology, actor, exact commands, receipts,
    /// and clear proofs.
    pub fn root(&self) -> [u8; 32] {
        self.root
    }
    pub fn events(&self) -> &[OverworldEvent] {
        &self.events
    }
    pub fn checkpoint(&self) -> Option<&OverworldCheckpoint> {
        self.checkpoint.as_ref()
    }
    pub fn staged_completion(&self) -> Option<&StagedCompletion> {
        self.staged.as_ref()
    }
    pub fn export_record(&self) -> OverworldRecord {
        OverworldRecord {
            seed: self.seed,
            opened_for: self.opened_for.clone(),
            actor: self.actor.clone(),
            events: self.events.clone(),
            root: self.root,
            checkpoint: self.checkpoint.clone(),
            staged: self.staged.clone(),
        }
    }
    /// The destinations reachable RIGHT NOW — a `to` for which an edge departs the current location
    /// and whose gate is satisfied by the cleared flags (the map's currently-open roads).
    pub fn available_destinations(&self) -> Vec<String> {
        let map = self.region.map();
        let here = self.current_location();
        map.edges_from(&here)
            .into_iter()
            .filter(|e| match &e.gate {
                None => true,
                Some(prereq) => self.region.is_cleared(prereq),
            })
            .map(|e| e.to.clone())
            .collect()
    }
}

/// **Why a completion was NOT credited** — the completion gate is fail-closed.
#[derive(Debug, Clone)]
pub enum ClearError {
    /// The completion was not attributed to a usable/bound player identity.
    ActorRefused(String),
    /// Generic clear only consumes the dungeon at the traveller's current location.
    NotAtLocation { location: String, current: String },
    /// A staged completion already awaits explicit consumption.
    CompletionAlreadyStaged(String),
    /// The run was deployed under a seed not derived from this player + location.
    WrongPlayerSeed {
        location: String,
        expected: u8,
        got: u8,
    },
    /// The location is not a place in this region.
    UnknownLocation(String),
    /// The run did not reach a WIN — an unfinished dungeon credits nothing.
    NotWon(String),
    /// The run's playthrough failed re-verification by replay — a forged/reordered record.
    ReplayFailed(String),
    /// The region cell refused the sanctioned clear turn (carries the executor reason).
    ClearRefused(String),
    /// The run is a win for a DIFFERENT universe than the location plays — a win for the wrong
    /// dungeon cannot credit this one.
    WrongUniverse {
        /// The location claimed.
        location: String,
        /// The universe the location actually plays.
        expected: String,
        /// The universe the run is actually for.
        got: String,
    },
}

impl std::fmt::Display for ClearError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ClearError::ActorRefused(why) => write!(f, "REFUSED (actor): {why}"),
            ClearError::NotAtLocation { location, current } => write!(
                f,
                "REFUSED: cannot clear `{location}` while standing at `{current}`"
            ),
            ClearError::CompletionAlreadyStaged(location) => write!(
                f,
                "REFUSED: a completion for `{location}` is already staged"
            ),
            ClearError::WrongPlayerSeed {
                location,
                expected,
                got,
            } => write!(
                f,
                "REFUSED: `{location}` run seed {got} is not this player's seed {expected}"
            ),
            ClearError::UnknownLocation(l) => {
                write!(f, "REFUSED: `{l}` is not a place in this region")
            }
            ClearError::NotWon(l) => write!(f, "REFUSED: the run of `{l}` is not won"),
            ClearError::ReplayFailed(l) => write!(f, "REFUSED (re-execution): `{l}` failed replay"),
            ClearError::ClearRefused(why) => write!(f, "REFUSED (executor): {why}"),
            ClearError::WrongUniverse {
                location,
                expected,
                got,
            } => write!(
                f,
                "REFUSED: this run is of `{got}`, not `{expected}` (the universe location `{location}` plays)"
            ),
        }
    }
}

impl std::error::Error for ClearError {}

impl ClearError {
    /// ⚑ **THE PLAYER HALF.** [`Display`](std::fmt::Display) above is written for a log: it SHOUTS
    /// "REFUSED" and, on two variants, names the audience it is shouting at — `"REFUSED (actor): …"`
    /// and `"REFUSED (executor): …"`. Both of those reach a player through
    /// `Outcome::Refused(error.to_string())` on the travel and credit paths, so the second one was
    /// putting the word *executor* on a traveller's screen.
    ///
    /// The inner text of those two is already the sentence to show — [`ClearError::ActorRefused`]
    /// carries [`crate::refusal::belongs_to_another_player`] and [`ClearError::ClearRefused`] carries
    /// the region cell's own refusal — so the fix is to stop wrapping it. Every other variant
    /// describes the traveller's own situation in plain words and passes straight through.
    pub fn player_message(&self) -> String {
        match self {
            ClearError::ActorRefused(why) | ClearError::ClearRefused(why) => why.clone(),
            other => other.to_string(),
        }
    }
}

/// **The overworld offering** — a stateless factory over a [`RegionMap`]. Each [`open`](Self::open)
/// deploys a fresh [`OverworldSession`] (a real region cell) for a player. Additive: the underlying
/// [`crate::dungeon::DungeonOffering`] / [`crate::character::AdventurerOffering`] are untouched; this
/// consumes the crate's universes through the `dungeon_on_dregg::overworld` registry.
pub struct OverworldOffering {
    map: RegionMap,
}

impl OverworldOffering {
    /// An offering over the concrete [`deepening_ways`] region (four universes, hub-and-branch).
    pub fn new() -> Self {
        OverworldOffering {
            map: deepening_ways(),
        }
    }

    /// An offering over an explicit region map.
    pub fn over(map: RegionMap) -> Self {
        OverworldOffering { map }
    }

    /// The region topology this offering serves.
    pub fn map(&self) -> &RegionMap {
        &self.map
    }

    fn open_session(
        &self,
        opened_for: Option<DreggIdentity>,
        cfg: SessionConfig,
    ) -> Result<OverworldSession, OfferingError> {
        if let Some(actor) = &opened_for {
            if !valid_actor(actor) {
                return Err(OfferingError::Deploy(
                    "overworld player identity is empty or overlong".to_string(),
                ));
            }
        }
        if !self.map.is_well_formed() {
            return Err(OfferingError::Deploy(format!(
                "malformed region: {:?}",
                self.map.validate()
            )));
        }
        let seed = ((cfg.seed.unwrap_or(1) % 251) + 1) as u8;
        let region = RegionCell::deploy(&self.map, seed);
        let root = genesis_root(&self.map, seed, opened_for.as_ref());
        Ok(OverworldSession {
            actor: opened_for.clone(),
            opened_for,
            region,
            seed,
            events: Vec::new(),
            root,
            checkpoint: None,
            staged: None,
        })
    }

    /// **Open a traversal for `who`** — deploy a fresh region cell at the config seed, at the
    /// region's start location with nothing cleared.
    pub fn open(
        &self,
        who: DreggIdentity,
        cfg: SessionConfig,
    ) -> Result<OverworldSession, OfferingError> {
        self.open_session(Some(who), cfg)
    }

    /// Deterministic player/location seed a separately played dungeon must use
    /// before its win can be staged for generic clear.
    pub fn completion_seed(&self, actor: &DreggIdentity, location: &str) -> Result<u8, ClearError> {
        if !valid_actor(actor) {
            return Err(ClearError::ActorRefused(
                "identity is empty or overlong".to_string(),
            ));
        }
        if self.map.location(location).is_none() {
            return Err(ClearError::UnknownLocation(location.to_string()));
        }
        Ok(dungeon_seed(actor, location))
    }

    /// Stage a separately obtained winning run for the generic clear action.
    /// This verifies the run immediately but commits no region turn, advances no
    /// revision, and does not bind an otherwise-unbound session.
    pub fn stage_completion(
        &self,
        session: &mut OverworldSession,
        actor: DreggIdentity,
        location: &str,
        run: WinRun,
    ) -> Result<(), ClearError> {
        self.validate_actor(session, &actor)?;
        if let Some(staged) = &session.staged {
            return Err(ClearError::CompletionAlreadyStaged(staged.location.clone()));
        }
        let current = session.current_location();
        if current != location {
            return Err(ClearError::NotAtLocation {
                location: location.to_string(),
                current,
            });
        }
        if session.is_cleared(location) {
            return Err(ClearError::ClearRefused(format!(
                "`{location}` is already cleared"
            )));
        }
        self.validate_completion(&actor, location, &run)?;
        session.staged = Some(StagedCompletion {
            actor,
            location: location.to_string(),
            run,
        });
        Ok(())
    }

    /// Resume an untrusted public record only after exact region/dungeon replay.
    pub fn resume_record(
        &self,
        record: &OverworldRecord,
    ) -> Result<OverworldSession, OfferingError> {
        replay_record(&self.map, record, true).map_err(OfferingError::Deploy)
    }

    fn validate_actor(
        &self,
        session: &OverworldSession,
        actor: &DreggIdentity,
    ) -> Result<(), ClearError> {
        if !valid_actor(actor) {
            return Err(ClearError::ActorRefused(
                "identity is empty or overlong".to_string(),
            ));
        }
        if let Some(bound) = &session.actor {
            if bound != actor {
                // ⚑ NEITHER KEY IS PRINTED — this branch only fires when `bound != actor`, so the
                // reader never needed to tell two 64-char hex strings apart (and could not read
                // either). The shared sentence gives them the ACCOUNT diagnosis instead.
                return Err(ClearError::ActorRefused(belongs_to_another_player(
                    "traversal",
                )));
            }
        }
        Ok(())
    }

    fn validate_completion(
        &self,
        actor: &DreggIdentity,
        loc: &str,
        run: &WinRun,
    ) -> Result<(), ClearError> {
        let expected = self
            .map
            .location(loc)
            .ok_or_else(|| ClearError::UnknownLocation(loc.to_string()))?
            .universe_id
            .clone();
        if run.id != expected {
            return Err(ClearError::WrongUniverse {
                location: loc.to_string(),
                expected,
                got: run.id.clone(),
            });
        }
        if !run.won {
            return Err(ClearError::NotWon(loc.to_string()));
        }
        let expected_seed = dungeon_seed(actor, loc);
        if run.seed != expected_seed {
            return Err(ClearError::WrongPlayerSeed {
                location: loc.to_string(),
                expected: expected_seed,
                got: run.seed,
            });
        }
        if !reverify_win(&run.id, run.seed, &run.playthrough) {
            return Err(ClearError::ReplayFailed(loc.to_string()));
        }
        if !replay_reaches_terminal_win(run) {
            return Err(ClearError::NotWon(loc.to_string()));
        }
        Ok(())
    }

    fn record_landed(
        &self,
        session: &mut OverworldSession,
        actor: DreggIdentity,
        command: OverworldMove,
        receipt: TurnReceipt,
        completion: Option<WinRun>,
    ) {
        if session.actor.is_none() {
            session.actor = Some(actor.clone());
        }
        let revision = session.revision() + 1;
        let root = event_root(
            session.root,
            revision,
            &actor,
            &command,
            &receipt,
            completion.as_ref(),
        );
        session.events.push(OverworldEvent {
            revision,
            actor: actor.clone(),
            command,
            receipt,
            completion,
            root,
        });
        session.root = root;
        session.checkpoint = Some(checkpoint(&session.region, actor, revision, root));
    }

    fn travel_as(
        &self,
        session: &mut OverworldSession,
        dest: &str,
        actor: DreggIdentity,
    ) -> Outcome {
        if let Err(error) = self.validate_actor(session, &actor) {
            return Outcome::Refused(error.player_message());
        }
        if session.events.len() >= MAX_OVERWORLD_EVENTS {
            return Outcome::Refused("overworld journal reached its fixed bound".to_string());
        }
        let here = session.current_location();
        let Some(edge) = self
            .map
            .edges_from(&here)
            .into_iter()
            .find(|edge| edge.to == dest)
        else {
            return Outcome::Refused(format!("no road leads from `{here}` to `{dest}`"));
        };
        // Refuse a visibly disabled road before constructing a signed turn. The
        // region cell repeats this exact predicate when an enabled/forged call
        // reaches it; avoiding a known refusal also keeps the signer nonce out of
        // anti-ghost UI clicks, which is required for byte-exact restart replay.
        if let Some(gate) = &edge.gate {
            if !session.is_cleared(gate) {
                return Outcome::Refused(format!(
                    "road to `{dest}` is locked until `{gate}` is cleared"
                ));
            }
        }
        match session.region.travel(dest) {
            Ok(receipt) => {
                self.record_landed(
                    session,
                    actor,
                    OverworldMove::Travel(dest.to_string()),
                    receipt.clone(),
                    None,
                );
                Outcome::Landed {
                    receipt,
                    ended: false,
                }
            }
            Err(why) => Outcome::Refused(why),
        }
    }

    fn credit_as(
        &self,
        session: &mut OverworldSession,
        loc: &str,
        run: WinRun,
        actor: DreggIdentity,
    ) -> Result<TurnReceipt, ClearError> {
        self.validate_actor(session, &actor)?;
        if session.events.len() >= MAX_OVERWORLD_EVENTS {
            return Err(ClearError::ClearRefused(
                "overworld journal reached its fixed bound".to_string(),
            ));
        }
        self.validate_completion(&actor, loc, &run)?;
        let current = session.current_location();
        if current != loc {
            return Err(ClearError::NotAtLocation {
                location: loc.to_string(),
                current,
            });
        }
        let receipt = session
            .region
            .clear(loc)
            .map_err(ClearError::ClearRefused)?;
        self.record_landed(
            session,
            actor,
            OverworldMove::Clear(loc.to_string()),
            receipt.clone(),
            Some(run),
        );
        Ok(receipt)
    }

    /// **Travel to `dest` — the gated travel turn.** Fires a real region-cell turn: a legal move
    /// (the destination's prerequisite is cleared) commits ([`Outcome::Landed`]); a locked road is a
    /// real executor [`Outcome::Refused`] that commits nothing (anti-ghost). A committed travel is
    /// recorded onto the traversal's chain.
    pub fn travel(&self, session: &mut OverworldSession, dest: &str) -> Outcome {
        let Some(actor) = session.actor.clone() else {
            return Outcome::Refused(
                "unbound generic traversal requires an attributed action".to_string(),
            );
        };
        self.travel_as(session, dest, actor)
    }

    /// **Play the location's universe to a WIN and, iff it genuinely won + re-verifies, CLEAR it.**
    /// Drives the universe START → WIN on the real substrate, re-verifies the whole playthrough by
    /// replay, and only then fires the sanctioned `clear` turn on the region cell (a real committed
    /// unlock). Returns the clear turn's receipt on success, or the precise [`ClearError`]. An
    /// unfinished / forged run credits NOTHING (the completion gate is fail-closed).
    pub fn play_and_clear(
        &self,
        session: &mut OverworldSession,
        loc: &str,
    ) -> Result<TurnReceipt, ClearError> {
        let uni = self
            .map
            .location(loc)
            .ok_or_else(|| ClearError::UnknownLocation(loc.to_string()))?
            .universe_id
            .clone();
        // A deterministic per-(player, location) dungeon seed, so a re-verify re-deploys the
        // identical world-cell (the identity gives the cell identity; the run gives the state).
        let actor = session.actor.clone().ok_or_else(|| {
            ClearError::ActorRefused(
                "unbound generic traversal cannot use the autoplay helper".to_string(),
            )
        })?;
        let seed = dungeon_seed(&actor, loc);
        let run =
            play_to_win(&uni, seed).ok_or_else(|| ClearError::UnknownLocation(loc.to_string()))?;
        self.credit(session, loc, run)
    }

    /// **Credit a location from an already-driven run** — the completion GATE, factored so the
    /// non-vacuous "an unfinished run credits nothing" leg can present a partial run. Fires the
    /// sanctioned `clear` turn IFF the run is a genuine WIN AND re-verifies by replay.
    pub fn credit(
        &self,
        session: &mut OverworldSession,
        loc: &str,
        run: WinRun,
    ) -> Result<TurnReceipt, ClearError> {
        let actor = session.actor.clone().ok_or_else(|| {
            ClearError::ActorRefused(
                "unbound generic traversal requires an attributed clear action".to_string(),
            )
        })?;
        self.credit_as(session, loc, run, actor)
    }

    /// **Re-verify the whole traversal by REPLAY.** Re-deploys a fresh, identically-seeded region
    /// cell and re-drives the recorded op sequence: every committed travel/clear must re-commit in
    /// order (a forged log — e.g. a travel before its prerequisite clear — is REFUSED on the fresh
    /// executor), and the replayed region reproduces exactly the live cleared set + position. Then
    /// every cleared dungeon's playthrough re-verifies by replay against a fresh world-cell. A
    /// forged region op or a forged dungeon record fails.
    pub fn verify(&self, session: &OverworldSession) -> VerifyReport {
        self.verify_record_mode(session, &session.export_record(), false)
    }

    fn actions_for_session(&self, session: &OverworldSession) -> Vec<Action> {
        let here = session.current_location();
        self.map
            .locations
            .iter()
            .enumerate()
            .filter_map(|(index, location)| {
                if location.id == here {
                    let staged = session.staged.as_ref().is_some_and(|staged| {
                        staged.location == here
                            && session
                                .actor
                                .as_ref()
                                .is_none_or(|actor| actor == &staged.actor)
                    });
                    return Some(Action::new(
                        format!("Clear {} with staged completion", location.name),
                        OVERWORLD_CLEAR,
                        i64::try_from(index)
                            .expect("the bounded region map fits the stable action wire"),
                        !session.is_cleared(&here) && staged,
                    ));
                }
                let edge = self
                    .map
                    .edges_from(&here)
                    .into_iter()
                    .find(|edge| edge.to == location.id)?;
                let enabled = edge
                    .gate
                    .as_ref()
                    .is_none_or(|gate| session.is_cleared(gate));
                Some(Action::new(
                    format!("Travel to {}", location.name),
                    OVERWORLD_TRAVEL,
                    i64::try_from(index)
                        .expect("the bounded region map fits the stable action wire"),
                    enabled,
                ))
            })
            .collect()
    }

    fn move_from_action(
        &self,
        session: &OverworldSession,
        action: &Action,
    ) -> Result<OverworldMove, String> {
        if action.text.is_some() || action.wants_text {
            return Err("overworld actions do not carry text".to_string());
        }
        let index = usize::try_from(action.arg)
            .map_err(|_| format!("no location #{} in this region", action.arg))?;
        let location = self
            .map
            .locations
            .get(index)
            .ok_or_else(|| format!("no location #{} in this region", action.arg))?;
        match action.turn.as_str() {
            OVERWORLD_CLEAR if location.id == session.current_location() => {
                Ok(OverworldMove::Clear(location.id.clone()))
            }
            OVERWORLD_CLEAR => Err(format!(
                "cannot clear `{}` while standing at `{}`",
                location.id,
                session.current_location()
            )),
            OVERWORLD_TRAVEL
                if self
                    .map
                    .edges_from(&session.current_location())
                    .iter()
                    .any(|edge| edge.to == location.id) =>
            {
                Ok(OverworldMove::Travel(location.id.clone()))
            }
            OVERWORLD_TRAVEL => Err(format!(
                "no road leads from `{}` to `{}`",
                session.current_location(),
                location.id
            )),
            other => Err(format!("`{other}` is not an overworld turn")),
        }
    }

    fn verify_exact_record(
        &self,
        session: &OverworldSession,
        record: &OverworldRecord,
    ) -> VerifyReport {
        self.verify_record_mode(session, record, true)
    }

    fn verify_record_mode(
        &self,
        session: &OverworldSession,
        record: &OverworldRecord,
        exact_receipts: bool,
    ) -> VerifyReport {
        let turns = verified_turns(record);
        if record.seed != session.seed
            || record.opened_for != session.opened_for
            || record.actor != session.actor
            || record.events.len() != session.events.len()
            || record.root != session.root
            || record.checkpoint != session.checkpoint
            || staged_digest(record.staged.as_ref()) != staged_digest(session.staged.as_ref())
        {
            return VerifyReport::broken(
                turns,
                "record does not name the exact live traversal head",
            );
        }
        match replay_record(&self.map, record, exact_receipts) {
            Ok(_) => VerifyReport::ok(turns),
            Err(reason) => VerifyReport::broken(turns, reason),
        }
    }
}

impl Offering for OverworldOffering {
    type Session = OverworldSession;

    fn open(&self, cfg: SessionConfig) -> Result<Self::Session, OfferingError> {
        self.open_session(None, cfg)
    }

    fn actions(&self, session: &Self::Session) -> Vec<Action> {
        self.actions_for_session(session)
    }

    fn actions_for(&self, session: &Self::Session, viewer: &DreggIdentity) -> Vec<Action> {
        let mut actions = self.actions_for_session(session);
        let attributed = session
            .actor
            .as_ref()
            .or_else(|| session.staged.as_ref().map(|staged| &staged.actor));
        if attributed.is_some_and(|actor| actor != viewer) {
            for action in &mut actions {
                action.enabled = false;
            }
        }
        actions
    }

    fn advance(&self, session: &mut Self::Session, input: Action, actor: DreggIdentity) -> Outcome {
        if !valid_actor(&actor) {
            return Outcome::Refused("the actor identity is empty or overlong".to_string());
        }
        if let Some(bound) = &session.actor {
            if bound != &actor {
                // Same condition, same sentence as `validate_actor` above — the sibling that used to
                // carry its own copy of the two-hex wording.
                return Outcome::Refused(belongs_to_another_player("traversal"));
            }
        }
        let command = match self.move_from_action(session, &input) {
            Ok(command) => command,
            Err(reason) => return Outcome::Refused(reason),
        };
        match command {
            OverworldMove::Travel(destination) => self.travel_as(session, &destination, actor),
            OverworldMove::Clear(location) => {
                let Some(staged) = session.staged.clone() else {
                    return Outcome::Refused(
                        "clear requires a separately staged, replay-verified winning run"
                            .to_string(),
                    );
                };
                if staged.actor != actor || staged.location != location {
                    return Outcome::Refused(
                        "the staged completion belongs to a different player or location"
                            .to_string(),
                    );
                }
                match self.credit_as(session, &location, staged.run, actor) {
                    Ok(receipt) => {
                        session.staged = None;
                        Outcome::Landed {
                            receipt,
                            ended: session.cleared_count() == self.map.locations.len(),
                        }
                    }
                    Err(error) => Outcome::Refused(error.player_message()),
                }
            }
        }
    }

    fn verify(&self, session: &Self::Session) -> VerifyReport {
        self.verify_exact_record(session, &session.export_record())
    }

    fn render(&self, session: &Self::Session) -> Surface {
        let here = session.current_location();
        let actor = session
            .actor
            .as_ref()
            .map(|actor| actor.as_str())
            .unwrap_or("unclaimed · the first landed region turn binds the traveller");
        let mut children = vec![
            ViewNode::Text(format!("traveller: {actor}")),
            ViewNode::Text(format!("you stand at {here}")),
            ViewNode::Text(format!(
                "{} / {} locations cleared · revision {} · root {}",
                session.cleared_count(),
                self.map.locations.len(),
                session.revision(),
                short_digest(session.root)
            )),
        ];
        if let Some(staged) = &session.staged {
            children.push(ViewNode::Text(format!(
                "verified completion staged for {} by {}",
                staged.location,
                staged.actor.as_str()
            )));
        } else if !session.is_cleared(&here) {
            children.push(ViewNode::Text(
                "play this location separately and stage its verified winning run to clear it"
                    .to_string(),
            ));
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
                    wants_text: action.wants_text,
                })
                .collect(),
        });
        Surface(ViewNode::Section {
            title: format!("{} · per-player overworld", self.map.name),
            tag: "accent".to_string(),
            children,
        })
    }

    fn price(&self, _input: &Action) -> RunCost {
        RunCost::free()
    }
}

impl RecordVerify for OverworldOffering {
    type Session = OverworldSession;
    type Record = OverworldRecord;

    fn export_record(&self, session: &Self::Session) -> Self::Record {
        session.export_record()
    }

    fn verify_record(&self, session: &Self::Session, record: &Self::Record) -> VerifyReport {
        self.verify_exact_record(session, record)
    }
}

fn replay_record(
    map: &RegionMap,
    record: &OverworldRecord,
    exact_receipts: bool,
) -> Result<OverworldSession, String> {
    if record.events.len() > MAX_OVERWORLD_EVENTS {
        return Err(format!(
            "{} events exceeds the overworld journal bound",
            record.events.len()
        ));
    }
    if let Some(opened_for) = &record.opened_for {
        if !valid_actor(opened_for) {
            return Err("record has an invalid pre-bound player".to_string());
        }
    }
    let region = RegionCell::deploy(map, record.seed);
    let mut root = genesis_root(map, record.seed, record.opened_for.as_ref());
    let mut actor = record.opened_for.clone();
    let mut derived_checkpoint = None;
    let offering = OverworldOffering::over(map.clone());

    for (index, expected) in record.events.iter().enumerate() {
        let revision = (index + 1) as u64;
        if expected.revision != revision {
            return Err(format!("event {revision} has a non-canonical revision"));
        }
        if !valid_actor(&expected.actor) {
            return Err(format!("event {revision} has an invalid actor"));
        }
        match &actor {
            None => actor = Some(expected.actor.clone()),
            Some(bound) if bound != &expected.actor => {
                return Err(format!("event {revision} substituted the bound player"));
            }
            Some(_) => {}
        }

        let actual = match (&expected.command, &expected.completion) {
            (OverworldMove::Travel(destination), None) => {
                let here = region.current_location();
                if !map
                    .edges_from(&here)
                    .iter()
                    .any(|edge| edge.to == *destination)
                {
                    return Err(format!(
                        "event {revision} travels a nonexistent road {here}->{destination}"
                    ));
                }
                region.travel(destination)
            }
            (OverworldMove::Travel(_), Some(_)) => {
                return Err(format!(
                    "travel event {revision} carries a dungeon completion"
                ));
            }
            (OverworldMove::Clear(location), Some(run)) => {
                let current = region.current_location();
                if current != *location {
                    return Err(format!(
                        "clear event {revision} targets `{location}` while at `{current}`"
                    ));
                }
                offering
                    .validate_completion(&expected.actor, location, run)
                    .map_err(|error| format!("clear event {revision}: {error}"))?;
                region.clear(location)
            }
            (OverworldMove::Clear(_), None) => {
                return Err(format!("clear event {revision} has no winning run"));
            }
        }
        .map_err(|why| format!("event {revision} refused on replay: {why}"))?;

        if exact_receipts
            && (actual.turn_hash != expected.receipt.turn_hash
                || actual.receipt_hash() != expected.receipt.receipt_hash()
                || actual.executor_signature != expected.receipt.executor_signature)
        {
            return Err(format!(
                "event {revision} receipt did not replay exactly (turn_hash={}, receipt_hash={}, executor_signature={})",
                actual.turn_hash == expected.receipt.turn_hash,
                actual.receipt_hash() == expected.receipt.receipt_hash(),
                actual.executor_signature == expected.receipt.executor_signature,
            ));
        }
        let derived_root = event_root(
            root,
            revision,
            &expected.actor,
            &expected.command,
            &expected.receipt,
            expected.completion.as_ref(),
        );
        if derived_root != expected.root {
            return Err(format!("event {revision} journal root does not recompute"));
        }
        root = derived_root;
        derived_checkpoint = Some(checkpoint(&region, expected.actor.clone(), revision, root));
    }

    if let Some(staged) = &record.staged {
        if !valid_actor(&staged.actor) {
            return Err("staged completion has an invalid actor".to_string());
        }
        if actor.as_ref().is_some_and(|bound| bound != &staged.actor) {
            return Err("staged completion substitutes the bound player".to_string());
        }
        let current = region.current_location();
        if current != staged.location {
            return Err("staged completion is not for the current location".to_string());
        }
        if region.is_cleared(&staged.location) {
            return Err("staged completion targets an already-cleared location".to_string());
        }
        offering
            .validate_completion(&staged.actor, &staged.location, &staged.run)
            .map_err(|error| format!("staged completion: {error}"))?;
    }

    if actor != record.actor || root != record.root || derived_checkpoint != record.checkpoint {
        return Err("record summary/checkpoint differs from replay".to_string());
    }
    Ok(OverworldSession {
        opened_for: record.opened_for.clone(),
        actor,
        region,
        seed: record.seed,
        events: record.events.clone(),
        root,
        checkpoint: derived_checkpoint,
        staged: record.staged.clone(),
    })
}

fn valid_actor(actor: &DreggIdentity) -> bool {
    !actor.as_str().is_empty() && actor.as_str().len() <= MAX_ACTOR_BYTES
}

/// `WinRun::won` is transmitted metadata, not authority. Re-drive the exact
/// recorded choices and ask the runtime whether the terminal passage was
/// actually reached, closing the "partial replay + flipped won bit" seam.
fn replay_reaches_terminal_win(run: &WinRun) -> bool {
    let Some(universe) = universe(&run.id) else {
        return false;
    };
    let scene = (universe.scene)();
    let Ok(mut driver) = Driver::start((universe.deploy)(run.seed), &scene) else {
        return false;
    };
    for step in &run.playthrough.steps {
        let landed = match step.decision_commitment {
            Some(commitment) => driver.advance_certified(step.choice_index, commitment),
            None => driver.advance(step.choice_index),
        };
        if landed.is_err() {
            return false;
        }
    }
    driver.is_ended()
}

fn genesis_root(map: &RegionMap, seed: u8, opened_for: Option<&DreggIdentity>) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(GENESIS_ROOT_DOMAIN);
    hasher.update(&[seed]);
    hash_string(&mut hasher, &map.id);
    hash_string(&mut hasher, &map.name);
    hash_string(&mut hasher, &map.start);
    hasher.update(&(map.locations.len() as u64).to_be_bytes());
    for location in &map.locations {
        hash_string(&mut hasher, &location.id);
        hash_string(&mut hasher, &location.name);
        hash_string(&mut hasher, &location.universe_id);
    }
    hasher.update(&(map.edges.len() as u64).to_be_bytes());
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
    match opened_for {
        Some(actor) => {
            hasher.update(&[1]);
            hash_string(&mut hasher, actor.as_str());
        }
        None => {
            hasher.update(&[0]);
        }
    }
    *hasher.finalize().as_bytes()
}

fn event_root(
    previous: [u8; 32],
    revision: u64,
    actor: &DreggIdentity,
    command: &OverworldMove,
    receipt: &TurnReceipt,
    completion: Option<&WinRun>,
) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(EVENT_ROOT_DOMAIN);
    hasher.update(&previous);
    hasher.update(&revision.to_be_bytes());
    hash_string(&mut hasher, actor.as_str());
    command.hash_into(&mut hasher);
    hash_receipt(&mut hasher, receipt);
    match completion {
        Some(run) => {
            hasher.update(&[1]);
            hash_win_run(&mut hasher, run);
        }
        None => {
            hasher.update(&[0]);
        }
    }
    *hasher.finalize().as_bytes()
}

fn checkpoint(
    region: &RegionCell,
    actor: DreggIdentity,
    revision: u64,
    root: [u8; 32],
) -> OverworldCheckpoint {
    OverworldCheckpoint {
        actor,
        revision,
        root,
        current_location: region.current_location(),
        cleared_locations: region
            .map()
            .locations
            .iter()
            .filter(|location| region.is_cleared(&location.id))
            .map(|location| location.id.clone())
            .collect(),
    }
}

fn staged_digest(staged: Option<&StagedCompletion>) -> Option<[u8; 32]> {
    staged.map(|staged| {
        let mut hasher = blake3::Hasher::new_derive_key("dregg.overworld.staged.v1");
        hash_string(&mut hasher, staged.actor.as_str());
        hash_string(&mut hasher, &staged.location);
        hash_win_run(&mut hasher, &staged.run);
        *hasher.finalize().as_bytes()
    })
}

fn hash_win_run(hasher: &mut blake3::Hasher, run: &WinRun) {
    hash_string(hasher, &run.id);
    hasher.update(&[run.seed, u8::from(run.won)]);
    hash_receipt(hasher, &run.playthrough.genesis);
    hash_u64s(hasher, &run.playthrough.genesis_state);
    hasher.update(&(run.playthrough.steps.len() as u64).to_be_bytes());
    for step in &run.playthrough.steps {
        hash_string(hasher, &step.passage);
        hasher.update(&(step.choice_index as u64).to_be_bytes());
        hash_receipt(hasher, &step.receipt);
        hash_u64s(hasher, &step.state);
        match step.decision_commitment {
            Some(commitment) => {
                hasher.update(&[1]);
                hasher.update(&commitment);
            }
            None => {
                hasher.update(&[0]);
            }
        }
    }
}

fn hash_receipt(hasher: &mut blake3::Hasher, receipt: &TurnReceipt) {
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
}

fn hash_u64s(hasher: &mut blake3::Hasher, values: &[u64]) {
    hasher.update(&(values.len() as u64).to_be_bytes());
    for value in values {
        hasher.update(&value.to_be_bytes());
    }
}

fn hash_string(hasher: &mut blake3::Hasher, value: &str) {
    hasher.update(&(value.len() as u64).to_be_bytes());
    hasher.update(value.as_bytes());
}

fn verified_turns(record: &OverworldRecord) -> usize {
    let cleared_turns: usize = record
        .events
        .iter()
        .filter_map(|event| event.completion.as_ref())
        .map(|run| run.playthrough.receipts().len())
        .sum();
    let staged_turns = record
        .staged
        .as_ref()
        .map_or(0, |staged| staged.run.playthrough.receipts().len());
    record.events.len() + cleared_turns + staged_turns
}

fn short_digest(digest: [u8; 32]) -> String {
    digest[..6]
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

impl Default for OverworldOffering {
    fn default() -> Self {
        OverworldOffering::new()
    }
}

/// Re-export the partial-run helper so a frontend/test can present an unfinished run to the
/// fail-closed completion gate (the non-vacuous "credits nothing" leg).
pub use dungeon_on_dregg::overworld::play_partial as play_partial_run;

/// A deterministic per-(player, location) dungeon deploy seed in `1..=251`.
fn dungeon_seed(who: &DreggIdentity, loc: &str) -> u8 {
    let mut h = blake3::Hasher::new();
    h.update(who.as_str().as_bytes());
    h.update(b"/");
    h.update(loc.as_bytes());
    (h.finalize().as_bytes()[0] % 251) + 1
}

#[cfg(test)]
mod tests {
    use super::*;

    fn player() -> DreggIdentity {
        DreggIdentity("player-overworld-key".to_string())
    }

    /// THE FULL DRIVEN TRAVERSAL: travel to a locked dungeon is REFUSED until its prerequisite is
    /// verified-cleared; clearing a dungeon (a real, replay-verified WIN) unlocks the next on a real
    /// turn; a forged cleared flag is refused; an unfinished run credits nothing; the whole
    /// traversal re-verifies.
    #[test]
    fn the_map_opens_as_you_honestly_clear_it() {
        let off = OverworldOffering::new();
        let mut s = off
            .open(player(), SessionConfig::with_seed(11))
            .expect("open the region");
        assert_eq!(s.current_location(), "keep", "start at the hub");
        assert_eq!(s.cleared_count(), 0);

        // LOCKED: travel to the vault before clearing the keep is a real executor refusal.
        let locked = off.travel(&mut s, "vault");
        assert!(
            !locked.landed(),
            "travel to a locked dungeon is refused, got {locked:?}"
        );
        assert_eq!(s.current_location(), "keep", "anti-ghost: did not move");

        // FORGED FLAG: writing the keep's cleared flag under a non-sanctioned method is refused.
        let forged = s.region().forge_cleared("keep");
        assert!(
            forged.is_err(),
            "a forged cleared flag is refused, got {forged:?}"
        );
        assert!(!s.is_cleared("keep"), "anti-ghost: keep still not cleared");

        // UNFINISHED RUN CREDITS NOTHING: a partial (not-won) keep run is refused by the gate.
        let partial =
            play_partial_run("keep", dungeon_seed(s.who(), "keep"), 2).expect("partial run");
        assert!(!partial.won);
        let refused = off.credit(&mut s, "keep", partial);
        assert!(
            matches!(refused, Err(ClearError::NotWon(_))),
            "an unfinished run credits nothing, got {refused:?}"
        );
        assert!(!s.is_cleared("keep"), "anti-ghost: still not cleared");

        // CLEAR (a genuine, replay-verified WIN) → unlock on a real committed turn.
        off.play_and_clear(&mut s, "keep")
            .expect("a genuine win clears the keep");
        assert!(s.is_cleared("keep"));

        // NON-VACUOUS: the SAME travel that was refused now commits.
        let now = off.travel(&mut s, "vault");
        assert!(
            now.landed(),
            "clearing the keep opens the road to the vault, got {now:?}"
        );
        assert_eq!(s.current_location(), "vault");

        // The deeper road stays sealed until the vault is cleared.
        let deep_locked = off.travel(&mut s, "crypt");
        assert!(
            !deep_locked.landed(),
            "the crypt stays sealed until the vault is cleared"
        );

        // Clear the vault → the deep road to the crypt opens; travel and clear it.
        off.play_and_clear(&mut s, "vault")
            .expect("clear the vault");
        assert!(
            off.travel(&mut s, "crypt").landed(),
            "the vault opens the way to the crypt"
        );
        assert_eq!(s.current_location(), "crypt");
        off.play_and_clear(&mut s, "crypt")
            .expect("clear the crypt");

        // Walk home along the open return roads (crypt ▸ vault ▸ keep), then take the keep's other
        // branch to the bazaar (opened when the keep cleared) and clear it — a full travelled sweep.
        assert!(
            off.travel(&mut s, "vault").landed(),
            "open return road crypt → vault"
        );
        assert!(
            off.travel(&mut s, "keep").landed(),
            "open return road vault → keep"
        );
        assert!(
            off.travel(&mut s, "bazaar").landed(),
            "the keep opened the bazaar branch"
        );
        assert_eq!(s.current_location(), "bazaar");
        off.play_and_clear(&mut s, "bazaar")
            .expect("clear the bazaar branch");
        assert_eq!(
            s.cleared_count(),
            4,
            "all four dungeons cleared by travelled, verified wins"
        );

        // THE WHOLE TRAVERSAL RE-VERIFIES.
        let report = off.verify(&s);
        assert!(
            report.verified,
            "the whole traversal re-verifies: {}",
            report.detail
        );
        assert!(report.turns > 0);
    }

    /// A win for the WRONG universe cannot clear a location: [`OverworldOffering::credit`] binds a
    /// location to its OWN universe id, so a GENUINE, replay-verified keep WIN offered to credit the
    /// vault is REFUSED with `WrongUniverse` — you cannot clear the vault by winning the keep. The
    /// non-vacuous identity tooth (the same keep run DOES credit the keep).
    #[test]
    fn a_win_for_the_wrong_universe_cannot_clear_a_location() {
        let off = OverworldOffering::new();
        let mut s = off
            .open(player(), SessionConfig::with_seed(5))
            .expect("open");

        let keep_run = play_to_win("keep", dungeon_seed(s.who(), "keep")).expect("keep run");
        assert!(keep_run.won);

        // Offered to credit the VAULT: refused — the run is of `keep`, the vault plays `vault`.
        let refused = off.credit(&mut s, "vault", keep_run.clone());
        assert!(
            matches!(&refused, Err(ClearError::WrongUniverse { expected, got, .. }) if expected == "vault" && got == "keep"),
            "a keep win cannot credit the vault, got {refused:?}"
        );
        assert!(
            !s.is_cleared("vault"),
            "anti-ghost: the vault is not cleared"
        );

        // The very same keep run DOES legitimately credit the keep (non-vacuous).
        off.credit(&mut s, "keep", keep_run)
            .expect("the keep run credits the keep");
        assert!(s.is_cleared("keep"));
    }
}
