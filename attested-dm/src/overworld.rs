//! # overworld — the CONNECTIVE layer: N standalone dungeons become ONE navigable REGION.
//!
//! Each bundled adventure ([`crate::sunken_vault`], [`crate::bramble_keep`],
//! [`crate::starfall_spire`], [`crate::deepdark_mine`], [`crate::venom_deep`]) is an
//! independently-verifiable [`crate::GameSession`]: the AI narrates, the world resolves, and a
//! stranger re-verifies the whole chain ([`crate::GameSession::verify`] + `verify_replay`). This
//! module is the layer ABOVE them — a [`Region`] of named [`Location`]s (each a dungeon) joined by
//! travel [`Edge`]s, so the platform is *a world you move through*, not N separate games.
//!
//! ## Completion is HONEST + verification-gated — you cannot forge your way across the map
//!
//! Progress is a [`RegionProgress`]: which locations are COMPLETED, and where the traveller stands.
//! A location is credited complete ONLY through [`RegionProgress::record_completion`], which
//! **re-verifies the whole finished session before crediting it**:
//!
//! 1. the session is a genuine session for THAT location's game — its map fingerprint
//!    ([`crate::savegame`]) equals the location's declared game (you cannot clear the gated
//!    [`crate::venom_deep`] by presenting a win for the easy [`crate::sunken_vault`]);
//! 2. the session is actually [`GameStatus::Won`] (an unfinished run is refused);
//! 3. the chain passes [`crate::GameSession::verify`] (integrity — untampered history) AND
//!    [`crate::GameSession::verify_replay`] (re-execution — every recorded effect is the
//!    rule-correct resolution of its bound action).
//!
//! Only then is the location added to [`RegionProgress::completed`]. A forged, tampered, or
//! unfinished session is REFUSED with a legible [`CompletionError`] — progress cannot be minted
//! from prose or from an incomplete run.
//!
//! ## Travel is gated on verified completion
//!
//! An [`Edge`] may be `gate`d on completing a prerequisite location. [`RegionProgress::travel`]
//! admits a move only along an edge whose gate is satisfied by the current (verified) progress; a
//! locked road is refused ([`TravelError::Locked`]). So the map OPENS as you honestly clear its
//! dungeons — the deep places stay sealed until you have earned the way.
//!
//! ## Honest scope — a first slice
//!
//! This is single-player LOCAL progress (a serializable [`RegionProgress`], persisted like a
//! [`crate::SaveGame`]). A fuller overworld persists progress server-side per identity, and folds
//! each location's verified head into a region-level commitment; that is the named extension. What
//! is REAL here: the per-dungeon verification is the SAME independent chain check each game already
//! ships, and a location is credited ONLY on a re-verified `Won` chain — travel is
//! verified-completion-gated, not merely UI-gated.

use std::collections::BTreeSet;

use serde::{Deserialize, Serialize};

use crate::game::{GameStatus, GameWorld, ReplayMismatch};
use crate::{GameSession, LedgerBreak};

/// **The five bundled games, by stable id → world constructor.** A [`Location`] references one of
/// these by its `game_id`; this is the single place the region binds an id to a real
/// [`GameWorld`]. The ids match the dungeon-service registry (`sunken-vault`, `bramble-keep`,
/// `starfall-spire`, `deepdark-mine`) plus `venom-deep` (wired into the region model). An unknown
/// id yields `None` — a region referencing one is flagged by [`Region::validate`].
pub fn game_ctor(game_id: &str) -> Option<fn() -> GameWorld> {
    match game_id {
        "sunken-vault" => Some(crate::sunken_vault),
        "bramble-keep" => Some(crate::bramble_keep),
        "starfall-spire" => Some(crate::starfall_spire),
        "deepdark-mine" => Some(crate::deepdark_mine),
        "venom-deep" => Some(crate::venom_deep),
        _ => None,
    }
}

/// **A place on the region map — one dungeon.** Its stable `id`, a display `name` + `blurb`, and
/// the `game_id` of the [`GameWorld`] it plays ([`game_ctor`]). Clearing this location means
/// finishing (and re-verifying) a `Won` session for that game.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Location {
    /// The location's stable id (the node id on the map, and the key in [`RegionProgress::completed`]).
    pub id: String,
    /// The location's display name.
    pub name: String,
    /// A one-line description for the map.
    pub blurb: String,
    /// The id of the game played here ([`game_ctor`]).
    pub game_id: String,
}

impl Location {
    /// A location builder.
    pub fn new(
        id: impl Into<String>,
        name: impl Into<String>,
        blurb: impl Into<String>,
        game_id: impl Into<String>,
    ) -> Location {
        Location {
            id: id.into(),
            name: name.into(),
            blurb: blurb.into(),
            game_id: game_id.into(),
        }
    }
}

/// **A directed travel road between two locations.** An edge from `from` to `to`, optionally
/// `gate`d on COMPLETING a prerequisite location: while `gate` is `Some(prereq)` and `prereq` is
/// not yet in [`RegionProgress::completed`], the road is barred ([`TravelError::Locked`]). `None`
/// is an always-open road. Roads are directed; a region wires return roads explicitly.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Edge {
    /// The location this road departs from.
    pub from: String,
    /// The location this road arrives at.
    pub to: String,
    /// The prerequisite LOCATION id that must be completed to travel this road, or `None` for an
    /// always-open road.
    pub gate: Option<String>,
}

impl Edge {
    /// An always-open road `from` → `to`.
    pub fn open(from: impl Into<String>, to: impl Into<String>) -> Edge {
        Edge {
            from: from.into(),
            to: to.into(),
            gate: None,
        }
    }

    /// A road `from` → `to` barred until location `prereq` is completed.
    pub fn gated(
        from: impl Into<String>,
        to: impl Into<String>,
        prereq: impl Into<String>,
    ) -> Edge {
        Edge {
            from: from.into(),
            to: to.into(),
            gate: Some(prereq.into()),
        }
    }
}

/// **A named region — the connective world.** Locations (dungeons) joined by travel edges, opened
/// at `start`. A region is pure ruleset data; the live traversal is a [`RegionProgress`].
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Region {
    /// The region's stable id.
    pub id: String,
    /// The region's display name.
    pub name: String,
    /// A one-line description of the world.
    pub blurb: String,
    /// The locations (dungeons) on the map.
    pub locations: Vec<Location>,
    /// The travel roads between locations.
    pub edges: Vec<Edge>,
    /// The starting location id (where a fresh traveller stands).
    pub start: String,
}

impl Region {
    /// The location with `id`, if any.
    pub fn location(&self, id: &str) -> Option<&Location> {
        self.locations.iter().find(|l| l.id == id)
    }

    /// Whether `id` names a known location.
    pub fn has_location(&self, id: &str) -> bool {
        self.locations.iter().any(|l| l.id == id)
    }

    /// The edges departing `from`.
    pub fn edges_from<'a>(&'a self, from: &str) -> Vec<&'a Edge> {
        self.edges.iter().filter(|e| e.from == from).collect()
    }

    /// **Well-formedness flaws, if any** (empty = well-formed). Checks that every location id is
    /// unique and its `game_id` resolves ([`game_ctor`]); that `start` and every edge's `from` /
    /// `to` name a known location; and that every edge `gate` names a known location. A demo
    /// service (or an author) runs this before mounting a region.
    pub fn validate(&self) -> Vec<RegionFlaw> {
        let mut flaws = Vec::new();
        let mut seen = BTreeSet::new();
        for loc in &self.locations {
            if !seen.insert(loc.id.clone()) {
                flaws.push(RegionFlaw::DuplicateLocation(loc.id.clone()));
            }
            if game_ctor(&loc.game_id).is_none() {
                flaws.push(RegionFlaw::UnknownGame {
                    location: loc.id.clone(),
                    game_id: loc.game_id.clone(),
                });
            }
        }
        if !self.has_location(&self.start) {
            flaws.push(RegionFlaw::UnknownStart(self.start.clone()));
        }
        for edge in &self.edges {
            if !self.has_location(&edge.from) {
                flaws.push(RegionFlaw::EdgeToUnknown {
                    from: edge.from.clone(),
                    to: edge.to.clone(),
                    which: edge.from.clone(),
                });
            }
            if !self.has_location(&edge.to) {
                flaws.push(RegionFlaw::EdgeToUnknown {
                    from: edge.from.clone(),
                    to: edge.to.clone(),
                    which: edge.to.clone(),
                });
            }
            if let Some(prereq) = &edge.gate {
                if !self.has_location(prereq) {
                    flaws.push(RegionFlaw::GateToUnknown {
                        from: edge.from.clone(),
                        to: edge.to.clone(),
                        prereq: prereq.clone(),
                    });
                }
            }
        }
        flaws
    }

    /// Whether the region is well-formed (no [`Region::validate`] flaws).
    pub fn is_well_formed(&self) -> bool {
        self.validate().is_empty()
    }
}

/// A way a [`Region`] is malformed — [`Region::validate`] returns all of them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RegionFlaw {
    /// Two locations share an id.
    DuplicateLocation(String),
    /// A location's `game_id` does not resolve to a bundled game ([`game_ctor`]).
    UnknownGame {
        /// The offending location.
        location: String,
        /// The unresolvable game id.
        game_id: String,
    },
    /// `start` does not name a known location.
    UnknownStart(String),
    /// An edge endpoint (`which`) is not a known location.
    EdgeToUnknown {
        /// The edge's declared `from`.
        from: String,
        /// The edge's declared `to`.
        to: String,
        /// The endpoint (`from` or `to`) that is unknown.
        which: String,
    },
    /// An edge's gate names a prerequisite location that does not exist.
    GateToUnknown {
        /// The edge's `from`.
        from: String,
        /// The edge's `to`.
        to: String,
        /// The unknown prerequisite.
        prereq: String,
    },
}

impl std::fmt::Display for RegionFlaw {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RegionFlaw::DuplicateLocation(id) => write!(f, "duplicate location id `{id}`"),
            RegionFlaw::UnknownGame { location, game_id } => {
                write!(
                    f,
                    "location `{location}` references unknown game `{game_id}`"
                )
            }
            RegionFlaw::UnknownStart(s) => write!(f, "start `{s}` is not a known location"),
            RegionFlaw::EdgeToUnknown { from, to, which } => {
                write!(f, "edge {from} -> {to} touches unknown location `{which}`")
            }
            RegionFlaw::GateToUnknown { from, to, prereq } => write!(
                f,
                "edge {from} -> {to} is gated on unknown location `{prereq}`"
            ),
        }
    }
}

impl std::error::Error for RegionFlaw {}

/// **The live traversal of a region** — which locations are COMPLETED and where the traveller
/// stands. Serializable (serde, like [`crate::SaveGame`]) so single-player progress persists.
/// Completion is only ever added by the verification-gated [`Self::record_completion`]; travel is
/// only ever moved by the gate-checked [`Self::travel`].
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RegionProgress {
    /// The region this progress belongs to ([`Region::id`]).
    pub region_id: String,
    /// The location the traveller currently stands in.
    pub location: String,
    /// The set of completed location ids (credited only through [`Self::record_completion`]).
    pub completed: BTreeSet<String>,
}

impl RegionProgress {
    /// A fresh traversal of `region` — at its `start`, nothing completed.
    pub fn new(region: &Region) -> RegionProgress {
        RegionProgress {
            region_id: region.id.clone(),
            location: region.start.clone(),
            completed: BTreeSet::new(),
        }
    }

    /// Whether location `id` is completed.
    pub fn is_completed(&self, id: &str) -> bool {
        self.completed.contains(id)
    }

    /// How many locations are cleared.
    pub fn cleared_count(&self) -> usize {
        self.completed.len()
    }

    /// Whether `edge`'s gate is satisfied by the current progress (an ungated edge is always open;
    /// a gated one opens once its prerequisite is completed).
    pub fn edge_open(&self, edge: &Edge) -> bool {
        match &edge.gate {
            None => true,
            Some(prereq) => self.completed.contains(prereq),
        }
    }

    /// The locations reachable RIGHT NOW — a `to` for which some open edge departs the current
    /// location.
    pub fn available_destinations(&self, region: &Region) -> BTreeSet<String> {
        region
            .edges_from(&self.location)
            .into_iter()
            .filter(|e| self.edge_open(e))
            .map(|e| e.to.clone())
            .collect()
    }

    /// **Whether travel to `to` is legal right now** — `Ok(())` iff an open edge from the current
    /// location reaches it; else the precise [`TravelError`]. A locked road names its prerequisite.
    pub fn can_travel(&self, region: &Region, to: &str) -> Result<(), TravelError> {
        if !region.has_location(to) {
            return Err(TravelError::UnknownLocation(to.to_string()));
        }
        let mut saw_road = false;
        for edge in region.edges_from(&self.location) {
            if edge.to == to {
                saw_road = true;
                if self.edge_open(edge) {
                    return Ok(());
                }
            }
        }
        if saw_road {
            // Every road to `to` is barred — report the (first) unmet prerequisite.
            let prereq = region
                .edges_from(&self.location)
                .into_iter()
                .filter(|e| e.to == to)
                .find_map(|e| e.gate.clone())
                .unwrap_or_default();
            Err(TravelError::Locked {
                to: to.to_string(),
                prerequisite: prereq,
            })
        } else {
            Err(TravelError::NoRoad {
                from: self.location.clone(),
                to: to.to_string(),
            })
        }
    }

    /// **Travel to `to`, returning the updated progress** (the current location moves). Refused
    /// with a [`TravelError`] when [`Self::can_travel`] would refuse — a locked or non-existent road
    /// moves nothing.
    pub fn travel(&self, region: &Region, to: &str) -> Result<RegionProgress, TravelError> {
        self.can_travel(region, to)?;
        let mut next = self.clone();
        next.location = to.to_string();
        Ok(next)
    }

    /// **Credit `location` as complete — but ONLY for a genuinely won + verified session.** The
    /// verification gate, in order:
    ///
    /// 1. `location` is a known location, and its game resolves ([`game_ctor`]);
    /// 2. `session` is a genuine session for THAT game — its map fingerprint equals the location's
    ///    declared game ([`CompletionError::WrongGame`] otherwise: a win for the wrong dungeon
    ///    cannot credit this one);
    /// 3. `session.status()` is [`GameStatus::Won`] ([`CompletionError::NotWon`] otherwise);
    /// 4. the chain passes [`crate::GameSession::verify`] (integrity) AND
    ///    [`crate::GameSession::verify_replay`] (re-execution) — a tampered or rule-incorrect chain
    ///    is refused ([`CompletionError::ChainBroken`] / [`CompletionError::ReplayMismatch`]).
    ///
    /// Only then is `location` added to a returned clone of the progress. Crediting an
    /// already-completed location is idempotent (it re-verifies and returns the same set). The
    /// self-progress is never mutated in place — the caller keeps the credited clone on success.
    pub fn record_completion(
        &self,
        region: &Region,
        location: &str,
        session: &GameSession,
    ) -> Result<RegionProgress, CompletionError> {
        let loc = region
            .location(location)
            .ok_or_else(|| CompletionError::UnknownLocation(location.to_string()))?;
        let ctor = game_ctor(&loc.game_id)
            .ok_or_else(|| CompletionError::UnknownGame(loc.game_id.clone()))?;
        // (2) IDENTITY — the session must be for this location's game. The map fingerprint is the
        // same identity the save/load registry uses, so a win for a different dungeon (or a
        // tampered map) cannot be laundered into crediting this location.
        let want = crate::savegame::world_fingerprint(&ctor());
        let got = crate::savegame::world_fingerprint(session.map());
        if want != got {
            return Err(CompletionError::WrongGame {
                location: location.to_string(),
                expected_game: loc.game_id.clone(),
            });
        }
        // (3) WON — an unfinished run credits nothing.
        if session.status() != GameStatus::Won {
            return Err(CompletionError::NotWon(session.status()));
        }
        // (4) VERIFIED — integrity AND re-execution, the SAME two teeth each game ships. A forged
        // or tampered chain is refused here, so progress can never be minted from a bad session.
        session.verify().map_err(CompletionError::ChainBroken)?;
        session
            .verify_replay()
            .map_err(CompletionError::ReplayMismatch)?;
        let mut next = self.clone();
        next.completed.insert(location.to_string());
        Ok(next)
    }
}

/// **Why travel was refused** — a legible reason.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TravelError {
    /// There is no road at all from the current location to `to`.
    NoRoad {
        /// Where the traveller stands.
        from: String,
        /// The unreachable destination.
        to: String,
    },
    /// A road to `to` exists but is barred until `prerequisite` is completed.
    Locked {
        /// The barred destination.
        to: String,
        /// The location that must be completed first.
        prerequisite: String,
    },
    /// `to` is not a location in this region.
    UnknownLocation(String),
}

impl std::fmt::Display for TravelError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TravelError::NoRoad { from, to } => {
                write!(f, "no road from `{from}` to `{to}`")
            }
            TravelError::Locked { to, prerequisite } => {
                write!(
                    f,
                    "the road to `{to}` stays barred until you clear `{prerequisite}`"
                )
            }
            TravelError::UnknownLocation(id) => write!(f, "`{id}` is not a place in this region"),
        }
    }
}

impl std::error::Error for TravelError {}

/// **Why a completion was NOT credited** — each variant names the tooth that bit. Every one is
/// fail-closed: [`RegionProgress::record_completion`] credits a location ONLY when all checks pass.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CompletionError {
    /// `location` is not a place in this region.
    UnknownLocation(String),
    /// The location's `game_id` does not resolve to a bundled game.
    UnknownGame(String),
    /// The session is not a session for this location's game (its map fingerprint disagrees) — a
    /// win for the wrong dungeon cannot credit this one.
    WrongGame {
        /// The location claimed.
        location: String,
        /// The game the location actually plays.
        expected_game: String,
    },
    /// The session has not been won — an unfinished run credits nothing.
    NotWon(GameStatus),
    /// The session's chain failed the INTEGRITY tier ([`crate::GameSession::verify`]) — a tampered
    /// history.
    ChainBroken(LedgerBreak),
    /// The session's chain failed the RE-EXECUTION tier ([`crate::GameSession::verify_replay`]) — a
    /// recorded effect is not the rule-correct resolution of its bound action.
    ReplayMismatch(ReplayMismatch),
}

impl std::fmt::Display for CompletionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CompletionError::UnknownLocation(id) => {
                write!(f, "REFUSED: `{id}` is not a place in this region")
            }
            CompletionError::UnknownGame(g) => {
                write!(f, "REFUSED: unknown game `{g}`")
            }
            CompletionError::WrongGame {
                location,
                expected_game,
            } => write!(
                f,
                "REFUSED: this session is not a run of `{expected_game}` (the game location `{location}` plays)"
            ),
            CompletionError::NotWon(s) => {
                write!(f, "REFUSED: the session is not won (status: {s:?})")
            }
            CompletionError::ChainBroken(b) => write!(f, "REFUSED (chain integrity): {b}"),
            CompletionError::ReplayMismatch(r) => write!(f, "REFUSED (re-execution): {r}"),
        }
    }
}

impl std::error::Error for CompletionError {}

// ─────────────────────────────────────────────────────────────────────────────
// THE CONCRETE REGION — the five bundled games wired into one navigable world.
// ─────────────────────────────────────────────────────────────────────────────

/// **THE DROWNED MARCHES — the region wiring all five bundled dungeons into one world.** A hub
/// (the tidewater vault) branches into two mid dungeons, one always-open and one sealed until the
/// hub is cleared; each mid dungeon opens a deeper way, and both deep ways converge on the final
/// venom deep — sealed until EITHER deep dungeon is cleared. So the map opens as you honestly clear
/// its dungeons:
///
/// ```text
///   tidewater (sunken-vault, START, the hub)
///     ├─ open ────────────────▶ thornmarch (bramble-keep)
///     │                            └─ gated on thornmarch ─▶ deepdark (deepdark-mine)
///     └─ gated on tidewater ──▶ starfall (starfall-spire)
///                                  └─ gated on starfall ───▶ venomdeep (venom-deep, the final)
///                              deepdark ─ gated on deepdark ─▶ venomdeep
/// ```
///
/// (Return roads are open, so a traveller can walk back freely; only the FORWARD roads into the
/// deeper dungeons are verified-completion-gated.)
pub fn drowned_marches() -> Region {
    Region {
        id: "drowned-marches".into(),
        name: "The Drowned Marches".into(),
        blurb: "Five sunken dungeons joined into one world — clear the tidewater vault to open the way inland, and earn your path down to the venom deep.".into(),
        locations: vec![
            Location::new(
                "tidewater",
                "The Tidewater Vault",
                "The drowned vault where every road inland begins — light the dark stair, best the Warden, and carry the amulet to the gate.",
                "sunken-vault",
            ),
            Location::new(
                "thornmarch",
                "The Thornmarch Keep",
                "A thorn-cursed ruin off the open road — trade the Hedge-Witch for her sickle and bear the Sunheart to open sky.",
                "bramble-keep",
            ),
            Location::new(
                "starfall",
                "The Starfall Spire",
                "A collapsing wizard's tower, sealed until the tidewater vault is cleared — read the grimoires and set the fallen star back in its cradle.",
                "starfall-spire",
            ),
            Location::new(
                "deepdark",
                "The Deepdark Mine",
                "A sunless mine beneath the keep — race the failing lamp down eleven pitch-black levels and back to daylight.",
                "deepdark-mine",
            ),
            Location::new(
                "venomdeep",
                "The Venomous Deep",
                "The drowned heart of the marches, sealed until a deeper dungeon is cleared — ward the venom, fell the Wyrm, and bear the Venom-Heart to the surface.",
                "venom-deep",
            ),
        ],
        edges: vec![
            // The hub branches: an always-open road to the keep, a sealed road to the spire.
            Edge::open("tidewater", "thornmarch"),
            Edge::gated("tidewater", "starfall", "tidewater"),
            // The deeper ways, each sealed behind its mid dungeon.
            Edge::gated("thornmarch", "deepdark", "thornmarch"),
            Edge::gated("starfall", "venomdeep", "starfall"),
            Edge::gated("deepdark", "venomdeep", "deepdark"),
            // Open return roads (walk back freely; the forward gates are the load-bearing ones).
            Edge::open("thornmarch", "tidewater"),
            Edge::open("starfall", "tidewater"),
            Edge::open("deepdark", "thornmarch"),
            Edge::open("venomdeep", "starfall"),
            Edge::open("venomdeep", "deepdark"),
        ],
        start: "tidewater".into(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        bramble_keep, starfall_spire, sunken_vault, GameSession, GameStatus, PlayResult, SaveGame,
    };

    // Winning command scripts for the two dungeons the record_completion tests drive to `Won`
    // (mirrors the engine's own playthrough scripts; the resolver is world-driven, so these are the
    // legal solving moves, not a scripted win).
    const SUNKEN_SOLVE: &[&str] = &[
        "go north",
        "take lantern",
        "go down",
        "go down",
        "take rusted_key",
        "go north",
        "use rusted_key on iron_door",
        "go east",
        "take sword",
        "go north",
        "attack warden",
        "go east",
        "take amulet",
        "go up",
    ];

    const STARFALL_SOLVE: &[&str] = &[
        "go up",
        "take candle_primer",
        "read candle_primer",
        "cast light",
        "go up",
        "take star_chart",
        "take mending_folio",
        "read mending_folio",
        "cast mend on stair",
        "go up",
        "take opening_codex",
        "read opening_codex",
        "go west",
        "ask astronomer about flame",
        "read flare_grimoire",
        "go east",
        "go up",
        "use star_chart on orrery",
        "cast unlock on sky_door",
        "go up",
        "cast flare",
        "attack voidling",
        "attack voidling",
        "attack voidling",
        "go up",
        "take fallen_star",
        "go up",
    ];

    fn play(mut game: GameSession, script: &[&str]) -> GameSession {
        for cmd in script {
            let res = game.command("hero", cmd);
            assert!(
                matches!(res, PlayResult::Landed { .. }),
                "`{cmd}` should land: {res:?}"
            );
        }
        game
    }

    #[test]
    fn the_drowned_marches_is_well_formed() {
        let region = drowned_marches();
        assert!(
            region.is_well_formed(),
            "the concrete region validates cleanly: {:?}",
            region.validate()
        );
        assert_eq!(region.locations.len(), 5, "it wires all five bundled games");
    }

    #[test]
    fn validate_flags_an_edge_to_an_unknown_location_and_an_unknown_game() {
        // A hand-built MALFORMED region: an edge to a location that does not exist, and a location
        // whose game_id does not resolve. validate() must surface BOTH (non-vacuous — the good
        // region above reports none).
        let region = Region {
            id: "broken".into(),
            name: "Broken".into(),
            blurb: "".into(),
            locations: vec![
                Location::new("a", "A", "", "sunken-vault"),
                Location::new("b", "B", "", "not-a-real-game"),
            ],
            edges: vec![Edge::open("a", "nowhere")],
            start: "a".into(),
        };
        let flaws = region.validate();
        assert!(
            flaws.iter().any(
                |f| matches!(f, RegionFlaw::EdgeToUnknown { which, .. } if which == "nowhere")
            ),
            "an edge to an unknown location is flagged: {flaws:?}"
        );
        assert!(
            flaws
                .iter()
                .any(|f| matches!(f, RegionFlaw::UnknownGame { game_id, .. } if game_id == "not-a-real-game")),
            "a location with an unknown game is flagged: {flaws:?}"
        );
        assert!(!region.is_well_formed());
    }

    #[test]
    fn record_completion_credits_a_genuinely_won_and_verified_session() {
        let region = drowned_marches();
        let progress = RegionProgress::new(&region);
        let game = play(GameSession::open(sunken_vault()), SUNKEN_SOLVE);
        assert_eq!(game.status(), GameStatus::Won);

        let credited = progress
            .record_completion(&region, "tidewater", &game)
            .expect("a genuine won + verified session credits the location");
        assert!(credited.is_completed("tidewater"));
        assert_eq!(credited.cleared_count(), 1);
        // Non-mutating: the original progress is untouched (the credit is the returned clone).
        assert!(!progress.is_completed("tidewater"));
    }

    #[test]
    fn record_completion_refuses_an_unfinished_session() {
        // NON-VACUOUS: the SAME location IS credited once the session is genuinely won (above), but
        // an unfinished run of that very game is REFUSED with NotWon — the progress is not minted.
        let region = drowned_marches();
        let progress = RegionProgress::new(&region);
        let mut game = GameSession::open(sunken_vault());
        // Play only the first couple of legal moves — nowhere near the win.
        assert!(game.command("hero", "go north").landed());
        assert!(game.command("hero", "take lantern").landed());
        assert_eq!(game.status(), GameStatus::Playing);

        let err = progress
            .record_completion(&region, "tidewater", &game)
            .expect_err("an unfinished session must be refused");
        assert_eq!(err, CompletionError::NotWon(GameStatus::Playing));
    }

    #[test]
    fn record_completion_refuses_a_win_for_the_wrong_game() {
        // NON-VACUOUS forged-claim refusal: a GENUINE, fully won + verified sunken-vault session is
        // offered to credit the `starfall` location (whose game is starfall-spire). The map
        // fingerprint disagrees, so it is REFUSED with WrongGame — you cannot clear a gated location
        // by winning a different, easier dungeon. (The same session DOES credit `tidewater`.)
        let region = drowned_marches();
        let progress = RegionProgress::new(&region);
        let vault_win = play(GameSession::open(sunken_vault()), SUNKEN_SOLVE);
        assert_eq!(vault_win.status(), GameStatus::Won);

        let err = progress
            .record_completion(&region, "starfall", &vault_win)
            .expect_err("a vault win cannot credit the starfall location");
        assert_eq!(
            err,
            CompletionError::WrongGame {
                location: "starfall".into(),
                expected_game: "starfall-spire".into(),
            }
        );
        // Sanity: the very same session DOES legitimately credit its own location.
        assert!(vault_win.verify().is_ok());
        assert!(progress
            .record_completion(&region, "tidewater", &vault_win)
            .is_ok());
    }

    #[test]
    fn a_tampered_won_session_cannot_even_be_constructed_the_gate_bites_at_load() {
        // The only way to obtain a GameSession is to PLAY one (honest) or LOAD a save — and load
        // re-verifies fail-closed. So a tampered `Won` session cannot be handed to
        // record_completion at all: forging an effect in a saved won run and reloading is REFUSED.
        // (record_completion re-verifies again as defense in depth; this proves the construction
        // path itself is gated.)
        let game = play(GameSession::open(sunken_vault()), SUNKEN_SOLVE);
        let save = game.save();
        // A clean save round-trips and loads (the contrast that makes the refusal non-vacuous).
        let ok = SaveGame::from_json(&save.to_json()).expect("clean save decodes");
        assert!(GameSession::load(&ok, sunken_vault()).is_ok());

        // Tamper: bump the effect of some landed turn. Its stored receipt no longer recomputes, so
        // load refuses fail-closed.
        let mut forged = save.clone();
        let victim = forged
            .ledger
            .iter_mut()
            .find(|e| e.effect.is_some())
            .expect("some turn carries an effect");
        victim.effect = Some(crate::WorldEffect::SetFlag("forged".into(), 99));
        // It is caught fail-closed (integrity or re-execution) — never silently resumed.
        match GameSession::load(&forged, sunken_vault()) {
            Ok(_) => panic!("a tampered saved win must be refused on load"),
            Err(e) => assert!(
                matches!(
                    e,
                    crate::LoadError::ChainBroken(_) | crate::LoadError::ReplayMismatch(_)
                ),
                "refused fail-closed, got {e:?}"
            ),
        }
    }

    #[test]
    fn travel_is_verified_completion_gated_and_the_gate_opens() {
        let region = drowned_marches();
        let start = RegionProgress::new(&region);
        assert_eq!(start.location, "tidewater");

        // The open road to the keep is always travellable.
        assert!(start.can_travel(&region, "thornmarch").is_ok());
        // The road to the spire is BARRED until the tidewater vault is cleared.
        assert_eq!(
            start.can_travel(&region, "starfall"),
            Err(TravelError::Locked {
                to: "starfall".into(),
                prerequisite: "tidewater".into(),
            })
        );

        // Clear the tidewater vault the honest way (a verified win), then the gate OPENS.
        let vault_win = play(GameSession::open(sunken_vault()), SUNKEN_SOLVE);
        let progress = start
            .record_completion(&region, "tidewater", &vault_win)
            .expect("verified win credits tidewater");
        assert!(
            progress.can_travel(&region, "starfall").is_ok(),
            "clearing tidewater opens the road to the starfall spire"
        );
        // And travel actually moves the traveller.
        let moved = progress
            .travel(&region, "starfall")
            .expect("the gate is open now");
        assert_eq!(moved.location, "starfall");
        assert!(progress
            .available_destinations(&region)
            .contains("starfall"));
    }

    #[test]
    fn a_second_dungeon_clears_and_the_deep_road_opens() {
        // A fuller traversal: clear tidewater → travel to and clear starfall → its deep road to the
        // venom deep opens. Proves the cumulative progress + the second gate.
        let region = drowned_marches();
        let p0 = RegionProgress::new(&region);
        let vault_win = play(GameSession::open(sunken_vault()), SUNKEN_SOLVE);
        let p1 = p0
            .record_completion(&region, "tidewater", &vault_win)
            .unwrap();
        let p2 = p1.travel(&region, "starfall").unwrap();
        assert_eq!(
            p2.can_travel(&region, "venomdeep"),
            Err(TravelError::Locked {
                to: "venomdeep".into(),
                prerequisite: "starfall".into(),
            }),
            "the venom deep stays sealed until the spire is cleared"
        );
        let spire_win = play(GameSession::open(starfall_spire()), STARFALL_SOLVE);
        let p3 = p2
            .record_completion(&region, "starfall", &spire_win)
            .unwrap();
        assert_eq!(p3.cleared_count(), 2);
        assert!(
            p3.can_travel(&region, "venomdeep").is_ok(),
            "clearing the spire opens the deep road to the venom deep"
        );
    }

    #[test]
    fn region_progress_serializes_round_trip() {
        let region = drowned_marches();
        let vault_win = play(GameSession::open(sunken_vault()), SUNKEN_SOLVE);
        let progress = RegionProgress::new(&region)
            .record_completion(&region, "tidewater", &vault_win)
            .unwrap();
        let json = serde_json::to_string(&progress).unwrap();
        let back: RegionProgress = serde_json::from_str(&json).unwrap();
        assert_eq!(progress, back);
        assert!(back.is_completed("tidewater"));

        // And a bramble win credits its location too (exercises a third game's identity check).
        let keep_win = play(
            GameSession::open(bramble_keep()),
            &[
                "take candle",
                "go north",
                "go down",
                "take key",
                "go up",
                "use key on gate",
                "go east",
                "take nightshade",
                "go west",
                "go west",
                "ask witch about sickle",
                "go east",
                "go north",
                "go north",
                "go north",
                "attack knight",
                "attack knight",
                "go north",
                "take sunheart",
                "go up",
            ],
        );
        assert!(back
            .record_completion(&region, "thornmarch", &keep_win)
            .is_ok());
    }
}
